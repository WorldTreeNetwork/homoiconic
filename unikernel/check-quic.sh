#!/bin/sh
# Authenticated QUIC on the existing UDP image: factorial, a budget reply
# with the guest still answering, a wrong peer key, and loss plus reordering.
set -eu
HERE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT="$(CDPATH= cd -- "$HERE/.." && pwd)"
CH="${CLOUD_HYPERVISOR:-$HOME/ch54/cloud-hypervisor}"
OUT="$HERE/out-net"
TAP="ukquic$$"
IP=192.168.249.2
PORT=4444
QPORT=4445
HOSTIP=192.168.249.1
MAC=02:00:00:00:00:02
CMD="reflect.ip=$IP reflect.port=$PORT reflect.quic_port=$QPORT"

[ -r /dev/kvm ] && [ -w /dev/kvm ]
"$CH" --version | grep -qx "cloud-hypervisor v54.0"
sh "$HERE/build-net.sh"

sudo ip link del "$TAP" 2>/dev/null || true
sudo ip tuntap add dev "$TAP" mode tap user "$(id -un)"
sudo ip addr add "$HOSTIP/24" dev "$TAP"
sudo ip link set "$TAP" up
cleanup() { sudo ip link del "$TAP" 2>/dev/null || true; }
trap cleanup EXIT

rm -f "$OUT/serial.log" "$OUT/ch.log"
timeout 400 "$CH" --kernel "$OUT/reflect-net.elf" --cpus boot=1 --memory size=512M \
    --serial "file=$OUT/serial.log" --console off \
    --net "tap=$TAP,mac=$MAC" --cmdline "$CMD" >"$OUT/ch.log" 2>&1 &
pid=$!

end=$(( $(date +%s) + 90 ))
while [ "$(date +%s)" -lt "$end" ]; do
    if grep -q "reflect: quic $QPORT" "$OUT/serial.log" 2>/dev/null; then
        break
    fi
    if ! kill -0 "$pid" 2>/dev/null; then
        echo "guest exited" >&2
        cat "$OUT/serial.log" >&2 || true
        exit 1
    fi
    sleep 0.05
done
grep -q "reflect: quic $QPORT" "$OUT/serial.log"

fact="$ROOT/examples/factorial.hom"
fore="$ROOT/examples/forever.hom"
"$OUT/reply" run 100000000 "$fact" > "$OUT/factorial.reply"
"$OUT/reply" run 5000 "$fore" > "$OUT/budget.reply"

body() {
    dd if="$1" of="$2" bs=1 skip=24 status=none
}
kind() {
    od -An -tx1 -N2 -j4 "$1" | grep -q "01 00"
}

"$OUT/quic-client" "$IP" "$QPORT" 100000000 "$fact" > "$OUT/quic-fact.frame"
body "$OUT/quic-fact.frame" "$OUT/quic-fact.body"
cmp -s "$OUT/quic-fact.body" "$OUT/factorial.reply"
kind "$OUT/quic-fact.frame"

"$OUT/quic-client" "$IP" "$QPORT" 5000 "$fore" > "$OUT/quic-budget.frame"
body "$OUT/quic-budget.frame" "$OUT/quic-budget.body"
cmp -s "$OUT/quic-budget.body" "$OUT/budget.reply"
kind "$OUT/quic-budget.frame"

# The guest stayed up: a new handshake still returns factorial.
"$OUT/quic-client" "$IP" "$QPORT" 100000000 "$fact" > "$OUT/quic-fact2.frame"
body "$OUT/quic-fact2.frame" "$OUT/quic-fact2.body"
cmp -s "$OUT/quic-fact2.body" "$OUT/factorial.reply"

"$OUT/quic-client" "$IP" "$QPORT" 100000000 "$fact" wrong
"$OUT/quic-client" "$IP" "$QPORT" 100000000 "$fact" loss > "$OUT/quic-loss.frame"
body "$OUT/quic-loss.frame" "$OUT/quic-loss.body"
cmp -s "$OUT/quic-loss.body" "$OUT/factorial.reply"

kill "$pid" 2>/dev/null || true
wait "$pid" 2>/dev/null || true
echo "quic guest ok"
