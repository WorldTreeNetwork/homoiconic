#!/bin/sh
# Two guests. One sends a closure and a reply channel. The other runs it and
# answers on that channel. The delivery log replays to the same result here.
# Each guest has its own entity key, made for this run, and allows only the
# other's name. A guest that expects another name refuses its peer, and a
# guest whose peer does not allow it gets no answer.
set -eu
HERE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT="$(CDPATH= cd -- "$HERE/.." && pwd)"
CH="${CLOUD_HYPERVISOR:-$HOME/ch54/cloud-hypervisor}"
OUT="$HERE/out-net"
BR="ukbr$$"
TA="ukwa$$"
TB="ukwb$$"
CHA=192.168.249.2
CHB=192.168.249.3
HOSTIP=192.168.249.1

[ -r /dev/kvm ] && [ -w /dev/kvm ]
"$CH" --version | grep -qx "cloud-hypervisor v54.0"
sh "$HERE/build-net.sh"
( cd "$ROOT/kernel" && lake env lean RemoteCheck.lean ) | tee "$OUT/remote-lean.txt"
grep -q "^FAIL" "$OUT/remote-lean.txt" && exit 1
grep -q "ok   a remote closure replays to 42" "$OUT/remote-lean.txt"
"$OUT/remote-check"

( umask 077
  for k in a b other; do head -c 32 /dev/urandom > "$OUT/wire-key-$k"; done )
KA="$OUT/wire-key-a"
KB="$OUT/wire-key-b"
NA="$("$OUT/entity" name "$KA")"
NB="$("$OUT/entity" name "$KB")"
NO="$("$OUT/entity" name "$OUT/wire-key-other")"

sudo ip link del "$TA" 2>/dev/null || true
sudo ip link del "$TB" 2>/dev/null || true
sudo ip link del "$BR" 2>/dev/null || true
sudo ip link add "$BR" type bridge
sudo ip addr add "$HOSTIP/24" dev "$BR"
sudo ip link set "$BR" up
sudo ip tuntap add dev "$TA" mode tap user "$(id -un)"
sudo ip tuntap add dev "$TB" mode tap user "$(id -un)"
sudo ip link set "$TA" master "$BR" up
sudo ip link set "$TB" master "$BR" up
sudo ip link set "$TA" promisc on
sudo ip link set "$TB" promisc on
cleanup() {
    sudo ip link del "$TA" 2>/dev/null || true
    sudo ip link del "$TB" 2>/dev/null || true
    sudo ip link del "$BR" 2>/dev/null || true
}
trap cleanup EXIT

boot() {
    tap="$1"
    mac="$2"
    cmd="$3"
    log="$4"
    key="$5"
    rm -f "$log"
    timeout 180 "$CH" --kernel "$OUT/reflect-net.elf" --initramfs "$key" --cpus boot=1 --memory size=512M \
        --serial "file=$log" --console off \
        --net "tap=$tap,mac=$mac" --cmdline "$cmd" >"$OUT/ch-wire.log" 2>&1 &
    echo $!
}

# pair <the name A allows> <the name B allows>
pair() {
    pb=$(boot "$TB" 02:00:00:00:00:03 "reflect.ip=$CHB reflect.port=4444 reflect.wire_port=4446 reflect.allow=$2" "$OUT/wire-b.log" "$KB")
    pa=$(boot "$TA" 02:00:00:00:00:02 "reflect.ip=$CHA reflect.port=4444 reflect.peer=$CHB:4446 reflect.allow=$1" "$OUT/wire-a.log" "$KA")
}
unpair() {
    kill "$pa" "$pb" 2>/dev/null || true
    wait "$pa" 2>/dev/null || true
    wait "$pb" 2>/dev/null || true
}
# said <line>: A says the line within 60 seconds and never `remote ok`.
said() {
    end=$(( $(date +%s) + 60 ))
    while [ "$(date +%s)" -lt "$end" ]; do
        if grep -qx "reflect: $1" "$OUT/wire-a.log" 2>/dev/null; then break; fi
        sleep 0.05
    done
    grep -qx "reflect: $1" "$OUT/wire-a.log"
    sleep 1
    if grep -q "reflect: remote ok" "$OUT/wire-a.log"; then
        echo "a guest finished the exchange with a peer it should not have" >&2
        exit 1
    fi
}

pair "$NB" "$NA"

end=$(( $(date +%s) + 90 ))
while [ "$(date +%s)" -lt "$end" ]; do
    if grep -q "reflect: remote ok" "$OUT/wire-a.log" 2>/dev/null; then
        break
    fi
    if ! kill -0 "$pa" 2>/dev/null || ! kill -0 "$pb" 2>/dev/null; then
        echo "a guest exited" >&2
        echo "-- A --" >&2
        cat "$OUT/wire-a.log" >&2 || true
        echo "-- B --" >&2
        cat "$OUT/wire-b.log" >&2 || true
        exit 1
    fi
    sleep 0.05
done
grep -q "reflect: remote ok" "$OUT/wire-a.log"
grep -q "reflect: log " "$OUT/wire-a.log"
grep -q "reflect: wire 4446" "$OUT/wire-b.log"
grep -qx "reflect: entity $NA" "$OUT/wire-a.log"
grep -qx "reflect: entity $NB" "$OUT/wire-b.log"
unpair
echo "ok   two guests with two keys, each allowing the other's name, exchange the message"

# A expects another name than B's: A refuses B and sends no offer.
pair "$NO" "$NA"
said "the peer is not allowed"
unpair
echo "ok   a guest that expects another name refuses its peer"

# B does not allow A: B takes none of A's handshake, and A gets no answer.
pair "$NB" "$NO"
said "the peer gave no answer"
unpair
echo "ok   a guest its peer does not allow gets no answer"
echo "wire guests ok"
