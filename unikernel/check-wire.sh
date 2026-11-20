#!/bin/sh
# Two guests. One sends a closure and a reply channel. The other runs it and
# answers on that channel. The delivery log replays to the same result here.
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
    rm -f "$log"
    timeout 180 "$CH" --kernel "$OUT/reflect-net.elf" --cpus boot=1 --memory size=512M \
        --serial "file=$log" --console off \
        --net "tap=$tap,mac=$mac" --cmdline "$cmd" >"$OUT/ch-wire.log" 2>&1 &
    echo $!
}

pb=$(boot "$TB" 02:00:00:00:00:03 "reflect.ip=$CHB reflect.port=4444 reflect.wire_port=4446" "$OUT/wire-b.log")
pa=$(boot "$TA" 02:00:00:00:00:02 "reflect.ip=$CHA reflect.port=4444 reflect.peer=$CHB:4446" "$OUT/wire-a.log")

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
kill "$pa" "$pb" 2>/dev/null || true
wait "$pa" 2>/dev/null || true
wait "$pb" 2>/dev/null || true
echo "wire guests ok"
