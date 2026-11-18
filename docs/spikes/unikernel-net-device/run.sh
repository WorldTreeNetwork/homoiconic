#!/bin/sh
# One ARP request and one UDP datagram, host to guest and back, on morphie.
# Not the Lean image and not the factorial acceptance.
set -eu
HERE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT="$(CDPATH= cd -- "$HERE/../../.." && pwd)"
CH="${CLOUD_HYPERVISOR:-$HOME/ch54/cloud-hypervisor}"
ZIG="${ZIG:-$HOME/zig-0.16.0/zig}"
OUT="$HERE/out"
TAP=ukspike0
GUEST_MAC=02:00:00:00:00:02

rm -rf "$OUT"
mkdir -p "$OUT"
"$ZIG" version
"$CH" --version | head -n 1
uname -sm

"$ZIG" build-exe -target x86_64-freestanding-none -O ReleaseSmall -fno-PIE \
    -fno-stack-check -fno-stack-protector \
    -femit-bin="$OUT/spike.elf" \
    "$HERE/guest/boot.S" "$HERE/guest/spike.zig"

sudo ip link del "$TAP" 2>/dev/null || true
sudo ip tuntap add dev "$TAP" mode tap user "$(id -un)"
sudo ip addr add 10.99.0.1/24 dev "$TAP"
sudo ip link set "$TAP" up
sudo ip link set "$TAP" promisc on
cleanup() {
    sudo ip link del "$TAP" 2>/dev/null || true
}
trap cleanup EXIT

rm -f "$OUT/serial.log" "$OUT/ch.log" "$OUT/exchange.log"
timeout 25 "$CH" --kernel "$OUT/spike.elf" --cpus boot=1 --memory size=512M \
    --serial "file=$OUT/serial.log" --console off \
    --net "tap=$TAP,mac=$GUEST_MAC" >"$OUT/ch.log" 2>&1 &
chpid=$!

sudo -n python3 - "$TAP" "$OUT/serial.log" "$OUT/exchange.log" <<'PY' &
import socket, struct, sys, time
tap, serial_path, log_path = sys.argv[1:]
log = open(log_path, "w")
def note(s):
    log.write(s + "\n"); log.flush()
deadline = time.time() + 20
while time.time() < deadline:
    try:
        text = open(serial_path).read()
    except FileNotFoundError:
        text = ""
    if "ready\n" in text or "spike: fail" in text:
        break
    time.sleep(0.05)
else:
    note("timeout waiting for ready")
    sys.exit(1)
text = open(serial_path).read()
if "spike: fail" in text:
    note("guest failed before ready")
    sys.exit(1)
note("guest ready")
s = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(0x0003))
s.bind((tap, 0))
s.settimeout(2)
host_mac = s.getsockname()[4]
guest_mac = bytes.fromhex("020000000002")
guest_ip = bytes([10, 99, 0, 2])
host_ip = bytes([10, 99, 0, 1])
def send(frame):
    s.send(frame)
def recv():
    return s.recv(2048)
arp = host_mac + b"\xff"*6
# ethernet dest broadcast, src host
frame = b"\xff"*6 + host_mac + b"\x08\x06"
frame += b"\x00\x01\x08\x00\x06\x04\x00\x01"
frame += host_mac + host_ip + b"\x00"*6 + guest_ip
send(frame)
note("sent arp")
arp_ok = False
end = time.time() + 3
while time.time() < end:
    try:
        pkt = recv()
    except socket.timeout:
        break
    if len(pkt) >= 42 and pkt[12:14] == b"\x08\x06" and pkt[20:22] == b"\x00\x02":
        if pkt[28:32] == guest_ip and pkt[38:42] == host_ip:
            guest_mac = pkt[22:28]
            arp_ok = True
            note("arp reply mac " + guest_mac.hex())
            break
if not arp_ok:
    note("no arp reply")
    sys.exit(1)
payload = b"spike-udp"
ulen = 8 + len(payload)
ip_len = 20 + ulen
def csum(data):
    if len(data) % 2: data += b"\x00"
    t = sum(struct.unpack("!%dH" % (len(data)//2), data))
    while t >> 16: t = (t & 0xffff) + (t >> 16)
    return (~t) & 0xffff
ip = bytearray(20)
ip[0] = 0x45
ip[2:4] = struct.pack("!H", ip_len)
ip[8] = 64
ip[9] = 17
ip[12:16] = host_ip
ip[16:20] = guest_ip
ip[10:12] = struct.pack("!H", csum(ip))
udp = bytearray(ulen)
udp[0:2] = struct.pack("!H", 9000)
udp[2:4] = struct.pack("!H", 9000)
udp[4:6] = struct.pack("!H", ulen)
udp[8:] = payload
pseudo = host_ip + guest_ip + b"\x00\x11" + struct.pack("!H", ulen)
udp[6:8] = struct.pack("!H", csum(pseudo + udp) or 0xffff)
frame = guest_mac + host_mac + b"\x08\x00" + bytes(ip) + bytes(udp)
send(frame)
note("sent udp")
udp_ok = False
end = time.time() + 3
while time.time() < end:
    try:
        pkt = recv()
    except socket.timeout:
        break
    if len(pkt) >= 42 and pkt[12:14] == b"\x08\x00" and pkt[23] == 17:
        if pkt[26:30] == guest_ip and pkt[30:34] == host_ip and pkt[42:42+len(payload)] == payload:
            udp_ok = True
            note("udp echo %d bytes" % len(payload))
            break
if not udp_ok:
    note("no udp echo")
    sys.exit(1)
note("exchange ok")
PY
pypid=$!
wait "$pypid" || py=$?
py="${py:-0}"
wait "$chpid" || ch=$?
ch="${ch:-0}"
echo "python $py cloud-hypervisor $ch"
echo "---- serial ----"
cat "$OUT/serial.log" || true
echo "---- exchange ----"
cat "$OUT/exchange.log" || true
[ "$py" = 0 ] || exit "$py"
grep -q "spike: ok" "$OUT/serial.log"
grep -q "exchange ok" "$OUT/exchange.log"
