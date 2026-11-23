#!/bin/sh
# Authenticated QUIC on the existing UDP image: factorial, a budget reply
# with the guest still answering, a wrong peer key, loss plus reordering,
# and a second host that sends what it likes: garbage and a new handshake in
# the middle of an exchange, garbage long headers after the reply, and a
# first flight with a bad UDP checksum.
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
OTHERIP=192.168.249.9
MAC=02:00:00:00:00:02
CMD="reflect.ip=$IP reflect.port=$PORT reflect.quic_port=$QPORT"

[ -r /dev/kvm ] && [ -w /dev/kvm ]
"$CH" --version | grep -qx "cloud-hypervisor v54.0"
sh "$HERE/build-net.sh"

pid=
sudo ip link del "$TAP" 2>/dev/null || true
sudo ip tuntap add dev "$TAP" mode tap user "$(id -un)"
sudo ip addr add "$HOSTIP/24" dev "$TAP"
sudo ip addr add "$OTHERIP/24" dev "$TAP"
sudo ip link set "$TAP" up
cleanup() {
    [ -z "$pid" ] || kill "$pid" 2>/dev/null || true
    sudo ip link del "$TAP" 2>/dev/null || true
}
trap cleanup EXIT

boot() {
    rm -f "$OUT/serial.log" "$OUT/ch.log"
    timeout 400 "$CH" --kernel "$OUT/reflect-net.elf" --cpus boot=1 --memory size=512M \
        --serial "file=$OUT/serial.log" --console off \
        --net "tap=$TAP,mac=$MAC" --cmdline "$1" >"$OUT/ch.log" 2>&1 &
    pid=$!
}

boot "$CMD"
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
# factorial <name> [client mode words]: the reply is the Linux process's.
factorial() {
    name="$1"
    shift
    "$OUT/quic-client" "$IP" "$QPORT" 100000000 "$fact" "$@" > "$OUT/quic-$name.frame"
    body "$OUT/quic-$name.frame" "$OUT/quic-$name.body"
    cmp -s "$OUT/quic-$name.body" "$OUT/factorial.reply"
    kind "$OUT/quic-$name.frame"
}

factorial fact
echo "ok   factorial over QUIC equals the Linux process"

"$OUT/quic-client" "$IP" "$QPORT" 5000 "$fore" > "$OUT/quic-budget.frame"
body "$OUT/quic-budget.frame" "$OUT/quic-budget.body"
cmp -s "$OUT/quic-budget.body" "$OUT/budget.reply"
kind "$OUT/quic-budget.frame"
echo "ok   a 5000-step budget reply equals the Linux process"

# The guest stayed up: a new handshake still returns factorial.
factorial fact2
echo "ok   factorial again on a new handshake"

"$OUT/quic-client" "$IP" "$QPORT" 100000000 "$fact" wrong
echo "ok   a wrong pin is refused by the client"

# The refused handshake was left unfinished. The guest keeps it for two idle
# seconds and then takes this one, which also loses and reorders datagrams.
factorial loss loss
echo "ok   factorial after an abandoned handshake, with loss and reordering"

# A second host at another address, during and after an exchange.
factorial spoof spoof "$OTHERIP"
echo "ok   factorial with a second address sending garbage and a new Initial; that address heard nothing"

factorial fact3
echo "ok   factorial again after the garbage"

# A real first flight with a bad UDP checksum is dropped; the same bytes with
# a good one are answered.
"$OUT/quic-client" "$IP" "$QPORT" 1 "$fact" initial > "$OUT/quic-initial.bin"
sudo -n python3 - "$TAP" "$OUT/quic-initial.bin" "$QPORT" <<'PY'
import socket, struct, sys, time
tap, path, qport = sys.argv[1], sys.argv[2], int(sys.argv[3])
payload = open(path, "rb").read()
s = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(0x0003))
s.bind((tap, 0))
host_mac = s.getsockname()[4]
guest_mac = bytes.fromhex("020000000002")
guest_ip = bytes([192, 168, 249, 2])
host_ip = bytes([192, 168, 249, 1])
sport = 9100

def csum(data):
    if len(data) % 2:
        data += b"\x00"
    t = sum(struct.unpack("!%dH" % (len(data) // 2), data))
    while t >> 16:
        t = (t & 0xffff) + (t >> 16)
    return (~t) & 0xffff

def send(bad):
    ulen = 8 + len(payload)
    ip = bytearray(20)
    ip[0] = 0x45
    ip[2:4] = struct.pack("!H", 20 + ulen)
    ip[8] = 64
    ip[9] = 17
    ip[12:16] = host_ip
    ip[16:20] = guest_ip
    ip[10:12] = struct.pack("!H", csum(bytes(ip)))
    u = bytearray(ulen)
    u[0:2] = struct.pack("!H", sport)
    u[2:4] = struct.pack("!H", qport)
    u[4:6] = struct.pack("!H", ulen)
    u[8:] = payload
    cs = csum(host_ip + guest_ip + b"\x00\x11" + struct.pack("!H", ulen) + bytes(u)) or 0xffff
    if bad:
        cs ^= 0x0100
        if cs == 0:
            cs = 0x0200
    u[6:8] = struct.pack("!H", cs)
    s.send(guest_mac + host_mac + b"\x08\x00" + bytes(ip) + bytes(u))

def answered(seconds):
    end = time.time() + seconds
    while time.time() < end:
        s.settimeout(max(0.01, end - time.time()))
        try:
            pkt = s.recv(4096)
        except socket.timeout:
            return False
        if len(pkt) >= 42 and pkt[12:14] == b"\x08\x00" and pkt[23] == 17 and pkt[26:30] == guest_ip \
                and struct.unpack("!H", pkt[34:36])[0] == qport and struct.unpack("!H", pkt[36:38])[0] == sport:
            return True
    return False

send(bad=True)
if answered(1.0):
    sys.exit("a first flight with a bad UDP checksum was answered")
send(bad=False)
if not answered(3.0):
    sys.exit("the same first flight with a good checksum was not answered")
PY
echo "ok   a first flight with a bad UDP checksum is dropped; with a good one it is answered"

# That handshake is left unfinished too; the guest still serves.
factorial fact4
echo "ok   factorial after the unfinished raw handshake"

if grep -v -e "^reflect: ready $IP:$PORT\$" -e "^reflect: quic $QPORT\$" "$OUT/serial.log" | grep -q .; then
    echo "the guest said something unexpected:" >&2
    cat "$OUT/serial.log" >&2
    exit 1
fi
kill "$pid" 2>/dev/null || true
wait "$pid" 2>/dev/null || true
pid=
echo "quic guest ok"
