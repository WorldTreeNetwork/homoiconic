#!/bin/sh
# Authenticated QUIC on the existing UDP image: factorial, a budget reply
# with the guest still answering, a wrong peer key, loss plus reordering,
# and a second host that sends what it likes: garbage and a new handshake in
# the middle of an exchange, garbage long headers after the reply, and a
# first flight with a bad UDP checksum. Then what the guest sends and stops
# sending: its answer to a first flight is at least 1200 bytes, a reply the
# client acknowledges is sent once, a reply nobody acknowledges is given up,
# and a first flight from an address that is never heard from again is
# answered with at most three times its bytes, in datagrams of 1200 or more. Before all that, the command lines that ask for two QUIC services at
# once, which the guest refuses.
#
# Every guest and client here has an entity key, made for this run. The
# guest's is the file given at boot; the client's name is on the guest's
# list. Checked: a guest with no key, a short key or a zero key serves no
# QUIC; two keys are two identities and one key twice is one; a client that
# expects another name refuses the guest; a client the guest does not allow
# is refused, and the guest serves the next one at once; stream data in an
# Initial packet is not acted on; and plain UDP beside QUIC is not answered.
#
# Admission (add-quic-admission), on a fresh boot of the same key: the
# client Mjolnir vendors (e9a4c86, which ignores a Retry) is served while a
# first-flight slot is free; while a second address floods the guest with new
# first flights, one first flight again and again and the datagrams of a
# finished exchange, five allowed clients are each served within a second;
# and four stalled clients with a key on no list hold the first-flight pool
# no longer than the cap.
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
FORGEDIP=192.168.249.77
MAC=02:00:00:00:00:02
BASE="reflect.ip=$IP reflect.port=$PORT reflect.quic_port=$QPORT"

[ -r /dev/kvm ] && [ -w /dev/kvm ]
"$CH" --version | grep -qx "cloud-hypervisor v54.0"
sh "$HERE/build-net.sh"

# Three entities for this run: the guest, the client it allows, and one
# that is on no list. A key is 32 bytes from anywhere; its name is computed
# from the file alone.
( umask 077
  for k in guest client other; do head -c 32 /dev/urandom > "$OUT/key-$k"; done
  head -c 31 /dev/urandom > "$OUT/key-short"
  head -c 32 /dev/zero > "$OUT/key-zero" )
KG="$OUT/key-guest"
KC="$OUT/key-client"
KO="$OUT/key-other"
NG="$("$OUT/entity" name "$KG")"
NC="$("$OUT/entity" name "$KC")"
NO="$("$OUT/entity" name "$KO")"
[ "$NG" != "$NC" ] && [ "$NG" != "$NO" ] && [ "$NC" != "$NO" ]
if "$OUT/entity" name "$OUT/key-short" >/dev/null 2>&1; then exit 1; fi
CMD="$BASE reflect.allow=$NC"

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

# boot <command line> [key file]: the key is the file given at boot.
boot() {
    rm -f "$OUT/serial.log" "$OUT/ch.log"
    if [ -n "${2:-}" ]; then
        timeout 400 "$CH" --kernel "$OUT/reflect-net.elf" --initramfs "$2" --cpus boot=1 --memory size=512M \
            --serial "file=$OUT/serial.log" --console off \
            --net "tap=$TAP,mac=$MAC" --cmdline "$1" >"$OUT/ch.log" 2>&1 &
    else
        timeout 400 "$CH" --kernel "$OUT/reflect-net.elf" --cpus boot=1 --memory size=512M \
            --serial "file=$OUT/serial.log" --console off \
            --net "tap=$TAP,mac=$MAC" --cmdline "$1" >"$OUT/ch.log" 2>&1 &
    fi
    pid=$!
}
# Wait for the guest to say it serves QUIC.
serving() {
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
}
stop() {
    kill "$pid" 2>/dev/null || true
    wait "$pid" 2>/dev/null || true
    pid=
}
# stops <command line> <key file or ""> <serial line>: the guest says the
# line, claims no readiness, and the hypervisor exits.
stops() {
    boot "$1" "$2"
    end=$(( $(date +%s) + 90 ))
    while kill -0 "$pid" 2>/dev/null && [ "$(date +%s)" -lt "$end" ]; do sleep 0.05; done
    if kill -0 "$pid" 2>/dev/null; then
        echo "a guest that should have stopped with '$3' kept running" >&2
        exit 1
    fi
    wait "$pid" 2>/dev/null || true
    pid=
    grep -qx "reflect: $3" "$OUT/serial.log"
    if grep -q -e "reflect: ready" -e "reflect: quic" "$OUT/serial.log"; then exit 1; fi
}

# One guest has one QUIC connection. A command line that asks for the QUIC
# service and an end of the remote channel is refused before the device is
# touched, with a key and an allow-list given so that nothing else is wrong.
refused() {
    stops "$CMD $1" "$KG" "the network address is not valid"
    echo "ok   refused: reflect.quic_port with $1"
}
refused "reflect.wire_port=4446"
refused "reflect.peer=192.168.249.3:4446"

# No list of names, no QUIC: there is no setting that admits everyone.
stops "$BASE" "$KG" "the network address is not valid"
echo "ok   refused: reflect.quic_port with no reflect.allow"

# No key, no QUIC: the guest has no other key to fall back to.
stops "$CMD" "" "no entity key"
echo "ok   a guest with no key serves no QUIC"
stops "$CMD" "$OUT/key-short" "the entity key is not 32 bytes"
echo "ok   a guest given 31 bytes serves no QUIC"
stops "$CMD" "$OUT/key-zero" "the entity key is all zero"
echo "ok   a guest given 32 zero bytes serves no QUIC"

fact="$ROOT/examples/factorial.hom"
fore="$ROOT/examples/forever.hom"
"$OUT/reply" run 100000000 "$fact" > "$OUT/factorial.reply"
"$OUT/reply" run 5000 "$fore" > "$OUT/budget.reply"

# Stream data in an Initial packet, whose keys anyone can make. This guest
# stops at its first run request (reflect.hook=alloc). A first flight with a
# run request in a STREAM frame beside its ClientHello must leave it up; the
# allowed client's request then stops it, so the hook was armed.
boot "$CMD reflect.hook=alloc" "$KG"
serving
"$OUT/quic-client" "$IP" "$QPORT" 100000000 "$fact" "$KC" "$NG" early
sleep 3
if ! kill -0 "$pid" 2>/dev/null || grep -q "allocation failure" "$OUT/serial.log"; then
    echo "the guest acted on stream data in an Initial packet" >&2
    cat "$OUT/serial.log" >&2
    exit 1
fi
"$OUT/quic-client" "$IP" "$QPORT" 100000000 "$fact" "$KC" "$NG" > /dev/null || true
end=$(( $(date +%s) + 30 ))
while kill -0 "$pid" 2>/dev/null && [ "$(date +%s)" -lt "$end" ]; do sleep 0.05; done
if kill -0 "$pid" 2>/dev/null; then exit 1; fi
wait "$pid" 2>/dev/null || true
pid=
grep -q "reflect: allocation failure" "$OUT/serial.log"
echo "ok   stream data in an Initial packet is not acted on; the allowed client's request is"

# Two keys are two identities: the same image with another key has another
# name, the one computed from its file, and the client that expects the
# first guest refuses it.
boot "$CMD" "$KO"
serving
grep -qx "reflect: entity $NO" "$OUT/serial.log"
"$OUT/quic-client" "$IP" "$QPORT" 100000000 "$fact" "$KC" "$NG" wrong
stop
echo "ok   a guest with another key has another name, and the client that expects the first refuses it"

boot "$CMD" "$KG"
serving
grep -qx "reflect: entity $NG" "$OUT/serial.log"
echo "ok   the guest's name is the one computed from its key file"

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
    "$OUT/quic-client" "$IP" "$QPORT" 100000000 "$fact" "$KC" "$NG" "$@" > "$OUT/quic-$name.frame"
    body "$OUT/quic-$name.frame" "$OUT/quic-$name.body"
    cmp -s "$OUT/quic-$name.body" "$OUT/factorial.reply"
    kind "$OUT/quic-$name.frame"
}

factorial fact
echo "ok   factorial over QUIC equals the Linux process"

"$OUT/quic-client" "$IP" "$QPORT" 5000 "$fore" "$KC" "$NG" > "$OUT/quic-budget.frame"
body "$OUT/quic-budget.frame" "$OUT/quic-budget.body"
cmp -s "$OUT/quic-budget.body" "$OUT/budget.reply"
kind "$OUT/quic-budget.frame"
echo "ok   a 5000-step budget reply equals the Linux process"

# The guest stayed up: a new handshake still returns factorial.
factorial fact2
echo "ok   factorial again on a new handshake"

"$OUT/quic-client" "$IP" "$QPORT" 100000000 "$fact" "$KC" "$NO" wrong
echo "ok   a client that expects another name refuses the guest"

# The refused handshake was left unfinished. It holds a first-flight slot
# until the cap; this one takes another at once, and loses and reorders
# datagrams.
factorial loss loss
echo "ok   factorial after an abandoned handshake, with loss and reordering"

# A client whose key is not on the guest's list: it accepts the guest, gets
# no reply and sees its flight given up. The guest lets the refused
# connection go at once: the allowed client, started 0.1 s later, while the
# first is still resending, is served within a second.
"$OUT/quic-client" "$IP" "$QPORT" 100000000 "$fact" "$KO" "$NG" denied > "$OUT/quic-denied.frame" &
dpid=$!
sleep 0.1
t0=$(date +%s%N)
factorial after-denied
t1=$(date +%s%N)
took=$(( (t1 - t0) / 1000000 ))
if [ "$took" -ge 1000 ]; then
    echo "the allowed client waited $took ms behind a refused one" >&2
    exit 1
fi
if ! wait "$dpid"; then
    echo "a client the guest does not allow was not refused" >&2
    exit 1
fi
[ ! -s "$OUT/quic-denied.frame" ]
echo "     the allowed client was served in $took ms"
echo "ok   a client the guest does not allow is refused, and the next client is served at once"

# Plain UDP beside QUIC: a ping to reflect.port is not answered.
python3 - "$IP" "$PORT" <<'PY'
import socket, struct, sys
s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
s.settimeout(2.0)
s.sendto(b"RFL1" + bytes([2, 0, 0, 0]) + struct.pack("!QQ", 9, 0), (sys.argv[1], int(sys.argv[2])))
try:
    s.recvfrom(2048)
except socket.timeout:
    sys.exit(0)
sys.exit("a guest with a QUIC port answered a ping on its plain UDP port")
PY
echo "ok   a ping to the plain UDP port of a QUIC guest is not answered"

# A second host at another address, during and after an exchange.
factorial spoof spoof "$OTHERIP"
echo "ok   factorial with a second address sending garbage and a new Initial; that address heard only its own handshake"

factorial fact3
echo "ok   factorial again after the garbage"

# A real first flight with a bad UDP checksum is dropped; the same bytes with
# a good one are answered.
"$OUT/quic-client" "$IP" "$QPORT" 1 "$fact" "$KC" "$NG" initial > "$OUT/quic-initial.bin"
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

# The UDP payload bytes of the first datagram the guest sends back, or 0.
def answered(seconds):
    end = time.time() + seconds
    while time.time() < end:
        s.settimeout(max(0.01, end - time.time()))
        try:
            pkt = s.recv(4096)
        except socket.timeout:
            return 0
        if len(pkt) >= 42 and pkt[12:14] == b"\x08\x00" and pkt[23] == 17 and pkt[26:30] == guest_ip \
                and struct.unpack("!H", pkt[34:36])[0] == qport and struct.unpack("!H", pkt[36:38])[0] == sport:
            return struct.unpack("!H", pkt[38:40])[0] - 8
    return 0

send(bad=True)
if answered(1.0):
    sys.exit("a first flight with a bad UDP checksum was answered")
send(bad=False)
got = answered(3.0)
if not got:
    sys.exit("the same first flight with a good checksum was not answered")
# RFC 9000 section 14.1: a datagram with a server's ack-eliciting Initial is
# expanded to at least 1200 bytes.
if got < 1200:
    sys.exit("the answer to a first flight is %d bytes, under 1200" % got)
print("     the answer to a first flight of %d bytes is %d bytes" % (len(payload), got))
PY
echo "ok   a first flight with a bad UDP checksum is dropped; with a good one it is answered in 1200 bytes or more"

# That handshake is left unfinished too; the guest still serves.
factorial fact4
echo "ok   factorial after the unfinished raw handshake"

# watch <mode>: listen on the TAP for what the guest sends from its QUIC port.
watch() {
    sudo -n python3 - "$TAP" "$OUT/quic-initial.bin" "$QPORT" "$1" "$HOSTIP" "$FORGEDIP" <<'PY'
import socket, struct, sys, time
tap, path, qport, mode = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
host_ip = bytes(int(x) for x in sys.argv[5].split("."))
forged_ip = bytes(int(x) for x in sys.argv[6].split("."))
payload = open(path, "rb").read()
s = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(0x0003))
s.bind((tap, 0))
host_mac = s.getsockname()[4]
guest_mac = bytes.fromhex("020000000002")
guest_ip = bytes([192, 168, 249, 2])

def csum(data):
    if len(data) % 2:
        data += b"\x00"
    t = sum(struct.unpack("!%dH" % (len(data) // 2), data))
    while t >> 16:
        t = (t & 0xffff) + (t >> 16)
    return (~t) & 0xffff

def send(src_ip, sport):
    ulen = 8 + len(payload)
    ip = bytearray(20)
    ip[0] = 0x45
    ip[2:4] = struct.pack("!H", 20 + ulen)
    ip[8] = 64
    ip[9] = 17
    ip[12:16] = src_ip
    ip[16:20] = guest_ip
    ip[10:12] = struct.pack("!H", csum(bytes(ip)))
    u = bytearray(ulen)
    u[0:2] = struct.pack("!H", sport)
    u[2:4] = struct.pack("!H", qport)
    u[4:6] = struct.pack("!H", ulen)
    u[8:] = payload
    cs = csum(src_ip + guest_ip + b"\x00\x11" + struct.pack("!H", ulen) + bytes(u)) or 0xffff
    u[6:8] = struct.pack("!H", cs)
    s.send(guest_mac + host_mac + b"\x08\x00" + bytes(ip) + bytes(u))

# What the guest sends from its QUIC port for `seconds`: (when, to, port,
# payload bytes). `todo` is a list of (when, call) run on the way.
def watch(seconds, todo=()):
    todo = sorted(todo, key=lambda e: e[0])
    start = time.time()
    seen = []
    while True:
        now = time.time() - start
        while todo and todo[0][0] <= now:
            todo.pop(0)[1]()
        if now >= seconds:
            return seen
        wait = seconds - now
        if todo:
            wait = min(wait, todo[0][0] - now)
        s.settimeout(max(0.005, wait))
        try:
            pkt = s.recv(4096)
        except socket.timeout:
            continue
        if len(pkt) >= 42 and pkt[12:14] == b"\x08\x00" and pkt[23] == 17 and pkt[26:30] == guest_ip \
                and struct.unpack("!H", pkt[34:36])[0] == qport:
            ulen = struct.unpack("!H", pkt[38:40])[0]
            seen.append((time.time() - start, pkt[30:34], struct.unpack("!H", pkt[36:38])[0],
                         ulen - 8, pkt[42:34 + ulen]))

def var(b, o):
    w = 1 << (b[o] >> 6)
    v = b[o] & 0x3f
    for i in range(1, w):
        v = (v << 8) | b[o + i]
    return v, w

# Whether a datagram carries a 1-RTT packet: its long-header packets are
# stepped over by their Length fields, which header protection leaves alone.
def one_rtt(d):
    i = 0
    while i < len(d):
        if d[i] & 0x80 == 0:
            return True
        o = i + 23
        if d[i] & 0x30 == 0:
            t, w = var(d, o)
            o += w + t
        n, w = var(d, o)
        i = o + w + n
    return False

if mode == "once":
    # An exchange runs while this listens. The guest sends the reply, the
    # only 1-RTT packet it has, and the client acknowledges it: no resend in
    # the time the guest would take to give a reply up.
    seen = watch(10.0)
    replies = [e for e in seen if one_rtt(e[4])]
    if not replies:
        sys.exit("no reply was seen")
    if len(replies) != 1:
        sys.exit("the guest sent the reply %d times, the last at %.1f s"
                 % (len(replies), replies[-1][0] - replies[0][0]))
    print("     the reply went out once; %d datagrams in all" % len(seen))
elif mode == "quiet":
    # The exchange before this left a reply the client never acknowledged.
    seen = watch(11.0)
    if not seen:
        sys.exit("the guest did not resend a reply nobody acknowledged")
    if len(seen) > 9 or seen[-1][0] > 8.0:
        sys.exit("the guest went on resending: %d datagrams in 11 s, the last at %.1f s" % (len(seen), seen[-1][0]))
    print("     %d more datagrams in 11 s, the last at %.1f s" % (len(seen), seen[-1][0]))
elif mode == "forged":
    # A real first flight with a source address nobody is at, and then the
    # same bytes again from another address, which must add nothing.
    send(forged_ip, 9300)
    again = lambda: send(host_ip, 9301)
    # Within the cap: after it the same bytes are a first flight like any.
    seen = watch(8.0, [(0.5, again), (1.0, again), (1.5, again)])
    there = [e for e in seen if e[1] == forged_ip and e[2] == 9300]
    if len(there) < 2:
        sys.exit("the guest did not answer the first flight and resend the answer")
    total = sum(e[3] for e in there)
    if total > 3 * len(payload):
        sys.exit("a first flight of %d bytes from a forged address drew %d bytes in %d datagrams"
                 % (len(payload), total, len(there)))
    if len(seen) != len(there):
        sys.exit("the guest sent to an address other than the first flight's")
    small = [e[3] for e in there if e[3] < 1200]
    if small:
        sys.exit("the guest answered a first flight in datagrams under 1200 bytes: %s" % small)
    print("     %d datagrams and %d bytes for a first flight of %d bytes" % (len(there), total, len(payload)))
else:
    sys.exit("watch: once, quiet or forged")
PY
}

# A client that acknowledges the reply is sent it once.
watch once > "$OUT/once.txt" 2>&1 &
wpid=$!
sleep 1
factorial once
if ! wait "$wpid"; then
    cat "$OUT/once.txt" >&2
    exit 1
fi
cat "$OUT/once.txt"
echo "ok   a reply the client acknowledges is sent once"

# A client that takes the reply and leaves without acknowledging it.
factorial silent silent
echo "ok   factorial for a client that does not acknowledge the reply"

# Nobody acknowledged that reply: the client had it and left. The guest
# resends it a bounded number of times and then says nothing.
watch quiet
echo "ok   a reply nobody acknowledges is resent and then given up"

# A first flight from an address nobody is at draws at most three times its
# bytes, also when the same flight comes again from somewhere else.
watch forged
echo "ok   a first flight from a forged address draws at most three times its bytes"

# The forged handshake is left unfinished; the guest still serves.
factorial fact5
echo "ok   factorial after the forged first flight"

if grep -v -e "^reflect: entity $NG\$" -e "^reflect: ready $IP:$PORT\$" -e "^reflect: quic $QPORT\$" "$OUT/serial.log" | grep -q .; then
    echo "the guest said something unexpected:" >&2
    cat "$OUT/serial.log" >&2
    exit 1
fi
stop

# The same key is the same identity: started again, the guest has the same
# name and the client that expects it is served.
boot "$CMD" "$KG"
serving
grep -qx "reflect: entity $NG" "$OUT/serial.log"
factorial again
echo "ok   the same key started again is the same name, and the same client is served"

# The client Mjolnir vendors (quic.zig of e9a4c86, unmodified), which drops
# a Retry, is served as before while a first-flight slot is free.
"$OUT/quic-client-e9a4c86" "$IP" "$QPORT" 100000000 "$fact" "$KC" "$NG" > "$OUT/quic-old.frame"
body "$OUT/quic-old.frame" "$OUT/quic-old.body"
cmp -s "$OUT/quic-old.body" "$OUT/factorial.reply"
kind "$OUT/quic-old.frame"
echo "ok   the client of e9a4c86, which Mjolnir vendors, is served while a first-flight slot is free"

# ms <command...>: run it, and print how many milliseconds it took.
ms() {
    s0=$(date +%s%N)
    "$@"
    echo $(( ($(date +%s%N) - s0) / 1000000 ))
}

# A flood from the second address, with a key on no list: new first flights,
# one first flight again and again, and every datagram of a finished
# exchange of the allowed client's. Five allowed clients in turn, each
# served within a second. FLOOD_RATE is datagrams a second (0: as fast as
# the flooder can). The default, 4000, is under the 5000 this mix was seen
# to leave the guest keeping up with on morphie (unikernel/README.md); a
# faster flood is dropped by the host's TAP queue without regard to sender.
factorial kept keep "$OUT/kept.bin"
"$OUT/quic-client" "$IP" "$QPORT" 1 "$fact" "$KO" "$NG" flood "$OTHERIP" 12 "${FLOOD_RATE:-4000}" "$OUT/kept.bin" \
    2> "$OUT/flood.txt" &
fpid=$!
sleep 1.5
i=1
while [ "$i" -le 5 ]; do
    took=$(ms factorial "flood$i" | tail -n 1)
    echo "     allowed client $i served in $took ms under the flood"
    if [ "$took" -ge 1000 ]; then
        echo "an allowed client waited $took ms under the flood" >&2
        exit 1
    fi
    i=$((i + 1))
done
wait "$fpid"
sed 's/^/     /' "$OUT/flood.txt"
grep -q "heard [1-9][0-9]* Retries" "$OUT/flood.txt"
echo "ok   while a second address floods the guest, five allowed clients are each served within a second"

# Let the flood's connections reach the cap. Then four clients with a key on
# no list take the first-flight pool, show their address and keep sending
# Handshake packets that open, never a Certificate, for 6 seconds. An
# allowed client that answers a Retry is served at once; the client of
# e9a4c86, which does not, only once the cap has freed a slot, while the
# stalled clients still send.
sleep 3
spids=
for k in 1 2 3 4; do
    "$OUT/quic-client" "$IP" "$QPORT" 1 "$fact" "$KO" "$NG" stall &
    spids="$spids $!"
    sleep 0.05
done
sleep 0.3
( ms "$OUT/quic-client-e9a4c86" "$IP" "$QPORT" 100000000 "$fact" "$KC" "$NG" > "$OUT/quic-capped.frame" ) > "$OUT/capped.ms" &
opid=$!
took=$(ms factorial retried | tail -n 1)
if [ "$took" -ge 1000 ]; then
    echo "the allowed client waited $took ms behind stalled clients" >&2
    exit 1
fi
wait "$opid" || { echo "the client that ignores a Retry was not served" >&2; exit 1; }
old=$(tail -n 1 "$OUT/capped.ms")
body "$OUT/quic-capped.frame" "$OUT/quic-capped.body"
cmp -s "$OUT/quic-capped.body" "$OUT/factorial.reply"
if [ "$old" -lt 1500 ] || [ "$old" -gt 6000 ]; then
    echo "the client that ignores a Retry was served in $old ms, not between 1.5 and 6 s" >&2
    exit 1
fi
for p in $spids; do wait "$p"; done
echo "     an allowed client in $took ms; the client of e9a4c86 in $old ms"
echo "ok   stalled clients on no list hold the first-flight pool no longer than the cap"

if grep -v -e "^reflect: entity $NG\$" -e "^reflect: ready $IP:$PORT\$" -e "^reflect: quic $QPORT\$" "$OUT/serial.log" | grep -q .; then
    echo "the guest said something unexpected:" >&2
    cat "$OUT/serial.log" >&2
    exit 1
fi
stop
echo "quic guest ok"
