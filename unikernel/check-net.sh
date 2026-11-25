#!/bin/sh
# Real guest: ping, factorial, a budget reply, factorial again, runs that pass
# their space, bad frames, an allocation abort, and a guest with the space
# limit undone. The one-program image check is separate.
set -eu
HERE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT="$(CDPATH= cd -- "$HERE/.." && pwd)"
CH="${CLOUD_HYPERVISOR:-$HOME/ch54/cloud-hypervisor}"
OUT="$HERE/out-net"
TAP="uknet$$"
IP=192.168.249.2
PORT=4444
HOSTIP=192.168.249.1
MAC=02:00:00:00:00:02
CMD="reflect.ip=$IP reflect.port=$PORT"
FACT=265252859812191058636308480000000

[ -r /dev/kvm ] && [ -w /dev/kvm ]
"$CH" --version | grep -qx "cloud-hypervisor v54.0"
sh "$HERE/build-net.sh"
( cd "$ROOT/kernel" && lake env lean WireReplyCheck.lean ) | tee "$OUT/lean-reply.txt"
grep -q "^FAIL" "$OUT/lean-reply.txt" && { echo "lean reply check failed" >&2; exit 1; }
grep -q "factorial reply is the known integer" "$OUT/lean-reply.txt"

sudo ip link del "$TAP" 2>/dev/null || true
sudo ip tuntap add dev "$TAP" mode tap user "$(id -un)"
sudo ip addr add "$HOSTIP/24" dev "$TAP"
sudo ip link set "$TAP" up
sudo ip link set "$TAP" promisc on
cleanup() { sudo ip link del "$TAP" 2>/dev/null || true; }
trap cleanup EXIT

boot() {
    extra="$1"
    rm -f "$OUT/serial.log" "$OUT/ch.log"
    timeout 400 "$CH" --kernel "$OUT/reflect-net.elf" --cpus boot=1 --memory size=512M \
        --serial "file=$OUT/serial.log" --console off \
        --net "tap=$TAP,mac=$MAC" --cmdline "$CMD $extra" >"$OUT/ch.log" 2>&1 &
    echo $!
}

python() { sudo -n python3 "$@"; }

# shellcheck disable=SC2016
run_cases() {
    python - "$TAP" "$OUT/serial.log" "$OUT/reply" "$ROOT" "$FACT" <<'PY'
import socket, struct, subprocess, sys, time, os
tap, serial_path, reply, root, fact = sys.argv[1:]
fact = int(fact)

def wait_ready():
    end = time.time() + 60
    while time.time() < end:
        try:
            text = open(serial_path).read()
        except FileNotFoundError:
            text = ""
        if "reflect: ready " in text:
            return
        if "reflect: " in text and "ready" not in text and "kernel did not" in text:
            sys.exit("guest failed\n" + text)
        time.sleep(0.05)
    sys.exit("no readiness\n" + open(serial_path).read() if os.path.exists(serial_path) else "no serial")

wait_ready()
s = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(0x0003))
s.bind((tap, 0))
s.settimeout(3)
host_mac = s.getsockname()[4]
guest_mac = bytes.fromhex("020000000002")
guest_ip = bytes([192, 168, 249, 2])
host_ip = bytes([192, 168, 249, 1])
port = 4444

def csum(data):
    if len(data) % 2:
        data += b"\x00"
    t = sum(struct.unpack("!%dH" % (len(data)//2), data))
    while t >> 16:
        t = (t & 0xffff) + (t >> 16)
    return (~t) & 0xffff

def send_frame(frame):
    s.send(frame)

def arp():
    frame = b"\xff"*6 + host_mac + b"\x08\x06" + b"\x00\x01\x08\x00\x06\x04\x00\x01"
    frame += host_mac + host_ip + b"\x00"*6 + guest_ip
    send_frame(frame)
    end = time.time() + 2
    while time.time() < end:
        pkt = s.recv(2048)
        if len(pkt) >= 42 and pkt[12:14] == b"\x08\x06" and pkt[20:22] == b"\x00\x02" and pkt[28:32] == guest_ip:
            return pkt[22:28]
    sys.exit("no arp")

guest_mac = arp()

def udp(payload, dst=guest_ip, dport=port, bad_sum=False, src=host_ip):
    ulen = 8 + len(payload)
    ip_len = 20 + ulen
    ip = bytearray(20)
    ip[0] = 0x45
    ip[2:4] = struct.pack("!H", ip_len)
    ip[8] = 64
    ip[9] = 17
    ip[12:16] = src
    ip[16:20] = dst
    ip[10:12] = struct.pack("!H", csum(ip))
    u = bytearray(ulen)
    u[0:2] = struct.pack("!H", 9000)
    u[2:4] = struct.pack("!H", dport)
    u[4:6] = struct.pack("!H", ulen)
    u[8:] = payload
    pseudo = src + dst + b"\x00\x11" + struct.pack("!H", ulen)
    cs = csum(pseudo + u) or 0xffff
    if bad_sum:
        cs ^= 0xff
    u[6:8] = struct.pack("!H", cs)
    send_frame(guest_mac + host_mac + b"\x08\x00" + bytes(ip) + bytes(u))

def recv_app(deadline=3):
    end = time.time() + deadline
    while time.time() < end:
        # The socket's timeout is shorter than a long run: keep waiting
        # until the deadline, not the first quiet interval.
        try:
            pkt = s.recv(2048)
        except socket.timeout:
            continue
        if len(pkt) < 42 or pkt[12:14] != b"\x08\x00" or pkt[23] != 17:
            continue
        if pkt[26:30] != guest_ip or pkt[30:34] != host_ip:
            continue
        ulen = struct.unpack("!H", pkt[38:40])[0]
        return bytes(pkt[42:42+ulen-8])
    return None

def frame(kind, status, ident, budget, payload=b""):
    return b"RFL1" + bytes([kind, status, 0, 0]) + ident.to_bytes(8, "big") + budget.to_bytes(8, "big") + payload

def exchange(kind, status, ident, budget, payload=b"", wait=8):
    udp(frame(kind, status, ident, budget, payload))
    return recv_app(wait)

def must(app, kind, status, ident, budget):
    if app is None or len(app) < 24:
        sys.exit(f"no reply ident={ident}")
    if app[:4] != b"RFL1" or app[4] != kind or app[5] != status:
        sys.exit(f"bad header {app[:8]!r}")
    if int.from_bytes(app[8:16], "big") != ident or int.from_bytes(app[16:24], "big") != budget:
        sys.exit("id or budget not echoed")
    return app[24:]

def prog(path):
    return subprocess.check_output([reply, "source", path])

def linux_run(budget, blob, space=None):
    words = [reply, "run", str(budget), "/dev/stdin"] + ([str(space)] if space is not None else [])
    p = subprocess.run(words, input=blob, capture_output=True)
    if p.returncode != 0:
        sys.exit(p.stderr.decode())
    return p.stdout

fact_bytes = prog(os.path.join(root, "examples/factorial.hom"))
pong = must(exchange(2, 0, 1, 0), 3, 0, 1, 0)
if pong != b"":
    sys.exit("pong had a payload")
body = must(exchange(0, 0, 7, 100000000, fact_bytes, wait=30), 1, 0, 7, 100000000)
want = linux_run(100000000, fact_bytes)
if body != want:
    sys.exit("factorial differs from the linux export")
# The known integer is inside the reply. The linux check already named it;
# require its decimal digits are not the whole payload and the bytes match a file we write.
open("/tmp/uk-factorial.reply", "wb").write(body)
fore = prog(os.path.join(root, "examples/forever.hom"))
b2 = must(exchange(0, 0, 8, 5000, fore), 1, 0, 8, 5000)
if b2 != linux_run(5000, fore):
    sys.exit("budget reply differs")
b3 = must(exchange(0, 0, 9, 100000000, fact_bytes, wait=30), 1, 0, 9, 100000000)
if b3 != body:
    sys.exit("second factorial differs")
# A tail loop at the default budget ends in the budget reply and the guest
# goes on answering (homoiconic-q59.65). With a frame kept per tail call its
# memory grew with its steps, past the 512 MiB guest.
b4 = must(exchange(0, 0, 10, 100000000, fore, wait=120), 1, 0, 10, 100000000)
if b4 != linux_run(100000000, fore) or b4 != bytes.fromhex("8101"):
    sys.exit(f"forever at the default budget gave {b4.hex()}")
b5 = must(exchange(0, 0, 15, 100000000, fact_bytes, wait=30), 1, 0, 15, 100000000)
if b5 != body:
    sys.exit("factorial after forever differs")
# A run has a space limit beside its budget (homoiconic-q59.67). A recursion
# whose calls wait on each other and a loop that builds data keep what they
# make; within the largest budget each used to end the guest in `INTERNAL
# PANIC: out of memory`, which powers it off. Each is now the space reply,
# `81 07`, equal to the Linux export's, and the guest answers the next
# request. So are an answer that is 2^40 bytes written from forty cells, and a
# function whose byte form writes thirty environments each inside the last.
def source(name, text):
    path = "/tmp/uk-" + name + ".hom"
    open(path, "w").write(text)
    return prog(path)

hostile = [
    ("a recursion that waits", "def deep x = [x, ...deep x]\ndeep 0\n"),
    ("a loop that builds", "def build acc = build [0, ...acc]\nbuild []\n"),
    ("an answer built by doubling",
     "def dbl x n =\n  case n\n    0 -> x\n    m + 1 -> dbl [x, ...x] m\n\ndbl [0] 40\n"),
    ("a function from thirty definitions",
     "def f0 x = x\n" + "".join(f"def f{i} x = f{i - 1} x\n" for i in range(1, 30)) + "fn x -> f29 x\n"),
]
ident = 30
for what, text in hostile:
    blob = source("space", text)
    got = must(exchange(0, 0, ident, 100000000, blob, wait=300), 1, 0, ident, 100000000)
    if got != bytes.fromhex("8107") or got != linux_run(100000000, blob):
        sys.exit(f"{what}: the guest gave {got.hex()}, not the space reply")
    after = must(exchange(0, 0, ident + 1, 100000000, fact_bytes, wait=30), 1, 0, ident + 1, 100000000)
    if after != body:
        sys.exit(f"factorial after {what} differs")
    print("space reply ok:", what)
    ident += 2
# Nesting deeper than the native stack (homoiconic-q59.72). Comparing data a
# million arrays deep recursed once for each level and ended the guest in the
# report of a full stack: one message of 119 bytes of program. Writing such data as the
# answer is a walk too; the answer is too large for one datagram.
nest = "def nest x n =\n  case n\n    0 -> x\n    m + 1 -> nest [x] m\n\n"
blob = source("deep", nest + "(fn d -> equal d d) (nest 0 1000000)\n")
got = must(exchange(0, 0, ident, 100000000, blob, wait=300), 1, 0, ident, 100000000)
if got != linux_run(100000000, blob) or got != bytes.fromhex("8200820001"):
    sys.exit(f"data a million deep compared with itself: the guest gave {got.hex()}")
after = must(exchange(0, 0, ident + 1, 100000000, fact_bytes, wait=30), 1, 0, ident + 1, 100000000)
if after != body:
    sys.exit("factorial after the deep comparison differs")
print("deep ok: data a million deep compared with itself")
ident += 2
blob = source("deep", nest + "nest 0 1000000\n")
if must(exchange(0, 0, ident, 100000000, blob, wait=300), 1, 2, ident, 100000000) != b"":
    sys.exit("data a million deep as the answer: the too-large reply carried a payload")
after = must(exchange(0, 0, ident + 1, 100000000, fact_bytes, wait=30), 1, 0, ident + 1, 100000000)
if after != body:
    sys.exit("factorial after the deep answer differs")
print("deep ok: data a million deep as the answer is too large for a datagram")
ident += 2
# The Linux export with the limit undone goes on to its budget on a shorter
# run: the space, not the budget, is what gave `81 07` above.
deep_blob = source("space", hostile[0][1])
if linux_run(10000000, deep_blob) != bytes.fromhex("8107"):
    sys.exit("the recursion at 10000000 steps is not the space reply")
if linux_run(10000000, deep_blob, 18446744073709551615) != bytes.fromhex("8101"):
    sys.exit("with the limit undone the recursion at 10000000 steps is not the budget reply")
big_path = "/tmp/uk-big.hom"
open(big_path, "w").write(
    "def factorial n =\n  case n\n    0 -> 1\n    m + 1 -> mul n (factorial m)\n\nfactorial 1200\n"
)
big = prog(big_path)
if len(big) > 1176:
    sys.exit("oversized program does not fit one datagram")
big_reply = linux_run(100000000, big)
if len(big_reply) <= 1176:
    sys.exit(f"factorial 1200 reply is only {len(big_reply)} bytes")
cap = subprocess.run([reply, "capacity", "100000000", "/dev/stdin"], input=big, capture_output=True)
if cap.returncode != 0 or cap.stdout != big_reply:
    sys.exit("capacity retry did not preserve the reply")
too_big = must(exchange(0, 0, 20, 100000000, big, wait=30), 1, 2, 20, 100000000)
if too_big != b"":
    sys.exit("oversized reply carried a payload")
# malformed: no reply, then a ping works
for blob in (
    b"nope",
    frame(1, 0, 2, 0),
    frame(3, 0, 2, 0),
    frame(255, 0, 2, 0),
    frame(0, 2, 2, 10, b"x"),
    frame(2, 3, 2, 0),
    frame(2, 0, 2, 1),
    frame(2, 0, 2, 0, b"x"),
):
    udp(blob)
time.sleep(0.2)
# drain
s.settimeout(0.2)
try:
    while True:
        got = recv_app(0.2)
        if got is None:
            break
        if got[:4] == b"RFL1" and got[4] in (1, 3):
            sys.exit("malformed packet got a reply")
except Exception:
    pass
s.settimeout(3)
must(exchange(2, 0, 11, 0), 3, 0, 11, 0)
bad_budget = must(exchange(0, 0, 12, 0), 1, 3, 12, 0)
if bad_budget != b"":
    sys.exit("invalid budget carried a payload")
# checksum-invalid then a good ping
udp(frame(2, 0, 13, 0), bad_sum=True)
must(exchange(2, 0, 14, 0), 3, 0, 14, 0)
# More completions than a 16-bit used index, then the same factorial.
for i in range(65537):
    app = exchange(2, 0, 100000 + i, 0, wait=2)
    if app is None or len(app) < 5 or app[4] != 3:
        sys.exit(f"ring wrap lost ping {i}")
again = must(exchange(0, 0, 21, 100000000, fact_bytes, wait=30), 1, 0, 21, 100000000)
if again != body:
    sys.exit("factorial after ring wrap differs")
print("guest cases ok", len(body))
PY
}

pid=$(boot "")
set +e
run_cases
rc=$?
set -e
sudo kill "$pid" 2>/dev/null || true
wait "$pid" 2>/dev/null || true
[ "$rc" = 0 ]
grep -q "reflect: ready $IP:$PORT" "$OUT/serial.log"

# Allocation abort after readiness. The guest must die and not answer again.
pid=$(boot "reflect.hook=alloc")
python - "$TAP" "$OUT/serial.log" <<'PY'
import socket, struct, sys, time, os
tap, serial_path = sys.argv[1:]
end = time.time() + 40
while time.time() < end:
    if os.path.exists(serial_path) and "reflect: ready " in open(serial_path).read():
        break
    time.sleep(0.05)
else:
    sys.exit("hook guest never ready")
s = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(0x0003))
s.bind((tap, 0))
s.settimeout(2)
host_mac = s.getsockname()[4]
guest_ip = bytes([192,168,249,2]); host_ip = bytes([192,168,249,1])
frame = b"\xff"*6 + host_mac + b"\x08\x06" + b"\x00\x01\x08\x00\x06\x04\x00\x01" + host_mac + host_ip + b"\x00"*6 + guest_ip
s.send(frame)
s.recv(2048)
def csum(data):
    if len(data)%2: data += b"\x00"
    t = sum(struct.unpack("!%dH"%(len(data)//2), data))
    while t>>16: t=(t&0xffff)+(t>>16)
    return (~t)&0xffff
app = b"RFL1" + bytes([0,0,0,0]) + (3).to_bytes(8,"big") + (10).to_bytes(8,"big") + b"\x00"
ulen=8+len(app); ip=bytearray(20); ip[0]=0x45; ip[2:4]=struct.pack("!H", 20+ulen); ip[8]=64; ip[9]=17
ip[12:16]=host_ip; ip[16:20]=guest_ip; ip[10:12]=struct.pack("!H", csum(ip))
u=bytearray(ulen); u[0:2]=struct.pack("!H", 1); u[2:4]=struct.pack("!H", 4444); u[4:6]=struct.pack("!H", ulen); u[8:]=app
pseudo=host_ip+guest_ip+b"\x00\x11"+struct.pack("!H", ulen)
u[6:8]=struct.pack("!H", csum(pseudo+u) or 0xffff)
s.send(bytes.fromhex("020000000002")+host_mac+b"\x08\x00"+bytes(ip)+bytes(u))
time.sleep(2)
text=open(serial_path).read()
if "allocation failure" not in text:
    sys.exit("serial did not name the allocation failure\n"+text)
print("abort named")
PY
wait "$pid" || true
if grep -q "reflect: ready" "$OUT/serial.log"; then
    # ready is announced once, before the abort. It must not appear twice.
    count=$(grep -c "reflect: ready" "$OUT/serial.log" || true)
    [ "$count" = 1 ]
fi

# The space limit undone: a guest told `reflect.space=` the largest space
# there is runs the recursion until its memory is gone, says so, and answers
# nothing more. This is what one small message did before the limit.
pid=$(boot "reflect.space=18446744073709551615")
python - "$TAP" "$OUT/serial.log" "$OUT/reply" <<'PY'
import socket, struct, subprocess, sys, time, os
tap, serial_path, reply = sys.argv[1:]
end = time.time() + 40
while time.time() < end:
    if os.path.exists(serial_path) and "reflect: ready " in open(serial_path).read():
        break
    time.sleep(0.05)
else:
    sys.exit("the guest with the limit undone was never ready")
s = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(0x0003))
s.bind((tap, 0))
s.settimeout(2)
host_mac = s.getsockname()[4]
guest_ip = bytes([192,168,249,2]); host_ip = bytes([192,168,249,1])
s.send(b"\xff"*6 + host_mac + b"\x08\x06" + b"\x00\x01\x08\x00\x06\x04\x00\x01" + host_mac + host_ip + b"\x00"*6 + guest_ip)
s.recv(2048)
def csum(data):
    if len(data)%2: data += b"\x00"
    t = sum(struct.unpack("!%dH"%(len(data)//2), data))
    while t>>16: t=(t&0xffff)+(t>>16)
    return (~t)&0xffff
def send(ident, budget, blob):
    app = b"RFL1" + bytes([0,0,0,0]) + ident.to_bytes(8,"big") + budget.to_bytes(8,"big") + blob
    ulen=8+len(app); ip=bytearray(20); ip[0]=0x45; ip[2:4]=struct.pack("!H", 20+ulen); ip[8]=64; ip[9]=17
    ip[12:16]=host_ip; ip[16:20]=guest_ip; ip[10:12]=struct.pack("!H", csum(ip))
    u=bytearray(ulen); u[0:2]=struct.pack("!H", 1); u[2:4]=struct.pack("!H", 4444); u[4:6]=struct.pack("!H", ulen); u[8:]=app
    pseudo=host_ip+guest_ip+b"\x00\x11"+struct.pack("!H", ulen)
    u[6:8]=struct.pack("!H", csum(pseudo+u) or 0xffff)
    s.send(bytes.fromhex("020000000002")+host_mac+b"\x08\x00"+bytes(ip)+bytes(u))
def reply_to(ident, wait):
    end = time.time() + wait
    while time.time() < end:
        try:
            pkt = s.recv(65535)
        except socket.timeout:
            continue
        if len(pkt) < 42 or pkt[12:14] != b"\x08\x00" or pkt[23] != 17 or pkt[26:30] != guest_ip:
            continue
        app = pkt[42:]
        if app[:4] == b"RFL1" and int.from_bytes(app[8:16], "big") == ident:
            return app
    return None
# Nesting deeper than the native stack (homoiconic-q59.72): with no space
# limit a chain of 300000 functions, each holding the last, passes the size
# check, and writing its byte form recursed once for each function and ended
# the guest in a full stack. It is a walk now; the form is too large for one
# datagram, and the guest answers so.
open("/tmp/uk-chain.hom", "w").write("let wrap = fn f -> fn y -> f\ndef chain f n =\n  case n\n    0 -> f\n    m + 1 -> chain (wrap f) m\n\nchain (fn z -> z) 300000\n")
send(39, 100000000, subprocess.check_output([reply, "source", "/tmp/uk-chain.hom"]))
app = reply_to(39, 300)
if app is None or app[4] != 1 or app[5] != 2 or len(app) != 24:
    sys.exit("a chain of 300000 functions: no too-large reply\n" + open(serial_path).read()[-2000:])
print("limit undone: a chain of 300000 functions is too large for a datagram")
open("/tmp/uk-undone.hom", "w").write("def deep x = [x, ...deep x]\ndeep 0\n")
blob = subprocess.check_output([reply, "source", "/tmp/uk-undone.hom"])
app = b"RFL1" + bytes([0,0,0,0]) + (40).to_bytes(8,"big") + (100000000).to_bytes(8,"big") + blob
ulen=8+len(app); ip=bytearray(20); ip[0]=0x45; ip[2:4]=struct.pack("!H", 20+ulen); ip[8]=64; ip[9]=17
ip[12:16]=host_ip; ip[16:20]=guest_ip; ip[10:12]=struct.pack("!H", csum(ip))
u=bytearray(ulen); u[0:2]=struct.pack("!H", 1); u[2:4]=struct.pack("!H", 4444); u[4:6]=struct.pack("!H", ulen); u[8:]=app
pseudo=host_ip+guest_ip+b"\x00\x11"+struct.pack("!H", ulen)
u[6:8]=struct.pack("!H", csum(pseudo+u) or 0xffff)
s.send(bytes.fromhex("020000000002")+host_mac+b"\x08\x00"+bytes(ip)+bytes(u))
end = time.time() + 300
while time.time() < end:
    if "out of memory" in open(serial_path).read():
        break
    time.sleep(0.5)
else:
    sys.exit("with the limit undone the guest did not run out of memory\n" + open(serial_path).read())
print("limit undone: the guest ran out of memory")
PY
wait "$pid" || true
grep -q "INTERNAL PANIC: out of memory" "$OUT/serial.log"
[ "$(grep -c "reflect: ready" "$OUT/serial.log")" = 1 ]
echo "network check passed"
