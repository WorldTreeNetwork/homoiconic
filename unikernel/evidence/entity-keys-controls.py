#!/usr/bin/env python3
"""Each fix of add-entity-keys undone in turn, on a copy of the tree.
usage: controls.py <tree> <self|guest|wire|all>
A control applies its patches to a copy, builds, runs the check and prints
where it failed. Every control must fail; one that passes is an error."""
import os, shutil, subprocess, sys

TREE = os.path.abspath(sys.argv[1])
WHAT = sys.argv[2] if len(sys.argv) > 2 else "all"
ENV = dict(os.environ)
ENV["PATH"] = os.path.expanduser("~/.local/share/mise/installs/zig/0.16.0/bin") + ":" + os.path.expanduser("~/.elan/bin") + ":" + ENV["PATH"]
ENV["CLOUD_HYPERVISOR"] = os.path.expanduser("~/ch54/cloud-hypervisor")

CLIENT_ALLOW = ("unikernel/quic.zig", "        if (!c.allow.has(&name)) return c.refuse();\n", "", 1)
SERVER_ALLOW = ("unikernel/quic.zig", "        if (!c.allow.has(&name)) return c.refuse();\n", "", 2)
CLIENT_CV = ("unikernel/quic.zig", '        if (!verifySig(cv, &key, "TLS 1.3, server CertificateVerify", &th)) return c.refuse();\n', "        _ = cv;\n", 1)
SERVER_CV = ("unikernel/quic.zig", '        if (!verifySig(cv, &key, "TLS 1.3, client CertificateVerify", &th)) return c.refuse();\n', "        _ = cv;\n", 1)
FIN = "        if (fin.len != 36 or !std.crypto.timing_safe.eql([32]u8, fin[4..36].*, expect)) return c.refuse();\n"
TRAIL = "        if (o != flight.len) return c.refuse(); // bytes after Finished\n"
SERVER_HEAD = """        if (!c.server or c.accepted or c.refused) return;
        const flight = c.hs_rx.buf[0..holeEnd(&c.hs_rx)];
"""
LONE_FINISHED = SERVER_HEAD + """        if (flight.len >= 36 and flight[0] == 20) {
            // The server before add-entity-keys: a Finished alone is taken.
            var tr0: [6000]u8 = undefined;
            const pre0 = c.client_hello_len + c.server_flight_len;
            @memcpy(tr0[0..c.client_hello_len], c.client_hello[0..c.client_hello_len]);
            @memcpy(tr0[c.client_hello_len..][0..c.server_flight_len], c.server_flight[0..c.server_flight_len]);
            var th0: [32]u8 = undefined;
            Sha256.hash(tr0[0..pre0], &th0, .{});
            const want0 = finished(&c.peer_hs, &th0);
            if (!std.mem.eql(u8, flight[4..36], &want0)) return c.refuse();
            installApp(c, &th0);
            c.accepted = true;
            c.pend[1].on = false;
            return;
        }
"""
EMPTY_CERT = SERVER_HEAD + """        if (flight.len >= 8 + 36 and flight[0] == 11 and read24(flight[1..]) == 4 and flight[8] == 20) {
            // A server that asks for a key and takes none, as TLS allows.
            var tr0: [6000]u8 = undefined;
            const pre0 = c.client_hello_len + c.server_flight_len;
            @memcpy(tr0[0..c.client_hello_len], c.client_hello[0..c.client_hello_len]);
            @memcpy(tr0[c.client_hello_len..][0..c.server_flight_len], c.server_flight[0..c.server_flight_len]);
            @memcpy(tr0[pre0..][0..8], flight[0..8]);
            var th0: [32]u8 = undefined;
            Sha256.hash(tr0[0 .. pre0 + 8], &th0, .{});
            const want0 = finished(&c.peer_hs, &th0);
            if (!std.mem.eql(u8, flight[12..44], &want0)) return c.refuse();
            Sha256.hash(tr0[0..pre0], &th0, .{});
            installApp(c, &th0);
            c.accepted = true;
            c.pend[1].on = false;
            return;
        }
"""
NO_REQUEST = [
    ("unikernel/quic.zig", """        const cr = switch (nextMsg(flight, &o, 13)) {
            .wait => return,
            .bad => return c.refuse(),
            .msg => |m| m,
        };
""", """        const cr: []const u8 = if (flight.len > o and flight[o] == 13) switch (nextMsg(flight, &o, 13)) {
            .wait => return,
            .bad => return c.refuse(),
            .msg => |m| m,
        } else "";
""", 1),
    ("unikernel/quic.zig", "        if (!std.mem.eql(u8, cr[4..], &cert_request)) return c.refuse();\n",
     "        if (cr.len != 0 and !std.mem.eql(u8, cr[4..], &cert_request)) return c.refuse();\n", 1),
]
SPACE_RULE = [
    ("unikernel/quic.zig", "                if (space == 2) return false;\n", "", 1),
    ("unikernel/quic.zig", "                if (space != 2) return false;\n", "", 1),
    ("unikernel/quic.zig", "            if (t == 0x06 and space < 2) {", "            if (t == 0x06) {", 1),
    ("unikernel/quic.zig", "            if (t >= 0x08 and t <= 0x0f and space == 2) {", "            if (t >= 0x08 and t <= 0x0f) {", 1),
    ("unikernel/quic.zig", "                const dest = if (space == 0) &c.init_rx else &c.hs_rx;", "                const dest = if (space == 0) &c.init_rx else &c.hs_rx;", 1),
]
ACCEPT_GATE = [
    ("unikernel/quic.zig", "                if (t & 0x01 != 0 and c.accepted) c.peer_fin = true;", "                if (t & 0x01 != 0) c.peer_fin = true;", 1),
    ("unikernel/quic.zig", "        if (!c.accepted or !c.peer_fin) return \"\";", "        if (!c.peer_fin) return \"\";", 1),
]
FIXED_SEED = """    var seed: [33]u8 = .{0} ** 33;
    const n = reflect_boot_take(&seed, seed.len);
"""

def rule(old):
    return [("unikernel/quic.zig", old, "", 1)]

SELF = [
    # (what is undone, patches, the quic-self codes that must now fail)
    ("the name's prefix has another first byte", [("unikernel/entity.zig", "const prefix = [19]u8{ 0xa2,", "const prefix = [19]u8{ 0xa3,", 1)], [0]),
    ("the client does not check the server's name against its list", [CLIENT_ALLOW], [42]),
    ("the server does not check the client's name against its list", [SERVER_ALLOW], [43]),
    ("the client does not verify the server's CertificateVerify", [CLIENT_CV], [44, 46]),
    ("the server does not verify the client's CertificateVerify", [SERVER_CV], [45, 47]),
    ("the server takes a Finished alone, as before this change", [("unikernel/quic.zig", SERVER_HEAD, LONE_FINISHED, 1)], [48]),
    ("the client does not check the server's Finished", [("unikernel/quic.zig", FIN, "        _ = fin;\n        _ = expect;\n", 1)], [49]),
    ("the server does not check the client's Finished", [("unikernel/quic.zig", FIN, "        _ = fin;\n        _ = expect;\n", 2)], [50]),
    ("the server takes an empty Certificate and no CertificateVerify", [("unikernel/quic.zig", SERVER_HEAD, EMPTY_CERT, 1)], [51]),
    ("a Certificate may hold more after its first entry", rule("    if (o != body.len) return null; // rule: one entry\n"), [52, 53]),
    ("a Certificate's context may be filled", rule("    if (ctx != 0) return null; // rule: no context\n"), [54, 55]),
    ("a Certificate entry may have extensions", rule("    if (ext != 0) return null; // rule: no entry extensions\n"), [56, 57]),
    ("the 12 bytes before the key are not compared", rule("    if (!std.mem.eql(u8, body[o .. o + 12], &spki)) return null; // rule: the Ed25519 prefix\n"), [58, 59]),
    ("a CertificateVerify may name another scheme", rule("    if (body[0] != 0x08 or body[1] != 0x07) return false; // rule: the scheme\n"), [60, 61]),
    ("a CertificateVerify's signature field may be longer", [("unikernel/quic.zig", "    if (siglen != 64 or body.len != 4 + 64) return false; // rule: 64 bytes\n", "    _ = siglen;\n", 1)], [62, 63]),
    ("the client takes bytes after the server's Finished", [("unikernel/quic.zig", TRAIL, "", 1)], [64]),
    ("the server takes bytes after the client's Finished", [("unikernel/quic.zig", TRAIL, "", 2)], [65]),
    ("the client takes a flight with no CertificateRequest", NO_REQUEST, [66]),
    ("STREAM and CRYPTO frames are taken in any packet number space", SPACE_RULE, [68]),
]

GUEST = [
    # (what is undone, patches, check script, text that must be in its output)
    ("the guest ignores the file given at boot and uses one seed",
     [("unikernel/net.zig", FIXED_SEED, "    var seed: [33]u8 = .{7} ** 33;\n    var unused: [33]u8 = undefined;\n    _ = reflect_boot_take(&unused, unused.len);\n    const n: usize = 32;\n", 1)],
     "check-quic.sh", None),
    ("the guest mixes random bytes into the key it was given",
     [("unikernel/net.zig", "    me = entity.identity(seed[0..32])", "    seed[0] ^= @truncate(rdrand64() | 1);\n    me = entity.identity(seed[0..32])", 1)],
     "check-quic.sh", None),
    ("the client does not check the server's name against its list", [CLIENT_ALLOW], "check-quic.sh", None),
    ("the server does not check the client's name against its list", [SERVER_ALLOW], "check-quic.sh", None),
    ("a refused connection does not give way at once",
     [("unikernel/net.zig", "(q_answered or qconn.refused or now -| q_seen >= q_idle)", "(q_answered or now -| q_seen >= q_idle)", 1)],
     "check-quic.sh", None),
    ("a QUIC guest still answers its plain UDP port",
     [("unikernel/net.zig", "    if (ep.guarded) return;\n", "", 1)], "check-quic.sh", None),
    ("stream data is taken in any space, and read before the handshake is accepted",
     SPACE_RULE + ACCEPT_GATE, "check-quic.sh", None),
    ("stream data is taken in any space; the accepted gate is left in place (this one passes the guest step and fails quic-self)",
     SPACE_RULE, "check-quic.sh", "quic-self"),
]
WIRE = [
    ("the client does not check the server's name against its list", [CLIENT_ALLOW], "check-wire.sh", None),
    ("the server does not check the client's name against its list", [SERVER_ALLOW], "check-wire.sh", None),
]

def nth_replace(text, old, new, nth):
    at = -1
    for _ in range(nth):
        at = text.find(old, at + 1)
        if at < 0:
            raise SystemExit("patch does not apply: %r" % old[:60])
    return text[:at] + new + text[at + len(old):]

def copy(patches, name):
    dst = TREE + "-control"
    if os.path.exists(dst):
        shutil.rmtree(dst)
    subprocess.run(["cp", "-a", TREE, dst], check=True)
    for path, old, new, nth in patches:
        full = os.path.join(dst, path)
        text = open(full).read()
        open(full, "w").write(nth_replace(text, old, new, nth))
    # The build goes on past a failing quic-self, and says so.
    b = os.path.join(dst, "unikernel/build-net.sh")
    text = open(b).read()
    old = '"$OUT/quic-self"\n'
    assert text.count(old) == 1
    open(b, "w").write(text.replace(old, '"$OUT/quic-self" || echo "quic-self exit $?"\n'))
    return dst

bad = 0
if WHAT in ("self", "all"):
    print("== quic-self, each fix undone ==", flush=True)
    for name, patches, codes in SELF:
        dst = copy(patches, name)
        exe = os.path.join(dst, "quic-self.bin")
        r = subprocess.run(["zig", "build-exe", "-O", "ReleaseSafe", "-femit-bin=" + exe, os.path.join(dst, "unikernel/quic-self.zig"),
                            "--cache-dir", dst + "/zc", "--global-cache-dir", dst + "/zg"], env=ENV, capture_output=True, text=True)
        if r.returncode != 0:
            print("control: %s\n  DID NOT BUILD\n%s" % (name, r.stderr[-600:]), flush=True)
            bad += 1
            continue
        got = []
        for code in codes:
            args = [exe] if code == 0 else [exe, str(code)]
            got.append(subprocess.run(args, env=ENV, capture_output=True).returncode)
        want = [40 if c == 0 else c for c in codes]
        ok = got == want
        bad += 0 if ok else 1
        print("control: %s\n  quic-self exits %s, wanted %s: %s" % (name, got, want, "fails as it should" if ok else "THE CHECK DID NOT FAIL"), flush=True)

def guest(controls):
    global bad
    for name, patches, script, must in controls:
        dst = copy(patches, name)
        r = subprocess.run(["sh", os.path.join(dst, "unikernel", script)], env=ENV, capture_output=True, text=True)
        lines = (r.stdout + r.stderr).strip().splitlines()
        shown = [l for l in lines if l.startswith("ok ") or l.startswith("quic-self exit") or not l.startswith(("built ", "All ", "1/", "2/", "3/"))][-6:]
        ok = r.returncode != 0 if must is None else any(must in l for l in lines)
        bad += 0 if ok else 1
        print("control: %s\n  %s exits %d: %s" % (name, script, r.returncode, "fails as it should" if ok else "THE CHECK DID NOT FAIL"), flush=True)
        for l in shown:
            print("    " + l, flush=True)

if WHAT in ("guest", "all"):
    print("== check-quic.sh on a real guest, each fix undone ==", flush=True)
    guest(GUEST)
if WHAT in ("wire", "all"):
    print("== check-wire.sh on two real guests, each fix undone ==", flush=True)
    guest(WIRE)
shutil.rmtree(TREE + "-control", ignore_errors=True)
print("controls that did not fail: %d" % bad)
sys.exit(1 if bad else 0)
