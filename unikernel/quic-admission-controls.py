#!/usr/bin/env python3
"""Each check of add-quic-admission, with its fix undone.

`self`: for every control, copy unikernel's Zig files to a scratch
directory, undo one fix by replacing one exact piece of source, build
quic-self, and require that `quic-self <code>` now exits with that code. It
first requires every code to pass on the source as it is.

`guest`: on a Linux host with KVM (morphie), undo one fix in this tree, run
check-quic.sh or check-wire.sh, require it to fail with the named message,
and put the source back. Run it from a `git archive` export, not a checkout
you work in.

usage: python3 unikernel/quic-admission-controls.py self|guest
"""
import functools, os, shutil, subprocess, sys, tempfile

print = functools.partial(print, flush=True)

HERE = os.path.dirname(os.path.abspath(__file__))
Q, A = "quic.zig", "admit.zig"

# (what is undone, file, source, replacement, codes that must fail)
SELF = [
    ("another key for the Retry integrity tag", Q,
     "const key = [16]u8{ 0xbe, 0x0c,", "const key = [16]u8{ 0xbf, 0x0c,", [70]),
    ("the client drops Retry packets", Q,
     "if (!c.server) c.onRetry(pkt, dcid[0..8], scid[0..8]);", "_ = scid;", [71]),
    ("a token's validation finishes the Initial space, as before the split", Q,
     "if (space == 1 and c.server and !c.hs_opened) {", "if (space == 1 and c.server and !c.validated) {", [71]),
    ("the client does not read the server's transport parameters", Q,
     "if (!c.paramsNamed(ee)) return c.refuse();", "", [72]),
    ("duplicates open", Q,
     "        if (!c.rx_any[space]) return false;\n        const top = c.rx_top[space];\n        if (pn > top) return false;\n        if (top - pn >= 64) return true;",
     "        if (!c.rx_any[space] or pn == pn) return false;\n        const top = c.rx_top[space];\n        if (pn > top) return false;\n        if (top - pn >= 64) return true;",
     [73]),
    ("no Retry: a first flight with no token is dropped when the first pool is full", A,
     "return .{ .retry = quic.makeRetry(&t.retry, dgram, &t.key, &from.ip, from.port, now, t.rand) };",
     "return .none;", [74]),
    ("the oldest connection not accepted is evicted, instead of a Retry", A,
     "return .{ .retry = quic.makeRetry(&t.retry, dgram, &t.key, &from.ip, from.port, now, t.rand) };",
     "var old: usize = 0;\n        var k: usize = 1;\n        while (k < first_slots) : (k += 1) {\n"
     "            if (t.slot[k].born < t.slot[old].born) old = k;\n        }\n"
     "        if (t.slot[old].conn.accepted) return .none;\n        t.slot[old].used = false;\n"
     "        return t.open(old, from, dgram, now, null);",
     [74]),
    ("no limit of one handshake per address in the address pool", A,
     "if (!t.addressBusy(from.ip)) at = t.free(first_slots, slots);",
     "at = t.free(first_slots, slots);", [75]),
    ("packets that open keep a connection not accepted (the old idle rule)", A,
     "if (now -| s.born >= cap) s.used = false;", "if (now -| s.seen >= idle) s.used = false;", [76]),
    ("a token has no time window", Q,
     "if (made > now or now - made > token_life) return null;", "", [77]),
    ("the port is left out of a token's MAC", Q,
     "std.mem.writeInt(u16, m[4..6], port, .big);", "_ = port;\n    std.mem.writeInt(u16, m[4..6], 0, .big);", [77]),
    ("the Retry's ID is left out of a token's MAC", Q,
     "@memcpy(m[6..14], rscid);", "_ = rscid;\n    @memset(m[6..14], 0);", [77]),
    ("a token's MAC is not compared", Q,
     "if (!std.crypto.timing_safe.eql([16]u8, mac, t[16..32].*)) return null;", "_ = mac;", [77]),
    ("a client takes a Retry whatever its tag", Q,
     "if (!std.crypto.timing_safe.eql([16]u8, tag, pkt[pkt.len - 16 ..][0..16].*)) return;", "_ = tag;", [79]),
    ("a client takes a second Retry", Q,
     "if (c.retried or c.rx_any[0]) return;", "if (c.rx_any[0]) return;", [79]),
    ("a client takes a Retry after an Initial opened", Q,
     "if (c.retried or c.rx_any[0]) return;", "if (c.retried) return;", [79]),
    ("a client takes a Retry for another destination ID", Q,
     "if (!std.mem.eql(u8, dcid, &c.local_cid)) return;", "_ = dcid;", [79]),
    ("a client takes a Retry whose source ID is its first destination ID", Q,
     "if (std.mem.eql(u8, scid, &c.orig_dcid)) return;", "", [79]),
]

# (what is undone, file, source, replacement, script, message it must print)
GUEST = [
    ("no Retry: a first flight with no token is dropped when the first pool is full", A,
     "return .{ .retry = quic.makeRetry(&t.retry, dgram, &t.key, &from.ip, from.port, now, t.rand) };",
     "return .none;", "check-quic.sh", "an allowed client waited"),
    ("packets that open keep a connection not accepted (the old idle rule)", A,
     "if (now -| s.born >= cap) s.used = false;", "if (now -| s.seen >= idle) s.used = false;",
     "check-quic.sh", "the client that ignores a Retry"),
    ("the client drops Retry packets", Q,
     "if (!c.server) c.onRetry(pkt, dcid[0..8], scid[0..8]);", "_ = scid;",
     "check-wire.sh", "flooded: guest A did not close"),
]


def patched(path, old, new):
    src = open(path).read()
    if src.count(old) != 1:
        sys.exit(f"control source not found once in {path}: {old[:60]!r}")
    return src.replace(old, new)


def selfrun(d, code):
    r = subprocess.run([os.path.join(d, "quic-self"), str(code)], capture_output=True)
    return r.returncode


def build(d):
    r = subprocess.run(["zig", "build-exe", "-O", "ReleaseSafe", "-femit-bin=" + os.path.join(d, "quic-self"),
                        os.path.join(d, "quic-self.zig")], capture_output=True, text=True,
                       cwd=d)
    if r.returncode != 0:
        print(r.stderr)
    return r.returncode == 0


def self_controls():
    codes = sorted({c for _, _, _, _, cs in SELF for c in cs})
    with tempfile.TemporaryDirectory() as d:
        for f in os.listdir(HERE):
            if f.endswith(".zig"):
                shutil.copy(os.path.join(HERE, f), d)
        print("== quic-self, as it is ==")
        if not build(d):
            sys.exit("quic-self does not build")
        for c in codes:
            got = selfrun(d, c)
            print(f"  quic-self {c} exits {got}")
            if got != 0:
                sys.exit("a check fails on the source as it is")
        print("== quic-self, each fix undone ==")
        bad = 0
        for what, f, old, new, want in SELF:
            keep = open(os.path.join(d, f)).read()
            new_src = patched(os.path.join(d, f), old, new)
            open(os.path.join(d, f), "w").write(new_src)
            print(f"control: {what}")
            if not build(d):
                print("  does not build")
                bad += 1
            else:
                got = [selfrun(d, c) for c in want]
                ok = got == want
                print(f"  quic-self exits {got}, wanted {want}: {'fails as it should' if ok else 'DOES NOT FAIL'}")
                bad += 0 if ok else 1
            open(os.path.join(d, f), "w").write(keep)
        if bad:
            sys.exit(f"{bad} controls did not fail")


def guest_controls():
    print("== real guests, each fix undone ==")
    bad = 0
    env = dict(os.environ)
    for what, f, old, new, script, msg in GUEST:
        path = os.path.join(HERE, f)
        keep = open(path).read()
        new_src = patched(path, old, new)
        open(path, "w").write(new_src)
        print(f"control: {what}")
        try:
            r = subprocess.run(["sh", os.path.join(HERE, script)], capture_output=True, text=True, env=env)
        finally:
            open(path, "w").write(keep)
        out = r.stdout + r.stderr
        ok = r.returncode != 0 and msg in out
        print(f"  {script} exits {r.returncode}; '{msg}' {'printed' if msg in out else 'not printed'}: "
              f"{'fails as it should' if ok else 'DOES NOT FAIL AS IT SHOULD'}")
        for line in out.strip().splitlines()[-6:]:
            print("    " + line)
        bad += 0 if ok else 1
    # The tree as it is, built again.
    subprocess.run(["sh", os.path.join(HERE, "build-net.sh")], capture_output=True)
    if bad:
        sys.exit(f"{bad} controls did not fail")


if __name__ == "__main__":
    if len(sys.argv) != 2 or sys.argv[1] not in ("self", "guest"):
        sys.exit(__doc__)
    self_controls() if sys.argv[1] == "self" else guest_controls()
