#!/usr/bin/env python3
"""Each refusal of the crossing check, with its check undone.

For every control: copy the kernel, undo one check by replacing one exact
piece of source, build `Surface.Cross`, run `CrossCheck.lean`, and require
that the named test now prints FAIL and that it printed ok before. A control
whose test still passes means that check is not what refuses that record.

usage: python3 kernel/cross-controls.py   (from the repository root)
"""
import functools, os, shutil, subprocess, sys, tempfile

print = functools.partial(print, flush=True)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CROSS = "Surface/Cross.lean"
MIX = "Reflect/Crossing.lean"

# (what is undone, file, source, replacement, tests that must fail)
CONTROLS = [
    ("the parent link is not checked", CROSS,
     "if parent != prev then .error s!\"log {who}: entry {k} does not name the entry before it\"\n    else if",
     "if",
     ["an entry dropped", "an entry repeated"]),
    ("neither the parent link nor the order is checked", CROSS,
     "if parent != prev then .error s!\"log {who}: entry {k} does not name the entry before it\"\n    else if n != k then .error s!\"log {who}: entry {k} is out of order\"\n    else\n",
     "",
     ["an entry moved", "an entry dropped", "an entry repeated", "an order that is not the place"]),
    ("a mark with no order is read as a link", CROSS,
     "  | k, _ :: _ => .error s!\"log {who}: entry {k} has no link\"",
     "  | k, .arr [.arr [.nat 0, parent], body] :: ds =>\n"
     "    if parent != prev then .error s!\"log {who}: entry {k} does not name the entry before it\"\n"
     "    else\n"
     "      match dataNote body with\n"
     "      | none => .error s!\"log {who}: entry {k} is not an entry\"\n"
     "      | some note => do\n"
     "        let r ← readChain who (Keep.entryName (.arr [.arr [.nat 0, parent], body])) (k + 1) ds\n"
     "        pure (note :: r.1, r.2)\n"
     "  | k, _ :: _ => .error s!\"log {who}: entry {k} has no link\"",
     ["a mark with no order"]),
    ("the head is not checked", CROSS,
     "if n != r.entries.length || name != c.2 then",
     "if false then",
     ["the last entry dropped"]),
    ("a crossing can be taken whatever its state", MIX,
     "    | some ⟨g, .offered⟩, some h =>\n      some (m.setOuts s.other ((m.outs s.other).set k ⟨g, .taken⟩), [.comm g h])",
     "    | some ⟨g, _⟩, some h =>\n      some (m.setOuts s.other ((m.outs s.other).set k ⟨g, .taken⟩), [.comm g h])",
     ["a taking repeated"]),
    # No test is named here. The walk takes the head of `a` whenever it can
    # be placed, so with this rule undone an honest acknowledgement is placed
    # before its taking and honest logs stop combining: the rule is also what
    # orders the walk, and cannot be undone alone.
    ("an acknowledgement needs no taking (honest logs then stop combining)", MIX,
     "    | some ⟨g, .taken⟩, some g' =>",
     "    | some ⟨g, _⟩, some g' =>",
     []),
    ("a taken crossing may stay unacknowledged", MIX,
     "  | _, m, [], [] => if m.settled then some ([], m) else none",
     "  | _, m, [], [] => some ([], m)",
     ["an acknowledgement dropped"]),
    ("a crossing number need not be the count", MIX,
     "      if k = (m.outs s).length then some (m.setOuts s (m.outs s ++ [⟨g, .offered⟩]), [])\n      else none",
     "      some (m.setOuts s (m.outs s ++ [⟨g, .offered⟩]), [])",
     ["a crossing number that is not the count"]),
    ("a held process may be named", MIX,
     "  | some g => if m.held g then none else some g",
     "  | some g => some g",
     ["an entry that names a held process"]),
    ("a schedule that stops is taken as run", CROSS,
     "          | (_, _, .refused ev) => .error (renderData (eventData ev) ++ \" cannot happen\")",
     "          | (_, cfg, .refused _) => pure (renderProcs 0 cfg.procs)",
     ["a local event repeated"]),
    ("the processes are not compared", CROSS,
     "      if procLine q == l then compare who cfg (i + 1) gs ls",
     "      if true then compare who cfg (i + 1) gs ls",
     ["the takings in another order", "a name not handed over"]),
    ("the number of processes is not compared", CROSS,
     "  | _, gs, ls =>\n    .error s!\"record {who} reports {ls.length} more processes and its log {gs.length} more\"",
     "  | _, _, _ => .ok ()",
     ["a process not reported"]),
    ("the names are not compared", CROSS,
     "if ra.me != rb.peer || rb.me != ra.peer then .error \"the records do not name each other\"",
     "if false then .error \"the records do not name each other\"",
     ["another peer"]),
    ("the budgets are not compared", CROSS,
     "if budget != budget' then .error \"the budgets differ\"",
     "if false then .error \"the budgets differ\"",
     ["another budget"]),
    # Only the choice of a local event sees held senders again. With held
    # processes shown to the whole step, a held process is put out again on
    # every step, 256 times a call, and the check does not end in any time
    # worth waiting for.
    ("a held sender is not hidden when a local event is chosen", CROSS,
     "  let m := g.masked\n  match pick m with",
     "  let m := g.masked\n"
     "  match pick ⟨g.cfg.procs.mapIdx fun i q =>\n"
     "      if (g.asked.any (·.place == i) && !wantsSend q) || g.stuck.contains i then ⟨.finished .wrong, []⟩ else q,\n"
     "    g.cfg.names⟩ with",
     ["a send put out is held from a local receiver"]),
    ("a new channel is named as one machine names it", CROSS,
     "    let n := 2 * g.made + (if g.side = .a then 0 else 1)",
     "    let n := nextName g.cfg.names",
     ["a name crosses in a message"]),
]

class Late:
    returncode = 124
    stdout = ""
    stderr = "no result in 300 seconds"

def run(cmd, cwd):
    try:
        return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=300)
    except subprocess.TimeoutExpired:
        return Late()

def lines(kernel):
    b = run(["lake", "build", "Surface.Cross"], kernel)
    if b.returncode == 124:
        return None, "the build gave " + b.stderr
    if b.returncode != 0:
        return None, b.stdout[-2000:] + b.stderr[-2000:]
    r = run(["lake", "env", "lean", "CrossCheck.lean"], kernel)
    if r.returncode == 124:
        return None, "CrossCheck.lean gave " + r.stderr
    return r.stdout.splitlines(), r.stderr

def main():
    tmp = tempfile.mkdtemp(prefix="cross-controls-")
    shutil.copytree(os.path.join(ROOT, "kernel"), os.path.join(tmp, "kernel"), symlinks=True)
    shutil.copytree(os.path.join(ROOT, "examples"), os.path.join(tmp, "examples"))
    kernel = os.path.join(tmp, "kernel")
    base, err = lines(kernel)
    if base is None or any(l.startswith("FAIL") for l in base):
        print("the unchanged tree does not pass:", err); return 1
    print(f"unchanged: {sum(l.startswith('ok') for l in base)} ok, 0 FAIL")
    bad = 0
    for what, rel, old, new, tests in CONTROLS:
        path = os.path.join(kernel, rel)
        src = open(path).read()
        if src.count(old) != 1:
            print(f"CONTROL BROKEN {what}: the source to undo is not there exactly once"); bad += 1; continue
        open(path, "w").write(src.replace(old, new))
        got, err = lines(kernel)
        open(path, "w").write(src)
        if got is None:
            print(f"CONTROL BROKEN {what}: no build or no result\n{err}"); bad += 1; continue
        failed = [l for l in got if l.startswith("FAIL")]
        print(f"undone: {what}: {len(failed)} FAIL")
        for l in failed:
            print("    " + l.split(": wanted")[0])
        if not tests and not failed:
            print("    no test fails: nothing in CrossCheck.lean is refused by this check alone")
        for t in tests:
            if any(l.startswith("FAIL " + t) for l in failed):
                print(f"  ok   `{t}` fails with the check undone")
            else:
                print(f"  NOT SHOWN `{t}` still passes with the check undone"); bad += 1
    shutil.rmtree(tmp, ignore_errors=True)
    print("controls ok" if bad == 0 else f"controls: {bad} not shown")
    return 0 if bad == 0 else 1

sys.exit(main())
