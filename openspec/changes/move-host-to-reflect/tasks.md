# Tasks

- [x] Owner: the user approved the syntax in `design.md`, 2026-11-09.
- [x] Owner: `kernel/Surface/Expect.lean` pairs each example program with the `Reflect` term it must read as.
- [x] `Surface.read : ByteArray → Except String Term`, in Lean, meeting those examples and refusing unknown names, tabs in indentation, and a block that does not end in a value.
- [x] `Surface.render` for outcomes, as the table in `design.md`. Rendered data reads back as the same data.
- [x] Export `reflect_run` as in `design.md`. It runs the machine, not `evalFuel`.
- [x] The Zig check passes program bytes, generated from `Surface.prints` into `host/out/cases.zig`, and compares printed text. Zig does not read or evaluate.
- [x] `sh host/check.sh` exits 0 with the new checks. `ReflectContract.lean`, `MachineContract.lean`, and `Contract.lean` still exit 0.
- [x] `Reflect.runUntil` stops when the machine stops, with `runUntil_eq : runUntil n s = run n s` pinned in `MachineContract.lean`, so a large budget costs nothing after a halt.
- [x] After review: a catch-all arm's name is no longer visible in the written arms (it silently rebound an outer name, and let an unbound name through). Regressions for all four arms, an arm-local `let`, and the refusal are in `Expect.lean`.
- [x] After review: `+` no longer takes its operand from a line at the statement's column. Refusals and an indented positive control are in `Expect.lean`.
- [x] After review: `Expect.runs` compiles, runs, and renders terms no text reads as, including `var 2147483647`; the self-application program goes through `reflect_run`.
