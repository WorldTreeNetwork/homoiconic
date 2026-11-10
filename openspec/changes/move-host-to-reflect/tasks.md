# Tasks

- [x] Owner: the user approved the syntax in `design.md`, 2026-11-09.
- [x] Owner: `kernel/Surface/Examples.lean` pairs each example program with the `Reflect` term it must read as.
- [x] `Surface.read : ByteArray → Except String Term`, in Lean, meeting those examples and refusing unknown names, tabs in indentation, and a block that does not end in a value.
- [x] `Surface.render` for outcomes, as the table in `design.md`. Rendered data reads back as the same data.
- [x] Export `reflect_run` as in `design.md`. It runs the machine, not `evalFuel`.
- [x] The Zig check passes program files and compares printed text. Zig does not read or evaluate.
- [x] `sh host/check.sh` exits 0 with the new checks. `ReflectContract.lean`, `MachineContract.lean`, and `Contract.lean` still exit 0.
- [x] `Reflect.runUntil` stops when the machine stops, with `runUntil_eq : runUntil n s = run n s` pinned in `MachineContract.lean`, so a large budget costs nothing after a halt.
