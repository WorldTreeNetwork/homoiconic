# Tasks

- [x] Owner: the user approved the syntax in `design.md`, 2026-11-09.
- [ ] Owner: `kernel/Surface/Examples.lean` pairs each example program with the `Reflect` term it must read as.
- [ ] `Surface.read : ByteArray → Except String Term`, in Lean, meeting those examples and refusing unknown names, tabs in indentation, and a block that does not end in a value.
- [ ] `Surface.render` for outcomes, as the table in `design.md`. Rendered data reads back as the same data.
- [ ] Export `reflect_run` as in `design.md`. It runs the machine, not `evalFuel`.
- [ ] The Zig check passes program files and compares printed text. Zig does not read or evaluate.
- [ ] `sh host/check.sh` exits 0 with the new checks. `ReflectContract.lean`, `MachineContract.lean`, and `Contract.lean` still exit 0.
