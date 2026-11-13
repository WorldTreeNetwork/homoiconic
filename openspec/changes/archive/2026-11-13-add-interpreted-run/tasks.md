# Tasks

- [x] Owner: the user, 2026-11-12. Bead `homoiconic-q59.31`.
- [x] `kernel/Surface/Bytes.lean`: `unreifyOutcome`, `unlift`, `renderInterpreted`, `interpBytes`, `interpText`.
- [x] `kernel/Surface/Host.lean`: export `reflect_interp`.
- [x] `host/run.zig`: `--interp` and `--interp=k`, in any order with `--bytes`.
- [x] `host/check.sh`: the interpreter scenarios.
- [x] `sh host/check.sh` exits 0 (2026-11-12, macOS arm64).
- [x] Advise: waived by the user, 2026-11-13.
- [x] Fold. 2026-11-13, with `add-string-literals`: the ADDED delta is in `openspec/specs/zig-host/spec.md`, with `reflect_interp` taking `flags` as landed, not a bytes flag. The export list in "The host returns the kernel's result" gains `reflect_interp`, and `reflect_vm_start`, `reflect_vm_from`, `reflect_node_start` and `reflect_node_from`, which it lacked, so it matches the `@[export]` definitions in `kernel/Surface/Host.lean`.
