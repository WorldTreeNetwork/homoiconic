# Tasks

- [x] Owner: the user, 2026-11-12. Bead `homoiconic-q59.31`.
- [x] `kernel/Surface/Bytes.lean`: `unreifyOutcome`, `unlift`, `renderInterpreted`, `interpBytes`, `interpText`.
- [x] `kernel/Surface/Host.lean`: export `reflect_interp`.
- [x] `host/run.zig`: `--interp` and `--interp=k`, in any order with `--bytes`.
- [x] `host/check.sh`: the interpreter scenarios.
- [x] `sh host/check.sh` exits 0 (2026-11-12, macOS arm64).
- [ ] Advise.
- [ ] Fold: the ADDED delta goes into `openspec/specs/zig-host/spec.md`; the export list in "The host returns the kernel's result" gains `reflect_interp` (it already lacks `reflect_vm_start` and `reflect_vm_from`).
