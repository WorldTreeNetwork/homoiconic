# Tasks

- [x] Owner: `Reflect.Machine` with the instruction set, state, `step`, `run`, `compile`, `decompile`, and `readOutcome`. `lake build` exits 0.
- [x] Owner: `kernel/MachineContract.lean` with the signatures in `design.md`. Definitions are frozen from here.
- [ ] Prove `run_add` and `run_halted`.
- [ ] Prove `decompile_compile`.
- [ ] Prove `machine_correct`, both directions.
- [ ] Prove `depth_bound`.
- [x] A run file slices one long run into three and compares the outcome with a single run (`kernel/ReflectRun.lean`).
- [ ] Measure steps per second and record the number in `docs/LEARNINGS.md`.
- [ ] `lake env lean MachineContract.lean` prints no `sorryAx` and no package axiom.
