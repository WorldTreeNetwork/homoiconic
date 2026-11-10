# Tasks

- [x] Owner: `Reflect.Machine` with the instruction set, state, `step`, `run`, `compile`, `decompile`, and `readOutcome`. `lake build` exits 0.
- [x] Owner: `kernel/MachineContract.lean` with the signatures in `design.md`. Definitions are frozen from here.
- [x] Prove `run_add` and `run_halted`.
- [x] Prove `decompile_compile`.
- [x] Prove `machine_correct`, both directions.
- [x] Prove `depth_bound`.
- [x] A run file slices one long run into three and compares the outcome with a single run (`kernel/ReflectRun.lean`).
- [x] Measure steps per second and record the number in `docs/LEARNINGS.md`.
- [x] `lake env lean MachineContract.lean` prints no `sorryAx` and no package axiom.
