# Tasks

- [ ] Owner: `Reflect.Machine` with the instruction set, state, `step`, `run`, `compile`, `decompile`, and `readOutcome`. `lake build` exits 0.
- [ ] Owner: `kernel/MachineContract.lean` with the four signatures in `design.md`. Definitions are frozen from here.
- [ ] Prove `run_add` and that a halted state steps to itself.
- [ ] Prove `decompile_compile`.
- [ ] Prove `machine_correct`, both directions.
- [ ] Prove `space_bound`.
- [ ] A run file slices one long run into three and compares the outcome with a single run.
- [ ] Measure steps per second and record the number in `docs/LEARNINGS.md`.
- [ ] `lake env lean MachineContract.lean` prints no `sorryAx` and no package axiom.
