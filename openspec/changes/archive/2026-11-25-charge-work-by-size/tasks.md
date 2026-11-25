- [x] Audit every step of `step` and every operation of `arith` for time that grows with data while the charge does not: `equal`; `cons` onto a text; `succ` and `case` of a number; reaching a variable; the charges themselves (`kernel/CostBench.lean`, the worst program for each, before and after)
- [x] `Ops.costWithin` with its law, `Ops.work`, `Ops.reach` (`kernel/Reflect/Semantics.lean`); `stepCost`, `reachIn`, `stepCostWithin`, `runPricedWithin` and `runPriced_eq_within` (`RunUntil.lean`); `runSpaceWithin` and `runSpace_eq_within` (`Space.lean`); `runPriced_unit` with the two new hypotheses (`RunUntilProof.lean`, `MachineContract.lean`) (`343250e`)
- [x] `arith`: `Data.weight`, `weighGo` and `weighGo_eq`, `weighWithin`, `minWeightGo`, `arithCost` for `equal`, `arithCostWithin` and its law, `arithWork`, `arithReach`; `lenEq` in `sameGo` (`343250e`)
- [x] The lazy machine's `lstepCost` charges `work` as `stepCost` does (`343250e`)
- [x] Checks: charges and a deep comparison in `kernel/Surface/Check.lean`; the deep comparison at the default budget in `host/check.sh`, `unikernel/check.sh` and `check-net.sh` (`343250e`, `742d062`); the restated equalities in `kernel/WalkContract.lean`
- [x] Which totals moved: on every example at levels 0 to 2, `calc.hom` +30 and `words.hom` +3; `reach` at `i / 8` would have moved nearly every interpreted total by about 5%, so it is `i / 32`
- [x] Fresh-context review of the two commits (Opus, 2026-11-25): three findings. The lazy machine's uncapped charge and conversion (`homoiconic-q59.80`, filed before, measured by the review); a syntax error printing a long number with `toString` (fixed: `Tk.show` uses `decimal`); `runSpaceLeft` in `Reflect/Hold.lean` asking the charge uncapped (`homoiconic-q59.81`, fixed by the crossing's agent, whose file it is)
- [x] Controls on the tree before: `host/check.sh`'s new cases time out at 120 s (`unikernel/evidence/q59.73-controls.log`)
- [x] morphie: the six image checks on the final tree; the measurements in `unikernel/evidence/q59.73-measurements.log`
- [x] Fold: `openspec/specs/bytecode-machine/spec.md`, `ARCHITECTURE.md`, `docs/PROOFS.md`, `docs/LEARNINGS.md`, `kernel/README.md`, `unikernel/README.md`

Left open, each with a bead: the lazy machine of a kept session (`homoiconic-q59.80`).
