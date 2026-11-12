# Tasks

- [x] Owner: the user, 2026-11-12. Bead `homoiconic-q59.13`.
- [x] Move `unreify` and `unreify_reify` from `Wire.Form` to `Reflect.Syntax`, so the scheduler can read a quoted program.
- [x] `kernel/Reflect/Channel.lean`: payload shapes, `Step`, `Sched`, `Network`; the executable `stepRun`, `schedRun`, `autoRun`.
- [x] `kernel/Reflect/ChannelProof.lean`: determinism, the held-name theorems, the machine simulation both ways, soundness of the executable scheduler.
- [x] `kernel/ChannelContract.lean`: the statements, for every table, with their axioms.
- [x] `kernel/Surface/Chan.lean`, the export `reflect_channels`, `host/chan.zig`.
- [x] `examples/ping.hom`, `race.hom`, `race.schedule`, `guess.hom`, `guess.schedule`, `spawns.hom`; the chan scenarios in `host/check.sh`.
- [x] MODIFIED deltas for the two requirements `homoiconic-1e7` names.
- [x] `sh host/check.sh` exits 0.
- [x] Advise by a reader from another model family. Send-back, 2026-11-12, two required fixes about what the text claims, both made; review in `reviews/`.
- [ ] Fold.
