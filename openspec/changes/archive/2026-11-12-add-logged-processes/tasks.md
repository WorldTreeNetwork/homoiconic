# Tasks

- [x] Owner: the user, 2026-11-12. Bead `homoiconic-q59.26`.
- [x] `kernel/Reflect/Node.lean`: `Op`, `Node`, `Apply`, `Applied`, `Ran`, `firstOps`; `Job`, `plan`; the executable `nodeRun`.
- [x] `kernel/Reflect/NodeProof.lean`: determinism, prefix, repeats, restart, the link to schedules, the machine simulation both ways, soundness of `nodeRun`, `plan_step` and `step_plan`.
- [x] `kernel/NodeContract.lean`: the statements, with their axioms.
- [x] `kernel/Surface/Keep.lean`: a session can be a node (`nodeStart`, `nodeFrom`). Exports `reflect_node_start`, `reflect_node_from`.
- [x] `host/node.zig`; `kernel/NodeCheck.lean`; `examples/ping.log`, `ping-part.log`, `ping-again.log`; the node scenarios in `host/check.sh`.
- [x] `sh host/check.sh` exits 0.
- [x] Advise by a reader from another model family. Send-back, 2026-11-12, one required correction to a stated limit, made. Review in `reviews/`.
- [x] Fold. 2026-11-12: `openspec/specs/logged-processes/spec.md` is new; the ADDED delta is in `openspec/specs/zig-host/spec.md`.
