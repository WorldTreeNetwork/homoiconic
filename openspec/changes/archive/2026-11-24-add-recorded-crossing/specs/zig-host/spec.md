# zig-host delta: the crossing exports replace the remote ones

## REMOVED Requirements

### Requirement: Lean exports carry the remote channel

Replaced by "Lean exports carry the crossing".

## ADDED Requirements

### Requirement: Lean exports carry the crossing

The Lean definitions exported from `kernel/Surface/Host.lean` SHALL be the guest and the check of `openspec/specs/crossing/spec.md`: `reflect_cross_start(flags)` begins a guest with no process (bit 0: it will be given the program; bit 1: its start requests go to the peer; bit 2: it takes the newest pending send first; bit 3: it opens the exchanges and closes the run); `reflect_cross_give(guest, program, length, budget)` begins the program, given in its byte form, as the first process; `reflect_cross_work(guest)`, `reflect_cross_take(guest, batch, length)` and `reflect_cross_batch(guest, out, capacity)` are `Guest.work`, `Guest.take` and `Guest.batch`; `reflect_cross_state(guest)` is 0 for work to do, 1 resting, 2 closed, 3 failed; `reflect_cross_record(guest, me, meLength, peer, peerLength, out, capacity)` is the record text; `reflect_cross_check(program, length, a, aLength, b, bLength, out, capacity)` is `Surface.Cross.check`; `reflect_cross_reseal(record, length, out, capacity)` is a check-only hook that makes a record's chain and head again. A guest is a Lean value the caller holds and cannot look inside; each call that takes it uses it up. `give`, `work` and `check` evaluate, each machine run they make is a priced run with the budget given, and Zig SHALL NOT make or read the bytes they exchange. `unikernel/out-net/cross-check` calls the last two.

#### Scenario: The same check outside a guest

- GIVEN `unikernel/out-net/cross-check`, linked from the objects the guests link
- WHEN `unikernel/check-wire.sh` runs it on two guests' records
- THEN it prints what `Surface.Cross.check` answers, and exits 0 only on `accepted`
