# zig-host delta: the crossing exports replace the remote ones

## REMOVED Requirements

### Requirement: Lean exports carry the remote channel

Replaced by "Lean exports carry the crossing".

## ADDED Requirements

### Requirement: Lean exports carry the crossing

The Lean definitions exported as `reflect_cross_start`, `reflect_cross_work`, `reflect_cross_take`, `reflect_cross_batch`, `reflect_cross_state`, `reflect_cross_record` and `reflect_cross_check` SHALL be the guest session and the check of `openspec/specs/crossing/spec.md` (`kernel/Surface/Host.lean`). They evaluate, each machine run they make is a priced run with the budget given, and Zig SHALL NOT make or read the bytes they exchange. The list of exports that evaluate in "The host calls the kernel" and the list in "The run command charges operation costs" SHALL name these in place of the four `reflect_remote_*` exports.

#### Scenario: The same check outside a guest

- GIVEN `unikernel/out-net/cross-check`, linked from the objects the guests link
- WHEN `unikernel/check-wire.sh` runs it on two guests' records
- THEN it prints what `Surface.Cross.check` answers
