# unikernel-net delta: guests carry crossings and print their records

## REMOVED Requirements

### Requirement: Two guests carry a remote channel over QUIC

Replaced by "Two guests run one program and record the crossing".

### Requirement: The wire check uses two real guests

Replaced by "The wire check replays the guests' records".

## ADDED Requirements

### Requirement: Two guests run one program and record the crossing

The command line MAY carry `reflect.wire_port=<port>` or `reflect.peer=<a.b.c.d>:<port>` as before, and with either MAY carry `reflect.spawn=far|near` and `reflect.take=old|new`, each at most once; either word without an end of the crossing SHALL be refused as other bad configuration is (`unikernel/net.zig` `parse`). Each guest SHALL begin a Lean guest with `reflect_cross_start` and hold it between calls; Zig SHALL NOT read a packet, a batch, an entry or a process. The guest with `reflect.wire_port` is the one given the program: a stream on the wire port that starts `RFL1` SHALL be judged as a run frame is (kind 0, status 0, a budget in range), its body and budget SHALL be handed to `reflect_cross_give`, and it SHALL be answered with a run reply frame with no body. Any other stream SHALL be a batch: the serving guest SHALL take batches from one address only, the first that sent one, hand each to `reflect_cross_take`, call `reflect_cross_work` until Lean says nothing is possible (at most 64 calls), and answer with the bytes of `reflect_cross_batch`. The guest with `reflect.peer` SHALL open one QUIC connection per exchange from UDP port 9000, send `reflect_cross_batch`, hand the answer to `reflect_cross_take`, work, and open the next exchange no sooner than 20 ms after the last answer; an exchange with no answer in 8 seconds SHALL be abandoned and the batch sent again on a new connection. When the Lean guest reports closed, each guest SHALL print its record on serial, one `reflect: cross ` line for each line of `reflect_cross_record`, then `reflect: cross done`. The names in the record are each guest's address and port until entity keys land (`homoiconic-q59.66`); nothing signs a record. A guest whose Lean guest reports failure SHALL print its error line and power off.

#### Scenario: Two guests on one bridge

- GIVEN guest A booted with `reflect.wire_port=4446 reflect.spawn=far`, handed `examples/cross-race.hom` as bytes with budget 100000 by `quic-client`, and guest B booted with `reflect.peer=<A>:4446`
- WHEN B calls A
- THEN within 90 seconds both serial logs end with `reflect: cross done`, A's record has seven entries and B's six, and they are the entries two guests in one Lean process record (`kernel/CrossCheck.lean`)

### Requirement: The wire check replays the guests' records

`unikernel/check-wire.sh` SHALL require KVM and Cloud Hypervisor v54.0, build with `build-net.sh`, run `kernel/CrossingContract.lean` and refuse an axiom outside `propext`, `Classical.choice` and `Quot.sound`, run `kernel/CrossCheck.lean` and require 48 `ok` lines and no `FAIL`, and then, for each run, boot the serving guest, hand it the program with `quic-client`, boot the calling guest, wait for both to close, read both records off the serial logs, and run `unikernel/out-net/cross-check check` on the program's bytes and the two records. It SHALL require `accepted` and the expected process lines for `examples/cross-reply.hom`, `examples/cross-name.hom`, and `examples/cross-race.hom` under `reflect.take=old` and `reflect.take=new`; for the last two it SHALL require one program, two different records, `[1, 2]` and `[2, 1]` reported by the guest, and the two schedules. From the records of the `old` run it SHALL make tampered records and require each refused with its reason: an entry moved, dropped from the middle and repeated (the link), the last entry dropped (the head), and, with the chain made again by `cross-check reseal`, a taking repeated, a taking dropped and an acknowledgement dropped (the merge), a local event repeated (the replay), and the takings in the other order (the comparison). It SHALL remove the TAPs and the bridge on exit. That each refusal is made by the check it is credited to is shown by `kernel/cross-controls.py`, which undoes one check at a time in a copy of the kernel and requires the test to fail (`unikernel/evidence/cross-controls.log`).

#### Scenario: The check passes

- GIVEN morphie with Cloud Hypervisor 54.0
- WHEN `sh unikernel/check-wire.sh` runs
- THEN it prints `wire guests ok` and exits 0 (`unikernel/evidence/check-wire.log`)
