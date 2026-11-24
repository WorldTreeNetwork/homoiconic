# unikernel-net delta: guests carry crossings and print their records

## REMOVED Requirements

### Requirement: Two guests carry a remote channel over QUIC

Replaced by "Two guests run one program and record the crossing".

### Requirement: The wire check uses two real guests

Replaced by "The wire check replays the guests' records".

## ADDED Requirements

### Requirement: Two guests run one program and record the crossing

The command line MAY carry `reflect.wire_port=<port>` or `reflect.peer=<a.b.c.d>:<port>` as before, and with either MAY carry `reflect.spawn=far`, `reflect.take=old|new` and `reflect.budget=<n>`. The guest with `reflect.peer` SHALL read the program's byte form from `/boot/program` and start it through the Lean export `reflect_cross_start`; the guest with `reflect.wire_port` SHALL start with no process. Zig SHALL hold the Lean session and SHALL NOT read a packet, an entry or a process. The client SHALL open one QUIC connection per exchange, send the bytes of `reflect_cross_batch` and give the answer to `reflect_cross_take`; the server SHALL give what it receives to `reflect_cross_take` and answer with `reflect_cross_batch`. Between exchanges each SHALL call `reflect_cross_work`. When the session reports closed, each guest SHALL print its record on serial, one `reflect: cross ` line per line of `reflect_cross_record`, then `reflect: cross done`.

#### Scenario: Two guests on one bridge

- GIVEN guest B booted with `reflect.wire_port=4446` and guest A with `reflect.peer=<B>:4446 reflect.spawn=far` and `examples/cross-race.hom` as bytes
- WHEN A connects to B
- THEN within 90 seconds both serial logs end with `reflect: cross done`

### Requirement: The wire check replays the guests' records

`unikernel/check-wire.sh` SHALL require KVM and Cloud Hypervisor v54.0, build with `build-net.sh`, run `kernel/CrossCheck.lean` with no `FAIL` line, boot two guests for each program and setting, collect both records from serial, and run `unikernel/out-net/cross-check` on the program's bytes and the two records. It SHALL require `accepted` and the expected result for each run, two different schedules for the two `take` settings of `examples/cross-race.hom`, and, for records with an entry moved, dropped from the middle, dropped from the end and repeated, `refused` with the reason of the check that catches each.

#### Scenario: The check passes

- GIVEN morphie with Cloud Hypervisor 54.0
- WHEN `sh unikernel/check-wire.sh` runs
- THEN it prints `wire guests ok` and exits 0 (`unikernel/evidence/check-wire.log`)
