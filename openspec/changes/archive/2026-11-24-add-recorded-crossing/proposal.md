# Record the crossing, and replay the record on one machine

> **FOLDED** 2026-11-24 into `openspec/specs/crossing/spec.md`, `channels`, `unikernel-net`, `zig-host` and `bytecode-machine`. Was ACTIVE BUILD, 2026-11-24. Bead `homoiconic-q59.51`. Duke, 2026-11-24: this is the priority, ahead of syntax and speed.

**Rigor:** architecture (new Lean definitions and theorems in `Reflect`; a new guest protocol in trusted, unproved image code).

## Why

`kernel/Surface/Remote.lean` prints the schedule one machine's scheduler chooses for one fixed program. Nothing records the order in which two guests delivered messages, no received schedule is replayed, the receiving guest runs the closure only to its first send, and the sender can offer only the program compiled into Lean. The vision's claim is D4: delivery order is an input, it is recorded, and a run across machines replayed from its record gives the same result on one machine.

## What changes

- Each guest runs its own processes under the Lean scheduler and keeps its own log. An entry is a local event, or one half of a crossing: a request put out to the peer, a crossing taken in from the peer, or the peer's acknowledgement. Entries are sealed and parent-linked as log entries are (`0d48980`).
- A program is given to the serving guest over QUIC as bytes, not compiled in (the boot file is the entity key's, `add-entity-keys`). A start request can cross: the quoted program and its start data leave as bytes and the other guest runs the new process under its scheduler, to its end or its budget. A send can cross: it meets a receive on the other guest.
- `Reflect.combine` merges two logs into one schedule of the one-machine network, refusing a pair in which an entry is out of place, a crossing is taken twice, taken without being put out, or left unacknowledged. The checker replays that schedule with `schedRun` and compares each process with what its guest reported.
- Proved: a record the checker accepts is a schedule of `Network sourceP` from the program, and the merge consumes each log exactly, in its order. Tested on two real guests: the replay ends where the guests said, two forced delivery orders of one program give two records and two results, and tampered records are refused.
- `Surface.Remote`, the four `reflect_remote_*` exports and `unikernel/remote-check.zig` are removed.

## What stays a hypothesis

- That a guest ran the Lean it claims to. A record is checked, not believed: a guest that lies is caught only where its log stops being a schedule, or its report differs from the replay.
- That a name cannot be forged across machines. The names handed over with a crossing are a list of numbers in the packet, and the receiving guest takes them as sent. The replay computes them again, so a wrong list is refused when the record is checked, not when it is received.
- That a signature names an entity. Zig checks it outside the kernel (`unikernel/cross-check.zig`, keys from `add-entity-keys`); the kernel does not.
- Liveness. A crossing put out may never be taken.

No new UI because this is a kernel, image and check change.
