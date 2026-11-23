# A channel on another machine

> **ACTIVE BUILD**, banner added 2026-11-23 after the fact. The code landed in `793b583` (2026-11-19); its message reports that the two guests exchanged the message and the schedule replayed (no log of `unikernel/check-wire.sh` is kept in `unikernel/evidence/`). The change had no banner and no spec delta, so fold could not admit it (`docs/LEARNINGS.md`, 2026-11-22). The deltas below were written on 2026-11-23 from the code and the checks, for `homoiconic-q59.44`, and were not read by another model family.

**Rigor:** instrument (trusted, unproved image code and a tested, unproved Lean check; no change to a definition or theorem of `Reflect`). Bead: `homoiconic-q59.44`.

A send on a remote name leaves as the wire bytes of a closure and a reply name. The other machine runs the closure, and the message it sends on that name comes back on the QUIC stream. The schedule of those deliveries is the log. The same program, given that schedule, finishes with the same result on one machine.

A name inside one machine is still a number the holder may use. That another machine cannot forge a name is a hypothesis about the host, not a proof.

The QUIC packet format, the certificate, and the virtio-net device are unchanged. `reflect.quic_port` still carries one RFL1 exchange. The remote channel uses `reflect.wire_port` and `reflect.peer`.

## What the deltas found

The code is narrower than the second paragraph above, and the deltas say what it does:

- The log is the schedule the scheduler takes for the program on one machine. Nothing records the order the two guests delivered in, and no received schedule is replayed. The guest that takes the offer runs the function only to its first send (`homoiconic-q59.51`).
- The offer is one program built into Lean; a peer guest cannot send another.
- `reflect.quic_port` with `reflect.wire_port` or `reflect.peer` is not refused, and the two then share one connection, so "`reflect.quic_port` still carries one RFL1 exchange" holds only when it is given alone (`homoiconic-q59.50`).
- The `zig-host` sentence that names every export that evaluates missed the four `reflect_remote_*` exports from `793b583` until this delta.
