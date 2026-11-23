# Authenticated QUIC on the reflect guest

> **ACTIVE BUILD**, banner added 2026-11-23 after the fact. The code landed in `8e7098c` (2026-11-19) and its message reports that `unikernel/check-quic.sh` passed (no log of that run is kept in `unikernel/evidence/`). The change had no banner and no spec delta, so fold could not admit it (`docs/LEARNINGS.md`, 2026-11-22). The deltas below were written on 2026-11-23 from the code and the check, for `homoiconic-q59.43`, and were not read by another model family.

**Rigor:** instrument (trusted, unproved image code; no kernel or semantics change). Bead: `homoiconic-q59.43`.

QUIC v1 runs on the existing virtio-net UDP path. The optional `reflect.quic_port` word leaves the UDP service and its command line unchanged. Zig carries datagrams and stream bytes. Lean still produces the reply through `reflect_reply_bytes`.

The guest clock is the KVM paravirtual clock. The one-program `clock_gettime` stand-in is untouched. The peer identity is a compiled P-256 certificate; the client checks its SHA-256 before it sends application data. A different pin is refused.

One bidirectional stream carries one RFL1 frame. After that exchange the guest accepts another handshake, so a budget reply does not take the guest down. The NIC feature bits, BARs, and queues are unchanged.

## What the deltas found

Writing the SHALLs from the code turned up four things the proposal does not say. Each is stated in the delta as it is, with a bead:

- The clock read uses a wrapping 64-bit multiply, so it goes backwards once the TSC delta since the last pvclock update passes about 2^32 (`homoiconic-q59.48`).
- The certificate's private key is a constant in `unikernel/quic.zig`, so the pin authenticates the source tree's key, not one guest. The guest does not authenticate the client (`homoiconic-q59.49`).
- QUIC datagrams are not checked against their UDP checksum, and any datagram to the QUIC port, even one that fails packet protection, changes where the guest sends its next QUIC packets (`homoiconic-q59.53`).
- `check-quic.sh` removes its TAP on exit but leaves the guest to its 400 s timeout when a step fails.
