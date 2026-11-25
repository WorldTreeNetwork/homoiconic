# Tasks

- [x] Design read in a fresh context (Opus): send-back, M1–M3 and S1–S7 answered in the design and deltas (`review.md`)
- [x] `quic.zig`: duplicate packets count as not opened (`rx_top`, `rx_win`), ACK frame from the window
- [x] `quic.zig`: `firstShape`, `initialOpens`, `retryTag`, `makeRetry`, token make and check; `validated` apart from `hs_opened`; `tp_odcid`, `retried`; a server admitted with a token names the Retry in its transport parameters
- [x] `quic.zig`: the client takes one Retry (`onRetry`), puts the token in its Initials, checks the server's transport parameters; the client checks 0x00, 0x0f and 0x10; test seam `Conn.poke`
- [x] `admit.zig`: the table, its two pools, admission, routing, `sweep`, `pause`
- [x] `net.zig`: the quic port and the wire port use the table; per-slot reply address and answered flag; the calling guest unchanged but for Retry
- [x] `quic-client`: `stall`, `keep`, `flood`; `spoof` hears only its own handshake
- [x] `unikernel/compat/e9a4c86/`: the client Mjolnir vendors, unmodified, built as `out-net/quic-client-e9a4c86`
- [x] `quic-self`: 70 to 79, and `@sizeOf(quic.Conn)` printed
- [x] `check-quic.sh`: the flood with five allowed clients, the stalled clients with an allowed client and the client of `e9a4c86`; the old client; all on a fresh boot; revised `spoof`, abandoned handshake and forged first flight steps
- [x] `check-wire.sh`: one run with the serving guest's first-flight pool flooded, so the calling guest answers Retries
- [x] Each new check shown to fail with its fix undone (`unikernel/quic-admission-controls.sh`, `unikernel/evidence/q59.63-controls.log`)
- [x] The guest's cost per datagram of each kind, and the flood rate it keeps up with, measured on morphie and recorded in `unikernel/README.md`
- [x] Final run on morphie (tree `5107fa8`; `check.sh` fails at the deep-bytes step of the kernel deep-walk change `3e0635d`, outside this change) from a `git archive` export of the rebased tree: `build.sh`, `build-net.sh`, `check.sh`, `check-net.sh`, `check-quic.sh`, `check-wire.sh`; logs `unikernel/evidence/q59.63-<sha>-*.log`, `source.sha256`, `objects.sha256`
- [x] Mjolnir bead `mjolnir-qwo5`: vendor the new `quic.zig` for Retry. Current Mjolnir still works: the client of `e9a4c86` is served with a first-flight slot free (check-quic.sh, morphie)
- [x] Specs, `ARCHITECTURE.md`, `LEARNINGS.md`; fold
