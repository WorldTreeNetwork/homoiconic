# Tasks

- [ ] Design read in a fresh context (Opus), verdict and findings in `review.md`, findings fixed
- [ ] `quic.zig`: duplicate packets count as not opened (`rx_top`, `rx_win`), ACK frame from the window
- [ ] `quic.zig`: `firstShape`, `initialOpens`, `retryTag`, `makeRetry`, token make and check; a server admitted with a token is validated and names the Retry in its transport parameters
- [ ] `quic.zig`: the client takes one Retry (`onRetry`), puts the token in its Initials, checks the server's transport parameters; test seams `Conn.poke` and `Conn.no_retry`
- [ ] `admit.zig`: the table, its two pools, admission, routing, `sweep`
- [ ] `net.zig`: the quic port and the wire port use the table; per-slot reply address and answered flag; the calling guest unchanged but for Retry
- [ ] `quic-client`: `noretry`, `stall`, `keep`, `flood`; `spoof` hears only its own handshake
- [ ] `quic-self`: 70 to 78, and `@sizeOf(quic.Conn)` printed
- [ ] `check-quic.sh`: the flood with five allowed clients, the stalled clients with an allowed and a `noretry` client; revised `spoof`, abandoned handshake and forged first flight steps
- [ ] Each new check shown to fail with its fix undone (`unikernel/quic-admission-controls.sh`, `unikernel/evidence/q59.63-controls.log`)
- [ ] The guest's cost per datagram of each kind, and the flood rate it keeps up with, measured on morphie and recorded in `unikernel/README.md`
- [ ] Final run on morphie from a `git archive` export of the rebased tree: `build.sh`, `build-net.sh`, `check.sh`, `check-net.sh`, `check-quic.sh`, `check-wire.sh`; logs `unikernel/evidence/q59.63-<sha>-*.log`, `source.sha256`, `objects.sha256`
- [ ] Mjolnir bead: vendor the new `quic.zig` for Retry; say whether current Mjolnir still works
- [ ] Specs, `ARCHITECTURE.md`, `LEARNINGS.md`; fold
