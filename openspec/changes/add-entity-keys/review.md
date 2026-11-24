# Reviews

## 2026-11-24, first read: send-back

Fresh context, Claude Fable 5.2, given only this directory and the code paths. Read-only.

Sound as written: the name (the 19 prefix bytes, base58 rules and the fixture key match identikey-protocol's own fixtures), the delivery of the key by `--initramfs` (the word limit, the module bounds, nothing prints the bytes), no fallback key, and the exit test.

Must-fix findings, and what was done:

| | Finding | Done |
|---|---|---|
| M1 | `takeFrames` takes STREAM frames in every packet number space and callers act on `peer_fin` alone. Shown with a probe on today's `quic.zig`: one client Initial with a STREAM frame leaves a server with `accepted=false peer_fin=true` and the bytes readable, so a serving guest evaluates them; a forged server Initial hands a client a forged reply. | Design §4 and the spec: STREAM only in 1-RTT, CRYPTO only in Initial and Handshake, `readApp` and the end of stream only on an accepted connection. Checks in `quic-self` and on a guest, each with a control. |
| M2 | `reflect.port` stays open: every QUIC guest still runs any `RFL1` program sent over plain UDP by anyone, beside the allow-list. | A guest with a QUIC word drops every datagram to `reflect.port` (design §3, a new requirement, a check). What stays reachable without a name is stated. |
| M3 | The TLS design left out what a mistake made on both sides would hide: context strings, what each signature and Finished covers, the application secrets' transcript, exact parsing. No check for a server or client that presents a key it does not hold, a signature over another transcript, a client that sends only Finished, or a bad Finished. | Design §2 "The handshake, message by message"; the spec states the same; `quic-self` gains a peer that breaks each rule (`Conn.signer`, `Conn.fault`), each with a control. |
| M4 | Deltas that contradicted the design or themselves: "sends no offer" when B refuses A; kept scenarios that boot with no key or allow-list; "no private key in the tree" beside the fixture seed; `reflect_boot_take` against the image spec's "SHALL NOT read or change the bytes". | Each corrected; a delta for `unikernel-image` added. |
| M5 | "Hold it for 2 seconds a time" understates the hold: a first flight that opens, resent or replayed, keeps the one connection for as long as it is sent. With an allow-list this is how an unlisted host shuts listed ones out. | Stated as it is in the spec; not fixed here. Bead `homoiconic-q59.63`. |

Notes taken: the seed stays in memory inside the key pair (said so); 32 zero bytes are refused; the `denied` check must not pass against a dead guest and the give-way after a refusal is timed; the name vector is now a value identikey's own code printed; the hello randoms are random; Finished is compared in constant time; no rotation or revocation (said so).

Not done: a run against another TLS 1.3 stack with raw public keys. Stated in the spec as not checked.
