# A key per entity

> **FOLDED** 2026-11-24 (UTC) into `openspec/specs/unikernel-net/spec.md` and `openspec/specs/unikernel-image/spec.md`. The two deltas for the remote channel's requirements were dropped before the fold: `add-recorded-crossing` replaced those requirements and its text already has the keys, the allow-lists and both refusals. Was ACTIVE BUILD since 2026-11-24 (UTC). Two fresh-context reads, both send-back, the second on text and check lists only with the design called sound and buildable; their findings are in `review.md` with what was done. A third read, to confirm the second's five fixes, was cut off by an API limit and not run again; the orchestrator said to go on to implementation.

**Rigor:** instrument (trusted, unproved image code; no change to a definition or theorem of `Reflect`). Bead: `homoiconic-q59.49`.

## Why

`unikernel/quic.zig` holds the guest's P-256 private key as a constant. Every guest built from the tree has that one identity, anyone with the source can present it, and the pin a client holds says only "built from this source". The guest does not authenticate its client at all.

Duke decided on 2026-11-24: a key per entity. An entity is the agent a guest runs for, and the same entity started again is the same identity.

## What changes

- An entity has an Ed25519 key. Its name is identikey-protocol's fingerprint of that key, 32 bytes, written in base58 (`design.md` §1).
- The key reaches the guest as the file given at boot (`--initramfs`), 32 bytes. It is not in the image, the image's hash, the command line or the tree.
- The QUIC handshake uses raw Ed25519 public keys in both directions. Each end checks the other's name against `reflect.allow`, given on the command line. The two guests of the remote channel pin each other.
- A guest asked for QUIC with no key prints `reflect: no entity key` and powers off. The constant key and certificate are deleted.
- Found by the first review and fixed here: stream data was taken from Initial packets, whose keys anyone can make, so a serving guest ran bytes from anyone and a client could be handed a forged reply. Stream data is now taken only from 1-RTT packets on an accepted connection.
- A guest with a QUIC word no longer answers plain UDP on `reflect.port`. Otherwise anyone could run a program beside the allow-list.
- `check-quic.sh` and `check-wire.sh` make their keys on each run and check: two keys are two identities, one key twice is one identity, a wrong server pin is refused, a client that is not allowed is refused, and a guest with no key serves no QUIC.

## What does not change

The `RFL1` frame, the UDP service of a guest with no QUIC word, packet protection, loss recovery, the amplification limit, the clock, and everything in Lean.

## What this does not give

The launcher and the host hold every key they give a guest; nothing is attested (`design.md` §3). There is no delegation from an entity's key to a lesser key, no rotation and no revocation. A `p256` entity cannot connect. No other QUIC implementation has been tried. A host on no list can still hold a guest's one connection (`homoiconic-q59.63`).

## Journey

No new UI because this is a guest image and its check scripts; the caller is a launcher such as Mjolnir.

## Who is affected

Mjolnir spawns these guests with a fixed pin and an older vendored `quic.zig` (`mjolnir-6h01`). After this change its guests refuse QUIC until it gives each one a key and names. A Mjolnir change follows this one.
