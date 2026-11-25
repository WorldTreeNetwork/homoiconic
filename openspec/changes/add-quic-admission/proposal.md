# Let no unlisted host hold the guest's QUIC service

> **ACTIVE BUILD** 2026-11-24 (UTC). Bead `homoiconic-q59.63`. Found by the first review of `add-entity-keys` (finding M5).

**Rigor:** instrument (trusted, unproved image code in `unikernel/`; nothing in Lean changes).

## Why

`unikernel/net.zig` keeps one QUIC server connection. A first flight that opens takes it whenever it is free, and every packet that opens, a replay included, starts its two idle seconds again. Opening an Initial needs no key: Initial keys come from the connection ID in the packet. So a host that is on no `reflect.allow` and keeps sending first flights, new or replayed, holds the one connection for as long as it sends, and every allowed entity is shut out. The spec says so today (`openspec/specs/unikernel-net/spec.md`, "A datagram that does not open changes nothing").

## The property

A host that holds no allowed key cannot stop an allowed entity from completing a handshake and getting its answer, beyond a stated bounded delay, whatever datagrams it sends. The assumptions under which this holds, the bound, and what a host on the path can still do are in `design.md` §1 and §6.

## What changes

- A serving guest holds a table of 12 server connections in two pools (`unikernel/admit.zig`): 4 for first flights that show nothing, and 8 for first flights from an address that has shown it receives, at most one handshake in progress per IPv4 address there. Nothing is evicted: a connection leaves its slot only by its own end (refused, answered and done, idle once accepted) or by a cap of 2 s from its first Initial to an accepted handshake, which nothing a peer sends extends.
- When the first-flight pool is full, a first Initial that opens and carries no valid token is answered with a Retry (RFC 9000 §8.1.2, §17.2.5) and nothing is kept. The token is the guest's MAC over the client's address, port and the Retry's connection ID, with the time; a first Initial that carries a valid one goes to the second pool with its address validated.
- The client side of `quic.zig` answers one Retry: it checks the integrity tag (RFC 9001 §5.8), takes the new connection ID and the token, makes its Initial keys again and sends its ClientHello again with the token. It checks the server's transport parameters name the first connection ID and, after a Retry, the Retry's (RFC 9000 §7.3).
- A packet whose number was opened already in its space, or is 64 or more below the largest opened, is a duplicate and counts as not opened (RFC 9000 §12.3).
- The wire port (a crossing's serving guest) uses the same table; the calling guest answers a Retry with the same client code.
- `quic-self` drives the table in one process against a flood of new and replayed first flights, replayed packets of a finished exchange, an unlisted host holding the address pool and one that stalls its handshake, with an allowed client served each time within the bound. `check-quic.sh` does the same against a real guest with a flood from a second address, and shows a stalled unlisted client holds its slot no longer than the cap and a client that cannot answer a Retry is served once a slot frees.

## What does not change

The `RFL1` frame, the handshake and its allow-lists on both ends, packet protection, the 3× limit on an address not validated, the give-up after ten sends, the clock, the UDP service of a guest with no QUIC word, and everything in Lean. "A datagram that does not open changes nothing" still holds; a Retry is sent only for an Initial that opens and changes nothing in the guest.

## What this does not give

An attacker on the path can drop the allowed client's datagrams, or replay its token-bearing Initial from its address within the token's 10 seconds; neither can be closed here. A flood faster than the guest reads datagrams is dropped by the host's queues without regard to sender. An entity on the list is trusted not to hold slots. See `design.md` §6.

## Journey

No new UI because this is a guest image and its check scripts; the callers are `quic-client`, a crossing's calling guest and Mjolnir.

## Who is affected

Mjolnir vendors the client side of `quic.zig` unmodified from `e9a4c86`. That client ignores a Retry. It still works against the new guest whenever a first-flight slot is free, which is always when no other host is filling them; under a flood it is not served until it is re-vendored (a bead in Mjolnir says what to take). Nothing about a working Mjolnir path is removed: before this change, under the same flood, it was not served either.
