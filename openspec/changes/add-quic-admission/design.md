# Design: admission to a guest's QUIC service

Bead `homoiconic-q59.63`. Dates are UTC. Code: `unikernel/admit.zig` (new), `unikernel/quic.zig`, `unikernel/net.zig`, `unikernel/quic-client.zig`, `unikernel/quic-self.zig`, `unikernel/check-quic.sh`.

## 1. The property, and what it assumes

Call the allowed client C, at IPv4 address `a_C`, and the other host X.

X holds no key on the guest's `reflect.allow`. X is **off the path**: it receives only what is sent to the h IPv4 addresses it holds (`a_C` is not one of them), it sees no datagram to or from `a_C`, and it does not stop C's datagrams. It may send any datagrams, from any source address and port, at any rate.

**Property.** Suppose

- (A0) X is not on the guest's Ethernet segment: X's frames reach the guest through a router (on morphie, the host itself) and carry the router's MAC. The guest answers to the source MAC of the frame it got (`net.zig` `sendUdp`), so a host on the segment receives whatever it asks for at any IPv4 address it names (§6);
- (A1) the guest reads every datagram that reaches it: X's datagrams arrive no faster than the guest handles them (§5 gives the cost of each kind, measured);
- (A2) h + a ≤ 7, where a is the number of connections other allowed entities hold in the address pool (§2) while C connects;
- (A3) C's handshake, once admitted, finishes within 2 seconds of guest time not spent in runs (the cap, §2), counting the queue ahead of each of its datagrams: its handshake time with no X plus, for its two datagrams before acceptance, the 8 receive buffers and the host's TAP queue (1000 on morphie) at the largest cost per datagram in §5. With the measured costs (README) this is well under 2 s; it is computed there, not assumed.

Then C completes its handshake and gets its answer. Its first Initial is admitted to the first-flight pool, or it draws a Retry and the Initial that answers the Retry is admitted to the address pool. Once C is admitted, no datagram of X's removes, replaces or changes C's connection.

**The bound.** C's time is its time with no X, plus at most one round trip (the Retry), plus the guest's time on X's datagrams that arrived before each of C's datagrams. The guest handles datagrams one at a time from 8 receive buffers; under (A1) the queue ahead of one of C's datagrams is at most those 8 buffers and the host's TAP queue, each of X's datagrams costing at most the largest cost in §5. The check takes this as: each allowed client served within 1 second of starting while the flood runs, five in a row (`check-quic.sh`), and in `quic-self`, where the guest's time is not counted, within one round trip of its time with no flood.

Why it holds:

1. Nothing is evicted. A connection leaves its slot only by its own handshake or exchange, or by the 2 s cap, which runs from its own first Initial and which nothing extends (§2).
2. A first Initial that finds the first-flight pool full and opens draws a Retry, and C's answer to it carries a token for `(a_C, C's port, the Retry's connection ID)`. Only a host that receives at `a_C` can hold such a token, so no handshake of X's is in progress in the address pool for `a_C`, and by (A2) a slot there is free: C's Initial with the token is admitted.
3. Once admitted, a datagram reaches C's connection only if its first packet carries one of that connection's IDs (random, 64 bits, sent only to `a_C`) and it comes from C's address and port; it changes the connection only if a packet in it opens under the connection's keys, which X does not have, and is not a duplicate (§4).
4. A Retry forged to C by X is not taken: C takes a Retry only if its integrity tag checks with C's first destination ID, which X has not seen (RFC 9001 §5.8).
5. X's own expensive datagrams are closed-loop: a handshake X runs to the guest's refusal needs the guest's flight before X can send the flight that is refused, so at most one is in flight for each slot X holds (4 + h), and C's datagram waits behind at most that many first flights (§5).

What X still costs the guest is time (§5).

## 2. The table

`unikernel/admit.zig`, `Table`: 12 slots, each a `quic.Conn` with its peer's IPv4 address and UDP port, the time its first Initial opened (`born`), the time a packet last opened on it (`seen`) and whether the guest has answered it.

| Pool | Slots | Taken by | Limit |
|---|---|---|---|
| First flight | 4 | a first Initial with no valid token, from any address | none per address (an address here is not shown) |
| Address | 8 | a first Initial with a valid token (§3) | one connection not yet accepted per source IPv4 address |

A **first Initial** is a datagram of at least 1200 bytes whose first packet is a version 1 Initial with 8-byte connection IDs (`quic.firstShape`), and whose destination ID is no slot's.

**Routing.** A datagram's first packet names a destination ID (bytes 6..14 of a long header, 1..9 of a short one). A slot whose own ID or original destination ID it is takes the datagram only from that slot's address and port; from anywhere else the datagram is dropped and starts nothing. A datagram that names no slot is dropped unless it is a first Initial.

**Admission of a first Initial.**

1. With a token that is valid for its source address, port and destination ID (§3): if no connection not yet accepted from the same IPv4 address holds an address slot and one is free, open a server connection there; otherwise, if a first-flight slot is free, open it there; otherwise drop it. Either way the connection has its address validated (`Conn.validated`, so the 3× limit does not apply: RFC 9000 §8.1), `Conn.retried` set and the token's original destination ID in `Conn.tp_odcid`; give it the datagram; it holds the slot only if the datagram opens. `validated` only lifts the limit: the Initial space is finished when a Handshake packet opens (`Conn.hs_opened`, RFC 9001 §4.9.1), as for any connection, or the server would resend its padded ServerHello to a client that has moved on.
2. Without a valid token (none, or one that does not check): if a first-flight slot is free, open a server connection there as above, not validated. Otherwise, if the Initial opens (`quic.initialOpens`: the Initial keys of its destination ID, header protection, the AEAD tag and the frame walk, with nothing kept), answer with a Retry (§3). Otherwise nothing.

A connection is built in its free slot; when the datagram does not open, the slot stays free. The connection in any other slot is never touched.

**Leaving a slot** (`Table.sweep`, after every datagram and on every tick):

1. refused: at once (the handshake check failed);
2. not accepted 2 s after `born`: the cap;
3. accepted, answered, and no 1-RTT flight on: its reply was acknowledged or given up after ten sends;
4. accepted, no 1-RTT flight on, and nothing opened for 2 s: idle.

Rule 2 replaces "two idle seconds" for a connection not accepted: a packet that opens no longer keeps it. Rule 4 is the idle rule, kept for accepted connections, where only an allowed entity's packets open and duplicates do not count.

The guest's own time in a run is not a peer's: after each run (`reflect_reply_bytes`, or a crossing's work), every connection not yet accepted has `born` moved on by the run's length (`Table.pause`), so an allowed entity's long run does not cap out the handshakes queued behind it. Nothing a peer sends moves `born`.

**What happens to the old give-way.** There is none. A new Initial never replaces a connection: an answered connection keeps resending its reply until it is acknowledged or given up, a refused one leaves at once, and an unfinished one leaves at the cap. A client who finds the first-flight pool full is sent a Retry instead of waiting for the one connection to idle.

**Why one address per handshake in the address pool, and per IPv4 address.** A token shows the client reads at that address, so the address is something X must hold, not forge. Counting per port would let one host fill the pool from 8 ports. Two allowed clients behind one IPv4 address that both need the address pool at once take turns: the second's token Initial is dropped and resent (20 ms, 40 ms, …) until the first is accepted.

**Why the first-flight pool exists.** A client that cannot answer a Retry (Mjolnir's vendored client today) is served whenever a first-flight slot is free, which is always unless another host fills them. Retry for every first flight would close that path (§7).

## 3. Retry and the token

**Retry** (RFC 9000 §17.2.5): first byte `0xf0` with four random low bits, version 1, destination ID the client's source ID, source ID 8 new random bytes, the token, and the integrity tag: AES-128-GCM under the fixed key `be0c690b9f66575a1d766b54e368c84e` and nonce `461599d35d632bf2239825bb` over the pseudo-packet (the length and bytes of the client's original destination ID, then the Retry up to its tag), with no plaintext (RFC 9001 §5.8). It is 71 bytes, sent for a first Initial of at least 1200 that opened, to the address it came from: one well under the 3× limit, and nothing kept.

**Token**, 32 bytes: the time it was made (8 bytes, the guest's clock in nanoseconds), the client's original destination ID (8), and the first 16 bytes of HMAC-SHA256 under the guest's token key over the client's IPv4 address, UDP port, the Retry's source ID, the time and the original ID. The token key is 32 bytes from `RDRAND`, made when the table is, kept in guest memory and never sent or kept across boots. A token is valid when its MAC checks for the datagram's source address and port and its destination ID (which a client that answers a Retry sets to the Retry's source ID), and it was made at most 10 s ago and not in the future. 10 s covers a client's ten sends of its Initial (6.36 s). An invalid token is treated as none.

**The server's transport parameters** after a Retry name the client's first destination ID (`Conn.tp_odcid`, from the token) as `original_destination_connection_id` (0x00) and the Retry's source ID, which is the token Initial's destination ID (`Conn.orig_dcid`, the source of its Initial keys and of routing), as `retry_source_connection_id` (0x10) (RFC 9000 §7.3); without a Retry, 0x00 is the first Initial's destination ID and there is no 0x10, as now.

**The client** (`quic.zig`, `Conn.onRetry`) takes a Retry only if it is a client, has taken no Retry and opened no Initial, the Retry's destination ID is its own source ID, its source ID is not the client's first destination ID (RFC 9000 §17.2.5.2), the token is 1 to 64 bytes, and the tag checks against its first destination ID. `retryTag` takes IDs of any length, so RFC 9001's vector (no destination ID) checks it. The client then sets its destination ID to the Retry's source ID, makes its Initial keys again from it with its packet numbers going on, keeps the token for the header of every Initial it sends (`size` and `seal` carry its length and bytes), and sends its ClientHello again at once with a fresh count of ten tries. Its transcript does not change: a Retry is not a TLS message. Anything else is dropped. When the server's flight is read, its `original_destination_connection_id` must be the client's first destination ID, its `initial_source_connection_id` the source ID of the server's Initial, and its `retry_source_connection_id` present exactly when a Retry was taken and equal to its source ID; otherwise the client refuses the connection. The server does not check the client's `initial_source_connection_id`, as before this change.

## 4. Duplicates

Each packet number space keeps the largest packet number opened and which of the 63 below it opened (`rx_top`, `rx_win`). A packet whose tag checks and whose frames are allowed, and whose number opened before or is 64 or more below the largest, is a duplicate (RFC 9000 §12.3: a receiver discards duplicates). It counts as not opened, with everything that means today: not acknowledged, not counted for the 3× limit, not activity for the idle rule, and no frame of it is read. The check is made after the tag checks and before anything changes. The ACK frame is built from the same window: largest, then the run below it.

## 5. What it costs

**Memory.** 12 connections of `@sizeOf(quic.Conn)` bytes each (about 70 KiB each, about 840 KiB in all; `quic-self` prints the exact number), in the guest's static data. No table grows with what is sent: the token carries its own state, and the per-address limit is a look at 8 slots. The guest has 512 MiB.

**Time per datagram of X's**, by kind, measured on morphie with the guest built as it is (ReleaseSmall, baseline x86_64, so AES and SHA-256 are in software) and recorded in `unikernel/README.md`:

| Kind | Work |
|---|---|
| garbage, or a packet for no slot | parse and drop |
| a packet for a slot, from another address | a look at 12 slots |
| a first Initial when the first-flight pool is full | Initial keys (HKDF), open (AES-GCM over ~1200 bytes), frame walk, token MAC, Retry tag |
| a token Initial when its address already holds a slot | token MAC |
| a first Initial admitted | as above, then the server's first flight: an X25519 key, an X25519 product and an Ed25519 signature |

Admissions are bounded in number: at most 4 per 2 s into the first-flight pool from forged sources (they cannot finish and leave at the cap), one per 2 s for each address X holds, and one for each handshake X runs to the guest's refusal. That last is cheap for X and dear for the guest: the guest checks the name before any signature, so X pays one X25519 product and sends a Certificate with any key, while the guest makes an X25519 key, an X25519 product and an Ed25519 signature. It is closed-loop (X needs the guest's flight first) and one per slot X holds, so at most 4 + h are in flight at once.

## 6. What an attacker can still do

- **On the path.** Drop C's datagrams: no protocol closes that. See C's token-bearing Initial and replay it from `a_C` within its 10 s: if C's connection has gone by then, the replay holds the address slot for `a_C` until the cap, and C's next token Initial from `a_C` waits up to 2 s more (C resends at 20 ms, 40 ms, …, so it is in by 2.54 s). Forge a Retry to C, since it sees C's destination ID: C then talks to an address the attacker chose a connection ID for and fails or is delayed. An attacker on the path is not bounded here.
- **Be on the guest's Ethernet segment.** The guest answers the source MAC of the frame it got, and a bridge learns whatever source MAC a port sends. So a host on the segment receives the Retry, and a valid token, for any IPv4 address it names, with no ARP: it can fill the address pool from eight made-up addresses and renew each at the cap, or hold `a_C`'s own address slot. It is on the path for every address. Binding the token to the MAC would not help. The guest's segment should hold only the router and guests that trust each other; on morphie it is the host and, in `check-wire.sh`, two guests. The calling guest of a crossing already takes any ARP reply that names its peer (`noteArp`), which lets a host on the segment redirect the crossing; that predates this change.
- **Hold 8 − a or more addresses it receives at.** Then it can keep every address slot in a handshake, renewing each at the cap, and C is admitted only while a first-flight slot is free. On a LAN, a host can answer ARP for many addresses; that host is on the path for those addresses.
- **Outrun the guest.** A flood faster than the guest's cost per datagram (§5) fills the 8 receive buffers and the host's TAP queue, and the host drops what does not fit without regard to sender, C's datagrams among them. C's resends then go through only by chance. This is a flood of the link, like dropping; (A1) excludes it, and the measured rate is stated.
- **Make the guest work.** Within (A1) each datagram costs at most the largest cost in §5, and admissions are bounded as there.
- **Fill the first-flight pool.** X can keep all 4 first-flight slots full from forged addresses. Clients that answer a Retry go to the address pool; one that cannot, such as current Mjolnir, waits for a free slot and loses the race to a flood.
- **Nothing, and still cost a slow client.** The 2 s cap applies with no attacker: a handshake not accepted 2 s after its first Initial (a client on a bad path, five or six losses in a row) fails, where before a connection whose packets kept opening was never cut off.
- **An allowed entity** is trusted: it can hold an address slot for as long as it keeps opening packets once accepted, and its runs use the guest's one processor.

## 7. Choices weighed

| Option | What it does against X | Taken |
|---|---|---|
| Several slots, evicting the oldest unauthenticated | A flood of first flights at the rate the guest takes them evicts C mid-handshake. C has sent its Handshake flight by then and cannot recover inside that connection; it gives up after ten sends. The guest cannot tell C's first Initial from a forged one. | No: eviction is what the flood uses. |
| Retry for every first flight | The cleanest cost: no first flight costs state until the address is shown. Every client must answer a Retry; current Mjolnir does not and would stop working. | Only when the first-flight pool is full. Making it every time is one test in `Table.take`; Mjolnir must answer Retry first. |
| A cap from first Initial to accepted | Bounds how long anything unlisted holds a slot. Alone, X retakes every freed slot first. | Yes, 2 s, for both pools. |
| Duplicate rejection | A replay no longer opens, so it is not activity, not acknowledged and not counted. | Yes. |
| Never letting an unauthenticated connection displace or delay an authenticated one | | Yes, and more: nothing displaces anything. |
| Pools apart | The address pool holds only handshakes whose address was shown, one per IPv4 address, so forged first flights cannot reach it. | Yes. |

## 8. Mjolnir

**Does current Mjolnir still work against the new guest when the first-flight pool is not full? Yes.** A first Initial with no token finds a free first-flight slot and is served exactly as before: no Retry is sent, the server's transport parameters are byte for byte what they were (0x00 the first destination ID, no 0x10), and its acknowledgement of the reply frees the slot at once. This is checked with the client of `e9a4c86` itself, copied unmodified into `unikernel/compat/e9a4c86/` and built as `out-net/quic-client-e9a4c86` (`check-quic.sh`), not with a flag that imitates it. If that check failed, the guest code would not be pushed.

Mjolnir (`native/reflect_quic/quic.zig`) is `quic.zig` from `e9a4c86` unmodified (the file has not changed in this tree since), and its `host.zig` acknowledges the reply. It does not read a Retry: `longPacket` returns for packet type 3 without opening it. Against the new guest it is served exactly as before whenever a first-flight slot is free, and its acknowledgement frees its slot at once. More than four Mjolnir exchanges at once get Retries for the fifth and later, which it ignores; its resent Initial is admitted when a slot frees (previously it waited for the one connection to give way). Under a flood that fills the first-flight pool it is not served; it was not served under such a flood before this change either. A Mjolnir bead asks it to vendor the new `quic.zig` (with `onRetry` and the transport-parameter check) and nothing else; `host.zig` needs no change. The server's transport parameters without a Retry are unchanged, so Mjolnir's client sees the same handshake.

## 9. Checks, each with a control

`quic-self` (in one process, run by `build-net.sh`):

| Exit | Check | Control (the fix undone) |
|---|---|---|
| 70 | the Retry integrity tag of RFC 9001 appendix A.4 | another tag key |
| 71 | a server sends a Retry when its first-flight pool is full; the client answers it and the exchange finishes, with the server's transport parameters naming the first ID and the Retry's | the client drops Retry packets |
| 72 | a client refuses a server whose parameters do not name the Retry it took | the client does not read them |
| 73 | a replayed datagram of every kind opens nothing on either end and is not acknowledged; an accepted connection given only replays leaves at the idle rule | duplicates open |
| 74 | the flood: while forged first flights, replays of one first flight and of every datagram of a finished exchange, and an unlisted host with an address of its own that takes tokens and stalls are given to the table, an allowed client is served within one round trip of its time with no flood, five times in a row | no Retry (a tokenless Initial is dropped when the pool is full); evicting the oldest unaccepted connection instead of Retry |
| 75 | an unlisted host at one address holds at most one address slot, whatever tokens it has | the per-address limit removed |
| 76 | a stalled unlisted client that keeps sending packets that open leaves its slot at the cap | packets that open keep a connection not accepted (the old idle rule) |
| 77 | a token is refused from another address or port, for another destination ID, after 10 s and with a changed byte | the MAC not compared |
| 78 | a replay from `a_C` of C's token Initial (the on-path case) delays C's next connection by no more than the cap and C's resend | none: it measures a stated limit |
| 79 | a client drops a second Retry, one after an Initial opened, one for another destination ID, one with an empty token or one over 64 bytes, one whose tag was made with another original ID, and one whose source ID is its first destination ID | each of the tag check, the one-Retry rule, the opened-Initial rule and the destination-ID rule undone |

Exit 71 also requires that after a Retry exchange whose reply is acknowledged the server has nothing more to send (control: `validated` finishes the Initial space again, as before the split). Exit 77 has a control per clause: the time window removed, the port left out of the MAC, the destination ID left out of the MAC, the MAC not compared.

`check-quic.sh` (a real guest on morphie):

The flood and the stalled clients run on a fresh boot of their own, after the main serving guest, so that no earlier step's connection holds a slot (review S7).

- **old client**: factorial with `quic-client-e9a4c86`, the client Mjolnir vendors, on a guest with free slots. Control: none needed; it is the compatibility claim itself.
- **flood**: `quic-client … flood <second-ip> <seconds> <rate> <file>` sends from the second address new first flights, one first flight again and again, and every datagram the allowed client sent in an earlier exchange (`quic-client … keep <file>`); while it runs, five allowed clients in turn are each served within 1 second, replies equal to the Linux process's. Control: no Retry; the step fails.
- **cap**: four clients with a key not on the list (`stall`) take the first-flight pool, finish the address check and keep sending packets that open without ever sending a Certificate. A client that answers a Retry is served within 1 second at once; `quic-client-e9a4c86`, which ignores Retry as Mjolnir does, is served only after the cap, between 1.5 and 6 seconds from its start. Control: the old idle rule; the old client is not served while the stalled clients send.
- The existing steps keep passing with their texts revised: the second address in `spoof` now hears only its own handshake's packets, never one of the exchange's; the abandoned handshake no longer delays the next client; the forged first flight's copies from another address come within the cap.
- `check-wire.sh`: the crossing's serving guest uses the same table. One more run (`cross-reply`) has `quic-client … flood` fill the serving guest's first-flight pool while the calling guest calls, so its exchanges go through Retries; the records must be accepted as in the plain run. Control: the client drops Retry packets; that run fails.
