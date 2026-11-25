# unikernel-net delta: admission to a guest's QUIC service

## ADDED Requirements

### Requirement: A serving guest admits connections into a bounded table

A guest with `reflect.quic_port` or `reflect.wire_port` SHALL hold its server connections in a table of 12 slots (`unikernel/admit.zig` `Table`), each a connection with its peer's IPv4 address and UDP port, the time its first Initial opened and the time a packet last opened on it. Four slots SHALL be the first-flight pool and eight the address pool. Nothing else that the guest keeps for QUIC SHALL grow with what is sent to it, and nothing SHALL be evicted: no datagram SHALL remove, replace or change a connection in a slot other than by opening on that connection.

A datagram's first packet names a destination connection ID. A slot whose own ID or original destination ID it is SHALL be given the datagram only when it comes from that slot's address and port; from anywhere else it SHALL be dropped and SHALL start nothing. A datagram that names no slot SHALL be dropped unless it is a first Initial: at least 1200 bytes whose first packet is a QUIC version 1 Initial with 8-byte connection IDs (`quic.zig` `firstShape`).

A first Initial whose token is valid (the requirement "A full first-flight pool answers with a Retry") SHALL be given a free address slot, with its address validated, unless a connection not yet accepted from the same IPv4 address holds an address slot or none is free, in which case it SHALL be dropped. A first Initial with no valid token SHALL be given a free first-flight slot, not validated; with none free it SHALL be answered with a Retry if it opens, and dropped otherwise. A connection SHALL be built in its free slot and SHALL hold it only if the datagram opens on it.

A connection SHALL leave its slot when it is refused, at once; when it is not accepted 2 seconds after its first Initial opened, whatever it has opened since (the cap); when it is accepted, the guest has answered it, and no 1-RTT flight of the guest's is on (the reply was acknowledged or given up); and when it is accepted, no 1-RTT flight is on, and nothing has opened on it for 2 seconds (`Table.sweep`). The table SHALL be swept after every datagram and on every pass of the guest's loop.

The table holds 12 connections of `@sizeOf(quic.Conn)` bytes each in the guest's static data; `quic-self` prints the number.

#### Scenario: Pools in one process

- GIVEN `quic-self` and a table
- WHEN four first Initials with no token arrive, then a fifth, then an Initial that answers the fifth's Retry
- THEN the four are in the first-flight pool, the fifth draws a Retry and is kept nowhere, the answer is in the address pool with its address validated, and the client finishes and is answered (exit 71 otherwise)

#### Scenario: One handshake per address in the address pool

- GIVEN `quic-self`, a table whose first-flight pool is full, and a host at one address with a key on no list that answers every Retry
- WHEN it sends one first flight after another, each answering a Retry with a valid token
- THEN at most one of its connections holds an address slot at a time (exit 75 otherwise)

#### Scenario: A stalled handshake leaves at the cap

- GIVEN `quic-self` and a client with a key on no list that validates its address and then sends, every 100 ms, a Handshake packet that opens and never its Certificate
- WHEN 2 seconds have passed since its first Initial opened
- THEN its slot is free, while it is still sending (exit 76 otherwise)

### Requirement: A full first-flight pool answers with a Retry

A Retry (RFC 9000 §17.2.5) SHALL be 71 bytes: the first byte `0xf0` with four random low bits, version 1, the client's source connection ID as its destination ID, 8 new random bytes as its source ID, a 32-byte token, and the integrity tag of RFC 9001 §5.8, AES-128-GCM under the key `be0c690b9f66575a1d766b54e368c84e` and nonce `461599d35d632bf2239825bb` over the client's original destination ID (its length, then its bytes) and the Retry up to the tag (`quic.zig` `retryTag`, `makeRetry`). It SHALL be sent only for a first Initial that opens, only to the address and port it came from, and nothing SHALL be kept for it.

The token SHALL be the time it was made (8 bytes, nanoseconds of the guest's clock), the client's original destination ID (8 bytes) and the first 16 bytes of HMAC-SHA256, under a 32-byte key from `RDRAND` made when the table is made, of the client's IPv4 address, UDP port, the Retry's source ID, the time and the original ID. It SHALL be valid for a first Initial whose source address and port and destination ID are the ones it was made for, at most 10 seconds after it was made and not before; any other token SHALL be treated as no token. The key SHALL NOT be sent, printed or kept across boots.

A connection admitted with a valid token SHALL be validated from its first packet (RFC 9000 §8.1), and its server SHALL send the token's original destination ID as `original_destination_connection_id` and its first Initial's destination ID as `retry_source_connection_id` (RFC 9000 §7.3). A connection admitted without one SHALL send its first Initial's destination ID as `original_destination_connection_id` and no `retry_source_connection_id`, as before.

A client (`quic.zig` `onRetry`) SHALL take one Retry, and only when it has taken none and opened no Initial, the Retry's destination ID is its own source ID, its token is 1 to 64 bytes, and its tag checks with the client's first destination ID. It SHALL then take the Retry's source ID as its destination ID, make its Initial keys from it with its packet numbers going on, put the token in every Initial it sends, and send its ClientHello again at once with ten tries. Its handshake transcript SHALL NOT change. It SHALL refuse a server whose `original_destination_connection_id` is not its first destination ID, or whose `retry_source_connection_id` is present without a Retry taken, absent with one, or not the Retry's source ID. The host client and the calling guest of a crossing SHALL answer a Retry this way.

What this does not give SHALL be stated as it is. The integrity tag's key is public; the tag binds a Retry to the client's first destination ID, which a host off the path has not seen. A host on the path can forge one. A client that does not read a Retry, such as Mjolnir's vendored `quic.zig` of `e9a4c86`, is served only through the first-flight pool.

#### Scenario: The RFC's Retry

- GIVEN `quic-self`
- WHEN it computes the integrity tag of the Retry of RFC 9001 appendix A.4
- THEN the tag is `04a265ba2eff4d829058fb3f0f2496ba` (exit 70 otherwise)

#### Scenario: Transport parameters that do not name the Retry

- GIVEN `quic-self`, a client that took a Retry, and a server whose parameters name the first destination ID and no Retry
- WHEN the client reads the server's flight
- THEN it refuses the connection and sends nothing more (exit 72 otherwise)

#### Scenario: Tokens that are not valid

- GIVEN `quic-self` and a token made for one address, port and Retry
- WHEN it comes from another address, from another port, with another destination ID, 10 seconds and one nanosecond after it was made, and with one byte changed
- THEN each is treated as no token (exit 77 otherwise)

### Requirement: A duplicate packet counts as not opened

Each end SHALL keep, for each packet number space, the largest packet number that opened and which of the 63 below it opened (`quic.zig` `rx_top`, `rx_win`). A packet whose tag checks and whose number opened before, or is 64 or more below the largest, SHALL count as not opened (RFC 9000 §12.3), with all the requirement "Each end proves its entity key and admits only allowed names" says of a packet not opened; the check SHALL be made before anything changes. The ACK frame SHALL name the largest number and the numbers that opened in one run below it.

#### Scenario: Replays in one process

- GIVEN `quic-self` and a finished exchange
- WHEN every datagram either end sent is given again to the end it went to, and an accepted connection is given only replays for 2 seconds
- THEN no replay opens, nothing is acknowledged for them, and the accepted connection leaves its slot by the idle rule (exit 73 otherwise)

### Requirement: A host with no allowed key cannot shut an allowed client out

Let a host hold no key on the guest's `reflect.allow`, receive only what is sent to the IPv4 addresses it holds, see nothing sent to or from the allowed client's address, and send any datagrams from any source. While the guest reads every datagram that reaches it, other allowed entities and that host's addresses together hold at most 7 address slots, and the allowed client's handshake finishes within 2 seconds of its admission, the allowed client SHALL complete its handshake and get its answer: its first Initial is admitted to the first-flight pool, or the Initial that answers its Retry is admitted to the address pool, and once admitted its connection is changed only by datagrams from its address and port that open under its keys. Its time SHALL be at most its time with no such host, one round trip more for the Retry, and the guest's time on that host's datagrams queued ahead of its own.

What this does not give SHALL be stated as it is (`openspec/changes/archive/<date>-add-quic-admission/design.md` §6). A host on the path can drop the client's datagrams, forge it a Retry, or replay its token Initial from its address within the token's 10 seconds, which delays its next connection by up to the cap. A host that receives at 8 or more addresses less the allowed entities' slots can keep the address pool full. A flood faster than the guest's cost per datagram is dropped by the host's queues without regard to sender, and the guest's rate is measured, not proved (`unikernel/README.md`). An allowed entity is trusted not to hold slots. A client that cannot answer a Retry is served only while a first-flight slot is free.

#### Scenario: A flood in one process

- GIVEN `quic-self`, a table, and another host that gives it, between each two datagrams of an allowed client, first flights from forged addresses, one first flight again and again, every datagram of a finished exchange, and from an address of its own Initials that answer Retries with a key on no list and then stall
- WHEN the allowed client connects, five times in a row
- THEN each time it is answered within one round trip of its time with no flood (exit 74 otherwise)

#### Scenario: A flood against a guest

- GIVEN a running guest with a QUIC port, and `quic-client ... flood <second-ip>` sending from the second address new first flights, one first flight again and again, and every datagram the allowed client sent in an earlier exchange, at the rate stated in `unikernel/README.md`
- WHEN five allowed clients connect in turn while it runs
- THEN each is answered within 1 second of its start, its reply equal to the Linux process's (`check-quic.sh`)

#### Scenario: Stalled clients and the cap on a guest

- GIVEN a running guest with a QUIC port and four `quic-client ... stall` clients with a key not on its list, which fill the first-flight pool, show their address and keep sending packets that open without a Certificate
- WHEN an allowed client and an allowed `noretry` client, which drops Retry packets as Mjolnir's client does, start at once
- THEN the first is answered within 1 second, and the second between 1.5 and 6 seconds after its start, while the stalled clients still send (`check-quic.sh`)

#### Scenario: A replay on the path, in one process

- GIVEN `quic-self` and an allowed client whose exchange through a Retry has finished
- WHEN its token Initial is replayed from its own address, and it connects again at once
- THEN it is answered no later than the cap and its next resend after it (exit 78 otherwise)

## MODIFIED Requirements

### Requirement: An optional port serves one authenticated QUIC stream
<!-- base: 754bebc58b9cac19e42a2408a7937aed1ba1a9c0 openspec/specs/unikernel-net/spec.md -->

The command line MAY carry `reflect.quic_port=<port>`, at most once, with a port in 1..65535; a repeated or malformed word, the word together with `reflect.wire_port` or `reflect.peer`, or the word without `reflect.allow`, SHALL be refused as other bad configuration is (`reflect: the network address is not valid`). Without the word, and without the words of a crossing, the guest SHALL serve UDP exactly as before and SHALL NOT start the clock. With it the guest SHALL have an entity key or stop before `reflect: ready` (the requirement "The entity key is the file given at boot"), and after `reflect: ready` it SHALL start the paravirtual clock, make its table of server connections and print `reflect: quic <port>` on serial (`unikernel/net.zig` `net_serve`, `parse`). The QUIC layer (`unikernel/quic.zig`) SHALL speak QUIC version 1 with TLS 1.3, the cipher suite TLS_AES_128_GCM_SHA256, X25519 key exchange and Ed25519 raw public keys in both directions (the requirement "Each end proves its entity key and admits only allowed names"), with 8-byte connection IDs and random values from `RDRAND`. A connection SHALL carry one bidirectional stream. The guest SHALL read a stream only on a connection whose handshake was accepted, which a client on the allow-list reaches and no other. The client's stream, ended by FIN, SHALL be one `RFL1` frame of at most 1200 bytes, judged by the frame rules of the UDP service: a ping answered by a pong, a well-framed run with an out-of-range budget answered with status 3 and not evaluated, a run whose reply exceeds 1176 bytes answered with status 2, and anything else answered with nothing. A valid run SHALL call `reflect_reply_bytes` once, and the guest SHALL write the answering frame on the stream with FIN (`net.zig` `quicPump`, `answerBytes`). Zig SHALL NOT read the program or the outcome. The guest SHALL serve up to 12 connections at once, in the table of the requirement "A serving guest admits connections into a bounded table", answering each when its stream ends, one run at a time; a budget reply leaves the guest serving. The build-only allocation hook SHALL apply to a QUIC run as it does to a UDP run.

#### Scenario: Factorial, a budget reply, and the guest still up

- GIVEN a guest booted with a key file and `reflect.ip=192.168.249.2 reflect.port=4444 reflect.quic_port=4445 reflect.allow=<the client's name>` on a TAP
- WHEN `unikernel/out/quic-client` sends factorial with budget 100000000, then `examples/forever.hom` with budget 5000, then factorial again over new handshakes
- THEN the first two reply frames have kind 1 and status 0, and each payload equals, byte for byte, what `unikernel/out/reply run` gives for the same program and budget in a Linux process (`unikernel/check-quic.sh`)

#### Scenario: Two QUIC services on one command line

- GIVEN a key file and the command line `reflect.ip=192.168.249.2 reflect.port=4444 reflect.quic_port=4445 reflect.allow=<a name>` with `reflect.wire_port=4446` added, and separately with `reflect.peer=192.168.249.3:4446` added
- WHEN the guest starts
- THEN serial shows `reflect: the network address is not valid` and no `reflect: ready`, and Cloud Hypervisor exits (`check-quic.sh`)

### Requirement: A datagram that does not open changes nothing
<!-- base: 754bebc58b9cac19e42a2408a7937aed1ba1a9c0 openspec/specs/unikernel-net/spec.md -->

A datagram to a QUIC port SHALL change a connection, and where the guest sends, only when one of its packets opens: its AEAD tag checks under keys of the connection it is given to, its frames are allowed, and it is not a duplicate (`quic.zig` `recv`, `open`). A server connection SHALL install the Initial keys named by a first Initial only if that packet opens, and either end SHALL take the peer's connection ID only from an Initial that opened (`quic.zig` `longPacket`). The guest SHALL send a server connection's packets to the address its first opened Initial came from and SHALL NOT move that address afterwards for any packet; there is no connection migration (`net.zig` `quicDatagram`). A server connection SHALL be given datagrams only from that IPv4 address and UDP port; a datagram from anywhere else SHALL NOT reach it, whatever it would open, and a first Initial that names its ID from anywhere else SHALL start nothing.

A first Initial SHALL start a connection only under the requirement "A serving guest admits connections into a bounded table": in a free slot, and only if it opens there on a connection built in that slot. A first Initial in a datagram shorter than 1200 bytes SHALL start nothing. A Retry SHALL be sent only for a first Initial that opens, and changes nothing in the guest. Every other long-header packet that does not open under the keys of the connection it names, of any type and from any address, SHALL be dropped with no effect. The guest's own connection to a peer (`reflect.peer`) SHALL never be replaced by a datagram.

What this does not give SHALL be stated as it is. Initial keys are derived from the connection ID in the packet, so opening as an Initial shows a well-formed QUIC client and nothing about who sent it, and a first Initial from a forged address can take a first-flight slot until the cap. A client is authenticated when its handshake finishes and not before (the requirement "Each end proves its entity key and admits only allowed names"). What a host on no list can and cannot do to an allowed client is the requirement "A host with no allowed key cannot shut an allowed client out".

#### Scenario: A second address during an exchange

- GIVEN a running guest with a QUIC port and a client whose handshake has been accepted
- WHEN `quic-client ... spoof <local-ip>` sends, from a second address, a short-header datagram, a full-size Initial, a small Initial and a Handshake packet of random bytes and then the well-formed first datagram of another handshake, sends nothing for half a second, and then sends its program
- THEN the second address receives only long-header packets addressed to the other handshake's source ID, none of the exchange's, and the client's reply equals the Linux process's (`check-quic.sh`)

#### Scenario: Garbage long headers after the reply

- GIVEN the same exchange, with the guest's first copy of the reply discarded by the client as a lost datagram would be
- WHEN the same four garbage datagrams are sent from the client's address and then from the second address before the guest resends, and the client then sends nothing for half a second
- THEN the guest resends the reply to the client within that time, the second address receives nothing of the exchange's, and a later handshake is served (`check-quic.sh`)

#### Scenario: An abandoned handshake

- GIVEN a guest whose last client refused the handshake and sent no more
- WHEN another client connects at once
- THEN it is served at once in another slot, and the unfinished connection leaves its slot at the cap (`check-quic.sh`, the step after the wrong pin)

#### Scenario: Garbage in one process

- GIVEN `unikernel/out/quic-self`
- WHEN a full-size Initial, a Handshake packet and a short-header datagram of random bytes are given to both ends before every step of a clean exchange and of a lossy one
- THEN no garbage datagram opens, the client's ID for the server does not change, both exchanges finish, and a real first flight cut to 1199 bytes starts nothing on a server

### Requirement: QUIC survives loss and reordering
<!-- base: 754bebc58b9cac19e42a2408a7937aed1ba1a9c0 openspec/specs/unikernel-net/spec.md -->

Each packet number space SHALL keep its unacknowledged flight and resend it, waiting 20 ms shifted left by the number of tries so far, at most by 6 (1.28 s), until the flight is finished or has been sent 10 times. After the tenth send, 6.36 s after the first, the flight SHALL be given up and not sent again (`quic.zig` `due`, `seal`, `max_tries`). Received CRYPTO and STREAM data SHALL be placed by offset, so packets that arrive out of order are used once the gap is filled (`holePut`).

An acknowledgement SHALL finish only the flight of the packet number space it arrived in, and only when one of its ranges holds a packet number that flight went out as, from its first send to its latest (`quic.zig` `ack`, `acked`; RFC 9002 section 3). No other packet of a space is sent while its flight is on, so every number in that span is a copy of the flight. The same number in another space is another packet. The flights that no acknowledgement in their own space reaches SHALL finish as RFC 9001 has them finish: a server's Initial flight when the server opens a Handshake packet, after which it opens no Initial (section 4.9.1); a client's Initial flight when the client sends a Handshake packet; a client's Handshake flight when its 1-RTT packet is acknowledged (section 4.1.2); and a server's Handshake flight when the client's Finished checks.

A packet with a CRYPTO or STREAM frame that opens SHALL leave an acknowledgement owed in its space. Every packet an end sends carries its space's ACK frame and pays what is owed. When a space owes an acknowledgement and has no flight on, the end SHALL send a packet in that space with only an ACK frame, once, which asks for nothing back and is not resent (`quic.zig` `ack_due`, `ackOnly`, `send`). A client that has its Finished to send owes nothing more in the Initial space. So the host client acknowledges the reply before it exits, and the guest that sent the offer acknowledges the answer (`quic-client.zig`, `net.zig` `wirePump`); the guest stops resending a reply when that acknowledgement arrives, and the connection leaves its slot. A long header's Length SHALL be written in its shortest form, and every variable-length integer read SHALL be stepped over by its own encoded width, so a longer form than needed also reads.

What this does not give SHALL be stated as it is. An acknowledgement is sent once; when it is lost the guest resends the reply to a client that has gone, up to the 10 sends over 6.36 s, and the connection holds its slot until then. There is no congestion control or connection close, and stream data is limited to 8192 bytes each way. A connection is not closed for a flight given up; it leaves the guest's table by the rules of the requirement "A serving guest admits connections into a bounded table". An end whose flight is given up is not told why. `quic-client` exits 6 when a flight of its own has been given up and 1.28 seconds have passed since its last send with no reply (`quic.zig` `gaveUp`), and 4 at its 60 seconds otherwise; a guest that called a peer prints `reflect: the peer gave no answer`.

#### Scenario: Loss and reordering against the guest

- GIVEN a running guest with a QUIC port
- WHEN `quic-client ... loss` drops every fifth datagram it sends and holds one back to send after the next
- THEN factorial still comes back, byte for byte the Linux process's reply (`check-quic.sh`)

#### Scenario: Loss in one process

- GIVEN `unikernel/out/quic-self`, which `unikernel/build-net.sh` runs
- WHEN it checks the RFC 9001 initial keys, a clean exchange, an exchange that drops every fifth datagram and swaps pairs in both directions, and a wrong pin
- THEN it prints `quic self ok` and the build continues

#### Scenario: An acknowledgement in another space

- GIVEN `quic-self`, a server whose Initial and Handshake flights have both gone out as packet 0, and a client that was given the Initial packet of that datagram and not the Handshake packet
- WHEN the client's resent first flight, an Initial that acknowledges Initial packet 0, reaches the server
- THEN the server's next datagram is its Handshake flight alone, and the exchange finishes (exit 21 when the acknowledgement finished the Handshake flight too); the client, whose flight that packet 0 acknowledged, sent its acknowledgement of the server's Initial as an Initial of at least 1200 bytes

#### Scenario: A reply the client acknowledges is sent once

- GIVEN a finished exchange
- WHEN the client's next datagram, in `quic-self`, reaches the server, and a real guest is watched on its TAP for 10 seconds from just before `quic-client` connects in `check-quic.sh`
- THEN that datagram is one 1-RTT packet, the server sends nothing more for two minutes of its clock and the client nothing more (exits 30 to 32 otherwise); the guest sends exactly one datagram with a 1-RTT packet in it, the reply

#### Scenario: A reply nobody acknowledges

- GIVEN a finished exchange whose client's acknowledgement is lost, in `quic-self`, or a guest whose client was `quic-client ... silent`, which takes the reply and leaves without acknowledging it
- WHEN the server is left for two minutes of its clock in `quic-self`, and a real guest is watched on its TAP for 11 seconds after that client has left in `check-quic.sh`
- THEN in `quic-self` the server resends the reply fewer than 10 times and nothing after the first 70 seconds, and the client sends nothing after its one acknowledgement; the guest sends at least one and at most 9 more datagrams and none after the eighth second

### Requirement: An address that is not validated is sent at most three times what came from it
<!-- base: 754bebc58b9cac19e42a2408a7937aed1ba1a9c0 openspec/specs/unikernel-net/spec.md -->

Until a server connection has opened a Handshake packet, or was admitted with a valid token, the bytes it has sent SHALL NOT exceed three times the bytes of the datagrams that opened under its keys (RFC 9000 section 8.1; `quic.zig` `seal`, `amplification`, `rx_bytes`, `tx_bytes`, `validated`). Both counts are UDP payload bytes. A packet that would pass the limit SHALL NOT be sent and SHALL NOT count as a try. It SHALL go as soon as a datagram that opens raises the limit, so a client that is where it says and loses the guest's answers is served when its resent first flight arrives. A Handshake packet that opens validates the address and lifts the limit: its keys come from the ServerHello, which was sent to that address and nowhere else. A valid token validates it too: it was sent in a Retry to that address and port and nowhere else. Because a server connection is given datagrams only from the address it answers (the requirement "A datagram that does not open changes nothing"), the bytes counted came from that address as far as a source address says. A datagram that does not open is not counted, which is less than the RFC allows. A Retry is 71 bytes, sent once for a first Initial of at least 1200 bytes that opened.

A server SHALL expand every datagram that carries its Initial flight to at least 1200 bytes (RFC 9000 section 14.1), with PADDING in the Initial packet sized by the packets that follow it in the datagram, and SHALL count the whole datagram against the limit before it sends the Initial packet (`quic.zig` `send`, `size`, `seal`). A client's first flight of 1200 bytes therefore draws at most three datagrams of 1200 bytes. A packet with only an ACK frame is not padded.

What this does not give SHALL be stated as it is. The limit bounds the factor, not the number: each well-formed first flight with a forged source that finds a first-flight slot free takes it until the cap and draws up to three times its bytes to that address. The padding is checked against the guest's own client and `quic-self`, not against another QUIC implementation.

#### Scenario: A first flight from a forged address

- GIVEN a running guest with a QUIC port that has answered its last client, and the 1200-byte first datagram of a real handshake written by `quic-client ... initial`
- WHEN it is sent from 192.168.249.77, where nobody is, and the same bytes are sent three more times from another address within the next 1.5 seconds
- THEN in 8 seconds the guest sends the forged address at least two datagrams, each of at least 1200 bytes, and at most 3600 bytes, sends nothing to any other address, and serves factorial to a real client afterwards (`check-quic.sh`)

#### Scenario: A first flight nobody follows, in one process

- GIVEN `quic-self` and a server given one first flight
- WHEN the server is asked to send every 10 ms for a minute of its clock, and then the client's resent first flight arrives
- THEN the server has sent more than once, each datagram at least 1200 bytes (exit 29 otherwise), and at most three times the flight's bytes (exit 24 otherwise), sends again at once when the second flight arrives, and the exchange finishes

### Requirement: The QUIC check uses a real guest
<!-- base: 754bebc58b9cac19e42a2408a7937aed1ba1a9c0 openspec/specs/unikernel-net/spec.md -->

`unikernel/check-quic.sh` SHALL require KVM and Cloud Hypervisor v54.0, build with `build-net.sh` (which runs `quic-self`), create its own TAP, make three key files from `/dev/urandom` and take their names from `unikernel/out-net/entity name`, boot the network image with `reflect.quic_port`, the first key as the file given at boot and `reflect.allow` naming the second, wait up to 90 seconds for `reflect: quic <port>` on serial, and run factorial, the 5000-step budget, factorial on a new handshake, a client that expects another name (`wrong`), loss straight after it, a client whose key is not allowed (`denied`) with the allowed client started 0.1 seconds after it and served within 1 second, a ping to `reflect.port` that must go unanswered, the second address (`spoof`, from a second address it gives its TAP), factorial again, the first flight with a bad and then a good UDP checksum, whose answer it requires to be at least 1200 bytes, factorial once more, factorial while it counts on the TAP the datagrams that carry the reply, factorial for a `silent` client, a watch on the TAP for the resends of that unacknowledged reply to stop, a first flight from a forged address, factorial after it, the flood of the requirement "A host with no allowed key cannot shut an allowed client out" with five allowed clients, and the stalled clients with an allowed and a `noretry` client, comparing reply payloads with `unikernel/out/reply`. Before that boot it SHALL boot the two refused command lines, a command line with a QUIC port and no `reflect.allow`, a guest with a QUIC port and no file given at boot, a guest given a 31-byte file, a guest given 32 zero bytes, a guest with `reflect.hook=alloc` that an `early` client must leave running and the allowed client must stop, and a guest given the third key, whose entity line it requires to differ from the first key's and which the client that expects the first name must refuse. After the serving guest it SHALL boot the first key again and require the same entity line and factorial from the same pinned client. It SHALL require that the serving guest printed nothing but its entity line and its two start lines, print one `ok` line a step, and stop its guest and remove its TAP on exit, pass or fail.

#### Scenario: The check passes

- GIVEN morphie with Cloud Hypervisor 54.0
- WHEN `sh unikernel/check-quic.sh` runs
- THEN it prints twenty-eight `ok` lines and `quic guest ok`, and exits 0 (`unikernel/evidence/check-quic.log`)

### Requirement: Each end proves its entity key and admits only allowed names
<!-- base: 754bebc58b9cac19e42a2408a7937aed1ba1a9c0 openspec/specs/unikernel-net/spec.md -->

The command line MAY carry `reflect.allow=<name>[,<name>...]`, at most once, with one to eight names in the text form and no name twice. It SHALL be given with exactly one of `reflect.quic_port`, `reflect.wire_port` and `reflect.peer` and not otherwise; a missing, repeated or malformed word SHALL be refused as other bad configuration is (`reflect: the network address is not valid`, `net.zig` `parse`). There is no setting that admits every name.

The TLS 1.3 handshake inside QUIC SHALL use the signature scheme `ed25519` (0x0807) and raw public keys (RFC 7250). The ClientHello SHALL offer only `ed25519` and only raw public keys for both ends (extensions 19 and 20, value 2), and the server's EncryptedExtensions SHALL select them. Each Certificate message SHALL hold one entry, the 44-byte SubjectPublicKeyInfo of an Ed25519 key (`30 2a 30 05 06 03 2b 65 70 03 21 00` and the key); any other entry SHALL refuse the connection. The server SHALL send a CertificateRequest with an empty context and one extension, `signature_algorithms` holding `08 07`, and the client SHALL answer the server's flight with Certificate, CertificateVerify and Finished (`unikernel/quic.zig` `buildServerFlight`, `onServerFlight`, `onClientFlight`). The ClientHello's extensions 19 and 20 SHALL each be the list `01 02` and the EncryptedExtensions' the one byte `02`. The ClientHello and ServerHello randoms SHALL be 32 random bytes.

The messages SHALL cover what RFC 8446 says they cover. The server's CertificateVerify SHALL be a signature over 64 spaces, `TLS 1.3, server CertificateVerify`, a zero byte and the hash of the transcript from ClientHello through the server's Certificate; the client's SHALL use `TLS 1.3, client CertificateVerify` and the transcript through the server's Finished and the client's Certificate (section 4.4.3). The server's Finished SHALL cover the transcript through its CertificateVerify and the client's the transcript through the client's CertificateVerify (section 4.4.4). The application secrets SHALL come from the transcript through the server's Finished and nothing after it (section 7.1). A reader SHALL refuse the connection for a Certificate whose context is not empty, that has no entry, a second entry or entry extensions, a CertificateVerify whose scheme is not `08 07` or whose signature field is not 64 bytes, a message out of this order (a server flight with no CertificateRequest, a client flight that begins with Finished), a Finished that differs (compared in constant time), and bytes after Finished. It SHALL wait while a message is incomplete and refuse when a complete message is the wrong one.

A client SHALL, before it sends its own key or any application data, take the name of the server's key, require it to be in its allow-list, verify the CertificateVerify signature over the transcript with that key, and check the server's Finished. A server SHALL take the name of the client's key, require it to be in its allow-list, verify the client's CertificateVerify over the transcript and check the client's Finished, and only then make its 1-RTT keys. STREAM frames SHALL be taken only from 1-RTT packets (RFC 9000 section 12.4) and CRYPTO frames only from Initial and Handshake packets, which is stricter than the RFC: it lets a server send CRYPTO in 1-RTT, and this stack sends none there. A packet whose tag checks SHALL have its frames walked before anything is changed, and a frame that is malformed, of a type this stack does not read, or not allowed in the packet's space SHALL fail the whole packet (`quic.zig` `allowed`). A packet that fails, a duplicate, and every packet for a refused connection, SHALL count as not opened wherever this spec says "opens": it is not acknowledged, its bytes are not counted for the amplification limit, it does not validate the address, it installs no keys and gives no connection ID, and it does not set where the guest sends, start a connection, or keep one from going idle. `readApp` SHALL give nothing, and the end of the peer's stream SHALL NOT be noted, on a connection whose handshake was not accepted (`quic.zig` `takeFrames`, `readApp`); with the frame rule in place nothing reaches this second gate, and no check does. Before this change a STREAM frame in an Initial packet, whose keys anyone can make, was taken: a serving guest ran its bytes, and a client could be handed a forged reply. On a connection whose handshake was accepted, `Conn.peer_name` SHALL be the other end's name; it is set at no other point.

An end that fails any of these checks SHALL mark the connection refused, SHALL send nothing more on it, an acknowledgement included, and SHALL take nothing more from it. A serving guest's refused connection SHALL leave its slot at once. There is no CONNECTION_CLOSE, so the other end is not told and gives its flight up after ten sends. A guest prints nothing when it refuses a client. The two guests of a crossing each have a key and allow the other's name; what they print when one refuses the other is the requirement "Two guests run one program and record the crossing".

What a name on a connection means SHALL be stated as it is: the other end signed this handshake's transcript with that entity's key, which shows the entity or the host it was given to (the requirement "The entity key is the file given at boot"). A key cannot hand a lesser key to a guest; there is no delegation. The handshake is checked against this stack's own client and `quic-self`, not against another QUIC implementation and not against a known-answer trace, so a context string or transcript wrong in the same way on both ends would pass. A standard server's 1-RTT packet that carries PING, HANDSHAKE_DONE or CRYPTO would be dropped here, with any reply in it.

#### Scenario: A client that is not allowed

- GIVEN a running guest with a QUIC port whose `reflect.allow` names one key
- WHEN `quic-client ... denied` connects with another key, and then the allowed client connects at once
- THEN the first client accepts the guest, gets no reply, sees its own flight given up and exits 0, and the allowed client, started 0.1 seconds after it, is served within 1 second of its start, while the first is still resending (`check-quic.sh`)

#### Scenario: Refusals in one process

- GIVEN `quic-self`, where `Conn.signer` makes an end sign with another key than the one it presents and `Conn.tamper` changes, drops or follows a handshake message as it is built, before it enters the sender's own transcript, so that the sender's signature and Finished stay right
- WHEN a client expects another name than the server's (exit 42 unless refused); a server does not allow the client's name (43); a server presents an allowed key and signs with another (44); a client does the same (45); the right key signs a transcript hash with one bit changed, as server (46) and as client (47); a client sends only its Finished, with no Certificate and no CertificateVerify (48); a Finished has one bit changed, from the server (49) and from the client (50); a client answers with an empty Certificate, no CertificateVerify and a right Finished (51); and, from the server and from the client in turn, a Certificate has two entries (52, 53), a context that is not empty (54, 55), entry extensions (56, 57) or another 12-byte prefix (58, 59), a CertificateVerify names the scheme `04 03` (60, 61) or has a signature field of 65 bytes (62, 63), and bytes follow Finished (64, 65); and a server sends no CertificateRequest (66). `quic-self <code>` runs one of them alone
- THEN in each case the end that checks is marked refused and sends nothing more, a refusing server has made no 1-RTT keys, and no application byte is read on either end

#### Scenario: Stream data before the handshake, in one process

- GIVEN `quic-self` and `Conn.earlyStream`, which puts a STREAM frame with FIN beside the CRYPTO frame of a flight
- WHEN a client's Initial flight, a server's Initial flight, a server's Handshake flight and a client's Handshake flight each carry one
- THEN the receiving end's `readApp` is empty, the end of the stream is not noted, and that packet counted as not opened (exit 68 otherwise); the same exchanges without the frame finish

#### Scenario: Stream data before the handshake, on a guest

- GIVEN a guest booted with a QUIC port, a key, an allow-list and `reflect.hook=alloc`, which stops it at its first run request
- WHEN `quic-client ... early` sends a first flight whose Initial packet also carries a STREAM frame with FIN holding a run request, and 3 seconds later the allowed client sends factorial
- THEN `early` exits 0, having sent its datagram, the guest is up and has printed no `reflect: allocation failure` 3 seconds later, and it prints that line and powers off at the second client's request (`check-quic.sh`)

#### Scenario: A QUIC word without an allow-list

- GIVEN the command line `reflect.ip=192.168.249.2 reflect.port=4444 reflect.quic_port=4445`, with no `reflect.allow`, and a key file
- WHEN the guest starts
- THEN serial shows `reflect: the network address is not valid` and no `reflect: ready`, and Cloud Hypervisor exits (`check-quic.sh`)

### Requirement: The host client proves its key and pins the guest's name
<!-- base: 754bebc58b9cac19e42a2408a7937aed1ba1a9c0 openspec/specs/unikernel-net/spec.md -->

The host client `unikernel/out-net/quic-client <ip> <port> <budget> <program-file> <key-file> <server-name> [loss|wrong|denied|early|spoof <local-ip>|initial|silent|noretry|stall|keep <file>|flood <local-ip> <seconds> <rate> <file>]` SHALL read its entity key from a 32-byte file and SHALL accept only a guest whose name is `<server-name>`. Its connection IDs and its X25519 secret SHALL come from the operating system's `getrandom`. It SHALL send no application data on a refused connection (`quic.zig` `onServerFlight`, `writeApp`). It SHALL answer one Retry (the requirement "A full first-flight pool answers with a Retry"). It SHALL write only the guest's reply frame to standard output and exit 0 when it gets one; it SHALL exit 3 when it refuses the guest, 6 when a flight of its own has been given up and 1.28 seconds have passed since its last send with no reply, 4 when nothing arrives within 60 seconds, and 2 for a wrong call, an unreadable program file, or a key file or name that is not well formed. With `wrong` it SHALL exit 0 only when it refuses the guest. With `denied` it SHALL exit 0 only when it accepted the guest and its flight was then given up with no reply, so a guest that never answered does not pass. With `early` it SHALL put its request in a STREAM frame in its Initial packet (`Conn.earlyStream`), send that first flight once, and exit 0 without waiting, or 2 when nothing was sent. With `spoof <local-ip>` it SHALL also bind a second socket to that address and play the second host of the requirement "A datagram that does not open changes nothing", and SHALL exit 5 when that socket receives anything other than a long-header packet addressed to its own other handshake, when the reply is not resent to the client while it is silent, or when the garbage was not sent. With `initial` it SHALL write the first datagram of a handshake to standard output and send nothing. It SHALL acknowledge the reply in a packet of its own before it exits, through its loss and reordering when `loss` is given; with `silent` it SHALL take the reply and leave without acknowledging it. With `noretry` it SHALL drop Retry packets, as a client of `e9a4c86` does. With `stall` it SHALL send no Certificate, CertificateVerify or Finished, and once its address is shown SHALL send a Handshake packet with an empty CRYPTO frame every 100 ms for 6 seconds (`Conn.poke`), then exit 0. With `keep <file>` it SHALL write every datagram it sends to that file, each after its length in two bytes. With `flood <local-ip> <seconds> <rate> <file>` it SHALL bind to `<local-ip>` and, for that many seconds, at that many datagrams a second (0 for as fast as it can), send the guest in turn a new first flight of its own (from a pool of 256 made with distinct IDs), one first flight again, and each datagram of the file; it SHALL print to standard error how many it sent and how many Retries and other datagrams came back, and exit 0.

#### Scenario: A wrong name is refused

- GIVEN a running guest with a QUIC port
- WHEN `quic-client ... wrong` connects expecting the name of another key
- THEN the client refuses the handshake, sends neither its key nor a program, and exits 0 (`check-quic.sh`; `quic-self` checks the same in one process)

### Requirement: Two guests run one program and record the crossing
<!-- base: 754bebc58b9cac19e42a2408a7937aed1ba1a9c0 openspec/specs/unikernel-net/spec.md -->

The command line MAY carry `reflect.wire_port=<port>` or `reflect.peer=<a.b.c.d>:<port>` as before, and with either MAY carry `reflect.spawn=far|near` and `reflect.take=old|new`, each at most once; either word without an end of the crossing SHALL be refused as other bad configuration is (`unikernel/net.zig` `parse`). Each guest SHALL begin a Lean guest with `reflect_cross_start` and hold it between calls; Zig SHALL NOT read a packet, a batch, an entry or a process. The guest with `reflect.wire_port` is the one given the program, and it holds its connections in the table of the requirement "A serving guest admits connections into a bounded table": a stream on the wire port that starts `RFL1` SHALL be judged as a run frame is (kind 0, status 0, a budget in range), its body and budget SHALL be handed to `reflect_cross_give`, and it SHALL be answered with a run reply frame with no body. Any other stream SHALL be a batch: the serving guest SHALL take batches from one entity only, the first that sent one, hand each to `reflect_cross_take`, call `reflect_cross_work` until Lean says nothing is possible (at most 64 calls), and answer with the bytes of `reflect_cross_batch`. The guest with `reflect.peer` SHALL open one QUIC connection per exchange from UDP port 9000, answering a Retry as the host client does, send `reflect_cross_batch`, hand the answer to `reflect_cross_take`, work, and open the next exchange no sooner than 20 ms after the last answer; an exchange with no answer in 8 seconds SHALL be abandoned and the batch sent again on a new connection. When the Lean guest reports closed, each guest SHALL print its record on serial, one `reflect: cross ` line for each line of `reflect_cross_record`, then `reflect: cross done`. Each guest has its entity key and `reflect.allow` as every QUIC guest does: the serving guest allows the other guest and the client that hands it the program, the calling guest allows the serving one. Before the record's lines a guest SHALL print `reflect: cross sig <public key> <signature>`, both hex: its Ed25519 signature, under its entity key, over the record's text as Lean gave it. The record's `me` SHALL be the text of the guest's own entity name and its `peer` the name of the entity its batches came from or went to (`Conn.peer_name` of the first such connection); a later connection from another allowed name SHALL carry no batch. A calling guest whose peer it does not allow SHALL print `reflect: the peer is not allowed`, and one whose handshake is given up `reflect: the peer gave no answer`, each once, and SHALL open the exchange again later. A guest whose Lean guest reports failure SHALL print its error line and power off.

#### Scenario: Two guests on one bridge

- GIVEN guest A booted with its key, `reflect.wire_port=4446 reflect.allow=<B's name>,<the client's name> reflect.spawn=far`, handed `examples/cross-race.hom` as bytes with budget 100000 by `quic-client`, and guest B booted with its key and `reflect.peer=<A>:4446 reflect.allow=<A's name>`
- WHEN B calls A
- THEN within 90 seconds both serial logs end with `reflect: cross done`, A's record has seven entries and B's six, and they are the entries two guests in one Lean process record (`kernel/CrossCheck.lean`)
