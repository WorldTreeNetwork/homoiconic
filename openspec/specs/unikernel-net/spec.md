# unikernel-net

What is built: a second image, `unikernel/out/reflect-net.elf`, built by `unikernel/build-net.sh`, that serves program bytes over UDP on a Cloud Hypervisor 54.0 guest with no operating system (`openspec/changes/archive/2026-11-22-add-unikernel-net/`). The Zig layer (`unikernel/net.zig`, `unikernel/netmain.zig`) carries a polling modern virtio-net PCI driver, Ethernet, ARP, IPv4 and UDP, reads `reflect.ip` and `reflect.port` from the PVH command line, and passes each run request's program bytes and step budget to the Lean export `reflect_reply_bytes`, which answers with the bounded-run reply form of `openspec/specs/wire-bytes/spec.md`. `unikernel/out/reply` is the Linux comparison process that calls the same export; `unikernel/check-net.sh` boots a real guest on a TAP, sends requests through its client, and compares each reply with that process. With `reflect.quic_port` the same guest also serves one `RFL1` exchange per connection over QUIC v1 (`unikernel/quic.zig`), with its clock read from the KVM paravirtual clock; the host client `unikernel/out/quic-client` pins the guest's compiled certificate, and `unikernel/check-quic.sh` checks it against the same Linux process (`openspec/changes/archive/2026-11-23-add-unikernel-quic/`). With `reflect.wire_port` on one guest and `reflect.peer` on another, the two run one program between them: the first is handed the program as bytes over QUIC, start requests and sends cross between them as packets Lean makes and reads, and each prints its own record of what it did; `unikernel/check-wire.sh` boots both, replays the records outside the guests and refuses tampered ones (`openspec/changes/archive/2026-11-24-add-recorded-crossing/`, Lean side in `openspec/specs/crossing/spec.md`). Nothing in this capability is proved; it is trusted as the host is (`docs/PROOFS.md`). The one-program image is `openspec/specs/unikernel-image/spec.md`.

## Purpose

State what the network image serves over UDP and QUIC, the frame it reads and writes, how the client authenticates the guest, how two guests carry a crossing and print their records, what it refuses before evaluation, what Lean owns, what the client may and may not claim, and what its check must show. This spec does not cover what a crossing means or how a record is checked (`openspec/specs/crossing/spec.md`), or Mjolnir.

## Requirements

### Requirement: A separate image serves program bytes over UDP

The system SHALL build a server ELF for Cloud Hypervisor 54.0, one vCPU and 512 MiB, with a modern virtio-net PCI interface and a persistent, sequential UDP service. It SHALL read its static IPv4 address and port from the PVH command line and SHALL refuse malformed, repeated or missing configuration. The one-program image and its serial checks SHALL remain supported. No guest Linux, root filesystem, asynchronous Lean event loop or second evaluator SHALL be introduced.

#### Scenario: Persistent service

- GIVEN a configured server guest and a same-subnet Linux client
- WHEN the client sends factorial program bytes, a program exhausting 5000 steps, and factorial again
- THEN all three replies arrive from the same running guest, match the Linux Lean export byte for byte, and the guest has not rebooted

#### Scenario: Startup failures

- GIVEN absent NIC, rejected required features or invalid endpoint configuration
- WHEN the server starts
- THEN serial reports the cause, no readiness is claimed, and initialization terminates or fails within a bounded check deadline

### Requirement: Device buffers and MMIO are bounded and ordered

The driver SHALL discover PCI BAR capabilities and map advertised MMIO before accessing it, including ranges above the boot map's first 4 GiB. Mapping overflow, RAM overlap, unsupported addresses and exhausted table capacity SHALL fail explicitly. It SHALL set exactly VERSION_1 (bit 32) and MAC (bit 5), and no other negotiated feature bit, failing startup if either is absent. It SHALL use modern split RX/TX queues, post RX buffers of at least 1526 bytes, drop a used length greater than the posted length without copying, preserve buffer ownership until completion and use memory barriers for descriptor publication/completion. Used IDs, lengths and outstanding counts SHALL be checked before access or reuse. MMIO and DMA buffers SHALL be excluded from RAM allocator overlap.

#### Scenario: Actual guest device

- GIVEN a real Cloud Hypervisor 54.0 network device
- WHEN the device spike boots and exchanges ARP and UDP traffic
- THEN recorded BAR/feature/queue evidence shows mapped capability accesses and correct DMA buffer ownership; compiling alone does not pass

#### Scenario: Ring reuse

- GIVEN more than 65536 packet completions
- WHEN ring indices wrap
- THEN subsequent packets still round-trip without stale data or buffer reuse before completion

### Requirement: Malformed packets do not reach evaluation

The stack SHALL serve only its own IPv4 address, answer ARP for that address and validate Ethernet/IP bounds and the IPv4 header checksum before dispatch. It SHALL reject IP fragments, options, unsupported protocols and inconsistent IP or UDP lengths. On every port it serves, an IPv4 UDP zero checksum MAY be accepted and nonzero checksums SHALL be verified before the datagram is dispatched. Replies SHALL have valid checksums. The UDP service SHALL bound application datagrams to 1200 bytes and SHALL NOT fragment or truncate application output into a successful reply. A datagram for a QUIC port (`reflect.quic_port`, `reflect.wire_port`, and port 9000 on a guest given `reflect.peer`) SHALL be passed to QUIC after the IP and UDP length checks and the same checksum check, and QUIC packet protection SHALL drop a packet that fails authentication before its frames are read (`unikernel/net.zig` `handle`, `unikernel/quic.zig` `open`). What such a datagram may change is the requirement "A datagram that does not open changes nothing".

#### Scenario: Bad traffic followed by good traffic

- GIVEN truncated, fragmented, misaddressed, oversized and checksum-invalid input to the UDP service port
- WHEN those packets precede a valid program request
- THEN malformed input invokes no evaluator, and the valid request still receives its complete correct reply

#### Scenario: A bad checksum on the QUIC port

- GIVEN a running guest with a QUIC port and the first datagram of a real handshake, written by `quic-client ... initial`
- WHEN it is sent to the QUIC port with a nonzero UDP checksum that is wrong, and then again with the right one
- THEN the guest sends nothing for the first and answers the second, in a datagram of at least 1200 bytes (`unikernel/check-quic.sh`)

### Requirement: Framing supplies correlation and a bounded step budget

Version-1 application frames SHALL have this 24-byte header, followed by payload bytes; no native struct padding is transmitted:

| Offset | Size | Meaning |
|---|---|---|
| 0 | 4 | ASCII magic `RFL1` |
| 4 | 1 | kind: 0 run, 1 reply, 2 ping, 3 pong |
| 5 | 1 | transport status: 0 success, 1 reserved (never emitted), 2 reply too large, 3 invalid budget |
| 6 | 2 | reserved, both zero |
| 8 | 8 | unsigned big-endian correlation ID |
| 16 | 8 | unsigned big-endian step budget |

The server SHALL accept only kinds 0 and 2 with status zero. It SHALL drop kinds 1 and 3, unknown kinds, nonzero status, and ping with nonzero budget or payload, without reply or evaluation. The only invalid combination that receives an error reply SHALL be an otherwise well-framed run with status zero and an out-of-range budget (status 3). Ping/pong SHALL carry no payload and budget zero. A run SHALL carry zero status and a budget in 1..100000000, with its remaining bytes passed unchanged as the program. Well-framed invalid budgets SHALL receive transport status 3 without evaluating. A reply exceeding the 1176-byte payload capacity SHALL receive status 2 and no payload. Unknown magic, kinds, malformed headers, reserved bytes or oversize requests SHALL be dropped without evaluation. Replies SHALL echo ID and budget.

#### Scenario: Readiness

- GIVEN device and Lean initialization complete
- WHEN a correctly framed ping arrives
- THEN a matching pong is returned without running a program

#### Scenario: Capacity and budget failures

- GIVEN a valid request for a response larger than 1176 bytes, and separately a zero/excessive run budget
- WHEN the service handles each
- THEN it returns the corresponding empty transport-error frame, never a truncated successful outcome; the next valid request works

#### Scenario: Invalid request combinations

- GIVEN kind 1, kind 3, kind 255, a run with status 2, a ping with status 3, a ping with budget 1, and a ping with one payload byte
- WHEN each reaches the server as an otherwise valid UDP packet
- THEN each is dropped without response or evaluation, while a subsequent valid ping succeeds

### Requirement: Lean owns binary replies

The Lean export `reflect_reply_bytes` SHALL copy program bytes, decode them with Wire.readProgram, compile and execute the existing Reflect machine under arithmetic for at most the budget in steps, and encode through `Wire.runReplyBytes` in `kernel/Wire/Reply.lean`. The budget SHALL be charged as `reflect_run` charges it (`runPriced`): one for every machine step, and an operation its cost under `arith` before it runs, so a budget bounds the work inside an operation (`homoiconic-q59.52`). A run the budget stops SHALL be the budget reply (`81 01`). The replies for factorial at 100000000 and for `examples/forever.hom` at 5000 SHALL be byte-identical to those the image at `793b583` gave. The payload SHALL be the bounded-run reply form specified by wire-bytes, independent of UDP framing. The server SHALL invoke the export once per received run request; an oversized answer SHALL NOT be evaluated again to retry it with more capacity. The export SHALL return the required byte length and write nothing unless capacity suffices. Non-Lean code SHALL NOT parse program syntax or reconstruct an outcome from rendered text.

#### Scenario: Known replies and a closure

- GIVEN factorial, exhaustion, invalid bytes and a program returning a closure
- WHEN the export runs and its output is independently decoded
- THEN every response has the specified shape, factorial's data equals the known integer, and the closure's code/environment round-trips through the existing Wire value format

#### Scenario: A large operation is bounded on the network path

- GIVEN `mul` applied to two numbers of 40 nines, as program bytes
- WHEN `Surface.replyBytes` runs it with the budget 200 and with 200000
- THEN the first reply is the budget reply `81 01` and the second is the product (`kernel/WireReplyCheck.lean`)

#### Scenario: Capacity contract

- GIVEN an insufficient output buffer surrounded by sentinels
- WHEN the export runs then retries with the reported capacity
- THEN the insufficient buffer is untouched, sentinels survive, and the retry gives the complete same reply bytes

### Requirement: The client distinguishes transport from execution

The UDP client in `unikernel/check-net.sh` SHALL match source endpoint, reply kind, correlation ID, status and echoed budget. It SHALL use a bounded OS deadline, reject oversized/truncated responses and report timeout or transport failure separately from Lean's reply bytes. It SHALL NOT retry automatically or claim exactly-once delivery, authentication, confidentiality or a native wall-clock bound from a machine-step budget. What the QUIC client checks is the requirement "The client pins the guest certificate".

#### Scenario: Wrong reply and loss

- GIVEN replies from the wrong endpoint, with the wrong ID, or no reply
- WHEN the client waits
- THEN unmatched replies are ignored and a deadline expires unsuccessfully; no bytes are presented as a successful matching outcome

### Requirement: Acceptance uses a real persistent guest and leaves no TAP

The network check SHALL create an isolated, uniquely named TAP/subnet, record toolchain and hypervisor versions, and clean up the guest and TAP on success, failure or interruption. It SHALL compare persistent guest replies against the same compiled Lean export in a Linux process and independently expected factorial and budget bytes, exercise malformed traffic, capacity failures and ring wrap, and rerun the one-program image check. Native parser tests or a cross-compiled ELF SHALL NOT replace KVM acceptance.

#### Scenario: Check cleanup

- GIVEN a check that succeeds, fails before readiness or is interrupted
- WHEN it ends
- THEN its owned guest process and TAP are removed, and preexisting devices and guests are untouched

### Requirement: A fatal request ends that guest boot observably

A Lean allocation abort, fatal runtime panic or processor fault during a request SHALL name its cause or cause class on serial, send no successful reply, and power off through the image's ACPI shutdown path. Cloud Hypervisor SHALL terminate (status 0 is the expected power-off status); its process death SHALL be the observable guest failure. The service SHALL NOT resume polling, re-announce readiness or reboot from that boot. The client SHALL report a transport timeout rather than an execution outcome. Mjolnir integration SHALL withdraw readiness on the VMM exit; a later explicit restart is a fresh boot with no replay.

#### Scenario: Failure after readiness

- GIVEN a real server guest that has answered ping, with a build-only failure hook armed to force a Lean allocation abort during a valid run request
- WHEN that request is delivered
- THEN serial names the allocation failure/abort, Cloud Hypervisor terminates, no matching successful response arrives, and subsequent ping times out; no new readiness is announced

### Requirement: Contradictory spike results reopen the contract

A device-spike result contradicting the reviewed discovery, MMIO, feature or queue contract SHALL cause an amendment and fresh architecture advise before implementation. A compiling image or native parser test SHALL NOT be used as hardware evidence.

#### Scenario: Different hardware behavior

- GIVEN a spike whose observed BAR placement or register-access requirements differ from the reviewed design
- WHEN the finding is recorded
- THEN the contract is amended, Fresh advise after preparation is reopened, and production implementation waits for a new accepting review

### Requirement: An optional port serves one authenticated QUIC stream

The command line MAY carry `reflect.quic_port=<port>`, at most once, with a port in 1..65535; a repeated or malformed word, or the word together with `reflect.wire_port` or `reflect.peer`, SHALL be refused as other bad configuration is (`reflect: the network address is not valid`). Without the word, and without the words of a crossing, the guest SHALL serve UDP exactly as before and SHALL NOT start the clock. With it, after `reflect: ready`, the guest SHALL start the paravirtual clock, open a QUIC server connection and print `reflect: quic <port>` on serial (`unikernel/net.zig` `net_serve`, `parse`). The QUIC layer (`unikernel/quic.zig`) SHALL speak QUIC version 1 with TLS 1.3, the cipher suite TLS_AES_128_GCM_SHA256, X25519 key exchange and a P-256 ECDSA certificate, with 8-byte connection IDs and random values from `RDRAND`. It SHALL carry one bidirectional stream. The client's stream, ended by FIN, SHALL be one `RFL1` frame of at most 1200 bytes, judged by the frame rules of the UDP service: a ping answered by a pong, a well-framed run with an out-of-range budget answered with status 3 and not evaluated, a run whose reply exceeds 1176 bytes answered with status 2, and anything else answered with nothing. A valid run SHALL call `reflect_reply_bytes` once, and the guest SHALL write the answering frame on the stream with FIN (`net.zig` `quicPump`, `answerBytes`). Zig SHALL NOT read the program or the outcome. The guest SHALL serve one QUIC connection at a time. After it has answered, the next datagram that opens as a new Initial SHALL start a new server connection, so a budget reply leaves the guest serving; when a connection gives way is the requirement "A datagram that does not open changes nothing". The build-only allocation hook SHALL apply to a QUIC run as it does to a UDP run.

#### Scenario: Factorial, a budget reply, and the guest still up

- GIVEN a guest booted with `reflect.ip=192.168.249.2 reflect.port=4444 reflect.quic_port=4445` on a TAP
- WHEN `unikernel/out/quic-client` sends factorial with budget 100000000, then `examples/forever.hom` with budget 5000, then factorial again over new handshakes
- THEN the first two reply frames have kind 1 and status 0, and each payload equals, byte for byte, what `unikernel/out/reply run` gives for the same program and budget in a Linux process (`unikernel/check-quic.sh`)

#### Scenario: Two QUIC services on one command line

- GIVEN the command line `reflect.ip=192.168.249.2 reflect.port=4444 reflect.quic_port=4445` with `reflect.wire_port=4446` added, and separately with `reflect.peer=192.168.249.3:4446` added
- WHEN the guest starts
- THEN serial shows `reflect: the network address is not valid` and no `reflect: ready`, and Cloud Hypervisor exits (`check-quic.sh`)

### Requirement: A datagram that does not open changes nothing

A datagram to a QUIC port SHALL change the guest's connection, and where the guest sends, only when one of its packets opens: its AEAD tag checks under keys of the connection it is given to (`quic.zig` `recv`, `open`). A server connection SHALL install the Initial keys named by a first Initial only if that packet opens, and either end SHALL take the peer's connection ID only from an Initial that opened (`quic.zig` `longPacket`). The guest SHALL send a server connection's packets to the address its first opened Initial came from and SHALL NOT move that address afterwards for any packet; there is no connection migration (`net.zig` `quicDatagram`). Once it has that address, a server connection SHALL be given datagrams only from that IPv4 address and UDP port; a datagram from anywhere else SHALL NOT reach it, whatever it would open, and can only start a connection under the policy below.

A server connection SHALL give way to a new one only under this policy. The datagram SHALL be at least 1200 bytes and begin with a QUIC version 1 Initial with 8-byte connection IDs whose destination ID is not the present connection's (`quic.zig` `newInitial`); the present connection SHALL have answered its stream, or have opened no packet for 2 seconds by the paravirtual clock (`net.zig` `q_idle`); and the Initial SHALL open under the Initial keys of its own destination ID on a connection built aside, which replaces the present one only then. A first Initial in a datagram shorter than 1200 bytes SHALL start nothing. Every other long-header packet that does not open under the present connection's keys, of any type and from any address, SHALL be dropped with no effect. The guest's own connection to a peer (`reflect.peer`) SHALL never be replaced.

What this does not give SHALL be stated as it is. Initial keys are derived from the connection ID in the packet, so opening as an Initial shows a well-formed QUIC client and nothing about who sent it; the guest does not authenticate clients (`homoiconic-q59.49`). A host that keeps sending well-formed Initials can therefore take the one connection each time it is free and hold it for 2 seconds a time, and one that sends a well-formed Initial after the guest has answered ends that connection's resending of the reply. What a host that cannot open packets can no longer do is move, stall or reset an exchange in progress. Packets are not checked for replay.

#### Scenario: A second address during an exchange

- GIVEN a running guest with a QUIC port and a client whose handshake has been accepted
- WHEN `quic-client ... spoof <local-ip>` sends, from a second address, a short-header datagram, a full-size Initial, a small Initial and a Handshake packet of random bytes and then the well-formed first datagram of another handshake, sends nothing for half a second, and then sends its program
- THEN the second address receives nothing from the guest, and the client's reply equals the Linux process's (`check-quic.sh`)

#### Scenario: Garbage long headers after the reply

- GIVEN the same exchange, with the guest's first copy of the reply discarded by the client as a lost datagram would be
- WHEN the same four garbage datagrams are sent from the client's address and then from the second address before the guest resends, and the client then sends nothing for half a second
- THEN the guest resends the reply to the client within that time, the second address still receives nothing, and a later handshake is served (`check-quic.sh`)

#### Scenario: An abandoned handshake

- GIVEN a guest whose last client refused the handshake and sent no more
- WHEN another client connects at once
- THEN its Initials are dropped until the unfinished connection has been idle for 2 seconds, and then it is served (`check-quic.sh`, the step after the wrong pin)

#### Scenario: Garbage in one process

- GIVEN `unikernel/out/quic-self`
- WHEN a full-size Initial, a Handshake packet and a short-header datagram of random bytes are given to both ends before every step of a clean exchange and of a lossy one
- THEN no garbage datagram opens, the client's ID for the server does not change, both exchanges finish, and a real first flight cut to 1199 bytes starts nothing on a server

### Requirement: The guest reads time from the KVM paravirtual clock

When a QUIC port is configured the guest SHALL check that CPUID leaf 0x40000000 carries the KVM signature in EBX and ECX and that leaf 0x40000001 sets feature bit 3 (the second paravirtual clock), and SHALL register a 64-byte-aligned clock record with MSR 0x4b564d01. A guest without them SHALL print `reflect: no monotonic clock` and power off, after `reflect: ready` and before `reflect: quic`. The time QUIC is given SHALL be read from that record, retried while its version is odd or changes during the read (`net.zig` `startClock`, `mono`). The conversion SHALL be the KVM one: the TSC delta since the record's `tsc_timestamp`, shifted left by `tsc_shift` or right when it is negative, times `tsc_to_system_mul` as a 128-bit product, shifted right by 32, added to `system_time` (`unikernel/pvclock.zig` `scale`, `nanos`). The time returned SHALL NOT go backwards: a read below the last value returned gives the last value. The one-program image's `clock_gettime` stand-in and the UDP-only guest SHALL be unchanged. The conversion is checked on the build host, not in a guest: no check keeps a guest up while its clock is compared with another.

#### Scenario: The clock is there on Cloud Hypervisor 54.0

- GIVEN Cloud Hypervisor 54.0 on KVM on morphie
- WHEN the guest starts with `reflect.quic_port`
- THEN serial shows `reflect: quic <port>` and not `reflect: no monotonic clock`

#### Scenario: Time runs forward past 2^32 ticks

- GIVEN `zig test unikernel/pvclock.zig`, which `unikernel/build-net.sh` runs
- WHEN the delta is stepped from zero to beyond 2^44 shifted ticks for a 3 GHz counter (shift -1), a 1.5 GHz counter (shift 0) and a shift of 1
- THEN every value is at least the one before and equals the product computed in two 64-bit halves, the wrapping 64-bit product is seen to go backwards over the same steps, and 3e9 ticks a second stay within one part in a million of a second for a day

### Requirement: The client pins the guest certificate

The host client `unikernel/out/quic-client <ip> <port> <budget> <program-file> [loss|wrong|spoof <local-ip>|initial|silent]` SHALL hold the SHA-256 of the DER certificate compiled into `unikernel/quic.zig`. Its connection IDs and its X25519 secret SHALL come from the operating system's `getrandom`. Before it accepts the handshake it SHALL check that the certificate the guest sends hashes to that pin, verify the CertificateVerify signature over the transcript with the certificate's P-256 key, and check the guest's Finished. Any failure SHALL mark the connection refused, and the client SHALL send no application data on a refused connection (`quic.zig` `onServerFlight`, `writeApp`). The client SHALL write only the guest's reply frame to standard output and exit 0 when it gets one; it SHALL exit 3 when the connection is refused, 4 when nothing arrives within 60 seconds, and 2 for a wrong call or an unreadable file. With `wrong` it SHALL flip the pin and exit 0 only when the connection is refused. With `spoof <local-ip>` it SHALL also bind a second socket to that address and play the second host of the requirement "A datagram that does not open changes nothing", and SHALL exit 5 when that socket receives anything, when the reply is not resent to the client while it is silent, or when the garbage was not sent. With `initial` it SHALL write the first datagram of a handshake to standard output and send nothing. It SHALL acknowledge the reply in a packet of its own before it exits, through its loss and reordering when `loss` is given; with `silent` it SHALL take the reply and leave without acknowledging it. The guest SHALL accept the client's stream only after the client's Finished checks. What the pin authenticates SHALL be stated as it is: the certificate's private key is a constant in `unikernel/quic.zig`, so every guest built from the tree has the same identity and anyone with the source can present it, and the guest does not authenticate the client (`homoiconic-q59.49`).

#### Scenario: A wrong key is refused

- GIVEN a running guest with a QUIC port
- WHEN `quic-client ... wrong` connects with one bit of the pin changed
- THEN the client refuses the handshake, sends no program, and exits 0 (`check-quic.sh`; `quic-self` checks the same in one process)

### Requirement: QUIC survives loss and reordering

Each packet number space SHALL keep its unacknowledged flight and resend it, waiting 20 ms shifted left by the number of tries so far, at most by 6 (1.28 s), until the flight is finished or has been sent 10 times. After the tenth send, 6.36 s after the first, the flight SHALL be given up and not sent again (`quic.zig` `due`, `seal`, `max_tries`). Received CRYPTO and STREAM data SHALL be placed by offset, so packets that arrive out of order are used once the gap is filled (`holePut`).

An acknowledgement SHALL finish only the flight of the packet number space it arrived in, and only when one of its ranges holds a packet number that flight went out as, from its first send to its latest (`quic.zig` `ack`, `acked`; RFC 9002 section 3). No other packet of a space is sent while its flight is on, so every number in that span is a copy of the flight. The same number in another space is another packet. The flights that no acknowledgement in their own space reaches SHALL finish as RFC 9001 has them finish: a server's Initial flight when the server opens a Handshake packet, after which it opens no Initial (section 4.9.1); a client's Initial flight when the client sends a Handshake packet; a client's Handshake flight when its 1-RTT packet is acknowledged (section 4.1.2); and a server's Handshake flight when the client's Finished checks.

A packet with a CRYPTO or STREAM frame that opens SHALL leave an acknowledgement owed in its space. Every packet an end sends carries its space's ACK frame and pays what is owed. When a space owes an acknowledgement and has no flight on, the end SHALL send a packet in that space with only an ACK frame, once, which asks for nothing back and is not resent (`quic.zig` `ack_due`, `ackOnly`, `send`). A client that has its Finished to send owes nothing more in the Initial space. So the host client acknowledges the reply before it exits, and the guest that sent the offer acknowledges the answer (`quic-client.zig`, `net.zig` `wirePump`); the guest stops resending a reply when that acknowledgement arrives. A long header's Length SHALL be written in its shortest form, and every variable-length integer read SHALL be stepped over by its own encoded width, so a longer form than needed also reads.

What this does not give SHALL be stated as it is. An acknowledgement is sent once; when it is lost the guest resends the reply to a client that has gone, up to the 10 sends over 6.36 s, unless another connection takes its place first. There is no congestion control or connection close, and stream data is limited to 8192 bytes each way. A connection is not closed for being idle or for a flight given up: it stays, sending nothing, until another takes its place, which an unfinished one allows after 2 idle seconds. A client whose flight is given up is not told; `quic-client` exits 4 at its 60 seconds.

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

Until a server connection has opened a Handshake packet, the bytes it has sent SHALL NOT exceed three times the bytes of the datagrams that opened under its keys (RFC 9000 section 8.1; `quic.zig` `seal`, `amplification`, `rx_bytes`, `tx_bytes`, `validated`). Both counts are UDP payload bytes. A packet that would pass the limit SHALL NOT be sent and SHALL NOT count as a try. It SHALL go as soon as a datagram that opens raises the limit, so a client that is where it says and loses the guest's answers is served when its resent first flight arrives. A Handshake packet that opens validates the address and lifts the limit: its keys come from the ServerHello, which was sent to that address and nowhere else. Because a server connection is given datagrams only from the address it answers (the requirement "A datagram that does not open changes nothing"), the bytes counted came from that address as far as a source address says. A datagram that does not open is not counted, which is less than the RFC allows.

A server SHALL expand every datagram that carries its Initial flight to at least 1200 bytes (RFC 9000 section 14.1), with PADDING in the Initial packet sized by the packets that follow it in the datagram, and SHALL count the whole datagram against the limit before it sends the Initial packet (`quic.zig` `send`, `size`, `seal`). A client's first flight of 1200 bytes therefore draws at most three datagrams of 1200 bytes. A packet with only an ACK frame is not padded.

What this does not give SHALL be stated as it is. The limit bounds the factor, not the number: each well-formed first flight with a forged source still takes the one connection for 2 seconds and draws up to three times its bytes to that address. The guest sends no Retry and has no address token. The padding is checked against the guest's own client and `quic-self`, not against another QUIC implementation.

#### Scenario: A first flight from a forged address

- GIVEN a running guest with a QUIC port that has answered its last client, and the 1200-byte first datagram of a real handshake written by `quic-client ... initial`
- WHEN it is sent from 192.168.249.77, where nobody is, and the same bytes are sent four more times from another address over the next three seconds
- THEN in 8 seconds the guest sends the forged address at least two datagrams, each of at least 1200 bytes, and at most 3600 bytes, sends nothing to any other address, and serves factorial to a real client afterwards (`check-quic.sh`)

#### Scenario: A first flight nobody follows, in one process

- GIVEN `quic-self` and a server given one first flight
- WHEN the server is asked to send every 10 ms for a minute of its clock, and then the client's resent first flight arrives
- THEN the server has sent more than once, each datagram at least 1200 bytes (exit 29 otherwise), and at most three times the flight's bytes (exit 24 otherwise), sends again at once when the second flight arrives, and the exchange finishes

### Requirement: The QUIC check uses a real guest

`unikernel/check-quic.sh` SHALL require KVM and Cloud Hypervisor v54.0, build with `build-net.sh` (which runs `quic-self`), create its own TAP, boot the network image with `reflect.quic_port`, wait up to 90 seconds for `reflect: quic <port>` on serial, and run factorial, the 5000-step budget, factorial on a new handshake, the wrong key, loss straight after it, the second address (`spoof`, from a second address it gives its TAP), factorial again, the first flight with a bad and then a good UDP checksum, whose answer it requires to be at least 1200 bytes, factorial once more, factorial while it counts on the TAP the datagrams that carry the reply, factorial for a `silent` client, a watch on the TAP for the resends of that unacknowledged reply to stop, a first flight from a forged address, and factorial after it, comparing reply payloads with `unikernel/out/reply`. Before that boot it SHALL boot the two refused command lines. It SHALL require that the serving guest printed nothing but its two start lines, print one `ok` line a step, and stop its guest and remove its TAP on exit, pass or fail.

#### Scenario: The check passes

- GIVEN morphie with Cloud Hypervisor 54.0
- WHEN `sh unikernel/check-quic.sh` runs
- THEN it prints fourteen `ok` lines and `quic guest ok`, and exits 0 (`unikernel/evidence/check-quic.log`)

### Requirement: Two guests run one program and record the crossing

The command line MAY carry `reflect.wire_port=<port>` or `reflect.peer=<a.b.c.d>:<port>` as before, and with either MAY carry `reflect.spawn=far|near` and `reflect.take=old|new`, each at most once; either word without an end of the crossing SHALL be refused as other bad configuration is (`unikernel/net.zig` `parse`). Each guest SHALL begin a Lean guest with `reflect_cross_start` and hold it between calls; Zig SHALL NOT read a packet, a batch, an entry or a process. The guest with `reflect.wire_port` is the one given the program: a stream on the wire port that starts `RFL1` SHALL be judged as a run frame is (kind 0, status 0, a budget in range), its body and budget SHALL be handed to `reflect_cross_give`, and it SHALL be answered with a run reply frame with no body. Any other stream SHALL be a batch: the serving guest SHALL take batches from one address only, the first that sent one, hand each to `reflect_cross_take`, call `reflect_cross_work` until Lean says nothing is possible (at most 64 calls), and answer with the bytes of `reflect_cross_batch`. The guest with `reflect.peer` SHALL open one QUIC connection per exchange from UDP port 9000, send `reflect_cross_batch`, hand the answer to `reflect_cross_take`, work, and open the next exchange no sooner than 20 ms after the last answer; an exchange with no answer in 8 seconds SHALL be abandoned and the batch sent again on a new connection. When the Lean guest reports closed, each guest SHALL print its record on serial, one `reflect: cross ` line for each line of `reflect_cross_record`, then `reflect: cross done`. The names in the record are each guest's address and port until entity keys land (`homoiconic-q59.66`); nothing signs a record. A guest whose Lean guest reports failure SHALL print its error line and power off.

#### Scenario: Two guests on one bridge

- GIVEN guest A booted with `reflect.wire_port=4446 reflect.spawn=far`, handed `examples/cross-race.hom` as bytes with budget 100000 by `quic-client`, and guest B booted with `reflect.peer=<A>:4446`
- WHEN B calls A
- THEN within 90 seconds both serial logs end with `reflect: cross done`, A's record has seven entries and B's six, and they are the entries two guests in one Lean process record (`kernel/CrossCheck.lean`)

### Requirement: The wire check replays the guests' records

`unikernel/check-wire.sh` SHALL require KVM and Cloud Hypervisor v54.0, build with `build-net.sh`, run `kernel/CrossingContract.lean` and refuse an axiom outside `propext`, `Classical.choice` and `Quot.sound`, run `kernel/CrossCheck.lean` and require 48 `ok` lines and no `FAIL`, and then, for each run, boot the serving guest, hand it the program with `quic-client`, boot the calling guest, wait for both to close, read both records off the serial logs, and run `unikernel/out-net/cross-check check` on the program's bytes and the two records. It SHALL require `accepted` and the expected process lines for `examples/cross-reply.hom`, `examples/cross-name.hom`, and `examples/cross-race.hom` under `reflect.take=old` and `reflect.take=new`; for the last two it SHALL require one program, two different records, `[1, 2]` and `[2, 1]` reported by the guest, and the two schedules. From the records of the `old` run it SHALL make tampered records and require each refused with its reason: an entry moved, dropped from the middle and repeated (the link), the last entry dropped (the head), and, with the chain made again by `cross-check reseal`, a taking repeated, a taking dropped and an acknowledgement dropped (the merge), a local event repeated (the replay), and the takings in the other order (the comparison). It SHALL remove the TAPs and the bridge on exit. That each refusal is made by the check it is credited to is shown by `kernel/cross-controls.py`, which undoes one check at a time in a copy of the kernel and requires the test to fail (`unikernel/evidence/cross-controls.log`).

#### Scenario: The check passes

- GIVEN morphie with Cloud Hypervisor 54.0
- WHEN `sh unikernel/check-wire.sh` runs
- THEN it prints `wire guests ok` and exits 0 (`unikernel/evidence/check-wire.log`)
