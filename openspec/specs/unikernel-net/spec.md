# unikernel-net

What is built: a second image, `unikernel/out/reflect-net.elf`, built by `unikernel/build-net.sh`, that serves program bytes over UDP on a Cloud Hypervisor 54.0 guest with no operating system (`openspec/changes/archive/2026-11-22-add-unikernel-net/`). The Zig layer (`unikernel/net.zig`, `unikernel/netmain.zig`) carries a polling modern virtio-net PCI driver, Ethernet, ARP, IPv4 and UDP, reads `reflect.ip` and `reflect.port` from the PVH command line, and passes each run request's program bytes and step budget to the Lean export `reflect_reply_bytes`, which answers with the bounded-run reply form of `openspec/specs/wire-bytes/spec.md`. `unikernel/out/reply` is the Linux comparison process that calls the same export; `unikernel/check-net.sh` boots a real guest on a TAP, sends requests through its client, and compares each reply with that process. With `reflect.quic_port` the same guest also serves one `RFL1` exchange per connection over QUIC v1 (`unikernel/quic.zig`), with its clock read from the KVM paravirtual clock; the host client `unikernel/out/quic-client` pins the guest's compiled certificate, and `unikernel/check-quic.sh` checks it against the same Linux process (`openspec/changes/archive/2026-11-23-add-unikernel-quic/`). With `reflect.wire_port` on one guest and `reflect.peer` on another, the second sends the first the offer of the remote channel over the same QUIC and checks the answer against its own Lean; `unikernel/check-wire.sh` boots both (`openspec/changes/archive/2026-11-23-add-network-channels/`, Lean side in `openspec/specs/channels/spec.md`). Nothing in this capability is proved; it is trusted as the host is (`docs/PROOFS.md`). The one-program image is `openspec/specs/unikernel-image/spec.md`.

## Purpose

State what the network image serves over UDP and QUIC, the frame it reads and writes, how the client authenticates the guest, how two guests carry the remote channel, what it refuses before evaluation, what Lean owns, what the client may and may not claim, and what its check must show. This spec does not cover what the remote channel's messages mean (`openspec/specs/channels/spec.md`) or Mjolnir.

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

The stack SHALL serve only its own IPv4 address, answer ARP for that address and validate Ethernet/IP bounds and the IPv4 header checksum before dispatch. It SHALL reject IP fragments, options, unsupported protocols and inconsistent IP or UDP lengths. On the UDP service port (`reflect.port`) an IPv4 UDP zero checksum MAY be accepted and nonzero checksums SHALL be verified. Replies SHALL have valid checksums. The UDP service SHALL bound application datagrams to 1200 bytes and SHALL NOT fragment or truncate application output into a successful reply. A datagram for a QUIC port (`reflect.quic_port`, `reflect.wire_port`, and port 9000 on a guest given `reflect.peer`) SHALL be passed to QUIC after the IP and UDP length checks; its UDP checksum is not verified, and QUIC packet protection SHALL drop a packet that fails authentication before its frames are read (`unikernel/net.zig` `handle`, `unikernel/quic.zig` `open`; `homoiconic-q59.53`).

#### Scenario: Bad traffic followed by good traffic

- GIVEN truncated, fragmented, misaddressed, oversized and checksum-invalid input to the UDP service port
- WHEN those packets precede a valid program request
- THEN malformed input invokes no evaluator, and the valid request still receives its complete correct reply

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

The command line MAY carry `reflect.quic_port=<port>`, at most once, with a port in 1..65535; a repeated or malformed word SHALL be refused as other bad configuration is (`reflect: the network address is not valid`). Without the word, and without the remote-channel words, the guest SHALL serve UDP exactly as before and SHALL NOT start the clock. With it, after `reflect: ready`, the guest SHALL start the paravirtual clock, open a QUIC server connection and print `reflect: quic <port>` on serial (`unikernel/net.zig` `net_serve`, `parse`). The QUIC layer (`unikernel/quic.zig`) SHALL speak QUIC version 1 with TLS 1.3, the cipher suite TLS_AES_128_GCM_SHA256, X25519 key exchange and a P-256 ECDSA certificate, with 8-byte connection IDs and random values from `RDRAND`. It SHALL carry one bidirectional stream. The client's stream, ended by FIN, SHALL be one `RFL1` frame of at most 1200 bytes, judged by the frame rules of the UDP service: a ping answered by a pong, a well-framed run with an out-of-range budget answered with status 3 and not evaluated, a run whose reply exceeds 1176 bytes answered with status 2, and anything else answered with nothing. A valid run SHALL call `reflect_reply_bytes` once, and the guest SHALL write the answering frame on the stream with FIN (`net.zig` `quicPump`, `answerBytes`). Zig SHALL NOT read the program or the outcome. The guest SHALL serve one QUIC connection at a time: after it has answered, the next long-header packet SHALL start a new server connection, so a budget reply leaves the guest serving. The build-only allocation hook SHALL apply to a QUIC run as it does to a UDP run.

#### Scenario: Factorial, a budget reply, and the guest still up

- GIVEN a guest booted with `reflect.ip=192.168.249.2 reflect.port=4444 reflect.quic_port=4445` on a TAP
- WHEN `unikernel/out/quic-client` sends factorial with budget 100000000, then `examples/forever.hom` with budget 5000, then factorial again over new handshakes
- THEN the first two reply frames have kind 1 and status 0, and each payload equals, byte for byte, what `unikernel/out/reply run` gives for the same program and budget in a Linux process (`unikernel/check-quic.sh`)

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

The host client `unikernel/out/quic-client <ip> <port> <budget> <program-file> [loss|wrong]` SHALL hold the SHA-256 of the DER certificate compiled into `unikernel/quic.zig`. Before it accepts the handshake it SHALL check that the certificate the guest sends hashes to that pin, verify the CertificateVerify signature over the transcript with the certificate's P-256 key, and check the guest's Finished. Any failure SHALL mark the connection refused, and the client SHALL send no application data on a refused connection (`quic.zig` `onServerFlight`, `writeApp`). The client SHALL write only the guest's reply frame to standard output and exit 0 when it gets one; it SHALL exit 3 when the connection is refused, 4 when nothing arrives within 60 seconds, and 2 for a wrong call or an unreadable file. With `wrong` it SHALL flip the pin and exit 0 only when the connection is refused. The guest SHALL accept the client's stream only after the client's Finished checks. What the pin authenticates SHALL be stated as it is: the certificate's private key is a constant in `unikernel/quic.zig`, so every guest built from the tree has the same identity and anyone with the source can present it, and the guest does not authenticate the client (`homoiconic-q59.49`).

#### Scenario: A wrong key is refused

- GIVEN a running guest with a QUIC port
- WHEN `quic-client ... wrong` connects with one bit of the pin changed
- THEN the client refuses the handshake, sends no program, and exits 0 (`check-quic.sh`; `quic-self` checks the same in one process)

### Requirement: QUIC survives loss and reordering

Each packet number space SHALL keep its unacknowledged flight and resend it, waiting 20 ms shifted left by the number of tries so far, at most by 4, until an acknowledgement for that packet arrives. Received CRYPTO and STREAM data SHALL be placed by offset, so packets that arrive out of order are used once the gap is filled (`quic.zig` `due`, `seal`, `holePut`). There is no congestion control, idle timeout or connection close, and stream data is limited to 8192 bytes each way.

#### Scenario: Loss and reordering against the guest

- GIVEN a running guest with a QUIC port
- WHEN `quic-client ... loss` drops every fifth datagram it sends and holds one back to send after the next
- THEN factorial still comes back, byte for byte the Linux process's reply (`check-quic.sh`)

#### Scenario: Loss in one process

- GIVEN `unikernel/out/quic-self`, which `unikernel/build-net.sh` runs
- WHEN it checks the RFC 9001 initial keys, a clean exchange, an exchange that drops every fifth datagram and swaps pairs in both directions, and a wrong pin
- THEN it prints `quic self ok` and the build continues

### Requirement: The QUIC check uses a real guest

`unikernel/check-quic.sh` SHALL require KVM and Cloud Hypervisor v54.0, build with `build-net.sh` (which runs `quic-self`), create its own TAP, boot the network image with `reflect.quic_port`, wait up to 90 seconds for `reflect: quic <port>` on serial, and run factorial, the 5000-step budget, factorial on a new handshake, the wrong key and loss, comparing reply payloads with `unikernel/out/reply`. It SHALL remove its TAP on exit. It stops the guest when every step passes; when a step fails the guest is left to its 400-second timeout.

#### Scenario: The check passes

- GIVEN morphie with Cloud Hypervisor 54.0
- WHEN `sh unikernel/check-quic.sh` runs
- THEN it prints `quic guest ok` and exits 0

### Requirement: Two guests carry a remote channel over QUIC

The command line MAY carry `reflect.wire_port=<port>` or `reflect.peer=<a.b.c.d>:<port>`, each at most once and not both; a repeated, malformed or combined word SHALL be refused as other bad configuration is (`unikernel/net.zig` `parse`). A guest with either SHALL start the paravirtual clock as a QUIC guest does, or power off with `reflect: no monotonic clock`. A guest with `reflect.wire_port` SHALL print `reflect: wire <port>`, serve QUIC on that port with the compiled certificate, and answer the first stream it receives, once per connection, with the bytes of the Lean export `reflect_remote_take` on what it received; bytes from Lean that are empty or longer than 1200 SHALL send nothing. A guest with `reflect.peer` SHALL print `reflect: peer <ip>:<port>`, find the peer's MAC by ARP, connect from UDP port 9000 as a QUIC client pinned to the compiled certificate, and once the handshake is accepted send the bytes of `reflect_remote_offer`. When the peer's stream ends it SHALL compare what came back with `reflect_remote_take` of its own offer, computed in its own Lean, and print `reflect: remote ok` and `reflect: log ` followed by the text of `reflect_remote_log` when they are equal, or `reflect: remote differs` when they are not (`net.zig` `wirePump`). Zig SHALL pass these bytes, compare them only for equality, and SHALL NOT decode them. The offer is the one program built into Lean (`Surface.Remote.program`, the text of `examples/remote.hom`); a peer guest sends nothing else. `reflect.quic_port` given together with either word is not refused today, and the two share one connection (`homoiconic-q59.50`).

#### Scenario: Two guests on one bridge

- GIVEN guest B booted with `reflect.ip=192.168.249.3 reflect.port=4444 reflect.wire_port=4446` and guest A with `reflect.ip=192.168.249.2 reflect.port=4444 reflect.peer=192.168.249.3:4446`, each on its own TAP on one bridge
- WHEN A connects to B
- THEN B's serial shows `reflect: wire 4446`, and within 90 seconds A's serial shows `reflect: remote ok` and a `reflect: log ` line (`unikernel/check-wire.sh`)

### Requirement: The wire check uses two real guests

`unikernel/check-wire.sh` SHALL require KVM and Cloud Hypervisor v54.0, build with `build-net.sh`, run `kernel/RemoteCheck.lean` and require `ok   a remote closure replays to 42` with no `FAIL` line, run `unikernel/out/remote-check` (which links the same Lean objects as the guests and exits 0 only when `reflect_remote_same` gives 1), and then boot the two guests of the scenario above on two TAPs on its own bridge. It SHALL remove the TAPs and the bridge on exit. It stops the guests when every step passes; when a step fails they are left to their 180-second timeout.

#### Scenario: The check passes

- GIVEN morphie with Cloud Hypervisor 54.0
- WHEN `sh unikernel/check-wire.sh` runs
- THEN it prints `wire guests ok` and exits 0
