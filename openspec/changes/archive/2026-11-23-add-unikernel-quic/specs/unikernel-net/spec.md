# unikernel-net delta: authenticated QUIC

## MODIFIED Requirements

### Requirement: Malformed packets do not reach evaluation
<!-- base: d67b3b1e59191b981a7c5ef4ee7b95f799b5fe95 openspec/specs/unikernel-net/spec.md -->

The stack SHALL serve only its own IPv4 address, answer ARP for that address and validate Ethernet/IP bounds and the IPv4 header checksum before dispatch. It SHALL reject IP fragments, options, unsupported protocols and inconsistent IP or UDP lengths. On the UDP service port (`reflect.port`) an IPv4 UDP zero checksum MAY be accepted and nonzero checksums SHALL be verified. Replies SHALL have valid checksums. The UDP service SHALL bound application datagrams to 1200 bytes and SHALL NOT fragment or truncate application output into a successful reply. A datagram for a QUIC port (`reflect.quic_port`, `reflect.wire_port`, and port 9000 on a guest given `reflect.peer`) SHALL be passed to QUIC after the IP and UDP length checks; its UDP checksum is not verified, and QUIC packet protection SHALL drop a packet that fails authentication before its frames are read (`unikernel/net.zig` `handle`, `unikernel/quic.zig` `open`; `homoiconic-q59.53`).

#### Scenario: Bad traffic followed by good traffic

- GIVEN truncated, fragmented, misaddressed, oversized and checksum-invalid input to the UDP service port
- WHEN those packets precede a valid program request
- THEN malformed input invokes no evaluator, and the valid request still receives its complete correct reply

### Requirement: The client distinguishes transport from execution
<!-- base: 135d7058deac5148c8170f68210a73e9b45617ca openspec/specs/unikernel-net/spec.md -->

The UDP client in `unikernel/check-net.sh` SHALL match source endpoint, reply kind, correlation ID, status and echoed budget. It SHALL use a bounded OS deadline, reject oversized/truncated responses and report timeout or transport failure separately from Lean's reply bytes. It SHALL NOT retry automatically or claim exactly-once delivery, authentication, confidentiality or a native wall-clock bound from a machine-step budget. What the QUIC client checks is the requirement "The client pins the guest certificate".

#### Scenario: Wrong reply and loss

- GIVEN replies from the wrong endpoint, with the wrong ID, or no reply
- WHEN the client waits
- THEN unmatched replies are ignored and a deadline expires unsuccessfully; no bytes are presented as a successful matching outcome

## ADDED Requirements

### Requirement: An optional port serves one authenticated QUIC stream

The command line MAY carry `reflect.quic_port=<port>`, at most once, with a port in 1..65535; a repeated or malformed word SHALL be refused as other bad configuration is (`reflect: the network address is not valid`). Without the word, and without the remote-channel words, the guest SHALL serve UDP exactly as before and SHALL NOT start the clock. With it, after `reflect: ready`, the guest SHALL start the paravirtual clock, open a QUIC server connection and print `reflect: quic <port>` on serial (`unikernel/net.zig` `net_serve`, `parse`). The QUIC layer (`unikernel/quic.zig`) SHALL speak QUIC version 1 with TLS 1.3, the cipher suite TLS_AES_128_GCM_SHA256, X25519 key exchange and a P-256 ECDSA certificate, with 8-byte connection IDs and random values from `RDRAND`. It SHALL carry one bidirectional stream. The client's stream, ended by FIN, SHALL be one `RFL1` frame of at most 1200 bytes, judged by the frame rules of the UDP service: a ping answered by a pong, a well-framed run with an out-of-range budget answered with status 3 and not evaluated, a run whose reply exceeds 1176 bytes answered with status 2, and anything else answered with nothing. A valid run SHALL call `reflect_reply_bytes` once, and the guest SHALL write the answering frame on the stream with FIN (`net.zig` `quicPump`, `answerBytes`). Zig SHALL NOT read the program or the outcome. The guest SHALL serve one QUIC connection at a time: after it has answered, the next long-header packet SHALL start a new server connection, so a budget reply leaves the guest serving. The build-only allocation hook SHALL apply to a QUIC run as it does to a UDP run.

#### Scenario: Factorial, a budget reply, and the guest still up

- GIVEN a guest booted with `reflect.ip=192.168.249.2 reflect.port=4444 reflect.quic_port=4445` on a TAP
- WHEN `unikernel/out/quic-client` sends factorial with budget 100000000, then `examples/forever.hom` with budget 5000, then factorial again over new handshakes
- THEN the first two reply frames have kind 1 and status 0, and each payload equals, byte for byte, what `unikernel/out/reply run` gives for the same program and budget in a Linux process (`unikernel/check-quic.sh`)

### Requirement: The guest reads time from the KVM paravirtual clock

When a QUIC port is configured the guest SHALL check that CPUID leaf 0x40000000 carries the KVM signature in EBX and ECX and that leaf 0x40000001 sets feature bit 3 (the second paravirtual clock), and SHALL register a 64-byte-aligned clock record with MSR 0x4b564d01. A guest without them SHALL print `reflect: no monotonic clock` and power off, after `reflect: ready` and before `reflect: quic`. The time QUIC is given SHALL be read from that record, retried while its version is odd or changes during the read (`net.zig` `startClock`, `mono`). The one-program image's `clock_gettime` stand-in and the UDP-only guest SHALL be unchanged. The read is not claimed monotonic over long runs: it scales the TSC delta with a wrapping 64-bit multiply, which wraps once the shifted delta since the last clock update passes about 2^32 (`homoiconic-q59.48`).

#### Scenario: The clock is there on Cloud Hypervisor 54.0

- GIVEN Cloud Hypervisor 54.0 on KVM on morphie
- WHEN the guest starts with `reflect.quic_port`
- THEN serial shows `reflect: quic <port>` and not `reflect: no monotonic clock`

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
