# unikernel-net

## ADDED Requirements

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

The stack SHALL serve only its own IPv4 UDP endpoint, answer ARP for that address and validate Ethernet/IP/UDP bounds and checksums before dispatch. It SHALL reject IP fragments, options, unsupported protocols and inconsistent lengths. IPv4 UDP zero checksum MAY be accepted; nonzero checksums SHALL be verified. Replies SHALL have valid checksums. It SHALL bound application datagrams to 1200 bytes and SHALL NOT fragment or truncate application output into a successful reply.

#### Scenario: Bad traffic followed by good traffic

- GIVEN truncated, fragmented, misaddressed, oversized and checksum-invalid input
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

The Lean export `reflect_reply_bytes` SHALL copy program bytes, decode them with Wire.readProgram, compile and execute the existing Reflect machine under arithmetic, and encode through `Wire.runReplyBytes` in `kernel/Wire/Reply.lean`. The payload SHALL be the bounded-run reply form specified by wire-bytes, independent of UDP framing. The server SHALL invoke the export once per received run request; an oversized answer SHALL NOT be evaluated again to retry it with more capacity. The export SHALL return the required byte length and write nothing unless capacity suffices. Non-Lean code SHALL NOT parse program syntax or reconstruct an outcome from rendered text.

#### Scenario: Known replies and a closure

- GIVEN factorial, exhaustion, invalid bytes and a program returning a closure
- WHEN the export runs and its output is independently decoded
- THEN every response has the specified shape, factorial's data equals the known integer, and the closure's code/environment round-trips through the existing Wire value format

#### Scenario: Capacity contract

- GIVEN an insufficient output buffer surrounded by sentinels
- WHEN the export runs then retries with the reported capacity
- THEN the insufficient buffer is untouched, sentinels survive, and the retry gives the complete same reply bytes

### Requirement: The client distinguishes transport from execution

The client SHALL match source endpoint, reply kind, correlation ID, status and echoed budget. It SHALL use a bounded OS deadline, reject oversized/truncated responses and report timeout or transport failure separately from Lean's reply bytes. It SHALL NOT retry automatically or claim exactly-once delivery, authentication, confidentiality or a native wall-clock bound from a machine-step budget.

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
