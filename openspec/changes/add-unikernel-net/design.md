# Design

## Boundaries and build

The normal image still calls reflect_run once, renders text and powers off. A separately built server remains in a polling loop. The low-level layer owns PCI, MMIO mappings, DMA queues and Ethernet/IP/UDP bytes. A server main above musl initializes Surface.Host and calls only a new Lean byte export for program requests. Kernel outcomes are never reconstructed by Zig or Python.

Build-net produces `unikernel/out/reflect-net.elf`, from the pinned Lean 4.35.0 generated C and Zig 0.16.0/musl path. Object provenance and the no-op libuv audit cover the current Surface.Host imports, including kept state and channels. There is no Lean async IO or scheduler thread in the served export. Linux comparison calls that same export with identical program bytes and budget; it is not a replacement evaluator. Server startup fails explicitly on missing NIC, configuration, features or mapping capacity.

## Hardware contract

Modern virtio-net over PCI, using the common/notify/ISR/device vendor capabilities. Enumerate PCI configuration through x86 CF8/CFC, validate capability chains and BAR types/ranges, and enable memory/bus-master access. Set exactly VERSION_1 (bit 32) and MAC (bit 5), and no other feature bit. Both must be offered or startup fails. This excludes ACCESS_PLATFORM, CTRL_VQ, MQ, RING_RESET, checksum/GSO/merge/packed/event-index and every unlisted feature. Use split queues only. Use one RX and one TX queue, power-of-two sizes no larger than the device permits, with stable static DMA buffers in guest RAM. Modern network headers are 12 bytes; each posted RX buffer is at least 1526 bytes (12-byte header plus a 1514-byte Ethernet frame). A used length exceeding its posted buffer is dropped without copying and the descriptor is safely recycled or the device stopped; it is never an array bound. No checksum or segmentation offloads are requested.

Read the MAC through the device configuration generation protocol. Set ACKNOWLEDGE, DRIVER, FEATURES_OK (verify accepted), then DRIVER_OK only after queues are configured. Reset or unsupported negotiation is an observable startup failure. Poll completion instead of installing interrupt delivery. Suppress available-ring interrupts and use release/acquire barriers around descriptors, ring indices and completion reads. Validate used IDs, lengths, outstanding counts and wrapping 16-bit indices before reusing a buffer. Never hand an RX buffer back until its contents have been copied or consumed; never reuse TX storage before completion.

The boot image currently maps only the first 4 GiB. Do not assume PCI BARs are below it: map each advertised MMIO range before dereferencing it, from a bounded reserved page-table pool, without making MMIO available to either RAM allocator. Check address overflow, canonical virtual addresses, RAM overlap and range bounds; report failure if unsupported. MMIO accesses are volatile and uncached. Descriptor buffers and page tables remain in the mapped RAM region. A real Cloud Hypervisor boot must establish the actual BAR placement and page-table behavior.

Primary contracts: [VIRTIO 1.2](https://docs.oasis-open.org/virtio/virtio/v1.2/virtio-v1.2.html), sections 2 (split virtqueues), 4.1 (PCI), 5.1 (network device); Cloud Hypervisor [v54.0 PCI transport](https://github.com/cloud-hypervisor/cloud-hypervisor/blob/v54.0/virtio-devices/src/transport/pci_device.rs) and [network device](https://github.com/cloud-hypervisor/cloud-hypervisor/blob/v54.0/virtio-devices/src/net.rs). The cited transport exposes configuration through PCI BAR capabilities; the virtio spec, not a guessed register layout, controls accesses.

## Link and IP limits

Single static IPv4 address and UDP port, supplied as `reflect.ip=A.B.C.D reflect.port=N` through PVH cmdline. Reject malformed, repeated, missing and out-of-range fields; bound command-line reads. Initial tests and Mjolnir use a same-subnet TAP, no gateway. Answer ARP for the configured address. Only reply to a datagram addressed to this guest and this port, using its source MAC/IP/port, so the service needs no unbounded ARP cache.

Ethernet MTU 1500. Validate frame size, IPv4 version/header length (IHL=5; options are unsupported), total length, header checksum, UDP length and nonzero UDP checksums; a zero UDP checksum is allowed for IPv4. Drop fragments, unsupported protocols, inconsistent lengths and packets for other endpoints before invoking Lean. Generate valid IP and UDP checksums on replies. Padding outside IP total length is not application input. Maximum application datagram is 1200 bytes, leaving 1176 bytes after the service header. There is no IP or application fragmentation/reassembly. Longer programs or replies require a later transport; do not truncate them into valid-looking outcomes.

## Service framing, version 1

A 24-byte header, followed by zero or more payload bytes:

| Offset | Size | Meaning |
|---|---|---|
| 0 | 4 | ASCII `RFL1` |
| 4 | 1 | kind: 0 run, 1 reply, 2 ping, 3 pong |
| 5 | 1 | transport status: 0 success, 1 reserved, 2 reply too large, 3 invalid budget |
| 6 | 2 | reserved, must be zero |
| 8 | 8 | caller correlation number, unsigned big-endian |
| 16 | 8 | machine-step budget, unsigned big-endian, echoed by replies |

The server accepts only run (kind 0) and ping (kind 2), each with status zero. Kind 1 or 3, any unknown kind, any nonzero status, or a ping with nonzero budget or payload is dropped without reply or evaluation. Only an otherwise valid run with zero status and an out-of-range budget receives status 3. Run budget is 1..100000000; refuse a larger or zero budget before evaluation. Ping has budget zero and no payload; pong echoes its ID with no payload. An empty run payload reaches Lean as invalid program bytes. Unknown magic, unsupported kinds, oversized input, truncated headers and nonzero reserved bytes are dropped, with no evaluator invocation. A well-framed run with an invalid budget receives status 3 and empty payload. An encoded reply over 1176 bytes receives status 2 and empty payload. No reply contains a prefix of an oversized result. Transport status 1 is reserved; no response is required for a malformed frame.

One request is evaluated at a time. The client matches source endpoint, kind, status, ID and echoed budget, uses an OS deadline and reports timeout without claiming execution failed. It does not automatically retry. UDP loss, duplication and reordering remain possible; a repeated request may be evaluated again. Correlation IDs are not credentials and the UDP service provides no peer identity or confidentiality. Mjolnir initially exposes it only on its controlled guest network.

## Lean reply bytes

The proposed `reflect_reply_bytes(program, length, out, capacity, budget)` copies input and delegates to a pure `Surface.replyBytes`. It returns required output length and writes nothing when capacity is too small. It decodes Wire.readProgram, compiles, runs the existing bounded machine with arithmetic, and delegates encoding to `Wire.runReplyData` and `Wire.runReplyBytes` in `kernel/Wire/Reply.lean`, with strict inverse `Wire.readRunReply`. The data envelope is:

- `[0, value]`, where `value` is Wire.valueData of the resulting machine value (including closure code/environment).
- `[1]`: machine is still running when the step budget is exhausted.
- `[2]`: program-byte decoding failed.
- `[3, index]`: unbound outcome.
- `[4]`: wrong outcome.
- `[5]`: machine fault, an internal failure rather than a language outcome.
- `[6]`: machine value could not be represented by Wire.valueData, also internal failure.

The outcome envelope belongs to the wire-bytes capability, not to the UDP stack. `Wire.RunReply` represents the complete bounded-run response, including invalid bytes, budget exhaustion and internal errors, which are not semantic `Outcome` values. It differs deliberately from `Reflect.reifyOutcome`: that encoding is used inside the metacircular interpreter, whereas this envelope uses the existing machine-value wire form, including validated compiled closure code, and additional service diagnostics. No existing reify/unreify function or proof changes.

Tests independently decode these bytes with Wire.read, compare factorial data and budget/error replies, and round-trip a closure through Wire.readValue. The transport treats the reply as opaque; application tags are parsed only by Lean-aware tests/callers. Zig may inspect the returned length to decide whether it fits a datagram. There is no text-to-byte reconstruction.

The server uses a fixed 1176-byte reply buffer; the export's length return detects oversized output. It does not allocate in proportion to an untrusted claimed wire length. Lean's own reader/evaluator can allocate; the existing RAM and stack limits apply, and a hardware fault still stops the guest. A machine step is not a bound on the native cost of a primitive (existing q59.9), so the service promises step accounting, not wall-clock preemption.

## Fatal request failure

An allocator abort, fatal runtime panic or processor fault during a request is a guest failure, not a Wire.RunReply. Existing runtime stderr and the layer's abort/fault report must name its cause or cause class. The fatal path powers off through the existing ACPI shutdown device; Cloud Hypervisor exits status 0 for that power-off, so VMM process death (not a nonzero hypervisor code) is the observable failure. There is no successful reply, resumed polling, second readiness announcement or implicit reboot from that boot. The client expires its deadline and reports a transport timeout. Mjolnir must observe the VMM exit and withdraw readiness; any later explicitly requested restart is a new boot with no request replay.

The real-guest check uses a build-only allocation-failure hook armed only after readiness and triggered by a valid run request. Force a real Lean allocation failure/abort, require its serial diagnostic and hypervisor termination, then confirm no matching success frame and no pong after death. The harness still has an outer deadline to catch a wedged failure path. This hook is absent in production builds and introduces no new request kind. A resource-exhausting source fixture is useful extra coverage, not a wall-clock guarantee.

## Checks

- Native Zig tests on the Mac for header/packet parsing, checksums, malformed lengths, fragmentation rejection and correlation matching; no NIC emulation counted as a guest test.
- Lean tests for each binary response, known value, budget exhaustion, invalid bytes, closure byte form and capacity-retry behavior via native FFI.
- Clean KVM/CH54 network check: create a uniquely named isolated TAP/subnet, trap cleanup, boot one guest; readiness ping, factorial program bytes, forever with 5000 steps, bad byte program, then factorial again without reboot. Compare every response byte with the same Lean export in a Linux process, and factorial/budget responses against independent expected bytes. Include oversized reply, malformed packet and wrong ID/source behavior; the next valid request must succeed.
- Ring stress beyond 65536 completions proves wrap/reuse; malformed traffic must not invoke Lean or change later output. Record BAR ranges, queue features and DMA address checks. Missing NIC/config fails; readiness is not emitted early. Existing image checks remain green.
- Mjolnir integration is a following node: readiness via ping/pong, opaque UDP message round trip, cleanup, restart without snapshot/resume, regression of ordinary Linux spawn.

## Unverified hypotheses

- virtio-mmio: claim: the image can discover CH54's modern PCI NIC, map its BARs (including above 4 GiB), initialize split queues and exchange ARP/one UDP datagram without interrupts. confidence: medium. verification: no KVM host currently reachable; requires a real minimal guest/TAP exchange with bounded startup failure. synthesis path: docs/spikes/unikernel-net-device/finding.md, then unikernel network layer.

Do not treat native parser tests or a cross-compiled ELF as go for this hypothesis. Host access is an external prerequisite, not permission to mark the spike passed.

If the device spike contradicts CF8/CFC discovery, MMIO placement or attributes, negotiated features or queue behavior, amend this contract to the evidenced behavior and reopen Fresh advise after preparation. Obtain fresh acceptance before production implementation; do not quietly change the driver to an unreviewed architecture. A passing spike records the matching contract and proceeds.
