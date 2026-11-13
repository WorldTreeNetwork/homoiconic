# add-unikernel-net

> **ACTIVE BUILD**

**Rigor:** architecture. Bead: `homoiconic-q59.15`.

## Why

The image runs a program fixed at build time and powers off. To let Mjolnir deliver executable bytes, the guest needs a network interface and a persistent request service whose answers still come from Lean.

## What

- Add a separate server image, with a polling modern virtio-net PCI driver, Ethernet, ARP, IPv4 and UDP. Keep the existing one-program image and its checks.
- A bounded UDP request carries a correlation number, step budget and program wire bytes. Lean decodes, runs and encodes a binary reply. Zig handles packet and transport bytes only.
- Provide a client, a Linux comparison path and a real Cloud Hypervisor 54.0/TAP check that sends multiple programs to one running guest.
- Read a static guest IPv4 address and UDP port from the PVH command line. Mjolnir can use the same endpoint for readiness and delivery.

## Preparation and authority

Upstream: `add-unikernel-image`, folded and closed (`518d1e8`); `wire-bytes`, `zig-host` and `channels` living specs. Current `Surface.Host` imports `Surface.Keep` and `Surface.Chan`; rebuild and re-audit that exact closure, rather than reuse the earlier image's objects.

Duke authorized completing the unikernel/network/Mjolnir scope, keeping `homoiconic-q59` open, and chose UDP first with QUIC separate (`homoiconic-q59.30`). This activates the dependency-ready UDP node. It does not activate QUIC or unrelated epic children. The cross-repository Mjolnir node follows only after this endpoint contract is verified. Outcome: revised from provisional TCP/QUIC notes to the explicit UDP decision.

Linux hardware validation is currently unavailable: morphie SSH reports Network is unreachable, Framework SSH times out. A Framework environment-link request is pending. The virtio/MMIO spike remains a prerequisite to implementation admission; this proposal is not evidence that it works.

## Impact

- Capabilities: ADDED `unikernel-net`; ADDED bounded-run reply form in `wire-bytes`; MODIFIED/ADDED export contract in `zig-host`. Existing `unikernel-image` one-shot behavior stays supported.
- New Lean byte export, with the same pointer/length/capacity ownership rules as the existing exports.
- ADR: amend ARCHITECTURE.md at fold. No new evaluator, semantics rule or Rust component.

## User journey & surfaces

Build the server with `sh unikernel/build-net.sh`. Start it with Cloud Hypervisor 54.0, one CPU, 512 MiB, a TAP and `--cmdline 'reflect.ip=192.168.249.2 reflect.port=4444'`. The serial port reports the endpoint after the device and Lean initialize. The client accepts a program's wire bytes, destination, budget and timeout, prints the raw reply bytes and exits nonzero on transport failure. A ping/pong exchange establishes service readiness without evaluating a program. An absent device or invalid configuration reports a startup error, never readiness.

## Out of scope

- QUIC, TLS, peer authentication, reliable delivery: `homoiconic-q59.30`.
- Remote channel names, closure exchange and schedule replay: `homoiconic-q59.16`.
- Mjolnir lifecycle integration: `homoiconic-q59.17`, after this contract passes.
- DHCP, IPv6, routing, IP fragments, NIC offloads, interrupts, concurrent evaluations.

## Review reconciliation

The first review sent this contract back with seven findings. The revised spec now carries its own header table and exact request-validity rules, homes replies in Wire.Reply, adds the zig-host export delta, pins the two-bit feature allow-list and RX capacity, specifies fatal-request power-off and client timeout, and routes contradictory spike evidence back through amendment and fresh advise. No hardware spike or network implementation has been claimed.
