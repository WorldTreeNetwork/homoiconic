---
spike_id: unikernel-net-device
hypothesis_id: virtio-mmio
source_synthesis: openspec/changes/add-unikernel-net/design.md
run_at: 2026-11-13T01:51:33Z
verdict: inconclusive
validation_scope: host-access-preflight-only
version-pinned: Cloud Hypervisor 54.0, Lean 4.35.0, Zig 0.16.0
---

# Device spike: blocked before hardware execution

## Claim to test

The image can discover Cloud Hypervisor 54.0's modern PCI virtio-net device, map its BARs (including above the existing first-4-GiB boot map), initialize split queues and exchange ARP and a UDP datagram without interrupts.

## Minimum distinguishing test

On Linux x86_64 with usable KVM and CH54, boot an isolated minimal guest with an owned TAP. Record PCI BAR ranges, mapped register addresses, accepted feature bits, queue setup and DMA buffer bounds. Receive an ARP request and exchange one UDP payload with the host. Require bounded startup failure and cleanup of only the test-owned guest/TAP. An ELF build or native packet-parser test cannot establish this claim.

## Evidence

[access.log](access.log) records two read-only SSH access attempts, each exiting 255 with Operation timed out. Neither reached Linux, so no device test ran. [repro-command.sh](repro-command.sh) is a read-only prerequisite check to run after connectivity returns; it is not the hardware spike itself.

## Verdict: inconclusive

This is an unavailable test environment, not evidence against the architecture. The device hypothesis remains unverified, its confidence is unchanged, and no network production implementation is admitted. The accepted contract is in `openspec/changes/add-unikernel-net/reviews/2026-11-12-advise-2.md`.

## What blocked validation

Neither configured Linux/KVM host is reachable over SSH. The Framework environment-link request remains pending. The Mac cannot supply the required Linux/KVM acceptance environment.

## Next action

Use the approved Framework link when connected, or restore access to Framework/morphie. Pass the read-only preflight and perform the actual minimal guest/TAP exchange above before reporting go. A finding that contradicts the hardware contract requires amendment and fresh architecture advise, as the accepted change requires. Do not close `homoiconic-q59.15` or `homoiconic-q59.17` from this preflight record.
