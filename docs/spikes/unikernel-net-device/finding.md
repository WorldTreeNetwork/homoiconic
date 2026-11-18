---
spike_id: unikernel-net-device
hypothesis_id: virtio-mmio
source_synthesis: openspec/changes/add-unikernel-net/design.md
run_at: 2026-11-18T19:20:00Z
verdict: go
validation_scope: one-arp-and-one-udp-datagram
version-pinned: Cloud Hypervisor 54.0, Zig 0.16.0
---

# Device spike: the hardware contract held

## Claim tested

A minimal guest can discover Cloud Hypervisor 54.0's modern PCI virtio-net device, map its BAR above 4 GiB, accept only VERSION_1 and MAC, set up split queues, and exchange one ARP reply and one UDP datagram with the KVM host. No interrupts. This is not the Lean image and not factorial-over-the-wire.

## Host

morphie, `Linux archbox 7.2.6-arch2-1 x86_64`, `/dev/kvm` writable by the login user. `cloud-hypervisor v54.0` at `~/ch54/cloud-hypervisor`. Zig `0.16.0` at `~/zig-0.16.0/zig`. Tap `ukspike0`, host `10.99.0.1/24`, guest `10.99.0.2`, UDP port 9000, payload `spike-udp`.

## Evidence

PCI via CF8/CFC: `00:01.0` vendor `1af4` device `1041`.

One memory BAR: address `0x3fffff800000`, length `0x80000`. That is above 4 GiB and outside the 512 MiB guest RAM. The guest installed an uncached 2 MiB page for it. Common, notify, and device config came from virtio PCI capabilities on that BAR. Notify multiplier `4`.

Offered feature bits: low word `0x20630028` (3 MTU, 5 MAC, 16 STATUS, 17 CTRL_VQ, 21 GUEST_ANNOUNCE, 22 MQ, and bit 29), high word `0x00000001` (bit 32 VERSION_1). Bit 33 ACCESS_PLATFORM was not offered. The driver wrote only MAC and VERSION_1. FEATURES_OK stayed set. MAC read back `02:00:00:00:00:02`.

Three queues exist. The guest enabled queue 0 (RX) and queue 1 (TX) at size 8; the device maximum is `0x100`. RX buffers are 2048 bytes with a 12-byte modern header. No interrupt, no packed ring, no extra feature bit.

The host sent one ARP request and one UDP datagram. The guest's serial log says `arp: replied`, `udp: echoed`, and `spike: ok`. The host log says the ARP reply MAC was `020000000002` and the UDP echo was the same 9 bytes. Cloud Hypervisor exited 0.

Logs: `openspec/changes/add-unikernel-net/spike/serial.log` and `exchange.log`. Reproducer: `docs/spikes/unikernel-net-device/run.sh` with `guest/boot.S` and `guest/spike.zig`.

## Verdict: go

The reviewed contract matches this boot: CF8/CFC discovery, a BAR above 4 GiB that had to be mapped, split queues, polling, and exactly VERSION_1 plus MAC. No amendment and no fresh advise. Production implementation is still not started.

## What this does not show

No Lean reply, no server, no Mjolnir guest, no QUIC, and no factorial program on the wire. The earlier 2026-11-13 note in this file was an SSH preflight only; morphie is reachable now.
