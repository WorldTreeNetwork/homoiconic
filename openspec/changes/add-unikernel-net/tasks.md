# Tasks

- [x] Prepare against folded image and current Lean imports; authority: Duke's unikernel/network/Mjolnir scope and UDP-first decision.
- [x] Fresh advise after preparation. Accepted by opus-arch-review in `reviews/2026-11-12-advise-2.md` against HEAD `d89806a` and the change-file sha256 values recorded there (unikernel-net `e2b4a75f…`, wire-bytes `c167d48f…`, zig-host `6d0f6706…`, design `8f3281ee…`, tasks before this check `c3b318e7…`).
  - [x] Owed (advise 2026-11-12 #1): inline the RFL1 header table, kind codes and status codes into `specs/unikernel-net/spec.md`; no reference to design.md.
  - [x] Owed (#2): name `reflect_reply_bytes` as an evaluating Lean export (zig-host delta or unikernel-net requirement), as add-interpreted-run does for `reflect_interp`.
  - [x] Owed (#3): home the outcome byte form in Wire (`Wire.outcomeData` + wire-bytes requirement) or justify a network-local form distinct from `reifyOutcome`; name the Lean definition tests decode against.
  - [x] Owed (#4): accepted request kinds are 0 and 2 only; every other kind/status/budget/payload combination is dropped except an out-of-range run budget (status 3); one malformed example each in the scenario.
  - [x] Owed (#5): feature allow-list (exactly VERSION_1 + MAC; startup fails if either is absent), RX buffers ≥ 1526 bytes, used length > posted length dropped.
  - [x] Owed (#6): requirement and scenario for a mid-request abort (OOM/panic/fault): serial cause, observable VMM exit, no re-readiness, client timeout.
  - [x] Owed (#7): a spike finding that contradicts the hardware contract amends the change and reopens fresh advise before implementation.
- [x] Spike modern virtio-net/MMIO mapping and a datagram exchange on CH54/KVM; record host/toolchain/BAR/feature evidence. Passed 2026-11-18 on morphie: `spike/serial.log`, `spike/exchange.log`. The hardware contract held. Implementation is still open.
- [x] Implement bounded PCI discovery, MMIO mappings, split queues and polling Ethernet/ARP/IPv4/UDP.
- [x] Add Lean-owned binary replies and native FFI capacity/closure/outcome checks.
- [x] Add server build, endpoint configuration, framing and client with deadline/correlation checks.
- [x] Run parser, Lean, ring-wrap, malformed-packet and persistent real-guest tests; rerun existing image suite.
- [ ] Publish verified endpoint contract for Mjolnir; fold living spec and archive this change.

External prerequisite: morphie answered on 2026-11-18 (Linux x86_64, KVM, Cloud Hypervisor 54.0). The Framework laptop still times out over SSH and is not the build host. The virtio-net spike passed and matched the reviewed contract. On 2026-11-19 `unikernel/check-net.sh` and `unikernel/check.sh` passed on morphie: factorial bytes, a budget reply with the guest still up, status 2, malformed drops, a 65537-completion ring wrap, an allocation abort, and the one-program image. QUIC is tracked separately as homoiconic-q59.30. Fold and the Mjolnir endpoint note are still open.

Spike routing rule: any finding that contradicts the reviewed hardware contract amends this change and reopens Fresh advise after preparation; a new accepting review is required before production implementation. A passing spike records the matching contract and proceeds.
