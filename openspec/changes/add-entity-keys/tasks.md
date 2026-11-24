# Tasks

- [ ] Design reviewed in a fresh context (Fable), verdict recorded in `review.md`
- [ ] `unikernel/entity.zig`: name, base58, identity, allow-list; `entity` host tool
- [ ] `quic.zig`: Ed25519 raw public keys, CertificateRequest, client Certificate and CertificateVerify, the allow check on both ends; the constant key and certificate deleted
- [ ] `kernel.zig` `reflect_boot_take`; `net.zig` takes the key, parses `reflect.allow`, refuses QUIC without a key, prints the entity line
- [ ] `quic-client`: key file and server name; `wrong`, `denied`, exit 6
- [ ] `quic-self`: wrong pin, client not allowed, forged CertificateVerify, name vector, base58
- [ ] `check-quic.sh`: two keys two identities, same key same identity, wrong pin, client not allowed, no key
- [ ] `check-wire.sh`: each guest pins the other, and both refusals
- [ ] Each check shown to fail with its fix undone (`unikernel/evidence/entity-keys-controls.log`)
- [ ] Final run on morphie from a `git archive` export: `build.sh`, `build-net.sh`, `check.sh`, `check-net.sh`, `check-quic.sh`, `check-wire.sh`; logs and manifests in `unikernel/evidence/`
- [ ] `host/check.sh` passes locally
- [ ] Mjolnir: change opened, vendored client updated, spawn gives each guest a key and names, acceptance rerun on morphie; or a precise bead
