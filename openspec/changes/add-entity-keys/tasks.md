# Tasks

- [ ] Design reviewed in a fresh context (Fable), verdict recorded in `review.md`
- [ ] `unikernel/entity.zig`: name, base58, identity, allow-list; `entity` host tool
- [ ] `quic.zig`: Ed25519 raw public keys, CertificateRequest, client Certificate and CertificateVerify, the allow check on both ends, exact readers; random hello values; Finished compared in constant time; the constant key and certificate deleted
- [ ] `quic.zig`: frames checked before a packet counts as opened (STREAM only in 1-RTT, CRYPTO only in Initial and Handshake); `readApp` and the end of stream only when accepted; a refused connection takes and sends nothing
- [ ] `quic.zig`: `Conn.peer_name`, `Conn.gaveUp`; the test seams `Conn.signer`, `Conn.tamper`, `Conn.earlyStream`
- [ ] `kernel.zig` `reflect_boot_take`; `net.zig` takes the key, parses `reflect.allow`, refuses QUIC without a key, prints the entity line, drops `reflect.port` on a guest with a QUIC word, lets a refused connection give way, prints the two peer lines
- [ ] `quic-client`: key file and server name; `wrong`, `denied`, `early`, exit 6
- [ ] `quic-self`: the name vector and base58 (40, 41) and the refusals 42 to 67
- [ ] `check-quic.sh`: two keys two identities, same key same identity, wrong pin, client not allowed and the timed give-way, no key (none, 31 bytes, zeros), no allow-list, the ping to `reflect.port`, `early` on a guest with the hook
- [ ] `check-wire.sh`: each guest pins the other, and both refusals
- [ ] Each check shown to fail with its fix undone (`unikernel/evidence/entity-keys-controls.log`)
- [ ] Final run on morphie from a `git archive` export: `build.sh`, `build-net.sh`, `check.sh`, `check-net.sh`, `check-quic.sh`, `check-wire.sh`; logs and manifests in `unikernel/evidence/`
- [ ] `host/check.sh` passes locally
- [ ] Mjolnir: change opened, vendored client updated, spawn gives each guest a key and names, acceptance rerun on morphie; or a precise bead
