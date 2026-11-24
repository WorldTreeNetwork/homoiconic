# Tasks

- [ ] Design reviewed in a fresh context (Fable): two reads, both send-back, findings fixed (`review.md`). No reader returned accept; the third read was cut off by an API limit
- [x] `unikernel/entity.zig`: name, base58, identity, allow-list; `entity` host tool
- [x] `quic.zig`: Ed25519 raw public keys, CertificateRequest, client Certificate and CertificateVerify, the allow check on both ends, exact readers; random hello values; Finished compared in constant time; the constant key and certificate deleted
- [x] `quic.zig`: frames checked before a packet counts as opened (STREAM only in 1-RTT, CRYPTO only in Initial and Handshake); `readApp` and the end of stream only when accepted; a refused connection takes and sends nothing
- [x] `quic.zig`: `Conn.peer_name`, `Conn.gaveUp`; the test seams `Conn.signer`, `Conn.tamper`, `Conn.earlyStream`
- [x] `kernel.zig` `reflect_boot_take`; `net.zig` takes the key, parses `reflect.allow`, refuses QUIC without a key, prints the entity line, drops `reflect.port` on a guest with a QUIC word, lets a refused connection give way, prints the two peer lines
- [x] `quic-client`: key file and server name; `wrong`, `denied`, `early`, exit 6
- [x] `quic-self`: the name vector and base58 (40, 41), the refusals 42 to 66 and early stream data (68)
- [x] `check-quic.sh`: two keys two identities, same key same identity, wrong pin, client not allowed and the timed give-way, no key (none, 31 bytes, zeros), no allow-list, the ping to `reflect.port`, `early` on a guest with the hook
- [x] `check-wire.sh`: each guest pins the other, and both refusals
- [x] Each check shown to fail with its fix undone (`unikernel/evidence/entity-keys-controls.log`)
- [x] Final run on morphie from a `git archive` export: `build.sh`, `build-net.sh`, `check.sh`, `check-net.sh`, `check-quic.sh`, `check-wire.sh`; logs and manifests in `unikernel/evidence/`
- [x] `host/check.sh` passes locally
- [x] Mjolnir: `add-unikernel-entity-keys` opened, built and folded there (mjolnir `71d90c5`): vendored client from `e9a4c86`, spawn takes the owner's `entity_key` and an `allow` list, Mjolnir has a client key of its own; its acceptance passed on morphie against this image, 47 PASS. `mjolnir-6h01` closed; `mjolnir-0wm4` filed for the deploy that does not build the two Zig binaries
