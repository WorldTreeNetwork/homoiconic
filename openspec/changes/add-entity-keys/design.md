# Design: a key per entity

Bead `homoiconic-q59.49`. Decision by Duke, 2026-11-24: a key per entity. An entity is the agent a guest runs for. It is not the build and not one boot: the same entity started again is the same identity.

## 1. An entity's public name (read this first if you build on it)

`homoiconic-q59.51` names each side of the remote channel by this.

- **Key.** An Ed25519 key pair (RFC 8032). The private key is the 32-byte seed. The public key is 32 bytes.
- **Name, bytes.** 32 bytes: `Blake3(P ‖ public key)`, where `P` is these 19 bytes:

  ```
  a2 63 61 6c 67 67 65 64 32 35 35 31 39 63 6b 65 79 58 20
  ```

  `P ‖ public key` is the dCBOR of the map `{"alg": "ed25519", "key": h'<32 bytes>'}`. This is the fingerprint of identikey-protocol (`docs/standards/identikey-auth-challenge-v1.md` §5, `crates/identikey-auth/src/key.rs` `ClassicalPublicKey::fingerprint`). An entity here has the name identikey gives the same key.
- **Name, text.** Base58 of the 32 bytes, as `identikey-protocol/docs/standards/encoding-conventions.md` has it: the alphabet `123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz`, no prefix, no checksum, each leading zero byte written as `1`. A name is 32 to 44 characters; the reader takes only text that decodes to exactly 32 bytes and that the writer would have written.
- **Vector.** Seed `11` × 32 (identikey's fixture seed) has public key `d04ab232742bb4ab3a1368bd4615e4e6d0224ab71a016baf8520a332c9778737` and the name `6mUFfKo4KPLqjeAVqthhCZB82jgWjbo3RPJAAWdTynq1`. That text was printed by identikey's own `ClassicalPublicKey::fingerprint` (a scratch program against `crates/identikey-auth`, 2026-11-24), and `quic-self` requires it.
- **In the code.** `unikernel/entity.zig`: `Name = [32]u8`, `nameOf(public_key)`, `text(name)`, `parse(text)`, `Identity` (key pair and name), `Allow` (up to 8 names). In `net.zig`, `me.name` is the guest's own name. On a connection whose handshake was accepted, `qconn.peer_name` is the other end's name, and it is set nowhere else.
- **On serial.** A guest that has a key prints `reflect: entity <text>` once, before `reflect: ready`.

The name commits to the algorithm, so a later `p256` or post-quantum key cannot collide with an Ed25519 one. Only `ed25519` is built here.

## 2. What the key is, and why not P-256

identikey-protocol has two classical identity keys: `ed25519`, the software key, and `p256`, the key a hardware enclave can hold. A guest has no enclave, so the entity key is identikey's software key, Ed25519. It is also the key the identikey wallet always holds.

TLS 1.3 carries it without a certificate. The handshake uses the signature scheme `ed25519` (0x0807) and raw public keys (RFC 7250): each end's Certificate message holds one SubjectPublicKeyInfo, the fixed 12 bytes `30 2a 30 05 06 03 2b 65 70 03 21 00` and the 32-byte key. Both ends offer and accept only that type (`client_certificate_type` and `server_certificate_type`, extensions 19 and 20, value 2).

Weighed against keeping P-256:

| | Ed25519, raw key | P-256, X.509 as now |
|---|---|---|
| What is given at boot | 32 bytes | A key and a certificate, or a certificate made and self-signed in the guest (a DER writer in Zig) |
| What a pin names | The key (through the name) | A certificate: a second thing with dates and a serial, re-issuable for one key |
| Signing | Deterministic, no random bytes | ECDSA takes a nonce per signature; a bad `RDRAND` leaks the key |
| identikey | The software key; the name above is identikey's own | The enclave key; no enclave here |
| Code | `std.crypto.sign.Ed25519` and `std.crypto.hash.Blake3` come in; `std.crypto.sign.ecdsa`, the DER signature and the search for a key in a certificate go out | Unchanged |
| Other QUIC stacks | Raw public keys are less widely built than X.509 | X.509 is universal, but this stack was never checked against another either |

Chosen: Ed25519 with raw public keys. What it costs is stated in the spec: a `p256` entity, such as a person's enclave key, cannot connect to a guest yet, and no other QUIC implementation has been tried.

### The handshake, message by message

Both ends are one file of code, so a mistake made the same way on both sides passes every exchange. The handshake is therefore fixed here against RFC 8446, and `quic-self` has a peer that breaks each rule in turn (§8).

| Message | Content | Rule |
|---|---|---|
| ClientHello | 32 random bytes; `supported_versions` 1.3; `supported_groups` and `key_share` X25519; `signature_algorithms` `08 07` only; `client_certificate_type` (19) and `server_certificate_type` (20), each the list `01 02`; QUIC transport parameters | RFC 8446 §4.1.2, RFC 7250 §3 |
| ServerHello | 32 random bytes, X25519 share | §4.1.3 |
| EncryptedExtensions | transport parameters; extensions 19 and 20, each the one byte `02` | RFC 7250 §3 |
| CertificateRequest | empty context; one extension, `signature_algorithms` holding `08 07` | §4.3.2 |
| Certificate (server) | empty context; one entry: the 44-byte SubjectPublicKeyInfo, no extensions | RFC 7250, RFC 8410 |
| CertificateVerify (server) | scheme `08 07`; a 64-byte signature over 64 spaces, `TLS 1.3, server CertificateVerify`, a zero byte, and the hash of ClientHello … server Certificate | §4.4.3 |
| Finished (server) | HMAC under the server handshake secret over ClientHello … server CertificateVerify | §4.4.4 |
| Certificate (client) | as the server's | |
| CertificateVerify (client) | as the server's, with `TLS 1.3, client CertificateVerify`, over ClientHello … server Finished, client Certificate | §4.4.3 |
| Finished (client) | HMAC under the client handshake secret over ClientHello … client CertificateVerify | §4.4.4 |

The application secrets come from the hash of ClientHello … server Finished and nothing after it (§7.1).

A reader refuses anything but exactly this: a context that is not empty, more or fewer than one entry, an entry that is not the 44 bytes, entry extensions, a scheme that is not `08 07`, a signature that is not 64 bytes, a message out of order, or bytes after Finished. The ClientHello and ServerHello randoms were the constants `11…` and `22…`; they are now random bytes. Finished values are compared in constant time.

## 3. How the key reaches the guest

What Cloud Hypervisor 54.0 gives a guest with no disk (`cloud-hypervisor --help` on morphie):

| Channel | Verdict |
|---|---|
| `--cmdline` | Every user of the host reads it in the process list, and it lands in logs and the API's `vm.info`. Used for what is public: the allowed names. |
| `--initramfs <file>` | The file's bytes go into guest memory. Only the path is on the command line. `kernel.zig` already finds the one PVH module, bounds it and moves it. **Chosen.** |
| `--platform oem_strings=`, `serial_number=`, `uuid=` | On the command line, so the same as `--cmdline`, and needs an SMBIOS reader. |
| `--disk`, `--pmem`, `--fs`, `--vsock`, `--tpm`, `--device` | Each needs a new driver in the layer. |
| `--serial`, `--console` input | The layer writes the serial port and never reads it; a reader and a framing would be new. |
| The network | Needs an identity before it has one. |
| `--restore` | A snapshot holds the key in its memory file; not a way to give one. |

The key file is exactly 32 bytes, the Ed25519 seed, and nothing else. The launcher starts the network image with `--initramfs <key-file>`. The image file and its hash do not hold the key, so one image serves every entity.

In the guest: `kernel.zig` moves the module above the image and clears where the hypervisor put it, as it does today. `net.zig` takes the bytes through a new export of the layer, `reflect_boot_take`, which copies them out, clears the layer's copy and forgets the file, so `/boot/program` no longer opens. `net.zig` makes the key pair, clears its copy of the bytes, and keeps the key pair for the life of the boot. Zig's key pair holds the seed inside its secret key, so the seed is in guest memory for the whole boot; clearing the copies only keeps it to one place. A file of 32 zero bytes is refused (`reflect: the entity key is all zero`): it is what a launcher that failed to write the key would give, and its name is known to everyone. The network image runs programs sent to it, so it has no other use for a file given at boot. The one-program image is unchanged: it does not call the export.

`kernel.zig` puts the command line's words into `argv` when a file was given at boot and stops at more than six words. The network image's command line has at most five (`reflect.ip`, `reflect.port`, one QUIC word, `reflect.allow`, `reflect.hook`).

### The trust boundary

Whoever launches the guest chooses its image, its memory and its command line, and can read or change that memory while it runs. So can root on the host, and anyone who can read the key file or a snapshot. **The launcher and the host hold every key they give a guest.** Giving the key at boot does not hide it from them and does not claim to.

What it does give: the key is not in the source tree, the image or its hash; it is not in the process list or the hypervisor's log; two guests from one image are two identities; and a holder of the source can no longer present the pinned identity.

**A guest with a QUIC word no longer answers plain UDP.** Until now a guest with `reflect.quic_port` also ran any `RFL1` program sent to `reflect.port` by anyone. With an allow-list that would be a second door beside the checked one, into the address space that now holds a long-term key. So a guest with `reflect.quic_port`, `reflect.wire_port` or `reflect.peer` drops every datagram to `reflect.port`, ping included. The word is still required, so command lines do not change shape. A guest with none of the three words serves UDP as before, with no key in it. Mjolnir's spec already says it sends nothing to that port.

What remains reachable without a name on the list: ARP, the IPv4 and UDP checks, and the QUIC handshake up to the allow check, all hand-written Zig built without safety checks. A fault there is a fault next to the key.

What it does not give: the guest cannot show that it is the only holder of the key, and a peer that trusts a name trusts the host that entity runs on. Every byte of guest memory is privileged and writable (`unikernel/README.md`), so the key is as safe from a program as Lean's evaluator is correct. Nothing is attested.

An owner who does not want an entity's key on a host cannot yet give a guest a lesser key that the entity's key signed. That would be a delegation (identikey's capability tokens) and is not built.

## 4. Each end checks the other

`reflect.allow=<name>[,<name>...]`, at most once, one to eight names in the text form above. It is the list of entities this guest will finish a handshake with, whichever end it is.

- A guest that serves (`reflect.quic_port`, `reflect.wire_port`) sends a CertificateRequest. The client answers with its key, a CertificateVerify signed over the transcript, and its Finished. The guest takes the name of the key, requires it to be in the list, verifies the signature and the Finished, and only then makes the 1-RTT keys.
- **Stream data is taken only from 1-RTT packets, and read only on an accepted connection.** The review of this design found that today `takeFrames` takes a STREAM frame in any packet number space, and the callers act on `peer_fin` alone. Initial keys are public, so one 1200-byte datagram from anyone made a serving guest run its bytes (the reply was not sent, the evaluation happened), and anyone who saw a client's first datagram could hand that client a forged reply. This change fixes it: STREAM frames are taken only in the 1-RTT space and CRYPTO frames only in the Initial and Handshake spaces (RFC 9000 §12.4); a packet with a frame its space does not allow is dropped whole; `readApp` gives nothing and `peer_fin` is not set unless the handshake was accepted.
- A guest that calls (`reflect.peer`) requires the server's name to be in its list before it sends its own key or the offer.
- The two-guest path: A (`reflect.peer`) has its key and `reflect.allow=<B's name>`; B (`reflect.wire_port`) has its key and `reflect.allow=<A's name>`. Each pins the other.
- The host client `quic-client` takes its key file and the one name it expects.

A QUIC word without `reflect.allow`, `reflect.allow` without a QUIC word, a name that does not parse, a repeated name or more than eight are refused like other bad configuration (`reflect: the network address is not valid`). There is no "allow anyone".

Refusal. An end that refuses sets `refused`, sends nothing more on that connection, not even an acknowledgement, and takes nothing more from it. A serving guest's refused connection gives way to the next new Initial at once. There is still no CONNECTION_CLOSE, so the refused end is not told: it resends its flight ten times over 6.36 s and gives up. `quic-client` exits 6 when its own flight is given up before any reply, instead of waiting out its 60 seconds. A calling guest prints `reflect: the peer is not allowed` when it refuses the server, and `reflect: the peer gave no answer` when its flight is given up. In the second case it had accepted the server, so its offer went out with its key, sealed for that server, which made no keys to open it.

Holding the connection. A guest has one QUIC connection. A host that keeps sending first flights that open, new ones or one replayed, takes the connection each time it is free and keeps it from going idle, for as long as it sends. It needs no key and no name on the list, so an unlisted host can shut listed ones out. That was true before this change and is still true; the spec said "2 seconds a time" and now says it as it is. More than one connection, or a Retry token, would be a change of its own (`homoiconic-q59.63`).

What a name on a connection means: the other end signed this handshake's transcript with that entity's key. Per the boundary above, that is the entity or its host.

## 5. A guest with no key

A guest given a QUIC word and no file at boot prints `reflect: no entity key` and powers off, before `reflect: ready`. A file that is not 32 bytes: `reflect: the entity key is not 32 bytes`. Thirty-two zero bytes: `reflect: the entity key is all zero`. There is no built-in key to fall back to: `guest_key`, `guest_cert` and `certificate()` are deleted from `quic.zig`, and no key is in the tree.

A guest with no QUIC word serves UDP as before. A file given to it is cleared and not used.

Test keys: `check-quic.sh` and `check-wire.sh` make theirs from `/dev/urandom` on each run. `quic-self.zig` holds seeds: its own fixed sequence and identikey's published fixture seed. It is a test program that is not linked into an image. What the tree must not hold is a key that any guest or client accepts without being told to, and there is none: nothing has a built-in name or list.

## 6. The exit test

The key is 32 bytes in a file its owner made with any tool (`head -c 32 /dev/urandom`). The name is computed offline, by `unikernel/out-net/entity name <key-file>` or by identikey's own code. The guest does not make, change, export or escrow a key, and no service holds one. An owner who stops using a launcher, this image or this project still has the key and can run the entity elsewhere under the same name. A launcher that makes a key for an entity must hand that file to the owner; that rule is the launcher's (Mjolnir's change), and nothing here lets a launcher hold a key the owner cannot have.

There is no rotation and no revocation. A new key is a new name. A host that was once given a key still has a working copy after the owner has left it; the only remedy is for peers to take that name off their lists.

## 7. What changes for callers

- `quic.zig`: `Conn.openClient(rand, identity, allow)` and `Conn.openServer(rand, identity, allow)`. `certificate()` is gone. `Conn.peer_name` and `Conn.gave_up` are new.
- `quic-client <ip> <port> <budget> <program-file> <key-file> <server-name> [mode]`; `wrong` now means "expect to refuse the server", `denied` means "expect the guest to refuse this key", and `early` sends stream data in the Initial packet and expects no reply.
- Mjolnir vendors `quic.zig` and now `entity.zig`, gives each guest a key file and `reflect.allow=<its client's name>`, and pins the guest's name. Until it does, its guests refuse to start QUIC (`reflect: no entity key`): bead `mjolnir-6h01` and a Mjolnir change follow this one.

## 8. Checks, each with its control

On real guests (`check-quic.sh`, `check-wire.sh`):

| Claim | Check | Control (the fix undone) |
|---|---|---|
| Two keys, two identities | A guest with key 3 prints another name than the guest with key 1, each equal to `entity name` of its file; the client that expects name 1 refuses it | Guest ignores the file and uses one fixed seed |
| Same key, same identity | The guest with key 1 is booted twice: same name, and the client that expects it is served | Guest mixes `RDRAND` into the seed |
| A wrong server pin is refused | Client that expects name 3, against the key-1 guest, exits 0 in `wrong` mode | Client skips the allow check |
| A client not allowed is refused | Client with key 3 accepts the guest, gets no reply, sees its flight given up, and exits 0 in `denied` mode (not 0 against a guest that never answered) | Guest skips the allow check |
| A refused connection gives way at once | The allowed client, started half a second after the `denied` one, is served within 2 s | Give-way on `refused` removed: the denied client's resends hold the connection about 8 s |
| No key, no QUIC | Boot with no `--initramfs`, with 31 bytes, with 32 zero bytes: the three lines, no `ready`, hypervisor exits | Guest falls back to a fixed seed |
| No plain UDP beside QUIC | A UDP ping to the serving guest's `reflect.port` gets nothing, and factorial over QUIC still works | The drop removed: a pong comes back |
| Stream data before the handshake | A guest booted with `reflect.hook=alloc` stops at its first run request. `quic-client ... early` sends it a first flight whose Initial packet also carries a STREAM frame with FIN holding a run request: the guest is still up 3 s later. The allowed client's request then stops it, which shows the hook was armed | The space rule removed: the guest stops at the first datagram |
| Each guest pins the other | Right names pass; A with a wrong name for B prints `the peer is not allowed`; B with a wrong name for A leaves A with `the peer gave no answer`; neither prints `remote ok` | The two allow checks above |

In one process (`quic-self`), where one end can be made to break a rule. `Conn.signer` is the key an end signs with, apart from the key it presents, `Conn.fault` makes it break one rule, and `Conn.earlyStream` puts a STREAM frame into a flight of the Initial or Handshake space. `net.zig` uses none of them; `quic-client` uses `earlyStream` in its `early` mode only.

| Claim | Check | Control |
|---|---|---|
| The name is identikey's | The vector of §1; base58 both ways and the refused texts | A changed prefix byte |
| A wrong pin | Client expects another name: refused, sends no key and no data | Client allow check removed |
| A client not allowed | Server refuses, has no 1-RTT keys, sends nothing more | Server allow check removed |
| A server that presents an allowed key it does not hold | Server's `signer` is another key: client refuses | Client skips the server's CertificateVerify |
| A client that presents an allowed key it does not hold | Client's `signer` is another key: server refuses | Server skips the client's CertificateVerify |
| A signature over another transcript, each direction | `fault = .transcript`: the right key signs a hash with one bit changed; the other end refuses | The same two controls |
| A client that sends only Finished | `fault = .no_certificate`: the server refuses. This is the flight today's server accepts | Server takes a lone Finished |
| A bad Finished, each direction | `fault = .finished`: refused | Finished check removed, each end |
| STREAM in an Initial or Handshake packet, each end | `earlyStream` puts a STREAM frame with FIN beside the CRYPTO frame: `readApp` is empty, `peer_fin` false, and the packet changed nothing | The space rule removed |

The controls are run on a copy of the tree with each fix undone in turn, and the log is kept in `unikernel/evidence/entity-keys-controls.log`.
