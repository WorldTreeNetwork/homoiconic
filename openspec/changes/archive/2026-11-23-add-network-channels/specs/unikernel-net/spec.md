# unikernel-net delta: a channel to another guest

## ADDED Requirements

### Requirement: Two guests carry a remote channel over QUIC

The command line MAY carry `reflect.wire_port=<port>` or `reflect.peer=<a.b.c.d>:<port>`, each at most once and not both; a repeated, malformed or combined word SHALL be refused as other bad configuration is (`unikernel/net.zig` `parse`). A guest with either SHALL start the paravirtual clock as a QUIC guest does, or power off with `reflect: no monotonic clock`. A guest with `reflect.wire_port` SHALL print `reflect: wire <port>`, serve QUIC on that port with the compiled certificate, and answer the first stream it receives, once per connection, with the bytes of the Lean export `reflect_remote_take` on what it received; bytes from Lean that are empty or longer than 1200 SHALL send nothing. A guest with `reflect.peer` SHALL print `reflect: peer <ip>:<port>`, find the peer's MAC by ARP, connect from UDP port 9000 as a QUIC client pinned to the compiled certificate, and once the handshake is accepted send the bytes of `reflect_remote_offer`. When the peer's stream ends it SHALL compare what came back with `reflect_remote_take` of its own offer, computed in its own Lean, and print `reflect: remote ok` and `reflect: log ` followed by the text of `reflect_remote_log` when they are equal, or `reflect: remote differs` when they are not (`net.zig` `wirePump`). Zig SHALL pass these bytes, compare them only for equality, and SHALL NOT decode them. The offer is the one program built into Lean (`Surface.Remote.program`, the text of `examples/remote.hom`); a peer guest sends nothing else. `reflect.quic_port` given together with either word is not refused today, and the two share one connection (`homoiconic-q59.50`).

#### Scenario: Two guests on one bridge

- GIVEN guest B booted with `reflect.ip=192.168.249.3 reflect.port=4444 reflect.wire_port=4446` and guest A with `reflect.ip=192.168.249.2 reflect.port=4444 reflect.peer=192.168.249.3:4446`, each on its own TAP on one bridge
- WHEN A connects to B
- THEN B's serial shows `reflect: wire 4446`, and within 90 seconds A's serial shows `reflect: remote ok` and a `reflect: log ` line (`unikernel/check-wire.sh`)

### Requirement: The wire check uses two real guests

`unikernel/check-wire.sh` SHALL require KVM and Cloud Hypervisor v54.0, build with `build-net.sh`, run `kernel/RemoteCheck.lean` and require `ok   a remote closure replays to 42` with no `FAIL` line, run `unikernel/out/remote-check` (which links the same Lean objects as the guests and exits 0 only when `reflect_remote_same` gives 1), and then boot the two guests of the scenario above on two TAPs on its own bridge. It SHALL remove the TAPs and the bridge on exit. It stops the guests when every step passes; when a step fails they are left to their 180-second timeout.

#### Scenario: The check passes

- GIVEN morphie with Cloud Hypervisor 54.0
- WHEN `sh unikernel/check-wire.sh` runs
- THEN it prints `wire guests ok` and exits 0
