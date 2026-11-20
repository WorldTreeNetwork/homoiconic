# A channel on another machine

A send on a remote name leaves as the wire bytes of a closure and a reply name. The other machine runs the closure, and the message it sends on that name comes back on the QUIC stream. The schedule of those deliveries is the log. The same program, given that schedule, finishes with the same result on one machine.

A name inside one machine is still a number the holder may use. That another machine cannot forge a name is a hypothesis about the host, not a proof.

The QUIC packet format, the certificate, and the virtio-net device are unchanged. `reflect.quic_port` still carries one RFL1 exchange. The remote channel uses `reflect.wire_port` and `reflect.peer`.
