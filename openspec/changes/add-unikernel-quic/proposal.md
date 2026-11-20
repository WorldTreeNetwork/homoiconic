# Authenticated QUIC on the reflect guest

QUIC v1 runs on the existing virtio-net UDP path. The optional `reflect.quic_port` word leaves the UDP service and its command line unchanged. Zig carries datagrams and stream bytes. Lean still produces the reply through `reflect_reply_bytes`.

The guest clock is the KVM paravirtual clock. The one-program `clock_gettime` stand-in is untouched. The peer identity is a compiled P-256 certificate; the client checks its SHA-256 before it sends application data. A different pin is refused.

One bidirectional stream carries one RFL1 frame. After that exchange the guest accepts another handshake, so a budget reply does not take the guest down. The NIC feature bits, BARs, and queues are unchanged.
