//! Host QUIC client. Verifies the guest certificate, sends one RFL1 payload,
//! acknowledges the reply in a packet of its own, and writes the reply bytes
//! to stdout. `loss` drops and reorders datagrams, the acknowledgement too.
//! `silent` takes the reply and leaves without acknowledging it.
//! `wrong` expects the peer key to be refused.
//! `spoof <local-ip>` plays a second host at <local-ip> beside the exchange:
//! once the handshake is accepted it sends the guest garbage and a well-formed
//! new Initial from that address, then loses the first copy of the reply,
//! sends garbage long-header datagrams from both addresses and goes silent
//! until the guest has resent the reply. The exchange must still finish, and
//! the second address must hear nothing from the guest (exit 5 otherwise).
//! `initial` writes the first datagram of a handshake to stdout and sends nothing.

const std = @import("std");
const quic = @import("quic.zig");

extern fn socket(domain: c_int, kind: c_int, proto: c_int) c_int;
extern fn sendto(fd: c_int, buf: [*]const u8, n: usize, flags: c_int, addr: *const Sock, len: u32) isize;
extern fn recvfrom(fd: c_int, buf: [*]u8, n: usize, flags: c_int, addr: *Sock, len: *u32) isize;
extern fn bind(fd: c_int, addr: *const Sock, len: u32) c_int;
extern fn clock_gettime(clk: c_int, ts: *Time) c_int;
extern fn write(fd: c_int, buf: [*]const u8, n: usize) isize;

const Sock = extern struct { family: u16, port: u16, addr: u32, zero: [8]u8 };
const Time = extern struct { sec: i64, nsec: i64 };

extern fn getrandom(buf: [*]u8, n: usize, flags: c_uint) isize;
extern fn _exit(status: c_int) noreturn;

/// Connection IDs and the key share come from the operating system. A fixed
/// sequence here gave every run the same IDs and the same private share.
fn rnd() u64 {
    var b: [8]u8 = undefined;
    var n: usize = 0;
    while (n < b.len) {
        const r = getrandom(b[n..].ptr, b.len - n, 0);
        if (r <= 0) _exit(2);
        n += @intCast(r);
    }
    return std.mem.readInt(u64, &b, .little);
}
fn now() u64 {
    var t: Time = undefined;
    _ = clock_gettime(1, &t);
    return @as(u64, @intCast(t.sec)) * 1_000_000_000 + @as(u64, @intCast(t.nsec));
}
fn ip4(s: []const u8) ?u32 {
    var n: u32 = 0;
    var acc: u32 = 0;
    var parts: u32 = 0;
    for (s) |c| {
        if (c == '.') {
            if (parts == 3) return null;
            n = (n << 8) | acc;
            acc = 0;
            parts += 1;
        } else if (c >= '0' and c <= '9') acc = acc * 10 + (c - '0') else return null;
    }
    if (parts != 3) return null;
    return (n << 8) | acc;
}

var hold: [1500]u8 = undefined;
var hold_n: usize = 0;
var sent: usize = 0;

fn pump(c: *quic.Conn, fd: c_int, dst: *const Sock, loss: bool) void {
    var buf: [1500]u8 = undefined;
    const n = c.send(&buf, now());
    if (n == 0) return;
    sent += 1;
    if (loss and sent % 5 == 0) return;
    if (loss and hold_n == 0) {
        @memcpy(hold[0..n], buf[0..n]);
        hold_n = n;
        return;
    }
    _ = sendto(fd, buf[0..n].ptr, n, 0, dst, @sizeOf(Sock));
    if (hold_n != 0) {
        _ = sendto(fd, hold[0..hold_n].ptr, hold_n, 0, dst, @sizeOf(Sock));
        hold_n = 0;
    }
}

var probe: quic.Conn = undefined;
var other: quic.Conn = undefined;

fn junk(buf: []u8) void {
    var i: usize = 0;
    while (i < buf.len) : (i += 8) {
        const v = rnd();
        var j: usize = 0;
        while (j < 8 and i + j < buf.len) : (j += 1) buf[i + j] = @truncate(v >> @intCast(8 * j));
    }
}

/// A datagram with a version 1 long header of the given first byte and
/// 8-byte connection IDs, and random bytes for the rest.
fn longJunk(buf: []u8, first: u8) void {
    junk(buf);
    buf[0] = first;
    std.mem.writeInt(u32, buf[1..5], 1, .big);
    buf[5] = 8;
    buf[14] = 8;
    if (first & 0x30 == 0) {
        buf[23] = 0; // no token
        buf[24] = 0x40 | @as(u8, @truncate((buf.len - 26) >> 8));
        buf[25] = @truncate(buf.len - 26);
    } else {
        buf[23] = 0x40 | @as(u8, @truncate((buf.len - 25) >> 8));
        buf[24] = @truncate(buf.len - 25);
    }
}

fn put(fd: c_int, dst: *const Sock, bytes: []const u8) void {
    _ = sendto(fd, bytes.ptr, bytes.len, 0, dst, @sizeOf(Sock));
}

/// Garbage that opens under no key: a short header, an Initial of full size,
/// a small Initial and a Handshake packet.
fn garbage(fd: c_int, dst: *const Sock) void {
    var buf: [1200]u8 = undefined;
    junk(buf[0..80]);
    buf[0] = 0x43;
    put(fd, dst, buf[0..80]);
    longJunk(buf[0..1200], 0xc3);
    put(fd, dst, buf[0..1200]);
    longJunk(buf[0..300], 0xc1);
    put(fd, dst, buf[0..300]);
    longJunk(buf[0..400], 0xe2);
    put(fd, dst, buf[0..400]);
}

fn heard(fd: c_int) bool {
    var pkt: [1500]u8 = undefined;
    var from: Sock = undefined;
    var ln: u32 = @sizeOf(Sock);
    return recvfrom(fd, &pkt, pkt.len, 0x40, &from, &ln) > 0;
}

/// Send nothing for `ns`. Datagrams for the exchange are still taken.
/// False when the second address hears anything.
fn quiet(c: *quic.Conn, fd: c_int, sfd: c_int, ns: u64) bool {
    const start = now();
    while (now() - start < ns) {
        if (heard(sfd)) return false;
        var pkt: [1500]u8 = undefined;
        var from: Sock = undefined;
        var ln: u32 = @sizeOf(Sock);
        const r = recvfrom(fd, &pkt, pkt.len, 0x40, &from, &ln);
        if (r > 0) _ = c.recv(pkt[0..@intCast(r)], now());
    }
    return true;
}

pub fn main(init: std.process.Init.Minimal) u8 {
    const v = init.args.vector;
    if (v.len < 5) return 2;
    const ip = ip4(std.mem.span(v[1])) orelse return 2;
    const port = std.fmt.parseInt(u16, std.mem.span(v[2]), 10) catch return 2;
    const budget = std.fmt.parseInt(u64, std.mem.span(v[3]), 10) catch return 2;
    const path = std.mem.span(v[4]);
    const mode = if (v.len > 5) std.mem.span(v[5]) else "";
    const loss = std.mem.eql(u8, mode, "loss");
    const wrong = std.mem.eql(u8, mode, "wrong");
    const spoof = std.mem.eql(u8, mode, "spoof");
    const only_initial = std.mem.eql(u8, mode, "initial");
    const silent = std.mem.eql(u8, mode, "silent");
    if (mode.len != 0 and !loss and !wrong and !spoof and !only_initial and !silent) return 2;
    if (spoof and v.len < 7) return 2;
    var pin: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(quic.certificate(), &pin, .{});
    if (wrong) pin[0] ^= 0xff;
    var file: [1 << 16]u8 = undefined;
    const n = readFile(path, &file) orelse return 2;
    var frame: [1200]u8 = undefined;
    if (24 + n > frame.len) return 2;
    @memcpy(frame[0..4], "RFL1");
    frame[4] = 0;
    frame[5] = 0;
    frame[6] = 0;
    frame[7] = 0;
    std.mem.writeInt(u64, frame[8..16], 7, .big);
    std.mem.writeInt(u64, frame[16..24], budget, .big);
    @memcpy(frame[24..][0..n], file[0..n]);

    var c = quic.Conn.openClient(rnd, &pin);
    if (only_initial) {
        var first: [1500]u8 = undefined;
        const fnn = c.send(&first, now());
        if (fnn < quic.min_initial or write(1, &first, fnn) != @as(isize, @intCast(fnn))) return 2;
        return 0;
    }
    const fd = socket(2, 2, 17);
    if (fd < 0) return 2;
    var local = Sock{ .family = 2, .port = 0, .addr = 0, .zero = .{0} ** 8 };
    if (bind(fd, &local, @sizeOf(Sock)) != 0) return 2;
    var dst = Sock{ .family = 2, .port = @byteSwap(port), .addr = @byteSwap(ip), .zero = .{0} ** 8 };
    var sfd: c_int = -1;
    if (spoof) {
        const sip = ip4(std.mem.span(v[6])) orelse return 2;
        sfd = socket(2, 2, 17);
        if (sfd < 0) return 2;
        var second = Sock{ .family = 2, .port = 0, .addr = @byteSwap(sip), .zero = .{0} ** 8 };
        if (bind(sfd, &second, @sizeOf(Sock)) != 0) return 2;
    }
    var stage: u8 = 0;
    const start = now();
    while (now() - start < 60_000_000_000) {
        // Once the reply is in, what there is to send is its acknowledgement.
        if (!(silent and c.peer_fin)) pump(&c, fd, &dst, loss);
        if (spoof and heard(sfd)) return 5;
        if (spoof and stage == 0 and c.accepted) {
            // Mid-connection, from the second address: garbage, and the
            // well-formed first flight of another handshake.
            garbage(sfd, &dst);
            other = quic.Conn.openClient(rnd, &pin);
            var first: [1500]u8 = undefined;
            const fnn = other.send(&first, now());
            if (fnn < quic.min_initial) return 2;
            put(sfd, &dst, first[0..fnn]);
            // The guest must answer none of it.
            if (!quiet(&c, fd, sfd, 500_000_000)) return 5;
            stage = 1;
        }
        if (c.accepted and !c.app_tx_on) {
            if (!c.writeApp(frame[0 .. 24 + n])) return 2;
        }
        if (c.refused) return if (wrong) 0 else 3;
        if (c.peer_fin) {
            const got = c.readApp();
            if (wrong) return 3;
            // The acknowledgement went out in the pump above, or is held
            // there to be sent after something else: nothing else follows.
            if (hold_n != 0 and !silent) {
                _ = sendto(fd, hold[0..hold_n].ptr, hold_n, 0, &dst, @sizeOf(Sock));
                hold_n = 0;
            }
            if (spoof and (stage != 2 or !quiet(&c, fd, sfd, 500_000_000))) return 5;
            var off: usize = 0;
            while (off < got.len) {
                const w = write(1, got[off..].ptr, got.len - off);
                if (w <= 0) return 2;
                off += @intCast(w);
            }
            return 0;
        }
        var pkt: [1500]u8 = undefined;
        var from: Sock = undefined;
        var ln: u32 = @sizeOf(Sock);
        const r = recvfrom(fd, &pkt, pkt.len, 0x40, &from, &ln); // MSG_DONTWAIT
        if (r > 0 and spoof and stage == 1) {
            // Would this datagram finish the reply? Then lose it, as a
            // network might, and send garbage from both addresses, the
            // second address last, before the guest resends. Then send
            // nothing: the guest's next packets are its own resends of the
            // reply, and they must come here and not go there.
            probe = c;
            _ = probe.recv(pkt[0..@intCast(r)], now());
            if (probe.peer_fin) {
                garbage(fd, &dst);
                garbage(sfd, &dst);
                stage = 2;
                if (!quiet(&c, fd, sfd, 500_000_000)) return 5;
                if (!c.peer_fin) return 5;
                continue;
            }
        }
        if (r > 0) _ = c.recv(pkt[0..@intCast(r)], now());
    }
    if (hold_n != 0) _ = sendto(fd, hold[0..hold_n].ptr, hold_n, 0, &dst, @sizeOf(Sock));
    return if (wrong) 3 else 4;
}

fn readFile(path: []const u8, buf: []u8) ?usize {
    var z: [4096:0]u8 = undefined;
    if (path.len >= z.len) return null;
    @memcpy(z[0..path.len], path);
    z[path.len] = 0;
    const fd = openRead(z[0..path.len :0]);
    if (fd < 0) return null;
    var n: usize = 0;
    while (n < buf.len) {
        const r = read(fd, buf[n..].ptr, buf.len - n);
        if (r < 0) return null;
        if (r == 0) break;
        n += @intCast(r);
    }
    _ = close(fd);
    return n;
}
extern fn open(path: [*:0]const u8, flags: c_int) c_int;
extern fn read(fd: c_int, buf: [*]u8, n: usize) isize;
extern fn close(fd: c_int) c_int;

fn openRead(path: [*:0]const u8) c_int {
    return open(path, 0);
}
