//! Host QUIC client. Verifies the guest certificate, sends one RFL1 payload,
//! and writes the reply bytes to stdout. `loss` drops and reorders datagrams.
//! `wrong` expects the peer key to be refused.

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

var rng: u64 = 0xdecafbad;
fn rnd() u64 {
    rng = rng *% 0x9E3779B97F4A7C15 +% 1;
    return rng;
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
    const fd = socket(2, 2, 17);
    if (fd < 0) return 2;
    var local = Sock{ .family = 2, .port = 0, .addr = 0, .zero = .{0} ** 8 };
    if (bind(fd, &local, @sizeOf(Sock)) != 0) return 2;
    var dst = Sock{ .family = 2, .port = @byteSwap(port), .addr = @byteSwap(ip), .zero = .{0} ** 8 };
    const start = now();
    while (now() - start < 60_000_000_000) {
        pump(&c, fd, &dst, loss);
        if (c.accepted and !c.app_tx_on) {
            if (!c.writeApp(frame[0 .. 24 + n])) return 2;
        }
        if (c.refused) return if (wrong) 0 else 3;
        if (c.peer_fin) {
            const got = c.readApp();
            if (wrong) return 3;
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
        if (r > 0) c.recv(pkt[0..@intCast(r)], now());
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
