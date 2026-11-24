//! In-process QUIC: a clean exchange, a lossy reordered exchange, a wrong pin,
//! and exchanges with garbage datagrams given to both ends at every step.
//! Then what a server sends and stops sending: an acknowledgement in one
//! packet number space leaves the flight of another, a first flight nobody
//! follows is answered with at most three times its bytes, and a reply
//! nobody acknowledges is given up.
const std = @import("std");
const quic = @import("quic.zig");

var state: u64 = 0x123456789abcdef0;
fn rnd() u64 {
    state = state *% 0x9E3779B97F4A7C15 +% 1;
    return state;
}

fn junk(buf: []u8, first: u8) void {
    var i: usize = 0;
    while (i < buf.len) : (i += 1) buf[i] = @truncate(rnd() >> 24);
    buf[0] = first;
    if (first & 0x80 != 0) {
        std.mem.writeInt(u32, buf[1..5], 1, .big);
        buf[5] = 8;
        buf[14] = 8;
        buf[23] = 0;
        buf[24] = 0x40 | @as(u8, @truncate((buf.len - 26) >> 8));
        buf[25] = @truncate(buf.len - 26);
    }
}

/// Garbage that must open under no key and change nothing: a full-size
/// Initial, a Handshake packet and a short header.
fn noise(to: *quic.Conn, now: u64) bool {
    var buf: [1200]u8 = undefined;
    junk(buf[0..1200], 0xc3);
    if (to.recv(buf[0..1200], now)) return false;
    junk(buf[0..400], 0xe1);
    if (to.recv(buf[0..400], now)) return false;
    junk(buf[0..90], 0x41);
    if (to.recv(buf[0..90], now)) return false;
    return true;
}

fn exchange(loss: bool, wrong: bool, noisy: bool) u8 {
    var pin: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(quic.certificate(), &pin, .{});
    if (wrong) pin[0] ^= 1;
    var client = quic.Conn.openClient(rnd, &pin);
    var server = quic.Conn.openServer(rnd);
    return drive(&client, &server, 1_000_000_000, loss, wrong, noisy);
}

/// Carry datagrams between the two ends from `start` until the client has
/// the reply.
fn drive(client: *quic.Conn, server: *quic.Conn, start: u64, loss: bool, wrong: bool, noisy: bool) u8 {
    var hold_c: [1500]u8 = undefined;
    var hold_cn: usize = 0;
    var hold_s: [1500]u8 = undefined;
    var hold_sn: usize = 0;
    var now: u64 = start;
    var n: usize = 0;
    var drops: usize = 0;
    while (n < 40) : (n += 1) {
        var buf: [1500]u8 = undefined;
        var sb: [1500]u8 = undefined;
        if (noisy) {
            const cid = client.peer_cid;
            if (!noise(server, now) or !noise(client, now)) return 10;
            // The client names the server by an ID from a packet that opened.
            if (!std.mem.eql(u8, &cid, &client.peer_cid)) return 11;
        }
        const cn = client.send(&buf, now);
        const sn = server.send(&sb, now);
        if (cn > 0) deliver(server, buf[0..cn], &hold_c, &hold_cn, loss, &drops, now);
        if (sn > 0) deliver(client, sb[0..sn], &hold_s, &hold_sn, loss, &drops, now);
        if (client.accepted and !client.app_tx_on) {
            if (!client.writeApp("program-bytes")) return 3;
        }
        if (server.accepted and server.peer_fin and !server.sent_fin) {
            if (!std.mem.eql(u8, server.readApp(), "program-bytes")) return 4;
            if (!server.writeApp("reply-bytes")) return 5;
        }
        if (client.peer_fin) {
            if (!std.mem.eql(u8, client.readApp(), "reply-bytes")) return 6;
            if (loss and drops < 3) return 7;
            return 0;
        }
        if (client.refused) return if (wrong) 0 else 8;
        now += 30_000_000;
    }
    return 9;
}

fn deliver(to: *quic.Conn, pkt: []const u8, hold: []u8, hn: *usize, loss: bool, drops: *usize, now: u64) void {
    drops.* += 1;
    if (loss and drops.* % 5 == 0) return;
    if (loss and hn.* == 0) {
        @memcpy(hold[0..pkt.len], pkt);
        hn.* = pkt.len;
        return;
    }
    if (hn.* != 0) {
        _ = to.recv(pkt, now);
        _ = to.recv(hold[0..hn.*], now);
        hn.* = 0;
    } else _ = to.recv(pkt, now);
}

/// What may start a connection: a full-size version 1 Initial for another ID.
fn shapes() bool {
    var buf: [1200]u8 = undefined;
    junk(buf[0..1200], 0xc3);
    var cur: [8]u8 = undefined;
    @memcpy(&cur, buf[6..14]);
    if (quic.newInitial(buf[0..1200], &cur)) return false; // the connection in place
    cur[0] ^= 1;
    if (!quic.newInitial(buf[0..1200], &cur)) return false;
    if (quic.newInitial(buf[0..1199], &cur)) return false; // too small
    buf[0] = 0xe3;
    if (quic.newInitial(buf[0..1200], &cur)) return false; // a Handshake packet
    buf[0] = 0x43;
    if (quic.newInitial(buf[0..1200], &cur)) return false; // a short header
    buf[0] = 0xc3;
    buf[4] = 2;
    if (quic.newInitial(buf[0..1200], &cur)) return false; // another version
    // A real first flight cut below 1200 bytes starts nothing on a server.
    var pin: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(quic.certificate(), &pin, .{});
    var client = quic.Conn.openClient(rnd, &pin);
    var server = quic.Conn.openServer(rnd);
    var first: [1500]u8 = undefined;
    const n = client.send(&first, 1);
    if (n < 1200) return false;
    if (server.recv(first[0..1199], 1)) return false;
    if (!server.recv(first[0..n], 1)) return false;
    return true;
}

const ms: u64 = 1_000_000;

fn pinned() [32]u8 {
    var pin: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(quic.certificate(), &pin, .{});
    return pin;
}

/// The length of the long-header packet at the front of a datagram.
fn firstLen(d: []const u8) ?usize {
    if (d.len < 26 or d[0] & 0x80 == 0) return null;
    var o: usize = 23;
    if (d[0] & 0x30 == 0) {
        if (d[o] != 0) return null; // a token
        o += 1;
    }
    const width = @as(usize, 1) << @intCast(d[o] >> 6);
    if (o + width > d.len) return null;
    var v: usize = d[o] & 0x3f;
    var i: usize = 1;
    while (i < width) : (i += 1) v = (v << 8) | d[o + i];
    if (o + width + v > d.len) return null;
    return o + width + v;
}

/// An acknowledgement clears the flight of its own packet number space only.
/// The server's Initial and Handshake flights both go out as packet 0. The
/// client gets the Initial and not the Handshake packet, and its resent
/// first flight acknowledges Initial packet 0. The Handshake flight is still
/// owed, and the server must send it again.
fn spaces() u8 {
    const pin = pinned();
    var client = quic.Conn.openClient(rnd, &pin);
    var server = quic.Conn.openServer(rnd);
    var a: [1500]u8 = undefined;
    var d: [1500]u8 = undefined;
    const a0 = client.send(&a, 0);
    if (a0 == 0 or !server.recv(a[0..a0], 0)) return 20;
    // The client resends before the answer comes, and the resend is lost:
    // the answer acknowledges packet 0, the client waits on packet 1.
    var lost: [1500]u8 = undefined;
    if (client.send(&lost, 50 * ms) == 0) return 20;
    const dn = server.send(&d, 50 * ms);
    const cut = firstLen(d[0..dn]) orelse return 20;
    if (cut >= dn) return 20; // Initial and Handshake left in one datagram
    if (!client.recv(d[0..cut], 50 * ms)) return 20;
    const a2 = client.send(&a, 140 * ms);
    if (a2 == 0 or a[0] & 0xf0 != 0xc0 or firstLen(a[0..a2]) != a2) return 20; // one Initial
    if (!server.recv(a[0..a2], 140 * ms)) return 20;
    const r = server.send(&d, 140 * ms);
    if (r == 0) return 21; // the Initial acknowledgement cleared the Handshake flight
    if (d[0] & 0xf0 != 0xe0 or firstLen(d[0..r]) != r) return 22; // the Handshake flight alone
    if (!client.recv(d[0..r], 140 * ms)) return 20;
    return drive(&client, &server, 140 * ms, false, false, false);
}

/// A first flight whose sender is never heard from again is answered with at
/// most three times its bytes, however long the server is left. When the
/// client is there after all, its resent first flight lets the server send
/// again and the exchange finishes.
fn unvalidated() u8 {
    const pin = pinned();
    var client = quic.Conn.openClient(rnd, &pin);
    var server = quic.Conn.openServer(rnd);
    var a: [1500]u8 = undefined;
    var d: [1500]u8 = undefined;
    const a0 = client.send(&a, 0);
    if (a0 == 0 or !server.recv(a[0..a0], 0)) return 23;
    var total: usize = 0;
    var sends: usize = 0;
    var now: u64 = 0;
    while (now < 60_000 * ms) : (now += 10 * ms) {
        const n = server.send(&d, now);
        total += n;
        if (n != 0) sends += 1;
    }
    if (sends < 2) return 23; // it does resend to a client that may have lost the flight
    if (total > quic.amplification * a0) return 24;
    const a1 = client.send(&a, now);
    if (a1 == 0 or !server.recv(a[0..a1], now)) return 25;
    const n = server.send(&d, now);
    if (n == 0 or !client.recv(d[0..n], now)) return 25;
    return drive(&client, &server, now, false, false, false);
}

/// The client never acknowledges the reply. The server resends it and then
/// gives it up; the client, whose flights were all acknowledged, is silent.
fn givesUp() u8 {
    const pin = pinned();
    var client = quic.Conn.openClient(rnd, &pin);
    var server = quic.Conn.openServer(rnd);
    const done = drive(&client, &server, 0, false, false, false);
    if (done != 0) return done;
    var d: [1500]u8 = undefined;
    var sends: usize = 0;
    var last: u64 = 0;
    var now: u64 = 10_000 * ms;
    while (now < 130_000 * ms) : (now += 10 * ms) {
        if (client.send(&d, now) != 0) return 26;
        if (server.send(&d, now) != 0) {
            sends += 1;
            last = now;
        }
    }
    if (sends == 0) return 27; // a lost reply is resent
    if (sends >= quic.max_tries or last > 70_000 * ms) return 28;
    return 0;
}

pub fn main() u8 {
    if (!quic.rfcInitialKey()) return 1;
    const clean = exchange(false, false, false);
    if (clean != 0) return clean;
    const lossy = exchange(true, false, false);
    if (lossy != 0) return lossy;
    const bad = exchange(false, true, false);
    if (bad != 0) return bad;
    const noisy = exchange(false, false, true);
    if (noisy != 0) return noisy;
    const both = exchange(true, false, true);
    if (both != 0) return both;
    if (!shapes()) return 12;
    const own = spaces();
    if (own != 0) return own;
    const bound = unvalidated();
    if (bound != 0) return bound;
    const quiet = givesUp();
    if (quiet != 0) return quiet;
    std.debug.print("quic self ok\n", .{});
    return 0;
}
