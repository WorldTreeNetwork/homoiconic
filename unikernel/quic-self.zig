//! In-process QUIC: a clean exchange, a lossy reordered exchange, a wrong pin,
//! and exchanges with garbage datagrams given to both ends at every step.
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
    var hold_c: [1500]u8 = undefined;
    var hold_cn: usize = 0;
    var hold_s: [1500]u8 = undefined;
    var hold_sn: usize = 0;
    var now: u64 = 1_000_000_000;
    var n: usize = 0;
    var drops: usize = 0;
    while (n < 40) : (n += 1) {
        var buf: [1500]u8 = undefined;
        var sb: [1500]u8 = undefined;
        if (noisy) {
            const cid = client.peer_cid;
            if (!noise(&server, now) or !noise(&client, now)) return 10;
            // The client names the server by an ID from a packet that opened.
            if (!std.mem.eql(u8, &cid, &client.peer_cid)) return 11;
        }
        const cn = client.send(&buf, now);
        const sn = server.send(&sb, now);
        if (cn > 0) deliver(&server, buf[0..cn], &hold_c, &hold_cn, loss, &drops, now);
        if (sn > 0) deliver(&client, sb[0..sn], &hold_s, &hold_sn, loss, &drops, now);
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
    std.debug.print("quic self ok\n", .{});
    return 0;
}
