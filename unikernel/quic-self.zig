//! In-process QUIC: a clean exchange, a lossy reordered exchange, a wrong pin.
const std = @import("std");
const quic = @import("quic.zig");

var state: u64 = 0x123456789abcdef0;
fn rnd() u64 {
    state = state *% 0x9E3779B97F4A7C15 +% 1;
    return state;
}

fn exchange(loss: bool, wrong: bool) u8 {
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
        to.recv(pkt, now);
        to.recv(hold[0..hn.*], now);
        hn.* = 0;
    } else to.recv(pkt, now);
}

pub fn main() u8 {
    if (!quic.rfcInitialKey()) return 1;
    const clean = exchange(false, false);
    if (clean != 0) return clean;
    const lossy = exchange(true, false);
    if (lossy != 0) return lossy;
    const bad = exchange(false, true);
    if (bad != 0) return bad;
    std.debug.print("quic self ok\n", .{});
    return 0;
}
