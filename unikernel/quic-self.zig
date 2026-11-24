//! In-process QUIC: a clean exchange, a lossy reordered exchange, a wrong pin,
//! and exchanges with garbage datagrams given to both ends at every step.
//! Then the entity name against identikey's vector, base58 both ways, and an
//! end that breaks each rule of the handshake in turn: the other end must
//! refuse it. The seeds here are test input; nothing accepts their names
//! without being given them.
//! Then what a server sends and stops sending: an acknowledgement in one
//! packet number space leaves the flight of another, a first flight nobody
//! follows is answered with at most three times its bytes and in datagrams
//! of at least 1200 bytes, a reply the client acknowledges is sent once, and
//! a reply nobody acknowledges is given up.
const std = @import("std");
const quic = @import("quic.zig");
const entity = @import("entity.zig");

/// The client's and the server's keys, a third key, and what each end allows.
var cid: entity.Identity = undefined;
var sid: entity.Identity = undefined;
var other: entity.Identity = undefined;
var allow_s: entity.Allow = .{}; // the client's list: the server
var allow_c: entity.Allow = .{}; // the server's list: the client
var allow_o: entity.Allow = .{}; // a list with only the third key

fn seeded() [32]u8 {
    var s: [32]u8 = undefined;
    for (&s) |*b| b.* = @truncate(rnd() >> 24);
    return s;
}
fn keys() bool {
    cid = entity.identity(&seeded()) orelse return false;
    sid = entity.identity(&seeded()) orelse return false;
    other = entity.identity(&seeded()) orelse return false;
    return allow_s.add(&sid.name) and allow_c.add(&cid.name) and allow_o.add(&other.name);
}

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
    var client = quic.Conn.openClient(rnd, &cid, if (wrong) &allow_o else &allow_s);
    var server = quic.Conn.openServer(rnd, &sid, &allow_c);
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
            const was = client.peer_cid;
            if (!noise(server, now) or !noise(client, now)) return 10;
            // The client names the server by an ID from a packet that opened.
            if (!std.mem.eql(u8, &was, &client.peer_cid)) return 11;
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
    var client = quic.Conn.openClient(rnd, &cid, &allow_s);
    var server = quic.Conn.openServer(rnd, &sid, &allow_c);
    var first: [1500]u8 = undefined;
    const n = client.send(&first, 1);
    if (n < 1200) return false;
    if (server.recv(first[0..1199], 1)) return false;
    if (!server.recv(first[0..n], 1)) return false;
    return true;
}

const ms: u64 = 1_000_000;

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
    var client = quic.Conn.openClient(rnd, &cid, &allow_s);
    var server = quic.Conn.openServer(rnd, &sid, &allow_c);
    var a: [1500]u8 = undefined;
    var d: [1500]u8 = undefined;
    const a0 = client.send(&a, 0);
    if (a0 == 0 or !server.recv(a[0..a0], 0)) return 20;
    // The client resends before the answer comes, and the resend is lost:
    // the answer acknowledges packet 0, a copy of the client's flight, which
    // is then done. The client acknowledges the server's Initial in an
    // Initial of its own, padded to 1200 bytes, which asks for nothing back.
    var lost: [1500]u8 = undefined;
    if (client.send(&lost, 50 * ms) == 0) return 20;
    const dn = server.send(&d, 50 * ms);
    const cut = firstLen(d[0..dn]) orelse return 20;
    if (cut >= dn) return 20; // Initial and Handshake left in one datagram
    if (!client.recv(d[0..cut], 50 * ms)) return 20;
    const a2 = client.send(&a, 140 * ms);
    if (a2 < quic.min_initial or a[0] & 0xf0 != 0xc0 or firstLen(a[0..a2]) != a2) return 20; // one Initial
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
    var client = quic.Conn.openClient(rnd, &cid, &allow_s);
    var server = quic.Conn.openServer(rnd, &sid, &allow_c);
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
        // Every datagram with the Initial flight is 1200 bytes or more.
        if (n != 0 and n < quic.min_initial) return 29;
    }
    if (sends < 2) return 23; // it does resend to a client that may have lost the flight
    if (total > quic.amplification * a0) return 24;
    const a1 = client.send(&a, now);
    if (a1 == 0 or !server.recv(a[0..a1], now)) return 25;
    const n = server.send(&d, now);
    if (n == 0 or !client.recv(d[0..n], now)) return 25;
    return drive(&client, &server, now, false, false, false);
}

/// The client acknowledges the reply in a packet of its own, once, and the
/// server sends nothing more.
fn acknowledged() u8 {
    var client = quic.Conn.openClient(rnd, &cid, &allow_s);
    var server = quic.Conn.openServer(rnd, &sid, &allow_c);
    const done = drive(&client, &server, 0, false, false, false);
    if (done != 0) return done;
    var d: [1500]u8 = undefined;
    const a = client.send(&d, 10_000 * ms);
    if (a == 0 or d[0] & 0x80 != 0) return 30; // a 1-RTT acknowledgement
    if (!server.recv(d[0..a], 10_000 * ms)) return 30;
    var now: u64 = 10_000 * ms;
    while (now < 130_000 * ms) : (now += 10 * ms) {
        if (client.send(&d, now) != 0) return 31; // one acknowledgement, not answered
        if (server.send(&d, now) != 0) return 32; // the reply is not sent again
    }
    return 0;
}

/// The client never acknowledges the reply: its acknowledgement is lost. The
/// server resends it and then gives it up; the client acknowledged once and
/// is silent since.
fn givesUp() u8 {
    var client = quic.Conn.openClient(rnd, &cid, &allow_s);
    var server = quic.Conn.openServer(rnd, &sid, &allow_c);
    const done = drive(&client, &server, 0, false, false, false);
    if (done != 0) return done;
    var d: [1500]u8 = undefined;
    if (client.send(&d, 10_000 * ms) == 0) return 26; // lost
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

/// The name is identikey's: the fixture seed of identikey-protocol, its
/// public key, and the fingerprint identikey's own code printed for it.
fn vector() bool {
    const seed = [_]u8{0x11} ** 32;
    const id = entity.identity(&seed) orelse return false;
    var want: [32]u8 = undefined;
    _ = std.fmt.hexToBytes(&want, "d04ab232742bb4ab3a1368bd4615e4e6d0224ab71a016baf8520a332c9778737") catch return false;
    if (!std.mem.eql(u8, &id.public, &want)) return false;
    return std.mem.eql(u8, entity.text(&id.name).slice(), "6mUFfKo4KPLqjeAVqthhCZB82jgWjbo3RPJAAWdTynq1");
}

fn base58() bool {
    const zero = [_]u8{0} ** 32;
    const full = [_]u8{0xff} ** 32;
    var low = zero;
    low[31] = 1;
    const names = [_]entity.Name{ cid.name, sid.name, other.name, zero, full, low };
    for (names) |n| {
        const txt = entity.text(&n);
        const back = entity.parse(txt.slice()) orelse return false;
        if (!std.mem.eql(u8, &back, &n)) return false;
    }
    if (!std.mem.eql(u8, entity.text(&zero).slice(), "1" ** 32)) return false;
    const good = entity.text(&full);
    var buf: [48]u8 = undefined;
    // A leading `1` fewer is 31 bytes; one character more or a leading `1`
    // more is a 33rd byte; `0` is not in the alphabet.
    const short = entity.text(&low);
    if (entity.parse(short.slice()[1..]) != null) return false;
    @memcpy(buf[0..good.len], good.slice());
    buf[good.len] = '2';
    if (entity.parse(buf[0 .. good.len + 1]) != null) return false;
    buf[0] = '1';
    @memcpy(buf[1..][0..good.len], good.slice());
    if (entity.parse(buf[0 .. good.len + 1]) != null) return false;
    @memcpy(buf[0..good.len], good.slice());
    buf[3] = '0';
    if (entity.parse(buf[0..good.len]) != null) return false;
    if (entity.parse("") != null or entity.parse("1" ** 31) != null or entity.parse("1" ** 33) != null) return false;
    // A list: one to eight names, none twice.
    var list: [100]u8 = undefined;
    const a = entity.text(&cid.name);
    const b = entity.text(&sid.name);
    @memcpy(list[0..a.len], a.slice());
    list[a.len] = ',';
    @memcpy(list[a.len + 1 ..][0..b.len], b.slice());
    const two = entity.Allow.parseList(list[0 .. a.len + 1 + b.len]) orelse return false;
    if (two.n != 2 or !two.has(&cid.name) or !two.has(&sid.name) or two.has(&other.name)) return false;
    @memcpy(list[a.len + 1 ..][0..a.len], a.slice());
    if (entity.Allow.parseList(list[0 .. 2 * a.len + 1]) != null) return false; // twice
    if (entity.Allow.parseList(list[0 .. a.len + 1]) != null) return false; // an empty name
    if (entity.Allow.parseList("") != null) return false;
    return true;
}

/// An end that breaks one rule. `s_` cases are the server's fault, checked
/// by the client; the others are the client's, checked by the server.
const Case = enum {
    wrong_pin,
    denied,
    s_signer,
    c_signer,
    s_hash,
    c_hash,
    only_finished,
    s_finished,
    c_finished,
    empty_certificate,
    s_two,
    c_two,
    s_context,
    c_context,
    s_extensions,
    c_extensions,
    s_prefix,
    c_prefix,
    s_scheme,
    c_scheme,
    s_length,
    c_length,
    s_trailer,
    c_trailer,
    no_request,
};
var case: Case = .wrong_pin;

fn tamper(_: *const quic.Conn, kind: u8, buf: []u8, len: usize) ?usize {
    switch (case) {
        .s_hash, .c_hash => if (kind == quic.tamper_hash) {
            buf[0] ^= 1;
        },
        .s_finished, .c_finished => if (kind == 20) {
            buf[0] ^= 1;
        },
        .only_finished => if (kind == 11 or kind == 15) return null,
        .empty_certificate => {
            if (kind == 15) return null;
            if (kind == 11) {
                @memset(buf[0..4], 0);
                return 4;
            }
        },
        .s_two, .c_two => if (kind == 11) {
            @memcpy(buf[53..102], buf[4..53]);
            buf[3] = 98;
            return 102;
        },
        .s_context, .c_context => if (kind == 11) {
            std.mem.copyBackwards(u8, buf[2 .. len + 1], buf[1..len]);
            buf[0] = 1;
            buf[1] = 0xaa;
            return len + 1;
        },
        .s_extensions, .c_extensions => if (kind == 11) {
            buf[52] = 4;
            @memset(buf[53..57], 0);
            buf[3] = 53;
            return 57;
        },
        .s_prefix, .c_prefix => if (kind == 11) {
            buf[7 + 11] = 1;
        },
        .s_scheme, .c_scheme => if (kind == 15) {
            buf[0] = 0x04;
            buf[1] = 0x03;
        },
        .s_length, .c_length => if (kind == 15) {
            buf[3] = 65;
            buf[68] = 0;
            return 69;
        },
        .s_trailer, .c_trailer => if (kind == quic.tamper_trailer) {
            buf[0] = 4;
            @memset(buf[1..4], 0);
            return 4;
        },
        .no_request => if (kind == 13) return null,
        else => {},
    }
    return len;
}

/// Run one faulty handshake. True when the end that checks refused, said
/// nothing after, and no application byte was read on either end.
fn refuses(which: Case) bool {
    case = which;
    const by_client = switch (which) {
        .wrong_pin, .s_signer, .s_hash, .s_finished, .s_two, .s_context, .s_extensions, .s_prefix, .s_scheme, .s_length, .s_trailer, .no_request => true,
        else => false,
    };
    var client = quic.Conn.openClient(rnd, &cid, if (which == .wrong_pin) &allow_o else &allow_s);
    var server = quic.Conn.openServer(rnd, &sid, if (which == .denied) &allow_o else &allow_c);
    if (which == .s_signer) server.signer = &other;
    if (which == .c_signer) client.signer = &other;
    if (which != .wrong_pin and which != .denied and which != .s_signer and which != .c_signer) {
        if (by_client) server.tamper = tamper else client.tamper = tamper;
    }
    var now: u64 = 0;
    var n: usize = 0;
    var a: [1500]u8 = undefined;
    var d: [1500]u8 = undefined;
    while (n < 60) : (n += 1) {
        const cn = client.send(&a, now);
        if (cn > 0) _ = server.recv(a[0..cn], now);
        const sn = server.send(&d, now);
        if (sn > 0) _ = client.recv(d[0..sn], now);
        if (client.accepted and !client.app_tx_on) _ = client.writeApp("program-bytes");
        if (server.accepted and !server.app_tx_on) _ = server.writeApp("reply-bytes");
        now += 30 * ms;
    }
    if (server.readApp().len != 0 or client.readApp().len != 0) return false;
    if (server.peer_fin or client.peer_fin) return false;
    if (by_client) {
        if (!client.refused or client.accepted or client.app_tx_on) return false;
        if (client.send(&a, now) != 0) return false;
    } else {
        if (!server.refused or server.accepted or server.app_keys) return false;
        if (server.send(&d, now) != 0) return false;
    }
    return true;
}

/// A STREAM frame with FIN beside the CRYPTO frame of a flight that goes in
/// an Initial or a Handshake packet. The packet must count as not opened.
fn early() bool {
    var a: [1500]u8 = undefined;
    var d: [1500]u8 = undefined;
    // In a client's Initial: the server starts nothing.
    {
        var client = quic.Conn.openClient(rnd, &cid, &allow_s);
        var server = quic.Conn.openServer(rnd, &sid, &allow_c);
        if (!client.earlyStream(0, "program-bytes")) return false;
        const n = client.send(&a, 0);
        if (n == 0 or server.recv(a[0..n], 0)) return false;
        if (server.peer_fin or server.readApp().len != 0 or server.send(&d, 0) != 0) return false;
    }
    // In a server's Initial, and in a server's Handshake packet.
    var space: usize = 0;
    while (space < 2) : (space += 1) {
        var client = quic.Conn.openClient(rnd, &cid, &allow_s);
        var server = quic.Conn.openServer(rnd, &sid, &allow_c);
        const n = client.send(&a, 0);
        if (n == 0 or !server.recv(a[0..n], 0)) return false;
        if (!server.earlyStream(space, "reply-bytes")) return false;
        const m = server.send(&d, 0);
        if (m == 0) return false;
        // With the Initial dropped the Handshake packet has no keys to open
        // under; with the Handshake packet dropped the Initial still opens.
        if (client.recv(d[0..m], 0) != (space == 1)) return false;
        if (client.peer_fin or client.readApp().len != 0 or client.accepted) return false;
        if (client.rx_any[space]) return false;
    }
    // In a client's Handshake packet: the server is not validated by it.
    {
        var client = quic.Conn.openClient(rnd, &cid, &allow_s);
        var server = quic.Conn.openServer(rnd, &sid, &allow_c);
        var n = client.send(&a, 0);
        if (n == 0 or !server.recv(a[0..n], 0)) return false;
        const m = server.send(&d, 0);
        if (m == 0 or !client.recv(d[0..m], 0) or !client.accepted) return false;
        if (!client.earlyStream(1, "program-bytes")) return false;
        n = client.send(&a, 0);
        if (n == 0 or server.recv(a[0..n], 0)) return false;
        if (server.validated or server.accepted or server.peer_fin or server.readApp().len != 0) return false;
    }
    return true;
}

/// A client whose handshake the server refuses sees its flights given up.
fn givenUp() bool {
    var client = quic.Conn.openClient(rnd, &cid, &allow_s);
    var server = quic.Conn.openServer(rnd, &sid, &allow_o);
    var a: [1500]u8 = undefined;
    var d: [1500]u8 = undefined;
    var now: u64 = 0;
    var at: u64 = 0;
    while (now < 20_000 * ms) : (now += 10 * ms) {
        const cn = client.send(&a, now);
        if (cn > 0) _ = server.recv(a[0..cn], now);
        const sn = server.send(&d, now);
        if (sn > 0) _ = client.recv(d[0..sn], now);
        if (client.accepted and !client.app_tx_on) _ = client.writeApp("program-bytes");
        if (at == 0 and client.gaveUp(now)) at = now;
    }
    // Ten sends over 6.36 s and the last wait of 1.28 s.
    return client.accepted and server.refused and at > 6_000 * ms and at < 9_000 * ms;
}

/// `quic-self` runs everything. `quic-self <code>` runs the one refusal
/// with that exit code (42 to 66) or the early stream data (68) alone, so a
/// control can show each of them failing.
pub fn main(init: std.process.Init.Minimal) u8 {
    if (!quic.rfcInitialKey()) return 1;
    if (!keys()) return 2;
    const v = init.args.vector;
    if (v.len > 1) {
        const code = std.fmt.parseInt(u8, std.mem.span(v[1]), 10) catch return 2;
        if (code == 68) return if (early()) 0 else 68;
        if (code < 42 or code - 42 >= @typeInfo(Case).@"enum".fields.len) return 2;
        return if (refuses(@enumFromInt(code - 42))) 0 else code;
    }
    if (!vector()) return 40;
    if (!base58()) return 41;
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
    const once = acknowledged();
    if (once != 0) return once;
    const quiet = givesUp();
    if (quiet != 0) return quiet;
    inline for (@typeInfo(Case).@"enum".fields, 0..) |f, i| {
        if (!refuses(@enumFromInt(f.value))) return 42 + @as(u8, i);
    }
    if (!early()) return 68; // stream data before the handshake
    if (!givenUp()) return 69;
    std.debug.print("quic self ok\n", .{});
    return 0;
}
