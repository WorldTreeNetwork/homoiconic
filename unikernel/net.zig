//! Virtio-net, ARP, IPv4 and UDP for the Reflect image. Bytes only.
//! A run payload is handed to `reflect_reply_bytes` unchanged.

const qsz: u16 = 8;
const buf_len: u32 = 2048;
const hdr_len: usize = 12;
const frame_len: usize = 24;
const max_dgram: usize = 1200;
const max_payload: usize = 1176;
const budget_max: u64 = 100000000;

extern fn reflect_reply_bytes(program: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64) usize;
extern fn reflect_abort_alloc(unused: usize) usize;
extern fn reflect_command_line() [*]const u8;
extern fn reflect_remote_offer(out: [*]u8, capacity: usize) usize;
extern fn reflect_remote_take(offer: [*]const u8, length: usize, out: [*]u8, capacity: usize) usize;
extern fn reflect_remote_log(out: [*]u8, capacity: usize) usize;

const Endpoint = struct {
    ip: [4]u8,
    port: u16,
    quic_port: u16,
    wire_port: u16,
    peer_ip: [4]u8,
    peer_port: u16,
    has_peer: bool,
    hook: bool,
};
const std = @import("std");
const quic_mod = @import("quic.zig");
const pvclock = @import("pvclock.zig");
var qconn: quic_mod.Conn = undefined;
var q_ready = false;
var q_wire = false;
var q_peer = false;
var q_answered = false;
var q_frame: [64]u8 = undefined;
var q_next: quic_mod.Conn = undefined;
var q_seen: u64 = 0;
const q_idle: u64 = 2_000_000_000;

export fn net_serve() noreturn {
    const ep = parse(line()) orelse halt("the network address is not valid");
    var nic = discover() orelse halt("no network device");
    var i: usize = 0;
    while (i < nic.nbars) : (i += 1) {
        if (nic.bars[i].addr < 512 * 1024 * 1024) halt("a network address overlaps memory");
        mapUncached(nic.bars[i].addr, nic.bars[i].len);
    }
    if (!bringUp(&nic, ep)) halt("the network device omitted a required feature");
    say("reflect: ready ");
    putIp(ep.ip);
    say(":");
    putDec(ep.port);
    say("\n");
    if (ep.quic_port != 0) {
        if (!startClock()) halt("no monotonic clock");
        qconn = quic_mod.Conn.openServer(rdrand64);
        q_ready = true;
        say("reflect: quic ");
        putDec(ep.quic_port);
        say("\n");
    }
    if (ep.wire_port != 0 or ep.has_peer) {
        if (!startClock()) halt("no monotonic clock");
        if (ep.wire_port != 0) {
            qconn = quic_mod.Conn.openServer(rdrand64);
            say("reflect: wire ");
            putDec(ep.wire_port);
            say("\n");
        } else {
            var pin: [32]u8 = undefined;
            std.crypto.hash.sha2.Sha256.hash(quic_mod.certificate(), &pin, .{});
            qconn = quic_mod.Conn.openClient(rdrand64, &pin);
            say("reflect: peer ");
            putIp(ep.peer_ip);
            say(":");
            putDec(ep.peer_port);
            say("\n");
        }
        q_wire = true;
    }
    while (true) {
        poll(nic, ep);
        if (q_wire) wireTick(nic, ep) else if (q_ready) quicTick(nic, ep);
    }
}

fn line() []const u8 {
    const p = reflect_command_line();
    var n: usize = 0;
    while (p[n] != 0 and n < 1023) n += 1;
    return p[0..n];
}

fn parse(s: []const u8) ?Endpoint {
    var ip: ?[4]u8 = null;
    var port: ?u16 = null;
    var hook = false;
    var quic_port: u16 = 0;
    var saw_quic = false;
    var wire_port: u16 = 0;
    var saw_wire = false;
    var peer_ip: [4]u8 = .{ 0, 0, 0, 0 };
    var peer_port: u16 = 0;
    var has_peer = false;
    var i: usize = 0;
    while (i < s.len) {
        while (i < s.len and s[i] == ' ') i += 1;
        const start = i;
        while (i < s.len and s[i] != ' ') i += 1;
        const word = s[start..i];
        if (word.len == 0) break;
        if (starts(word, "reflect.ip=")) {
            if (ip != null) return null;
            ip = parseIp(word["reflect.ip=".len..]) orelse return null;
        } else if (starts(word, "reflect.port=")) {
            if (port != null) return null;
            port = parsePort(word["reflect.port=".len..]) orelse return null;
        } else if (eql(word, "reflect.hook=alloc")) {
            if (hook) return null;
            hook = true;
        } else if (starts(word, "reflect.quic_port=")) {
            if (saw_quic) return null;
            saw_quic = true;
            quic_port = parsePort(word["reflect.quic_port=".len..]) orelse return null;
        } else if (starts(word, "reflect.wire_port=")) {
            if (saw_wire) return null;
            saw_wire = true;
            wire_port = parsePort(word["reflect.wire_port=".len..]) orelse return null;
        } else if (starts(word, "reflect.peer=")) {
            if (has_peer) return null;
            const rest = word["reflect.peer=".len..];
            var at: usize = 0;
            while (at < rest.len and rest[at] != ':') at += 1;
            if (at == rest.len) return null;
            peer_ip = parseIp(rest[0..at]) orelse return null;
            peer_port = parsePort(rest[at + 1 ..]) orelse return null;
            has_peer = true;
        } else return null;
    }
    if (wire_port != 0 and has_peer) return null;
    return .{
        .ip = ip orelse return null,
        .port = port orelse return null,
        .quic_port = quic_port,
        .wire_port = wire_port,
        .peer_ip = peer_ip,
        .peer_port = peer_port,
        .has_peer = has_peer,
        .hook = hook,
    };
}

fn parseIp(s: []const u8) ?[4]u8 {
    var out: [4]u8 = undefined;
    var n: usize = 0;
    var acc: u16 = 0;
    var digs: u8 = 0;
    for (s) |c| {
        if (c == '.') {
            if (digs == 0 or n == 3) return null;
            out[n] = @truncate(acc);
            n += 1;
            acc = 0;
            digs = 0;
        } else if (c >= '0' and c <= '9') {
            digs += 1;
            acc = acc * 10 + (c - '0');
            if (acc > 255 or digs > 3) return null;
        } else return null;
    }
    if (digs == 0 or n != 3) return null;
    out[3] = @truncate(acc);
    return out;
}

fn parsePort(s: []const u8) ?u16 {
    if (s.len == 0 or s.len > 5) return null;
    var acc: u32 = 0;
    for (s) |c| {
        if (c < '0' or c > '9') return null;
        acc = acc * 10 + (c - '0');
    }
    if (acc == 0 or acc > 65535) return null;
    return @truncate(acc);
}

fn starts(s: []const u8, p: []const u8) bool {
    return s.len >= p.len and eql(s[0..p.len], p);
}
fn eql(a: []const u8, b: []const u8) bool {
    if (a.len != b.len) return false;
    for (a, b) |x, y| if (x != y) return false;
    return true;
}

// ---- device (the spike's contract: CF8/CFC, VERSION_1 and MAC only) ----

const Bar = struct { addr: u64, len: u64 };
const Nic = struct {
    bus: u8,
    dev: u8,
    func: u8,
    bars: [6]Bar,
    nbars: usize,
    common: u64,
    notify: u64,
    notify_mul: u32,
    devcfg: u64,
    mac: [6]u8,
};

fn discover() ?Nic {
    var bus: u16 = 0;
    while (bus < 256) : (bus += 1) {
        var dev: u16 = 0;
        while (dev < 32) : (dev += 1) {
            const v = pcird(bus, dev, 0, 0);
            if (v == 0xffffffff) continue;
            const vendor: u16 = @truncate(v);
            const device: u16 = @truncate(v >> 16);
            if (vendor == 0x1af4 and device == 0x1041)
                return readNic(@truncate(bus), @truncate(dev));
        }
    }
    return null;
}

fn readNic(bus: u8, dev: u8) ?Nic {
    var nic = Nic{
        .bus = bus,
        .dev = dev,
        .func = 0,
        .bars = undefined,
        .nbars = 0,
        .common = 0,
        .notify = 0,
        .notify_mul = 0,
        .devcfg = 0,
        .mac = undefined,
    };
    var bar_i: u8 = 0;
    while (bar_i < 6) : (bar_i += 1) {
        const off: u16 = 0x10 + @as(u16, bar_i) * 4;
        const raw = pcird(bus, dev, 0, off);
        if (raw & 1 != 0) return null;
        const is64 = (raw & 0x6) == 0x4;
        var addr: u64 = raw & 0xfffffff0;
        if (is64) {
            addr |= @as(u64, pcird(bus, dev, 0, off + 4)) << 32;
            pcwr(bus, dev, 0, off + 4, 0xffffffff);
        }
        pcwr(bus, dev, 0, off, 0xffffffff);
        var mask: u64 = pcird(bus, dev, 0, off) & 0xfffffff0;
        if (is64) mask |= @as(u64, pcird(bus, dev, 0, off + 4)) << 32;
        pcwr(bus, dev, 0, off, raw);
        if (is64) pcwr(bus, dev, 0, off + 4, @truncate(addr >> 32));
        const len = if (mask == 0) 0 else (~mask +% 1);
        if (addr != 0 and len != 0) {
            nic.bars[nic.nbars] = .{ .addr = addr, .len = len };
            nic.nbars += 1;
        }
        if (is64) bar_i += 1;
    }
    const cmd = pcird(bus, dev, 0, 0x04);
    pcwr(bus, dev, 0, 0x04, (cmd & 0xffff0000) | 0x6);
    var cap: u16 = @truncate(pcird(bus, dev, 0, 0x34) & 0xfc);
    var guard: u8 = 0;
    while (cap != 0 and guard < 48) : (guard += 1) {
        const c0 = pcird(bus, dev, 0, cap);
        const id: u8 = @truncate(c0);
        const next: u16 = @truncate((c0 >> 8) & 0xfc);
        if (id == 0x09) {
            const cfg_type: u8 = @truncate(c0 >> 24);
            const bar: u8 = @truncate(pcird(bus, dev, 0, cap + 4));
            const offset = pcird(bus, dev, 0, cap + 8);
            const base = barAddr(bus, dev, bar) orelse return null;
            const mmio = base + offset;
            if (cfg_type == 1) nic.common = mmio;
            if (cfg_type == 2) {
                nic.notify = mmio;
                nic.notify_mul = pcird(bus, dev, 0, cap + 16);
            }
            if (cfg_type == 4) nic.devcfg = mmio;
        }
        cap = next;
    }
    if (nic.common == 0 or nic.notify == 0 or nic.devcfg == 0) return null;
    return nic;
}

fn barAddr(bus: u8, dev: u8, index: u8) ?u64 {
    const raw = pcird(bus, dev, 0, 0x10 + @as(u16, index) * 4);
    if (raw & 1 != 0) return null;
    var addr: u64 = raw & 0xfffffff0;
    if ((raw & 0x6) == 0x4)
        addr |= @as(u64, pcird(bus, dev, 0, 0x14 + @as(u16, index) * 4)) << 32;
    if (addr == 0) return null;
    return addr;
}

fn bringUp(nic: *Nic, _: Endpoint) bool {
    wr8(nic.common + 20, 0);
    var spin: u32 = 0;
    while (spin < 100000) : (spin += 1) {}
    wr8(nic.common + 20, 1);
    wr8(nic.common + 20, 3);
    const lo = feat(nic.*, 0);
    const hi = feat(nic.*, 1);
    if (lo & (1 << 5) == 0 or hi & 1 == 0) return false;
    setFeat(nic.*, 0, 1 << 5);
    setFeat(nic.*, 1, 1);
    wr8(nic.common + 20, 11);
    if (rd8(nic.common + 20) & 8 == 0) return false;
    var m: usize = 0;
    while (m < 6) : (m += 1) nic.mac[m] = rd8(nic.devcfg + m);
    if (rd16(nic.common + 18) < 2) return false;
    if (!setupQueue(nic.*, 0, true)) return false;
    if (!setupQueue(nic.*, 1, false)) return false;
    wr8(nic.common + 20, 15);
    return true;
}

const Desc = extern struct { addr: u64, len: u32, flags: u16, next: u16 };
const UsedElem = extern struct { id: u32, len: u32 };
const Avail = extern struct { flags: u16, idx: u16, ring: [qsz]u16, used_event: u16 };
const Used = extern struct { flags: u16, idx: u16, ring: [qsz]UsedElem, avail_event: u16 };
var rx_desc: [qsz]Desc align(16) = undefined;
var rx_avail: Avail align(2) = undefined;
var rx_used: Used align(4) = undefined;
var rx_buf: [qsz][buf_len]u8 align(16) = undefined;
var rx_last: u16 = 0;
var rx_out: u16 = 0;
var tx_desc: [qsz]Desc align(16) = undefined;
var tx_avail: Avail align(2) = undefined;
var tx_used: Used align(4) = undefined;
var tx_buf: [buf_len]u8 align(16) = undefined;
var tx_last: u16 = 0;
var reply_buf: [max_payload]u8 = undefined;

fn setupQueue(nic: Nic, q: u16, rx: bool) bool {
    wr16(nic.common + 22, q);
    const max = rd16(nic.common + 24);
    if (max < qsz or max & (max - 1) != 0) return false;
    wr16(nic.common + 24, qsz);
    const desc = if (rx) &rx_desc else &tx_desc;
    const avail = if (rx) &rx_avail else &tx_avail;
    const used = if (rx) &rx_used else &tx_used;
    @memset(@as([*]u8, @ptrCast(desc))[0..@sizeOf(@TypeOf(desc.*))], 0);
    @memset(@as([*]u8, @ptrCast(avail))[0..@sizeOf(@TypeOf(avail.*))], 0);
    @memset(@as([*]u8, @ptrCast(used))[0..@sizeOf(@TypeOf(used.*))], 0);
    wr64(nic.common + 32, @intFromPtr(desc));
    wr64(nic.common + 40, @intFromPtr(avail));
    wr64(nic.common + 48, @intFromPtr(used));
    wr16(nic.common + 28, 1);
    if (rx) {
        var n: u16 = 0;
        while (n < qsz) : (n += 1) {
            rx_desc[n] = .{ .addr = @intFromPtr(&rx_buf[n]), .len = buf_len, .flags = 2, .next = 0 };
            rx_avail.ring[n] = n;
        }
        @atomicStore(u16, &rx_avail.idx, qsz, .release);
        rx_out = qsz;
        notifyQueue(nic, 0);
    }
    return true;
}

fn notifyQueue(nic: Nic, q: u16) void {
    wr16(nic.common + 22, q);
    const off = rd16(nic.common + 30);
    const addr = nic.notify + @as(u64, off) * nic.notify_mul;
    fence();
    @as(*align(1) volatile u16, @ptrFromInt(addr)).* = q;
}

fn poll(nic: Nic, ep: Endpoint) void {
    if (@atomicLoad(u16, &rx_used.idx, .acquire) == rx_last) return;
    const slot = rx_last % qsz;
    const id = rx_used.ring[slot].id;
    const len = rx_used.ring[slot].len;
    rx_last +%= 1;
    if (rx_out == 0) return;
    rx_out -%= 1;
    if (id < qsz and len >= hdr_len + 14 and len <= buf_len)
        handle(rx_buf[id][hdr_len..@as(usize, len)], nic, ep);
    if (id < qsz) {
        rx_desc[id] = .{ .addr = @intFromPtr(&rx_buf[id]), .len = buf_len, .flags = 2, .next = 0 };
        const a = @atomicLoad(u16, &rx_avail.idx, .acquire) % qsz;
        rx_avail.ring[a] = @truncate(id);
        fence();
        _ = @atomicRmw(u16, &rx_avail.idx, .Add, 1, .release);
        rx_out +%= 1;
        notifyQueue(nic, 0);
    }
}

fn handle(frame: []u8, nic: Nic, ep: Endpoint) void {
    if (frame.len < 42) return;
    const et = be16(frame[12..14]);
    if (et == 0x0806) {
        noteArp(frame, ep);
        _ = answerArp(frame, nic, ep);
        return;
    }
    if (et != 0x0800) return;
    if (frame[14] >> 4 != 4) return;
    const ihl: usize = @as(usize, frame[14] & 0xf) * 4;
    if (ihl != 20) return;
    if (frame.len < 14 + 20 + 8) return;
    const frag = be16(frame[20..22]);
    if (frag & 0x3fff != 0) return;
    if (frame[23] != 17) return;
    if (!sumOk(frame[14..34])) return;
    if (!eq4(frame[30..34], &ep.ip)) return;
    const total = be16(frame[16..18]);
    if (total < 28 or 14 + @as(usize, total) > frame.len) return;
    const udp = 34;
    const ulen = be16(frame[udp + 4 .. udp + 6]);
    if (ulen < 8 or @as(usize, ulen) + 20 != total) return;
    const dport = be16(frame[udp + 2 .. udp + 4]);
    const got = be16(frame[udp + 6 .. udp + 8]);
    if (got != 0 and !udpOk(frame[26..34], frame[udp .. udp + ulen])) return;
    if (ep.quic_port != 0 and dport == ep.quic_port) {
        quicDatagram(frame, nic, ep);
        return;
    }
    if (ep.wire_port != 0 and dport == ep.wire_port) {
        quicDatagram(frame, nic, ep);
        return;
    }
    if (ep.has_peer and dport == 9000) {
        quicDatagram(frame, nic, ep);
        return;
    }
    if (dport != ep.port) return;
    const payload = frame[udp + 8 .. udp + ulen];
    if (payload.len > max_dgram) return;
    onDatagram(frame, payload, nic, ep);
}

fn onDatagram(frame: []const u8, payload: []const u8, nic: Nic, ep: Endpoint) void {
    if (payload.len < frame_len) return;
    if (!eql(payload[0..4], "RFL1")) return;
    if (payload[6] != 0 or payload[7] != 0) return;
    const kind = payload[4];
    const status = payload[5];
    const id = be64(payload[8..16]);
    const budget = be64(payload[16..24]);
    const body = payload[frame_len..];
    if (kind == 2 and status == 0 and budget == 0 and body.len == 0) {
        sendApp(frame, nic, ep, 3, 0, id, 0, &.{});
        return;
    }
    if (kind != 0 or status != 0) return;
    if (budget == 0 or budget > budget_max) {
        sendApp(frame, nic, ep, 1, 3, id, budget, &.{});
        return;
    }
    if (ep.hook) {
        say("reflect: allocation failure\n");
        _ = reflect_abort_alloc(0);
        halt("allocation failure");
    }
    const need = reflect_reply_bytes(body.ptr, body.len, &reply_buf, reply_buf.len, budget);
    if (need > max_payload) {
        sendApp(frame, nic, ep, 1, 2, id, budget, &.{});
        return;
    }
    sendApp(frame, nic, ep, 1, 0, id, budget, reply_buf[0..need]);
}

fn sendApp(req: []const u8, nic: Nic, ep: Endpoint, kind: u8, status: u8, id: u64, budget: u64, payload: []const u8) void {
    const total = frame_len + payload.len;
    if (total > max_dgram) return;
    var app: [max_dgram]u8 = undefined;
    @memcpy(app[0..4], "RFL1");
    app[4] = kind;
    app[5] = status;
    app[6] = 0;
    app[7] = 0;
    st64(app[8..16], id);
    st64(app[16..24], budget);
    @memcpy(app[frame_len..][0..payload.len], payload);
    sendUdp(req, nic, ep, app[0..total], ep.port);
}

fn answerArp(frame: []const u8, nic: Nic, ep: Endpoint) bool {
    if (frame.len < 42) return false;
    if (be16(frame[16..18]) != 0x0800 or frame[18] != 6 or frame[19] != 4) return false;
    if (be16(frame[20..22]) != 1) return false;
    if (!eq4(frame[38..42], &ep.ip)) return false;
    var out: [hdr_len + 42]u8 = .{0} ** (hdr_len + 42);
    const pkt = out[hdr_len..];
    @memcpy(pkt[0..6], frame[6..12]);
    @memcpy(pkt[6..12], &nic.mac);
    pkt[12] = 0x08;
    pkt[13] = 0x06;
    @memcpy(pkt[14..20], frame[14..20]);
    pkt[21] = 2;
    @memcpy(pkt[22..28], &nic.mac);
    @memcpy(pkt[28..32], &ep.ip);
    @memcpy(pkt[32..38], frame[22..28]);
    @memcpy(pkt[38..42], frame[28..32]);
    return tx(nic, &out);
}

fn quicDatagram(frame: []const u8, nic: Nic, ep: Endpoint) void {
    if (frame.len < 50) return;
    const ulen = be16(frame[38..40]);
    if (ulen < 8 or 42 + (ulen - 8) > frame.len) return;
    const payload = frame[42..][0 .. ulen - 8];
    const now = mono();
    // Nothing a datagram says is used until one of its packets opens (AEAD).
    if (qconn.recv(payload, now)) {
        // The reply address is the one the connection's first Initial came
        // from. It is not moved afterwards, by any packet.
        if (!q_peer) {
            @memcpy(q_frame[0..42], frame[0..42]);
            q_peer = true;
        }
        q_seen = now;
    } else if (qconn.server and q_peer and (q_answered or now -| q_seen >= q_idle) and
        quic_mod.newInitial(payload, &qconn.orig_dcid))
    {
        // A server connection gives way only when it has answered or has
        // opened nothing for q_idle, and only to a datagram that opens as a
        // new Initial. The candidate is built aside; if it does not open,
        // the connection in place is untouched.
        q_next = quic_mod.Conn.openServer(rdrand64);
        if (q_next.recv(payload, now)) {
            qconn = q_next;
            @memcpy(q_frame[0..42], frame[0..42]);
            q_answered = false;
            q_seen = now;
        }
    }
    if (q_wire) wirePump(nic, ep) else quicPump(nic, ep);
}

fn quicTick(nic: Nic, ep: Endpoint) void {
    quicPump(nic, ep);
}

var peer_mac: [6]u8 = .{0} ** 6;
var peer_known = false;
var wire_sent = false;
var wire_done = false;
var offer_buf: [2048]u8 = undefined;
var offer_len: usize = 0;

fn noteArp(frame: []const u8, ep: Endpoint) void {
    if (!ep.has_peer or frame.len < 42) return;
    if (be16(frame[20..22]) != 2) return;
    if (!eq4(frame[28..32], &ep.peer_ip)) return;
    @memcpy(&peer_mac, frame[22..28]);
    peer_known = true;
}

fn askArp(nic: Nic, ep: Endpoint) void {
    var out: [hdr_len + 42]u8 = .{0} ** (hdr_len + 42);
    const pkt = out[hdr_len..];
    @memset(pkt[0..6], 0xff);
    @memcpy(pkt[6..12], &nic.mac);
    pkt[12] = 0x08;
    pkt[13] = 0x06;
    pkt[14] = 0;
    pkt[15] = 1;
    pkt[16] = 0x08;
    pkt[17] = 0;
    pkt[18] = 6;
    pkt[19] = 4;
    pkt[20] = 0;
    pkt[21] = 1;
    @memcpy(pkt[22..28], &nic.mac);
    @memcpy(pkt[28..32], &ep.ip);
    @memcpy(pkt[38..42], &ep.peer_ip);
    _ = tx(nic, &out);
}

fn sendTo(nic: Nic, ep: Endpoint, dst_mac: *const [6]u8, dst_ip: *const [4]u8, dport: u16, sport: u16, payload: []const u8) void {
    const ulen: u16 = @truncate(8 + payload.len);
    const ip_len: u16 = 20 + ulen;
    const n = hdr_len + 14 + @as(usize, ip_len);
    @memset(tx_buf[0..n], 0);
    const pkt = tx_buf[hdr_len..n];
    @memcpy(pkt[0..6], dst_mac);
    @memcpy(pkt[6..12], &nic.mac);
    pkt[12] = 0x08;
    pkt[13] = 0x00;
    pkt[14] = 0x45;
    st16(pkt[16..18], ip_len);
    pkt[22] = 64;
    pkt[23] = 17;
    @memcpy(pkt[26..30], &ep.ip);
    @memcpy(pkt[30..34], dst_ip);
    st16(pkt[24..26], ipSum(pkt[14..34]));
    st16(pkt[34..36], sport);
    st16(pkt[36..38], dport);
    st16(pkt[38..40], ulen);
    @memcpy(pkt[42..][0..payload.len], payload);
    const uc = udpSum(pkt[26..34], pkt[34 .. 34 + ulen]);
    st16(pkt[40..42], if (uc == 0) 0xffff else uc);
    _ = tx(nic, tx_buf[0..n]);
}

var arp_tick: u32 = 0;
fn wireTick(nic: Nic, ep: Endpoint) void {
    arp_tick +%= 1;
    if (ep.has_peer and !peer_known and (arp_tick == 1 or arp_tick % 100000 == 0)) askArp(nic, ep);
    wirePump(nic, ep);
}

fn wirePump(nic: Nic, ep: Endpoint) void {
    if (ep.wire_port != 0) {
        if (!q_answered and qconn.peer_fin) {
            const n = reflect_remote_take(qconn.readApp().ptr, qconn.readApp().len, &answer_buf, answer_buf.len);
            if (n != 0 and n <= answer_buf.len) _ = qconn.writeApp(answer_buf[0..n]);
            q_answered = true;
        }
        var out: [1500]u8 = undefined;
        const n = qconn.send(&out, mono());
        if (n > 0 and q_peer) sendUdp(q_frame[0..42], nic, ep, out[0..n], ep.wire_port);
        return;
    }
    if (!peer_known) return;
    if (!wire_sent and qconn.accepted) {
        offer_len = reflect_remote_offer(&offer_buf, offer_buf.len);
        if (offer_len == 0 or offer_len > offer_buf.len) halt("no remote offer");
        if (!qconn.writeApp(offer_buf[0..offer_len])) halt("the offer was not sent");
        wire_sent = true;
    }
    var out: [1500]u8 = undefined;
    const n = qconn.send(&out, mono());
    if (n > 0) sendTo(nic, ep, &peer_mac, &ep.peer_ip, ep.peer_port, 9000, out[0..n]);
    if (!wire_done and qconn.peer_fin) {
        const got = qconn.readApp();
        var expect: [256]u8 = undefined;
        const want = reflect_remote_take(offer_buf[0..offer_len].ptr, offer_len, &expect, expect.len);
        if (want == got.len and eql(got, expect[0..want])) {
            say("reflect: remote ok\nreflect: log ");
            var logb: [1024]u8 = undefined;
            const ln = reflect_remote_log(&logb, logb.len);
            const show = if (ln > logb.len) logb.len else ln;
            say(logb[0..show]);
            say("\n");
        } else say("reflect: remote differs\n");
        wire_done = true;
    }
}

fn quicPump(nic: Nic, ep: Endpoint) void {
    if (!q_answered and qconn.peer_fin) {
        const reply = answerBytes(qconn.readApp(), ep);
        if (reply.len != 0) _ = qconn.writeApp(reply);
        q_answered = true;
    }
    var out: [1500]u8 = undefined;
    const n = qconn.send(&out, mono());
    if (n > 0 and q_peer) sendUdp(q_frame[0..42], nic, ep, out[0..n], ep.quic_port);
}

var answer_buf: [1200]u8 = undefined;
fn answerBytes(payload: []const u8, ep: Endpoint) []const u8 {
    if (payload.len < frame_len or payload.len > max_dgram) return "";
    if (!eql(payload[0..4], "RFL1") or payload[6] != 0 or payload[7] != 0) return "";
    const kind = payload[4];
    const status = payload[5];
    const id = be64(payload[8..16]);
    const budget = be64(payload[16..24]);
    const body = payload[frame_len..];
    if (kind == 2 and status == 0 and budget == 0 and body.len == 0) {
        return fillAnswer(3, 0, id, 0, "");
    }
    if (kind != 0 or status != 0) return "";
    if (budget == 0 or budget > budget_max) return fillAnswer(1, 3, id, budget, "");
    if (ep.hook) {
        say("reflect: allocation failure\n");
        _ = reflect_abort_alloc(0);
        halt("allocation failure");
    }
    const need = reflect_reply_bytes(body.ptr, body.len, &reply_buf, reply_buf.len, budget);
    if (need > max_payload) return fillAnswer(1, 2, id, budget, "");
    return fillAnswer(1, 0, id, budget, reply_buf[0..need]);
}

fn fillAnswer(kind: u8, status: u8, id: u64, budget: u64, payload: []const u8) []const u8 {
    const total = frame_len + payload.len;
    if (total > answer_buf.len) return "";
    @memcpy(answer_buf[0..4], "RFL1");
    answer_buf[4] = kind;
    answer_buf[5] = status;
    answer_buf[6] = 0;
    answer_buf[7] = 0;
    st64(answer_buf[8..16], id);
    st64(answer_buf[16..24], budget);
    @memcpy(answer_buf[frame_len..][0..payload.len], payload);
    return answer_buf[0..total];
}

fn sendUdp(req: []const u8, nic: Nic, ep: Endpoint, payload: []const u8, source: u16) void {
    const ulen: u16 = @truncate(8 + payload.len);
    const ip_len: u16 = 20 + ulen;
    const n = hdr_len + 14 + @as(usize, ip_len);
    @memset(tx_buf[0..n], 0);
    const pkt = tx_buf[hdr_len..n];
    @memcpy(pkt[0..6], req[6..12]);
    @memcpy(pkt[6..12], &nic.mac);
    pkt[12] = 0x08;
    pkt[13] = 0x00;
    pkt[14] = 0x45;
    st16(pkt[16..18], ip_len);
    pkt[22] = 64;
    pkt[23] = 17;
    @memcpy(pkt[26..30], &ep.ip);
    @memcpy(pkt[30..34], req[26..30]);
    st16(pkt[24..26], ipSum(pkt[14..34]));
    st16(pkt[34..36], source);
    st16(pkt[36..38], be16(req[34..36]));
    st16(pkt[38..40], ulen);
    @memcpy(pkt[42..][0..payload.len], payload);
    const uc = udpSum(pkt[26..34], pkt[34 .. 34 + ulen]);
    st16(pkt[40..42], if (uc == 0) 0xffff else uc);
    _ = tx(nic, tx_buf[0..n]);
}

fn tx(nic: Nic, bytes: []const u8) bool {
    if (bytes.len > buf_len) return false;
    if (@intFromPtr(bytes.ptr) != @intFromPtr(&tx_buf)) @memcpy(tx_buf[0..bytes.len], bytes);
    tx_desc[0] = .{ .addr = @intFromPtr(&tx_buf), .len = @truncate(bytes.len), .flags = 0, .next = 0 };
    const slot = @atomicLoad(u16, &tx_avail.idx, .unordered) % qsz;
    tx_avail.ring[slot] = 0;
    fence();
    _ = @atomicRmw(u16, &tx_avail.idx, .Add, 1, .release);
    notifyQueue(nic, 1);
    var spins: u32 = 0;
    while (@atomicLoad(u16, &tx_used.idx, .acquire) == tx_last and spins < 5_000_000) : (spins += 1) {}
    if (@atomicLoad(u16, &tx_used.idx, .acquire) == tx_last) return false;
    tx_last = @atomicLoad(u16, &tx_used.idx, .acquire);
    return true;
}

fn be16(b: []const u8) u16 {
    return (@as(u16, b[0]) << 8) | b[1];
}
fn be64(b: []const u8) u64 {
    var v: u64 = 0;
    for (b[0..8]) |c| v = (v << 8) | c;
    return v;
}
fn st16(b: []u8, v: u16) void {
    b[0] = @truncate(v >> 8);
    b[1] = @truncate(v);
}
fn st64(b: []u8, v: u64) void {
    var i: usize = 0;
    while (i < 8) : (i += 1) b[i] = @truncate(v >> @intCast(56 - 8 * i));
}
fn eq4(a: []const u8, b: *const [4]u8) bool {
    return a[0] == b[0] and a[1] == b[1] and a[2] == b[2] and a[3] == b[3];
}
fn fold(sum0: u32) u16 {
    var sum = sum0;
    while (sum >> 16 != 0) sum = (sum & 0xffff) + (sum >> 16);
    return @truncate(sum);
}
fn sumOk(bytes: []const u8) bool {
    var sum: u32 = 0;
    var i: usize = 0;
    while (i + 1 < bytes.len) : (i += 2) sum += be16(bytes[i .. i + 2]);
    if (i < bytes.len) sum += @as(u32, bytes[i]) << 8;
    const f = fold(sum);
    return f == 0 or f == 0xffff;
}
fn udpOk(addrs: []const u8, udp: []const u8) bool {
    var sum: u32 = 0;
    sum += @as(u32, be16(addrs[0..2])) + be16(addrs[2..4]) + be16(addrs[4..6]) + be16(addrs[6..8]);
    sum += 17 + @as(u32, @truncate(udp.len));
    var i: usize = 0;
    while (i + 1 < udp.len) : (i += 2) sum += be16(udp[i .. i + 2]);
    if (i < udp.len) sum += @as(u32, udp[i]) << 8;
    const f = fold(sum);
    return f == 0 or f == 0xffff;
}
fn ipSum(hdr: []const u8) u16 {
    var sum: u32 = 0;
    var i: usize = 0;
    while (i + 1 < hdr.len) : (i += 2) {
        if (i == 10) continue;
        sum += be16(hdr[i .. i + 2]);
    }
    while (sum >> 16 != 0) sum = (sum & 0xffff) + (sum >> 16);
    return @truncate(~sum);
}
fn udpSum(addrs: []const u8, udp: []const u8) u16 {
    var sum: u32 = 0;
    sum += @as(u32, be16(addrs[0..2])) + be16(addrs[2..4]) + be16(addrs[4..6]) + be16(addrs[6..8]);
    sum += 17 + @as(u32, @truncate(udp.len));
    var i: usize = 0;
    while (i + 1 < udp.len) : (i += 2) {
        if (i == 6) continue;
        sum += be16(udp[i .. i + 2]);
    }
    if (i < udp.len) sum += @as(u32, udp[i]) << 8;
    while (sum >> 16 != 0) sum = (sum & 0xffff) + (sum >> 16);
    return @truncate(~sum);
}

fn pcird(bus: u16, dev: u16, func: u16, off: u16) u32 {
    outl(0xcf8, 0x80000000 | (@as(u32, bus) << 16) | (@as(u32, dev) << 11) | (@as(u32, func) << 8) | (off & 0xfc));
    return inl(0xcfc);
}
fn pcwr(bus: u16, dev: u16, func: u16, off: u16, v: u32) void {
    outl(0xcf8, 0x80000000 | (@as(u32, bus) << 16) | (@as(u32, dev) << 11) | (@as(u32, func) << 8) | (off & 0xfc));
    outl(0xcfc, v);
}
fn feat(nic: Nic, sel: u32) u32 {
    wr32(nic.common + 0, sel);
    return rd32(nic.common + 4);
}
fn setFeat(nic: Nic, sel: u32, bits: u32) void {
    wr32(nic.common + 8, sel);
    wr32(nic.common + 12, bits);
}
fn rd8(a: u64) u8 {
    return @as(*align(1) volatile u8, @ptrFromInt(a)).*;
}
fn rd16(a: u64) u16 {
    return @as(*align(1) volatile u16, @ptrFromInt(a)).*;
}
fn rd32(a: u64) u32 {
    return @as(*align(1) volatile u32, @ptrFromInt(a)).*;
}
fn wr8(a: u64, v: u8) void {
    @as(*align(1) volatile u8, @ptrFromInt(a)).* = v;
}
fn wr16(a: u64, v: u16) void {
    @as(*align(1) volatile u16, @ptrFromInt(a)).* = v;
}
fn wr32(a: u64, v: u32) void {
    @as(*align(1) volatile u32, @ptrFromInt(a)).* = v;
}
fn wr64(a: u64, v: u64) void {
    @as(*align(1) volatile u64, @ptrFromInt(a)).* = v;
}
fn fence() void {
    asm volatile ("mfence"
        ::: .{ .memory = true });
}

var tables: [8][512]u64 align(4096) = undefined;
var tables_used: usize = 0;
fn allocTable() [*]u64 {
    if (tables_used >= tables.len) halt("the page table is full");
    @memset(&tables[tables_used], 0);
    const p: [*]u64 = &tables[tables_used];
    tables_used += 1;
    return p;
}
fn mapUncached(phys: u64, len: u64) void {
    var a = phys & ~@as(u64, 0x1f_ffff);
    const end = (phys + len + 0x1f_ffff) & ~@as(u64, 0x1f_ffff);
    while (a < end) : (a += 0x20_0000) {
        const cr3 = asm volatile ("mov %%cr3, %[o]"
            : [o] "=r" (-> u64),
        );
        const pml4: [*]u64 = @ptrFromInt(cr3 & ~@as(u64, 0xfff));
        const ix4 = (a >> 39) & 0x1ff;
        if (pml4[ix4] & 1 == 0) pml4[ix4] = @intFromPtr(allocTable()) | 0x3;
        const pdpt: [*]u64 = @ptrFromInt(pml4[ix4] & ~@as(u64, 0xfff));
        const ix3 = (a >> 30) & 0x1ff;
        if (pdpt[ix3] & 1 == 0) pdpt[ix3] = @intFromPtr(allocTable()) | 0x3;
        const pd: [*]u64 = @ptrFromInt(pdpt[ix3] & ~@as(u64, 0xfff));
        pd[(a >> 21) & 0x1ff] = a | 0x9b;
        asm volatile ("invlpg (%[p])"
            :
            : [p] "r" (a),
            : .{ .memory = true }
        );
    }
}

fn outb(port: u16, v: u8) void {
    asm volatile ("outb %[v], %[p]"
        :
        : [v] "{al}" (v),
          [p] "{dx}" (port),
    );
}
fn inb(port: u16) u8 {
    return asm volatile ("inb %[p], %[r]"
        : [r] "={al}" (-> u8),
        : [p] "{dx}" (port),
    );
}
fn outl(port: u16, v: u32) void {
    asm volatile ("outl %[v], %[p]"
        :
        : [v] "{eax}" (v),
          [p] "{dx}" (port),
    );
}
fn inl(port: u16) u32 {
    return asm volatile ("inl %[p], %[r]"
        : [r] "={eax}" (-> u32),
        : [p] "{dx}" (port),
    );
}
fn say(s: []const u8) void {
    for (s) |c| {
        while (inb(0x3f8 + 5) & 0x20 == 0) {}
        outb(0x3f8, c);
    }
}
fn putDec(v: u64) void {
    var buf: [20]u8 = undefined;
    var n = v;
    var i: usize = buf.len;
    while (true) {
        i -= 1;
        buf[i] = '0' + @as(u8, @truncate(n % 10));
        n /= 10;
        if (n == 0) break;
    }
    say(buf[i..]);
}
fn putIp(ip: [4]u8) void {
    putDec(ip[0]);
    say(".");
    putDec(ip[1]);
    say(".");
    putDec(ip[2]);
    say(".");
    putDec(ip[3]);
}
const Pvc = extern struct {
    version: u32,
    pad0: u32,
    tsc: u64,
    system_time: u64,
    mul: u32,
    shift: i8,
    flags: u8,
    pad1: [2]u8,
};
var pvc: Pvc align(64) = .{ .version = 0, .pad0 = 0, .tsc = 0, .system_time = 0, .mul = 0, .shift = 0, .flags = 0, .pad1 = .{ 0, 0 } };

fn startClock() bool {
    const id = cpuid(0x40000000, 0);
    // edx on this Cloud Hypervisor is 0x4d; ebx and ecx are the KVM signature.
    if (id.b != 0x4b4d564b or id.c != 0x564b4d56) return false;
    const leaf = cpuid(0x40000001, 0);
    if (leaf.a & (1 << 3) == 0) return false;
    const phys = @intFromPtr(&pvc);
    wrmsr(0x4b564d01, phys | 1);
    return true;
}

fn cpuid(leaf: u32, sub: u32) struct { a: u32, b: u32, c: u32, d: u32 } {
    var regs: [4]u32 = undefined;
    asm volatile (
        \\cpuid
        \\mov %%eax, 0(%[p])
        \\mov %%ebx, 4(%[p])
        \\mov %%ecx, 8(%[p])
        \\mov %%edx, 12(%[p])
        :
        : [p] "r" (&regs),
          [l] "{eax}" (leaf),
          [s] "{ecx}" (sub),
        : .{ .eax = true, .ebx = true, .ecx = true, .edx = true, .memory = true }
    );
    return .{ .a = regs[0], .b = regs[1], .c = regs[2], .d = regs[3] };
}

fn wrmsr(msr: u32, v: u64) void {
    asm volatile ("wrmsr"
        :
        : [c] "{ecx}" (msr),
          [a] "{eax}" (@as(u32, @truncate(v))),
          [d] "{edx}" (@as(u32, @truncate(v >> 32))),
    );
}

fn rdtsc() u64 {
    var lo: u32 = undefined;
    var hi: u32 = undefined;
    asm volatile ("rdtsc"
        : [lo] "={eax}" (lo),
          [hi] "={edx}" (hi),
    );
    return (@as(u64, hi) << 32) | lo;
}

var mono_last: u64 = 0;

/// Nanoseconds from the paravirtual clock. It never goes backwards: the
/// scaling keeps the 128-bit product (pvclock.zig), and a record that the
/// hypervisor moved back is held at the last value returned.
fn mono() u64 {
    const p: *volatile Pvc = &pvc;
    while (true) {
        const v1 = p.version;
        if (v1 & 1 != 0) continue;
        const tsc = p.tsc;
        const sys = p.system_time;
        const mul = p.mul;
        const shift = p.shift;
        const t = rdtsc();
        if (p.version != v1) continue;
        const now = pvclock.nanos(sys, t -% tsc, mul, shift);
        if (now > mono_last) mono_last = now;
        return mono_last;
    }
}

fn rdrand64() u64 {
    var v: u64 = undefined;
    var ok: u8 = 0;
    while (ok == 0) {
        asm volatile ("rdrand %[v]"
            : [v] "={rax}" (v),
              [ok] "={@ccc}" (ok),
        );
    }
    return v;
}

fn halt(why: []const u8) noreturn {
    say("reflect: ");
    say(why);
    say("\n");
    outb(0x600, 0x34);
    while (true) asm volatile ("hlt");
}
