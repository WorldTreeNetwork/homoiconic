//! Which first flights a serving guest takes, and where it keeps them.
//! Twelve server connections in two pools: four for first flights that show
//! nothing, eight for first flights that answered a Retry, at most one
//! handshake in progress there per IPv4 address. Nothing is evicted. When
//! the first pool is full, a first flight that opens is answered with a
//! Retry and nothing is kept. A connection leaves its slot by its own end,
//! or 2 seconds after its first Initial if it is not accepted by then.
//! (`openspec/changes/add-quic-admission/design.md`)

const std = @import("std");
const quic = @import("quic.zig");
const entity = @import("entity.zig");

pub const first_slots: usize = 4;
pub const address_slots: usize = 8;
pub const slots: usize = first_slots + address_slots;
/// From the first Initial that opened to an accepted handshake. Nothing a
/// peer sends extends it.
pub const cap: u64 = 2_000_000_000;
/// An accepted connection with nothing in flight and nothing opened.
pub const idle: u64 = 2_000_000_000;

pub const Addr = struct { ip: [4]u8, port: u16 };

pub const Slot = struct {
    used: bool = false,
    conn: quic.Conn = undefined,
    /// The address and port its first Initial came from; it takes
    /// datagrams from there only.
    from: Addr = .{ .ip = .{ 0, 0, 0, 0 }, .port = 0 },
    /// When its first Initial opened, moved on by the guest's own runs.
    born: u64 = 0,
    /// When a packet last opened on it.
    seen: u64 = 0,
    /// The guest has taken its stream and answered it.
    answered: bool = false,
};

/// What became of a datagram: given to slot `i` (`fresh` when it started
/// that connection), answered by the Retry in `Table.retry[0..n]`, or
/// nothing.
pub const Got = union(enum) {
    none,
    slot: struct { i: usize, fresh: bool },
    retry: usize,
};

pub const Table = struct {
    slot: [slots]Slot = [_]Slot{.{}} ** slots,
    /// The key Retry tokens are made under: random, made with the table,
    /// never sent and never kept across boots.
    key: [32]u8 = .{0} ** 32,
    rand: *const fn () u64 = undefined,
    id: *const entity.Identity = undefined,
    allow: *const entity.Allow = undefined,
    retry: [71]u8 = undefined,

    pub fn init(t: *Table, rand: *const fn () u64, id: *const entity.Identity, allow: *const entity.Allow) void {
        for (&t.slot) |*s| s.used = false;
        t.rand = rand;
        t.id = id;
        t.allow = allow;
        var i: usize = 0;
        while (i < 4) : (i += 1) std.mem.writeInt(u64, t.key[i * 8 ..][0..8], rand(), .little);
    }

    /// Take one datagram from `from`.
    pub fn take(t: *Table, from: Addr, dgram: []const u8, now: u64) Got {
        const id = quic.dcidOf(dgram) orelse return .none;
        for (&t.slot, 0..) |*s, i| {
            if (!s.used) continue;
            if (!std.mem.eql(u8, id, &s.conn.local_cid) and !std.mem.eql(u8, id, &s.conn.orig_dcid)) continue;
            // A connection takes datagrams from its own address and port.
            // From anywhere else this one starts nothing either.
            if (!same(s.from, from)) return .none;
            if (!s.conn.recv(dgram, now)) return .none;
            s.seen = now;
            return .{ .slot = .{ .i = i, .fresh = false } };
        }
        if (!quic.firstShape(dgram)) return .none;
        if (quic.tokenCheck(dgram, &t.key, &from.ip, from.port, now)) |odcid| {
            // The address is shown: an address slot, one handshake in
            // progress per IPv4 address, else a first-flight slot.
            var at: ?usize = null;
            if (!t.addressBusy(from.ip)) at = t.free(first_slots, slots);
            if (at == null) at = t.free(0, first_slots);
            const i = at orelse return .none;
            return t.open(i, from, dgram, now, odcid);
        }
        if (t.free(0, first_slots)) |i| return t.open(i, from, dgram, now, null);
        // The first pool is full: a Retry, for an Initial that opens, and
        // nothing kept.
        if (!quic.initialOpens(dgram)) return .none;
        return .{ .retry = quic.makeRetry(&t.retry, dgram, &t.key, &from.ip, from.port, now, t.rand) };
    }

    /// Free the slots whose connections are done: refused; not accepted
    /// `cap` after their first Initial; answered with nothing left in
    /// flight; or accepted, nothing in flight and nothing opened for `idle`.
    pub fn sweep(t: *Table, now: u64) void {
        for (&t.slot) |*s| {
            if (!s.used) continue;
            const c = &s.conn;
            if (c.refused) {
                s.used = false;
            } else if (!c.accepted) {
                if (now -| s.born >= cap) s.used = false;
            } else if (!c.flightOn(2)) {
                if ((s.answered and !c.ack_due[2]) or now -| s.seen >= idle) s.used = false;
            }
        }
    }

    /// The guest spent `d` in a run of its own: no handshake waiting
    /// behind it is charged for that time.
    pub fn pause(t: *Table, d: u64) void {
        for (&t.slot) |*s| {
            if (s.used and !s.conn.accepted) s.born +|= d;
        }
    }

    /// How many slots of `[lo, hi)` are held.
    pub fn held(t: *const Table, lo: usize, hi: usize) usize {
        var n: usize = 0;
        for (t.slot[lo..hi]) |s| {
            if (s.used) n += 1;
        }
        return n;
    }

    fn addressBusy(t: *const Table, ip: [4]u8) bool {
        for (t.slot[first_slots..]) |s| {
            if (s.used and !s.conn.accepted and !s.conn.refused and std.mem.eql(u8, &s.from.ip, &ip)) return true;
        }
        return false;
    }

    fn free(t: *const Table, lo: usize, hi: usize) ?usize {
        var i = lo;
        while (i < hi) : (i += 1) {
            if (!t.slot[i].used) return i;
        }
        return null;
    }

    /// A server connection in free slot `i`; it holds the slot only if the
    /// datagram opens on it. With a token's first destination ID it is
    /// validated and names the Retry in its transport parameters.
    fn open(t: *Table, i: usize, from: Addr, dgram: []const u8, now: u64, odcid: ?[8]u8) Got {
        const s = &t.slot[i];
        s.conn = quic.Conn.openServer(t.rand, t.id, t.allow);
        if (odcid) |o| {
            s.conn.validated = true;
            s.conn.retried = true;
            s.conn.tp_odcid = o;
        }
        if (!s.conn.recv(dgram, now)) return .none;
        s.used = true;
        s.from = from;
        s.born = now;
        s.seen = now;
        s.answered = false;
        return .{ .slot = .{ .i = i, .fresh = true } };
    }
};

fn same(a: Addr, b: Addr) bool {
    return a.port == b.port and std.mem.eql(u8, &a.ip, &b.ip);
}
