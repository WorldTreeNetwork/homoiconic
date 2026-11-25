//! Outside a guest: check two guests' records against a program's bytes, with
//! the Lean the guests link. Zig reads the files and prints what Lean answers.
//!
//!   cross-check check <program-bytes> <record-a> <record-b>
//!   cross-check reseal <record>
//!   cross-check sign <key-file> <record>
//!
//! `check` exits 0 when the answer starts `accepted`, 1 otherwise. `<record-a>`
//! is the record of the guest that was given the program. A record starts
//! with `sig <public key> <signature>`, both hex: an Ed25519 signature over
//! every byte after that line. This program checks it, and that the record's
//! `me` line is the entity name of that key, before Lean sees the record; the
//! kernel never sees the line. A record with no such line is refused.
//!
//! `reseal` writes a record, with or without a `sig` line, with its chain and
//! head made again from its entries and no signature. `sign` writes a record
//! signed with the key in a file. Together they make what a guest that lies
//! would hand over; the wire check uses them.

const std = @import("std");
const entity = @import("entity.zig");
const Ed = std.crypto.sign.Ed25519;

extern fn open(path: [*:0]const u8, flags: c_int) c_int;
extern fn read(fd: c_int, buf: [*]u8, n: usize) isize;
extern fn write(fd: c_int, buf: [*]const u8, n: usize) isize;
extern fn close(fd: c_int) c_int;

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_cross_check(program: [*]const u8, length: usize, a: [*]const u8, a_len: usize, b: [*]const u8, b_len: usize, out: [*]u8, capacity: usize) usize;
extern fn reflect_cross_reseal(record: [*]const u8, length: usize, out: [*]u8, capacity: usize) usize;

export fn initialize_libuv() void {}

var program: [1 << 20]u8 = undefined;
var rec_a: [1 << 24]u8 = undefined;
var rec_b: [1 << 24]u8 = undefined;
var out: [1 << 26]u8 = undefined;

pub fn main(init: std.process.Init.Minimal) u8 {
    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0) return 2;
    const v = init.args.vector;
    if (v.len < 2) return usage();
    const cmd = std.mem.span(v[1]);
    if (std.mem.eql(u8, cmd, "check")) {
        if (v.len != 5) return usage();
        const pn = readFile(std.mem.span(v[2]), &program) orelse return 2;
        const an = readFile(std.mem.span(v[3]), &rec_a) orelse return 2;
        const bn = readFile(std.mem.span(v[4]), &rec_b) orelse return 2;
        const a = signed("a", rec_a[0..an]) orelse return 1;
        const b = signed("b", rec_b[0..bn]) orelse return 1;
        const need = reflect_cross_check(program[0..pn].ptr, pn, a.ptr, a.len, b.ptr, b.len, &out, out.len);
        if (need > out.len) return 2;
        writeAll(out[0..need]);
        return if (std.mem.startsWith(u8, out[0..need], "accepted\n")) 0 else 1;
    }
    if (std.mem.eql(u8, cmd, "reseal")) {
        if (v.len != 3) return usage();
        const an = readFile(std.mem.span(v[2]), &rec_a) orelse return 2;
        const body = unsigned(rec_a[0..an]);
        const need = reflect_cross_reseal(body.ptr, body.len, &out, out.len);
        if (need > out.len) return 2;
        writeAll(out[0..need]);
        return 0;
    }
    if (std.mem.eql(u8, cmd, "sign")) {
        if (v.len != 4) return usage();
        var seed: [32]u8 = undefined;
        if ((readFile(std.mem.span(v[2]), &seed) orelse return 2) != 32) return 2;
        const id = entity.identity(&seed) orelse return 2;
        const an = readFile(std.mem.span(v[3]), &rec_a) orelse return 2;
        const body = unsigned(rec_a[0..an]);
        const sig = id.pair.sign(body, null) catch return 2;
        writeAll("sig ");
        writeHex(&id.public);
        writeAll(" ");
        writeHex(&sig.toBytes());
        writeAll("\n");
        writeAll(body);
        return 0;
    }
    return usage();
}

/// The record after its `sig` line, or as it stands when it has none.
fn unsigned(record: []const u8) []const u8 {
    if (!std.mem.startsWith(u8, record, "sig ")) return record;
    const nl = std.mem.indexOfScalar(u8, record, '\n') orelse return record;
    return record[nl + 1 ..];
}

fn refuse(who: []const u8, why: []const u8) ?[]const u8 {
    writeAll("refused: record ");
    writeAll(who);
    writeAll(": ");
    writeAll(why);
    writeAll("\n");
    return null;
}

/// The record's text, when its first line is a good signature over the rest
/// by the entity its `me` line names. Says why and gives nothing otherwise.
fn signed(who: []const u8, record: []const u8) ?[]const u8 {
    if (!std.mem.startsWith(u8, record, "sig ")) return refuse(who, "it is not signed");
    const nl = std.mem.indexOfScalar(u8, record, '\n') orelse return refuse(who, "it is not signed");
    const line = record["sig ".len..nl];
    if (line.len != 64 + 1 + 128 or line[64] != ' ') return refuse(who, "the signature is not valid");
    var public: [32]u8 = undefined;
    var sig_bytes: [64]u8 = undefined;
    _ = std.fmt.hexToBytes(&public, line[0..64]) catch return refuse(who, "the signature is not valid");
    _ = std.fmt.hexToBytes(&sig_bytes, line[65..]) catch return refuse(who, "the signature is not valid");
    const body = record[nl + 1 ..];
    const key = Ed.PublicKey.fromBytes(public) catch return refuse(who, "the signature is not valid");
    Ed.Signature.fromBytes(sig_bytes).verify(body, key) catch return refuse(who, "the signature is not valid");
    // The key that signed is the entity the record says it is: its `me`
    // line, after the `form` line of a record of form 2.
    const name = entity.text(&entity.nameOf(&public));
    var want: [3 + entity.text_max + 1]u8 = undefined;
    @memcpy(want[0..3], "me ");
    @memcpy(want[3..][0..name.len], name.slice());
    want[3 + name.len] = '\n';
    const rest = if (std.mem.startsWith(u8, body, "form 2\n")) body["form 2\n".len..] else body;
    if (!std.mem.startsWith(u8, rest, want[0 .. 4 + name.len])) return refuse(who, "it is not signed by the entity it names");
    return body;
}

fn writeHex(bytes: []const u8) void {
    const digits = "0123456789abcdef";
    for (bytes) |b| writeAll(&[2]u8{ digits[b >> 4], digits[b & 0xf] });
}

fn usage() u8 {
    std.debug.print("usage: cross-check check <program-bytes> <record-a> <record-b> | cross-check reseal <record> | cross-check sign <key-file> <record>\n", .{});
    return 2;
}
fn readFile(path: []const u8, buf: []u8) ?usize {
    var z: [4096:0]u8 = undefined;
    if (path.len >= z.len) return null;
    @memcpy(z[0..path.len], path);
    z[path.len] = 0;
    const fd = open(&z, 0);
    if (fd < 0) return null;
    defer _ = close(fd);
    var n: usize = 0;
    while (n < buf.len) {
        const got = read(fd, buf[n..].ptr, buf.len - n);
        if (got < 0) return null;
        if (got == 0) break;
        n += @intCast(got);
    }
    return n;
}
fn writeAll(b: []const u8) void {
    var at: usize = 0;
    while (at < b.len) {
        const n = write(1, b[at..].ptr, b.len - at);
        if (n <= 0) return;
        at += @intCast(n);
    }
}
