const std = @import("std");

const Ed25519 = std.crypto.sign.Ed25519;

const usage = "usage: sign <seed-hex> <file>\n";

fn fail(comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(format, args);
    std.process.exit(2);
}

fn hexByte(c: u8) ?u8 {
    return switch (c) {
        '0'...'9' => c - '0',
        'a'...'f' => c - 'a' + 10,
        'A'...'F' => c - 'A' + 10,
        else => null,
    };
}

/// Print `sig <public key> <signature>` for the file, under a 32-byte seed.
/// The host's check (`sig.zig`) accepts that line and hands the file to the kernel.
pub fn main(init: std.process.Init) void {
    const arena = init.arena.allocator();
    const io = init.io;
    const args = init.minimal.args.toSlice(arena) catch fail("sign: out of memory\n", .{});
    if (args.len != 3) fail("{s}", .{usage});
    const seed_hex = args[1];
    if (seed_hex.len != Ed25519.KeyPair.seed_length * 2) fail("sign: the seed is 32 bytes\n", .{});
    var seed: [Ed25519.KeyPair.seed_length]u8 = undefined;
    for (&seed, 0..) |*b, i| {
        const hi = hexByte(seed_hex[i * 2]) orelse fail("sign: the seed is 32 bytes\n", .{});
        const lo = hexByte(seed_hex[i * 2 + 1]) orelse fail("sign: the seed is 32 bytes\n", .{});
        b.* = hi << 4 | lo;
    }
    const msg = std.Io.Dir.cwd().readFileAlloc(io, args[2], arena, .unlimited) catch |err|
        fail("sign: cannot read the file: {s}\n", .{@errorName(err)});
    const kp = Ed25519.KeyPair.generateDeterministic(seed) catch
        fail("sign: the seed is not a key\n", .{});
    const sig = kp.sign(msg, null) catch fail("sign: the seed is not a key\n", .{});
    const pk = kp.public_key.toBytes();
    const sb = sig.toBytes();
    var out: [4 + 64 + 1 + 128 + 1]u8 = undefined;
    out[0..4].* = "sig ".*;
    const alphabet = "0123456789abcdef";
    for (pk, 0..) |b, i| {
        out[4 + i * 2] = alphabet[b >> 4];
        out[5 + i * 2] = alphabet[b & 0xf];
    }
    out[4 + 64] = ' ';
    for (sb, 0..) |b, i| {
        out[4 + 65 + i * 2] = alphabet[b >> 4];
        out[4 + 66 + i * 2] = alphabet[b & 0xf];
    }
    out[out.len - 1] = '\n';
    const stdout = std.Io.File.stdout();
    stdout.writeStreamingAll(io, &out) catch fail("sign: cannot write the signature\n", .{});
}
