const std = @import("std");

const Ed25519 = std.crypto.sign.Ed25519;

fn fail(comptime who: []const u8, comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(who ++ ": " ++ format, args);
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

fn unhex(comptime who: []const u8, text: []const u8, out: []u8) void {
    if (text.len != out.len * 2) fail(who, "the signature is not valid\n", .{});
    for (out, 0..) |*b, i| {
        const hi = hexByte(text[i * 2]) orelse fail(who, "the signature is not valid\n", .{});
        const lo = hexByte(text[i * 2 + 1]) orelse fail(who, "the signature is not valid\n", .{});
        b.* = hi << 4 | lo;
    }
}

/// A log file may start with `sig <public key> <signature>`, both hex, over
/// the bytes that follow that line. The check is Ed25519. A log with no such
/// line is returned as it stands. The kernel never sees this line.
pub fn body(comptime who: []const u8, log: []const u8) []const u8 {
    if (!std.mem.startsWith(u8, log, "sig ")) return log;
    const nl = std.mem.indexOfScalar(u8, log, '\n') orelse
        fail(who, "the signature is not valid\n", .{});
    const line = log["sig ".len..nl];
    const sp = std.mem.indexOfScalar(u8, line, ' ') orelse
        fail(who, "the signature is not valid\n", .{});
    var pk_bytes: [Ed25519.PublicKey.encoded_length]u8 = undefined;
    var sig_bytes: [Ed25519.Signature.encoded_length]u8 = undefined;
    unhex(who, line[0..sp], &pk_bytes);
    unhex(who, line[sp + 1 ..], &sig_bytes);
    const pk = Ed25519.PublicKey.fromBytes(pk_bytes) catch
        fail(who, "the signature is not valid\n", .{});
    const sig = Ed25519.Signature.fromBytes(sig_bytes);
    const rest = log[nl + 1 ..];
    sig.verify(rest, pk) catch fail(who, "the signature is not valid\n", .{});
    return rest;
}
