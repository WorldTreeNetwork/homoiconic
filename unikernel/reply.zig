//! Linux side of the same export the guest calls.

const std = @import("std");

extern fn open(path: [*:0]const u8, flags: c_int) c_int;
extern fn read(fd: c_int, buf: [*]u8, n: usize) isize;
extern fn write(fd: c_int, buf: [*]const u8, n: usize) isize;
extern fn close(fd: c_int) c_int;

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_reply_bytes(program: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64, space: u64) usize;
extern fn reflect_default_space(ignored: u32) u64;
extern fn reflect_source_bytes(program: [*]const u8, length: usize, out: [*]u8, capacity: usize) usize;

export fn initialize_libuv() void {}

pub fn main(init: std.process.Init.Minimal) u8 {
    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0) return 2;
    var buf: [1 << 20]u8 = undefined;
    const v = init.args.vector;
    if (v.len < 2) return usage();
    const cmd = std.mem.span(v[1]);
    if (std.mem.eql(u8, cmd, "source")) {
        if (v.len != 3) return usage();
        const path = std.mem.span(v[2]);
        const n = readFile(path, &buf) orelse return 2;
        var out: [1 << 20]u8 = undefined;
        const need = reflect_source_bytes(buf[0..n].ptr, n, &out, out.len);
        if (need > out.len or need < 1 or out[0] != 0) return 2;
        writeAll(out[1..need]);
        return 0;
    }
    if (std.mem.eql(u8, cmd, "run")) {
        if (v.len != 4 and v.len != 5) return usage();
        const budget_s = std.mem.span(v[2]);
        const path = std.mem.span(v[3]);
        const budget = std.fmt.parseInt(u64, budget_s, 10) catch return 2;
        // The cells the run may make: the kernel's default unless one is given.
        const space = if (v.len == 5)
            std.fmt.parseInt(u64, std.mem.span(v[4]), 10) catch return 2
        else
            reflect_default_space(0);
        const n = readFile(path, &buf) orelse return 2;
        var out: [1 << 20]u8 = undefined;
        const need = reflect_reply_bytes(buf[0..n].ptr, n, &out, out.len, budget, space);
        if (need > out.len) return 2;
        writeAll(out[0..need]);
        return 0;
    }
    if (std.mem.eql(u8, cmd, "capacity")) {
        if (v.len != 4) return usage();
        const budget_s = std.mem.span(v[2]);
        const path = std.mem.span(v[3]);
        const budget = std.fmt.parseInt(u64, budget_s, 10) catch return 2;
        const n = readFile(path, &buf) orelse return 2;
        var small: [16]u8 = .{0xaa} ** 16;
        const need = reflect_reply_bytes(buf[0..n].ptr, n, &small, 4, budget, reflect_default_space(0));
        if (need <= 4) return 2;
        for (small) |b| if (b != 0xaa) return 2;
        var out: [1 << 20]u8 = undefined;
        const again = reflect_reply_bytes(buf[0..n].ptr, n, &out, out.len, budget, reflect_default_space(0));
        if (again != need) return 2;
        writeAll(out[0..again]);
        return 0;
    }
    return usage();
}

fn usage() u8 {
    std.debug.print("usage: reply source <file> | reply run <budget> <bytes> [space] | reply capacity <budget> <bytes>\n", .{});
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
    _ = write(1, b.ptr, b.len);
}
