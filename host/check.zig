const std = @import("std");
const cases = @import("out/cases.zig");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_run(program: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64, space: u64) usize;
extern fn reflect_default_space(ignored: u32) u64;

/// Pass `program` to `reflect_run` and return the printed bytes. A first buffer
/// that is too small is answered by the needed length; call again with room.
/// Zig holds and prints bytes only.
fn reflect(program: []const u8, budget: u64, small: []u8, big: []u8) ?[]const u8 {
    const needed = reflect_run(program.ptr, program.len, small.ptr, small.len, budget, reflect_default_space(0));
    if (needed <= small.len) return small[0..needed];
    if (needed > big.len) return null;
    const again = reflect_run(program.ptr, program.len, big.ptr, big.len, budget, reflect_default_space(0));
    if (again != needed) return null;
    return big[0..needed];
}

fn checkReflect() void {
    var small: [8]u8 = undefined;
    var big: [4096]u8 = undefined;
    var retried: usize = 0;
    for (cases.prints) |case| {
        const got = reflect(case.program, case.budget, &small, &big) orelse {
            std.debug.print("reflect_run: rendering did not fit or changed size: {s}\n", .{case.program});
            std.process.exit(1);
        };
        std.debug.print("{s}\n  => {s}\n", .{ case.program, got });
        if (!std.mem.eql(u8, got, case.expected)) {
            std.debug.print("reflect_run check failed: expected {s}\n", .{case.expected});
            std.process.exit(1);
        }
        if (case.expected.len > small.len) retried += 1;
    }
    // The retry path was taken: some rendering is longer than the small buffer.
    if (retried == 0) std.process.exit(1);

    // A buffer that is too small is answered by the needed length and left alone.
    const array = "[1, 2, 3, 4]";
    var tiny: [3]u8 = .{ 'x', 'y', 'z' };
    const need = reflect_run(array.ptr, array.len, &tiny, tiny.len, 1000000, reflect_default_space(0));
    if (need != array.len or !std.mem.eql(u8, &tiny, "xyz")) {
        std.debug.print("reflect_run too-small buffer check failed: needed {d}\n", .{need});
        std.process.exit(1);
    }

    // Text that is not a program comes back as a syntax error with line and column.
    const Refusal = struct { program: []const u8, expected: []const u8 };
    const refusals = [_]Refusal{
        .{ .program = "f 1", .expected = "syntax error: line 1, column 1: unbound name `f`" },
        .{ .program = "(1", .expected = "syntax error: line 1, column 3: expected `)`" },
        .{ .program = "", .expected = "syntax error: line 1, column 1: empty program: there is nothing to read" },
        .{ .program = "\xff", .expected = "syntax error: line 1, column 1: unexpected character; programs are ASCII text" },
        // A zero byte does not end the program: the bytes before it are not run alone.
        .{ .program = "42\x00", .expected = "syntax error: line 1, column 3: unexpected character; programs are ASCII text" },
    };
    for (refusals) |case| {
        const got = reflect(case.program, 1000, &small, &big) orelse std.process.exit(1);
        if (!std.mem.eql(u8, got, case.expected)) {
            std.debug.print("syntax error check failed: {any}: got {s}\n", .{ case.program, got });
            std.process.exit(1);
        }
    }
    std.debug.print("reflect_run checks passed\n", .{});
}

pub fn main() void {
    const surface = initialize_circularKernel_Surface_Host(0);
    if (kernel_finish_initialization(surface) == 0) std.process.exit(2);

    // The bytes beyond the declared length are not part of this program.
    const buffer = "42invalid";
    var out: [8]u8 = undefined;
    const needed = reflect_run(buffer.ptr, 2, &out, out.len, 1000, reflect_default_space(0));
    if (needed != 2 or !std.mem.eql(u8, out[0..2], "42")) {
        std.debug.print("reflect_run read past the declared length\n", .{});
        std.process.exit(1);
    }

    checkReflect();
}
