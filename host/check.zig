const std = @import("std");
const cases = @import("out/cases.zig");

extern fn initialize_circularKernel_Circular_Host(builtin: u8) *anyopaque;
extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn kernel_run(program: [*]const u8, length: usize) u32;
extern fn reflect_run(program: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64) usize;

/// Pass `program` to `reflect_run` and return the printed bytes. A first buffer
/// that is too small is answered by the needed length; call again with room.
/// Zig holds and prints bytes only.
fn reflect(program: []const u8, budget: u64, small: []u8, big: []u8) ?[]const u8 {
    const needed = reflect_run(program.ptr, program.len, small.ptr, small.len, budget);
    if (needed <= small.len) return small[0..needed];
    if (needed > big.len) return null;
    const again = reflect_run(program.ptr, program.len, big.ptr, big.len, budget);
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
    const need = reflect_run(array.ptr, array.len, &tiny, tiny.len, 1000000);
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
    const circular = initialize_circularKernel_Circular_Host(0);
    const surface = initialize_circularKernel_Surface_Host(0);
    if (kernel_finish_initialization(circular) == 0) std.process.exit(2);
    if (kernel_finish_initialization(surface) == 0) std.process.exit(2);

    const Case = struct { program: []const u8, expected: u32 };
    const scenarios = [_]Case{
        .{ .program = "([0] [0])", .expected = 0 },
        .{ .program = "0", .expected = 1 },
        .{ .program = "[1]", .expected = 0 },
        .{ .program = "(0 ([(0 0)] [(0 0)]))", .expected = 1 },
        .{ .program = "([(0 0)] [(0 0)])", .expected = 4294967295 },
    };
    for (scenarios) |case| {
        const got = kernel_run(case.program.ptr, case.program.len);
        std.debug.print("{s} => {d}\n", .{ case.program, got });
        if (got != case.expected) std.process.exit(1);
    }

    // Exercise the byte boundary and parser, including length-delimited input.
    const boundaries = [_]Case{
        .{ .program = "12", .expected = 25 },
        .{ .program = " \t\r\n[0]\x0b\x0c", .expected = 0 },
        .{ .program = "([1] [0])", .expected = 3 },
        .{ .program = "", .expected = 4294967295 },
        .{ .program = "bad", .expected = 4294967295 },
        .{ .program = "[0", .expected = 4294967295 },
        .{ .program = "(0)", .expected = 4294967295 },
        .{ .program = "(0 0 0)", .expected = 4294967295 },
        .{ .program = "[0] trailing", .expected = 4294967295 },
        .{ .program = "quote 0", .expected = 4294967295 },
        .{ .program = "0\x00", .expected = 4294967295 },
        .{ .program = "\xff", .expected = 4294967295 },
    };
    for (boundaries) |case| {
        const got = kernel_run(case.program.ptr, case.program.len);
        if (got != case.expected) {
            std.debug.print("byte/parser check failed: {any}: expected {d}, got {d}\n", .{ case.program, case.expected, got });
            std.process.exit(1);
        }
    }
    // The bytes beyond the declared length are not part of this program.
    const buffer = "0invalid";
    if (kernel_run(buffer.ptr, 1) != 1) std.process.exit(1);
    std.debug.print("byte/parser checks passed\n", .{});

    checkReflect();
}
