const std = @import("std");

extern fn initialize_circularKernel_Circular_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn kernel_run(program: [*]const u8, length: usize) u32;

pub fn main() void {
    const initialized = initialize_circularKernel_Circular_Host(0);
    if (kernel_finish_initialization(initialized) == 0) std.process.exit(2);

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
}
