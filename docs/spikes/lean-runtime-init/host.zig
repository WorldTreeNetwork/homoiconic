const std = @import("std");

extern fn initialize_src_Spike(builtin: u8) ?*anyopaque;
extern fn lean_io_mark_end_initialization() void;
extern fn lean_io_result_show_error(r: *anyopaque) void;
extern fn lean_mk_string(s: [*:0]const u8) ?*anyopaque;
extern fn kernel_run(program: *anyopaque) u32;

const LeanObject = extern struct {
    rc: i32,
    packed_tail: u32,
};

fn initTag(object: *anyopaque) u8 {
    const header: *LeanObject = @ptrCast(@alignCast(object));
    return @truncate(header.packed_tail >> 24);
}

fn run(program: [*:0]const u8) u32 {
    const text = lean_mk_string(program) orelse {
        std.debug.print("lean_mk_string failed\n", .{});
        std.process.exit(3);
    };
    return kernel_run(text);
}

pub fn main() void {
    const init = initialize_src_Spike(0) orelse {
        std.debug.print("initializer returned null\n", .{});
        std.process.exit(2);
    };
    if (initTag(init) != 0) {
        lean_io_result_show_error(init);
        std.process.exit(2);
    }
    lean_io_mark_end_initialization();

    const programs = [_][*:0]const u8{
        "([0] [0])",
        "0",
        "[1]",
        "(0 ([(0 0)] [(0 0)]))",
        "([(0 0)] [(0 0)])",
        "bad",
    };
    const expected = [_]u32{ 0, 1, 0, 1, 4294967295, 4294967295 };
    for (programs, expected) |program, want| {
        const got = run(program);
        std.debug.print("{s} {d}\n", .{ program, got });
        if (got != want) std.process.exit(1);
    }
}
