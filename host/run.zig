const std = @import("std");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_run(program: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64) usize;

/// Steps the machine may take when no budget is given.
const default_budget: u64 = 100_000_000;

const usage = "usage: run <program-file> [step-budget]   (default budget: 100000000 machine steps)\n";

fn fail(comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(format, args);
    std.process.exit(2);
}

/// Read a file, hand its bytes to `reflect_run`, print the bytes that come
/// back. Zig does not read the program, and it does not look at the answer:
/// a syntax error, an error outcome and a value are all text the kernel wrote,
/// and all of them exit 0. Exit 2 means this command could not ask the kernel
/// or could not write its answer.
pub fn main(init: std.process.Init) void {
    const arena = init.arena.allocator();
    const args = init.minimal.args.toSlice(arena) catch fail("run: out of memory\n", .{});
    if (args.len < 2 or args.len > 3) fail("{s}", .{usage});

    const budget = if (args.len == 3)
        std.fmt.parseInt(u64, args[2], 10) catch
            fail("run: the step budget must be a whole number, got `{s}`\n", .{args[2]})
    else
        default_budget;

    const program = std.Io.Dir.cwd().readFileAlloc(init.io, args[1], arena, .unlimited) catch |err|
        fail("run: cannot read `{s}`: {s}\n", .{ args[1], @errorName(err) });

    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0)
        fail("run: the kernel did not start\n", .{});

    // Most answers fit the first buffer. One that does not is answered by its
    // length, and the same program is run again with that much room.
    var first: [65536]u8 = undefined;
    var text: []u8 = &first;
    var needed = reflect_run(program.ptr, program.len, text.ptr, text.len, budget);
    if (needed > text.len) {
        text = arena.alloc(u8, needed) catch fail("run: out of memory\n", .{});
        needed = reflect_run(program.ptr, program.len, text.ptr, text.len, budget);
        if (needed > text.len) fail("run: the kernel gave two different answers\n", .{});
    }

    const out = std.Io.File.stdout();
    out.writeStreamingAll(init.io, text[0..needed]) catch fail("run: cannot write the answer\n", .{});
    out.writeStreamingAll(init.io, "\n") catch fail("run: cannot write the answer\n", .{});
}
