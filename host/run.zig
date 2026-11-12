const std = @import("std");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_run(program: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64) usize;
extern fn reflect_run_bytes(program: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64) usize;

/// Steps the machine may take when no budget is given.
const default_budget: u64 = 100_000_000;

const usage = "usage: run [--bytes] <program-file> [step-budget]   (default budget: 100000000 machine steps)\n";

fn fail(comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(format, args);
    std.process.exit(2);
}

/// Read a file, hand its bytes to `reflect_run`, print the bytes that come
/// back. With `--bytes` the file is a program in its byte form and goes to
/// `reflect_run_bytes`; bytes that are not a program are the kernel's text too. Zig does not read the program, and it does not look at the answer:
/// a syntax error, an error outcome and a value are all text the kernel wrote,
/// and all of them exit 0. Exit 2 means this command could not ask the kernel
/// or could not write its answer.
pub fn main(init: std.process.Init) void {
    const arena = init.arena.allocator();
    const all = init.minimal.args.toSlice(arena) catch fail("run: out of memory\n", .{});
    const as_bytes = all.len > 1 and std.mem.eql(u8, all[1], "--bytes");
    const args = if (as_bytes) all[1..] else all;
    const ask = if (as_bytes) &reflect_run_bytes else &reflect_run;
    if (args.len < 2 or args.len > 3) fail("{s}", .{usage});

    // Diagnostics do not repeat the arguments, so each is one line whatever
    // bytes the arguments hold.
    const budget = if (args.len == 3)
        std.fmt.parseInt(u64, args[2], 10) catch
            fail("run: the step budget must be a whole number\n", .{})
    else
        default_budget;

    const program = std.Io.Dir.cwd().readFileAlloc(init.io, args[1], arena, .unlimited) catch |err|
        fail("run: cannot read the program file: {s}\n", .{@errorName(err)});

    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0)
        fail("run: the kernel did not start\n", .{});

    // Most answers fit the first buffer. One that does not is answered by its
    // length, and the same program is run again with that much room.
    var first: [65536]u8 = undefined;
    var text: []u8 = &first;
    var needed = ask(program.ptr, program.len, text.ptr, text.len, budget);
    if (needed > text.len) {
        text = arena.alloc(u8, needed) catch fail("run: out of memory\n", .{});
        needed = ask(program.ptr, program.len, text.ptr, text.len, budget);
        if (needed > text.len) fail("run: the kernel gave two different answers\n", .{});
    }

    const out = std.Io.File.stdout();
    out.writeStreamingAll(init.io, text[0..needed]) catch fail("run: cannot write the answer\n", .{});
    out.writeStreamingAll(init.io, "\n") catch fail("run: cannot write the answer\n", .{});
}
