const std = @import("std");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_converse(program: [*]const u8, length: usize, answers: [*]const u8, answers_length: usize, out: [*]u8, capacity: usize, budget: u64) usize;

/// Steps each turn may take when no budget is given.
const default_budget: u64 = 100_000_000;

const usage = "usage: ask <program-file> <answers-file> [step-budget]   (default budget: 100000000 machine steps for each turn)\n";

fn fail(comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(format, args);
    std.process.exit(2);
}

/// Read a program file and an answers file, hand both to `reflect_converse`,
/// print the bytes that come back. Zig reads neither file's contents and does
/// not look at the answer: the requests made, a run that is waiting, a value,
/// an error and a syntax error are all text the kernel wrote, and all exit 0.
/// Exit 2 means this command could not ask the kernel or could not write its
/// answer.
pub fn main(init: std.process.Init) void {
    const arena = init.arena.allocator();
    const args = init.minimal.args.toSlice(arena) catch fail("ask: out of memory\n", .{});
    if (args.len < 3 or args.len > 4) fail("{s}", .{usage});

    // Diagnostics do not repeat the arguments, so each is one line whatever
    // bytes the arguments hold.
    const budget = if (args.len == 4)
        std.fmt.parseInt(u64, args[3], 10) catch
            fail("ask: the step budget must be a whole number\n", .{})
    else
        default_budget;

    const program = std.Io.Dir.cwd().readFileAlloc(init.io, args[1], arena, .unlimited) catch |err|
        fail("ask: cannot read the program file: {s}\n", .{@errorName(err)});
    const answers = std.Io.Dir.cwd().readFileAlloc(init.io, args[2], arena, .unlimited) catch |err|
        fail("ask: cannot read the answers file: {s}\n", .{@errorName(err)});

    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0)
        fail("ask: the kernel did not start\n", .{});

    // Most answers fit the first buffer. One that does not is answered by its
    // length, and the same call is made again with that much room.
    var first: [65536]u8 = undefined;
    var text: []u8 = &first;
    var needed = reflect_converse(program.ptr, program.len, answers.ptr, answers.len, text.ptr, text.len, budget);
    if (needed > text.len) {
        text = arena.alloc(u8, needed) catch fail("ask: out of memory\n", .{});
        needed = reflect_converse(program.ptr, program.len, answers.ptr, answers.len, text.ptr, text.len, budget);
        if (needed > text.len) fail("ask: the kernel gave two different answers\n", .{});
    }

    const out = std.Io.File.stdout();
    out.writeStreamingAll(init.io, text[0..needed]) catch fail("ask: cannot write the answer\n", .{});
    out.writeStreamingAll(init.io, "\n") catch fail("ask: cannot write the answer\n", .{});
}
