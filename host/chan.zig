const std = @import("std");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_channels(program: [*]const u8, length: usize, schedule: [*]const u8, schedule_length: usize, out: [*]u8, capacity: usize, budget: u64, limit: u64) usize;

/// Steps each machine run may take when no budget is given.
const default_budget: u64 = 100_000_000;
/// Events chosen at most when no schedule and no limit is given.
const default_limit: u64 = 10_000;

const usage = "usage: chan <program-file> [schedule-file | -] [step-budget] [event-limit]   (default budget: 100000000 machine steps for each turn; default limit: 10000 events)\n";

fn fail(comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(format, args);
    std.process.exit(2);
}

/// Read a program file and, when one is named, a schedule file, hand both to
/// `reflect_channels`, print the bytes that come back. With no schedule file,
/// or `-` in its place, the kernel chooses the events. Zig reads neither
/// file's contents, chooses nothing, and does not look at the answer: the
/// schedule, each process, a refused event and a syntax error are all text the
/// kernel wrote, and all exit 0. Exit 2 means this command could not ask the
/// kernel or could not write its answer.
pub fn main(init: std.process.Init) void {
    const arena = init.arena.allocator();
    const args = init.minimal.args.toSlice(arena) catch fail("chan: out of memory\n", .{});
    if (args.len < 2 or args.len > 5) fail("{s}", .{usage});

    // Diagnostics do not repeat the arguments, so each is one line whatever
    // bytes the arguments hold.
    const budget = if (args.len >= 4)
        std.fmt.parseInt(u64, args[3], 10) catch
            fail("chan: the step budget must be a whole number\n", .{})
    else
        default_budget;
    const limit = if (args.len >= 5)
        std.fmt.parseInt(u64, args[4], 10) catch
            fail("chan: the event limit must be a whole number\n", .{})
    else
        default_limit;

    const program = std.Io.Dir.cwd().readFileAlloc(init.io, args[1], arena, .unlimited) catch |err|
        fail("chan: cannot read the program file: {s}\n", .{@errorName(err)});
    // An empty schedule means the kernel chooses. A schedule file that is
    // empty is refused here, so that it is not taken for no schedule.
    var schedule: []const u8 = "";
    if (args.len >= 3 and !std.mem.eql(u8, args[2], "-")) {
        schedule = std.Io.Dir.cwd().readFileAlloc(init.io, args[2], arena, .unlimited) catch |err|
            fail("chan: cannot read the schedule file: {s}\n", .{@errorName(err)});
        if (schedule.len == 0) fail("chan: the schedule file is empty\n", .{});
    }

    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0)
        fail("chan: the kernel did not start\n", .{});

    // Most answers fit the first buffer. One that does not is answered by its
    // length, and the same call is made again with that much room.
    var first: [65536]u8 = undefined;
    var text: []u8 = &first;
    var needed = reflect_channels(program.ptr, program.len, schedule.ptr, schedule.len, text.ptr, text.len, budget, limit);
    if (needed > text.len) {
        text = arena.alloc(u8, needed) catch fail("chan: out of memory\n", .{});
        needed = reflect_channels(program.ptr, program.len, schedule.ptr, schedule.len, text.ptr, text.len, budget, limit);
        if (needed > text.len) fail("chan: the kernel gave two different answers\n", .{});
    }

    const out = std.Io.File.stdout();
    out.writeStreamingAll(init.io, text[0..needed]) catch fail("chan: cannot write the answer\n", .{});
    out.writeStreamingAll(init.io, "\n") catch fail("chan: cannot write the answer\n", .{});
}
