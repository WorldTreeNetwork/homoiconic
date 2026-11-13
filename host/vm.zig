const std = @import("std");
const session = @import("session.zig");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_vm_start(program: [*]const u8, length: usize, log: [*]const u8, log_length: usize, budget: u64) *anyopaque;
extern fn reflect_vm_from(root: [*]const u8, root_length: usize, log: [*]const u8, log_length: usize, budget: u64) *anyopaque;

const default_budget: u64 = 100_000_000;

const usage = "usage: vm <store-dir> start <program-file> <log-file> [step-budget]\n       vm <store-dir> from <root> <log-file> [step-budget]\n";

fn fail(comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(format, args);
    std.process.exit(2);
}

/// A program handling a log, with its state kept in a directory. `start` runs
/// the program from its beginning and hands it the log. `from` hands the log
/// to the state kept under a root. The kernel reads the log, decides what each
/// entry does, and names the state; this command reads the two files, moves
/// pieces between the kernel and the directory (`session.zig`), and prints
/// the kernel's text.
///
/// Exit 0: the kernel answered. Exit 3: the store lacks a piece that is
/// needed; nothing was written. Exit 2: the command could not ask the kernel,
/// read or write.
pub fn main(init: std.process.Init) void {
    const arena = init.arena.allocator();
    const io = init.io;
    const args = init.minimal.args.toSlice(arena) catch fail("vm: out of memory\n", .{});
    if (args.len != 5 and args.len != 6) fail("{s}", .{usage});
    const starting = std.mem.eql(u8, args[2], "start");
    if (!starting and !std.mem.eql(u8, args[2], "from")) fail("{s}", .{usage});
    const budget = if (args.len == 6)
        std.fmt.parseInt(u64, args[5], 10) catch
            fail("vm: the step budget must be a whole number\n", .{})
    else
        default_budget;

    const program = if (starting)
        std.Io.Dir.cwd().readFileAlloc(io, args[3], arena, .unlimited) catch |err|
            fail("vm: cannot read the program file: {s}\n", .{@errorName(err)})
    else
        args[3];
    const log = std.Io.Dir.cwd().readFileAlloc(io, args[4], arena, .unlimited) catch |err|
        fail("vm: cannot read the log file: {s}\n", .{@errorName(err)});
    const store = std.Io.Dir.cwd().openDir(io, args[1], .{}) catch |err|
        fail("vm: cannot open the store directory: {s}\n", .{@errorName(err)});

    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0)
        fail("vm: the kernel did not start\n", .{});

    const first = if (starting)
        reflect_vm_start(program.ptr, program.len, log.ptr, log.len, budget)
    else
        reflect_vm_from(program.ptr, program.len, log.ptr, log.len, budget);

    session.carry("vm", io, arena, store, first);
}
