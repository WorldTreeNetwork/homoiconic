const std = @import("std");
const session = @import("session.zig");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_keep_start(program: [*]const u8, length: usize, budget: u64) *anyopaque;
extern fn reflect_keep_answer(root: [*]const u8, root_length: usize, answer: [*]const u8, answer_length: usize, budget: u64) *anyopaque;

const default_budget: u64 = 100_000_000;

const usage = "usage: keep <store-dir> start <program-file> [step-budget]\n       keep <store-dir> answer <root> <answer-file> [step-budget]\n";

fn fail(comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(format, args);
    std.process.exit(2);
}

fn parseBudget(text: []const u8) u64 {
    return std.fmt.parseInt(u64, text, 10) catch
        fail("keep: the step budget must be a whole number\n", .{});
}

/// One turn of a program whose state is kept in a directory between turns.
/// The kernel runs the turn. This command does three things for it: it reads
/// the file a piece is named by when the kernel asks for that piece, it writes
/// the files the kernel hands back, and it prints the kernel's text. It does
/// not read a piece, hash one, or name one: every name is text from the
/// kernel, and the kernel checks every piece against its name.
///
/// Exit 0: the kernel answered. Exit 3: the store lacks a piece the turn
/// needs; nothing was written and the turn can be run again when the piece is
/// there. Exit 2: the command could not ask the kernel, read or write.
pub fn main(init: std.process.Init) void {
    const arena = init.arena.allocator();
    const io = init.io;
    const args = init.minimal.args.toSlice(arena) catch fail("keep: out of memory\n", .{});
    if (args.len < 4) fail("{s}", .{usage});
    const starting = std.mem.eql(u8, args[2], "start");
    const answering = std.mem.eql(u8, args[2], "answer");
    if (!starting and !answering) fail("{s}", .{usage});
    const fixed: usize = if (starting) 4 else 5;
    if (args.len != fixed and args.len != fixed + 1) fail("{s}", .{usage});
    const budget = if (args.len == fixed + 1) parseBudget(args[fixed]) else default_budget;

    const source = std.Io.Dir.cwd().readFileAlloc(io, args[fixed - 1], arena, .unlimited) catch |err|
        fail("keep: cannot read the {s} file: {s}\n", .{ if (starting) "program" else "answer", @errorName(err) });
    const store = std.Io.Dir.cwd().openDir(io, args[1], .{}) catch |err|
        fail("keep: cannot open the store directory: {s}\n", .{@errorName(err)});

    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0)
        fail("keep: the kernel did not start\n", .{});

    const first = if (starting)
        reflect_keep_start(source.ptr, source.len, budget)
    else
        reflect_keep_answer(args[3].ptr, args[3].len, source.ptr, source.len, budget);

    session.carry("keep", io, arena, store, first);
}
