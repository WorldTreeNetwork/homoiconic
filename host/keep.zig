const std = @import("std");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn kernel_retain(value: *anyopaque) void;
extern fn reflect_keep_start(program: [*]const u8, length: usize, budget: u64) *anyopaque;
extern fn reflect_keep_answer(root: [*]const u8, root_length: usize, answer: [*]const u8, answer_length: usize, budget: u64) *anyopaque;
extern fn reflect_keep_need(session: *anyopaque, out: [*]u8, capacity: usize) usize;
extern fn reflect_keep_give(session: *anyopaque, piece: [*]const u8, length: usize) *anyopaque;
extern fn reflect_keep_count(session: *anyopaque) usize;
extern fn reflect_keep_name(session: *anyopaque, index: usize, out: [*]u8, capacity: usize) usize;
extern fn reflect_keep_piece(session: *anyopaque, index: usize, out: [*]u8, capacity: usize) usize;
extern fn reflect_keep_text(session: *anyopaque, out: [*]u8, capacity: usize) usize;

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

    var session = if (starting)
        reflect_keep_start(source.ptr, source.len, budget)
    else
        reflect_keep_answer(args[3].ptr, args[3].len, source.ptr, source.len, budget);

    // Supply pieces until the turn needs no more.
    var name: [64]u8 = undefined;
    while (true) {
        kernel_retain(session);
        const length = reflect_keep_need(session, &name, name.len);
        if (length == 0) break;
        if (length != name.len) fail("keep: the kernel named a piece badly\n", .{});
        const piece = store.readFileAlloc(io, &name, arena, .unlimited) catch |err| {
            if (err == error.FileNotFound) {
                std.debug.print("keep: the store lacks piece {s}\n", .{name});
                std.process.exit(3);
            }
            fail("keep: cannot read piece {s}: {s}\n", .{ name, @errorName(err) });
        };
        session = reflect_keep_give(session, piece.ptr, piece.len);
    }

    // Store the new pieces before saying where the root is.
    kernel_retain(session);
    const count = reflect_keep_count(session);
    var index: usize = 0;
    var none: [1]u8 = undefined;
    while (index < count) : (index += 1) {
        kernel_retain(session);
        if (reflect_keep_name(session, index, &name, name.len) != name.len)
            fail("keep: the kernel named a piece badly\n", .{});
        kernel_retain(session);
        const size = reflect_keep_piece(session, index, &none, 0);
        const bytes = arena.alloc(u8, size) catch fail("keep: out of memory\n", .{});
        kernel_retain(session);
        if (reflect_keep_piece(session, index, bytes.ptr, bytes.len) != size)
            fail("keep: the kernel gave two different answers\n", .{});
        store.writeFile(io, .{ .sub_path = &name, .data = bytes }) catch |err|
            fail("keep: cannot write piece {s}: {s}\n", .{ name, @errorName(err) });
    }

    kernel_retain(session);
    const size = reflect_keep_text(session, &none, 0);
    const text = arena.alloc(u8, size) catch fail("keep: out of memory\n", .{});
    kernel_retain(session);
    if (reflect_keep_text(session, text.ptr, text.len) != size)
        fail("keep: the kernel gave two different answers\n", .{});
    const out = std.Io.File.stdout();
    out.writeStreamingAll(io, text) catch fail("keep: cannot write the answer\n", .{});
    out.writeStreamingAll(io, "\n") catch fail("keep: cannot write the answer\n", .{});
}
