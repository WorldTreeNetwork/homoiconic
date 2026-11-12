const std = @import("std");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_source_bytes(program: [*]const u8, length: usize, out: [*]u8, capacity: usize) usize;

const usage = "usage: bytes <program-file>   (writes the program's byte form to standard output)\n";

fn fail(comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(format, args);
    std.process.exit(2);
}

/// Read a program's source, hand it to `reflect_source_bytes`, and write the
/// byte form that comes back. Zig does not read the program and does not make
/// the bytes. A syntax error is the kernel's text: it goes to standard error
/// and the exit is 1, because standard output is for the byte form alone.
/// Exit 2 means this command could not ask the kernel or could not write.
pub fn main(init: std.process.Init) void {
    const arena = init.arena.allocator();
    const args = init.minimal.args.toSlice(arena) catch fail("bytes: out of memory\n", .{});
    if (args.len != 2) fail("{s}", .{usage});

    const program = std.Io.Dir.cwd().readFileAlloc(init.io, args[1], arena, .unlimited) catch |err|
        fail("bytes: cannot read the program file: {s}\n", .{@errorName(err)});

    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0)
        fail("bytes: the kernel did not start\n", .{});

    var first: [65536]u8 = undefined;
    var answer: []u8 = &first;
    var needed = reflect_source_bytes(program.ptr, program.len, answer.ptr, answer.len);
    if (needed > answer.len) {
        answer = arena.alloc(u8, needed) catch fail("bytes: out of memory\n", .{});
        needed = reflect_source_bytes(program.ptr, program.len, answer.ptr, answer.len);
        if (needed > answer.len) fail("bytes: the kernel gave two different answers\n", .{});
    }
    if (needed == 0) fail("bytes: the kernel gave no answer\n", .{});

    if (answer[0] != 0) {
        std.debug.print("{s}\n", .{answer[1..needed]});
        std.process.exit(1);
    }
    std.Io.File.stdout().writeStreamingAll(init.io, answer[1..needed]) catch
        fail("bytes: cannot write the byte form\n", .{});
}
