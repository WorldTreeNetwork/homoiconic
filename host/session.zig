const std = @import("std");

extern fn kernel_retain(value: *anyopaque) void;
extern fn reflect_keep_need(session: *anyopaque, out: [*]u8, capacity: usize) usize;
extern fn reflect_keep_give(session: *anyopaque, piece: [*]const u8, length: usize) *anyopaque;
extern fn reflect_keep_count(session: *anyopaque) usize;
extern fn reflect_keep_name(session: *anyopaque, index: usize, out: [*]u8, capacity: usize) usize;
extern fn reflect_keep_piece(session: *anyopaque, index: usize, out: [*]u8, capacity: usize) usize;
extern fn reflect_keep_text(session: *anyopaque, out: [*]u8, capacity: usize) usize;

/// Carry a kernel session to its end against a store directory, for the
/// command called `name`. It does three things for the kernel: it reads the
/// file a piece is named by when the kernel asks for that piece, it writes the
/// files the kernel hands back, and it prints the kernel's text. It does not
/// read a piece, hash one, or name one: every name is text from the kernel,
/// and the kernel checks every piece against its name.
///
/// Returns when the kernel answered. Exit 3: the store lacks a piece the
/// session needs; nothing was written. Exit 2: could not read or write.
pub fn carry(comptime name_of: []const u8, io: std.Io, arena: std.mem.Allocator, store: std.Io.Dir, first: *anyopaque) void {
    var session = first;
    // Supply pieces until the turn needs no more.
    var name: [64]u8 = undefined;
    while (true) {
        kernel_retain(session);
        const length = reflect_keep_need(session, &name, name.len);
        if (length == 0) break;
        if (length != name.len) fail(name_of ++ ": the kernel named a piece badly\n", .{});
        const piece = store.readFileAlloc(io, &name, arena, .unlimited) catch |err| {
            if (err == error.FileNotFound) {
                std.debug.print(name_of ++ ": the store lacks piece {s}\n", .{name});
                std.process.exit(3);
            }
            fail(name_of ++ ": cannot read piece {s}: {s}\n", .{ name, @errorName(err) });
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
            fail(name_of ++ ": the kernel named a piece badly\n", .{});
        kernel_retain(session);
        const size = reflect_keep_piece(session, index, &none, 0);
        const bytes = arena.alloc(u8, size) catch fail(name_of ++ ": out of memory\n", .{});
        kernel_retain(session);
        if (reflect_keep_piece(session, index, bytes.ptr, bytes.len) != size)
            fail(name_of ++ ": the kernel gave two different answers\n", .{});
        store.writeFile(io, .{ .sub_path = &name, .data = bytes }) catch |err|
            fail(name_of ++ ": cannot write piece {s}: {s}\n", .{ name, @errorName(err) });
    }

    kernel_retain(session);
    const size = reflect_keep_text(session, &none, 0);
    const text = arena.alloc(u8, size) catch fail(name_of ++ ": out of memory\n", .{});
    kernel_retain(session);
    if (reflect_keep_text(session, text.ptr, text.len) != size)
        fail(name_of ++ ": the kernel gave two different answers\n", .{});
    const out = std.Io.File.stdout();
    out.writeStreamingAll(io, text) catch fail(name_of ++ ": cannot write the answer\n", .{});
    out.writeStreamingAll(io, "\n") catch fail(name_of ++ ": cannot write the answer\n", .{});
}

fn fail(comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(format, args);
    std.process.exit(2);
}
