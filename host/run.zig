const std = @import("std");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_run(program: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64) usize;
extern fn reflect_run_bytes(program: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64) usize;
extern fn reflect_interp(program: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64, levels: u32, flags: u8) usize;

/// Steps the machine may take when no budget is given.
const default_budget: u64 = 100_000_000;

const usage = "usage: run [--bytes] [--interp[=levels]] [--text] <program-file> [step-budget]   (default budget: 100000000 machine steps)\n";

fn fail(comptime format: []const u8, args: anytype) noreturn {
    std.debug.print(format, args);
    std.process.exit(2);
}

/// Read a file, hand its bytes to `reflect_run`, print the bytes that come
/// back. With `--bytes` the file is a program in its byte form and goes to
/// `reflect_run_bytes`; bytes that are not a program are the kernel's text too.
/// With `--interp` the program runs through the metacircular interpreter, the
/// closed term `interp` given the program as data (`reflect_interp`), and with
/// `--interp=k` through `k` interpreters, each running the next. With `--text`
/// the kernel writes a result that is an array of code points as the text it
/// spells. Zig does not
/// read the program, and it does not look at the answer:
/// a syntax error, an error outcome and a value are all text the kernel wrote,
/// and all of them exit 0. Exit 2 means this command could not ask the kernel
/// or could not write its answer.
pub fn main(init: std.process.Init) void {
    const arena = init.arena.allocator();
    const all = init.minimal.args.toSlice(arena) catch fail("run: out of memory\n", .{});
    var as_bytes = false;
    var levels: ?u32 = null;
    var as_text = false;
    var first_arg: usize = 1;
    while (first_arg < all.len) : (first_arg += 1) {
        const a = all[first_arg];
        if (std.mem.eql(u8, a, "--bytes") and !as_bytes) {
            as_bytes = true;
        } else if (std.mem.eql(u8, a, "--text") and !as_text) {
            as_text = true;
        } else if (std.mem.eql(u8, a, "--interp") and levels == null) {
            levels = 1;
        } else if (std.mem.startsWith(u8, a, "--interp=") and levels == null) {
            levels = std.fmt.parseInt(u32, a["--interp=".len..], 10) catch
                fail("run: the interpreter levels must be a whole number\n", .{});
        } else break;
    }
    const args = all[first_arg - 1 ..];
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
    var needed = ask(program, text, budget, as_bytes, as_text, levels);
    if (needed > text.len) {
        text = arena.alloc(u8, needed) catch fail("run: out of memory\n", .{});
        needed = ask(program, text, budget, as_bytes, as_text, levels);
        if (needed > text.len) fail("run: the kernel gave two different answers\n", .{});
    }

    const out = std.Io.File.stdout();
    out.writeStreamingAll(init.io, text[0..needed]) catch fail("run: cannot write the answer\n", .{});
    out.writeStreamingAll(init.io, "\n") catch fail("run: cannot write the answer\n", .{});
}

fn ask(program: []const u8, text: []u8, budget: u64, as_bytes: bool, as_text: bool, levels: ?u32) usize {
    if (levels != null or as_text) {
        const flags: u8 = @as(u8, @intFromBool(as_bytes)) | (@as(u8, @intFromBool(as_text)) << 1);
        return reflect_interp(program.ptr, program.len, text.ptr, text.len, budget, levels orelse 0, flags);
    }
    const run = if (as_bytes) &reflect_run_bytes else &reflect_run;
    return run(program.ptr, program.len, text.ptr, text.len, budget);
}
