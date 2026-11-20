//! The program the image runs. It hands one program to the kernel and writes
//! the text that comes back. It does not read the program and it does not look
//! at the answer.
//!
//!   reflect                                  the source built in, by reflect_run
//!   reflect <bytes-file> [step-budget [levels]]
//!                                            a program's byte form, by reflect_interp
//!
//! In the image the second form is what bytes given at boot start: the layer
//! names them `/boot/program` and passes the command line's words after it.
//! The budget defaults to the one built in, and the levels to 1.

const program = @import("program");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_run(source: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64) usize;
extern fn reflect_interp(program: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64, levels: u32, flags: u8) usize;
extern fn open(path: [*:0]const u8, flags: c_int) c_int;
extern fn read(fd: c_int, buf: [*]u8, n: usize) isize;
extern fn close(fd: c_int) c_int;
extern fn realloc(p: ?[*]u8, n: usize) ?[*]u8;
extern fn write(fd: c_int, buf: [*]const u8, n: usize) isize;
extern fn malloc(n: usize) ?[*]u8;
extern fn _exit(status: c_int) noreturn;

/// The Lean runtime starts an event-loop thread for input and output when a
/// package initialises. This image has one thread, and the kernel's exports do
/// no input or output through Lean. The build makes the runtime's own
/// `initialize_libuv` weak, so this empty one is the one that is called.
export fn initialize_libuv() void {}

fn say(s: []const u8) void {
    var rest = s;
    while (rest.len > 0) {
        const n = write(1, rest.ptr, rest.len);
        if (n <= 0 or n > rest.len) _exit(2);
        rest = rest[@intCast(n)..];
    }
}

var first: [65536]u8 = undefined;

/// One run: the bytes, and which export takes them.
const Run = struct {
    input: []const u8,
    budget: u64,
    levels: ?u32, // null: source, by reflect_run

    fn into(r: Run, out: []u8) usize {
        if (r.levels) |k| return reflect_interp(r.input.ptr, r.input.len, out.ptr, out.len, r.budget, k, 1);
        return reflect_run(r.input.ptr, r.input.len, out.ptr, out.len, r.budget);
    }
};

/// A whole number in decimal digits and nothing else.
fn number(comptime T: type, word: [*:0]const u8) ?T {
    var v: T = 0;
    var i: usize = 0;
    while (word[i] != 0) : (i += 1) {
        if (word[i] < '0' or word[i] > '9') return null;
        v = @import("std").math.mul(T, v, 10) catch return null;
        v = @import("std").math.add(T, v, word[i] - '0') catch return null;
    }
    return if (i == 0) null else v;
}

/// Every byte of a file.
fn contents(path: [*:0]const u8) ?[]const u8 {
    const fd = open(path, 0);
    if (fd < 0) return null;
    var room: usize = 65536;
    var buf = malloc(room) orelse return null;
    var n: usize = 0;
    while (true) {
        if (n == room) {
            room *= 2;
            buf = realloc(buf, room) orelse return null;
        }
        const got = read(fd, buf + n, room - n);
        if (got < 0 or got > room - n) return null;
        if (got == 0) break;
        n += @intCast(got);
    }
    _ = close(fd);
    return buf[0..n];
}

pub export fn main(argc: c_int, argv: [*]const [*:0]const u8) c_int {
    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0) {
        say("reflect: the kernel did not start\n");
        return 2;
    }
    var run: Run = .{ .input = program.source, .budget = program.budget, .levels = null };
    if (argc > 4) {
        say("reflect: usage: reflect [bytes-file [step-budget [levels]]]\n");
        return 2;
    }
    if (argc > 1) {
        run.levels = 1;
        if (argc > 2) run.budget = number(u64, argv[2]) orelse {
            say("reflect: the step budget must be a whole number\n");
            return 2;
        };
        if (argc > 3) run.levels = number(u32, argv[3]) orelse {
            say("reflect: the levels must be a whole number\n");
            return 2;
        };
        run.input = contents(argv[1]) orelse {
            say("reflect: cannot read the program bytes\n");
            return 2;
        };
    }
    // Most answers fit the first buffer. One that does not is answered by its
    // length, and the same program is run again with that much room.
    var text: []u8 = &first;
    var needed = run.into(text);
    if (needed > text.len) {
        const more = malloc(needed) orelse {
            say("reflect: out of memory\n");
            return 2;
        };
        text = more[0..needed];
        needed = run.into(text);
        if (needed > text.len) {
            say("reflect: the kernel gave two different answers\n");
            return 2;
        }
    }
    say(text[0..needed]);
    say("\n");
    return 0;
}
