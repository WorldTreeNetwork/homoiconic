//! The program the image runs. It holds the bytes of one program's source,
//! hands them to the kernel, and writes the text that comes back. It does not
//! read the program and it does not look at the answer.

const program = @import("program");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_run(source: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64) usize;
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

pub export fn main() c_int {
    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0) {
        say("reflect: the kernel did not start\n");
        return 2;
    }
    // Most answers fit the first buffer. One that does not is answered by its
    // length, and the same program is run again with that much room.
    var text: []u8 = &first;
    var needed = reflect_run(program.source.ptr, program.source.len, text.ptr, text.len, program.budget);
    if (needed > text.len) {
        const more = malloc(needed) orelse {
            say("reflect: out of memory\n");
            return 2;
        };
        text = more[0..needed];
        needed = reflect_run(program.source.ptr, program.source.len, text.ptr, text.len, program.budget);
        if (needed > text.len) {
            say("reflect: the kernel gave two different answers\n");
            return 2;
        }
    }
    say(text[0..needed]);
    say("\n");
    return 0;
}
