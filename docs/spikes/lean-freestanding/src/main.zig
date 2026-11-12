// The program the image runs. It holds bytes and calls the kernel; it does not evaluate.
extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_run(program: [*]const u8, length: usize, out: [*]u8, capacity: usize, budget: u64) usize;
extern fn write(fd: c_int, buf: [*]const u8, n: usize) isize;

/// The Lean runtime starts an event-loop thread for input and output when a
/// program initialises. This image has one thread and does no input or output
/// through Lean, so the link sends that call here (`--wrap=initialize_libuv`).
export fn __wrap_initialize_libuv() void {}

const program = @embedFile("factorial.hom");
var out: [65536]u8 = undefined;

fn say(s: []const u8) void {
    _ = write(1, s.ptr, s.len);
}

pub export fn main() c_int {
    say("reflect: starting\n");
    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0) {
        say("reflect: the kernel did not start\n");
        return 2;
    }
    const n = reflect_run(program.ptr, program.len, &out, out.len, 100_000_000);
    if (n > out.len) return 3;
    say(out[0..n]);
    say("\n");
    return 0;
}
