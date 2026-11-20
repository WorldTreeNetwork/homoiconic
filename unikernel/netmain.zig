//! The network image's program: start Lean, then serve. It does not read a
//! program and it does not look at an answer.

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn net_serve() noreturn;
extern fn write(fd: c_int, buf: [*]const u8, n: usize) isize;
extern fn _exit(status: c_int) noreturn;

export fn initialize_libuv() void {}

pub export fn main() c_int {
    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0) {
        const s = "reflect: the kernel did not start\n";
        _ = write(1, s, s.len);
        return 2;
    }
    net_serve();
}
