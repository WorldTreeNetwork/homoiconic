//! Programs the check boots in place of the real one, to look at the layer
//! from above. Each says what it saw on the serial port. None calls the kernel.

const which = @import("program").probe;

extern fn write(fd: c_int, buf: [*]const u8, n: usize) isize;
extern fn syscall(nr: c_long, ...) c_long;
extern fn getrandom(buf: [*]u8, n: usize, flags: c_uint) isize;
extern fn open(path: [*:0]const u8, flags: c_int, ...) c_int;
extern fn read(fd: c_int, buf: [*]u8, n: usize) isize;
extern fn probe_preserve() u64;

export fn initialize_libuv() void {}

fn say(s: []const u8) void {
    _ = write(1, s.ptr, s.len);
}
fn sayHex(v: u64) void {
    var buf: [18]u8 = undefined;
    buf[0] = '0';
    buf[1] = 'x';
    var i: usize = 0;
    while (i < 16) : (i += 1) buf[2 + i] = "0123456789abcdef"[@as(usize, @truncate((v >> @as(u6, @truncate(60 - 4 * i))) & 15))];
    say(&buf);
}

const sentinel: u64 = 0x5eed5eed5eed5eed;
const guard_size = 2 << 20;

pub export fn main() c_int {
    switch (which) {
        // Registers, flags, the red zone and the vector state across a system
        // call whose handler overwrites the vector state.
        .preserve => {
            const lost = probe_preserve();
            if (lost == 0) {
                say("probe: a system call gave back the caller's state\n");
                return 0;
            }
            say("probe: a system call lost state, check ");
            sayHex(lost);
            say("\n");
            return 1;
        },
        // Touch the last word of the unmapped page under the stack.
        .guard => {
            const guard_hi: usize = @intCast(syscall(1000, @as(c_long, 0)));
            const below: *volatile u64 = @ptrFromInt(guard_hi - guard_size - 8);
            below.* = sentinel;
            say("probe: touching ");
            sayHex(guard_hi - 8);
            say("\n");
            const inside: *volatile u64 = @ptrFromInt(guard_hi - 8);
            inside.* = 1;
            say("probe: the guard did not stop the write\n");
            return 1;
        },
        // The three ways a program gets random bytes after start.
        .random => {
            var a: [32]u8 = undefined;
            var b: [32]u8 = undefined;
            var c: [32]u8 = undefined;
            if (getrandom(&a, a.len, 0) != a.len or getrandom(&b, b.len, 0) != b.len) {
                say("probe: getrandom was short\n");
                return 1;
            }
            const fd = open("/dev/urandom", 0);
            if (fd < 0 or read(fd, &c, c.len) != c.len) {
                say("probe: the random file was short\n");
                return 1;
            }
            var same_ab = true;
            var same_ac = true;
            for (a, b, c) |x, y, z| {
                if (x != y) same_ab = false;
                if (x != z) same_ac = false;
            }
            if (same_ab or same_ac) {
                say("probe: the same random bytes twice\n");
                return 1;
            }
            say("probe: random bytes were served\n");
            return 0;
        },
    }
}
