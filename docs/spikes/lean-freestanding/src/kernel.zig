// The part of the image that stands where an operating system would: serial
// port, memory, and the few system calls the C library and the Lean runtime
// make. It carries bytes and hands out memory. It does not evaluate.

extern fn enter_program(entry: usize, stack: usize) noreturn;
extern fn syscall_entry() void;
extern const fault_stubs: u8;
extern const __ehdr_start: u8;
extern const _end: u8;
extern fn _start() void;

// ---- ports ----
fn outb(port: u16, v: u8) void {
    asm volatile ("outb %[v], %[p]"
        :
        : [v] "{al}" (v),
          [p] "{dx}" (port),
    );
}
fn inb(port: u16) u8 {
    return asm volatile ("inb %[p], %[r]"
        : [r] "={al}" (-> u8),
        : [p] "{dx}" (port),
    );
}
fn wrmsr(msr: u32, v: u64) void {
    asm volatile ("wrmsr"
        :
        : [m] "{ecx}" (msr),
          [lo] "{eax}" (@as(u32, @truncate(v))),
          [hi] "{edx}" (@as(u32, @truncate(v >> 32))),
    );
}
fn rdtsc() u64 {
    var lo: u32 = undefined;
    var hi: u32 = undefined;
    asm volatile ("rdtsc"
        : [lo] "={eax}" (lo),
          [hi] "={edx}" (hi),
    );
    return (@as(u64, hi) << 32) | lo;
}
fn zero(addr: usize, len: usize) void {
    asm volatile ("rep stosb"
        :
        : [d] "{rdi}" (addr),
          [c] "{rcx}" (len),
          [a] "{al}" (@as(u8, 0)),
        : .{ .rdi = true, .rcx = true, .memory = true });
}

const COM1 = 0x3f8;
fn putc(c: u8) void {
    while (inb(COM1 + 5) & 0x20 == 0) {}
    outb(COM1, c);
}
fn puts(s: []const u8) void {
    var i: usize = 0;
    while (i < s.len) : (i += 1) putc(s[i]);
}
fn putHex(v: u64) void {
    puts("0x");
    var shift: u7 = 64;
    while (shift != 0) {
        shift -= 4;
        putc("0123456789abcdef"[@as(usize, @truncate((v >> @as(u6, @truncate(shift))) & 15))]);
    }
}
fn putDec(v: u64) void {
    var buf: [20]u8 = undefined;
    var i: usize = buf.len;
    var x = v;
    while (true) {
        i -= 1;
        buf[i] = '0' + @as(u8, @truncate(x % 10));
        x /= 10;
        if (x == 0) break;
    }
    while (i < buf.len) : (i += 1) putc(buf[i]);
}

fn powerOff() noreturn {
    outb(0x600, 0x34); // Cloud Hypervisor's ACPI shutdown device: sleep state S5
    while (true) asm volatile ("hlt");
}

export fn fault_report(vector: u64, code: u64, rip: u64, cr2: u64, rsp: u64) noreturn {
    puts("\nreflect: processor fault ");
    putDec(vector);
    puts(" error ");
    putHex(code);
    puts(" at ");
    putHex(rip);
    puts(" address ");
    putHex(cr2);
    puts(" stack ");
    putHex(rsp);
    puts("\n");
    powerOff();
}

// ---- memory ----
const page = 4096;
const stack_size = 16 << 20;
var brk_lo: usize = 0;
var brk_now: usize = 0;
var brk_hi: usize = 0;
var map_next: usize = 0;
var map_hi: usize = 0;

const Range = struct { addr: usize, len: usize };
var free_list: [256]Range = undefined;
var free_count: usize = 0;

fn up(x: usize) usize {
    return (x + page - 1) & ~@as(usize, page - 1);
}

fn mapAlloc(len: usize) ?usize {
    var i: usize = 0;
    while (i < free_count) : (i += 1) {
        if (free_list[i].len >= len) {
            const a = free_list[i].addr;
            free_list[i].addr += len;
            free_list[i].len -= len;
            if (free_list[i].len == 0) {
                free_count -= 1;
                free_list[i] = free_list[free_count];
            }
            zero(a, len);
            return a;
        }
    }
    if (map_hi - map_next < len) return null;
    const a = map_next;
    map_next += len;
    return a; // memory never handed out before is zero
}

fn mapFree(addr: usize, len: usize) void {
    if (addr + len == map_next) {
        zero(addr, len);
        map_next = addr;
        return;
    }
    if (free_count < free_list.len) {
        free_list[free_count] = .{ .addr = addr, .len = len };
        free_count += 1;
    }
}

// ---- the start ----
const StartInfo = extern struct {
    magic: u32,
    version: u32,
    flags: u32,
    nr_modules: u32,
    modlist_paddr: u64,
    cmdline_paddr: u64,
    rsdp_paddr: u64,
    memmap_paddr: u64,
    memmap_entries: u32,
    reserved: u32,
};
const MemEntry = extern struct { addr: u64, size: u64, kind: u32, reserved: u32 };

const Gate = extern struct { lo: u16, sel: u16, ist: u8, attr: u8, mid: u16, hi: u32, zero: u32 };
var idt: [32]Gate = undefined;
const Idtr = extern struct { limit: u16 align(1), base: u64 align(1) };
var idtr: Idtr = undefined;

var random_bytes: [16]u8 = undefined;
var trace: bool = false;

export fn kmain(info: *const StartInfo) noreturn {
    outb(COM1 + 1, 0);
    outb(COM1 + 3, 3);
    puts("reflect: booted\n");

    const stubs = @intFromPtr(&fault_stubs);
    var v: usize = 0;
    while (v < 32) : (v += 1) {
        const h = stubs + v * 16;
        idt[v] = .{
            .lo = @truncate(h),
            .sel = 0x08,
            .ist = 0,
            .attr = 0x8e,
            .mid = @truncate(h >> 16),
            .hi = @truncate(h >> 32),
            .zero = 0,
        };
    }
    idtr = .{ .limit = @sizeOf(@TypeOf(idt)) - 1, .base = @intFromPtr(&idt) };
    asm volatile ("lidt (%[p])"
        :
        : [p] "r" (&idtr),
    );

    wrmsr(0xC0000081, @as(u64, 0x08) << 32); // STAR
    wrmsr(0xC0000082, @intFromPtr(&syscall_entry)); // LSTAR
    wrmsr(0xC0000084, 0x400); // SFMASK: clear the direction flag

    // The memory that holds this image, up to 4 GiB (what boot mapped).
    const image_end = up(@intFromPtr(&_end));
    var ram_end: usize = 0;
    if (info.magic == 0x336ec578 and info.version >= 1) {
        const entries: [*]const MemEntry = @ptrFromInt(info.memmap_paddr);
        var i: usize = 0;
        while (i < info.memmap_entries) : (i += 1) {
            const e = entries[i];
            if (e.kind == 1 and e.addr <= image_end and e.addr + e.size > image_end)
                ram_end = e.addr + e.size;
        }
    }
    if (ram_end == 0) {
        puts("reflect: no memory map\n");
        powerOff();
    }
    if (ram_end > (4 << 30)) ram_end = 4 << 30;
    puts("reflect: memory to ");
    putHex(ram_end);
    puts("\n");

    const stack_top = ram_end & ~@as(usize, 15);
    const usable_hi = ram_end - stack_size;
    brk_lo = image_end;
    brk_now = image_end;
    brk_hi = up(image_end + (usable_hi - image_end) / 4);
    map_next = brk_hi;
    map_hi = usable_hi & ~@as(usize, page - 1);

    var t = rdtsc();
    for (&random_bytes) |*b| {
        t = t *% 6364136223846793005 +% 1442695040888963407;
        b.* = @truncate(t >> 33);
    }

    // What the C library expects on entry: argc, argv, envp, auxv.
    const ehdr = @intFromPtr(&__ehdr_start);
    const phoff = @as(*align(1) const u64, @ptrFromInt(ehdr + 32)).*;
    const phnum = @as(*align(1) const u16, @ptrFromInt(ehdr + 56)).*;
    const name: [*:0]const u8 = "reflect";
    const words = [_]usize{
        1,                         @intFromPtr(name),             0, // argc, argv
        0, // envp
        3,                         ehdr + phoff, // AT_PHDR
        4,                         56, // AT_PHENT
        5,                         phnum, // AT_PHNUM
        6,                         page, // AT_PAGESZ
        9,                         @intFromPtr(&_start), // AT_ENTRY
        23,                        0, // AT_SECURE
        25,                        @intFromPtr(&random_bytes), // AT_RANDOM
        0,                         0,
    };
    const sp = (stack_top - 4096) & ~@as(usize, 15);
    const dst: [*]usize = @ptrFromInt(sp);
    var i: usize = 0;
    while (i < words.len) : (i += 1) dst[i] = words[i];
    enter_program(@intFromPtr(&_start), sp);
}

// ---- system calls ----
const random_fd = 3;

/// Not a random source anyone should trust: the processor's time counter,
/// stirred. The spike needs bytes here, not secrecy.
fn fillRandom(addr: u64, len: u64) u64 {
    const p: [*]u8 = @ptrFromInt(addr);
    var t = rdtsc();
    var i: usize = 0;
    while (i < len) : (i += 1) {
        t = t *% 6364136223846793005 +% 1442695040888963407 +% rdtsc();
        p[i] = @truncate(t >> 33);
    }
    return len;
}

const Frame = extern struct { nr: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64, a6: u64 };

fn err(e: u64) u64 {
    return @bitCast(-@as(i64, @intCast(e)));
}
const ENOENT = 2;
const EBADF = 9;
const EAGAIN = 11;
const ENOMEM = 12;
const EINVAL = 22;
const ENOTTY = 25;
const ENOSYS = 38;

const Iovec = extern struct { base: [*]const u8, len: usize };
const Timespec = extern struct { sec: i64, nsec: i64 };

export fn syscall_dispatch(f: *const Frame) u64 {
    if (trace) {
        puts("[sys ");
        putDec(f.nr);
        puts("]");
    }
    switch (f.nr) {
        1 => { // write
            if (f.a1 != 1 and f.a1 != 2) return err(EBADF);
            puts(@as([*]const u8, @ptrFromInt(f.a2))[0..f.a3]);
            return f.a3;
        },
        20 => { // writev
            if (f.a1 != 1 and f.a1 != 2) return err(EBADF);
            const iov: [*]const Iovec = @ptrFromInt(f.a2);
            var total: usize = 0;
            var i: usize = 0;
            while (i < f.a3) : (i += 1) {
                puts(iov[i].base[0..iov[i].len]);
                total += iov[i].len;
            }
            return total;
        },
        12 => { // brk
            const want = f.a1;
            if (want >= brk_lo and want <= brk_hi) {
                if (want < brk_now) zero(want, brk_now - want);
                brk_now = want;
            }
            return brk_now;
        },
        9 => { // mmap
            const len = up(f.a2);
            const flags = f.a4;
            if (@as(i64, @bitCast(f.a5)) != -1 and flags & 0x20 == 0) return err(ENOSYS);
            if (flags & 0x10 != 0) { // MAP_FIXED, over memory already handed out
                zero(f.a1, len);
                return f.a1;
            }
            return mapAlloc(len) orelse err(ENOMEM);
        },
        11 => { // munmap
            mapFree(f.a1, up(f.a2));
            return 0;
        },
        10, 28 => return 0, // mprotect, madvise
        25 => return err(ENOMEM), // mremap
        158 => { // arch_prctl
            if (f.a1 == 0x1002) {
                wrmsr(0xC0000100, f.a2);
                return 0;
            }
            return err(EINVAL);
        },
        218, 39, 186 => return 1, // set_tid_address, getpid, gettid
        273, 13, 14, 131 => return 0, // set_robust_list, signals
        334 => return err(ENOSYS), // rseq
        302 => { // prlimit64
            if (f.a4 != 0) {
                const out: [*]u64 = @ptrFromInt(f.a4);
                const lim: u64 = if (f.a2 == 3) stack_size - (1 << 20) else ~@as(u64, 0);
                out[0] = lim;
                out[1] = lim;
            }
            return 0;
        },
        318 => return fillRandom(f.a1, f.a2), // getrandom
        2, 257 => { // open, openat: the one file is the random source
            const path: [*:0]const u8 = @ptrFromInt(if (f.nr == 2) f.a1 else f.a2);
            const want = "/dev/urandom";
            var i: usize = 0;
            while (i < want.len) : (i += 1) if (path[i] != want[i]) return err(ENOENT);
            if (path[want.len] != 0) return err(ENOENT);
            return random_fd;
        },
        0 => { // read
            if (f.a1 != random_fd) return err(EBADF);
            return fillRandom(f.a2, f.a3);
        },
        3 => return if (f.a1 == random_fd) 0 else err(EBADF), // close
        5 => { // fstat: a character device
            if (f.a1 != random_fd and f.a1 > 2) return err(EBADF);
            zero(f.a2, 144);
            @as(*u32, @ptrFromInt(f.a2 + 24)).* = 0o020666;
            return 0;
        },
        228 => { // clock_gettime, uncalibrated
            const ts: *Timespec = @ptrFromInt(f.a2);
            const ns = rdtsc() / 3;
            ts.* = .{ .sec = @intCast(ns / 1_000_000_000), .nsec = @intCast(ns % 1_000_000_000) };
            return 0;
        },
        229 => { // clock_getres
            if (f.a2 != 0) @as(*Timespec, @ptrFromInt(f.a2)).* = .{ .sec = 0, .nsec = 1 };
            return 0;
        },
        99 => { // sysinfo: only the memory totals are filled in
            zero(f.a1, 112);
            const words: [*]u64 = @ptrFromInt(f.a1);
            words[4] = map_hi - brk_lo; // totalram
            words[5] = map_hi - map_next; // freeram
            @as(*u32, @ptrFromInt(f.a1 + 104)).* = 1; // mem_unit
            return 0;
        },
        234, 62, 200 => { // tgkill, kill, tkill: the program gave up
            puts("reflect: aborted\n");
            powerOff();
        },
        202 => { // futex: one thread, so nothing ever waits
            const op = f.a2 & 0x7f;
            if (op == 0 or op == 9) return err(EAGAIN);
            return 0;
        },
        16 => return err(ENOTTY), // ioctl
        8, 72 => return err(EBADF), // lseek, fcntl
        89, 267, 262, 4, 21 => return err(ENOENT), // readlink, stat, access
        60, 231 => { // exit
            puts("reflect: exit ");
            putDec(f.a1);
            puts("\n");
            powerOff();
        },
        else => {
            puts("reflect: system call ");
            putDec(f.nr);
            puts(" is not provided\n");
            return err(ENOSYS);
        },
    }
}
