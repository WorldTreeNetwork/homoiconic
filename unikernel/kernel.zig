//! The part of the image that stands where an operating system would: the
//! serial port, memory, random bytes, power, and the system calls the C
//! library and the Lean runtime make. It carries bytes and hands out memory.
//! It does not read a program and it does not evaluate.

const std = @import("std");
const options = @import("options");

extern fn enter_program(entry: usize, stack: usize) noreturn;
extern fn syscall_entry() void;
extern fn load_tables(gdt: *const TablePtr, idt: *const TablePtr, task: u16) void;
extern fn reload_map() void;
extern const fault_stubs: u8;
extern var boot_pd: [2048]u64;
extern const fault_stack_top: u8;
extern const __ehdr_start: u8;
extern const _end: u8;
extern fn _start() void;

// ---- the processor ----

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
const Cpuid = struct { a: u32, b: u32, c: u32, d: u32 };
fn cpuid(leaf: u32, sub: u32) Cpuid {
    var a: u32 = undefined;
    var b: u32 = undefined;
    var c: u32 = undefined;
    var d: u32 = undefined;
    asm volatile ("cpuid"
        : [a] "={eax}" (a),
          [b] "={ebx}" (b),
          [c] "={ecx}" (c),
          [d] "={edx}" (d),
        : [l] "{eax}" (leaf),
          [s] "{ecx}" (sub),
    );
    return .{ .a = a, .b = b, .c = c, .d = d };
}
fn hasSavedState() bool {
    if (options.pretend == .no_saved_state) return false;
    return cpuid(1, 0).c & (1 << 26) != 0; // XSAVE
}
fn hasRandom() bool {
    if (options.pretend == .no_random) return false;
    return cpuid(1, 0).c & (1 << 30) != 0; // RDRAND
}

/// True once the C library has been entered.
var started: bool = false;

/// Eight random bytes from the processor. The instruction says whether it
/// produced a value (the carry flag). It is tried ten times, as its maker
/// advises; after that the image stops. There is no other source.
fn random64() u64 {
    const failing = options.pretend == .random_fails_at_boot or
        (options.pretend == .random_fails_when_served and started);
    var tries: usize = 0;
    while (tries < 10 and !failing) : (tries += 1) {
        var v: u64 = undefined;
        var ok: u8 = undefined;
        asm volatile ("rdrand %[v]; setc %[ok]"
            : [v] "=r" (v),
              [ok] "=r" (ok),
        );
        if (ok != 0) return v;
    }
    puts("reflect: the processor gave no random bytes\n");
    powerOff();
}
fn fillRandom(addr: u64, len: u64) u64 {
    const p: [*]u8 = @ptrFromInt(addr);
    var i: usize = 0;
    while (i < len) {
        var v = random64();
        var k: usize = 0;
        while (k < 8 and i < len) : (k += 1) {
            p[i] = @truncate(v);
            v >>= 8;
            i += 1;
        }
    }
    return len;
}

// ---- the serial port ----

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
    puts(" code ");
    putHex(code);
    puts(" at ");
    putHex(rip);
    puts(" address ");
    putHex(cr2);
    puts(" stack ");
    putHex(rsp);
    const here = @frameAddress();
    const top = @intFromPtr(&fault_stack_top);
    if (here < top and here >= top - 65536) puts(" (on the fault stack)");
    if (vector == 14 and cr2 >= guard_lo and cr2 < guard_hi) {
        // The word just under the unmapped page, so a check can see it is untouched.
        puts(": the stack is full; below the guard: ");
        putHex(@as(*const u64, @ptrFromInt(guard_lo - 8)).*);
    }
    puts("\n");
    powerOff();
}

// ---- memory ----

const page = 4096;
const big_page = 2 << 20;
const stack_size = 16 << 20;
var brk_lo: usize = 0;
var brk_now: usize = 0;
var brk_hi: usize = 0;
var map_next: usize = 0;
var map_hi: usize = 0;
var guard_lo: usize = 0;
var guard_hi: usize = 0;

/// Freed ranges of the map area, sorted by address, no two touching.
const Range = struct { addr: usize, len: usize };
var free_list: [512]Range = undefined;
var free_count: usize = 0;

fn up(x: usize) usize {
    return (x + page - 1) & ~@as(usize, page - 1);
}

fn dropRange(i: usize) void {
    var k = i;
    while (k + 1 < free_count) : (k += 1) free_list[k] = free_list[k + 1];
    free_count -= 1;
}

fn mapAlloc(len: usize) ?usize {
    var i: usize = 0;
    while (i < free_count) : (i += 1) {
        if (free_list[i].len >= len) {
            const a = free_list[i].addr;
            free_list[i].addr += len;
            free_list[i].len -= len;
            if (free_list[i].len == 0) dropRange(i);
            zero(a, len);
            return a;
        }
    }
    if (map_hi - map_next < len) return null;
    const a = map_next;
    map_next += len;
    return a; // memory above map_next has never been handed out and is zero
}

/// Give a range back. A range that is not wholly inside what was handed out
/// is ignored. If the table of ranges is full the range is not reused.
fn mapFree(addr: usize, len: usize) void {
    if (len == 0 or addr < brk_hi or addr + len > map_next or addr & (page - 1) != 0) return;
    var i: usize = 0;
    while (i < free_count and free_list[i].addr < addr) : (i += 1) {}
    const joins_before = i > 0 and free_list[i - 1].addr + free_list[i - 1].len == addr;
    const joins_after = i < free_count and addr + len == free_list[i].addr;
    if (joins_before and joins_after) {
        free_list[i - 1].len += len + free_list[i].len;
        dropRange(i);
    } else if (joins_before) {
        free_list[i - 1].len += len;
    } else if (joins_after) {
        free_list[i].addr = addr;
        free_list[i].len += len;
    } else {
        if (free_count == free_list.len) return;
        var k = free_count;
        while (k > i) : (k -= 1) free_list[k] = free_list[k - 1];
        free_list[i] = .{ .addr = addr, .len = len };
        free_count += 1;
    }
    // The top of the area goes back to never-handed-out, zeroed.
    if (free_count > 0) {
        const last = free_list[free_count - 1];
        if (last.addr + last.len == map_next) {
            zero(last.addr, last.len);
            map_next = last.addr;
            free_count -= 1;
        }
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
const Module = extern struct { addr: u64, size: u64, cmdline_paddr: u64, reserved: u64 };

/// The bytes Cloud Hypervisor was given with --initramfs, if any: one file the
/// program can open, `boot_path`. The layer copies them and does not read them.
const boot_path = "/boot/program";
const boot_limit = 16 << 20;
const boot_fd = 4;
var boot_given = false;
var boot_at: usize = 0;
var boot_len: usize = 0;
var boot_pos: usize = 0;
var boot_open = false;

/// The words the program starts with: its name, then, when bytes were given at
/// boot, the path of those bytes and the words of the command line.
const max_args = 8;
var arg_text: [1024]u8 = .{0} ** 1024;

const Gate = extern struct { lo: u16, sel: u16, ist: u8, attr: u8, mid: u16, hi: u32, zero: u32 };
const TablePtr = extern struct { limit: u16 align(1), base: u64 align(1) };
const Tss = extern struct {
    reserved0: u32 align(1) = 0,
    rsp: [3]u64 align(1) = .{ 0, 0, 0 },
    reserved1: u64 align(1) = 0,
    ist: [7]u64 align(1) = .{ 0, 0, 0, 0, 0, 0, 0 },
    reserved2: u64 align(1) = 0,
    reserved3: u16 align(1) = 0,
    iomap: u16 align(1) = @sizeOf(Tss),
};

var command_line: [1024]u8 = .{0} ** 1024;

export fn reflect_command_line() [*]const u8 {
    return &command_line;
}

var idt: [32]Gate = undefined;
var gdt: [5]u64 = undefined;
var tss: Tss = .{};
var gdt_ptr: TablePtr = undefined;
var idt_ptr: TablePtr = undefined;
var random_bytes: [16]u8 = undefined;

fn stop(comptime why: []const u8) noreturn {
    puts("reflect: " ++ why ++ "\n");
    powerOff();
}

/// Whether `len` bytes at `addr` lie inside one stretch of usable memory in the
/// hypervisor's map, below the 4 GiB that boot mapped.
fn inRam(info: *const StartInfo, addr: u64, len: u64) bool {
    if (addr == 0 or addr > (4 << 30) or (4 << 30) - addr < len) return false;
    const entries: [*]const MemEntry = @ptrFromInt(info.memmap_paddr);
    var i: usize = 0;
    while (i < info.memmap_entries) : (i += 1) {
        const e = entries[i];
        if (e.kind == 1 and e.addr <= addr and addr - e.addr <= e.size and e.size - (addr - e.addr) >= len) return true;
    }
    return false;
}

export fn kmain(info: *const StartInfo) noreturn {
    outb(COM1 + 1, 0);
    outb(COM1 + 3, 3);

    // Faults that can come from a full stack run on their own stack.
    tss.ist[0] = @intFromPtr(&fault_stack_top);
    const tss_at = @intFromPtr(&tss);
    gdt = .{
        0,
        0x00af9a000000ffff, // 0x08: 64-bit code
        0x00cf92000000ffff, // 0x10: data
        (@sizeOf(Tss) - 1) | ((tss_at & 0xffffff) << 16) | (@as(u64, 0x89) << 40) | (((tss_at >> 24) & 0xff) << 56),
        tss_at >> 32, // 0x18: the task segment, two entries
    };
    const stubs = @intFromPtr(&fault_stubs);
    var v: usize = 0;
    while (v < 32) : (v += 1) {
        const h = stubs + v * 16;
        idt[v] = .{
            .lo = @truncate(h),
            .sel = 0x08,
            .ist = if (v == 8 or v == 12 or v == 14) 1 else 0,
            .attr = 0x8e,
            .mid = @truncate(h >> 16),
            .hi = @truncate(h >> 32),
            .zero = 0,
        };
    }
    gdt_ptr = .{ .limit = @sizeOf(@TypeOf(gdt)) - 1, .base = @intFromPtr(&gdt) };
    idt_ptr = .{ .limit = @sizeOf(@TypeOf(idt)) - 1, .base = @intFromPtr(&idt) };
    load_tables(&gdt_ptr, &idt_ptr, 0x18);

    wrmsr(0xC0000081, @as(u64, 0x08) << 32); // STAR: the code segment syscall loads
    wrmsr(0xC0000082, @intFromPtr(&syscall_entry)); // LSTAR
    wrmsr(0xC0000084, 0x400); // SFMASK: clear the direction flag

    // The floor: saved vector state (XSAVE) in an area the syscall entry has
    // room for, and a random instruction. boot.S turned on x87, SSE, and AVX
    // where present, and nothing else, so the area is at most 832 bytes.
    if (!hasSavedState()) stop("this processor has no XSAVE");
    if (cpuid(0xd, 0).b > 4096) stop("the saved state is larger than the room for it");
    if (!hasRandom()) stop("this processor has no random instruction");

    // The memory region that holds this image, up to the 4 GiB that boot mapped.
    var image_end = up(@intFromPtr(&_end));
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
    if (info.magic == 0x336ec578 and info.cmdline_paddr != 0) {
        // A command line is kept whole or refused: a cut one could read as
        // other words than the ones given.
        const src: [*]const u8 = @ptrFromInt(info.cmdline_paddr);
        var n: usize = 0;
        while (n + 1 < command_line.len and src[n] != 0) : (n += 1) command_line[n] = src[n];
        if (src[n] != 0) stop("the command line is longer than " ++ std.fmt.comptimePrint("{d}", .{command_line.len - 1}) ++ " bytes");
    }
    if (ram_end == 0) stop("the machine gave no memory map");
    if (ram_end > (4 << 30)) ram_end = 4 << 30;

    // Bytes given at boot lie wherever the hypervisor put them, which is where
    // the stack will be. Nothing has been written there yet: this code runs on
    // the boot stack. Move them to just above the image and clear where they were.
    // Cloud Hypervisor hands over at most one file; the check reaches the other
    // two refusals with `pretend`.
    const nr_modules = if (options.pretend == .two_modules and info.nr_modules == 1) 2 else info.nr_modules;
    const modlist_paddr = if (options.pretend == .module_list_outside) ram_end else info.modlist_paddr;
    if (info.magic == 0x336ec578 and nr_modules > 1) stop("more than one file was given at boot");
    if (info.magic == 0x336ec578 and nr_modules == 1) {
        if (!inRam(info, modlist_paddr, @sizeOf(Module))) stop("the list of files given at boot is not in usable memory");
        const m = @as(*align(1) const Module, @ptrFromInt(modlist_paddr)).*;
        if (m.size > boot_limit) stop("the program given at boot is too large");
        const len: usize = @intCast(m.size);
        if (m.addr < image_end + len or m.addr > ram_end or ram_end - m.addr < len)
            stop("the program given at boot is not in usable memory");
        const from: [*]u8 = @ptrFromInt(m.addr);
        const to: [*]u8 = @ptrFromInt(image_end);
        var n: usize = 0;
        while (n < len) : (n += 1) {
            to[n] = from[n];
            from[n] = 0;
        }
        boot_given = true;
        boot_at = image_end;
        boot_len = len;
        image_end = up(image_end + len);
    }

    // From the top: the stack, then one unmapped 2 MiB page under it.
    const stack_top = ram_end & ~@as(usize, big_page - 1);
    if (stack_top < image_end + stack_size + 2 * big_page + (16 << 20)) stop("not enough memory");
    guard_hi = stack_top - stack_size;
    guard_lo = guard_hi - big_page;
    boot_pd[guard_lo / big_page] = 0;
    reload_map();

    brk_lo = image_end;
    brk_now = image_end;
    brk_hi = up(image_end + (guard_lo - image_end) / 4);
    map_next = brk_hi;
    map_hi = guard_lo;

    _ = fillRandom(@intFromPtr(&random_bytes), random_bytes.len);

    // What the C library expects on entry: argc, argv, envp, auxv.
    const ehdr = @intFromPtr(&__ehdr_start);
    const phoff = @as(*align(1) const u64, @ptrFromInt(ehdr + 32)).*;
    const phnum = @as(*align(1) const u16, @ptrFromInt(ehdr + 56)).*;
    const name: [*:0]const u8 = "reflect";
    const path: [*:0]const u8 = boot_path;
    var args: [max_args + 2]usize = undefined;
    var argc: usize = 0;
    args[argc] = @intFromPtr(name);
    argc += 1;
    if (boot_given) {
        args[argc] = @intFromPtr(path);
        argc += 1;
        // The command line's words, each ended by a zero byte. The last byte
        // of arg_text is never written, so the last word is ended too.
        var at: usize = 0;
        var in_word = false;
        while (at + 1 < arg_text.len and command_line[at] != 0) : (at += 1) {
            const c = command_line[at];
            if (c == ' ' or c == '\t' or c == '\n') {
                in_word = false;
                continue;
            }
            arg_text[at] = c;
            if (!in_word) {
                if (argc == max_args) stop("the command line has too many words");
                args[argc] = @intFromPtr(&arg_text[at]);
                argc += 1;
                in_word = true;
            }
        }
    }
    const tail = [_]usize{
        0, // envp
        3, ehdr + phoff, // AT_PHDR
        4, 56, // AT_PHENT
        5, phnum, // AT_PHNUM
        6, page, // AT_PAGESZ
        9, @intFromPtr(&_start), // AT_ENTRY
        23, 0, // AT_SECURE
        25, @intFromPtr(&random_bytes), // AT_RANDOM
        0,  0,
    };
    // The stack pointer is a multiple of 16 where argc lies.
    const sp = (stack_top - 4096) & ~@as(usize, 15);
    const dst: [*]usize = @ptrFromInt(sp);
    dst[0] = argc;
    var i: usize = 0;
    while (i < argc) : (i += 1) dst[1 + i] = args[i];
    dst[1 + argc] = 0;
    i = 0;
    while (i < tail.len) : (i += 1) dst[2 + argc + i] = tail[i];
    started = true;
    enter_program(@intFromPtr(&_start), sp);
}

// ---- system calls ----

const Frame = extern struct { nr: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64, a6: u64 };

fn err(e: u64) u64 {
    return @bitCast(-@as(i64, @intCast(e)));
}
const ENOENT = 2;
const EACCES = 13;
const EBADF = 9;
const EAGAIN = 11;
const ENOMEM = 12;
const EINVAL = 22;
const ENOTTY = 25;
const ENOSYS = 38;

const random_fd = 3;
const Iovec = extern struct { base: [*]const u8, len: usize };
const Timespec = extern struct { sec: i64, nsec: i64 };

const probe_call = 1000;

/// Overwrite what a system call must give back unchanged: the vector
/// registers and the floating-point control words. The probe sets them,
/// makes this call, and looks again.
fn spoil() void {
    var words: [2]u32 = .{ 0x1f80, 0x037f };
    asm volatile (
        \\ pcmpeqd %%xmm0, %%xmm0
        \\ movdqa %%xmm0, %%xmm1
        \\ movdqa %%xmm0, %%xmm2
        \\ movdqa %%xmm0, %%xmm3
        \\ movdqa %%xmm0, %%xmm4
        \\ movdqa %%xmm0, %%xmm5
        \\ movdqa %%xmm0, %%xmm6
        \\ movdqa %%xmm0, %%xmm7
        \\ movdqa %%xmm0, %%xmm8
        \\ movdqa %%xmm0, %%xmm9
        \\ movdqa %%xmm0, %%xmm10
        \\ movdqa %%xmm0, %%xmm11
        \\ movdqa %%xmm0, %%xmm12
        \\ movdqa %%xmm0, %%xmm13
        \\ movdqa %%xmm0, %%xmm14
        \\ movdqa %%xmm0, %%xmm15
        \\ ldmxcsr (%[w])
        \\ fninit
        \\ fldcw 4(%[w])
        :
        : [w] "r" (&words),
        : .{ .xmm0 = true, .xmm1 = true, .xmm2 = true, .xmm3 = true, .xmm4 = true, .xmm5 = true, .xmm6 = true, .xmm7 = true, .xmm8 = true, .xmm9 = true, .xmm10 = true, .xmm11 = true, .xmm12 = true, .xmm13 = true, .xmm14 = true, .xmm15 = true, .memory = true });
    if (cpuid(1, 0).c & (1 << 28) != 0) {
        asm volatile (
            \\ vxorps %%ymm0, %%ymm0, %%ymm0
            \\ vmovdqa %%ymm0, %%ymm1
            \\ vmovdqa %%ymm0, %%ymm2
            \\ vmovdqa %%ymm0, %%ymm3
            \\ vmovdqa %%ymm0, %%ymm4
            \\ vmovdqa %%ymm0, %%ymm5
            \\ vmovdqa %%ymm0, %%ymm6
            \\ vmovdqa %%ymm0, %%ymm7
            \\ vmovdqa %%ymm0, %%ymm8
            \\ vmovdqa %%ymm0, %%ymm9
            \\ vmovdqa %%ymm0, %%ymm10
            \\ vmovdqa %%ymm0, %%ymm11
            \\ vmovdqa %%ymm0, %%ymm12
            \\ vmovdqa %%ymm0, %%ymm13
            \\ vmovdqa %%ymm0, %%ymm14
            \\ vmovdqa %%ymm0, %%ymm15
            ::: .{ .ymm0 = true, .ymm1 = true, .ymm2 = true, .ymm3 = true, .ymm4 = true, .ymm5 = true, .ymm6 = true, .ymm7 = true, .ymm8 = true, .ymm9 = true, .ymm10 = true, .ymm11 = true, .ymm12 = true, .ymm13 = true, .ymm14 = true, .ymm15 = true });
    }
}

fn isPath(path: [*:0]const u8, comptime want: []const u8) bool {
    var i: usize = 0;
    while (i < want.len) : (i += 1) if (path[i] != want[i]) return false;
    return path[want.len] == 0;
}

fn notProvided(nr: u64) u64 {
    puts("reflect: system call ");
    putDec(nr);
    puts(" is not provided\n");
    return err(ENOSYS);
}

export fn syscall_dispatch(f: *const Frame) u64 {
    // The check builds one image that lacks a call, to see that it is noticed.
    if (options.omit_call) |n| if (f.nr == n) return notProvided(n);
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
        9 => { // mmap: memory only, no files
            const len = up(f.a2);
            const flags = f.a4;
            if (flags & 0x20 == 0) return err(ENOSYS); // not MAP_ANONYMOUS
            if (flags & 0x10 != 0) { // MAP_FIXED: only over memory already handed out
                if (f.a1 < brk_hi or f.a1 + len > map_next or f.a1 & (page - 1) != 0) return err(ENOMEM);
                zero(f.a1, len);
                return f.a1;
            }
            return mapAlloc(len) orelse err(ENOMEM);
        },
        11 => { // munmap
            mapFree(f.a1, up(f.a2));
            return 0;
        },
        10, 28 => return 0, // mprotect, madvise: one address space, nothing to change
        25 => return err(ENOMEM), // mremap: the caller copies instead
        158 => { // arch_prctl
            if (f.a1 == 0x1002) { // set the thread pointer
                wrmsr(0xC0000100, f.a2);
                return 0;
            }
            return err(EINVAL);
        },
        218, 39, 186 => return 1, // set_tid_address, getpid, gettid
        273, 13, 14, 131 => return 0, // set_robust_list, signal set-up
        334 => return err(ENOSYS), // rseq: the C library does without
        302 => { // prlimit64: the stack's size, no other limit
            if (f.a4 != 0) {
                const out: [*]u64 = @ptrFromInt(f.a4);
                const lim: u64 = if (f.a2 == 3) stack_size - (1 << 20) else ~@as(u64, 0);
                out[0] = lim;
                out[1] = lim;
            }
            return 0;
        },
        204 => { // sched_getaffinity: one processor
            if (f.a2 < 8) return err(EINVAL);
            @as(*align(1) u64, @ptrFromInt(f.a3)).* = 1;
            return 8;
        },
        318 => return fillRandom(f.a1, f.a2), // getrandom
        2, 257 => { // open, openat: the random source, and the bytes given at boot
            const path: [*:0]const u8 = @ptrFromInt(if (f.nr == 2) f.a1 else f.a2);
            if (isPath(path, "/dev/urandom")) return random_fd;
            if (boot_given and !boot_open and isPath(path, boot_path)) {
                const flags = if (f.nr == 2) f.a2 else f.a3;
                if (flags & 3 != 0) return err(EACCES); // read only
                boot_open = true;
                boot_pos = 0;
                return boot_fd;
            }
            return err(ENOENT);
        },
        0 => { // read
            if (f.a1 == boot_fd and boot_open) {
                const left = boot_len - boot_pos;
                const n: usize = if (f.a3 < left) @intCast(f.a3) else left;
                const from: [*]const u8 = @ptrFromInt(boot_at + boot_pos);
                const to: [*]u8 = @ptrFromInt(f.a2);
                var i: usize = 0;
                while (i < n) : (i += 1) to[i] = from[i];
                boot_pos += n;
                return n;
            }
            if (f.a1 != random_fd) return err(EBADF);
            return fillRandom(f.a2, f.a3);
        },
        3 => { // close
            if (f.a1 == boot_fd and boot_open) {
                boot_open = false;
                return 0;
            }
            return if (f.a1 == random_fd) 0 else err(EBADF);
        },
        5 => { // fstat: a character device, or the bytes given at boot
            if (f.a1 == boot_fd and boot_open) {
                zero(f.a2, 144);
                @as(*align(1) u32, @ptrFromInt(f.a2 + 24)).* = 0o100444;
                @as(*align(1) u64, @ptrFromInt(f.a2 + 48)).* = boot_len;
                return 0;
            }
            if (f.a1 > random_fd) return err(EBADF);
            zero(f.a2, 144);
            @as(*align(1) u32, @ptrFromInt(f.a2 + 24)).* = 0o020666;
            return 0;
        },
        228 => { // clock_gettime: a stand-in, processor ticks at an assumed rate
            const ts: *align(1) Timespec = @ptrFromInt(f.a2);
            const ns = if (options.pretend == .clock_stuck) 0 else rdtsc() / 3;
            ts.* = .{ .sec = @intCast(ns / 1_000_000_000), .nsec = @intCast(ns % 1_000_000_000) };
            return 0;
        },
        229 => { // clock_getres
            if (f.a2 != 0) @as(*align(1) Timespec, @ptrFromInt(f.a2)).* = .{ .sec = 0, .nsec = 1 };
            return 0;
        },
        99 => { // sysinfo: only the memory totals are filled in
            zero(f.a1, 112);
            const words: [*]align(1) u64 = @ptrFromInt(f.a1);
            words[4] = map_hi - brk_lo; // totalram
            words[5] = map_hi - map_next; // freeram
            @as(*align(1) u32, @ptrFromInt(f.a1 + 104)).* = 1; // mem_unit
            return 0;
        },
        202 => { // futex: one thread, so nothing ever waits
            const op = f.a2 & 0x7f;
            if (op == 0 or op == 9) return err(EAGAIN);
            return 0;
        },
        16 => return err(ENOTTY), // ioctl: no terminal
        8, 72 => return err(EBADF), // lseek, fcntl
        89, 267, 262, 4, 21 => return err(ENOENT), // readlink, stat, access: no files
        234, 62, 200 => { // tgkill, kill, tkill: the program gave up
            puts("reflect: aborted\n");
            powerOff();
        },
        60, 231 => { // exit, exit_group
            puts("reflect: exit ");
            putDec(f.a1);
            puts("\n");
            powerOff();
        },
        probe_call => { // only in an image built for the check
            if (!options.probe) return notProvided(f.nr);
            if (f.a1 == 0) return guard_hi;
            spoil();
            return 77;
        },
        else => return notProvided(f.nr),
    }
}
