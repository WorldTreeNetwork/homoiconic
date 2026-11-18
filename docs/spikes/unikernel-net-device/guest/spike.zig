//! Minimal PVH guest: discover CH54 virtio-net, negotiate VERSION_1 and MAC
//! only, and answer one ARP request plus one UDP datagram. Not the Lean image.

const qsz: u16 = 8;
const buf_len: u32 = 2048;
const hdr_len: u32 = 12;
const guest_ip = [4]u8{ 10, 99, 0, 2 };
const udp_port: u16 = 9000;

export fn kmain(_: u64) void {
    serialInit();
    say("spike: boot\n");
    const nic = discover() orelse {
        say("spike: fail no virtio-net\n");
        halt();
    };
    say("pci: ");
    hex8(nic.bus);
    say(" ");
    hex8(nic.dev);
    say(" ");
    hex8(nic.func);
    say(" vendor ");
    hex16(nic.vendor);
    say(" device ");
    hex16(nic.device);
    say("\n");
    var i: usize = 0;
    while (i < nic.nbars) : (i += 1) {
        say("bar ");
        hex8(@truncate(i));
        say(": ");
        hex64(nic.bars[i].addr);
        say(" len ");
        hex64(nic.bars[i].len);
        say("\n");
        if (nic.bars[i].addr < 512 * 1024 * 1024) {
            say("spike: fail BAR overlaps guest RAM\n");
            halt();
        }
        mapUncached(nic.bars[i].addr, nic.bars[i].len);
    }
    if (!drive(nic)) halt();
    say("spike: ok\n");
    powerOff();
}

const Bar = struct { addr: u64, len: u64 };
const Nic = struct {
    bus: u8,
    dev: u8,
    func: u8,
    vendor: u16,
    device: u16,
    bars: [6]Bar,
    nbars: usize,
    common: u64,
    notify: u64,
    notify_mul: u32,
    devcfg: u64,
    isr: u64,
};

fn discover() ?Nic {
    var bus: u16 = 0;
    while (bus < 256) : (bus += 1) {
        var dev: u16 = 0;
        while (dev < 32) : (dev += 1) {
            var func: u16 = 0;
            while (func < 8) : (func += 1) {
                const v = pcird(bus, dev, func, 0);
                if (v == 0xffffffff) {
                    if (func == 0) break;
                    continue;
                }
                const vendor: u16 = @truncate(v);
                const device: u16 = @truncate(v >> 16);
                if (vendor == 0x1af4 and device == 0x1041) {
                    return readNic(@truncate(bus), @truncate(dev), @truncate(func), vendor, device);
                }
                if (vendor == 0x1af4) {
                    say("pci other: ");
                    hex16(device);
                    say("\n");
                }
                if (func == 0) {
                    const hdr = pcird(bus, dev, func, 0x0c);
                    if ((hdr >> 16) & 0x80 == 0) break;
                }
            }
        }
    }
    return null;
}

fn readNic(bus: u8, dev: u8, func: u8, vendor: u16, device: u16) ?Nic {
    var nic = Nic{
        .bus = bus,
        .dev = dev,
        .func = func,
        .vendor = vendor,
        .device = device,
        .bars = undefined,
        .nbars = 0,
        .common = 0,
        .notify = 0,
        .notify_mul = 0,
        .devcfg = 0,
        .isr = 0,
    };
    var bar_i: u8 = 0;
    while (bar_i < 6) : (bar_i += 1) {
        const off: u16 = 0x10 + @as(u16, bar_i) * 4;
        const raw = pcird(bus, dev, func, off);
        if (raw & 1 != 0) {
            say("spike: fail IO BAR\n");
            return null;
        }
        const is64 = (raw & 0x6) == 0x4;
        var addr: u64 = raw & 0xfffffff0;
        if (is64) {
            if (bar_i == 5) return null;
            const hi = pcird(bus, dev, func, off + 4);
            addr |= @as(u64, hi) << 32;
        }
        pcwr(bus, dev, func, off, 0xffffffff);
        var mask: u64 = pcird(bus, dev, func, off) & 0xfffffff0;
        if (is64) {
            pcwr(bus, dev, func, off + 4, 0xffffffff);
            mask |= @as(u64, pcird(bus, dev, func, off + 4)) << 32;
            pcwr(bus, dev, func, off + 4, @truncate(addr >> 32));
        }
        pcwr(bus, dev, func, off, raw);
        const len = if (mask == 0) 0 else (~mask +% 1);
        if (addr != 0 and len != 0) {
            nic.bars[nic.nbars] = .{ .addr = addr, .len = len };
            nic.nbars += 1;
        }
        if (is64) bar_i += 1;
    }
    const cmd = pcird(bus, dev, func, 0x04);
    pcwr(bus, dev, func, 0x04, (cmd & 0xffff0000) | 0x6);

    const status = pcird(bus, dev, func, 0x04) >> 16;
    if (status & 0x10 == 0) return null;
    var cap: u16 = @truncate(pcird(bus, dev, func, 0x34) & 0xfc);
    var guard: u8 = 0;
    while (cap != 0 and guard < 48) : (guard += 1) {
        const c0 = pcird(bus, dev, func, cap);
        const id: u8 = @truncate(c0);
        const next: u16 = @truncate((c0 >> 8) & 0xfc);
        const len: u8 = @truncate(c0 >> 16);
        if (id == 0x09 and len >= 16) {
            const cfg_type: u8 = @truncate(c0 >> 24);
            const c1 = pcird(bus, dev, func, cap + 4);
            const bar: u8 = @truncate(c1);
            const offset = pcird(bus, dev, func, cap + 8);
            const base = barAddr(&nic, bar) orelse return null;
            const mmio = base + offset;
            if (cfg_type == 1) nic.common = mmio;
            if (cfg_type == 2) {
                nic.notify = mmio;
                nic.notify_mul = pcird(bus, dev, func, cap + 16);
            }
            if (cfg_type == 3) nic.isr = mmio;
            if (cfg_type == 4) nic.devcfg = mmio;
        }
        cap = next;
    }
    if (nic.common == 0 or nic.notify == 0 or nic.devcfg == 0) {
        say("spike: fail missing virtio cap\n");
        return null;
    }
    return nic;
}

fn barAddr(nic: *const Nic, index: u8) ?u64 {
    // PCI BAR index, not the compressed list. Re-read the BAR register.
    const raw = pcird(nic.bus, nic.dev, nic.func, 0x10 + @as(u16, index) * 4);
    if (raw & 1 != 0) return null;
    var addr: u64 = raw & 0xfffffff0;
    if ((raw & 0x6) == 0x4) {
        addr |= @as(u64, pcird(nic.bus, nic.dev, nic.func, 0x14 + @as(u16, index) * 4)) << 32;
    }
    if (addr == 0) return null;
    return addr;
}

fn drive(nic: Nic) bool {
    wr8(nic.common + 20, 0);
    var reset_spin: u32 = 0;
    while (reset_spin < 100000) : (reset_spin += 1) {}
    wr8(nic.common + 20, 1); // ACKNOWLEDGE
    wr8(nic.common + 20, 3); // + DRIVER
    const lo = feat(nic, 0);
    const hi = feat(nic, 1);
    say("features0: ");
    hex32(lo);
    say("\nfeatures1: ");
    hex32(hi);
    say("\n");
    const mac_bit: u32 = 1 << 5;
    const ver_bit: u32 = 1; // bit 32 lives in the high word
    if (lo & mac_bit == 0 or hi & ver_bit == 0) {
        say("spike: fail device omits MAC or VERSION_1\n");
        return false;
    }
    setFeat(nic, 0, mac_bit);
    setFeat(nic, 1, ver_bit);
    wr8(nic.common + 20, 11); // + FEATURES_OK
    if (rd8(nic.common + 20) & 8 == 0) {
        say("spike: fail FEATURES_OK rejected\n");
        return false;
    }
    say("negotiated: MAC VERSION_1\n");
    var mac: [6]u8 = undefined;
    var m: usize = 0;
    while (m < 6) : (m += 1) mac[m] = rd8(nic.devcfg + m);
    say("mac: ");
    var k: usize = 0;
    while (k < 6) : (k += 1) {
        hex8(mac[k]);
        if (k != 5) say(":");
    }
    say("\n");

    const nq = rd16(nic.common + 18);
    say("num_queues: ");
    hex16(nq);
    say("\n");
    if (nq < 2) {
        say("spike: fail fewer than 2 queues\n");
        return false;
    }
    if (!setupQueue(nic, 0, true)) return false;
    if (!setupQueue(nic, 1, false)) return false;
    wr8(nic.common + 20, 15); // + DRIVER_OK
    say("ready\n");

    var saw_arp = false;
    var saw_udp = false;
    while (!(saw_arp and saw_udp)) {
        const got = pollRx(nic, mac);
        if (got == 1 and !saw_arp) {
            saw_arp = true;
            say("arp: replied\n");
        }
        if (got == 2 and !saw_udp) {
            saw_udp = true;
            say("udp: echoed\n");
        }
    }
    return true;
}

const Desc = extern struct { addr: u64, len: u32, flags: u16, next: u16 };
const UsedElem = extern struct { id: u32, len: u32 };
const Avail = extern struct { flags: u16, idx: u16, ring: [qsz]u16, used_event: u16 };
const Used = extern struct { flags: u16, idx: u16, ring: [qsz]UsedElem, avail_event: u16 };

var rx_desc: [qsz]Desc align(16) = undefined;
var rx_avail: Avail align(2) = undefined;
var rx_used: Used align(4) = undefined;
var rx_buf: [qsz][buf_len]u8 align(16) = undefined;
var rx_last: u16 = 0;

var tx_desc: [qsz]Desc align(16) = undefined;
var tx_avail: Avail align(2) = undefined;
var tx_used: Used align(4) = undefined;
var tx_buf: [buf_len]u8 align(16) = undefined;
var tx_last: u16 = 0;

fn setupQueue(nic: Nic, q: u16, rx: bool) bool {
    wr16(nic.common + 22, q);
    const max = rd16(nic.common + 24);
    say(if (rx) "rx_size: " else "tx_size: ");
    hex16(max);
    say("\n");
    if (max < qsz or (max & (max - 1)) != 0) {
        say("spike: fail queue size\n");
        return false;
    }
    wr16(nic.common + 24, qsz);
    const desc = if (rx) &rx_desc else &tx_desc;
    const avail = if (rx) &rx_avail else &tx_avail;
    const used = if (rx) &rx_used else &tx_used;
    @memset(stdMem(desc), 0);
    @memset(stdMem(avail), 0);
    @memset(stdMem(used), 0);
    if (rx) {
        var n: u16 = 0;
        while (n < qsz) : (n += 1) {
            rx_desc[n] = .{
                .addr = @intFromPtr(&rx_buf[n]),
                .len = buf_len,
                .flags = 2, // WRITE
                .next = 0,
            };
            rx_avail.ring[n] = n;
        }
        rx_avail.idx = qsz;
    }
    wr64(nic.common + 32, @intFromPtr(desc));
    wr64(nic.common + 40, @intFromPtr(avail));
    wr64(nic.common + 48, @intFromPtr(used));
    wr16(nic.common + 28, 1);
    const off = rd16(nic.common + 30);
    say(if (rx) "rx_notify: " else "tx_notify: ");
    hex16(off);
    say(" mul ");
    hex32(nic.notify_mul);
    say("\n");
    if (rx) notifyQueue(nic, 0);
    return true;
}

fn notifyQueue(nic: Nic, q: u16) void {
    wr16(nic.common + 22, q);
    const off = rd16(nic.common + 30);
    const addr = nic.notify + @as(u64, off) * nic.notify_mul;
    @as(*align(1) volatile u16, @ptrFromInt(addr)).* = q;
}

fn pollRx(nic: Nic, mac: [6]u8) u8 {
    if (vol16(&rx_used.idx) == rx_last) return 0;
    const slot = rx_last % qsz;
    const id = rx_used.ring[slot].id;
    const len = rx_used.ring[slot].len;
    rx_last += 1;
    var kind: u8 = 0;
    if (id < qsz and len >= hdr_len + 14 and len <= buf_len) {
        const frame: []u8 = rx_buf[id][@intCast(hdr_len)..@intCast(len)];
        kind = handle(frame, mac, nic);
    }
    if (id < qsz) {
        rx_desc[id].addr = @intFromPtr(&rx_buf[id]);
        rx_desc[id].len = buf_len;
        rx_desc[id].flags = 2;
        const a = rx_avail.idx % qsz;
        rx_avail.ring[a] = @truncate(id);
        rx_avail.idx += 1;
        notifyQueue(nic, 0);
    }
    return kind;
}

fn handle(frame: []u8, mac: [6]u8, nic: Nic) u8 {
    if (frame.len < 14) return 0;
    const et = rdbe16(frame[12..14]);
    if (et == 0x0806 and frame.len >= 42) return if (answerArp(frame, mac, nic)) 1 else 0;
    if (et == 0x0800) return if (answerUdp(frame, mac, nic)) 2 else 0;
    return 0;
}

fn answerArp(frame: []const u8, mac: [6]u8, nic: Nic) bool {
    if (frame[14] != 0 or frame[15] != 1) return false;
    if (rdbe16(frame[16..18]) != 0x0800) return false;
    if (frame[18] != 6 or frame[19] != 4) return false;
    if (rdbe16(frame[20..22]) != 1) return false; // request
    if (!eq4(frame[38..42], &guest_ip)) return false;
    var out: [hdr_len + 42]u8 = undefined;
    @memset(out[0..hdr_len], 0);
    var pkt = out[hdr_len..];
    copy6(pkt[0..6], frame[6..12]);
    copy6(pkt[6..12], &mac);
    pkt[12] = 0x08;
    pkt[13] = 0x06;
    @memcpy(pkt[14..20], frame[14..20]);
    pkt[20] = 0;
    pkt[21] = 2; // reply
    copy6(pkt[22..28], &mac);
    @memcpy(pkt[28..32], &guest_ip);
    copy6(pkt[32..38], frame[22..28]);
    @memcpy(pkt[38..42], frame[28..32]);
    return tx(nic, &out);
}

fn answerUdp(frame: []u8, mac: [6]u8, nic: Nic) bool {
    if (frame.len < 14 + 20 + 8) return false;
    if (frame[14] >> 4 != 4) return false;
    const ihl: usize = @as(usize, frame[14] & 0xf) * 4;
    if (ihl < 20 or frame.len < 14 + ihl + 8) return false;
    if (frame[23] != 17) return false;
    if (!eq4(frame[14 + 16 .. 14 + 20], &guest_ip)) return false;
    const udp = 14 + ihl;
    if (rdbe16(frame[udp + 2 .. udp + 4]) != udp_port) return false;
    const ulen = rdbe16(frame[udp + 4 .. udp + 6]);
    if (ulen < 8 or frame.len < udp + ulen) return false;
    const total = hdr_len + 14 + 20 + ulen;
    if (total > buf_len) return false;
    @memset(tx_buf[0..total], 0);
    var pkt = tx_buf[hdr_len .. hdr_len + 14 + 20 + ulen];
    copy6(pkt[0..6], frame[6..12]);
    copy6(pkt[6..12], &mac);
    pkt[12] = 0x08;
    pkt[13] = 0x00;
    pkt[14] = 0x45;
    wrbe16(pkt[16..18], @truncate(20 + ulen));
    pkt[18] = frame[18];
    pkt[19] = frame[19];
    pkt[22] = 64;
    pkt[23] = 17;
    @memcpy(pkt[26..30], &guest_ip);
    @memcpy(pkt[30..34], frame[26..30]);
    const csum = ipChecksum(pkt[14..34]);
    wrbe16(pkt[24..26], csum);
    const sport = rdbe16(frame[udp .. udp + 2]);
    wrbe16(pkt[34..36], udp_port);
    wrbe16(pkt[36..38], sport);
    wrbe16(pkt[38..40], ulen);
    @memcpy(pkt[42 .. 42 + ulen - 8], frame[udp + 8 .. udp + ulen]);
    const uc = udpChecksum(pkt[26..34], pkt[34 .. 34 + ulen]);
    wrbe16(pkt[40..42], if (uc == 0) 0xffff else uc);
    return tx(nic, tx_buf[0..total]);
}

fn tx(nic: Nic, bytes: []const u8) bool {
    if (bytes.len > buf_len) return false;
    if (bytes.ptr != &tx_buf) @memcpy(tx_buf[0..bytes.len], bytes);
    tx_desc[0] = .{
        .addr = @intFromPtr(&tx_buf),
        .len = @truncate(bytes.len),
        .flags = 0,
        .next = 0,
    };
    const slot = tx_avail.idx % qsz;
    tx_avail.ring[slot] = 0;
    tx_avail.idx += 1;
    notifyQueue(nic, 1);
    var spins: u32 = 0;
    while (vol16(&tx_used.idx) == tx_last and spins < 1_000_000) : (spins += 1) {}
    if (vol16(&tx_used.idx) == tx_last) {
        say("spike: fail tx timeout\n");
        return false;
    }
    tx_last = vol16(&tx_used.idx);
    return true;
}

fn ipChecksum(hdr: []const u8) u16 {
    var sum: u32 = 0;
    var i: usize = 0;
    while (i < hdr.len) : (i += 2) {
        if (i == 10) continue; // checksum field
        sum += rdbe16(hdr[i .. i + 2]);
    }
    while (sum >> 16 != 0) sum = (sum & 0xffff) + (sum >> 16);
    return @truncate(~sum);
}

fn udpChecksum(addrs: []const u8, udp: []const u8) u16 {
    var sum: u32 = 0;
    sum += rdbe16(addrs[0..2]);
    sum += rdbe16(addrs[2..4]);
    sum += rdbe16(addrs[4..6]);
    sum += rdbe16(addrs[6..8]);
    sum += 17;
    sum += @as(u32, @truncate(udp.len));
    var i: usize = 0;
    while (i + 1 < udp.len) : (i += 2) {
        if (i == 6) continue;
        sum += rdbe16(udp[i .. i + 2]);
    }
    if (i < udp.len) sum += @as(u32, udp[i]) << 8;
    while (sum >> 16 != 0) sum = (sum & 0xffff) + (sum >> 16);
    return @truncate(~sum);
}

fn eq4(a: []const u8, b: *const [4]u8) bool {
    return a[0] == b[0] and a[1] == b[1] and a[2] == b[2] and a[3] == b[3];
}
fn copy6(d: []u8, s: []const u8) void {
    @memcpy(d[0..6], s[0..6]);
}
fn rdbe16(b: []const u8) u16 {
    return (@as(u16, b[0]) << 8) | b[1];
}
fn wrbe16(b: []u8, v: u16) void {
    b[0] = @truncate(v >> 8);
    b[1] = @truncate(v);
}

fn stdMem(p: anytype) []u8 {
    return @as([*]u8, @ptrCast(p))[0..@sizeOf(@TypeOf(p.*))];
}

// ---- PCI ----

fn pciAddr(bus: u16, dev: u16, func: u16, off: u16) u32 {
    return 0x80000000 | (@as(u32, bus) << 16) | (@as(u32, dev) << 11) | (@as(u32, func) << 8) | (off & 0xfc);
}
fn pcird(bus: u16, dev: u16, func: u16, off: u16) u32 {
    outl(0xcf8, pciAddr(bus, dev, func, off));
    return inl(0xcfc);
}
fn pcwr(bus: u16, dev: u16, func: u16, off: u16, v: u32) void {
    outl(0xcf8, pciAddr(bus, dev, func, off));
    outl(0xcfc, v);
}

// ---- MMIO ----

fn vol16(p: *u16) u16 {
    return @as(*volatile u16, @ptrCast(p)).*;
}
fn rd8(a: u64) u8 {
    return @as(*align(1) volatile u8, @ptrFromInt(a)).*;
}
fn rd16(a: u64) u16 {
    return @as(*align(1) volatile u16, @ptrFromInt(a)).*;
}
fn rd32(a: u64) u32 {
    return @as(*align(1) volatile u32, @ptrFromInt(a)).*;
}
fn wr8(a: u64, v: u8) void {
    @as(*align(1) volatile u8, @ptrFromInt(a)).* = v;
}
fn wr16(a: u64, v: u16) void {
    @as(*align(1) volatile u16, @ptrFromInt(a)).* = v;
}
fn wr32(a: u64, v: u32) void {
    @as(*align(1) volatile u32, @ptrFromInt(a)).* = v;
}
fn wr64(a: u64, v: u64) void {
    @as(*align(1) volatile u64, @ptrFromInt(a)).* = v;
}
fn feat(nic: Nic, sel: u32) u32 {
    wr32(nic.common + 0, sel);
    return rd32(nic.common + 4);
}
fn setFeat(nic: Nic, sel: u32, bits: u32) void {
    wr32(nic.common + 8, sel);
    wr32(nic.common + 12, bits);
}

// ---- page tables: uncached 2 MiB pages, including above 4 GiB ----

var tables: [8][512]u64 align(4096) = undefined;
var tables_used: usize = 0;

fn allocTable() [*]u64 {
    if (tables_used >= tables.len) halt();
    @memset(&tables[tables_used], 0);
    const p: [*]u64 = &tables[tables_used];
    tables_used += 1;
    return p;
}

fn mapUncached(phys: u64, len: u64) void {
    var a = phys & ~@as(u64, 0x1f_ffff);
    const end = (phys + len + 0x1f_ffff) & ~@as(u64, 0x1f_ffff);
    while (a < end) : (a += 0x20_0000) map2m(a);
}

fn map2m(a: u64) void {
    const cr3 = asm volatile ("mov %%cr3, %[o]"
        : [o] "=r" (-> u64),
    );
    const pml4: [*]u64 = @ptrFromInt(cr3 & ~@as(u64, 0xfff));
    const ix4 = (a >> 39) & 0x1ff;
    if (pml4[ix4] & 1 == 0) pml4[ix4] = @intFromPtr(allocTable()) | 0x3;
    const pdpt: [*]u64 = @ptrFromInt(pml4[ix4] & ~@as(u64, 0xfff));
    const ix3 = (a >> 30) & 0x1ff;
    if (pdpt[ix3] & 1 == 0) pdpt[ix3] = @intFromPtr(allocTable()) | 0x3;
    const pd: [*]u64 = @ptrFromInt(pdpt[ix3] & ~@as(u64, 0xfff));
    const ix2 = (a >> 21) & 0x1ff;
    // present, writable, PWT, PCD, large page
    pd[ix2] = a | 0x9b;
    asm volatile ("invlpg (%[p])"
        :
        : [p] "r" (a),
        : .{ .memory = true }
    );
}

// ---- serial and power ----

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
fn outl(port: u16, v: u32) void {
    asm volatile ("outl %[v], %[p]"
        :
        : [v] "{eax}" (v),
          [p] "{dx}" (port),
    );
}
fn inl(port: u16) u32 {
    return asm volatile ("inl %[p], %[r]"
        : [r] "={eax}" (-> u32),
        : [p] "{dx}" (port),
    );
}

fn serialInit() void {
    outb(0x3f8 + 1, 0);
    outb(0x3f8 + 3, 0x80);
    outb(0x3f8, 1);
    outb(0x3f8 + 1, 0);
    outb(0x3f8 + 3, 3);
    outb(0x3f8 + 2, 0xc7);
    outb(0x3f8 + 4, 0x0b);
}
fn say(s: []const u8) void {
    for (s) |c| {
        while (inb(0x3f8 + 5) & 0x20 == 0) {}
        outb(0x3f8, c);
    }
}
fn hex8(v: u8) void {
    const d = "0123456789abcdef";
    say(&[_]u8{ d[v >> 4], d[v & 0xf] });
}
fn hex16(v: u16) void {
    hex8(@truncate(v >> 8));
    hex8(@truncate(v));
}
fn hex32(v: u32) void {
    hex16(@truncate(v >> 16));
    hex16(@truncate(v));
}
fn hex64(v: u64) void {
    hex32(@truncate(v >> 32));
    hex32(@truncate(v));
}
fn powerOff() noreturn {
    outb(0x600, 0x34);
    halt();
}
fn halt() noreturn {
    while (true) asm volatile ("hlt");
}
