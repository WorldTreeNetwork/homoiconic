//! The KVM paravirtual clock's conversion from a TSC delta to nanoseconds.
//! The ABI: shift the delta by tsc_shift (right when it is negative), then
//! take (delta * tsc_to_system_mul) >> 32 from the 128-bit product.
//! `zig test unikernel/pvclock.zig` runs on any host; build-net.sh runs it.

/// Nanoseconds for `delta` TSC ticks since the record's `tsc_timestamp`.
pub fn scale(delta: u64, mul: u32, shift: i8) u64 {
    var d = delta;
    if (shift >= 0) {
        const s: u8 = @intCast(shift);
        d = if (s >= 64) 0 else d << @intCast(s);
    } else {
        const s: u8 = @intCast(-@as(i16, shift));
        d = if (s >= 64) 0 else d >> @intCast(s);
    }
    return @truncate((@as(u128, d) * mul) >> 32);
}

/// The clock: the record's `system_time` plus the scaled delta.
pub fn nanos(system_time: u64, delta: u64, mul: u32, shift: i8) u64 {
    return system_time +% scale(delta, mul, shift);
}

const testing = @import("std").testing;

/// What net.zig did before homoiconic-q59.48: a wrapping 64-bit product.
fn wrapped(delta: u64, mul: u32, shift: i8) u64 {
    var d = delta;
    if (shift >= 0) d <<= @intCast(shift) else d >>= @intCast(-@as(i16, shift));
    return (d *% mul) >> 32;
}

/// The same value from two 64-bit products, with no 128-bit arithmetic.
fn halves(d: u64, mul: u32) u64 {
    return (d >> 32) * mul + (((d & 0xffff_ffff) * mul) >> 32);
}

fn forward(mul: u32, shift: i8, step: u64, steps: u64) !void {
    var delta: u64 = 0;
    var last: u64 = 0;
    var old_last: u64 = 0;
    var old_went_back = false;
    var n: u64 = 0;
    while (n < steps) : (n += 1) {
        const now = scale(delta, mul, shift);
        try testing.expect(now >= last);
        const shifted = if (shift >= 0) delta << @intCast(shift) else delta >> @intCast(-@as(i16, shift));
        try testing.expectEqual(halves(shifted, mul), now);
        const old = wrapped(delta, mul, shift);
        if (old < old_last) old_went_back = true;
        last = now;
        old_last = old;
        delta += step;
    }
    // The run went far past 2^32 shifted ticks, where the old read wrapped.
    const end = if (shift >= 0) delta << @intCast(shift) else delta >> @intCast(-@as(i16, shift));
    try testing.expect(end > (@as(u64, 1) << 44));
    try testing.expect(old_went_back);
}

test "time runs forward far past 2^32 shifted ticks" {
    // A 3 GHz TSC as KVM describes it: shift -1, mul 2^33 / 3.
    try forward(2863311531, -1, (1 << 27) + 12345, 300000);
    // A 1.5 GHz TSC: shift 0, same mul.
    try forward(2863311531, 0, (1 << 27) + 12345, 150000);
    // A slow counter scaled up: shift 1.
    try forward(0xc000_0000, 1, (1 << 26) + 999, 150000);
}

test "a 3 GHz counter gives a second per 3e9 ticks, for a day" {
    const day: u64 = 86400;
    var s: u64 = 1;
    while (s <= day) : (s *= 2) {
        const ns = scale(3_000_000_000 * s, 2863311531, -1);
        const want = 1_000_000_000 * s;
        const off = if (ns > want) ns - want else want - ns;
        try testing.expect(off * 1_000_000 < want);
    }
}

test "a shift out of range gives zero, not a trap" {
    try testing.expectEqual(@as(u64, 0), scale(1 << 40, 0xffff_ffff, -64));
    try testing.expectEqual(@as(u64, 0), scale(1 << 40, 0xffff_ffff, -128));
    try testing.expectEqual(@as(u64, 0), scale(1 << 40, 0xffff_ffff, 64));
    try testing.expectEqual(@as(u64, 7), nanos(7, 0, 0xffff_ffff, 3));
}
