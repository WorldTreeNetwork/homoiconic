const std = @import("std");

extern fn kernel_eval(n: u32) u32;

pub fn main() void {
    const result = kernel_eval(4);
    std.debug.print("{d}\n", .{result});
}
