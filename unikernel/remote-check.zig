//! One machine replays the delivery log of the remote channel.

const std = @import("std");

extern fn initialize_circularKernel_Surface_Host(builtin: u8) *anyopaque;
extern fn kernel_finish_initialization(result: *anyopaque) u8;
extern fn reflect_remote_same(unused: usize) usize;

export fn initialize_libuv() void {}

pub fn main(init: std.process.Init.Minimal) u8 {
    _ = init;
    if (kernel_finish_initialization(initialize_circularKernel_Surface_Host(0)) == 0) return 2;
    return if (reflect_remote_same(0) == 1) 0 else 1;
}
