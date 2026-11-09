#!/bin/sh
# Rebuild the spike and print the Zig host's result. Expected: 71
set -eu
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p out
lean -c out/kernel.c src/Kernel.lean
leanc -c -o out/kernel.o out/kernel.c
zig build-obj host.zig -femit-bin=out/host.o
leanc -o out/host out/host.o out/kernel.o
./out/host
