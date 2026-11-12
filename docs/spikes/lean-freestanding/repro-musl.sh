#!/bin/sh
# The same image linked against musl, with Zig as the only compiler and linker.
# Run after repro-command.sh (it builds out/kernel.o). Needs objcopy.
# Expected on the serial port: the lines repro-command.sh expects.
set -eu
export PATH="$HOME/.elan/bin:$HOME/zig-0.16.0:$PATH"
SPIKE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
OUT="$SPIKE/out"
H="$SPIKE/../../../host/out"
L="$(cd "$SPIKE/../../../kernel" && lake env lean --print-prefix)/lib"
Z="--cache-dir $OUT/zc --global-cache-dir $OUT/zg"
mkdir -p "$OUT/musl"
# The C++ archives name libraries musl does not have as separate files.
for a in libc++.a libc++abi.a libunwind.a; do
    objcopy --remove-section=.deplibs "$L/$a" "$OUT/musl/$a"
done
# A weak initialize_libuv lets main's empty one stand in for it.
objcopy --weaken-symbol=initialize_libuv "$L/lean/libleanrt.a" "$OUT/musl/libleanrt.a"
sed 's/export fn __wrap_initialize_libuv/export fn initialize_libuv/' "$SPIKE/src/main.zig" > "$OUT/musl/main.zig"
cp "$SPIKE/src/factorial.hom" "$OUT/musl/"
# shellcheck disable=SC2086
zig build-obj "$OUT/musl/main.zig" -lc -target x86_64-linux-musl -O ReleaseSafe -fno-PIE \
    -femit-bin="$OUT/musl/main.o" $Z
# shellcheck disable=SC2086
zig build-exe -target x86_64-linux-musl -static -fno-PIE -femit-bin="$OUT/reflect-musl.elf" \
    "$SPIKE/src/boot.S" "$OUT/kernel.o" "$OUT/musl/main.o" "$SPIKE/src/glibc_names.c" \
    "$H/runtime.o" "$H/ffi.o" "$H"/lean-*.o \
    "$L/lean/libInit.a" "$OUT/musl/libleanrt.a" "$L/lean/libStd.a" "$L/lean/libInit.a" "$OUT/musl/libleanrt.a" \
    "$L/libgmp.a" "$L/libuv.a" "$OUT/musl/libc++.a" "$OUT/musl/libc++abi.a" "$OUT/musl/libunwind.a" \
    -lc --gc-sections $Z
python3 "$SPIKE/src/onenote.py" "$OUT/reflect-musl.elf"
rm -f "$OUT/serial-musl.log"
timeout 60 cloud-hypervisor --kernel "$OUT/reflect-musl.elf" --cpus boot=1 --memory size=512M \
    --serial file="$OUT/serial-musl.log" --console off
cat "$OUT/serial-musl.log"
