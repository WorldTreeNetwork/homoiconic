#!/bin/sh
# Build the image and boot it under Cloud Hypervisor. Expected on the serial port:
#   reflect: booted / reflect: memory to ... / reflect: starting /
#   265252859812191058636308480000000 / reflect: exit 0
# Run on Linux x86_64 with KVM, gcc with a static glibc, python3, Zig 0.16.0 and elan,
# after `sh host/check.sh` has compiled the kernel's Lean objects into host/out.
# (On Linux that script's own last link step fails; the objects are there by then.)
set -eu
export PATH="$HOME/.elan/bin:$HOME/zig-0.16.0:$PATH"
SPIKE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
HERE="$SPIKE/src"
OUT="$SPIKE/out"
H="$SPIKE/../../../host/out"
L="$(cd "$SPIKE/../../../kernel" && lake env lean --print-prefix)/lib"
mkdir -p "$OUT"
zig build-obj "$HERE/main.zig" -lc -O ReleaseSafe -fno-PIE -femit-bin="$OUT/main.o" \
    --cache-dir "$OUT/zc" --global-cache-dir "$OUT/zg"
zig build-obj "$HERE/kernel.zig" -target x86_64-freestanding-none -O ReleaseSmall -fno-PIE \
    -fno-builtin -fno-stack-check -fno-stack-protector -femit-bin="$OUT/kernel.o" \
    --cache-dir "$OUT/zc" --global-cache-dir "$OUT/zg"
gcc -c -o "$OUT/boot.o" "$HERE/boot.S"
echo "kernel.o needs:"; nm -u "$OUT/kernel.o"
gcc -static -no-pie -o "$OUT/reflect.elf" "$OUT/boot.o" "$OUT/kernel.o" "$OUT/main.o" \
    "$H/runtime.o" "$H/ffi.o" "$H"/lean-*.o -L"$L/lean" -L"$L" \
    -Wl,--start-group -lInit -lleanrt -lStd -Wl,--end-group \
    -lc++ -lc++abi -lgmp -luv -lm -lpthread -Wl,--gc-sections -Wl,-u,pvh_start32 -Wl,--wrap=initialize_libuv 2>&1 |
    grep -v "warning\|in function\|statically linked\|garbage collection" || true
python3 "$HERE/onenote.py" "$OUT/reflect.elf"
readelf -lW "$OUT/reflect.elf" | grep -E "LOAD|NOTE|TLS"
readelf -n "$OUT/reflect.elf" | grep -A2 Xen || { echo "no PVH note"; exit 1; }
rm -f "$OUT/serial.log"
timeout 60 cloud-hypervisor --kernel "$OUT/reflect.elf" --cpus boot=1 --memory size=512M \
    --serial file="$OUT/serial.log" --console off > "$OUT/ch.log" 2>&1 || echo "cloud-hypervisor exit $?"
tail -5 "$OUT/ch.log"
cat "$OUT/serial.log"
