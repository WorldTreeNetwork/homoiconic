#!/bin/sh
# Build from any working directory; the Lean toolchain is pinned by the package.
set -eu
export PATH="$HOME/.elan/bin:$PATH"
HOST="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$HOST/../kernel"
OUT="$HOST/out"
mkdir -p "$OUT"

lake build
lake env lean Contract.lean

# Preserve Lake's package identity so the initializer and imported symbols agree.
# Only syntax and semantics are needed by the executable entry, not proof objects.
for name in Syntax Semantics Host; do
    lake env lean --setup ".lake/build/ir/Circular/$name.setup.json" \
        -c "$OUT/$name.c" "Circular/$name.lean"
    lake env leanc -c -o "$OUT/lean-$name.o" "$OUT/$name.c"
done
lake env leanc -c -o "$OUT/ffi.o" ffi.c
lake env leanc -c -o "$OUT/runtime.o" "$HOST/runtime.c"
zig build-obj "$HOST/check.zig" -femit-bin="$OUT/zig-host.o" \
    --cache-dir "$OUT/zig-cache" --global-cache-dir "$OUT/zig-global-cache"
lake env leanc -o "$OUT/check" "$OUT/zig-host.o" "$OUT/runtime.o" \
    "$OUT/ffi.o" "$OUT/lean-Host.o" "$OUT/lean-Semantics.o" "$OUT/lean-Syntax.o"
"$OUT/check"
