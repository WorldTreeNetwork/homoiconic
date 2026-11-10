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
lake env lean Surface/Check.lean

# The programs the host passes come from Surface.prints, so Zig only holds bytes.
lake env lean --run Surface/EmitCases.lean > "$OUT/cases.zig"

# Preserve Lake's package identity so the initializer and imported symbols agree.
# Only the modules the entry points import are compiled, not proof objects.
OBJS=""
for module in Circular/Syntax Circular/Semantics Circular/Host \
              Reflect/Syntax Reflect/Semantics Reflect/Interpreter Reflect/Machine \
              Surface/Read Surface/Render Surface/Run Surface/Host; do
    name="$(echo "$module" | tr / -)"
    lake env lean --setup ".lake/build/ir/$module.setup.json" \
        -c "$OUT/$name.c" "$module.lean"
    lake env leanc -c -o "$OUT/lean-$name.o" "$OUT/$name.c"
    OBJS="$OBJS $OUT/lean-$name.o"
done
lake env leanc -c -o "$OUT/ffi.o" ffi.c
lake env leanc -c -o "$OUT/runtime.o" "$HOST/runtime.c"
zig build-obj "$HOST/check.zig" -femit-bin="$OUT/zig-host.o" \
    --cache-dir "$OUT/zig-cache" --global-cache-dir "$OUT/zig-global-cache"
# shellcheck disable=SC2086
lake env leanc -o "$OUT/check" "$OUT/zig-host.o" "$OUT/runtime.o" \
    "$OUT/ffi.o" $OBJS
"$OUT/check"
