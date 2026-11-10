#!/bin/sh
# Build from any working directory; the Lean toolchain is pinned by the package.
set -eu
export PATH="$HOME/.elan/bin:$PATH"
HOST="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$HOST/../kernel"
OUT="$HOST/out"
mkdir -p "$OUT"

lake build
lake env lean ReflectContract.lean
lake env lean MachineContract.lean
lake env lean Surface/Check.lean

# The programs the host passes come from Surface.prints, so Zig only holds bytes.
lake env lean --run Surface/EmitCases.lean > "$OUT/cases.zig"

# Preserve Lake's package identity so the initializer and imported symbols agree.
# Only the modules the entry points import are compiled, not proof objects.
OBJS=""
for module in Reflect/Syntax Reflect/Semantics Reflect/Interpreter Reflect/Machine Reflect/RunUntil \
              Surface/Read Surface/Render Surface/Run Surface/Host; do
    name="$(echo "$module" | tr / -)"
    lake env lean --setup ".lake/build/ir/$module.setup.json" \
        -c "$OUT/$name.c" "$module.lean"
    lake env leanc -c -O3 -o "$OUT/lean-$name.o" "$OUT/$name.c"
    OBJS="$OBJS $OUT/lean-$name.o"
done
lake env leanc -c -o "$OUT/ffi.o" ffi.c
lake env leanc -c -o "$OUT/runtime.o" "$HOST/runtime.c"
for program in check run; do
    zig build-obj "$HOST/$program.zig" -femit-bin="$OUT/zig-$program.o" \
        --cache-dir "$OUT/zig-cache" --global-cache-dir "$OUT/zig-global-cache"
    # shellcheck disable=SC2086
    lake env leanc -o "$OUT/$program" "$OUT/zig-$program.o" "$OUT/runtime.o" \
        "$OUT/ffi.o" $OBJS
done
"$OUT/check"

# The run command: a program file in, the kernel's text out.
EXAMPLES="$HOST/../examples"
expect() {
    wanted="$1"
    shift
    got="$("$OUT/run" "$@")"
    if [ "$got" != "$wanted" ]; then
        echo "run $*: expected '$wanted', got '$got'" >&2
        exit 1
    fi
    echo "run $* => $got"
}
expect "[1, 2, 3, 4]" "$EXAMPLES/append.hom"
expect "[0, [1, 42]]" "$EXAMPLES/code.hom"
expect "no result within 5000 steps" "$EXAMPLES/forever.hom" 5000
# An answer longer than the command's first buffer is printed in full.
printf 'def fill n =\n  case n\n    0 -> []\n    m + 1 -> [n, ...fill m]\n\nfill 20000\n' > "$OUT/long.hom"
"$OUT/run" "$OUT/long.hom" > "$OUT/long.txt"
size="$(wc -c < "$OUT/long.txt")"
size="$((size + 0))"
ending="$(tail -c 9 "$OUT/long.txt")"
if [ "$size" != 128895 ] || [ "$ending" != "3, 2, 1]" ]; then
    echo "run: a long answer was not printed in full" >&2
    exit 1
fi

# A call the command cannot make: exit 2, nothing on standard output, and
# exactly one line on standard error.
refuse() {
    status=0
    "$OUT/run" "$@" > "$OUT/refuse.out" 2> "$OUT/refuse.err" || status=$?
    lines="$(wc -l < "$OUT/refuse.err")"
    lines="$((lines + 0))"
    if [ "$status" != 2 ] || [ -s "$OUT/refuse.out" ] || [ "$lines" != 1 ]; then
        echo "run $*: expected exit 2, no output and one line of error; got exit $status, $lines error lines" >&2
        exit 1
    fi
    echo "run $* refused: $(cat "$OUT/refuse.err")"
}
refuse
refuse "$EXAMPLES/append.hom" 1 extra
refuse "$EXAMPLES/missing.hom"
refuse "$EXAMPLES"
refuse "$EXAMPLES/append.hom" -1
echo "run command checks passed"
