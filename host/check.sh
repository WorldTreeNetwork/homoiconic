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
lake env lean RequestContract.lean
lake env lean Surface/Check.lean
# The scenarios print one line each; a line that starts with FAIL fails the check.
lake env lean ReflectRun.lean > "$OUT/scenarios.txt"
if grep -q "^FAIL" "$OUT/scenarios.txt"; then
    grep "^FAIL" "$OUT/scenarios.txt" >&2
    exit 1
fi

# The programs the host passes come from Surface.prints, so Zig only holds bytes.
lake env lean --run Surface/EmitCases.lean > "$OUT/cases.zig"

# Preserve Lake's package identity so the initializer and imported symbols agree.
# Only the modules the entry points import are compiled, not proof objects.
OBJS=""
for module in Reflect/Syntax Reflect/Semantics Reflect/Interpreter Reflect/Machine Reflect/RunUntil Reflect/Arith Reflect/Request \
              Surface/Read Surface/Render Surface/Run Surface/Host; do
    name="$(echo "$module" | tr / -)"
    lake env lean --setup ".lake/build/ir/$module.setup.json" \
        -c "$OUT/$name.c" "$module.lean"
    lake env leanc -c -O3 -o "$OUT/lean-$name.o" "$OUT/$name.c"
    OBJS="$OBJS $OUT/lean-$name.o"
done
lake env leanc -c -o "$OUT/ffi.o" ffi.c
lake env leanc -c -o "$OUT/runtime.o" "$HOST/runtime.c"
for program in check run ask; do
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
expect "265252859812191058636308480000000" "$EXAMPLES/factorial.hom"
expect "no result within 5000 steps" "$EXAMPLES/forever.hom" 5000
# An answer longer than the command's first buffer is printed in full: every
# byte is compared.
printf 'def fill n =\n  case n\n    0 -> []\n    m + 1 -> [n, ...fill m]\n\nfill 20000\n' > "$OUT/long.hom"
"$OUT/run" "$OUT/long.hom" > "$OUT/long.txt"
awk 'BEGIN { printf "["; for (i = 20000; i > 1; i--) printf "%d, ", i; printf "1]\n" }' > "$OUT/long.expected"
cmp "$OUT/long.expected" "$OUT/long.txt"

# A call the command cannot make: exit 2, nothing on standard output, and
# exactly the one expected line on standard error, byte for byte.
USAGE="usage: run <program-file> [step-budget]   (default budget: 100000000 machine steps)"
BUDGET="run: the step budget must be a whole number"
NEWLINE="x
y"
refuse() {
    wanted="$1"
    shift
    status=0
    "$OUT/run" "$@" > "$OUT/refuse.out" 2> "$OUT/refuse.err" || status=$?
    printf '%s\n' "$wanted" > "$OUT/refuse.expected"
    if [ "$status" != 2 ] || [ -s "$OUT/refuse.out" ]; then
        echo "run $*: expected exit 2 and no output; got exit $status" >&2
        exit 1
    fi
    cmp "$OUT/refuse.expected" "$OUT/refuse.err"
    echo "run refused: $wanted"
}
refuse "$USAGE"
refuse "$USAGE" "$EXAMPLES/append.hom" 1 extra
refuse "run: cannot read the program file: FileNotFound" "$EXAMPLES/missing.hom"
refuse "run: cannot read the program file: FileNotFound" "$EXAMPLES/$NEWLINE"
refuse "run: cannot read the program file: IsDir" "$EXAMPLES"
refuse "$BUDGET" "$EXAMPLES/append.hom" -1
refuse "$BUDGET" "$EXAMPLES/append.hom" "$NEWLINE"
echo "run command checks passed"

# The ask command: a program file and an answers file in, the kernel's text out.
converse() {
    wanted="$1"
    shift
    got="$("$OUT/ask" "$@")"
    if [ "$got" != "$wanted" ]; then
        echo "ask $*: expected '$wanted', got '$got'" >&2
        exit 1
    fi
    echo "ask $* => $(echo "$got" | tr '\n' '|')"
}
converse "asked: [1]
asked: [2, 20]
42" "$EXAMPLES/ask.hom" "$EXAMPLES/ask.answers"
converse "asked: [1]
asked: [2, 20]
waiting" "$EXAMPLES/ask.hom" "$EXAMPLES/ask-one.answers"
# A program that asks nothing answers as it does under run.
converse "[1, 2, 3, 4]" "$EXAMPLES/append.hom" "$EXAMPLES/ask.answers"
converse "no result within 5000 steps of a turn" "$EXAMPLES/forever.hom" "$EXAMPLES/ask.answers" 5000
# An answers file that is not an array is the kernel's text, and exits 0.
converse "answers: not an array" "$EXAMPLES/ask.hom" "$EXAMPLES/factorial.hom"

ASKUSAGE="usage: ask <program-file> <answers-file> [step-budget]   (default budget: 100000000 machine steps for each turn)"
refuseAsk() {
    wanted="$1"
    shift
    status=0
    "$OUT/ask" "$@" > "$OUT/refuse.out" 2> "$OUT/refuse.err" || status=$?
    printf '%s\n' "$wanted" > "$OUT/refuse.expected"
    if [ "$status" != 2 ] || [ -s "$OUT/refuse.out" ]; then
        echo "ask $*: expected exit 2 and no output; got exit $status" >&2
        exit 1
    fi
    cmp "$OUT/refuse.expected" "$OUT/refuse.err"
    echo "ask refused: $wanted"
}
refuseAsk "$ASKUSAGE"
refuseAsk "$ASKUSAGE" "$EXAMPLES/ask.hom"
refuseAsk "$ASKUSAGE" "$EXAMPLES/ask.hom" "$EXAMPLES/ask.answers" 1 extra
refuseAsk "ask: cannot read the program file: FileNotFound" "$EXAMPLES/missing.hom" "$EXAMPLES/ask.answers"
refuseAsk "ask: cannot read the answers file: FileNotFound" "$EXAMPLES/ask.hom" "$EXAMPLES/$NEWLINE"
refuseAsk "ask: the step budget must be a whole number" "$EXAMPLES/ask.hom" "$EXAMPLES/ask.answers" "$NEWLINE"
echo "ask command checks passed"
