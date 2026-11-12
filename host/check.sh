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
lake env lean StoreContract.lean
lake env lean Surface/Check.lean
# The scenarios print one line each; a line that starts with FAIL fails the check.
lake env lean ReflectRun.lean > "$OUT/scenarios.txt"
if grep -q "^FAIL" "$OUT/scenarios.txt"; then
    grep "^FAIL" "$OUT/scenarios.txt" >&2
    exit 1
fi

lake env lean WireCheck.lean > "$OUT/wire.txt"
if grep -q "^FAIL" "$OUT/wire.txt" || ! grep -q "^ok" "$OUT/wire.txt"; then
    cat "$OUT/wire.txt" >&2
    exit 1
fi

lake env lean KeepCheck.lean > "$OUT/keep.txt"
if grep -q "^FAIL" "$OUT/keep.txt" || ! grep -q "^ok" "$OUT/keep.txt" || grep -q "error" "$OUT/keep.txt"; then
    cat "$OUT/keep.txt" >&2
    exit 1
fi

lake env lean StoreCheck.lean > "$OUT/store.txt"
if grep -q "^FAIL" "$OUT/store.txt" || ! grep -q "^ok" "$OUT/store.txt"; then
    cat "$OUT/store.txt" >&2
    exit 1
fi

# The programs the host passes come from Surface.prints, so Zig only holds bytes.
lake env lean --run Surface/EmitCases.lean > "$OUT/cases.zig"

# Preserve Lake's package identity so the initializer and imported symbols agree.
# Only the modules the entry points import are compiled, not proof objects.
OBJS=""
for module in Reflect/Syntax Reflect/Semantics Reflect/Interpreter Reflect/Machine Reflect/RunUntil Reflect/Arith Reflect/Request Reflect/Store \
              Wire/Cbor Wire/Form Wire/Blake3 Wire/Piece \
              Surface/Read Surface/Render Surface/Run Surface/Bytes Surface/Keep Surface/Host; do
    name="$(echo "$module" | tr / -)"
    lake env lean --setup ".lake/build/ir/$module.setup.json" \
        -c "$OUT/$name.c" "$module.lean"
    lake env leanc -c -O3 -o "$OUT/lean-$name.o" "$OUT/$name.c"
    OBJS="$OBJS $OUT/lean-$name.o"
done
lake env leanc -c -o "$OUT/ffi.o" ffi.c
lake env leanc -c -o "$OUT/runtime.o" "$HOST/runtime.c"
for program in check run ask bytes keep; do
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
USAGE="usage: run [--bytes] <program-file> [step-budget]   (default budget: 100000000 machine steps)"
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

# The byte form: each example is written as bytes by the kernel and run from
# them, and prints what its source prints.
sameFromBytes() {
    "$OUT/bytes" "$1" > "$OUT/program.bytes"
    shift_budget="${2:-}"
    # shellcheck disable=SC2086
    fromSource="$("$OUT/run" "$1" $shift_budget)"
    # shellcheck disable=SC2086
    fromBytes="$("$OUT/run" --bytes "$OUT/program.bytes" $shift_budget)"
    if [ "$fromSource" != "$fromBytes" ]; then
        echo "run --bytes $1: expected '$fromSource', got '$fromBytes'" >&2
        exit 1
    fi
    echo "run --bytes $(basename "$1") ($(wc -c < "$OUT/program.bytes" | tr -d ' ') bytes) => $(printf '%s' "$fromBytes" | cut -c1-60)"
}
sameFromBytes "$EXAMPLES/append.hom"
sameFromBytes "$EXAMPLES/code.hom"
sameFromBytes "$EXAMPLES/factorial.hom"
sameFromBytes "$EXAMPLES/forever.hom" 5000
sameFromBytes "$OUT/long.hom"
# A byte form longer than the command's first buffer is written in full.
awk 'BEGIN { printf "["; for (i = 0; i < 30000; i++) printf "70000, "; printf "1]\n" }' > "$OUT/wide.hom"
sameFromBytes "$OUT/wide.hom"
if [ "$(wc -c < "$OUT/program.bytes" | tr -d ' ')" -le 65536 ]; then
    echo "the wide program's byte form does not exceed the first buffer" >&2
    exit 1
fi
# The identity function is three bytes, and the kernel writes those three.
printf 'fn x -> x\n' > "$OUT/identity.hom"
"$OUT/bytes" "$OUT/identity.hom" > "$OUT/identity.bytes"
printf '\202\001\000' > "$OUT/identity.expected"
cmp "$OUT/identity.expected" "$OUT/identity.bytes"
# Bytes that are not the one form, and bytes that are no program, are the
# kernel's text and exit 0, as a syntax error is.
printf '\030\027' > "$OUT/long-form.bytes"
expect "bytes error: a number or length is not in its shortest form" --bytes "$OUT/long-form.bytes"
printf '\200' > "$OUT/empty-array.bytes"
expect "bytes error: the value is not a program" --bytes "$OUT/empty-array.bytes"
expect "bytes error: a kind of value that is not a number or an array" --bytes "$EXAMPLES/append.hom"
refuse "$USAGE" --bytes
refuse "run: cannot read the program file: FileNotFound" --bytes "$EXAMPLES/missing.hom"
# A syntax error leaves standard output empty: exit 1 and the kernel's text.
printf 'fn x ->\n' > "$OUT/broken.hom"
status=0
"$OUT/bytes" "$OUT/broken.hom" > "$OUT/refuse.out" 2> "$OUT/refuse.err" || status=$?
if [ "$status" != 1 ] || [ -s "$OUT/refuse.out" ] || ! grep -q "^syntax error: " "$OUT/refuse.err"; then
    echo "bytes on a syntax error: expected exit 1, no output and the error; got exit $status" >&2
    exit 1
fi
status=0
"$OUT/bytes" > "$OUT/refuse.out" 2> "$OUT/refuse.err" || status=$?
if [ "$status" != 2 ] || [ -s "$OUT/refuse.out" ]; then
    echo "bytes with no file: expected exit 2 and no output; got exit $status" >&2
    exit 1
fi
echo "byte form checks passed"

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

# The keep command: one turn for each call, with the program's state in a
# directory between calls.
STORE="$OUT/store"
rm -rf "$STORE"
mkdir -p "$STORE"
echo 20 > "$OUT/twenty.hom"
echo 22 > "$OUT/twenty-two.hom"
echo 30 > "$OUT/thirty.hom"
# Run a turn; the lines it printed are in $ASKED (first line), $ROOT, $FETCHED
# and $WROTE.
turn() {
    "$OUT/keep" "$STORE" "$@" > "$OUT/turn.txt"
    ASKED="$(sed -n 1p "$OUT/turn.txt")"
    ROOT="$(sed -n 's/^root: //p' "$OUT/turn.txt")"
    FETCHED="$(sed -n 's/^store: fetched \([0-9]*\), wrote [0-9]*$/\1/p' "$OUT/turn.txt")"
    WROTE="$(sed -n 's/^store: fetched [0-9]*, wrote \([0-9]*\)$/\1/p' "$OUT/turn.txt")"
    echo "keep $(echo "$*" | cut -c1-24) => $ASKED (fetched $FETCHED, wrote $WROTE)"
}
want() {
    if [ "$1" != "$2" ]; then
        echo "keep: expected '$2', got '$1'" >&2
        exit 1
    fi
}
turn start "$EXAMPLES/keep.hom"
want "$ASKED" "asked: [1]"
FIRST="$ROOT"
PIECES="$WROTE"
want "$(ls "$STORE" | wc -l | tr -d ' ')" "$PIECES"
# Every file is named by the Blake3 hash of its bytes; the names are the
# kernel's. Where b3sum is installed, an outside program agrees.
if command -v b3sum > /dev/null; then
    for piece in "$STORE"/*; do
        want "$(b3sum --no-names "$piece")" "$(basename "$piece")"
    done
    echo "keep: b3sum agrees with every piece name"
fi
# The second turn does not read the long list and does not write it again.
turn answer "$FIRST" "$OUT/twenty.hom"
want "$ASKED" "asked: [2, 20]"
SECOND="$ROOT"
if [ "$FETCHED" -ge "$PIECES" ] || [ "$WROTE" -ge "$PIECES" ] || [ "$PIECES" -lt 20 ]; then
    echo "keep: the second turn fetched $FETCHED and wrote $WROTE of $PIECES pieces" >&2
    exit 1
fi
# The last turn reads the list, and gives what one run against both answers gives.
turn answer "$SECOND" "$OUT/twenty-two.hom"
want "$ASKED" "[2000, 42]"
want "$WROTE" "0"
printf '[20, 22]\n' > "$OUT/keep.answers"
want "$ASKED" "$("$OUT/ask" "$EXAMPLES/keep.hom" "$OUT/keep.answers" | tail -1)"
# A root is kept: the first one can be answered again, differently, and the
# two runs share the list.
BEFORE="$(ls "$STORE" | wc -l | tr -d ' ')"
turn answer "$FIRST" "$OUT/thirty.hom"
want "$ASKED" "asked: [2, 30]"
turn answer "$ROOT" "$OUT/twenty-two.hom"
want "$ASKED" "[2000, 52]"
AFTER="$(ls "$STORE" | wc -l | tr -d ' ')"
if [ $((AFTER - BEFORE)) -ge 10 ]; then
    echo "keep: a second run from the same root added $((AFTER - BEFORE)) pieces" >&2
    exit 1
fi
# A turn run twice gives the same root and the same files: nothing is added.
turn answer "$FIRST" "$OUT/twenty.hom"
want "$ROOT" "$SECOND"
want "$(ls "$STORE" | wc -l | tr -d ' ')" "$AFTER"
# A missing piece: exit 3, nothing printed, and the turn runs once it is back.
mv "$STORE/$SECOND" "$OUT/hidden.piece"
status=0
"$OUT/keep" "$STORE" answer "$SECOND" "$OUT/twenty-two.hom" > "$OUT/refuse.out" 2> "$OUT/refuse.err" || status=$?
printf 'keep: the store lacks piece %s\n' "$SECOND" > "$OUT/refuse.expected"
if [ "$status" != 3 ] || [ -s "$OUT/refuse.out" ]; then
    echo "keep with a piece missing: expected exit 3 and no output; got exit $status" >&2
    exit 1
fi
cmp "$OUT/refuse.expected" "$OUT/refuse.err"
mv "$OUT/hidden.piece" "$STORE/$SECOND"
turn answer "$SECOND" "$OUT/twenty-two.hom"
want "$ASKED" "[2000, 42]"
# A piece whose bytes were changed is refused by the kernel.
cp "$STORE/$SECOND" "$OUT/good.piece"
printf 'x' >> "$STORE/$SECOND"
want "$("$OUT/keep" "$STORE" answer "$SECOND" "$OUT/twenty-two.hom")" "store error: piece $SECOND does not match its name"
cp "$OUT/good.piece" "$STORE/$SECOND"
# The kernel's text for a bad root, an answer that is not data, and a program
# that asks nothing.
want "$("$OUT/keep" "$STORE" answer nothex "$OUT/twenty.hom")" "store error: a root is 64 hex digits"
want "$("$OUT/keep" "$STORE" answer "$SECOND" "$EXAMPLES/ask.hom")" "answer: not data"
want "$("$OUT/keep" "$STORE" start "$EXAMPLES/append.hom" | sed -n 1p)" "[1, 2, 3, 4]"
want "$("$OUT/keep" "$STORE" start "$EXAMPLES/forever.hom" 5000 | sed -n 1p)" "no result within 5000 steps of a turn"
refuseKeep() {
    status=0
    "$OUT/keep" "$@" > "$OUT/refuse.out" 2> "$OUT/refuse.err" || status=$?
    if [ "$status" != 2 ] || [ -s "$OUT/refuse.out" ] || ! [ -s "$OUT/refuse.err" ]; then
        echo "keep $*: expected exit 2, no output and a message; got exit $status" >&2
        exit 1
    fi
    echo "keep refused: $(sed -n 1p "$OUT/refuse.err")"
}
refuseKeep
refuseKeep "$STORE" start
refuseKeep "$STORE" resume "$EXAMPLES/keep.hom"
refuseKeep "$STORE" start "$EXAMPLES/missing.hom"
refuseKeep "$OUT/no-such-store" start "$EXAMPLES/keep.hom"
refuseKeep "$STORE" start "$EXAMPLES/keep.hom" many
refuseKeep "$STORE" answer "$SECOND" "$OUT/twenty.hom" 1 extra
echo "keep command checks passed"
