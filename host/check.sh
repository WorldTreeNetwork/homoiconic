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
lake env lean ChannelContract.lean
lake env lean LogContract.lean
lake env lean NodeContract.lean
lake env lean RootContract.lean
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

lake env lean LogCheck.lean > "$OUT/log.txt"
if grep -q "^FAIL" "$OUT/log.txt" || ! grep -q "^ok" "$OUT/log.txt" || grep -q "error" "$OUT/log.txt"; then
    cat "$OUT/log.txt" >&2
    exit 1
fi

lake env lean NodeCheck.lean > "$OUT/node.txt"
if grep -q "^FAIL" "$OUT/node.txt" || ! grep -q "^ok" "$OUT/node.txt" || grep -q "error:" "$OUT/node.txt"; then
    cat "$OUT/node.txt" >&2
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
for module in Reflect/Text Reflect/Syntax Reflect/Semantics Reflect/Interpreter Reflect/Machine Reflect/RunUntil Reflect/Arith Reflect/Request Reflect/Channel Reflect/Log Reflect/Node Reflect/Store \
              Wire/Cbor Wire/Form Wire/Blake3 Wire/Piece Wire/Reply \
              Surface/Read Surface/Render Surface/Run Surface/Bytes Surface/Chan Surface/Keep Surface/Remote Surface/Host; do
    name="$(echo "$module" | tr / -)"
    lake env lean --setup ".lake/build/ir/$module.setup.json" \
        -c "$OUT/$name.c" "$module.lean"
    lake env leanc -c -O3 -o "$OUT/lean-$name.o" "$OUT/$name.c"
    OBJS="$OBJS $OUT/lean-$name.o"
done
lake env leanc -c -o "$OUT/ffi.o" ffi.c
lake env leanc -c -o "$OUT/runtime.o" "$HOST/runtime.c"
for program in check run ask bytes keep chan vm node sign; do
    # Without -lc, Zig's object defines _start. leanc also links glibc's
    # Scrt1.o, and the two _start symbols fail the link. -lc makes the object
    # export main and leave startup to glibc, which the C++ runtime needs
    # (locale is set up before static constructors). The version is the oldest
    # glibc the Lean toolchain's bundled libc still matches; a newer target
    # references symbols that libc does not have. macOS objects already export
    # main, so this is Linux only.
    ZIG_FLAGS=""
    if [ "$(uname -s)" = "Linux" ]; then
        ZIG_FLAGS="-lc -target $(uname -m)-linux-gnu.2.17"
    fi
    # shellcheck disable=SC2086
    zig build-obj $ZIG_FLAGS "$HOST/$program.zig" -femit-bin="$OUT/zig-$program.o" \
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
USAGE="usage: run [--bytes] [--interp[=levels]] [--text] <program-file> [step-budget]   (default budget: 100000000 machine steps)"
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
# A step budget charges the operation's cost before the operation runs.
# Multiplication costs the product of the operands' bit lengths, so the same
# budget finishes a small product and stops a large one.
printf 'mul 2 3\n' > "$OUT/small-mul.hom"
expect "6" "$OUT/small-mul.hom" 200
python3 -c 'print("mul", 10**40 - 1, 10**40 - 1)' > "$OUT/big-mul.hom"
expect "no result within 200 steps" "$OUT/big-mul.hom" 200
python3 -c 'print((10**40 - 1)**2)' > "$OUT/big-mul.expected"
expect "$(cat "$OUT/big-mul.expected")" "$OUT/big-mul.hom" 200000
# The interpreter performs the program's operation as the same machine
# primitive, so it pays the same charge and its own steps on top: a budget
# that bounds the program bounds it through the interpreter, and a budget the
# program finishes in (18000 here) is not enough through one interpreter.
expect "no result within 200 steps" --interp "$OUT/big-mul.hom" 200
expect "no result within 200 steps" --interp=2 "$OUT/big-mul.hom" 200
expect "$(cat "$OUT/big-mul.expected")" "$OUT/big-mul.hom" 18000
expect "no result within 18000 steps" --interp "$OUT/big-mul.hom" 18000
expect "$(cat "$OUT/big-mul.expected")" --interp "$OUT/big-mul.hom" 200000
echo "a step budget bounds a large operation and lets a small one finish"
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
# An array literal of 66,000 items. The source reader used to recurse once per
# item and crash; 30,000 items was fine. The printed text is the literal.
awk 'BEGIN { printf "["; for (i = 0; i < 65999; i++) printf "0, "; printf "0]\n" }' > "$OUT/many.hom"
"$OUT/run" "$OUT/many.hom" > "$OUT/many.txt"
cmp "$OUT/many.hom" "$OUT/many.txt"
"$OUT/bytes" "$OUT/many.hom" > "$OUT/many.bytes"
"$OUT/run" --bytes "$OUT/many.bytes" > "$OUT/many-bytes.txt"
cmp "$OUT/many.hom" "$OUT/many-bytes.txt"
echo "array of 66000 items reads from source and from bytes"
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
expect "bytes error: a kind of value that is not a number, an array, a text or a name" --bytes "$EXAMPLES/append.hom"
refuse "$USAGE" --bytes
refuse "run: cannot read the program file: FileNotFound" --bytes "$EXAMPLES/missing.hom"

# The metacircular interpreter: the program's byte form, as data, is handed to
# the closed term `interp` on the machine, and the outcome it answers is read
# back. It prints what the program prints run directly (`Reflect.reflective`).
# `--interp=2` runs the interpreter interpreting the interpreter.
sameThroughInterp() {
    file="$1"; levels="$2"; shift_budget="${3:-}"
    "$OUT/bytes" "$file" > "$OUT/program.bytes"
    # shellcheck disable=SC2086
    direct="$("$OUT/run" "$file" $shift_budget)"
    for mode in "--interp=$levels" "--bytes --interp=$levels"; do
        input="$file"
        case "$mode" in --bytes*) input="$OUT/program.bytes" ;; esac
        # shellcheck disable=SC2086
        got="$("$OUT/run" $mode "$input" $shift_budget)"
        if [ "$direct" != "$got" ]; then
            echo "run $mode $file: expected '$direct', got '$got'" >&2
            exit 1
        fi
    done
    echo "run --interp=$levels $(basename "$file") => $(printf '%s' "$got" | cut -c1-60)"
}
printf 'case fn x -> x\n  0 -> 1\n  m + 1 -> m\n' > "$OUT/wrong.hom"
for levels in 0 1 2; do
    sameThroughInterp "$EXAMPLES/append.hom" "$levels"
    sameThroughInterp "$EXAMPLES/code.hom" "$levels"
    sameThroughInterp "$EXAMPLES/factorial.hom" "$levels"
    sameThroughInterp "$OUT/identity.hom" "$levels"
    sameThroughInterp "$OUT/wrong.hom" "$levels"
done
# A third language: Brainfuck written in this one, running Hello World, run
# through the interpreter.
expect "[72, 101, 108, 108, 111, 32, 87, 111, 114, 108, 100, 33, 10]" "$EXAMPLES/brainfuck.hom"
sameThroughInterp "$EXAMPLES/brainfuck.hom" 1
# A quine: its output is its own data form. Run as code, the output gives
# itself back, and the interpreter gives the same output.
quine="$("$OUT/run" "$EXAMPLES/quine.hom")"
printf 'interpret %s\n' "$quine" > "$OUT/quine-again.hom"
expect "[0, [1, $quine]]" "$OUT/quine-again.hom"
sameThroughInterp "$EXAMPLES/quine.hom" 2
# Strings: a string literal is a text and a character literal is a number. A
# text prints in quotes with the reader's escapes, and what is printed reads
# back as the same text. `--text` writes a result that is a text raw, with no
# quotes and no escapes, and any other result as it is written without the
# flag: an array of code points is not a text.
printf '"h\\\\i\\n"\n' > "$OUT/string.hom"
expect '"h\\i\n"' "$OUT/string.hom"
expect "$(printf 'h\\i\n')" --text "$OUT/string.hom"
"$OUT/run" "$OUT/string.hom" > "$OUT/string-again.hom"
expect '"h\\i\n"' "$OUT/string-again.hom"
printf 'equal "h\\\\i\\n" [104, 92, 105, 10]\n' > "$OUT/string-equal.hom"
expect "0" "$OUT/string-equal.hom"
printf 'def count t =\n  case t\n    [] -> 0\n    [c, ...rest] ->\n      case equal c '"'i'"'\n        0 -> count rest\n        _ -> add 1 (count rest)\n\ncount "h\\\\i\\n"\n' > "$OUT/string-count.hom"
expect "1" "$OUT/string-count.hom"
printf "['a', '\\\\n', '\\\\'']\n" > "$OUT/chars.hom"
expect "[97, 10, 39]" "$OUT/chars.hom"
printf '"h\303\251 \342\206\222"\n' > "$OUT/utf8.hom"
expect "$(printf '"h\303\251 \342\206\222"')" "$OUT/utf8.hom"
expect "$(printf 'h\303\251 \342\206\222')" --text "$OUT/utf8.hom"
expect "$(printf 'h\303\251 \342\206\222')" --text --interp "$OUT/utf8.hom"
"$OUT/bytes" "$OUT/utf8.hom" > "$OUT/utf8.bytes"
expect "$(printf 'h\303\251 \342\206\222')" --text --bytes "$OUT/utf8.bytes"
# The byte form of a string literal: `[2, text]`, the text as a CBOR text
# string of its UTF-8, here 7 bytes.
if [ "$(od -An -tx1 "$OUT/utf8.bytes" | tr -d ' \n')" != "82026768c3a920e28692" ]; then
    echo "bytes: a string literal is not 82 02 67 and its UTF-8" >&2
    exit 1
fi
printf 'codes "h\303\251 \342\206\222"\n' > "$OUT/codes.hom"
expect "[104, 233, 32, 8594]" "$OUT/codes.hom"
expect "[104, 233, 32, 8594]" --text "$OUT/codes.hom"
printf 'text [104, ...codes "i"]\n' > "$OUT/text.hom"
expect '"hi"' "$OUT/text.hom"
expect "hi" --text "$OUT/text.hom"
expect "hi" --text --interp=2 "$OUT/text.hom"
printf '[1, ..."hi"]\n' > "$OUT/cons-text.hom"
expect "[1, 104, 105]" "$OUT/cons-text.hom"
printf '"a" + 1\n' > "$OUT/succ-text.hom"
expect "error: wrong" "$OUT/succ-text.hom"
expect "error: wrong" --text --interp "$OUT/succ-text.hom"
expect "[1, 2, 3, 4]" --text "$EXAMPLES/append.hom"
expect "<function>" --text "$OUT/identity.hom"
printf '"no end\n' > "$OUT/open-string.hom"
expect "syntax error: line 1, column 1: a string that does not end on its line, or an escape other than \\n \\t \\\\ \\\" \\'" "$OUT/open-string.hom"
# An array pattern on a text names code points, and the rest is a text.
printf 'case "abcd"\n  [a, b, ...rest] -> [a, b, rest]\n' > "$OUT/text-pattern.hom"
expect '[97, 98, "cd"]' "$OUT/text-pattern.hom"
printf 'case "abc"\n  [a, b, c] -> [c, b, a]\n' > "$OUT/text-three.hom"
expect "[99, 98, 97]" "$OUT/text-three.hom"
for levels in 1 2; do
    sameThroughInterp "$OUT/string.hom" "$levels"
    sameThroughInterp "$OUT/text.hom" "$levels"
    sameThroughInterp "$OUT/cons-text.hom" "$levels"
    sameThroughInterp "$OUT/succ-text.hom" "$levels"
    sameThroughInterp "$OUT/text-pattern.hom" "$levels"
done
# Programs that use them. A calculator reads an expression from text; words
# are sorted under three orders passed as functions; a program builds the code
# of a power function as data and runs it. The first two end in `text`, so
# their result is a text: in quotes without the flag, raw with it. Each prints
# the same through the interpreter.
expect '"2 * (3 + 4) * 5 - 100 / (7 - 2) = 50"' "$EXAMPLES/calc.hom"
expect "2 * (3 + 4) * 5 - 100 / (7 - 2) = 50" --text "$EXAMPLES/calc.hom"
expect "2 * (3 + 4) * 5 - 100 / (7 - 2) = 50" --text --interp "$EXAMPLES/calc.hom"
expect '"brown dog fox jumps lazy over quick the the\ndog fox the the lazy over brown jumps quick\nthe the quick over lazy jumps fox dog brown\n"' "$EXAMPLES/words.hom"
expect "brown dog fox jumps lazy over quick the the
dog fox the the lazy over brown jumps quick
the the quick over lazy jumps fox dog brown" --text "$EXAMPLES/words.hom"
expect "brown dog fox jumps lazy over quick the the
dog fox the the lazy over brown jumps quick
the the quick over lazy jumps fox dog brown" --text --interp "$EXAMPLES/words.hom"
sameThroughInterp "$EXAMPLES/calc.hom" 1
sameThroughInterp "$EXAMPLES/words.hom" 1
sameThroughInterp "$EXAMPLES/power.hom" 1
case "$("$OUT/run" "$EXAMPLES/power.hom")" in
    *", [0, [1, 8]], [0, [1, 1024]], [0, [1, 1267650600228229401496703205376]]]") ;;
    *) echo "power.hom: the built code did not give 2^3, 2^10 and 2^100" >&2; exit 1 ;;
esac
sameThroughInterp "$EXAMPLES/forever.hom" 1 5000
# Definitions that name one another, and array patterns that name a length.
# Two definitions in a ring; a later definition used with no ring; a name that
# is bound where it is used staying what it was; an arm for exactly three
# items; another length going to the catch-all arm, and to `wrong` with none;
# an arm for two items or more. The calculator above is a ring of five. Each
# prints the same through the interpreter.
printf 'def even n =\n  case n\n    0 -> 1\n    m + 1 -> odd m\n\ndef odd n =\n  case n\n    0 -> 0\n    m + 1 -> even m\n\n[even 10, odd 10, even 7, odd 7]\n' > "$OUT/ring.hom"
expect "[1, 0, 0, 1]" "$OUT/ring.hom"
printf 'def a = [1, ...b]\ndef b = [2]\na\n' > "$OUT/later.hom"
expect "[1, 2]" "$OUT/later.hom"
printf 'def f x = add x 1\ndef add a b = 99\n[f 1, add 1 1]\n' > "$OUT/bound.hom"
expect "[2, 99]" "$OUT/bound.hom"
printf 'case [1, 2, 3]\n  [a, b, c] -> [c, b, a]\n' > "$OUT/three.hom"
expect "[3, 2, 1]" "$OUT/three.hom"
printf 'case [1, 2]\n  [a, b, c] -> [c, b, a]\n  other -> [9, ...other]\n' > "$OUT/other-length.hom"
expect "[9, 1, 2]" "$OUT/other-length.hom"
# A catch-all that the written arms leave nothing for is not read, as before
# array arms had lengths: it may name what is not bound, and the program is the
# term it was, the one the same case reads as with its scrutinee bound by a let.
printf 'case 0\n  0 -> 7\n  m + 1 -> 8\n  [] -> 9\n  [h, ...t] -> 10\n  _ -> ghost\n' > "$OUT/unread-arm.hom"
expect "7" "$OUT/unread-arm.hom"
expect "7" --interp "$OUT/unread-arm.hom"
printf 'let s = 0\ncase s\n  0 -> 7\n  m + 1 -> 8\n  [] -> 9\n  [h, ...t] -> 10\n' > "$OUT/unread-arm-let.hom"
"$OUT/bytes" "$OUT/unread-arm.hom" > "$OUT/unread-arm.bytes"
"$OUT/bytes" "$OUT/unread-arm-let.hom" > "$OUT/unread-arm-let.bytes"
cmp "$OUT/unread-arm.bytes" "$OUT/unread-arm-let.bytes"
printf 'case 0\n  0 -> 7\n  m + 1 -> 8\n  [a, b] -> 10\n  _ -> ghost\n' > "$OUT/live-arm.hom"
expect "syntax error: line 5, column 8: unbound name \`ghost\`" "$OUT/live-arm.hom"
printf 'case [1, 2]\n  [a, b, c] -> [c, b, a]\n' > "$OUT/no-arm.hom"
expect "error: wrong" "$OUT/no-arm.hom"
printf 'case [1, 2, 3, 4]\n  [a, b, ...rest] -> [b, a, rest]\n' > "$OUT/at-least.hom"
expect "[2, 1, [3, 4]]" "$OUT/at-least.hom"
for program in ring later bound three other-length no-arm at-least; do
    sameThroughInterp "$OUT/$program.hom" 1
done
sameThroughInterp "$OUT/ring.hom" 2
# What the reader refuses: a pattern inside a pattern, an arm that an arm above
# it leaves nothing for, and a later definition on the far side of a `let`.
printf 'case [1, 2]\n  [a, [b]] -> a\n' > "$OUT/nested-pattern.hom"
expect 'syntax error: line 2, column 7: an item of an array pattern is a name or `_`: `[a, b]` or `[a, b, ...rest]`' "$OUT/nested-pattern.hom"
printf 'case [1, 2]\n  [a, ...rest] -> a\n  [a, b] -> b\n' > "$OUT/dead-arm.hom"
expect 'syntax error: line 3, column 3: this arm is never taken: an arm above it takes every array this one would' "$OUT/dead-arm.hom"
printf 'def f x = g x\nlet y = 1\ndef g x = 8\nf 1\n' > "$OUT/split-run.hom"
expect 'syntax error: line 1, column 11: unbound name `g`' "$OUT/split-run.hom"
sameThroughInterp "$OUT/wide.hom" 1
expect "[1, 2, 3, 4]" --interp "$EXAMPLES/append.hom"
expect "bytes error: the value is not a program" --bytes --interp "$OUT/empty-array.bytes"
refuse "run: the interpreter levels must be a whole number" --interp=x "$EXAMPLES/append.hom"
refuse "$USAGE" --interp
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

# The chan command: a program run as the first of several processes that talk
# over channels. With no schedule the kernel chooses the events and prints the
# schedule it went through; given that schedule back, it prints the same text.
channels() {
    wanted="$1"
    shift
    got="$("$OUT/chan" "$@")"
    if [ "$got" != "$wanted" ]; then
        echo "chan $*: expected '$wanted', got '$got'" >&2
        exit 1
    fi
    echo "chan $* => $(echo "$got" | tr '\n' '|')"
}
channels "schedule: [[0, 0, 0], [1, 0], [0, 0, 1], [2, 0, 1], [2, 0, 1], [2, 1, 0]]
process 0: 42; holds [#1, #0]
process 1: [41]; holds [#1, #0]
no event is offered" "$EXAMPLES/ping.hom"
# Replay: the schedule line of a run, given back, gives the same text.
"$OUT/chan" "$EXAMPLES/ping.hom" > "$OUT/ping.txt"
sed -n 's/^schedule: //p' "$OUT/ping.txt" > "$OUT/ping.schedule"
"$OUT/chan" "$EXAMPLES/ping.hom" "$OUT/ping.schedule" > "$OUT/ping-replay.txt"
cmp "$OUT/ping.txt" "$OUT/ping-replay.txt"
echo "chan: the recorded schedule replays to the same text"
# A line of thirteen processes finds the primes to 30, and its schedule replays.
"$OUT/chan" "$EXAMPLES/sieve.hom" - 100000000 100000 > "$OUT/sieve.txt"
want "$(sed -n 's/^process 0: \(.*\); holds.*/\1/p' "$OUT/sieve.txt")" "[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]"
want "$(tail -1 "$OUT/sieve.txt")" "no event is offered"
sed -n 's/^schedule: //p' "$OUT/sieve.txt" > "$OUT/sieve.schedule"
"$OUT/chan" "$EXAMPLES/sieve.hom" "$OUT/sieve.schedule" > "$OUT/sieve-replay.txt"
cmp "$OUT/sieve.txt" "$OUT/sieve-replay.txt"
echo "chan: the sieve finds the primes to 30 and replays"
# Numbers in code and messages hand over nothing. Each filter is started on its
# own quoted code, which is full of numbers, and the numbers 2 to 30 and 0 go
# by as messages: no process after process 2 holds #0, the channel only the
# first three were given, and no process holds a name twice.
want "$(grep '^process' "$OUT/sieve.txt")" "process 0: [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]; holds [#1, #0]
process 1: []; holds [#0]
process 2: [2]; holds [#2, #1, #0]
process 3: [3]; holds [#3, #2, #1]
process 4: [5]; holds [#4, #3, #1]
process 5: [7]; holds [#5, #4, #1]
process 6: [11]; holds [#6, #5, #1]
process 7: [13]; holds [#7, #6, #1]
process 8: [17]; holds [#8, #7, #1]
process 9: [19]; holds [#9, #8, #1]
process 10: [23]; holds [#10, #9, #1]
process 11: [29]; holds [#11, #10, #1]
process 12: []; holds [#11, #1]"
if ! awk -F'; holds ' '/^process/ {
        count++
        split("", seen)
        n = split(substr($2, 2, length($2) - 2), held, ", ")
        for (i = 1; i <= n; i++) { if (held[i] in seen) bad = 1; seen[held[i]] = 1 }
        split($1, word, "[ :]")
        if (word[2] > 2 && ("#0" in seen)) bad = 1
    } END { exit (bad || count != 13) }' "$OUT/sieve.txt"; then
    echo "chan: in the sieve a process holds a name twice, or a process after process 2 holds #0" >&2
    exit 1
fi
echo "chan: in the sieve no process holds a name twice and none after process 2 holds #0"
# A prefix of the schedule stops part way, and the chooser has a next event.
printf '[[0, 0, 0], [1, 0]]\n' > "$OUT/prefix.schedule"
channels "schedule: [[0, 0, 0], [1, 0]]
process 0: waiting on [0]; holds [#0]
process 1: waiting on [2, #0]; holds [#0]
an event is offered" "$EXAMPLES/ping.hom" "$OUT/prefix.schedule"
# One message, two receivers: the schedule decides, and supplies the name.
channels "schedule: [[0, 0, 0], [1, 0], [1, 0], [2, 0, 1]]
process 0: []; holds [#0]
process 1: [7]; holds [#0]
process 2: waiting on [2, #0]; holds [#0]
no event is offered" "$EXAMPLES/race.hom"
channels "schedule: [[0, 0, 5], [1, 0], [1, 0], [2, 0, 2]]
process 0: []; holds [#5]
process 1: waiting on [2, #5]; holds [#5]
process 2: [7]; holds [#5]
no event is offered" "$EXAMPLES/race.hom" "$EXAMPLES/race.schedule"
# A name in hand is not a name held. The first process splices the name into
# the program of its start request and starts it on []: the second process has
# the name value and does not hold it. Nothing is chosen, and a schedule that
# says they meet is refused.
channels "schedule: [[0, 0, 0], [1, 0]]
process 0: waiting on [1, #0, 7]; holds [#0]
process 1: waiting on [2, #0]; holds []
no event is offered" "$EXAMPLES/guess.hom"
channels "schedule: [[0, 0, 0], [1, 0]]
process 0: waiting on [1, #0, 7]; holds [#0]
process 1: waiting on [2, #0]; holds []
refused: [2, 0, 1] cannot happen" "$EXAMPLES/guess.hom" "$EXAMPLES/guess.schedule"
# A number is not a name: [2, 0] with the number 0 is a request to the outside.
# No event is offered, a schedule that says the two meet is refused, and the
# schedule can answer it from outside.
channels "schedule: [[0, 0, 0], [1, 0]]
process 0: waiting on [1, #0, 7]; holds [#0]
process 1: waiting on [2, 0]; holds []
no event is offered" "$EXAMPLES/number.hom"
channels "schedule: [[0, 0, 0], [1, 0]]
process 0: waiting on [1, #0, 7]; holds [#0]
process 1: waiting on [2, 0]; holds []
refused: [2, 0, 1] cannot happen" "$EXAMPLES/number.hom" "$EXAMPLES/number.schedule"
printf '[[0, 0, 0], [1, 0], [3, 1, 9]]\n' > "$OUT/number-outside.schedule"
channels "schedule: [[0, 0, 0], [1, 0], [3, 1, 9]]
process 0: waiting on [1, #0, 7]; holds [#0]
process 1: 9; holds []
no event is offered" "$EXAMPLES/number.hom" "$OUT/number-outside.schedule"
# What hands a name over. The same program as guess.hom started on its own
# body, quoted code that holds [2, #0]: the name is in the start data, the
# process started holds it, and the two meet.
printf 'ask [0] (fn ch ->\n  let body = quote (ask [2, ~[2, ch]] (fn x -> [x]))\n  ask [3, [1, body], body] (fn started ->\n    ask [1, ch, 7] (fn sent -> [])))\n' > "$OUT/quoted-start.hom"
channels "schedule: [[0, 0, 0], [1, 0], [2, 0, 1]]
process 0: []; holds [#0]
process 1: [7]; holds [#0]
no event is offered" "$OUT/quoted-start.hom"
# A name three arrays deep in a message is handed to the receiver; the same
# message with the number of that name hands over nothing.
for item in other 1; do
    printf 'let waiter = quote (fn meet -> ask [2, meet] (fn m -> m))\nask [0] (fn meet ->\n  ask [0] (fn other ->\n    ask [3, waiter, meet] (fn started ->\n      ask [1, meet, [[[2, %s]]]] (fn sent -> []))))\n' "$item" > "$OUT/nested-$item.hom"
done
channels "schedule: [[0, 0, 0], [0, 0, 1], [1, 0], [2, 0, 1]]
process 0: []; holds [#1, #0]
process 1: [[[2, #1]]]; holds [#1, #0]
no event is offered" "$OUT/nested-other.hom"
channels "schedule: [[0, 0, 0], [0, 0, 1], [1, 0], [2, 0, 1]]
process 0: []; holds [#1, #0]
process 1: [[[2, 1]]]; holds [#0]
no event is offered" "$OUT/nested-1.hom"
# A name is a value of its own kind: `equal` tells it from its number, `add`
# does not take it, `case` and `+ 1` see its number. It is written #0, which
# is not program text.
printf 'ask [0] (fn ch ->\n  case ch\n    0 -> [equal ch 0, equal ch ch, add ch 0, ch + 1, ch]\n    m + 1 -> m)\n' > "$OUT/name-kind.hom"
printf '[[0, 0, 0]]\n' > "$OUT/name-kind.schedule"
channels "schedule: [[0, 0, 0]]
process 0: [0, 1, [], 1, #0]; holds [#0]
no event is offered" "$OUT/name-kind.hom" "$OUT/name-kind.schedule"
printf '#0\n' > "$OUT/name-text.hom"
expect "syntax error: line 1, column 1: unexpected character; programs are ASCII text" "$OUT/name-text.hom"
# A name that was already made is refused.
printf '[[0, 0, 3], [1, 0], [0, 0, 3]]\n' > "$OUT/twice.schedule"
channels "schedule: [[0, 0, 3], [1, 0]]
process 0: waiting on [0]; holds [#3]
process 1: waiting on [2, #3]; holds [#3]
refused: [0, 0, 3] cannot happen" "$EXAMPLES/ping.hom" "$OUT/twice.schedule"
# A request that is none of the four is the outside's, answered by the schedule.
printf 'ask [9] (fn a -> add a 1)\n' > "$OUT/outside.hom"
printf '[[3, 0, 41]]\n' > "$OUT/outside.schedule"
channels "schedule: []
process 0: waiting on [9]; holds []
no event is offered" "$OUT/outside.hom"
channels "schedule: [[3, 0, 41]]
process 0: 42; holds []
no event is offered" "$OUT/outside.hom" "$OUT/outside.schedule"
# Choosing stops at the event limit.
LIMITED="$("$OUT/chan" "$EXAMPLES/spawns.hom" - 100000000 3)"
want "$(echo "$LIMITED" | sed -n 1p)" "schedule: [[1, 0], [1, 1], [1, 2]]"
want "$(echo "$LIMITED" | tail -1)" "an event is offered"
want "$(echo "$LIMITED" | grep -c '^process')" "4"
echo "chan: choosing stopped at the event limit"
# After a refusal the printed schedule replays to the same processes; the last
# line differs, because the refused event is not in it.
"$OUT/chan" "$EXAMPLES/guess.hom" "$EXAMPLES/guess.schedule" > "$OUT/refused.txt"
sed -n 's/^schedule: //p' "$OUT/refused.txt" > "$OUT/refused.schedule"
"$OUT/chan" "$EXAMPLES/guess.hom" "$OUT/refused.schedule" > "$OUT/refused-replay.txt"
want "$(sed '$d' "$OUT/refused-replay.txt")" "$(sed '$d' "$OUT/refused.txt")"
want "$(tail -1 "$OUT/refused-replay.txt")" "no event is offered"
# An offered event may not halt: the chooser offers it without running it.
printf 'let w = fn x -> x x\nask [0] (fn a -> w w)\n' > "$OUT/stuck.hom"
want "$("$OUT/chan" "$OUT/stuck.hom" - 5000 0 | tail -1)" "an event is offered"
want "$("$OUT/chan" "$OUT/stuck.hom" - 5000 1 | tail -1)" "no result within 5000 steps of a turn, at [0, 0, 0]"
echo "chan: the last line says what is offered, not what will finish"
channels "schedule: []
process 0: [1, 2, 3, 4]; holds []
no event is offered" "$EXAMPLES/append.hom"
channels "no result within 5000 steps of a turn" "$EXAMPLES/forever.hom" - 5000
channels "schedule: entry 0 is not an event" "$OUT/outside.hom" "$EXAMPLES/ask.answers"
channels "schedule: not an array" "$OUT/outside.hom" "$EXAMPLES/factorial.hom"

CHANUSAGE="usage: chan <program-file> [schedule-file | -] [step-budget] [event-limit]   (default budget: 100000000 machine steps for each turn; default limit: 10000 events)"
refuseChan() {
    wanted="$1"
    shift
    status=0
    "$OUT/chan" "$@" > "$OUT/refuse.out" 2> "$OUT/refuse.err" || status=$?
    printf '%s\n' "$wanted" > "$OUT/refuse.expected"
    if [ "$status" -ne 2 ] || [ -s "$OUT/refuse.out" ] || ! cmp -s "$OUT/refuse.expected" "$OUT/refuse.err"; then
        echo "chan $*: expected exit 2 and no output; got exit $status" >&2
        exit 1
    fi
    echo "chan refused: $wanted"
}
refuseChan "$CHANUSAGE"
refuseChan "$CHANUSAGE" "$EXAMPLES/ping.hom" - 1 1 extra
refuseChan "chan: cannot read the program file: FileNotFound" "$EXAMPLES/missing.hom"
refuseChan "chan: cannot read the schedule file: FileNotFound" "$EXAMPLES/ping.hom" "$EXAMPLES/missing.schedule"
: > "$OUT/empty.schedule"
refuseChan "chan: the schedule file is empty" "$EXAMPLES/ping.hom" "$OUT/empty.schedule"
refuseChan "chan: the step budget must be a whole number" "$EXAMPLES/ping.hom" - many
refuseChan "chan: the event limit must be a whole number" "$EXAMPLES/ping.hom" - 5000 many
echo "chan command checks passed"

# The vm command: a program handling a log, with its state kept in a directory.
VMSTORE="$OUT/vm-store"
rm -rf "$VMSTORE"
mkdir -p "$VMSTORE"
# Run the command; its lines are in $STANDS (first line), $ENTRIES and $STATE.
vm() {
    "$OUT/vm" "$VMSTORE" "$@" > "$OUT/vm.txt"
    STANDS="$(sed -n 1p "$OUT/vm.txt")"
    ENTRIES="$(sed -n 's/^entries: //p' "$OUT/vm.txt")"
    STATE="$(sed -n 's/^state: //p' "$OUT/vm.txt")"
    echo "vm $(echo "$1 $(basename "$2" | cut -c1-12) $(basename "$3")") => $STANDS ($ENTRIES; state $(echo "$STATE" | cut -c1-12))"
}
wantVm() {
    if [ "$1" != "$2" ]; then
        echo "vm: expected '$2', got '$1'" >&2
        exit 1
    fi
}
# From the start with the whole log.
vm start "$EXAMPLES/ask.hom" "$EXAMPLES/ask.log"
wantVm "$STANDS" "42"
wantVm "$ENTRIES" "2 given, 2 acted on"
WHOLE="$STATE"
wantVm "${#WHOLE}" "64"
# The result is what the answers alone give.
wantVm "$STANDS" "$("$OUT/ask" "$EXAMPLES/ask.hom" "$EXAMPLES/ask.answers" | tail -1)"
# Stop after the first entry, then hand the whole log to the kept state in a
# new process: it acts on the entry it has not seen and reaches the same state.
vm start "$EXAMPLES/ask.hom" "$EXAMPLES/ask-one.log"
wantVm "$STANDS" "waiting on [2, 20]"
wantVm "$ENTRIES" "1 given, 1 acted on"
PART="$STATE"
vm from "$PART" "$EXAMPLES/ask.log"
wantVm "$STANDS" "42"
wantVm "$ENTRIES" "2 given, 1 acted on"
wantVm "$STATE" "$WHOLE"
# Lose every kept state and run the log again: the state has the same name.
rm -rf "$VMSTORE"
mkdir -p "$VMSTORE"
vm start "$EXAMPLES/ask.hom" "$EXAMPLES/ask.log"
wantVm "$STATE" "$WHOLE"
# Entries delivered again change nothing.
vm start "$EXAMPLES/ask.hom" "$EXAMPLES/ask-again.log"
wantVm "$ENTRIES" "5 given, 2 acted on"
wantVm "$STATE" "$WHOLE"
# An entry is named by the hash of all of it: the mark of another entry with a
# different answer is a different entry, and is acted on.
# A link mark names the previous entry. The chain is printed by LogCheck,
# which hashed it the way the kernel does.
sed -n 's/^chain-log: //p' "$OUT/log.txt" > "$OUT/chain.log"
test -s "$OUT/chain.log"
vm start "$EXAMPLES/ask.hom" "$OUT/chain.log"
wantVm "$STANDS" "42"
printf '[[[0, [], 0], 20], [[0, 1, 1], 22]]\n' > "$OUT/bad-parent.log"
wantVm "$("$OUT/vm" "$VMSTORE" start "$EXAMPLES/ask.hom" "$OUT/bad-parent.log")" "log: entry 1 does not name the entry before it"
# The second entry's parent stays the first entry's name; only its order changes.
sed 's/, 1], 22]/, 5], 22]/' "$OUT/chain.log" > "$OUT/bad-order.log"
wantVm "$("$OUT/vm" "$VMSTORE" start "$EXAMPLES/ask.hom" "$OUT/bad-order.log")" "log: entry 1 is out of order"
# The host checks an Ed25519 signature over the log and does not hand the
# signature line to the kernel. A good one is accepted; a bad one is refused.
SEED=0000000000000000000000000000000000000000000000000000000000000001
"$OUT/sign" "$SEED" "$OUT/chain.log" > "$OUT/chain.sig"
{ cat "$OUT/chain.sig"; cat "$OUT/chain.log"; } > "$OUT/chain-signed.log"
vm start "$EXAMPLES/ask.hom" "$OUT/chain-signed.log"
wantVm "$STANDS" "42"
# Flip one byte of the signature. The refusal is on stderr and exits 2.
python3 - "$OUT/chain.sig" "$OUT/chain.log" "$OUT/bad-sig.log" << 'PY'
import sys
sig, body, dest = sys.argv[1:]
line = open(sig).read().rstrip("\n")
head, hexsig = line.rsplit(" ", 1)
last = format((int(hexsig[-2:], 16) ^ 1), "02x")
open(dest, "w").write(head + " " + hexsig[:-2] + last + "\n" + open(body).read())
PY
status=0
got="$("$OUT/vm" "$VMSTORE" start "$EXAMPLES/ask.hom" "$OUT/bad-sig.log" 2>&1)" || status=$?
wantVm "$got" "vm: the signature is not valid"
wantVm "$status" "2"
echo "a log entry names the one before it, and the host checks the signature"
printf '[[1, 20], [1, 22]]\n' > "$OUT/one-mark.log"
vm start "$EXAMPLES/ask.hom" "$OUT/one-mark.log"
wantVm "$STANDS" "42"
wantVm "$ENTRIES" "2 given, 2 acted on"
if [ "$STATE" = "$WHOLE" ]; then
    echo "vm: another entry under the same mark gave the same state" >&2
    exit 1
fi
# A finished VM given the log again is the same state, and nothing is written.
vm from "$WHOLE" "$EXAMPLES/ask-again.log"
wantVm "$STANDS" "42"
wantVm "$ENTRIES" "5 given, 0 acted on"
wantVm "$STATE" "$WHOLE"
wantVm "$(sed -n 's/^store: fetched [0-9]*, wrote //p' "$OUT/vm.txt")" "0"
# The same entries in the other order are another state: the names of the
# entries are recorded in the order they were acted on.
printf '[[2, 22], [1, 20]]\n' > "$OUT/other.log"
vm start "$EXAMPLES/ask.hom" "$OUT/other.log"
if [ "$STATE" = "$WHOLE" ]; then
    echo "vm: another order gave the same state" >&2
    exit 1
fi
# A program with a long list: the state after one entry is kept in many
# pieces, and restarted on the whole log it reaches the same state.
printf '[[[7], 20]]\n' > "$OUT/keep-one.log"
printf '[[[7], 20], [8, 22]]\n' > "$OUT/keep.log"
vm start "$EXAMPLES/keep.hom" "$OUT/keep.log"
wantVm "$STANDS" "[2000, 42]"
BIG="$STATE"
vm start "$EXAMPLES/keep.hom" "$OUT/keep-one.log"
wantVm "$STANDS" "waiting on [2, 20]"
vm from "$STATE" "$OUT/keep.log"
wantVm "$STATE" "$BIG"
# With no entry, a VM waits on its first request; a program that asks nothing
# is finished at once.
printf '[]\n' > "$OUT/empty.log"
vm start "$EXAMPLES/ask.hom" "$OUT/empty.log"
wantVm "$STANDS" "waiting on [1]"
vm start "$EXAMPLES/append.hom" "$EXAMPLES/ask.log"
wantVm "$STANDS" "[1, 2, 3, 4]"
wantVm "$ENTRIES" "2 given, 0 acted on"
# The kernel's text for a bad log, a bad root, and a turn that does not end.
wantVm "$("$OUT/vm" "$VMSTORE" start "$EXAMPLES/ask.hom" "$EXAMPLES/ask.answers")" "log: entry 0 is not a mark and an answer"
wantVm "$("$OUT/vm" "$VMSTORE" start "$EXAMPLES/ask.hom" "$EXAMPLES/factorial.hom")" "log: not an array"
wantVm "$("$OUT/vm" "$VMSTORE" from nothex "$EXAMPLES/ask.log")" "store error: a root is 64 hex digits"
wantVm "$("$OUT/vm" "$VMSTORE" start "$EXAMPLES/forever.hom" "$EXAMPLES/ask.log" 5000 | sed -n 1p)" "no result within 5000 steps of a turn"
# A root that names a piece which is not a state.
PIECE="$(ls "$STORE" | sed -n 1p)"
cp "$STORE/$PIECE" "$VMSTORE/$PIECE"
wantVm "$("$OUT/vm" "$VMSTORE" from "$PIECE" "$EXAMPLES/ask.log" | sed -n 1p)" "store error: the root is not a kept state"
# A state that is not in the store: exit 3 and nothing printed.
status=0
"$OUT/vm" "$VMSTORE" from "$(printf '%064d' 0)" "$EXAMPLES/ask.log" > "$OUT/refuse.out" 2> "$OUT/refuse.err" || status=$?
printf 'vm: the store lacks piece %064d\n' 0 > "$OUT/refuse.expected"
if [ "$status" != 3 ] || [ -s "$OUT/refuse.out" ] || ! cmp -s "$OUT/refuse.expected" "$OUT/refuse.err"; then
    echo "vm with the state missing: expected exit 3 and no output; got exit $status" >&2
    exit 1
fi
refuseVm() {
    status=0
    "$OUT/vm" "$@" > "$OUT/refuse.out" 2> "$OUT/refuse.err" || status=$?
    if [ "$status" != 2 ] || [ -s "$OUT/refuse.out" ] || ! [ -s "$OUT/refuse.err" ]; then
        echo "vm $*: expected exit 2, no output and a message; got exit $status" >&2
        exit 1
    fi
    echo "vm refused: $(sed -n 1p "$OUT/refuse.err")"
}
refuseVm
refuseVm "$VMSTORE" start "$EXAMPLES/ask.hom"
refuseVm "$VMSTORE" resume "$EXAMPLES/ask.hom" "$EXAMPLES/ask.log"
refuseVm "$VMSTORE" start "$EXAMPLES/missing.hom" "$EXAMPLES/ask.log"
refuseVm "$VMSTORE" start "$EXAMPLES/ask.hom" "$EXAMPLES/missing.log"
refuseVm "$OUT/no-such-store" start "$EXAMPLES/ask.hom" "$EXAMPLES/ask.log"
refuseVm "$VMSTORE" start "$EXAMPLES/ask.hom" "$EXAMPLES/ask.log" many
refuseVm "$VMSTORE" start "$EXAMPLES/ask.hom" "$EXAMPLES/ask.log" 1 extra
echo "vm command checks passed"

# The node command: several processes applying a log, kept in a directory.
NODESTORE="$OUT/node-store"
rm -rf "$NODESTORE"
mkdir -p "$NODESTORE"
# Run the command; its text is in $OUT/node.out and its root in $STATE.
node() {
    "$OUT/node" "$NODESTORE" "$@" > "$OUT/node.out"
    STATE="$(sed -n 's/^state: //p' "$OUT/node.out")"
    echo "node $1 $(basename "$2" | cut -c1-12) $(basename "$3") => $(sed '$d' "$OUT/node.out" | sed 's/^state: \(.\{12\}\).*/state: \1/' | tr '\n' '|')"
}
wantNode() {
    if [ "$1" != "$2" ]; then
        echo "node: expected '$2', got '$1'" >&2
        exit 1
    fi
}
# The whole log from the start: the processes end where chan's run ends.
node start "$EXAMPLES/ping.hom" "$EXAMPLES/ping.log"
wantNode "$(sed -n 1,3p "$OUT/node.out")" "process 0: 42; holds [#1, #0]
process 1: [41]; holds [#1, #0]
entries: 6 given, 6 acted on"
wantNode "$(sed -n 1,2p "$OUT/node.out")" "$("$OUT/chan" "$EXAMPLES/ping.hom" | sed -n 2,3p)"
WHOLE="$STATE"
wantNode "${#WHOLE}" "64"
# Stop after three ops with both processes waiting, then give the whole log to
# the kept node in a new process: it applies the three ops it has not seen.
node start "$EXAMPLES/ping.hom" "$EXAMPLES/ping-part.log"
wantNode "$(sed -n 1,3p "$OUT/node.out")" "process 0: waiting on [1, #0, #1]; holds [#1, #0]
process 1: waiting on [2, #0]; holds [#0]
entries: 3 given, 3 acted on"
node from "$STATE" "$EXAMPLES/ping.log"
wantNode "$(sed -n 3p "$OUT/node.out")" "entries: 6 given, 3 acted on"
wantNode "$STATE" "$WHOLE"
# Lose every kept node and apply the log again: the node has the same name.
rm -rf "$NODESTORE"
mkdir -p "$NODESTORE"
node start "$EXAMPLES/ping.hom" "$EXAMPLES/ping.log"
wantNode "$STATE" "$WHOLE"
# Ops delivered again change nothing.
node start "$EXAMPLES/ping.hom" "$EXAMPLES/ping-again.log"
wantNode "$(sed -n 3p "$OUT/node.out")" "entries: 10 given, 6 acted on"
wantNode "$STATE" "$WHOLE"
# The finished node given the log again: nothing is applied or written.
node from "$WHOLE" "$EXAMPLES/ping-again.log"
wantNode "$(sed -n 3p "$OUT/node.out")" "entries: 10 given, 0 acted on"
wantNode "$STATE" "$WHOLE"
wantNode "$(sed -n 's/^store: fetched [0-9]*, wrote //p' "$OUT/node.out")" "0"
# The other schedule of the race, as a log: process 2 gets the message.
printf '[[10, [0, 0, 5]], [11, [1, 0]], [12, [1, 0]], [13, [2, 0, 2]]]\n' > "$OUT/race.log"
node start "$EXAMPLES/race.hom" "$OUT/race.log"
wantNode "$(sed -n 1,3p "$OUT/node.out")" "$("$OUT/chan" "$EXAMPLES/race.hom" "$EXAMPLES/race.schedule" | sed -n 2,4p)"
# An op whose event cannot happen: the node is kept as it stood before it, and
# the ops after it are not applied.
printf '[[1, [0, 0, 0]], [2, [1, 0]], [3, [2, 0, 1]], [4, [0, 0, 1]]]\n' > "$OUT/guess.log"
node start "$EXAMPLES/guess.hom" "$OUT/guess.log"
wantNode "$(sed -n 3,4p "$OUT/node.out")" "entries: 4 given, 2 acted on
refused: entry 2, [2, 0, 1], cannot happen"
REFUSED="$STATE"
# The place in a refusal counts every delivery before it, repeats too.
printf '[[1, [0, 0, 0]], [1, [0, 0, 0]], [2, [1, 0]], [1, [0, 0, 0]], [3, [2, 0, 1]]]\n' > "$OUT/guess-again.log"
node start "$EXAMPLES/guess.hom" "$OUT/guess-again.log"
wantNode "$(sed -n 3,4p "$OUT/node.out")" "entries: 5 given, 2 acted on
refused: entry 4, [2, 0, 1], cannot happen"
wantNode "$STATE" "$REFUSED"
printf '[[1, [0, 0, 0]], [2, [1, 0]]]\n' > "$OUT/guess-two.log"
node start "$EXAMPLES/guess.hom" "$OUT/guess-two.log"
wantNode "$STATE" "$REFUSED"
wantNode "$(sed -n 1,2p "$OUT/node.out")" "process 0: waiting on [1, #0, 7]; holds [#0]
process 1: waiting on [2, #0]; holds []"
# The same log on number.hom: the meeting is refused there too, and the second
# process is waiting on the outside.
node start "$EXAMPLES/number.hom" "$OUT/guess.log"
wantNode "$(sed -n 1,4p "$OUT/node.out")" "process 0: waiting on [1, #0, 7]; holds [#0]
process 1: waiting on [2, 0]; holds []
entries: 4 given, 2 acted on
refused: entry 2, [2, 0, 1], cannot happen"
# A logged node and a name. The log makes two channels, starts a second process
# on the first, hands it the second name in a message, and then hands it both
# names again. It holds each once. An op delivered a second time changes
# nothing; the node saved part way and given the whole log reaches the same
# root; and the saved pieces hold the name value under tag 39 (d8 27 01).
HANDSTORE="$OUT/handoff-store"
rm -rf "$HANDSTORE"
mkdir -p "$HANDSTORE"
printf 'let child = quote (fn meet ->\n  ask [2, meet] (fn a ->\n    ask [2, meet] (fn b ->\n      ask [1, a, 5] (fn sent -> [a, b]))))\nask [0] (fn meet ->\n  ask [3, child, meet] (fn started ->\n    ask [0] (fn line ->\n      ask [1, meet, line] (fn first ->\n        ask [1, meet, [line, meet]] (fn second ->\n          ask [2, line] (fn reply -> reply))))))\n' > "$OUT/handoff.hom"
printf '[[1, [0, 0, 0]], [2, [1, 0]], [3, [0, 0, 1]], [4, [2, 0, 1]], [5, [2, 0, 1]], [6, [2, 1, 0]]]\n' > "$OUT/handoff.log"
printf '[[1, [0, 0, 0]], [2, [1, 0]], [3, [0, 0, 1]], [4, [2, 0, 1]]]\n' > "$OUT/handoff-part.log"
printf '[[1, [0, 0, 0]], [2, [1, 0]], [3, [0, 0, 1]], [4, [2, 0, 1]], [4, [2, 0, 1]], [5, [2, 0, 1]], [3, [0, 0, 1]], [6, [2, 1, 0]], [5, [2, 0, 1]]]\n' > "$OUT/handoff-again.log"
"$OUT/node" "$HANDSTORE" start "$OUT/handoff.hom" "$OUT/handoff.log" > "$OUT/handoff.out"
wantNode "$(sed -n 1,3p "$OUT/handoff.out")" "process 0: 5; holds [#1, #0]
process 1: [#1, [#1, #0]]; holds [#1, #0]
entries: 6 given, 6 acted on"
wantNode "$(sed -n 1,2p "$OUT/handoff.out")" "$("$OUT/chan" "$OUT/handoff.hom" | sed -n 2,3p)"
HANDED="$(sed -n 's/^state: //p' "$OUT/handoff.out")"
wantNode "${#HANDED}" "64"
"$OUT/node" "$HANDSTORE" start "$OUT/handoff.hom" "$OUT/handoff-again.log" > "$OUT/handoff.out"
wantNode "$(sed -n 3p "$OUT/handoff.out")" "entries: 9 given, 6 acted on"
wantNode "$(sed -n 's/^state: //p' "$OUT/handoff.out")" "$HANDED"
rm -rf "$HANDSTORE"
mkdir -p "$HANDSTORE"
"$OUT/node" "$HANDSTORE" start "$OUT/handoff.hom" "$OUT/handoff-part.log" > "$OUT/handoff.out"
wantNode "$(sed -n 1,3p "$OUT/handoff.out")" "process 0: waiting on [1, #0, [#1, #0]]; holds [#1, #0]
process 1: waiting on [2, #0]; holds [#1, #0]
entries: 4 given, 4 acted on"
PARTWAY="$(sed -n 's/^state: //p' "$OUT/handoff.out")"
if ! cat "$HANDSTORE"/* | od -An -v -tx1 | tr -d ' \n' | grep -q 'd82701'; then
    echo "node: no saved piece of the handoff holds the name #1 under tag 39" >&2
    exit 1
fi
"$OUT/node" "$HANDSTORE" from "$PARTWAY" "$OUT/handoff-again.log" > "$OUT/handoff.out"
wantNode "$(sed -n 1,3p "$OUT/handoff.out")" "process 0: 5; holds [#1, #0]
process 1: [#1, [#1, #0]]; holds [#1, #0]
entries: 9 given, 2 acted on"
wantNode "$(sed -n 's/^state: //p' "$OUT/handoff.out")" "$HANDED"
echo "node: a name handed over twice is held once, and the logged node restarts to the same root"
# The kernel's text for a bad log, a bad root, a root that is another kind of
# state, and a run that does not end.
wantNode "$("$OUT/node" "$NODESTORE" start "$EXAMPLES/ping.hom" "$EXAMPLES/ask.log")" "log: entry 0 is not a mark and an event"
wantNode "$("$OUT/node" "$NODESTORE" start "$EXAMPLES/ping.hom" "$EXAMPLES/factorial.hom")" "log: not an array"
wantNode "$("$OUT/node" "$NODESTORE" from nothex "$EXAMPLES/ping.log")" "store error: a root is 64 hex digits"
wantNode "$("$OUT/node" "$NODESTORE" start "$EXAMPLES/forever.hom" "$EXAMPLES/ping.log" 5000 | sed -n 1p)" "no result within 5000 steps of a turn"
"$OUT/vm" "$NODESTORE" start "$EXAMPLES/ask.hom" "$EXAMPLES/ask.log" > "$OUT/vm.txt"
VMSTATE="$(sed -n 's/^state: //p' "$OUT/vm.txt")"
wantNode "$("$OUT/node" "$NODESTORE" from "$VMSTATE" "$EXAMPLES/ping.log" | sed -n 1p)" "store error: the root is not a kept node"
wantNode "$("$OUT/vm" "$NODESTORE" from "$WHOLE" "$EXAMPLES/ask.log" | sed -n 1p)" "store error: the root is not a kept state"
# A node that is not in the store: exit 3, nothing printed, the piece named.
status=0
"$OUT/node" "$NODESTORE" from "$(printf '%064d' 0)" "$EXAMPLES/ping.log" > "$OUT/refuse.out" 2> "$OUT/refuse.err" || status=$?
printf 'node: the store lacks piece %064d\n' 0 > "$OUT/refuse.expected"
if [ "$status" != 3 ] || [ -s "$OUT/refuse.out" ] || ! cmp -s "$OUT/refuse.expected" "$OUT/refuse.err"; then
    echo "node with the root missing: expected exit 3 and no output; got exit $status" >&2
    exit 1
fi
refuseNode() {
    status=0
    "$OUT/node" "$@" > "$OUT/refuse.out" 2> "$OUT/refuse.err" || status=$?
    if [ "$status" != 2 ] || [ -s "$OUT/refuse.out" ] || ! [ -s "$OUT/refuse.err" ]; then
        echo "node $*: expected exit 2, no output and a message; got exit $status" >&2
        exit 1
    fi
    echo "node refused: $(sed -n 1p "$OUT/refuse.err")"
}
refuseNode
refuseNode "$NODESTORE" start "$EXAMPLES/ping.hom"
refuseNode "$NODESTORE" resume "$EXAMPLES/ping.hom" "$EXAMPLES/ping.log"
refuseNode "$NODESTORE" start "$EXAMPLES/missing.hom" "$EXAMPLES/ping.log"
refuseNode "$NODESTORE" start "$EXAMPLES/ping.hom" "$EXAMPLES/missing.log"
refuseNode "$OUT/no-such-store" start "$EXAMPLES/ping.hom" "$EXAMPLES/ping.log"
refuseNode "$NODESTORE" start "$EXAMPLES/ping.hom" "$EXAMPLES/ping.log" many
echo "node command checks passed"
