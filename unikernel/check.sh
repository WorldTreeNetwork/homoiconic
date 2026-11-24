#!/bin/sh
# Build the image from nothing and boot it under Cloud Hypervisor, once for
# each case, comparing everything the serial port says. Needs what build.sh
# needs, plus KVM, nm and timeout.
#   CLOUD_HYPERVISOR=/path/to/cloud-hypervisor sh unikernel/check.sh
set -eu
HERE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
EXAMPLES="$HERE/../examples"
CH="${CLOUD_HYPERVISOR:-cloud-hypervisor}"
OUT="$HERE/out"
export OUT
LIMIT="${LIMIT:-60}"

[ -r /dev/kvm ] && [ -w /dev/kvm ] || { echo "check: /dev/kvm is not usable here" >&2; exit 2; }
"$CH" --version > /dev/null 2>&1 || { echo "check: cannot run $CH" >&2; exit 2; }
version="$("$CH" --version | head -n 1)"
[ "$version" = "cloud-hypervisor v54.0" ] || { echo "check: Cloud Hypervisor 54.0 is needed (got $version)" >&2; exit 2; }
echo "with $version"

fail() {
    echo "FAIL $1" >&2
    [ -r "$OUT/serial.log" ] && sed 's/^/  serial: /' "$OUT/serial.log" | head -n 20 >&2
    exit 1
}

# image <case> [NAME=value ...] <program-file> [step-budget]: build it.
image() {
    name="$1"
    shift
    rm -f "$OUT/reflect.elf" "$OUT/reflect-linux"
    (
        while [ $# -gt 0 ]; do
            case "$1" in *=*) export "$1"; shift ;; *) break ;; esac
        done
        sh "$HERE/build.sh" "$@"
    ) > "$OUT/build.log" 2>&1 || { cat "$OUT/build.log" >&2; fail "$name: build"; }
}

# boot <case>: Cloud Hypervisor must exit 0 inside the limit. It does that only
# when the guest powers off; a guest that resets or hangs runs into the limit.
boot() {
    rm -f "$OUT/serial.log"
    status=0
    timeout "$LIMIT" "$CH" --kernel "$OUT/reflect.elf" --cpus boot=1 --memory size=512M \
        --serial file="$OUT/serial.log" --console off > "$OUT/cloud-hypervisor.log" 2>&1 || status=$?
    [ "$status" = 124 ] && fail "$1: no power off within $LIMIT seconds"
    [ "$status" = 0 ] || { cat "$OUT/cloud-hypervisor.log" >&2; fail "$1: cloud-hypervisor exit $status"; }
    [ -r "$OUT/serial.log" ] || fail "$1: the serial port said nothing"
}

# A line the layer writes when the image lacks something or stops early.
# No passing run of a program has one.
trouble() {
    grep -q "is not provided\|processor fault\|^reflect: aborted\|^reflect: this processor\|^reflect: the processor\|^reflect: the kernel\|^reflect: out of memory" "$OUT/serial.log"
}

# same <case> [expected-file]: the serial port says what the same program says
# as a Linux process, then `reflect: exit 0`; and what the file says, if given.
same() {
    if trouble; then fail "$1: the image lacked something"; fi
    "$OUT/reflect-linux" > "$OUT/linux.txt" || fail "$1: the Linux process failed"
    [ -s "$OUT/linux.txt" ] || fail "$1: the Linux process said nothing"
    { cat "$OUT/linux.txt"; echo "reflect: exit 0"; } > "$OUT/wanted.txt"
    cmp "$OUT/wanted.txt" "$OUT/serial.log" || fail "$1: the image and the Linux process differ"
    if [ $# -gt 1 ]; then cmp "$2" "$OUT/serial.log" || fail "$1: the serial port differs from $2"; fi
    echo "ok   $1"
}

# given <bytes-file> <command-line>: boot the image as it is, with a file handed
# to it at boot, through the documented launch (given.sh). The command line is
# `[step-budget [levels]]`, split into words as the launch takes them.
given() {
    rm -f "$OUT/serial.log"
    GIVEN_BYTES="$1"
    GIVEN_WORDS="$2"
    status=0
    # shellcheck disable=SC2086
    CLOUD_HYPERVISOR="$CH" IMAGE="$OUT/reflect.elf" SERIAL="file=$OUT/serial.log" \
        timeout "$LIMIT" sh "$HERE/given.sh" "$1" $2 > "$OUT/cloud-hypervisor.log" 2>&1 || status=$?
    [ "$status" = 124 ] && fail "given $1: no power off within $LIMIT seconds"
    [ "$status" = 0 ] || { cat "$OUT/cloud-hypervisor.log" >&2; fail "given $1: cloud-hypervisor exit $status"; }
    [ -r "$OUT/serial.log" ] || fail "given $1: the serial port said nothing"
}

# given_raw <bytes-file> <command-line>: the same, with Cloud Hypervisor started
# directly, so the image's own refusals can be seen past the launch's.
given_raw() {
    rm -f "$OUT/serial.log"
    status=0
    timeout "$LIMIT" "$CH" --kernel "$OUT/reflect.elf" --initramfs "$1" ${2:+--cmdline "$2"} --cpus boot=1 --memory size=512M \
        --serial file="$OUT/serial.log" --console off > "$OUT/cloud-hypervisor.log" 2>&1 || status=$?
    [ "$status" = 124 ] && fail "given $1: no power off within $LIMIT seconds"
    [ "$status" = 0 ] || { cat "$OUT/cloud-hypervisor.log" >&2; fail "given $1: cloud-hypervisor exit $status"; }
    [ -r "$OUT/serial.log" ] || fail "given $1: the serial port said nothing"
}

# launch_refuses <case> <bytes-file>: the launch refuses the file with its line
# and status 2, and Cloud Hypervisor is not started.
launch_refuses() {
    rm -f "$OUT/serial.log"
    status=0
    CLOUD_HYPERVISOR="$CH" IMAGE="$OUT/reflect.elf" SERIAL="file=$OUT/serial.log" \
        sh "$HERE/given.sh" "$2" > "$OUT/launch.log" 2>&1 || status=$?
    [ "$status" = 2 ] || fail "$1: the launch ended with $status"
    printf 'given: the program given at boot is larger than 16 MiB\n' > "$OUT/wanted.txt"
    cmp "$OUT/wanted.txt" "$OUT/launch.log" || fail "$1: the launch said something else"
    [ ! -e "$OUT/serial.log" ] || fail "$1: the image was started"
    echo "ok   $1"
}

# says <case> <line>...: the serial port says exactly these lines and then
# `reflect: exit 0`.
says() {
    name="$1"
    shift
    { printf '%s\n' "$@"; echo "reflect: exit 0"; } > "$OUT/wanted.txt"
    cmp "$OUT/wanted.txt" "$OUT/serial.log" || fail "$name: expected '$*'"
}

# same_given <case> [expected-file]: the serial port says what the Linux process
# says for the same file and words, then `reflect: exit 0`.
same_given() {
    if trouble; then fail "$1: the image lacked something"; fi
    # shellcheck disable=SC2086
    "$OUT/reflect-linux" "$GIVEN_BYTES" $GIVEN_WORDS > "$OUT/linux.txt" || fail "$1: the Linux process failed"
    [ -s "$OUT/linux.txt" ] || fail "$1: the Linux process said nothing"
    { cat "$OUT/linux.txt"; echo "reflect: exit 0"; } > "$OUT/wanted.txt"
    cmp "$OUT/wanted.txt" "$OUT/serial.log" || fail "$1: the image and the Linux process differ"
    if [ $# -gt 1 ]; then cmp "$2" "$OUT/serial.log" || fail "$1: the serial port differs from $2"; fi
    echo "ok   $1"
}

# refused_given <case> <line>: the program refuses its words with this line and
# status 2, in the image and as a Linux process.
refused_given() {
    status=0
    # shellcheck disable=SC2086
    "$OUT/reflect-linux" "$GIVEN_BYTES" $GIVEN_WORDS > "$OUT/linux.txt" || status=$?
    [ "$status" = 2 ] || fail "$1: the Linux process ended with $status"
    { cat "$OUT/linux.txt"; echo "reflect: exit 2"; } > "$OUT/wanted.txt"
    cmp "$OUT/wanted.txt" "$OUT/serial.log" || fail "$1: the image and the Linux process differ"
    grep -qx "$2" "$OUT/serial.log" || fail "$1: expected '$2'"
    echo "ok   $1"
}

# only <case> <text>: the serial port says exactly this line and nothing else.
only() {
    printf '%s\n' "$2" > "$OUT/wanted.txt"
    cmp "$OUT/wanted.txt" "$OUT/serial.log" || fail "$1: expected only '$2'"
    echo "ok   $1"
}

rm -rf "$OUT"
mkdir -p "$OUT"

# ---- programs ----
image factorial "$EXAMPLES/factorial.hom"; boot factorial; same factorial "$HERE/expected/factorial.txt"
image forever "$EXAMPLES/forever.hom" 5000; boot forever; same forever "$HERE/expected/forever.txt"
image not-syntax "$HERE/expected/not-syntax.hom"; boot not-syntax; same not-syntax "$HERE/expected/not-syntax.txt"
# Text is its own kind of data: quoted, escaped, UTF-8 on the serial port, and the
# two text operations. (A name cannot reach this image: reflect_run answers no request.)
image text "$HERE/expected/text.hom"; boot text; same text "$HERE/expected/text.txt"

# A source with a zero byte in it: the bytes are passed by address and length.
printf 'quote 1\0 2\n' > "$OUT/zero.hom"
image "zero byte" "$OUT/zero.hom"; boot "zero byte"; same "a zero byte in the source"

# An answer longer than the program's first buffer arrives whole: every byte is compared.
printf 'def fill n =\n  case n\n    0 -> []\n    m + 1 -> [n, ...fill m]\n\nfill 20000\n' > "$OUT/long.hom"
awk 'BEGIN { printf "["; for (i = 20000; i > 1; i--) printf "%d, ", i; printf "1]\nreflect: exit 0\n" }' > "$OUT/long.expected"
[ "$(wc -c < "$OUT/long.expected")" -gt 65536 ] || fail "long: the answer fits the first buffer"
image long "$OUT/long.hom"; boot long; same "an answer of $(wc -c < "$OUT/long.expected" | tr -d ' ') bytes" "$OUT/long.expected"

# The clock does not reach a result: with the clock stopped the answer is the same.
image clock PRETEND=clock_stuck "$EXAMPLES/factorial.hom"; boot clock; same "the clock stopped" "$HERE/expected/factorial.txt"

# ---- what the image holds ----
image factorial "$EXAMPLES/factorial.hom"
# The event loop's start is the program's empty one.
real="$(nm "$OUT/reflect.elf" | awk '$3 == "initialize_libuv" { print $1 }')"
mine="$(nm "$OUT/reflect.elf" | awk '$3 == "main.initialize_libuv" { print $1 }')"
[ -n "$real" ] && [ "$real" = "$mine" ] || fail "initialize_libuv is not the program's empty one"
echo "ok   the event loop's start is the empty one"
# The layer names nothing in the kernel, and the program names five things in
# it: the initializers, the two runs, and the kernel's bound on levels.
if nm -u "$OUT/kernel.o" | awk '{ print $2 }' | grep -q "^reflect_\|^circularKernel\|^lean_\|^l_"; then fail "the layer refers to the kernel"; fi
uses="$(nm -u "$OUT/main.o" | awk '{ print $2 }' | grep "^reflect_\|circularKernel\|^kernel_\|^lean_\|^l_" | sort | tr '\n' ' ')"
[ "$uses" = "initialize_circularKernel_Surface_Host kernel_finish_initialization reflect_interp reflect_max_levels reflect_run " ] ||
    fail "the program refers to: $uses"
echo "ok   the program calls reflect_run and reflect_interp and nothing else that evaluates or reads"
(cd "$OUT" && sha256sum --quiet -c objects.sha256) || fail "the objects are not the ones compiled at the start"
echo "ok   the Lean objects are the ones Lake's C compiled to"

# ---- a program given at boot ----
# One image, built once above from factorial, runs each byte form it is handed
# at boot through the interpreter. It is not built again inside this section:
# the file's hash is taken here and compared at the end.
before="$(sha256sum < "$OUT/reflect.elf")"
bytes() { "$OUT/reply" source "$1" > "$2" || fail "$3: no byte form"; [ -s "$2" ] || fail "$3: an empty byte form"; }
bytes "$HERE/expected/text.hom" "$OUT/text.bytes" text
bytes "$EXAMPLES/factorial.hom" "$OUT/factorial.bytes" factorial
bytes "$EXAMPLES/forever.hom" "$OUT/forever.bytes" forever
bytes "$EXAMPLES/quine.hom" "$OUT/quine.bytes" quine
# The built-in program is factorial, so a text answer can only come from the bytes.
given "$OUT/text.bytes" ""; same_given "bytes at boot: text, through one interpreter" "$HERE/expected/text.txt"
given "$OUT/factorial.bytes" ""; same_given "bytes at boot: factorial, through one interpreter" "$HERE/expected/factorial.txt"
given "$OUT/factorial.bytes" "100000000 0"; same_given "bytes at boot: factorial, through none" "$HERE/expected/factorial.txt"
given "$OUT/factorial.bytes" "1000000000 2"; same_given "bytes at boot: factorial, through two interpreters" "$HERE/expected/factorial.txt"
given "$OUT/quine.bytes" ""; same_given "bytes at boot: the quine"
# The budget on the command line is the one that counts.
given "$OUT/forever.bytes" "5000"; same_given "bytes at boot: a budget of 5000 steps" "$HERE/expected/forever.txt"
# The levels on the command line are the ones that count: 10000 steps are
# enough for factorial itself and not through one interpreter, and 100000 are
# enough through one and not through two.
given "$OUT/factorial.bytes" "10000 0"; same_given "bytes at boot: 10000 steps are enough through none" "$HERE/expected/factorial.txt"
given "$OUT/factorial.bytes" "10000 1"; same_given "bytes at boot: 10000 steps are not enough through one"
says "10000 steps through one" "no result within 10000 steps"
given "$OUT/factorial.bytes" "100000 1"; same_given "bytes at boot: 100000 steps are enough through one" "$HERE/expected/factorial.txt"
given "$OUT/factorial.bytes" "100000 2"; same_given "bytes at boot: 100000 steps are not enough through two"
says "100000 steps through two" "no result within 100000 steps"
# The most levels there are is 8: the tower is built, and the budget stops it.
given "$OUT/factorial.bytes" "1000 8"; same_given "bytes at boot: eight interpreters"
says "eight interpreters" "no result within 1000 steps"
# The largest budget there is.
given "$OUT/factorial.bytes" "18446744073709551615 0"; same_given "bytes at boot: the largest budget" "$HERE/expected/factorial.txt"
# Bytes that are no program are the kernel's to refuse, in the kernel's words,
# and a megabyte of them arrives whole.
head -c 1048576 /dev/zero | tr '\0' '\377' > "$OUT/not-a-program.bytes"
given "$OUT/not-a-program.bytes" ""; same_given "bytes at boot: a megabyte that is no program"
says "a megabyte that is no program" "bytes error: an indefinite length or a reserved form"
{ cat "$OUT/factorial.bytes"; printf '\0'; } > "$OUT/one-more.bytes"
given "$OUT/one-more.bytes" ""; same_given "bytes at boot: one byte past a program"
says "one byte past a program" "bytes error: there are bytes after the value"
# 16 MiB is the most the layer takes, and all of it arrives.
head -c 16777216 /dev/zero > "$OUT/limit.bytes"
given "$OUT/limit.bytes" ""; same_given "bytes at boot: exactly 16 MiB"
says "exactly 16 MiB" "bytes error: there are bytes after the value"
# 16 MiB of arrays opened and never closed is refused as bytes cut short,
# before the kernel makes anything of them.
head -c 16777216 /dev/zero | tr '\0' '\201' > "$OUT/open-arrays.bytes"
given "$OUT/open-arrays.bytes" ""; same_given "bytes at boot: 16 MiB of arrays never closed"
says "16 MiB of arrays never closed" "bytes error: the bytes end inside a value"
# Words that are not numbers, or numbers past the limits, are refused by the
# program as the Linux process refuses them, each with its own line.
given "$OUT/factorial.bytes" "many"; refused_given "bytes at boot: a budget that is not a number" "reflect: the step budget must be a whole number"
given "$OUT/factorial.bytes" "18446744073709551616"; refused_given "bytes at boot: a budget of 2^64" "reflect: the step budget must be below 18446744073709551616"
given "$OUT/factorial.bytes" "1000 x"; refused_given "bytes at boot: levels that are not a number" "reflect: the levels must be a whole number"
given "$OUT/factorial.bytes" "1000 9"; refused_given "bytes at boot: nine levels" "reflect: the levels must be at most 8"
given "$OUT/factorial.bytes" "1000 4294967296"; refused_given "bytes at boot: 2^32 levels" "reflect: the levels must be at most 8"
# A command line is kept whole up to 1023 bytes, and one longer is refused, not cut.
words="$(awk 'BEGIN { for (i = 0; i < 1019; i++) printf "0"; printf "5000" }')"
[ "${#words}" = 1023 ] || fail "the long command line is not 1023 bytes"
given "$OUT/forever.bytes" "$words"; same_given "bytes at boot: a command line of 1023 bytes" "$HERE/expected/forever.txt"
words="$(awk 'BEGIN { for (i = 0; i < 1100; i++) printf "0"; printf "x" }')"
given "$OUT/factorial.bytes" "$words"
only "bytes at boot: a command line of 1101 bytes is refused" "reflect: the command line is longer than 1023 bytes"
# More than the layer keeps room for is refused by the launch before the
# hypervisor starts, and by the image when the hypervisor is started without it.
head -c 16777217 /dev/zero > "$OUT/too-large.bytes"
launch_refuses "bytes at boot: the launch refuses more than 16 MiB" "$OUT/too-large.bytes"
given_raw "$OUT/too-large.bytes" ""
only "bytes at boot: the image refuses more than 16 MiB" "reflect: the program given at boot is too large"
# A file just under the first memory region: Cloud Hypervisor would put it on
# top of the image. The launch refuses it; started directly, the image never
# gets to say anything (Cloud Hypervisor 54.0 reports an internal error from
# the processor and still exits 0).
rm -f "$OUT/huge.bytes"
truncate -s $((512 * 1048576 - 4096)) "$OUT/huge.bytes"
launch_refuses "bytes at boot: the launch refuses a file that would land on the image" "$OUT/huge.bytes"
given_raw "$OUT/huge.bytes" ""
[ ! -s "$OUT/serial.log" ] || fail "huge: the image spoke with a file on top of it"
grep -q "InternalError" "$OUT/cloud-hypervisor.log" || fail "huge: Cloud Hypervisor did not report the processor's internal error"
echo "ok   started directly, a file that lands on the image silences it"
rm -f "$OUT/huge.bytes"
[ "$before" = "$(sha256sum < "$OUT/reflect.elf")" ] || fail "the image changed between the programs given at boot"
echo "ok   one image ran every program given at boot"
# With nothing given, the same image still runs the program built into it.
boot factorial; same "the same image with nothing given at boot" "$HERE/expected/factorial.txt"

# Cloud Hypervisor hands over one file at most; two files, and a list of files
# outside memory, are what an image told to see them refuses.
image "two files" PRETEND=two_modules "$EXAMPLES/factorial.hom"
given "$OUT/factorial.bytes" ""
only "bytes at boot: two files are refused" "reflect: more than one file was given at boot"
image "file list outside memory" PRETEND=module_list_outside "$EXAMPLES/factorial.hom"
given "$OUT/factorial.bytes" ""
only "bytes at boot: a list of files outside memory is refused" "reflect: the list of files given at boot is not in usable memory"

# ---- the rules above have to trip ----
# An image whose layer does not answer a call the C library makes at its start says so.
image "omitted call" OMIT_CALL=218 "$EXAMPLES/factorial.hom"; boot "omitted call"
trouble || fail "omitted call: nothing was reported"
grep -q "^reflect: system call 218 is not provided$" "$OUT/serial.log" || fail "omitted call: the line does not name the call"
echo "ok   an unanswered system call is reported"

# ---- the stack ----
# A source nested deeper than the stack holds ends in a report, and the machine powers off.
awk 'BEGIN { for (i = 0; i < 300000; i++) printf "("; printf "1"; for (i = 0; i < 300000; i++) printf ")"; print "" }' > "$OUT/deep.hom"
image deep "$OUT/deep.hom"; boot deep
grep -q "^reflect: processor fault 14 .* (on the fault stack): the stack is full" "$OUT/serial.log" || fail "deep: no report of a full stack"
if grep -q "reflect: exit" "$OUT/serial.log"; then fail "deep: the program went on after the fault"; fi
echo "ok   a source nested too deep ends in a report of a full stack"

# One write into the unmapped page: a page fault at that address, taken on the
# fault stack, with the word under the page still what the probe put there.
image guard PROBE=guard "$EXAMPLES/factorial.hom"; boot guard
touched="$(sed -n 's/^probe: touching \(0x[0-9a-f]*\)$/\1/p' "$OUT/serial.log")"
[ -n "$touched" ] || fail "guard: the probe did not say what it touched"
grep -q "^reflect: processor fault 14 code 0x0000000000000002 at 0x[0-9a-f]* address $touched stack 0x[0-9a-f]* (on the fault stack): the stack is full; below the guard: 0x5eed5eed5eed5eed$" "$OUT/serial.log" ||
    fail "guard: not a page fault at $touched on the fault stack with the word below intact"
if grep -q "did not stop\|reflect: exit" "$OUT/serial.log"; then fail "guard: the write went through"; fi
echo "ok   a write into the page under the stack faults, and the memory under it is untouched"

# ---- system calls ----
image preserve PROBE=preserve "$EXAMPLES/factorial.hom"; boot preserve
printf 'probe: a system call gave back the caller'"'"'s state\nreflect: exit 0\n' > "$OUT/wanted.txt"
cmp "$OUT/wanted.txt" "$OUT/serial.log" || fail "preserve: state was lost across a system call"
echo "ok   a system call gives back registers, flags, the red zone and the vector state"

# ---- the processor floor and random bytes ----
image random PROBE=random "$EXAMPLES/factorial.hom"; boot random
printf 'probe: random bytes were served\nreflect: exit 0\n' > "$OUT/wanted.txt"
cmp "$OUT/wanted.txt" "$OUT/serial.log" || fail "random: bytes were not served"
echo "ok   random bytes are served"
image "no saved state" PRETEND=no_saved_state "$EXAMPLES/factorial.hom"; boot "no saved state"
only "a processor without XSAVE is refused" "reflect: this processor has no XSAVE"
image "no random" PRETEND=no_random "$EXAMPLES/factorial.hom"; boot "no random"
only "a processor without a random instruction is refused" "reflect: this processor has no random instruction"
image "random fails" PRETEND=random_fails_at_boot "$EXAMPLES/factorial.hom"; boot "random fails"
only "a random instruction that fails at the start stops the image" "reflect: the processor gave no random bytes"
image "random fails later" PRETEND=random_fails_when_served "$EXAMPLES/factorial.hom"; boot "random fails later"
only "a random instruction that fails under the program stops the image" "reflect: the processor gave no random bytes"
image "random fails later" PRETEND=random_fails_when_served PROBE=random "$EXAMPLES/factorial.hom"; boot "random fails later"
only "a random instruction that fails under a request stops the image" "reflect: the processor gave no random bytes"

# ---- the time limit ----
# A guest that never powers off is a failure: the image that waits for random
# bytes forever is not buildable, so the limit itself is tried on a sleep.
status=0
timeout 1 sleep 5 || status=$?
[ "$status" = 124 ] || fail "timeout(1) did not stop a long command"
echo "ok   a command that runs past the limit is stopped"
echo "unikernel checks passed"
