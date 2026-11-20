#!/bin/sh
# Build the image: unikernel/out/reflect.elf, one file Cloud Hypervisor boots,
# and unikernel/out/reflect-linux, the same program as a Linux process.
# The program file is the one the image runs when it is given none at boot.
# Given a byte form at boot (--initramfs <bytes> --cmdline "[budget [levels]]")
# the same image runs that instead; unikernel/out/reply source <file> writes one.
#   sh unikernel/build.sh <program-file> [step-budget]
# Needs Linux x86_64, elan, Zig 0.16.0, and objcopy and sha256sum.
# The check also sets:
#   PROBE=preserve|guard|random   link a probe in place of the program
#   OMIT_CALL=<number>            leave one system call unanswered
#   PRETEND=<name>                see `pretend` in kernel.zig
set -eu
export PATH="$HOME/.elan/bin:$PATH"
HERE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
KERNEL="$(CDPATH= cd -- "$HERE/../kernel" && pwd)"
OUT="${OUT:-$HERE/out}"
if [ $# -lt 1 ] || [ $# -gt 2 ]; then
    echo "usage: build.sh <program-file> [step-budget]   (default budget: 100000000 machine steps)" >&2
    exit 2
fi
PROGRAM="$1"
BUDGET="${2:-100000000}"
case "$BUDGET" in '' | *[!0-9]*) echo "build: the step budget must be a whole number" >&2; exit 2 ;; esac
[ -r "$PROGRAM" ] || { echo "build: cannot read the program file" >&2; exit 2; }
[ "$(uname -s) $(uname -m)" = "Linux x86_64" ] || { echo "build: the image is built on Linux x86_64" >&2; exit 2; }
[ "$(zig version)" = "0.16.0" ] || { echo "build: Zig 0.16.0 is needed" >&2; exit 2; }
Z="--cache-dir $OUT/zig-cache --global-cache-dir $OUT/zig-global-cache"
mkdir -p "$OUT"
OUT="$(CDPATH= cd -- "$OUT" && pwd)"
Z="--cache-dir $OUT/zig-cache --global-cache-dir $OUT/zig-global-cache"
mkdir -p "$OUT/lib" "$OUT/gen" "$OUT/lean"
rm -f "$OUT/reflect.elf" "$OUT/reflect-linux"
source_stamp() {
    (
        cd "$KERNEL"
        # Source changes invalidate generated objects, including newly imported modules.
        find . -path './.lake' -prune -o -type f \( -name '*.lean' -o -name '*.c' -o -name 'lean-toolchain' -o -name 'lake-manifest.json' \) -print |
            LC_ALL=C sort | while IFS= read -r file; do sha256sum "$file"; done
        sha256sum ../host/runtime.c
        uname -sm
        zig version
        lake env lean --version
        lake env lean --print-prefix
    )
}
source_stamp > "$OUT/source.current"
if [ -r "$OUT/lean/done" ]; then
    cmp -s "$OUT/source.current" "$OUT/source.sha256" || {
        echo "build: source or toolchain changed; remove $OUT and rebuild" >&2; exit 2;
    }
fi

# 1. The kernel's Lean objects, compiled here from the C that Lake generates,
#    for the modules Surface.Host imports and no others. The toolchain is the
#    one kernel/lean-toolchain pins.
if [ ! -r "$OUT/lean/done" ]; then
    (
        cd "$KERNEL"
        lake build
        L="$(lake env lean --print-prefix)"
        lake env lean --version > "$OUT/versions.txt"
        todo="Surface/Host"
        seen=" "
        while [ -n "$todo" ]; do
            module="${todo%% *}"
            rest="${todo#"$module"}"
            todo="${rest# }"
            case "$seen" in *" $module "*) continue ;; esac
            seen="$seen$module "
            for dep in $(lake env lean --deps "$module.lean" | sed -n "s|^$KERNEL/.lake/build/lib/lean/\(.*\)\.olean$|\1|p"); do
                todo="$todo $dep"
                todo="${todo# }"
            done
        done
        for module in $seen; do
            name="$(echo "$module" | tr / -)"
            lake env leanc -c -O3 -o "$OUT/lean/lean-$name.o" ".lake/build/ir/$module.c"
        done
        lake env leanc -c -o "$OUT/lean/ffi.o" ffi.c
        lake env leanc -c -o "$OUT/lean/runtime.o" "$HERE/../host/runtime.c"
        # 2. Copies of four toolchain archives, each with one edit.
        # The C++ archives list pthread, rt and dl as libraries to link; musl has them inside libc.
        for a in libc++.a libc++abi.a libunwind.a; do
            objcopy --remove-section=.deplibs "$L/lib/$a" "$OUT/lib/$a"
        done
        # A weak initialize_libuv lets the program's empty one be the one that is called.
        objcopy --weaken-symbol=initialize_libuv "$L/lib/lean/libleanrt.a" "$OUT/lib/libleanrt.a"
        cp "$L/lib/lean/libInit.a" "$L/lib/lean/libStd.a" "$L/lib/libgmp.a" "$L/lib/libuv.a" "$OUT/lib/"
        zig version >> "$OUT/versions.txt"
        (cd "$OUT" && sha256sum lean/*.o lib/*.a) > "$OUT/objects.sha256"
        cp "$OUT/source.current" "$OUT/source.sha256"
        touch "$OUT/lean/done"
    )
fi
# Every object must be the one that was compiled: an ELF x86-64 object with the recorded hash.
(cd "$OUT" && sha256sum --quiet -c objects.sha256) || { echo "build: an object in $OUT changed since it was compiled; remove $OUT" >&2; exit 2; }

# 3. The layer and the program.
cp "$PROGRAM" "$OUT/gen/program.hom"
printf 'pub const source = @embedFile("program.hom");\npub const budget: u64 = %s;\npub const probe: enum { preserve, guard, random } = .%s;\n' \
    "$BUDGET" "${PROBE:-preserve}" > "$OUT/gen/program.zig"
if [ -n "${PROBE:-}" ]; then IS_PROBE=true; TOP="$HERE/probe.zig"; EXTRA="$HERE/probe.S"; else IS_PROBE=false; TOP="$HERE/main.zig"; EXTRA=""; fi
printf 'pub const omit_call: ?u64 = %s;\npub const probe = %s;\npub const pretend: enum { nothing, no_saved_state, no_random, random_fails_at_boot, random_fails_when_served, clock_stuck } = .%s;\n' \
    "${OMIT_CALL:-null}" "$IS_PROBE" "${PRETEND:-nothing}" > "$OUT/gen/options.zig"

# shellcheck disable=SC2086
zig build-obj -target x86_64-freestanding-none -O ReleaseSmall -fno-PIE -fno-builtin \
    -fno-stack-check -fno-stack-protector --dep options "-Mroot=$HERE/kernel.zig" "-Moptions=$OUT/gen/options.zig" \
    -femit-bin="$OUT/kernel.o" $Z
# shellcheck disable=SC2086
zig build-obj -target x86_64-linux-musl -O ReleaseSafe -fno-PIE -lc \
    --dep program "-Mroot=$TOP" "-Mprogram=$OUT/gen/program.zig" \
    -femit-bin="$OUT/main.o" $Z

# 4. One link for the image, and one without the boot code and the layer.
LIBS="$OUT/lib/libInit.a $OUT/lib/libleanrt.a $OUT/lib/libStd.a $OUT/lib/libInit.a $OUT/lib/libleanrt.a \
    $OUT/lib/libgmp.a $OUT/lib/libuv.a $OUT/lib/libc++.a $OUT/lib/libc++abi.a $OUT/lib/libunwind.a"
# shellcheck disable=SC2086
zig build-exe -target x86_64-linux-musl -static -fno-PIE -femit-bin="$OUT/reflect.elf" \
    "$HERE/boot.S" "$OUT/kernel.o" "$OUT/main.o" $EXTRA "$HERE/glibc_names.c" \
    "$OUT"/lean/*.o $LIBS -lc --gc-sections $Z
if [ -z "${PROBE:-}" ]; then
    # shellcheck disable=SC2086
    zig build-exe -target x86_64-linux-musl -static -fno-PIE -femit-bin="$OUT/reflect-linux" \
        "$OUT/main.o" "$HERE/glibc_names.c" "$OUT"/lean/*.o $LIBS -lc --gc-sections $Z
    # The same objects once more, as the tool that writes a source's byte form
    # (`reply source <file>`): what a program given at boot is made with.
    # shellcheck disable=SC2086
    zig build-exe -target x86_64-linux-musl -static -fno-PIE -femit-bin="$OUT/reply" \
        "$HERE/reply.zig" "$HERE/glibc_names.c" "$OUT"/lean/*.o $LIBS -lc --gc-sections $Z
fi
echo "built $OUT/reflect.elf"
