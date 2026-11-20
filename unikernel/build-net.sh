#!/bin/sh
# The network image and the Linux process that calls the same reply export.
#   sh unikernel/build-net.sh
set -eu
export PATH="$HOME/.elan/bin:$PATH"
HERE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
KERNEL="$(CDPATH= cd -- "$HERE/../kernel" && pwd)"
OUT="${OUT:-$HERE/out-net}"
[ "$(uname -s) $(uname -m)" = "Linux x86_64" ] || { echo "build-net: the image is built on Linux x86_64" >&2; exit 2; }
[ "$(zig version)" = "0.16.0" ] || { echo "build-net: Zig 0.16.0 is needed" >&2; exit 2; }
Z="--cache-dir $OUT/zig-cache --global-cache-dir $OUT/zig-global-cache"
mkdir -p "$OUT/lib" "$OUT/gen" "$OUT/lean"
OUT="$(CDPATH= cd -- "$OUT" && pwd)"
Z="--cache-dir $OUT/zig-cache --global-cache-dir $OUT/zig-global-cache"
source_stamp() {
    (
        cd "$KERNEL"
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
        echo "build-net: source or toolchain changed; remove $OUT and rebuild" >&2; exit 2;
    }
fi
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
        for a in libc++.a libc++abi.a libunwind.a; do
            objcopy --remove-section=.deplibs "$L/lib/$a" "$OUT/lib/$a"
        done
        objcopy --weaken-symbol=initialize_libuv "$L/lib/lean/libleanrt.a" "$OUT/lib/libleanrt.a"
        cp "$L/lib/lean/libInit.a" "$L/lib/lean/libStd.a" "$L/lib/libgmp.a" "$L/lib/libuv.a" "$OUT/lib/"
        zig version >> "$OUT/versions.txt"
        (cd "$OUT" && sha256sum lean/*.o lib/*.a) > "$OUT/objects.sha256"
        cp "$OUT/source.current" "$OUT/source.sha256"
        touch "$OUT/lean/done"
    )
fi
(cd "$OUT" && sha256sum --quiet -c objects.sha256) || { echo "build-net: an object changed; remove $OUT" >&2; exit 2; }
printf 'pub const omit_call: ?u64 = null;\npub const probe = false;\npub const pretend: enum { nothing, no_saved_state, no_random, random_fails_at_boot, random_fails_when_served, clock_stuck } = .nothing;\n' \
    > "$OUT/gen/options.zig"
LIBS="$OUT/lib/libInit.a $OUT/lib/libleanrt.a $OUT/lib/libStd.a $OUT/lib/libInit.a $OUT/lib/libleanrt.a \
    $OUT/lib/libgmp.a $OUT/lib/libuv.a $OUT/lib/libc++.a $OUT/lib/libc++abi.a $OUT/lib/libunwind.a"
# shellcheck disable=SC2086
zig build-obj -target x86_64-freestanding-none -O ReleaseSmall -fno-PIE -fno-builtin \
    -fno-stack-check -fno-stack-protector --dep options "-Mroot=$HERE/kernel.zig" "-Moptions=$OUT/gen/options.zig" \
    -femit-bin="$OUT/kernel.o" $Z
# shellcheck disable=SC2086
zig build-obj -target x86_64-freestanding-none -O ReleaseSmall -fno-PIE -fno-builtin \
    -fno-stack-check -fno-stack-protector -femit-bin="$OUT/net.o" "$HERE/net.zig" $Z
# shellcheck disable=SC2086
zig build-obj -target x86_64-linux-musl -O ReleaseSafe -fno-PIE -lc \
    -femit-bin="$OUT/netmain.o" "$HERE/netmain.zig" $Z
# shellcheck disable=SC2086
zig build-exe -target x86_64-linux-musl -static -fno-PIE -femit-bin="$OUT/reflect-net.elf" \
    "$HERE/boot.S" "$OUT/kernel.o" "$OUT/net.o" "$OUT/netmain.o" "$HERE/glibc_names.c" \
    "$OUT"/lean/*.o $LIBS -lc --gc-sections $Z
# shellcheck disable=SC2086
zig build-exe -target x86_64-linux-musl -static -fno-PIE -femit-bin="$OUT/reply" \
    "$HERE/reply.zig" "$HERE/glibc_names.c" "$OUT"/lean/*.o $LIBS -lc --gc-sections $Z
# shellcheck disable=SC2086
zig build-exe -target x86_64-linux-musl -static -fno-PIE -femit-bin="$OUT/remote-check" \
    "$HERE/remote-check.zig" "$HERE/glibc_names.c" "$OUT"/lean/*.o $LIBS -lc --gc-sections $Z
# shellcheck disable=SC2086
zig build-exe -O ReleaseSafe -femit-bin="$OUT/quic-self" "$HERE/quic-self.zig" $Z
# shellcheck disable=SC2086
zig build-exe -O ReleaseSafe -lc -femit-bin="$OUT/quic-client" "$HERE/quic-client.zig" $Z
"$OUT/quic-self"
echo "built $OUT/reflect-net.elf"
