#!/bin/sh
# Object-link a Lean export that calls evalFuel, then print one code per program.
set -eu
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
SPIKE="$(pwd)"
ROOT="$(cd ../../.. && pwd)"
mkdir -p out
LIBDIR="$(lean --print-libdir)"
# Compile the two kernel modules outside the package root. Inside it, Lean
# looks up the Lake oleans and emits the package-qualified symbol names.
rm -rf out/root
mkdir -p out/root/Circular
cp "$ROOT/kernel/Circular/Syntax.lean" out/root/Circular/Syntax.lean
cp "$ROOT/kernel/Circular/Semantics.lean" out/root/Circular/Semantics.lean
# A package root makes `Circular` a module prefix. The name stays off the
# kernel package so these objects do not collide with its Lake oleans.
cat > out/root/lakefile.toml <<'EOF'
name = "spikehost"
version = "0.0.0"
EOF
export LEAN_PATH="$LIBDIR:$SPIKE/out/root"
(
  cd out/root
  lean -o Circular/Syntax.olean -c ../Syntax.c Circular/Syntax.lean
  lean -o Circular/Semantics.olean -c ../Semantics.c Circular/Semantics.lean
)
lean -c out/spike.c src/Spike.lean
leanc -c -o out/Syntax.o out/Syntax.c
leanc -c -o out/Semantics.o out/Semantics.c
leanc -c -o out/spike.o out/spike.c
zig build-obj host.zig -femit-bin=out/host.o
leanc -o out/host out/host.o out/spike.o out/Semantics.o out/Syntax.o
./out/host
