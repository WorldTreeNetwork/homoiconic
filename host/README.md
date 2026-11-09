# Zig host check

From the repository root, run `sh host/check.sh` with Zig 0.16.0 and the
Lean toolchain pinned in `kernel/lean-toolchain` installed. The script builds
the package, checks `Contract.lean`, compiles Lean to C and C to objects,
compiles the Zig check to an object, and links with `leanc`.

The host first calls `initialize_circularKernel_Circular_Host`, the symbol
emitted using Lake's package setup. The C runtime helper checks and releases
its result and marks initialization complete. Each `kernel_run` call then
borrows a pointer and byte length; `kernel/ffi.c` copies those bytes into a
Lean-owned array. No trailing zero is required. Zig does not parse or evaluate.

`Circular.Host` parses decimal indices, `[body]` and `(function argument)`,
with ASCII whitespace between tokens. It requires one complete term and
rejects other bytes, including quote syntax and embedded zero bytes. Parsing
depth is bounded by input length. Evaluation calls `Circular.evalFuel` with
fuel 64 and the empty environment. It returns 0 for a closure, `2 * i + 1`
in uint32 arithmetic for an unbound index, or 4294967295 for parse failure
or exhausted fuel. This finite budget does not decide divergence generally.

The Zig executable checks the five design scenarios and byte/parser boundary
cases. Generated C, objects, executable and Zig caches stay in ignored `out/`.
