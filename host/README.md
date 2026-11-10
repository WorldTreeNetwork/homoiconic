# Zig host check

From the repository root, run `sh host/check.sh` with Zig 0.16.0 and the
Lean toolchain pinned in `kernel/lean-toolchain` installed. The script builds
the package, checks `Contract.lean` and `Surface/Check.lean`, writes the
programs to run, compiles Lean to C and C to objects, compiles the Zig check to
an object, and links with `leanc`. Generated C, objects, the generated
`cases.zig`, the executable and Zig caches stay in ignored `out/`.

The host first calls `initialize_circularKernel_Circular_Host` and
`initialize_circularKernel_Surface_Host`, the symbols emitted using Lake's
package setup, then passes both results to `kernel_finish_initialization` in
`runtime.c`, which checks and releases each and marks initialization complete.
Zig does not read the syntax, compile, or evaluate.

## `reflect_run`: surface text in, rendered text out

```
size_t reflect_run(const uint8_t *program, size_t length,
                   uint8_t *out, size_t capacity, uint64_t budget);
```

It borrows the program bytes (no trailing zero required; `kernel/ffi.c`
copies them into a Lean-owned array), reads the surface syntax, compiles the
term, runs the bytecode machine for `budget` steps, and renders the state.
It returns the number of bytes the rendering needs. If that is no more than
`capacity` the bytes are in `out`; otherwise nothing was written and the host
calls again with a buffer at least that large. There is no numeric result code.

The Lean side is `kernel/Surface/Host.lean`; the byte copy and store helpers
are in `kernel/ffi.c`. The reader, renderer and `runText` are
`kernel/Surface/Read.lean`, `Render.lean` and `Run.lean`. They are tested by
`kernel/Surface/Check.lean` against `Surface/Expect.lean`, not proved; what is
proved is that the machine's outcome for the term read is the term's outcome.

Rendering: a number is its digits, an array is `[1, 2, [3, 4]]`, a function is
`<function>`, then `error: unbound N`, `error: wrong`,
`no result within N steps`, and `syntax error: line L, column C: ...`.

`check.sh` runs `kernel/Surface/EmitCases.lean` to turn `Surface.prints` into
`out/cases.zig`, so the Zig check passes exactly the programs `Expect.lean`
lists and compares the printed bytes. Each is called with an 8-byte buffer
first and retried with a larger one when the first is too small. The Zig check
also tries a buffer too small for the answer (the needed length comes back and
the buffer is untouched) and four refused texts, comparing the syntax-error
bytes.

## `kernel_run`: the old kernel

`kernel_run` stays until `retire-circular-kernel`. `Circular.Host` parses
decimal indices, `[body]` and `(function argument)`, with ASCII whitespace
between tokens. It requires one complete term and rejects other bytes,
including quote syntax and embedded zero bytes. Parsing depth is bounded by
input length. Evaluation calls `Circular.evalFuel` with fuel 64 and the empty
environment. It returns 0 for a closure, `2 * i + 1` in uint32 arithmetic for
an unbound index, or 4294967295 for parse failure or exhausted fuel. This
finite budget does not decide divergence generally. The Zig executable checks
the five design scenarios and byte/parser boundary cases for it as before.
