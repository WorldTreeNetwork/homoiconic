# Zig host check

From the repository root, run `sh host/check.sh` with Zig 0.16.0 and the
Lean toolchain pinned in `kernel/lean-toolchain` installed. The script builds
the package, checks `ReflectContract.lean`, `MachineContract.lean`,
`RequestContract.lean` and `Surface/Check.lean`, writes the
programs to run, compiles Lean to C and C to objects, compiles the Zig check to
an object, and links with `leanc`. Generated C, objects, the generated
`cases.zig`, the executable and Zig caches stay in ignored `out/`.

The host first calls `initialize_circularKernel_Surface_Host`, the symbol
emitted using Lake's package setup, then passes the result to
`kernel_finish_initialization` in `runtime.c`, which checks and releases it
and marks initialization complete.
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

The check also passes `42` followed by a zero byte and expects a syntax error
at column 3, so a zero byte does not end a program. It passes `42invalid` with a declared length of 2 and expects `42`:
bytes past the length are not part of the program.

The host runs with the operation table `arith` (`kernel/Reflect/Arith.lean`).
Programs reach it through the built-in names `add`, `sub`, `mul`, `div`, `mod`,
`equal`, `less`, and `op number argument`.

## Running a program file

`check.sh` also builds `out/run`:

```
host/out/run examples/append.hom          # prints [1, 2, 3, 4]
host/out/run examples/forever.hom 5000    # prints no result within 5000 steps
```

The second argument is the step budget; the default is 100000000, about two
seconds. `run.zig` reads the file, calls `reflect_run`, and prints the bytes
and a newline. It does not look at them, so it exits 0 for a value, an error
outcome, a syntax error, or a run with no result. It exits 2, with one line on
standard error that does not repeat the arguments, for a wrong argument count, a budget that is not a whole
number, a file it cannot read, or an answer it cannot write. An answer longer than 65536 bytes is asked
for a second time with a buffer of the needed size, which runs the program
twice.

## Running a program against answers

```
size_t reflect_converse(const uint8_t *program, size_t length,
                        const uint8_t *answers, size_t answers_length,
                        uint8_t *out, size_t capacity, uint64_t budget);
```

`reflect_converse` is the second export that evaluates. It borrows the
program bytes and the answers bytes, runs `Surface.converseText`
(`kernel/Surface/Run.lean`), and returns the number of bytes the rendering
needs, as `reflect_run` does. The answers text is a program whose result is an
array; its items are the answers. The rendering is one line `asked: <payload>`
for each request, in order, then how the run ended: the outcome as `run`
prints it, `waiting` when the program asked and no answer was left, or
`no result within N steps of a turn`. An answers text that does not read
prints `answers: ` and the syntax error; one whose result is not an array, or
that errors or does not finish, prints `answers: not an array`.

`check.sh` also builds `out/ask`:

```
host/out/ask examples/ask.hom examples/ask.answers       # asked: [1], asked: [2, 20], 42
host/out/ask examples/ask.hom examples/ask-one.answers   # asked: [1], asked: [2, 20], waiting
```

The third argument is the step budget for each turn: the first evaluation of
the program, each reading of a payload, each running of the rest on an answer,
and the answers program each get it afresh. The default is 100000000. There is
no budget for the whole run. `ask.zig` reads both files, calls
`reflect_converse`, and prints the bytes and a newline. It exits 0 whenever the
kernel answered, and 2, with one line on standard error, for a wrong argument
count, a budget that is not a whole number, a file it cannot read, or an answer
it cannot write. Each call runs the program from the start against the whole
answers file; a paused run is not stored.

A request carries no mark. Every function a turn ends in is read as a request,
so `fn x -> x` prints `error: wrong` and `fn x -> 42` prints `asked: 42` and
`waiting`. When a turn runs out of budget the requests printed before that
line are not covered by any theorem.

The Lean objects are compiled with `-O3`. Without it the machine runs about ten
times slower. Lean's runtime assertions are left on (`NDEBUG` is not defined):
turning them off gains about a third more speed and removes the checks that
would catch a fault in the generated C.
