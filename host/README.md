# Zig host check

From the repository root, run `sh host/check.sh` with Zig 0.16.0 and the
Lean toolchain pinned in `kernel/lean-toolchain` installed. The script builds
the package, checks `ReflectContract.lean`, `MachineContract.lean`,
`RequestContract.lean`, `StoreContract.lean` and `Surface/Check.lean`, runs
`ReflectRun.lean`, `WireCheck.lean`, `KeepCheck.lean` and `StoreCheck.lean`
and fails on a line that starts with `FAIL`, writes the
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

## Programs as bytes

```
size_t reflect_run_bytes(const uint8_t *program, size_t length,
                         uint8_t *out, size_t capacity, uint64_t budget);
size_t reflect_source_bytes(const uint8_t *program, size_t length,
                            uint8_t *out, size_t capacity);
```

`reflect_run_bytes` is `reflect_run` for a program given in its byte form
(`openspec/specs/wire-bytes/spec.md`). It reads the bytes with `Wire`, runs the
machine, and renders as `reflect_run` does. Bytes that are not the one form of
a value, or a value that is no program, render as `bytes error: ` and the
reason. `reflect_source_bytes` evaluates nothing. It reads a program's source
and answers one status byte, then either the program's byte form (status 0) or
the syntax error (status 1). Both return the number of bytes needed, as
`reflect_run` does. The Lean side is `kernel/Surface/Bytes.lean` and
`kernel/Surface/Host.lean`.

`check.sh` also builds `out/bytes`:

```
host/out/bytes examples/append.hom > append.bytes
host/out/run --bytes append.bytes         # prints [1, 2, 3, 4]
```

`run --bytes <file> [step-budget]` passes the file to `reflect_run_bytes` and
otherwise behaves as `run`. It exits 0 whenever the kernel answered, bad bytes
included, as `run` does on a syntax error. `bytes <program-file>` passes the
source to `reflect_source_bytes` and writes the byte form to standard output
with nothing added; Zig does not make or inspect the bytes. On a syntax error
it writes nothing to standard output, writes the kernel's text to standard
error, and exits 1, because standard output is for the byte form alone. It
exits 2, with one line on standard error, for a wrong argument count, a file it
cannot read, a kernel that did not start or answer, or a byte form it cannot
write. A byte form longer than 65536
bytes is asked for a second time with a buffer of the needed size.

`check.sh` writes each example as bytes, runs it with `--bytes`, and compares
the text with the source's; it includes a program whose byte form is longer
than the first buffer. It checks that `fn x -> x` is the three bytes
`82 01 00`, that `18 17` and an empty array are refused with the kernel's text,
and the exit codes of `bytes` on a syntax error and with no file.

## Keeping a program's state in a directory

```
lean_object *reflect_keep_start(const uint8_t *program, size_t length, uint64_t budget);
lean_object *reflect_keep_answer(const uint8_t *root, size_t root_length,
                                 const uint8_t *answer, size_t answer_length,
                                 uint64_t budget);
size_t reflect_keep_need(lean_object *session, uint8_t *out, size_t capacity);
lean_object *reflect_keep_give(lean_object *session, const uint8_t *piece, size_t length);
size_t reflect_keep_count(lean_object *session);
size_t reflect_keep_name(lean_object *session, size_t index, uint8_t *out, size_t capacity);
size_t reflect_keep_piece(lean_object *session, size_t index, uint8_t *out, size_t capacity);
size_t reflect_keep_text(lean_object *session, uint8_t *out, size_t capacity);
void kernel_retain(lean_object *value);
```

A session is one turn of a program whose state is kept in a store between
turns (`kernel/Surface/Keep.lean`). It is a Lean value the host holds and
cannot look inside. Every exported function that takes a session uses it up,
as Lean's exported functions do with every Lean value. Before each call that
must leave the session usable, the host calls `kernel_retain` on it
(`kernel/ffi.c`). `reflect_keep_give` takes the old session and returns the
next one. `reflect_keep_need`, `reflect_keep_name`, `reflect_keep_piece` and
`reflect_keep_text` return the number of bytes needed, as `reflect_run` does;
`reflect_keep_need` gives no bytes when no piece is needed.

`check.sh` also builds `out/keep`:

```
mkdir store
host/out/keep store start examples/keep.hom          # asked: [1], root: a399…
echo 20 > a.hom
host/out/keep store answer a399… a.hom               # asked: [2, 20], root: 5664…
echo 22 > b.hom
host/out/keep store answer 5664… b.hom               # [2000, 42]
```

`keep <store-dir> start <program-file> [step-budget]` runs the first turn of a
program. `keep <store-dir> answer <root> <answer-file> [step-budget]` runs the
next turn of the waiting program stored under `root`; the answer file is a
program whose result is the data to give. The default budget is 100000000
steps for each machine run in the turn. While the kernel names a piece it
needs, `keep.zig` reads the file of that name from the directory and passes
its bytes in. When the turn is over it writes each piece the kernel hands
back to a file with the name the kernel gives, then prints the kernel's text
and a newline. That text is `asked: <payload>`, `root: <64 hex digits>` and
`store: fetched N, wrote M` for a request, or the result and the `store:`
line. `wrote` counts pieces handed back, not new files. Zig does not read,
hash or name a piece: every name is the kernel's, and the kernel checks each
piece against the name it asked for. Files are not written atomically, and
nothing is deleted.

Exit codes: 0 whenever the kernel answered, a refused piece included
(`store error: piece <name> does not match its name`). 3 when the directory
lacks a piece the turn needs: one line on standard error naming it, nothing on
standard output, and nothing written; the same turn runs once the file is
back. 2, with a message on standard error, for a wrong call, a budget that is
not a whole number, a file or directory it cannot read, or a file it cannot
write.

`check.sh` runs `examples/keep.hom`, which builds a list of 2000 numbers and
asks twice. It checks the three turns print `asked: [1]`, `asked: [2, 20]` and
`[2000, 42]`, the same as `ask` against `[20, 22]`; that the second turn
fetches and writes fewer pieces than the first stored; that `b3sum`, where it
is installed, agrees with every file name; that the first root answered again
with 30 ends in `[2000, 52]` and adds fewer than ten files; that a turn run
twice gives the same root and no new file; the exit 3 with a piece moved away;
the refusal of a piece with a byte added; and the exit 2 cases.

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
answers file; a paused run is not stored. `keep`, above, stores one.

## Running a program as processes

```
size_t reflect_channels(const uint8_t *program, size_t length,
                        const uint8_t *schedule, size_t schedule_length,
                        uint8_t *out, size_t capacity,
                        uint64_t budget, uint64_t limit);
```

`reflect_channels` runs the program as the first of several processes that
talk over channels (`kernel/README.md`, Channels). It runs
`Surface.channelsText` (`kernel/Surface/Chan.lean`). With a schedule of no
bytes the kernel chooses the events, at most `limit`. Otherwise the schedule
text is a program whose result is an array of events, and exactly those are
run. An event is `[0, i, n]` (process `i` is given the new name `n`), `[1, i]`
(process `i` starts a process), `[2, i, j]` (process `i` sends to process `j`)
or `[3, i, a]` (process `i` is answered `a` from outside).

`check.sh` also builds `out/chan`:

```
host/out/chan examples/ping.hom
schedule: [[0, 0, 0], [1, 0], [0, 0, 1], [2, 0, 1], [2, 0, 1], [2, 1, 0]]
process 0: 42; holds [1, 0]
process 1: [41]; holds [1, 0]
nothing more can happen
```

The first line is the schedule that happened, in the form a schedule file is
written in. Saved to a file and given as the second argument, it prints the
same text. Then one line for each process: what it finished with, or the
payload it is waiting on, and the names it holds. The last line is
`nothing more can happen`, `more can happen`, `refused: <event> cannot happen`
for a schedule whose next event is not possible, or
`no result within N steps of a turn, at <event>`. After a refusal or a run out
of budget the lines above it describe the run up to that event.

```
host/out/chan examples/race.hom                          # process 1 gets the message
host/out/chan examples/race.hom examples/race.schedule   # process 2 gets it, on the name 5
host/out/chan examples/guess.hom                         # a name not held: both left waiting
host/out/chan examples/guess.hom examples/guess.schedule # refused: [2, 0, 1] cannot happen
```

The arguments after the program are a schedule file or `-` for none, the step
budget for each machine run (default 100000000), and the most events to choose
(default 10000). `chan.zig` reads the files, calls `reflect_channels`, and
prints the bytes and a newline. It chooses nothing. It exits 0 whenever the
kernel answered, and 2, with one line on standard error, for a wrong argument
count, a number that is not a whole number, a file it cannot read, or a
schedule file that is empty. The set of processes is not stored between calls.

Under `chan` the payloads `[0]`, `[1, name, message]`, `[2, name]` and
`[3, program, start]` are channel requests, so `examples/ask.hom`, whose
second request is `[2, 20]`, waits to receive on 20. Under `ask` a payload
means nothing to the kernel.

A request carries no mark. Every function a turn ends in is read as a request,
so `fn x -> x` prints `error: wrong` and `fn x -> 42` prints `asked: 42` and
`waiting`. When a turn runs out of budget the requests printed before that
line are not covered by any theorem.

The Lean objects are compiled with `-O3`. Without it the machine runs about ten
times slower. Lean's runtime assertions are left on (`NDEBUG` is not defined):
turning them off gains about a third more speed and removes the checks that
would catch a fault in the generated C.
