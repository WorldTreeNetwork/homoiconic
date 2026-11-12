# Kernel

One Lean package with three libraries, and the host that calls it.

- `Reflect` is the language and its proofs. A program is a data value, and
  one closed term of the language interprets programs given as data.
- `Wire` is the byte form of data, programs and machine values. It is tested,
  not proved, except `unreify_reify`.
- `Surface` reads program text into `Reflect` terms and renders outcomes as
  text. It is tested, not proved.
- The Zig host in `../host` calls the exports `reflect_run`, `reflect_converse`,
  `reflect_run_bytes` and `reflect_source_bytes`.

Use Lean 4.35.0, pinned in `lean-toolchain`, and run from this directory:

```sh
lake build
lake env lean ReflectContract.lean   # the interpreter theorems, exact statements
lake env lean MachineContract.lean   # the machine theorems, exact statements
lake env lean RequestContract.lean   # the request theorems, exact statements
lake env lean StoreContract.lean     # the stored-state theorems, exact statements
lake env lean ReflectRun.lean        # the scenarios, executed
lake env lean Surface/Check.lean     # the reader and renderer against examples
lake env lean StoreCheck.lean        # runs cut into pieces and continued
lake env lean WireCheck.lean         # the byte form against vectors and programs
lake exe reflectBench                # steps per second
```

All four contract files print each theorem's axioms. They are Lean's standard
three (`propext`, `Classical.choice`, `Quot.sound`), with no admissions.

## Reflect

| File | Holds |
|---|---|
| `Reflect/Syntax.lean` | `Data` (numbers and arrays), `Term`, and `reify : Term → Data` |
| `Reflect/Semantics.lean` | `Ops`, the table of operations; `Direct`, the call-by-value relation; `evalFuel`, its total executable form |
| `Reflect/Arith.lean` | `arith`, the first table: exact arithmetic and comparison. No theorem depends on it |
| `Reflect/Interpreter.lean` | `interp`, the interpreter as one closed term; `level k` nests it |
| `Reflect/SemanticsProofs.lean` | `Direct` is deterministic; `evalFuel` agrees with it |
| `Reflect/Proof.lean`, `Correctness.lean` | `reflective`, `reflective_coverage`, `reflective_env`, `tower` |
| `Reflect/Machine.lean` | `compile`, `step`, `run`: a stack machine that can stop after any step |
| `Reflect/MachineProof.lean`, `MachineExact.lean` | `machine_correct`, `machine_exact`, `machine_never_halts`, `run_add`, `depth_bound` |
| `Reflect/RunUntil.lean`, `RunUntilProof.lean` | `runUntil`, which stops when the machine stops, and `runUntil_eq` |
| `Reflect/Request.lean` | `askTerm`, `payloadTerm`, `resumeTerm`; `Sys`, a way of evaluating; `Drive`, the driver over any `Sys`; `Interact`, `InteractI`, `InteractM`; `driveRun` and `converse`, the executable driver |
| `Reflect/RequestProof.lean` | Determinism, resume and extra answers; `Sim.drive`, which lifts turn-by-turn agreement to runs; the interpreter and machine instances; soundness of `converse` |
| `Reflect/Store.lean` | `P`, a piece; `Store`; `Unf`, which resolves a piece; partial states; `lstep` and `lrun`, the lazy machine, with a pause; `RState` |
| `Reflect/StoreProof.lean` | Saving loses nothing; the lazy machine reaches every plain state; a missing piece is a pause; more pieces change nothing; stores that agree give the same result; a turn of the request driver from a stored continuation |
| `Reflect/Examples.lean` | Worked cases, checked by the kernel |

`reflective` says: for every term `p` and outcome `o`, `p` evaluates to `o`
exactly when the interpreter applied to `p` as data evaluates to the data form
of `o`. There is no fragment and no fuel in the statement. `tower` says the
same for the interpreter interpreting itself to any depth.

## Operations

`prim c x` runs operation number `c` on the data value `x`. What an operation
computes is not part of the language. It comes from a table, `Ops`, holding one
total function `op : Nat → Data → Data`, and every definition and theorem takes
the table as a parameter. The interpreter is the same term for every table, so
adding an operation is adding a line to a table: no proof changes.

The contract files state each theorem as `∀ [Ops], …` and do not import a
table. The host runs with `arith`.

## Requests

A request is a function value: `ask payload next` is the closed term
`askTerm`, which hands `payload` and `next` to its caller. No term, value,
outcome, rule or instruction is added. A driver, `Drive`, runs a program
against a list of answers. A turn that ends in data or an error ends the run.
A turn that ends in a function is read as a request, whether or not `ask`
built it: the driver applies it to `payloadTerm` to read the payload, which
must be data, and to `resumeTerm` to run the rest on the next answer. With no
answer left the run is waiting.

`Drive` is defined once over `Sys`, a way of evaluating, and used three times:
`Interact` (direct evaluation), `InteractI` (the interpreter on data) and
`InteractM` (the machine). `RequestContract.lean` states
`interact_deterministic`, `interact_resume`, `interact_extra`,
`interact_reflective`, `interact_coverage`, `interact_machine`,
`interact_machine_exact`, `converse_finished` and `converse_waiting`, each as
`∀ [Ops], …`. `converse` gives each machine run a fresh step budget and is
proved sound, not complete.

## Stored state

A piece, `P R`, is a number, an empty list, a pair, a function (code and its
environment), or a reference `ref r`. One type serves for data, values and
environments. `R` is the kind of reference and is a parameter of every
definition and theorem; nothing in the kernel says how a reference is made. A
store, `Store R`, maps references to pieces and may lack any of them. `Unf`
says a piece resolves to a value by following every reference, and `RState`
says the same of a partial machine state.

The lazy machine, `lstep` and `lrun`, runs a partial state. When a step has to
look at a reference it fetches that one piece. When the store lacks it the run
pauses, holding the reference and the state it stopped in. It does not write
fetched pieces back. `StoreContract.lean` states `saved_resolves`,
`cut_resolves`, `RState.mono`, `Unf.unique`, `resolve_unique`,
`lazy_simulates`, `lazy_complete`, `lazy_sound`, `lazy_pause`, `lrun_mono`,
`lazy_agree`, `lazy_program`, `lazy_turn_complete` and `lazy_turn_sound`, for
every table and every kind of reference. `StoreCheck.lean` stops eight
programs at four points, cuts each at every value, and continues it with the
whole store and with one piece withheld; it also keeps a waiting run and
continues it from its root. A line that starts with `FAIL` fails the check.
Hashing, the byte form of a piece, disk, the network and attestation are not
part of the store; the store is in memory.

## Wire

`Wire` is the byte form. It is its own library: no definition or theorem in
`Reflect` mentions bytes.

| File | Holds |
|---|---|
| `Wire/Cbor.lean` | `write : Data → ByteArray` and `read : ByteArray → Except String Data`, for the part of dCBOR that `Data` has. A number below 2^64 is a CBOR unsigned integer in its shortest form; a larger number is tag 2 over its bytes with no leading zero; an array is a definite-length CBOR array. The reader refuses every other spelling |
| `Wire/Form.lean` | `unreify`, which reads a program back from its data form, and `unreify_reify`; `blockTerm`; `valueData` and `dataValue`, a machine value as data; `programBytes`, `readProgram`, `valueBytes`, `readValue` |

A program's bytes are the bytes of `reify` of it; the identity function is
`82 01 00`. A machine value is `[0, d]` for data and `[1, body, captured]` for
a function, where `body` is the program its code was compiled from. Reading
compiles `body` again. `decompile` also reads code that no compilation gives,
so `blockTerm` compiles its result and compares: a function whose code is not
exactly a compiled program has no byte form. Tag 2 for large numbers is this
project's rule; dCBOR's numeric rules stop at 64 bits.

Proved: `unreify_reify`, `unreify (reify t) = some t` for every program, with
Lean's standard axioms. Everything else in `Wire` is tested, not proved
(decision D7 of the vision). `WireCheck.lean` checks the RFC 8949 appendix A
examples that are numbers or arrays, each integer width at its edges,
twenty-six spellings that must be refused, every string of one or two bytes,
eleven programs written, read back and run from their bytes, a waiting run
kept as bytes and continued, data that is no program, and a function whose
code no program compiles to. It prints the axioms of `unreify_reify`. A line
that starts with `FAIL` fails the check.

## Surface

`Surface/Read.lean` is the reader, `Render.lean` the renderer, `Run.lean` joins
them to the machine, `Bytes.lean` runs a program given as bytes and gives a
program's byte form from its source, and `Host.lean` holds the C exports. `Expect.lean` is the
specification by example that `Check.lean` runs.

## History

The first kernel, `Circular`, proved the interpreter theorem for quote-free
programs with a Mogensen–Scott encoding. `Reflect` replaced it. It is in git at
`8b23867` and earlier.
