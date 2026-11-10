# Kernel

One Lean package with two libraries, and the host that calls it.

- `Reflect` is the language and its proofs. A program is a data value, and
  one closed term of the language interprets programs given as data.
- `Surface` reads program text into `Reflect` terms and renders outcomes as
  text. It is tested, not proved.
- The Zig host in `../host` calls the exports `reflect_run` and `reflect_converse`.

Use Lean 4.35.0, pinned in `lean-toolchain`, and run from this directory:

```sh
lake build
lake env lean ReflectContract.lean   # the interpreter theorems, exact statements
lake env lean MachineContract.lean   # the machine theorems, exact statements
lake env lean RequestContract.lean   # the request theorems, exact statements
lake env lean ReflectRun.lean        # the scenarios, executed
lake env lean Surface/Check.lean     # the reader and renderer against examples
lake exe reflectBench                # steps per second
```

All three contract files print each theorem's axioms. They are Lean's standard
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

## Surface

`Surface/Read.lean` is the reader, `Render.lean` the renderer, `Run.lean` joins
them to the machine, and `Host.lean` is the C export. `Expect.lean` is the
specification by example that `Check.lean` runs.

## History

The first kernel, `Circular`, proved the interpreter theorem for quote-free
programs with a Mogensen–Scott encoding. `Reflect` replaced it. It is in git at
`8b23867` and earlier.
