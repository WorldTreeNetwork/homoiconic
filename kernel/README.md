# Kernel

One Lean package with two libraries, and the host that calls it.

- `Reflect` is the language and its proofs. A program is a data value, and
  one closed term of the language interprets programs given as data.
- `Surface` reads program text into `Reflect` terms and renders outcomes as
  text. It is tested, not proved.
- The Zig host in `../host` calls the export `reflect_run`.

Use Lean 4.35.0, pinned in `lean-toolchain`, and run from this directory:

```sh
lake build
lake env lean ReflectContract.lean   # the interpreter theorems, exact statements
lake env lean MachineContract.lean   # the machine theorems, exact statements
lake env lean ReflectRun.lean        # the scenarios, executed
lake env lean Surface/Check.lean     # the reader and renderer against examples
lake exe reflectBench                # steps per second
```

Both contract files print each theorem's axioms. They are Lean's standard
three (`propext`, `Classical.choice`, `Quot.sound`), with no admissions.

## Reflect

| File | Holds |
|---|---|
| `Reflect/Syntax.lean` | `Data` (numbers and arrays), `Term`, and `reify : Term → Data` |
| `Reflect/Semantics.lean` | `Direct`, the call-by-value relation; `evalFuel`, its total executable form |
| `Reflect/Interpreter.lean` | `interp`, the interpreter as one closed term; `level k` nests it |
| `Reflect/SemanticsProofs.lean` | `Direct` is deterministic; `evalFuel` agrees with it |
| `Reflect/Proof.lean`, `Correctness.lean` | `reflective`, `reflective_coverage`, `reflective_env`, `tower` |
| `Reflect/Machine.lean` | `compile`, `step`, `run`: a stack machine that can stop after any step |
| `Reflect/MachineProof.lean`, `MachineExact.lean` | `machine_correct`, `machine_exact`, `machine_never_halts`, `run_add`, `depth_bound` |
| `Reflect/RunUntil.lean`, `RunUntilProof.lean` | `runUntil`, which stops when the machine stops, and `runUntil_eq` |
| `Reflect/Examples.lean` | Worked cases, checked by the kernel |

`reflective` says: for every term `p` and outcome `o`, `p` evaluates to `o`
exactly when the interpreter applied to `p` as data evaluates to the data form
of `o`. There is no fragment and no fuel in the statement. `tower` says the
same for the interpreter interpreting itself to any depth.

## Surface

`Surface/Read.lean` is the reader, `Render.lean` the renderer, `Run.lean` joins
them to the machine, and `Host.lean` is the C export. `Expect.lean` is the
specification by example that `Check.lean` runs.

## History

The first kernel, `Circular`, proved the interpreter theorem for quote-free
programs with a Mogensen–Scott encoding. `Reflect` replaced it. It is in git at
`8b23867` and earlier.
