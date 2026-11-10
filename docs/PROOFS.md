# What is proved

A record of what the Lean proofs say, how they got there, and what they leave
out. The exact statements are in `kernel/ReflectContract.lean` and
`kernel/MachineContract.lean`; the requirements are in `openspec/specs/`.
Written 2026-11-10, after `add-operation-tables`.

## In one sentence

The language proves its own interpreter correct on every program, and keeps
that proof when the set of processor operations changes.

## How the quote proof got here

**2026-11-08: correct, except for quote.** The first kernel, `Circular`, had
`quote` as a term, but direct evaluation had no rule for it. A Lean function
beside the language turned programs into data, with a Mogensen–Scott encoding
into lambdas. The theorem `metacircular` (commit `46048e9`) said the
interpreter written in the language agrees with direct evaluation, for
programs that contain no quote. A program could not build, hold or inspect
another program. Code was data in Lean and not in the language.

**2026-11-09: the side condition goes.** Data became primitive: numbers and
arrays. In the library `Reflect` a literal holds data, and `reify` maps every
term to data. The interpreter takes that data apart with an ordinary case
expression. `reflective` (commit `4ec21ae`) has no condition on the program:

> `p` evaluates to `o` exactly when the interpreter applied to `p`'s data form
> evaluates to `o`'s data form.

**2026-11-10: one kernel, and operations.** `Circular` was deleted (`26a88ca`).
Every theorem now begins `∀ [Ops]`: it holds for every table of operations
(`f89c88a`). The interpreter runs an operation by using the same operation, so
it never looks at which table is in force.

## The definitions

- **Data** is numbers and arrays.
- **Terms** are variable, function, application, literal, successor, cons,
  case on data, and operation.
- **`reify`** turns any term into data.
- **Evaluation** is defined twice: as a relation, `Direct`, and as a function
  with fuel, `evalFuel`.
- **Outcomes** are a value, an unbound variable, or `wrong`. A program that
  runs forever has no outcome.

## The theorems

All hold for every operation table. All rest on Lean's three standard axioms
and nothing else.

### Evaluation

| Theorem | Says |
|---|---|
| `direct_deterministic` | A program has at most one outcome |
| `direct_iff_evalFuel` | The relation and the runnable function agree |

### The interpreter written in the language

| Theorem | Says |
|---|---|
| `reflective` | A program gives `o` exactly when the interpreter on the program's data gives `o`'s data |
| `reflective_coverage` | The interpreter only ever produces the data form of a real outcome |
| `reflective_env` | The same for open terms in any environment |
| `tower` | Interpreters stacked `k` deep still agree |

### The stack machine

| Theorem | Says |
|---|---|
| `machine_correct` | A program gives `o` exactly when the compiled program halts with `o` |
| `machine_exact` | Anything the machine halts with is the outcome of the program |
| `machine_never_halts` | A program with no outcome never halts the machine |
| `run_add`, `run_halted` | Pausing and resuming equals running straight through; a halted machine stays halted |
| `runUntil_eq` | The early-exit loop the host uses equals the proved one |
| `decompile_compile` | Bytecode converts back to the exact term |
| `depth_bound` | Stack depth grows by at most one per step |

## Why these proofs can be trusted

- **Both directions.** The main theorems are "if and only if". Errors map
  across exactly, and a program that never finishes never halts the machine.
- **Nothing assumed.** No `sorry`, no added axiom. The contract files print
  each theorem's axioms on every check.
- **The contract cannot rot.** The two contract files restate each theorem
  with its exact signature, so a weakened theorem fails to compile. They do
  not import an operation table, so nothing is proved for one table only.
- **New operations cost no proof.** Adding a table changes no lemma.
- **The fast path equals the specification.** What the host runs is the
  machine with the early-exit loop, and both are proved equal to `Direct`.
- **Compiled code is still data.** Bytecode decompiles to the term it came
  from.
- **Read by another model family.** Each change went to an outside reviewer
  before it was folded. Reviews sent work back five times before accepting.

## What the proofs do not cover

- **Reader, renderer, Zig host.** Tested, not proved.
- **What an operation computes.** The arithmetic table is seven Lean
  definitions with test scenarios. No theorem is about it.
- **Failure inside an operation.** An operation is a total function from data
  to data. It cannot fail as `wrong`; arithmetic answers `[]` for input it does
  not expect.
- **Cost and time.** A step budget counts machine steps, not work inside an
  operation (`homoiconic-q59.9`).
- **The fault state.** That a non-halting run never reaches the machine's
  fault state is not proved (`homoiconic-q59.3`).
- **Speed.** About 34 million machine steps per second, with operations
  emulated in compiled Lean.
- **The network.** Requests, logs, several VMs and model calls are the
  roadmap in `openspec/changes/add-verifiable-network-vision/`.

## Next

Requests: a program that asks the outside for something, stops, and continues
from the answer. The change is `add-requests`.
