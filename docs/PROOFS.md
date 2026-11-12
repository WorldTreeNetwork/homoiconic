# What is proved

A record of what the Lean proofs say, how they got there, and what they leave
out. The exact statements are in `kernel/ReflectContract.lean`,
`kernel/MachineContract.lean`, `kernel/RequestContract.lean` and
`kernel/StoreContract.lean`; the requirements are in `openspec/specs/`.
Written 2026-11-10, after `add-operation-tables`; updated 2026-11-10, after
`add-requests`, and 2026-11-11, after `add-state-store`.

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

**2026-11-10: requests.** A program can ask the outside for something and
continue from the answer (`b5885e3`, `c14f63a`). A request is not a new
outcome: it is a function value that holds a payload and the rest of the
program, and a driver outside evaluation answers it from a list. Nothing in
the language, evaluation, the interpreter or the machine changed, and no
earlier theorem statement changed. The driver is defined once over any way of
evaluating, so the agreement of the interpreter and the machine with direct
evaluation carries over to whole runs of requests and answers.

**2026-11-11: stored state.** A running program's state can be held in pieces
and fetched on first use (`f022a06`, `9348a9d`). A piece is a number, an empty
list, a pair, a function, or a reference to another piece. A lazy machine runs
a partial state, fetches a piece when a step first looks at it, and pauses
when the store lacks it. The kind of reference is a parameter, as the
operation table is. Nothing in the language, evaluation, the interpreter or
the machine changed, and no earlier theorem statement changed.

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

### Requests

A run is a program driven against a list of answers: the requests it makes, in
order, and how it ends (finished with an outcome, or waiting on a request).

| Theorem | Says |
|---|---|
| `interact_deterministic` | The requests a program makes and how it ends are fixed by the program and the answers |
| `interact_resume` | A waiting program continued with an answer is the program run from the start with that answer added |
| `interact_extra` | A program that finished is not changed by more answers |
| `interact_reflective` | The interpreter, driven on data, makes the same requests in the same order and ends the same way |
| `interact_coverage` | Every interpreted run is the data form of a run of the program |
| `interact_machine` | The machine makes the same requests and ends the same way |
| `interact_machine_exact` | Whatever the machine's run ends with is the compiled form of the program's ending |
| `converse_finished`, `converse_waiting` | What the executable driver reports as finished or waiting is a run of the program by direct evaluation |

### Stored state

A store holds pieces under references and may lack any of them. A piece
resolves to a value when following every reference gives that value. These
hold for every operation table and every kind of reference.

| Theorem | Says |
|---|---|
| `saved_resolves` | A state held whole resolves to itself |
| `cut_resolves` | A stored piece can be replaced by its reference, and what resolves is the same |
| `RState.mono` | A state that resolves still does when the store holds more |
| `Unf.unique`, `resolve_unique` | A piece resolves to one thing, and a partial outcome to one outcome |
| `lazy_simulates` | For every number of plain steps, the lazy machine with the whole store reaches a state that resolves to the plain machine's state |
| `lazy_complete` | The lazy machine halts with what the plain machine halts with |
| `lazy_sound` | Under any part of the store, what the lazy machine halts with is what the plain machine halts with |
| `lazy_pause` | A run pauses only on a reference the store lacks, and under a store that holds more, the run from the start passes through the paused state |
| `lrun_mono` | More pieces change no run that did not pause |
| `lazy_agree` | Two stores that agree wherever both hold a piece give the same result from the same state, when both runs halt |
| `lazy_program` | A program run through any store has exactly the outcome direct evaluation gives it |
| `lazy_turn_complete`, `lazy_turn_sound` | A turn of the request driver from a stored continuation is a turn of the machine |

## Why these proofs can be trusted

- **Both directions.** The main theorems are "if and only if". Errors map
  across exactly, and a program that never finishes never halts the machine.
- **Nothing assumed.** No `sorry`, no added axiom. The contract files print
  each theorem's axioms on every check.
- **The contract cannot rot.** The four contract files restate each theorem
  with its exact signature, so a weakened theorem fails to compile. They do
  not import an operation table, so nothing is proved for one table only.
- **New operations cost no proof.** Adding a table changes no lemma.
- **The fast path equals the specification.** What the host runs is the
  machine with the early-exit loop, and both are proved equal to `Direct`.
- **Compiled code is still data.** Bytecode decompiles to the term it came
  from.
- **Read by another model family.** Each change went to an outside reviewer
  before it was folded. Reviews have sent work back six times before
  accepting. `add-state-store` was accepted on first reading.

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
- **A request carries no mark.** The driver reads every function a turn
  ends in as a request, so a driven program cannot finish with a function as
  its result, and one that returns a function by mistake may be read as
  asking.
- **Reaching only what a program was handed (P12).** A payload is data, and a
  program can build any data. Nothing here stops a program from naming
  something it was not given.
- **Completeness of the driver, and unfinished runs.** `converse` is proved
  sound, not complete: that every run is reported for some budget is not
  proved. When a turn does not finish within its budget, nothing is claimed,
  including about the requests listed before it.
- **A budget for a whole run.** The step budget is per machine run: the first
  evaluation, each reading of a payload, and each running of the rest on an
  answer get it afresh.
- **What a reference means.** That a reference names one piece, for ever, is
  assumed. The theorems state it as a hypothesis on the stores they compare.
  How a reference is made and checked is outside the kernel.
- **Bytes, hashing and disk.** The store is in memory. A piece has no byte
  form yet, references are not hashes, and nothing is written to disk.
- **Writing back.** The lazy machine does not write fetched pieces back to the
  state or the store. Remembering them is the store's.
- **Partial arguments.** An operation fetches its whole argument before it
  runs.
- **Finer cuts.** Code, the stack and the frame list are held whole. Their
  values and environments can be references.
- **Garbage collection.** Nothing is deleted. Which pieces no kept root
  reaches is not computed.
- **Fetch steps.** There is no bound on the number of steps the lazy machine
  takes to fetch.
- **An executable driver over stored state.** The theorems cover each turn.
  `converse` and the `ask` command still run in memory and replay from the
  start.
- **Sharing in the check.** `StoreCheck.lean` cuts a state as a tree, so a
  value held in two places is stored twice.
- **The network.** What a payload means, logs, several VMs and model calls
  are the roadmap in `openspec/changes/add-verifiable-network-vision/`.

## Next

The store needs bytes and hashing to go on disk: `add-wire-bytes`
(`homoiconic-q59.12`). The event log and one VM follow (vision stage 5, P13
and P14).
