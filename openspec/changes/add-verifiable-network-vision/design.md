# add-verifiable-network-vision

The architecture the vision implies, and the proofs that carry it. Statements are sketches. Each owning change fixes the exact Lean signature and puts it in a `Contract.lean` check the way `metacircular` is.

## Where the floor stands

Proved in `kernel/`:

- `direct_deterministic`: `Direct` has at most one outcome.
- `evalFuel_sound`, `evalFuel_complete`, `evalFuel_mono`: the executable entry agrees with `Direct`.
- `metacircular`, `coverage`: at the empty environment, on every quote-free term, the interpreter term and `Direct` agree.
- Round trip and injectivity for the outcome encoding (`decodeOutcome_encodeOutcome`, `encodeOutcome_injective`, `Represents_unique`).

Not yet true:

- **Code-as-data is in Lean, not in the language.** `encode` is a Lean function. `quote` has no evaluation rule in `Direct`. An object program cannot build or inspect a program.
- **No value leaves the kernel.** `kernel_run` returns one `uint32`. Every closure is `0`.
- **The result code is ambiguous.** `resultCode` computes `2 * i + 1` in 32-bit arithmetic. `unbound 2147483647` gives `4294967295`, the code for `none`. Indices from `2147483648` up wrap onto smaller ones.
- **The parser has no theorem.** `parseProgram` is total and tested, and nothing relates it to a printer.
- **Fuel is a height bound fixed at 64 in the host.** It is not a step count and the interpreter route needs a different amount.
- **Evaluation cannot pause.** `evalFuel` is big-step.

## Decisions

### D1. Data carrier — open

Data is currently Scott-encoded lambda terms. The alternative is a primitive first-order type: bytes and pairs, or S-expressions.

| | Scott-encoded | Primitive data |
|---|---|---|
| Kernel size | Smallest | A few more rules |
| Wire format | Must be derived from terms | Is the data |
| Hashing | Over term syntax | Over the data |
| Inspecting code in the language | Only by applying it | By case analysis |
| Existing proof | Stands as is | Restated through P8 |

Recommendation: primitive data, introduced through the parametric statement P8, with `quote` producing it. Every proof from P4 on depends on this choice. It is the first thing stage 1 settles, by a spike that restates `metacircular` for a language with one primitive data type and reports the cost.

### D2. The machine is the executable entry; `Direct` stays the specification

`Direct` remains the definition of meaning. A step machine with an explicit state becomes what runs. P1 ties them. `evalFuel` stays as a second, simpler executable witness.

### D3. Non-determinism enters only as an answer to a request

The evaluator stays deterministic. A program that needs a model, a clock, a random number, or another VM stops with a request. The answer comes from outside and is recorded. There is no probabilistic rule in the semantics.

### D4. Delivery order is an input

The network model does not pick an order and does not pretend order is irrelevant. A schedule is data. Theorems are either "the same for every schedule" (P16, for a named class) or "a function of the schedule" (P17).

### D5. Hashing is a hypothesis, not an axiom

Collision resistance appears as an explicit premise on theorems that need it. No axiom is declared in the package. `#print axioms` stays clean.

### D6. Lean owns the log and the network semantics

The partition extends. The step function, the event handler, the log fold, the serialization, and the network transition are Lean definitions. Zig owns sockets, files, the event loop, and calling a model. Zig does not decide what an event means.

## Proof obligations

Ordered by dependency. "Free" means it follows from earlier results with little new work.

### Machine

| | Statement | Why | Needs |
|---|---|---|---|
| **P1** | `Direct env t o ↔ ∃ n, run n (load env t) = done o` | The thing that runs means what `Direct` says. | — |
| **P2** | `run (n + m) s = run m (run n s)` | Pause, resume, checkpoint, slice. | P1's machine |
| **P3** | After `n` steps the state holds at most `c * n + size s₀` cells | A budget bounds memory, not only time. A hostile program cannot exhaust a VM. | P1's machine |

### Bytes

| | Statement | Why | Needs |
|---|---|---|---|
| **P4** | `parse (print x) = some x` for terms, values, outcomes, and machine states; `print` is injective | One canonical form. The current parser gets its theorem here. | D1 |
| **P5** | Given a hash with no collisions on a set `S`: `hash (print a) = hash (print b) → a = b` for `a b ∈ S` | A hash names a program. | P4, D5 |

### Wider language

| | Statement | Why | Needs |
|---|---|---|---|
| **P6** | `metacircular` at an arbitrary pure environment | A shipped closure is never at `[]`. The internal lemma `source_beta` already carries an environment. | — |
| **P7** | For every depth `k`, the interpreter interpreting itself `k` times agrees with `Direct`. **Free:** `interpreterApplication` is pure, so `metacircular` applies to it; induct on `k` and compose `Represents`. | Rules can be stacked: a metering interpreter under a tracing one. | P6 helps |
| **P8** | For a signature of primitives, each with a rule and an object-level implementation satisfying one local lemma, `metacircular` holds for the extended language | Adding numbers or bytes costs one lemma each, not a new 785-line simulation. | D1 |
| **P9** | The interpreter's step count is bounded by a stated function of the program's step count and size | A step budget means something at every interpreter depth. | P1 |

### Requests

| | Statement | Why | Needs |
|---|---|---|---|
| **P10** | With a `request op payload k` outcome: the final outcome and the request trace are a function of the code and the list of answers | Replay. This is `direct_deterministic` lifted to interactive programs. | P1, P2 |
| **P11** | The interpreter run on `encode p` emits a request trace that represents `p`'s trace, answer by answer | `metacircular` lifted from outcomes to traces. An interpreter that adds a rule does not change what the program asks for. | P10, P6 |
| **P12** | Every `op` a program requests is reachable from the environment it started with | A program cannot reach an effect it was not handed. | P10 |

### One VM

| | Statement | Why | Needs |
|---|---|---|---|
| **P13** | `state log = foldl handle init log`, and the running VM's state equals it after any prefix | The log is the truth. A snapshot is a prefix. | P10 |
| **P14** | Handling an event whose identifier is already in the log leaves the state unchanged | At-least-once delivery behaves as exactly-once. | P13, P5 |

### Network

| | Statement | Why | Needs |
|---|---|---|---|
| **P15** | `run n (parse (print s)) = run n s`, and: a request answered by sending a closure to another VM, running it, and returning the bytes gives the outcome of running it locally. **Mostly free** from P4, P2, P6. | Location does not change meaning. | P4, P2, P6 |
| **P16** | For a named class of handlers, the final configuration is the same for every delivery schedule | Some programs need no ordering. The class must be decidable or checked by a proved checker. | P13 |
| **P17** | The network configuration after a schedule is a function of the initial configuration, the schedule, and the answers | Everything else is replayable given the order. | P13, P10 |

### Model calls

| | Statement | Why | Needs |
|---|---|---|---|
| **P18** | If an output is labelled independent, it is equal under every two answer lists | The exact part of a program stays exact. | P10 |
| **P19** | `∀ a, check a = true → Safe (resume k a)` for a program's stated `check` and `Safe` | The model proposes. Proved code decides. The obligation is on the checker and the continuation. | P10 |

### Receipts

| | Statement | Why | Needs |
|---|---|---|---|
| **P20** | `verify r = true → ` the receipt's code, on its inputs and answers, has the receipt's outcome. **Free today** for plain programs: `evalFuel n [] p = some o` is a checkable certificate by `evalFuel_sound`. | A receipt cannot lie about a result. | P4; P10 for answers |
| **P21** | Two parties who commit to different states after `n` steps reach, in `⌈log₂ n⌉` rounds, one step that a single `step` call decides; the party whose claims are true is never the one refuted | Disputes are cheap to settle. | P1, P2, P4, P5 |

## What is assumed, not proved

- **The model.** That a given model produced an answer, or that the answer is good. This enters as a signed answer, re-execution of fixed-weight integer inference, a hardware attestation, or a succinct proof. The system records which.
- **The toolchain.** The Lean compiler, `leanc`, the C compiler, and `kernel/ffi.c`. The theorems are about Lean definitions.
- **The hash.** See D5.
- **Divergence.** A receipt can show a result within `n` steps. It cannot show that a program never finishes.
- **Liveness.** The proofs above are safety properties. That a message is eventually delivered is an assumption about the network.

## Unverified hypotheses

- primitive-data-restatement: claim: `metacircular` can be restated for a language with one primitive first-order data type by changing the encoding and three dispatch lemmas, without redoing the fixed-point simulation. confidence: medium. verification: none. synthesis path: stage 1. Decides D1.
- parametric-primitives: claim: P8 can be stated so each new primitive adds one local lemma. confidence: medium. verification: none. synthesis path: stage 3.
- interpreter-overhead: claim: P9's bound is a constant times program size times source steps. Variable lookup walks a Church index, so the factor is not a pure constant. confidence: medium. verification: none. synthesis path: stage 3.
- order-free-class: claim: there is a useful class for P16 that a proved checker can recognise. confidence: low. verification: none. synthesis path: stage 6.
- compiled-machine-speed: claim: the step machine compiled by Lean is fast enough to re-execute receipts of practical size. confidence: low. verification: none. synthesis path: stage 2.
