# Decisions and proof obligations

The decisions (D1–D10), the proof obligations (P1–P21), and what is assumed, behind the vision in [`VISION.md`](VISION.md). What is proved now is in [`PROOFS.md`](PROOFS.md).

This text is the design of the change `add-verifiable-network-vision`, folded on 2026-11-24 and archived at `openspec/changes/archive/2026-11-24-add-verifiable-network-vision/`. It is kept as written, with its dated notes.

> **Written 2026-11-09 against the first kernel, `Circular`, which `retire-circular-kernel` removed on 2026-11-10.** Where this document names `metacircular`, `coverage`, `source_beta`, `interpreterApplication`, `Represents`, `encode` or `kernel_run`, read it as the plan as it stood then. What landed: `reflective` and `reflective_coverage` (P8a), `reflective_env` (P6), `tower` (P7), the machine theorems (P1, P1b, P2, P3), and `reflect_run`. Their exact statements are in `openspec/specs/code-as-data/spec.md` and `openspec/specs/bytecode-machine/spec.md`. P8 landed later on 2026-11-10 as `prim` with an `Ops` table (`add-operation-tables`), and needs no lemma per operation. P10 and P11 landed later on 2026-11-10 in another form (`add-requests`; see Requests below); P12 is open. On 2026-11-11 `add-state-store` delivered the state half of stage 5 (see One VM below); P13 as a fold over an event log, and P14, are open. On 2026-11-12 `add-event-log` met P13 and P14 for one program, with identifiers supplied by the log (see One VM below).

The architecture the vision implies, and the proofs that carry it. Statements are sketches. Each owning change fixes the exact Lean signature and puts it in a `Contract.lean` check the way `metacircular` is.

## Where the floor stands

> This section is the state on 2026-11-09, when the vision was written. `Circular`, `metacircular` and `kernel_run` were replaced by `Reflect`, `reflective` and `reflect_run`, and removed by `retire-circular-kernel` on 2026-11-10.

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

### D1. Data carrier — decided 2026-11-09: primitive data

Decided by the user. Data is a primitive first-order type, not Scott-encoded terms. D7 says which type and which bytes. D8 says how code is a value of it. The comparison below is kept as the record of why.

Data was Scott-encoded lambda terms. The alternative was a primitive first-order type: bytes and pairs, or S-expressions.

| | Scott-encoded | Primitive data |
|---|---|---|
| Kernel size | Smallest | A few more rules |
| Wire format | Must be derived from terms | Is the data |
| Hashing | Over term syntax | Over the data |
| Inspecting code in the language | Only by applying it | By case analysis |
| Existing proof | Stands as is | Restated through P8 |

Primitive data is introduced through the parametric statement P8, with `quote` producing it. Stage 1 opens with a spike that restates `metacircular` for a language with this data type and reports the cost.

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

### D7. Formats come from identikey-protocol; the code that reads them is Lean — relaxed 2026-11-12, confirmed 2026-11-24

> **Relaxed by the user, 2026-11-12, confirmed 2026-11-24.** The data, storage and wire formats may be designed for this system first, and identikey-protocol updated to match where needed. The canonical form is hash-named pieces. Working memory stays Lean's native objects. The starting data subset below is confirmed. The table records where the choices came from, not a constraint to follow identikey-protocol.

Direction from the user, 2026-11-09: reuse identikey-protocol's choices where useful. Source: `identikey-protocol/docs/standards/` and `crates/identikey-log`.

| Need here | identikey-protocol choice | Used for |
|---|---|---|
| Canonical bytes | dCBOR: sorted map keys, smallest-form integers, definite lengths, no floats, re-serialization byte-identical | P4 |
| Hash | Blake3 over canonical bytes, 32 raw bytes | P5 |
| Event record | `identikey-log` op: signed, content-addressed, hybrid logical clock, parent links, opaque dCBOR `body` | P13, P14, D4 |
| Signed container | Gordian Envelope (`#6.200`), signatures on the wrapper, salted elision | Receipts (P20) |
| Authority | Biscuit capability tokens with attenuation | The host's side of P12 |
| Text form | `ur:envelope/…` for a whole envelope; base58 or base64 by size for one value | Host output only |

Boundary, revised 2026-11-09 by the user: the wire format is an implementation detail outside the language and is not proved. The language has an abstract data type (D1) and code is a value of it (D8). That is inside the proofs. How a data value becomes bytes is not. The reader and writer are tested against the identikey-protocol fixtures. That they round-trip, and that the hash has no collisions, are assumptions of the same kind as the toolchain. The op wrapper, signatures, clocks, and tokens are the host's.

What this gives up: "equal hashes mean equal programs" and receipt soundness hold given a correct codec, not unconditionally. The likely codec fault, two byte strings for one value, fails closed: hashes differ and a check is refused.

Constraints this puts on us:

- **No Rust.** The identikey crates are Rust and the partition excludes Rust. We adopt the formats and the committed fixtures as test vectors, not the crates.
- **A strict decoder.** dCBOR rejects non-canonical bytes. The round trip is tested in both directions.
- **Two hashes exist upstream.** The log's identity is Blake3 of canonical bytes. Envelope digests are SHA-256. Code identity here is Blake3, to match the log.
- **Start with a subset.** The language's data type is unsigned integers, byte strings, and arrays. More is added through P8 when something needs it. The wire format can carry more than the language can inspect.
- **Biscuit carries Datalog.** Evaluating a token is evaluation. It stays outside the kernel and outside the theorems until someone decides otherwise.

> **2026-11-11, `add-wire-bytes`:** P4 holds, tested, for data, programs and machine values; not yet for outcomes, whole machine states, or a piece that holds references. The language's numbers have no upper limit. A number of 2^64 or more is written as CBOR tag 2 over its bytes with no leading zero, and only such a number. That is this project's rule: dCBOR's numeric rules cover 64-bit numbers and neither define nor forbid tag 2. The statements are in `openspec/specs/wire-bytes/spec.md`.

### D8. Code is a value of the data type — confirmed by spike 2026-11-09, confirmed by the user 2026-11-24

The spike used flat tags `0`–`5` and a single case form in place of the nested primitive tag sketched below. `add-code-as-data/design.md` (`openspec/changes/archive/2026-11-09-add-code-as-data/design.md`) has the table that stands.

We do not need a new format. We need a schema of a few lines over dCBOR, and its shape has precedent.

```
term = uint                 ; variable, de Bruijn index
     / [0, term, term]      ; application
     / [1, term]            ; lambda
     / [2, data]            ; literal: the data value itself, not evaluated
     / [3, uint, *term]     ; primitive operation
```

The identity function is three bytes: `82 01 00`. The numbering is stage 1's to fix.

What this buys: `quote p` evaluates to the data value that is `p`'s representation. The interpreter takes that value and takes it apart with primitives. The wire form, the hashed form, the quoted form, and the interpreter's input are the same bytes. `encode` stops being a Lean function beside the language and becomes the identity on bytes. The metacircular theorem is restated over that.

Existing work considered:

| | What it is | Take | Leave |
|---|---|---|---|
| Dhall binary | A standard CBOR encoding of lambda terms, hashed after normalization | The shape: bare integer for a variable, labelled arrays for the rest | The language: typed and total |
| Untyped Plutus Core | Untyped lambda calculus with de Bruijn indices, builtins, a CBOR data type, a costed abstract machine, and a formal specification | The design of builtins with a cost each, and a machine with a step budget (P1, P3, P8) | The wire format (bit-oriented, not CBOR) and the builtin set; adopting the language means redoing the central proof for a much larger one |
| Unison | Code identified by the hash of its syntax tree; names are metadata | The principle | Its own format |
| Nock | Code is a tree of numbers; a machine is a function of its event log | The architecture, which matches stages 5 and 6 | Combinators instead of lambda; the existing proof would not carry |
| Binary lambda calculus | Bit encoding of exactly this language | Nothing | No data, not byte-aligned |
| WebAssembly | A specified, mechanized bytecode | A later compile target | Code is not a value in it |

These descriptions are from memory and were not checked against current sources. Stage 1 checks the two it borrows from.

### D9. Speed comes from a small machine and native primitives, not from the canonical form — proposed

Asked 2026-11-09: can code be close to bytecode and run efficiently, perhaps as WebAssembly, without hurting the proof or code-as-data.

The canonical form stays the term (D8). That is what is hashed, quoted, and reasoned about. What runs is derived from it.

- **A stack bytecode in the SECD / ZINC family.** About six instructions: access a variable, build a closure, apply, return, push a literal, call a primitive. Code is a flat array of integers, so it is a dCBOR value too. The unoptimized compile is a postfix flattening of the term and is invertible. This machine is the P1 machine; stage 2 builds it.
- **Compile correctness is one more theorem (P1b).** Running `compile t` gives the outcome `Direct` gives `t`. `metacircular` stays stated on terms and is not touched.
- **Heavy work is primitives.** Hashing, byte operations, big integers, and tensor arithmetic are native code behind P8, each with a cost and a local obligation. The language is the glue. Model inference is a request (D3) or, for fixed-weight integer inference, a primitive.
- **Processor extensions live inside primitives.** Each primitive has a Lean definition, which is its meaning, and may have a native implementation bound with `@[extern]` that uses vector or cryptographic instructions chosen at run time. The rule is the same bits on every processor. Integer vector code, hashing, and cipher instructions meet it. Float vector code does not: fused multiply-add and summation order change results. A primitive's cost is fixed by its definition, not by the processor. That a native implementation equals its Lean definition is a hypothesis per primitive, tested against the definition and exposed by P21, which judges a disputed step with the definition.
- **The machine is written in Lean and compiled by Lean to C.** The C compiler handles the processor. The proof stays about the code that runs.
- **If that is too slow, add an unchecked fast executor, not a trusted one.** It must be able to produce the canonical machine state at a given step count. The reference machine judges it through P21. This would put an evaluator outside Lean and needs a decision against the partition when it comes up.
- **No floats.** Processors differ on float edge cases. dCBOR in this tier already excludes them.

WebAssembly as the language is declined: code is not a value in it, it has no closures, and a self-interpreter and its proof would be far larger than everything here. WebAssembly as packaging is welcome: the compiled kernel can be built for it so a receipt can be checked in a browser.

### D10. Channels are requests; names are identikey's — decided 2026-11-09

Programs communicate in the style of the pi-calculus: channels are values, and a channel can be sent over a channel. The kernel gains nothing for this. `send`, `receive`, `spawn`, and `new` are request operations (D3).

- A channel name is unforgeable because it is an identikey key or capability. The host enforces that. The proofs take it as a hypothesis.
- A fresh name is an answer from the host, recorded like any other answer, so replay (P10) covers it.
- A program can use only the channels it was given or received (P12).
- Delivery order is recorded (D4). Agreement on order between parties is not provided.
- Properties of a particular concurrent algorithm, such as freedom from deadlock, are proved per algorithm, later.

## Proof obligations

Ordered by dependency. "Free" means it follows from earlier results with little new work.

### Machine

| | Statement | Why | Needs |
|---|---|---|---|
| **P1** | `Direct env t o ↔ ∃ n, run n (load env t) = done o` | The thing that runs means what `Direct` says. | — |
| **P1b** | `Direct [] t o ↔ ∃ n, run n (load (compile t)) = done o`, and `decompile (compile t) = t` | The bytecode means what the term means, and is the same information. | P1's machine, D9 |
| **P2** | `run (n + m) s = run m (run n s)` | Pause, resume, checkpoint, slice. | P1's machine |
| **P3** | After `n` steps the state holds at most `c * n + size s₀` cells | A budget bounds memory, not only time. A hostile program cannot exhaust a VM. | P1's machine. Not proved as stated, and false as stated (2026-11-24): one step of `cons` onto a text makes cells without bound, so no `c` exists. `depth_bound` bounds the stack and frames; a tail call keeps no frame (`homoiconic-q59.65`), so a tail loop holds finitely many states (`forever_bounded`). What stands in its place (`add-space-budget`, `homoiconic-q59.67`): a run has a space limit, a second number beside its budget, and it is proved that every state of a space-limited run was reached by steps that made no more cells than the run had left (`trail_held`, `runIn_ledger`, for every table and every count a host supplies). That is a bound on cells made. A bound on cells held, computed from the state, is not proved: the state is a tree and does not say what is held once, and the count that lets a long run go on is the runtime's (`homoiconic-q59.74` for one that is a function of the state). A recursion that waits and a loop that builds now end in the kernel's space outcome on the 512 MiB image instead of out of memory. |

### Bytes

| | Statement | Why | Needs |
|---|---|---|---|
| **P4** | *Assumed, tested.* The dCBOR reader and writer round-trip in both directions for data, terms, values, outcomes, and machine states | One canonical form. Not proved, by decision (D7). | D7, D8 |
| **P5** | *Assumed.* The hash has no collisions on the values in play | A hash names a program. | P4, D5 |

### Wider language

| | Statement | Why | Needs |
|---|---|---|---|
| **P6** | `metacircular` at an arbitrary pure environment | A shipped closure is never at `[]`. The internal lemma `source_beta` already carries an environment. | — |
| **P7** | For every depth `k`, the interpreter interpreting itself `k` times agrees with `Direct`. **Free:** `interpreterApplication` is pure, so `metacircular` applies to it; induct on `k` and compose `Represents`. | Rules can be stacked: a metering interpreter under a tracing one. | P6 helps |
| **P8a** | With primitive data, a case primitive, and `quote` evaluating to a program's data value: for every program `p`, including programs that use `quote`, `Direct env p o ↔` the interpreter applied to `quote p` derives a value that is the data form of `o` | Code-as-data inside the language. `encode` is no longer a Lean function beside it. The quote-free restriction ends. | D1, D8 |
| **P8** | For a signature of primitives, each with a rule and an object-level implementation satisfying one local lemma, `metacircular` holds for the extended language | Adding numbers or bytes costs one lemma each, not a new 785-line simulation. | D1 |
| **P9** | The interpreter's step count is bounded by a stated function of the program's step count and size | A step budget means something at every interpreter depth. | P1 |

### Requests

> **2026-11-10, `add-requests`:** P10 and P11 are met in a different form from the one below. A request is a value, not a new outcome: `ask payload next` is a function that holds a payload and the rest of the program, and the driver that answers it is outside evaluation. P10 is `interact_deterministic`, and P11 is `interact_reflective` and `interact_coverage` (the interpreter on data), with `interact_machine` for the machine. A request carries no mark, so the driver reads every function a turn ends in as a request. The statements are in `openspec/specs/requests/spec.md`. P12 is still open: a payload is data, and nothing yet stops a program from naming what it was not handed.

> **2026-11-12, `add-channels`:** P12 is met for channel names inside one machine. Four payload shapes are channel requests (new, send, receive, start), and a process can send or receive only on a name it holds: `Step.comm_held`, `Step.held_from` and `Network.held_issued`, for every table. Holding is kept by the scheduler. When this landed a name was a number, so a process could write any name; it could not use one it did not hold. Since `add-data-kinds` (2026-11-17) a name is its own kind of data, `Data.name`: a plain number no longer hands one over, the reader does not read `#`, and no operation makes a name (`openspec/changes/archive/2026-11-17-add-data-kinds/`). A name is still not an identikey key. A fresh name is an event of the schedule, as D10 says. P12 for every requested operation, including requests to the outside, is still open. The statements are in `openspec/specs/channels/spec.md`.

| | Statement | Why | Needs |
|---|---|---|---|
| **P10** | With a `request op payload k` outcome: the final outcome and the request trace are a function of the code and the list of answers | Replay. This is `direct_deterministic` lifted to interactive programs. | P1, P2 |
| **P11** | The interpreter run on `encode p` emits a request trace that represents `p`'s trace, answer by answer | `metacircular` lifted from outcomes to traces. An interpreter that adds a rule does not change what the program asks for. | P10, P6 |
| **P12** | Every `op` a program requests is reachable from the environment it started with | A program cannot reach an effect it was not handed. | P10 |

### One VM

> **2026-11-11, `add-state-store`:** the state half of stage 5 is met, and P13 and P14 are not. A machine state can be cut into pieces held in a store under references, at any step, and continued by a lazy machine that fetches a piece when a step first looks at it and pauses when the store lacks it. It is proved that the continued run gives what the plain machine gives (`lazy_simulates`, `lazy_complete`, `lazy_sound`), so a snapshot can be taken at any step and continued. A waiting run of the request driver can be kept and continued from its root (`lazy_turn_complete`, `lazy_turn_sound`). The kind of reference is a parameter; that a reference names one piece is a stated hypothesis, which is D5's in another form. For stage 6, a closure or a paused machine can now travel as a root and the pieces it reaches. What is still needed is the byte form of a piece (P4, `add-wire-bytes`), references made by hashing (P5), and moving pieces between VMs; P15 is not proved. P13 as `foldl handle init log` over an event log, and P14, remain. The statements are in `openspec/specs/state-store/spec.md`.

> **2026-11-12, `add-kept-state`:** references are now Blake3 hashes of a piece's bytes, computed by a Lean definition (`Wire.Blake3.hash`), and a piece has a byte form. A waiting program is kept on disk, one file per piece, and answered in a later process (`host/out/keep`). Per D5, that two pieces do not share a hash is assumed; no theorem states it and no axiom is added. The hash, the byte form and the session are tested, not proved. P13 as a fold over an event log, and P14, are still to come. The statements are in `openspec/specs/wire-bytes/spec.md`, `openspec/specs/state-store/spec.md` and `openspec/specs/zig-host/spec.md`.

> **2026-11-12, `add-event-log`:** P13 and P14 are met for one program. A VM is a program run by the request driver plus the identifiers of the log entries it has acted on, and its state is the fold of a handler over a log of `[identifier, answer]` entries (`log_deterministic`, `log_prefix`; the executable `vmRun` is `List.foldl`). An entry already in the log changes nothing (`log_again`, `log_redeliver`, `log_once`), and a kept state handed its whole log reaches what the log reaches from the start (`log_restart`). P14 was planned to need P5; it does not, because an identifier is data the log supplies, not a hash made here. That is the open part: identifiers are not content hashes, nothing is signed, and the entry is not an identikey-log op. A VM is one program, not a set of processes. That a restarted state has the same root is tested, not proved. The statements are in `openspec/specs/event-log/spec.md`.

> **2026-11-17, `seal-log-entries`:** an entry's identifier is now the Blake3 hash of the entry, computed by the kernel; a log supplies a mark and an answer. Two sealed entries with one identifier are one entry (`sealed_same`, `sealed_op_same`), under the hypothesis that the naming function gives different names to different data. Nothing is signed and an entry does not name the one before it; the mark is where both will go.

> **2026-11-18, Duke:** the host owns signature checks. That check is a mechanical validity operation and stays out of the kernel. The kernel reads the parent link, and the order if it lives in the entry, from the mark. Proofs take a valid signature as a hypothesis. A compact record of entries acted on still waits until the hash chain cannot cycle. `homoiconic-q59.42` stays open for that design and is not implemented here.

| | Statement | Why | Needs |
|---|---|---|---|
| **P13** | `state log = foldl handle init log`, and the running VM's state equals it after any prefix | The log is the truth. A snapshot is a prefix. | P10 |
| **P14** | Handling an event whose identifier is already in the log leaves the state unchanged | At-least-once delivery behaves as exactly-once. | P13, P5 |

### Network

> **2026-11-12, `add-channels`:** P17 is met for one machine as `network_deterministic`: a program and a schedule lead to at most one configuration, for every table. The schedule holds the new names and the answers from outside, so it is the whole record. This is uniqueness only: it does not say a schedule can happen or that a run makes progress. The machine runs a schedule as direct evaluation does (`network_machine`, `network_machine_exact`). The interpreter on data is not covered for schedules, P13 and P16 are not touched, and nothing here is about more than one machine. The statements are in `openspec/specs/channels/spec.md`.

> **2026-11-12, `add-logged-processes`:** inside one machine, the schedule is now a log. An op is a scheduler event with an identifier, and a node is a set of processes plus the identifiers it has acted on; P13, P14 and P17 hold of it together (`node_deterministic`, `node_again`, `node_restart`), and its processes are where the schedule of first deliveries leads (`node_network`), so P12 for channel names holds of a node. A node is kept under one root and restarted from it. An op that cannot happen stops the log. Still one machine: nothing is about two nodes, identifiers are supplied by the log, and nothing chooses events. The statements are in `openspec/specs/logged-processes/spec.md`.

> **2026-11-25, `add-recorded-crossing`, `harden-crossing`, `homoiconic-q59.68`:** P17 now reaches two machines, for one program on two guests. Each guest records what it did, and the check combines the two logs into one schedule of the one-machine network and replays it. A record the check accepts is a run of that network (`accepted_network`), so `network_deterministic` holds of it: the configuration is a function of the program and the recorded schedule. Of two guests that follow `Surface.Cross` it is proved that, where nothing is in flight and once `a` has begun the program it was given, their logs combine, the merge and the replay accept them, and what the replay reaches is, guest by guest and place by place, the processes the guests hold (`honest_combine`, `honest_accept`); a guest that has run anything runs with the other's budgets (`honest_budget`); and the merge finds a schedule whenever the table allows one (`combine_complete`). So for two guests that follow the protocol the record replays to the state they hold. For a guest that does not, the design of `harden-crossing`, D-3, still says what it can hand over. This is also what the second half of P15 asks, in the form D4 allows: a start or a send taken on the other guest leads where the one-machine run of the same recorded schedule leads. It is not the run of any other schedule, since delivery order is an input. P15 is not met as stated. Its first half (`run n (parse (print s)) = run n s`) and that a batch's bytes read back are tested (P4), not proved; the theorems are about a model of the two guests (`kernel/Surface/CrossModel.lean`) in which a batch is taken as the data it was made from. Also not proved: that two guests that have closed have nothing in flight, which rests on one exchange at a time and on an idle guest having no step left (`homoiconic-q59.85`); that the check's ledger walk accepts an honest pair (`homoiconic-q59.86`); that a record's text reads back (`homoiconic-q59.87`). Hypotheses, as before: a guest runs the Lean it claims to, a name is not forged across machines, the hash has no collisions (D5), and a batch a guest takes is one the other made. P16 is not touched. Two guests only (`homoiconic-q59.83`). The statements are in `openspec/specs/crossing/spec.md`, `kernel/CrossingContract.lean` and `kernel/GuestContract.lean`.

| | Statement | Why | Needs |
|---|---|---|---|
| **P15** | `run n (parse (print s)) = run n s`, and: a request answered by sending a closure to another VM, running it, and returning the bytes gives the outcome of running it locally. **Mostly free** from P4, P2, P6. | Location does not change meaning. | P4, P2, P6 |
| **P16** | *Future work.* For a named class of handlers, the final configuration is the same for every delivery schedule | Some programs need no ordering. Not on the roadmap. | P13 |
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

- primitive-data-restatement: claim: `metacircular` can be restated for a language with one primitive first-order data type by changing the encoding and three dispatch lemmas, without redoing the fixed-point simulation. confidence: medium. verification: empirically-tested. synthesis path: add-code-as-data. spike-artifact: docs/spikes/primitive-data-restatement/finding.md. Validated by spike primitive-data-restatement on 2026-11-09. — go, with a correction: the restatement works and is simpler, but the simulation is redone, not kept.
- lean-dcbor-subset: claim: a Lean reader and writer for the D7 subset reproduces the identikey-protocol fixtures byte for byte. confidence: high. verification: none. synthesis path: stage 1. 2026-11-11, `add-wire-bytes`: still open. The reader and writer landed for numbers and arrays, but the claim could not be checked: the identikey fixtures (`crates/identikey-log/tests/fixtures`) are Gordian envelopes of maps, text and byte strings, which `Data` lacks. RFC 8949 appendix A was used as the test vectors instead. The claim can be checked once `Data` has byte strings and the log op is read (stage 5).
- parametric-primitives: claim: P8 can be stated so each new primitive adds one local lemma. confidence: medium. verification: none. synthesis path: stage 3.
- interpreter-overhead: claim: P9's bound is a constant times program size times source steps. Variable lookup walks a Church index, so the factor is not a pure constant. confidence: medium. verification: none. synthesis path: stage 3.
- order-free-class: claim: there is a useful class for P16 that a proved checker can recognise. confidence: low. verification: none. synthesis path: stage 6.
- compiled-machine-speed: claim: the step machine compiled by Lean is fast enough to re-execute receipts of practical size. confidence: low. verification: none. synthesis path: stage 2.
