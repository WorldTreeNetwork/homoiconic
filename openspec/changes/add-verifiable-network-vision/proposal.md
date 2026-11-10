# add-verifiable-network-vision

> **PENDING**

**Rigor:** vision. This change holds the project vision and the roadmap. It adds no behavior and no spec delta. Each roadmap stage lands as its own change.

Depends on: `add-language-partition`, `add-lean-circular-kernel`, `add-zig-host` (all folded).

Sections marked *(inferred)* were written from the code and one conversation, not from an interview. Correct them before this is treated as settled.

## Why

### Executive summary

Homoiconic is a small language whose programs are data, with a kernel whose behavior is proved in Lean. The goal is a network of virtual machines that pass programs and events to each other, where anyone can check what any machine computed without trusting the machine that ran it. Some of that computation is exact. Some of it is a model call. The system says which is which, and proves everything it can about both.

### Problem statement

Distributed programs are hard to trust for three reasons.

- **The code that runs is not the code that was reasoned about.** A specification sits beside an implementation and the two drift.
- **Moving a computation changes it.** Serialization, a different runtime, a retry, or a reordered message can each change a result, and nothing says they cannot.
- **Model calls are opaque.** A neural network or an LLM returns an answer that cannot be re-derived. Systems that use one tend to lose the ability to say anything exact about the rest of the program.

The usual answer is to trust the operator. Whoever runs the machine tells you what happened. That works until the operator is wrong, compromised, or has a reason to lie.

### Core insight

If a program is a value, then everything a distributed system does to a computation is an operation on a value: send it, store it, hash it, pause it, resume it elsewhere, replay it, hand it to an interpreter that adds a rule. Each of those can be stated as a theorem about one evaluator.

The first theorem is in place. `metacircular` says an interpreter written in the language agrees with direct evaluation on every quote-free program. That shows the language can hold and run its own programs, and that the proof is about the code that executes.

The second half of the insight is about model calls. A model call does not have to be inside the semantics. It can be a request the program makes and an answer it receives. Then the program is exact relative to the answers it was given. The answers are recorded. Everything downstream of them can be replayed and checked, and the program can be proved correct for every answer that passes a check it runs itself.

### Target users *(inferred)*

- **People building systems across machines they do not all control.** They need a result they can check, not a result they are told.
- **People putting model calls inside programs that matter.** They need to know which outputs depend on the model and what holds regardless of what the model says.
- **Someone who receives a result and wants to verify it later, alone.** They hold a receipt and a copy of the kernel. They need nothing else.

## What

### Proposed solution

Four layers, each resting on the one before.

1. **A proved kernel.** One evaluator, in Lean. It runs as a machine that can stop after any number of steps and continue from where it stopped. Programs, values, and paused machines have one canonical byte form.
2. **An event-driven virtual machine.** A VM is the kernel plus a log. Each event is handled by a program. A program that needs something from outside makes a request and waits for the answer. The VM's state is what you get by replaying its log.
3. **A network.** VMs send each other events, closures, and paused computations. Running something remotely gives the same result as running it locally. Where message order can change a result, the order is recorded as an input.
4. **Receipts.** A receipt names the code, the inputs, the answers received, the number of steps, and the output. Anyone can check one by running the kernel. Two parties who disagree can find the single step where they differ.

Model calls live in layer 2 as requests. The model is outside the proof. The program's use of the answer is inside it.

### Key differentiators

- **One evaluator.** The host does not contain a second copy of the semantics. Later layers must keep this: the network and the log are Lean definitions, and the host carries bytes.
- **New rules arrive as data.** Metering, tracing, and sandboxing can be interpreters written in the language. The metacircular theorem is what makes an interpreter a safe place to put a rule.
- **Exact and inexact computation are separated by a theorem.** An output is either independent of every model answer or it is labelled as depending on one.
- **Checking needs no permission.** Verification is re-execution of a small kernel on public bytes.

### What this is not

- Not a blockchain. There is no token and no global ledger. Ordering is an input that some other mechanism may supply.
- Not a proof that a model is correct, honest, or was the model that was claimed. Those are assumptions, named as such.
- Not a general-purpose language yet. It has variables, functions, and calls.
- Not a verified compiler. The Lean compiler and the C toolchain are trusted.
- Not a second runtime in Zig or Rust for speed. If the kernel is too slow, the answer is a proved refinement, not a rewrite.

### Anti-vision: how we lose the plot *(inferred)*

- The host grows an `eval`, a scheduler rule, or a serialization rule that Lean does not define.
- A theorem is stated about a model of the system while the running code is something else.
- A model answer flows into an output with no label and no check.
- "Verified" starts to mean "tests pass" or "the operator signed it."
- Checking a result requires an account, a service, or someone's approval.
- The language grows features faster than the theorems that cover them.
- A roadmap stage is called done without a named theorem and something that runs.

### Roadmap

Each stage is one or more changes. A stage is done when its theorems are checked by Lean with no admitted steps and its demonstration runs. The proof obligations are stated in `design.md`.

Two tracks. The spine pushes the metacircular theorem as far as it goes, because every later stage rests on it and it is the largest risk. The machine track is textbook work that can run beside it.

| Stage | Track | Name | What lands | Demonstration | Proofs |
|---|---|---|---|---|---|
| 0 | — | Floor | The metacircular theorem and the Zig call. **Done.** | `sh host/check.sh` | — |
| 1 | Spine | Code is data | Primitive data in the language. `quote` gives a program as data. The interpreter takes that data. The theorem covers programs that use quote, at any environment and any interpreter depth. | The interpreter runs itself running a program that builds and runs another program. | P6, P7, P8a |
| 2 | Machine | Bytecode | A stack machine that agrees with `Direct`, pauses and resumes, and has a step and space budget. A speed measurement. | A long program run in three slices gives the outcome of one run. | P1, P1b, P2, P3 |
| 3 | Spine | Primitives | New primitives added through one parametric statement, with native implementations. | Arithmetic and hashing on bytes, interpreted and direct, agree. | P8, P9 |
| 4 | Spine | Requests and channels | Programs make requests and continue from answers. Send, receive, spawn, and fresh name are requests. The interpreter preserves what a program asks for. | Two processes exchange a channel name and then talk over it; replaying the recorded answers gives the same outcome. | P10, P11, P12 |
| 5 | Join | One VM | A VM whose state is a replay of its event log. Events are identikey-log ops. | Kill the VM, restart from the log, and the state hash is unchanged. | P13, P14 |
| 6 | Join | Two VMs | Closures and paused machines move between VMs. Delivery order is recorded. | A computation starts on one VM and finishes on another with the same receipt as a local run. | P15, P17 |
| 7 | Join | Model calls | Requests answered by a model. Outputs labelled by dependence. Checked use of answers. | A program takes a model's proposal, checks it, and the receipt shows which outputs depended on the model. | P18, P19 |
| 8 | Join | Receipts | Receipt checking and dispute by bisection. | A wrong receipt is rejected, and a dispute over a million steps is settled by checking one. | P20, P21 |

Stages 1 and 2 start together. Stage 4 needs stages 1 and 2. Stage 8's receipt check for plain programs (P20) can land any time after stage 1.

### Success

- A stranger with the kernel and a receipt can confirm a result computed across several machines, including which parts depended on a model.
- Adding a language feature costs one local proof, not a rewrite of the central one.
- Nobody on the project can say what the system does without pointing at a Lean definition.

## Impact

- Capabilities: none added by this change. Each stage adds its own.
- `ARCHITECTURE.md`: unchanged by this change. Stage 1 and stage 2 will extend it.
- Living specs: unchanged.

## User journey & surfaces

No new UI because this change is a vision and a roadmap.

## Out of scope

- Any implementation. This change does not edit `kernel/` or `host/`.
- Choosing a consensus or ordering mechanism. Agreement on order is not part of this system. Tools for it may come later.
- Proofs about particular concurrent algorithms. Those are future work, one algorithm at a time.
- A proved wire format. dCBOR and the identikey formats are implementation, tested and not proved.
- Choosing how model execution is attested.
- A surface syntax, module system, or editor.

## Changelog

### 2026-11-09 (third entry)

- Direction from the user: the wire format is an implementation detail and is not proved; channel-style programming is in, with unforgeability resting on identikey; proofs of concurrent algorithms and consensus are out. Roadmap reordered into a spine that pushes metacircularity first and a machine track beside it.

### 2026-11-09 (second entry)

- D1 decided: primitive data. Added D7 (formats from identikey-protocol: dCBOR, Blake3, the log op, envelopes) and D8 (code as a dCBOR value, proposed). P4 restated over dCBOR in both directions.

### 2026-11-09

- Created from a reading of the kernel, the proofs, and the host, and from the stated goal: an event-oriented network of VMs running verifiable programs that include deterministic and non-deterministic compute.
