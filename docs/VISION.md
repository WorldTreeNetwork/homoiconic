# Vision

The project vision and the roadmap. Each roadmap stage lands as its own change. The decisions (D1–D10) and the proof obligations (P1–P21) are in [`DECISIONS.md`](DECISIONS.md). What is proved now is in [`PROOFS.md`](PROOFS.md); how the system is shaped is in [`../ARCHITECTURE.md`](../ARCHITECTURE.md).

This text is the proposal of the change `add-verifiable-network-vision`, folded on 2026-11-24. The change's bookkeeping (banner, impact, surfaces, tasks) is in its archive, `openspec/changes/archive/2026-11-24-add-verifiable-network-vision/`. The text below is as the user reviewed it, except that the roadmap has a status column.

The target users and the anti-vision were first written from the code and one conversation. The user reviewed them on 2026-11-24 and added the fourth target user.

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

The first theorem is in place. `reflective` says an interpreter written in the language, given a program as data, agrees with direct evaluation on every program. (When this was written the theorem was `metacircular`, for quote-free programs only; `Reflect` replaced it.) That shows the language can hold and run its own programs, and that the proof is about the code that executes.

The second half of the insight is about model calls. A model call does not have to be inside the semantics. It can be a request the program makes and an answer it receives. Then the program is exact relative to the answers it was given. The answers are recorded. Everything downstream of them can be replayed and checked, and the program can be proved correct for every answer that passes a check it runs itself.

### Target users

- **People building systems across machines they do not all control.** They need a result they can check, not a result they are told.
- **People putting model calls inside programs that matter.** They need to know which outputs depend on the model and what holds regardless of what the model says.
- **Someone who receives a result and wants to verify it later, alone.** They hold a receipt and a copy of the kernel. They need nothing else.
- **People computing together across ownership boundaries.** Many machines with different owners cooperate on one massively parallel computation, under rules about how that happens: reciprocity, permissions that can be delegated, capability tokens. Verifiability is one use; cooperation at scale is the other. The process calculus the channels already follow fits this, and interaction nets are a candidate model for the parallel evaluation. (Added by the user, 2026-11-24. No roadmap stage covers interaction nets, reciprocity or delegation yet.)

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

### Anti-vision: how we lose the plot

- The host grows an `eval`, a scheduler rule, or a serialization rule that Lean does not define.
- A theorem is stated about a model of the system while the running code is something else.
- A model answer flows into an output with no label and no check.
- "Verified" starts to mean "tests pass" or "the operator signed it."
- Checking a result requires an account, a service, or someone's approval.
- The language grows features faster than the theorems that cover them.
- A roadmap stage is called done without a named theorem and something that runs.

### Roadmap

Each stage is one or more changes. A stage is done when its theorems are checked by Lean with no admitted steps and its demonstration runs. The proof obligations are stated in [`DECISIONS.md`](DECISIONS.md).

Two tracks. The spine pushes the metacircular theorem as far as it goes, because every later stage rests on it and it is the largest risk. The machine track is textbook work that can run beside it.

Statuses as of 2026-11-24, brought up to date at the fold from the git history, `docs/PROOFS.md` and the beads. Each names the commit or bead that shows it. The stages are as the user reviewed them.

| Stage | Track | Name | What lands | Demonstration | Proofs | Status |
|---|---|---|---|---|---|---|
| 0 | — | Floor | The metacircular theorem for quote-free programs and the Zig call. **Done, then replaced by stages 1 and 2.** | `sh host/check.sh` | — | Done, then replaced: `retire-circular-kernel` removed the first kernel (`c16513d`). |
| 1 | Spine | Code is data | Primitive data in the language. `quote` gives a program as data. The interpreter takes that data. The theorem covers programs that use quote, at any environment and any interpreter depth. | The interpreter runs itself running a program that builds and runs another program. | P6, P7, P8a | Done. `add-code-as-data`, folded in `18339d7` (`homoiconic-q59.1`): `reflective` and `reflective_coverage` (P8a), `reflective_env` (P6), `tower` (P7). |
| 2 | Machine | Bytecode | A stack machine that agrees with `Direct`, pauses and resumes, and has a step and space budget. A speed measurement. | A long program run in three slices gives the outcome of one run. | P1, P1b, P2, P3 | Done, with P3 weaker than stated. `add-bytecode-machine`, folded in `18339d7` (`homoiconic-q59.2`): P1, P1b, P2. P3 landed as `depth_bound`, which bounds stack and frame depth, not the heap. Speed: about 34 million machine steps per second (`docs/PROOFS.md`). |
| 3 | Spine | Primitives | New primitives added through one parametric statement, with native implementations. | Arithmetic and hashing on bytes, interpreted and direct, agree. | P8, P9 | Partly done. P8: `add-operation-tables`, `e01f6c6`; a new operation needs no lemma. A cost per operation, charged by every budgeted run: `homoiconic-q59.9`, `homoiconic-q59.52` (`c25766d`). Open: bytes and hashing as operations, native implementations (`homoiconic-q59.20`), P9. |
| 4 | Spine | Requests and channels | Programs make requests and continue from answers. Send, receive, spawn, and fresh name are requests. The interpreter preserves what a program asks for. | Two processes exchange a channel name and then talk over it; replaying the recorded answers gives the same outcome. | P10, P11, P12 | Done inside one machine; P12 for requests to the outside is open. P10, P11: `add-requests`, `eeb3706`. Send, receive, start and new as requests, the demonstration, and P12 for channel names: `add-channels`, `ddbc076`; a name is its own kind of data since `add-data-kinds`, `5539df4`. |
| 5 | Join | One VM | A VM whose state is a replay of its event log. Events are identikey-log ops. | Kill the VM, restart from the log, and the state hash is unchanged. | P13, P14 | Done, except that an event is not an identikey-log op. P13, P14 for one program: `add-event-log`, `65ed13c`; for a node of processes: `add-logged-processes`, `7383928`. Restart from the log: `log_restart`; equal states saved under one root: `homoiconic-q59.29` (`aa2ab1a`). An entry is named by its Blake3 hash (`seal-log-entries`, `4f91779`) and names the entry before it; the host checks its signature (`homoiconic-q59.42`, `0d48980`). |
| 6 | Join | Two VMs | Closures and paused machines move between VMs. Delivery order is recorded. | A computation starts on one VM and finishes on another with the same receipt as a local run. | P15, P17 | Started. A closure and a reply name cross between two guests over QUIC: `add-unikernel-quic` (`94cb89a`), `add-network-channels` (`246a233`, `homoiconic-q59.16`). P17 holds for one machine (`network_deterministic`, `ddbc076`). Open: the order the two guests delivered in is not recorded and no received schedule is replayed (`homoiconic-q59.51`, in progress); the offer is one program built into Lean; P15 is not proved. |
| 7 | Join | Model calls | Requests answered by a model. Outputs labelled by dependence. Checked use of answers. | A program takes a model's proposal, checks it, and the receipt shows which outputs depended on the model. | P18, P19 | Not started. No change or bead. |
| 8 | Join | Receipts | Receipt checking and dispute by bisection. | A wrong receipt is rejected, and a dispute over a million steps is settled by checking one. | P20, P21 | Not started. No change or bead. |

Stages 1 and 2 start together. Stage 4 needs stages 1 and 2. Stage 8's receipt check for plain programs (P20) can land any time after stage 1.

### Success

- A stranger with the kernel and a receipt can confirm a result computed across several machines, including which parts depended on a model.
- Adding a language feature costs one local proof, not a rewrite of the central one.
- Nobody on the project can say what the system does without pointing at a Lean definition.

## Out of scope

- Choosing a consensus or ordering mechanism. Agreement on order is not part of this system. Tools for it may come later.
- Proofs about particular concurrent algorithms. Those are future work, one algorithm at a time.
- A proved wire format. dCBOR and the identikey formats are implementation, tested and not proved.
- Choosing how model execution is attested.
- A surface syntax, module system, or editor.

## Changelog

### 2026-11-24

The user reviewed the target users and the anti-vision, and added cooperative computation across ownership boundaries as a target use. D8 confirmed. D7 confirmed as relaxed on 2026-11-12: formats may be designed for this system first.

Folded the same day: the proposal became this file and the design became `docs/DECISIONS.md`. The roadmap gained a status column, filled from what had landed.

### 2026-11-11

- The state half of stage 5 landed as `add-state-store`: a running program's state can be cut into pieces held under references, and a snapshot taken at any step can be continued, with the same result, proved. A waiting run can be kept. For stage 6 a closure can travel as a root and its pieces, once pieces have bytes and references are hashes (`add-wire-bytes`). P13 as a fold over an event log, P14 and P15 remain. Annotated in `design.md`.

### 2026-11-10

- Stage 4's P10 and P11 landed as `add-requests`, in the form "a request is a value, the driver is outside evaluation" rather than a `request` outcome. P12, `send`, `receive`, `spawn`, fresh names and the meaning of a payload remain. Annotated in `design.md`.
- Stage 3's parametric statement (P8) landed as `add-operation-tables` for total data-to-data operations, with arithmetic as the first table. Bytes and hashing, a cost per operation, and P9 remain.
- Stages 1 and 2 landed and were folded (`code-as-data`, `bytecode-machine`), with a surface syntax and a host command. The first kernel was removed by `retire-circular-kernel`. The core insight now names `reflective`.

### 2026-11-09 (third entry)

- Direction from the user: the wire format is an implementation detail and is not proved; channel-style programming is in, with unforgeability resting on identikey; proofs of concurrent algorithms and consensus are out. Roadmap reordered into a spine that pushes metacircularity first and a machine track beside it.

### 2026-11-09 (second entry)

- D1 decided: primitive data. Added D7 (formats from identikey-protocol: dCBOR, Blake3, the log op, envelopes) and D8 (code as a dCBOR value, proposed). P4 restated over dCBOR in both directions.

### 2026-11-09

- Created from a reading of the kernel, the proofs, and the host, and from the stated goal: an event-oriented network of VMs running verifiable programs that include deterministic and non-deterministic compute.
