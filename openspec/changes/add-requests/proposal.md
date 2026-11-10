# add-requests

> **ACTIVE BUILD**

**Rigor:** change

Depends on: `add-operation-tables` (folded, `e01f6c6`). Vision: `add-verifiable-network-vision`, stage 4, obligations P10 and P11. Authority: the user said `go` on 2026-11-10 to opening the requests change, and "do it" while it was being built.

## Why

A program runs to an answer and cannot talk to anything. A model call, a message from another VM, a clock and a fresh channel name all need the same thing: a program that stops with a question and continues from the answer. The answer comes from outside and is recorded, so the evaluator stays deterministic (vision D3).

## What

- A **request** is an ordinary value: a function that holds a payload and the rest of the program. `ask payload next` builds one. `ask` is a closed term of the existing language. No term, value, outcome, evaluation rule, interpreter branch or machine instruction is added
- A **driver** outside the program runs it against a list of answers. A turn that ends in data or an error ends the run. A turn that ends in a function is a request: the driver reads its payload, which must be data, and runs the rest of the program on the next answer. With no answer left the run is **waiting**
- The driver is defined once, over any way of evaluating, and used three times: on direct evaluation (`Interact`), through the interpreter on data (`InteractI`), and on the machine (`InteractM`)
- An executable driver, `converse`, runs the machine with a step budget for each turn
- The surface syntax resolves `ask` as a built-in name
- The host gains an export, `reflect_converse`, and a command, `host/out/ask <program-file> <answers-file> [step-budget]`

## What is proved

For every operation table, with Lean's standard axioms only. Exact statements: `kernel/RequestContract.lean`.

| Theorem | Says |
|---|---|
| `interact_deterministic` | The requests a program makes and how it ends are fixed by the program and the answers. This is P10 |
| `interact_resume` | A waiting program continued with an answer is the program run from the start with that answer added |
| `interact_extra` | A program that finished is not changed by more answers |
| `interact_reflective`, `interact_coverage` | The interpreter, driven on data, makes the same requests in the same order and ends the same way. This is P11 |
| `interact_machine`, `interact_machine_exact` | The machine makes the same requests and ends the same way |
| `converse_finished`, `converse_waiting` | What the executable driver reports is a run of the program by direct evaluation |

No existing definition or theorem changes.

## How this differs from the vision

The vision wrote P10 "with a `request op payload k` outcome", a new kind of outcome. This change does not add one. A request is a value the program returns, and the driver sits outside evaluation. The reasons:

- A new outcome would have to pass through every evaluation rule and collect the rest of the program as it goes. That reopens every proof and puts the same bookkeeping into the interpreter. As a value, a request needs nothing from the kernel, which is what decision D10 asked of channels.
- The cost is the style of the program. A request is made at the end of a turn, with the rest of the program passed as a function. A function deep inside a computation cannot ask and then return to its caller; it has to be written to pass its continuation. Syntax that hides this is not in this change.

## Not in this change

- **P12**, that a program can only reach what it was handed. A payload is data, and a program can build any data. What stops a program from naming a channel it was not given is that names are unguessable keys, which is identikey's, on the host side (D10).
- **Meaning of a payload.** Nothing here says what a payload is for. `send`, `receive`, `spawn`, a model call and their payload formats are later changes.
- **A stored paused run.** The `ask` command replays from the start with the whole answers file each time. `interact_resume` is the theorem that keeping the paused run instead gives the same result; storing it needs the wire format.
- **Completeness of the executable driver.** `converse` is proved sound: what it reports is true. That every run is reported for some budget is not proved.
- **Syntax for sequencing requests**, an event log, more than one VM.
- **A step budget for the whole run.** The budget is for each turn.

## Impact

- Capabilities: ADDED `requests`. ADDED requirement in `surface-syntax`. MODIFIED two requirements and ADDED one in `zig-host`: `reflect_run` is no longer the only export that evaluates
- New files: `kernel/Reflect/Request.lean`, `kernel/Reflect/RequestProof.lean`, `kernel/RequestContract.lean`, `host/ask.zig`, `examples/ask.hom`, `examples/ask.answers`, `examples/ask-one.answers`
- `ARCHITECTURE.md`, `kernel/README.md`, `host/README.md`, `docs/PROOFS.md`: amended at fold
- Vision: P10 and P11 are met in this form; P12 stays open; noted at fold

## User journey & surfaces

The surface is program text, an answers file and the command line.

- **Working** — `host/out/ask examples/ask.hom examples/ask.answers` prints `asked: [1]`, `asked: [2, 20]`, `42`.
- **Waiting** — with `examples/ask-one.answers`, which holds one answer, it prints the two `asked:` lines and then `waiting`.
- **Empty** — a program that asks nothing prints what `run` prints for it.
- **Failed** — the same program and answers give different requests directly, interpreted, or on the machine; or the command reports a request the program did not make.
- **Off** — a program that ends in a function that is not a request prints `error: wrong`.

## Out of scope

Listed under "Not in this change".
