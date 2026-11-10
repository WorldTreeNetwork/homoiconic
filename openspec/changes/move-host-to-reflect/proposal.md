# move-host-to-reflect

> **ACTIVE BUILD**

**Rigor:** change

Depends on: `add-code-as-data`, `add-bytecode-machine` (both folded, `18339d7`). Vision: `add-verifiable-network-vision`. Fixes bead `homoiconic-3gx`.

## Why

The host still calls the quote-free kernel, takes de Bruijn text, and answers with one 32-bit code that is ambiguous for large indices. The language people should write in is `Reflect`, and it has no way to be written by hand.

## What

- ADD capability `surface-syntax`: an indentation syntax with names, from the ML family, with quotation and splicing, read by a Lean function into `Reflect` terms
- A plain text rendering of outcomes
- MODIFY `zig-host`: the host passes program text to a new export, which reads it, compiles it, runs the machine under a step budget, and writes the rendering back
- The reader and the renderer are implementation. They are tested and not proved, as the vision decided for wire formats. What runs is the proved machine

## Impact

- Capabilities: ADDED `surface-syntax`; MODIFIED `zig-host` (at fold)
- `lean-kernel` and `Circular` stay until `retire-circular-kernel`, the next change. After this change nothing calls them
- Bead `homoiconic-3gx` closes: there is no result code

## User journey & surfaces

The surface is program text and the text the host check prints. A command that runs a program file is not in this change; it is tracked as a bead.

- **Working** — the host is given the countdown program in `design.md` and prints `0`. Given a quoted program it prints that program's data. Given a program that builds code and interprets it, it prints the outcome.
- **Empty** — today: programs are written as `([0] [0])` and the answer is a number.
- **Failed** — the host prints a result the machine did not produce, a name resolves to the wrong binder, or a malformed program is run instead of refused.
- **Off** — there is no command-line program yet.

## Out of scope

- Retiring `Circular` (`retire-circular-kernel`).
- CBOR on the wire and dCBOR in the log. Those arrive with messages and the event log.
- A proof about the reader or the renderer.
- Modules, imports, strings, macros, nested patterns, or declared constructors. `design.md` lists what comes later and in what order.
- A REPL.

## Preparation

- Upstream: living specs `code-as-data`, `bytecode-machine`, `zig-host`. `machine_exact` is what lets the host run the machine and call the answer the program's outcome.
- Anchors: Zig carries bytes and contains no evaluator and no reader. The reader is Lean.
- Outcome: a person can write a program with names and indentation, run it, and read the answer.
- Authority: the user chose a text syntax and plain rendering, and approved the ML-family syntax in `design.md`, on 2026-11-09. The user said "go" on 2026-11-09 for this change. Bounds are this contract; no file a contract depends on is edited.
