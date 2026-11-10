# move-host-to-reflect

> **PENDING**

**Rigor:** change

Depends on: `add-code-as-data`, `add-bytecode-machine` (both folded, `18339d7`). Vision: `add-verifiable-network-vision`. Fixes bead `homoiconic-3gx`.

## Why

The host still calls the quote-free kernel, takes de Bruijn text, and answers with one 32-bit code that is ambiguous for large indices. The language people should write in is `Reflect`, and it has no way to be written by hand.

## What

- ADD capability `surface-syntax`: an indentation syntax with names, in the manner of Wisp, read by a Lean function into `Reflect` terms
- A plain text rendering of outcomes
- MODIFY `zig-host`: the host passes program text to a new export, which reads it, compiles it, runs the machine under a step budget, and writes the rendering back
- The reader and the renderer are implementation. They are tested and not proved, as the vision decided for wire formats. What runs is the proved machine

## Impact

- Capabilities: ADDED `surface-syntax`; MODIFIED `zig-host` (at fold)
- `lean-kernel` and `Circular` stay until `retire-circular-kernel`, the next change. After this change nothing calls them
- Bead `homoiconic-3gx` closes: there is no result code

## User journey & surfaces

The surface is a program file and the text the host prints.

- **Working** — the host is given the countdown program in `design.md` and prints `0`. Given a quoted program it prints that program's data. Given a program that builds code and interprets it, it prints the outcome.
- **Empty** — today: programs are written as `([0] [0])` and the answer is a number.
- **Failed** — the host prints a result the machine did not produce, a name resolves to the wrong binder, or a malformed program is run instead of refused.
- **Off** — no file given: the host prints usage.

## Out of scope

- Retiring `Circular` (`retire-circular-kernel`).
- CBOR on the wire and dCBOR in the log. Those arrive with messages and the event log.
- A proof about the reader or the renderer.
- Modules, imports, strings, or macros.
- A REPL.

## Preparation

- Upstream: living specs `code-as-data`, `bytecode-machine`, `zig-host`. `machine_exact` is what lets the host run the machine and call the answer the program's outcome.
- Anchors: Zig carries bytes and contains no evaluator and no reader. The reader is Lean.
- Outcome: a person can write a program with names and indentation, run it, and read the answer.
- Authority: the user chose a Wisp-like text syntax and plain rendering on 2026-11-09. The syntax in `design.md` is a proposal and has not been approved. This change is PENDING.
