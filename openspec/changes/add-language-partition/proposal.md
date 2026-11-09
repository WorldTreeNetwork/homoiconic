# add-language-partition

> **ACTIVE BUILD**

**Rigor:** architecture

Depends on: none.

## Why

The circular evaluator has to live in one language, or the proof is about a model that the running program can drift away from. Lean 4 is that language. Zig is the process around it. Rust is a second type system and does not discharge Lean theorems, so it is not in the first system.

## What

- ADD capability `language-partition`
- The evaluator is Lean 4 source. Theorems about evaluation are theorems about that source.
- Zig owns IO, allocation, and the REPL. It calls the Lean kernel and contains no evaluator.
- The kernel's later acceptance is metacircular: an interpreter written as a term of the language, proved equal to direct evaluation on a small fragment.
- Rust is absent.
- An ADR in `ARCHITECTURE.md` records this split. The text is in `design.md`. The file is owed after advise accepts.

## Impact

- Capabilities: ADDED `language-partition` (at fold)
- ADRs: will amend `ARCHITECTURE.md` after advise accept

## User journey & surfaces

No new UI because the surface is `openspec/specs/language-partition/spec.md` and `ARCHITECTURE.md`.

- **Working** — a reader asks which language defines `eval`. The answer is Lean 4, and Zig is only the host.
- **Empty** — the tree has no Lean package and no Zig host yet. This change names the split. It does not build either.
- **Failed** — a second evaluator appears in Zig, or a Rust crate enters the build. The partition is then false.
- **Off** — there is no product UI to turn off.

## Out of scope

- The Lean kernel and its metacircular theorem. Tracked as `add-lean-circular-kernel`.
- The Zig host and the C ABI call. Tracked as `add-zig-host`.
- A Rust memory component. Dropped with this partition.
- A surface language, module system, editor, compiler, garbage collector, or package manager.

## Preparation

- Upstream: no product commits, no living spec, no `docs/LEARNINGS.md`. The steered chat DAG (2026-11-08) is the input.
- Anchors: none. The directory was empty.
- Outcome: still valid. This contract matches the two decisions already made: Lean kernel with a Zig host, and a metacircular theorem.
- Authority: the user said `activate` on intention `homoiconic-circular`. Bounds: Lean 4 is the only semantics language; Zig is the only host and contains no `eval`; the first proof is metacircular equality on a small fragment; Rust stays out. Non-goals stay the ones in Out of scope. This grant activates this dependency-ready node only. It does not activate `add-lean-circular-kernel` or `add-zig-host`.
