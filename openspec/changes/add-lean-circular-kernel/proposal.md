# add-lean-circular-kernel

> **ACTIVE BUILD**

**Rigor:** instrument

Depends on: `add-language-partition` (folded, `e834845`).

## Why

The partition says the evaluator is Lean 4 source and that the first proof is metacircular. That proof does not exist yet. This change is the executable kernel and that theorem, for one named fragment.

## What

- ADD capability `lean-kernel`
- A Lean 4 package the kernel builds from
- Terms are variable, abstraction, application, and quote
- The pure fragment is terms that contain no quote
- An interpreter written as a term of the language
- A theorem: on the pure fragment, evaluating that interpreter-term equals direct evaluation
- One level. No reflective tower

## Impact

- Capabilities: ADDED `lean-kernel` (at fold)
- ADRs: none. `ARCHITECTURE.md` already names this change as the owner of the theorem

## User journey & surfaces

No new UI because the surface is `lake build` and the named theorem.

- **Working** — `lake build` succeeds and the theorem checks for a program in the pure fragment.
- **Empty** — there is no Lean package yet.
- **Failed** — the build fails, or the theorem is stated for quoted re-entry.
- **Off** — there is no product UI.

## Out of scope

- The Zig host, initialization, and allocation. Tracked as `add-zig-host`.
- Rust.
- A surface language, module system, editor, compiler, or garbage collector.
- A tower of interpreters.

## Preparation

- Upstream: living spec `openspec/specs/language-partition/spec.md` at `e834845`. `ARCHITECTURE.md` names this change as the owner of the metacircular theorem. Spike `lean-c-abi` is `go` for one unboxed call and is not an input to this proof.
- Anchors: `language-partition` — eval is Lean 4 source.
- Outcome: still valid. The fragment below is the small fragment the partition left unnamed.
- Authority: the user said `activate` on 2026-11-08 for this dependency-ready node. Bounds stay the pure fragment: variable, abstraction, application, and quote; the theorem covers programs with no quote; one level; no Zig host and no Rust. `add-zig-host` stays blocked.
