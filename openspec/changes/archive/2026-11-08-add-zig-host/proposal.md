# add-zig-host

> **ACTIVE BUILD**

**Rigor:** change

Depends on: `add-language-partition` (folded, `e834845`), `add-lean-circular-kernel` (folded, `1060902`).

## Why

The partition says Zig is the host and calls Lean for evaluation. The kernel package proves `metacircular` and `coverage` and exposes `evalFuel` as a Lean function. Nothing in that package yet receives a program from Zig. This change is that call.

## What

- ADD capability `zig-host`
- A Zig test reads one pure program as bytes and prints the kernel's result code
- The Lean package exports `kernel_run`, which parses those bytes and calls `evalFuel` at the empty environment
- The Zig tree loads that export and contains no evaluator
- The link is the object path from `docs/spikes/lean-c-abi/`

## Impact

- Capabilities: ADDED `zig-host` (at fold)
- The kernel theorem requirements stay as folded. This change adds an export beside them
- ADRs: none. `ARCHITECTURE.md` already names this change as the owner of initialization, allocation, and the interpreter ABI

## User journey & surfaces

No new UI because the surface is a Zig test that passes program text and checks the result code.

- **Working** — the identity text `([0] [0])` returns the closure code, and the open variable `0` returns unbound `0`.
- **Empty** — there is no Zig host yet. The kernel package builds and has no interpreter export.
- **Failed** — the Zig sources compute the outcome themselves, or the export returns a code `evalFuel` does not.
- **Off** — there is no product UI.

## Out of scope

- Rust.
- A reflective tower, or a proof that the C call preserves `Direct`.
- `dlopen` and `leanc -shared`. The spike's working path is the object link.
- A surface language, module system, editor, compiler, or garbage collector.
- Changing `metacircular`, `coverage`, or the pure-fragment statement.
- A multi-line session. One program in, one code out.

## Preparation

- Upstream: living specs `openspec/specs/language-partition/spec.md` (`e834845`) and `openspec/specs/lean-kernel/spec.md` (`1060902`). `ARCHITECTURE.md` assigns initialization, allocation, and the interpreter ABI to this change. Spike `lean-c-abi` is `go` for one unboxed call that returned `71`. Spike `lean-runtime-init` is `go` at `7fad594`: object-linking `kernel_run` after the initializer returns the design codes, and the kernel package was not edited. `evalFuel` remains the executable entry and agrees with `Direct` on quote-free terms.
- Anchors: the partition requires the Zig host to call Lean and to contain no evaluator. The kernel spec's executable entry is `evalFuel`. `metacircular` and `coverage` already cover every quote-free term. Quote-as-data stays on `Eval` and is outside this change.
- Outcome: still valid. The runtime spike confirmed this contract. The goal is unchanged: Zig loads the kernel, reads a program, and returns the kernel's result.
- Authority: the user said `activate` on 2026-11-08 for `add-zig-host`. Bounds are this contract: one pure program in, one result code out, object link, runtime initializer, no `dlopen`, no evaluator in the Zig tree, and no edit to `metacircular` or `coverage`. This is not a grant to act in the same breath.
