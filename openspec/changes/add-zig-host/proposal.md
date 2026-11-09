# add-zig-host

> **PENDING**

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

- Upstream: living specs `openspec/specs/language-partition/spec.md` (`e834845`) and `openspec/specs/lean-kernel/spec.md` (`1060902`). `ARCHITECTURE.md` assigns initialization, allocation, and the interpreter ABI to this change. Spike `lean-c-abi` is `go` for one unboxed `uint32` call that returned `71`. That call did not run the Lean initializer and did not evaluate a term. `evalFuel` remains a Lean function.
- Anchors: the partition requires the Zig host to call Lean and to contain no evaluator. The kernel spec's executable entry is `evalFuel`, and that entry does not call Zig.
- Outcome: revised. The bead assumed a callable interpreter ABI already existed. The spike showed the link for arithmetic. This contract adds `kernel_run` on that link. The goal is unchanged: Zig loads the kernel, reads a program, and returns the kernel's result.
- Authority: none for this node. The user activated `add-lean-circular-kernel` only. Banner stays `PENDING`.
