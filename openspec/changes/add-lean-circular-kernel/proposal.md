# add-lean-circular-kernel

> **ACTIVE BUILD**

**Rigor:** instrument

Depends on: `add-language-partition` (folded, `e834845`).

## Why

The partition says the evaluator is Lean 4 source and that the first proof is metacircular. That proof does not exist yet. This change is the executable kernel and that theorem, for one named fragment.

## What

- ADD capability `lean-kernel`
- A Lean 4 package the kernel builds from
- Terms are de Bruijn variable, abstraction, application, and quote
- The pure fragment is every term that contains no quote, including open and diverging terms
- The interpreter-term is `quote interpreterBody`, where the body is one closed pure term. The route projects that payload and evaluates it with `Direct` on the Mogensen–Scott encoding of the program. The body does not call `Direct`
- A theorem: for every pure program and outcome, direct call-by-value evaluation agrees with that route under `Represents`
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

- Upstream: living spec `openspec/specs/language-partition/spec.md` at `e834845`. `ARCHITECTURE.md` names this change as the owner of the metacircular theorem. Spike `lean-c-abi` is `go` for one unboxed call and is not an input to this proof. Astra's send-back is `reviews/2026-11-08-advise.md` at `082b583`.
- Anchors: `language-partition` — eval is Lean 4 source, and circularity is the metacircular equality. This change's `design.md` now names the route and the theorem signature.
- Outcome: still valid. Commit `2df19e2` is the contract Astra accepted in `reviews/2026-11-08-advise-3.md` (`4f3c1f9`). It names call-by-value `Direct`, the Scott encoding, the quote-payload route, `Represents`, `coverage`, and `evalFuel`. Purity is every quote-free term. The accept did not change that contract.
- Authority: the user said `activate` on 2026-11-08 for this dependency-ready node. Bounds stay the pure fragment: variable, abstraction, application, and quote; the theorem covers programs with no quote; one level; no Zig host and no Rust. `add-zig-host` stays blocked.
