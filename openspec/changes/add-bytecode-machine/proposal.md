# add-bytecode-machine

> **ACTIVE BUILD**

**Rigor:** change

Depends on: the first task of `add-code-as-data` (the `Reflect` definitions). It does not depend on that change's theorems. Vision: `add-verifiable-network-vision`, stage 2, decision D9, obligations P1, P1b, P2, P3.

## Why

`evalFuel` is big-step. It cannot stop partway and continue, its fuel is a height and not a count, and it walks a tree. Pausing, metering, moving a computation, and settling a dispute each need a machine with an explicit state and a step.

## What

- ADD capability `bytecode-machine`
- An instruction set for the `Reflect` language in continuation form, and `compile` from terms to it. Flattening to an array with offsets is a later pass
- A total `step` on an explicit machine state, and `run n`
- `machine_correct` and `machine_exact`: the machine agrees with `Direct`, and what it halts with is exactly the compiled form of the source outcome
- `machine_never_halts`: a term with no derivation never halts
- `run_add`: running `n + m` steps is running `n` then `m`
- `decompile_compile`: the bytecode holds the same information as the term
- `depth_bound`: stack and frame depth grows by at most one per step. A heap bound is not in this change
- A recorded speed measurement of the compiled machine

## Impact

- Capabilities: ADDED `bytecode-machine` (at fold)
- `lean-kernel`, `code-as-data`, and the Zig host are unchanged
- `ARCHITECTURE.md`: gains a section at fold

## User journey & surfaces

No new UI because the surface is `lake build`, a contract file, and a run file.

- **Working** — a long program run as three slices gives the outcome of one run, and the contract file prints only Lean's standard axioms.
- **Empty** — today: evaluation is one call that returns or runs out of fuel.
- **Failed** — the machine disagrees with `Direct` on some term, a pause changes an outcome, or the bytecode cannot be turned back into its term.
- **Off** — there is no product UI.

## Out of scope

- Optimization passes. The compile is the plain postfix translation into continuation-form code.
- A native or Zig executor.
- Serializing machine states to bytes.
- Primitives beyond those in `Reflect`.
- Changing the host to call the machine.

## Preparation

- Upstream: `Reflect.Syntax` and `Reflect.Semantics` from `add-code-as-data`. This change starts when they are merged and frozen.
- Anchors: `Direct` is the meaning. The machine is what runs. Stack machines of this family and their correctness proofs against call-by-value big-step semantics are standard.
- Outcome: a pausable, metered machine proved equal to `Direct`, and a number for how fast it runs.
- Authority: the user said "build them together, then we can retire the old one ... please continue" on 2026-11-09, for `add-code-as-data` and `add-bytecode-machine`. Bounds are this contract. `Circular`, its theorems, and the Zig host are not edited.
