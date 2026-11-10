# add-code-as-data

> **PENDING**

**Rigor:** change

Depends on: `add-lean-circular-kernel` (folded). Vision: `add-verifiable-network-vision`, stage 1, decisions D1 and D8, obligations P6, P7, P8a. Spike: `docs/spikes/primitive-data-restatement/finding.md` (`go`).

## Why

The kernel proves that an interpreter written in the language agrees with direct evaluation. It does so with the program encoded by a Lean function that sits beside the language, and only for programs without quote. A program cannot build, hold, or inspect another program.

Everything the vision needs later, from shipping a closure to checking a receipt, treats a program as a value. This change makes that true inside the language and proves the interpreter theorem again in that setting.

## What

- ADD capability `code-as-data`
- A second Lean library in the kernel package, beside `Circular`, with primitive data: natural numbers and arrays
- `lit d` evaluates to `d`. Quoting a program `p` is `lit (reify p)`, where `reify` is total
- `succ`, `cons`, and one case form build data and take it apart
- One closed interpreter term that takes a program as data and answers with the outcome as data
- `reflective`, `reflective_coverage`, `reflective_env`, and `tower`, proved for every term

## Impact

- Capabilities: ADDED `code-as-data` (at fold)
- `lean-kernel`: unchanged. `Circular`, `metacircular`, `coverage`, and the Zig host stay as they are. Moving the host to the new library and retiring the quote-free kernel is a later change
- `ARCHITECTURE.md`: gains a section at fold. For a time the package holds two evaluators, both Lean

## User journey & surfaces

No new UI because the surface is `lake build` and a contract file.

- **Working** — `lake env lean ReflectContract.lean` exits 0 and prints only Lean's standard axioms for the four theorems. The run file shows the interpreter interpreting itself on a program that builds another program.
- **Empty** — today: `encode` is a Lean function and quoted programs are outside the theorem.
- **Failed** — a theorem is stated for a fragment, an outcome is compared through a decoder, or a `sorry` or package axiom appears.
- **Off** — there is no product UI.

## Out of scope

- Bytes, text, maps, or any wire format. Bytes arrive with the parametric statement (P8).
- A primitive `eval`. The interpreter term is the only way to run data in this change.
- The bytecode machine (`add-bytecode-machine`).
- Requests, channels, or any effect.
- Editing `Circular` or the Zig host.

## Preparation

- Upstream: living spec `openspec/specs/lean-kernel/spec.md`. Spike `primitive-data-restatement` is `go`: seventeen programs agree at one and two interpreter levels, and two cases are proved for every payload by reduction.
- Anchors: the spike's definitions of data, terms, outcomes, `evalFuel`, `reify`, and the interpreter are the starting point. The spike did not prove the application case or the reverse direction.
- Outcome: the interpreter theorem holds for every term, with the program passed as its own data form and the answer compared by equality.
- Authority: none yet. This change is PENDING.
