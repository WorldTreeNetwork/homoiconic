# add-lean-circular-kernel

## Fragment

The named fragment is the pure lambda fragment.

- A term is a variable, an abstraction, an application, or a quote of a term.
- The pure fragment is the terms that contain no quote.
- Values are closures.
- Direct evaluation is a Lean function on pure terms.
- The interpreter-term is a quoted representation of that function, written with quote so the interpreter is data.
- The theorem quantifies only over pure programs. Evaluating the interpreter-term on a pure program equals direct evaluation. Quoted re-entry is outside the theorem. That is one level, not a tower.

## Why this fragment

It is large enough for an interpreter to be a term, and small enough that the equality is one theorem. Numbers, recursion, and effects are later languages.

## Build

The package is Lean 4, built with `lake build`. The theorem is a declaration in that package, not a comment beside it.

## Downstream

`add-zig-host` calls this package. It does not start from this contract. It starts when this kernel exports a callable entry and the host change is activated.
