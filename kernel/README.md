# Circular kernel

This package proves `metacircular` and `coverage` for every quote-free
term, including open and diverging programs. `Contract.lean` checks the
exact general signatures and prints their axiom dependencies. Both proofs
use only Lean's standard logical axioms (`propext`, `Classical.choice`, and
`Quot.sound`), with no admissions or package-declared axioms.

Use Lean 4.35.0, pinned in `lean-toolchain`, and run commands from this directory:

```sh
lake build
lake env lean Run.lean
lake env lean Axioms.lean
lake env lean Contract.lean
```

`Axioms.lean` also prints the dependencies of the interpreter omega proof.
`Run.lean` executes both routes on the identity application and open variable,
and the interpreter on the remaining scenarios. Its bounded omega result is
an execution check; `omega_interpreter_no_direct` proves the general absence
of an interpreter derivation.

`Circular.Semantics` defines function-first, call-by-value `Direct`, its
determinism proof, total `evalFuel`, and fuel soundness, monotonicity, and
completeness. Environments contain closures; unbound errors propagate before
unused arguments are evaluated. Quote has no `Direct` rule. `Eval` adds
quotation as data.

`Circular.Encoding` encodes every quote-free term, with no closedness or
normalization restriction. `encode p h` requires the proof `h : Circular.Pure p`.
The encoding is Mogensen–Scott with Church indices and explicit binder shifts.
`Circular.Data` encodes pure outcomes and their captured environments.

`Circular.Interpreter` constructs the interpreter with a name-erasing syntax
builder. The resulting `interpreterBody` is proved pure and closed. Its only
constructors are variables, lambdas, and applications. Recursion uses a
call-by-value fixed-point combinator. Neither the builder nor the generated
term invokes `Direct` or `Eval`. The execution application projects the payload
of `quote interpreterBody` syntactically.

`Circular.Representation` reads back captured closures by syntactic
substitution and parses the exact Scott data encoding. `Represents` uses this
decoder; it never invokes a source evaluator. Round-trip, injectivity, and
unique-decoding theorems establish that this is a data representation.

`Circular.Examples` contains kernel-checked execution witnesses and decoded
results for the identity application, open variable, unbound function with
omega as its argument, and open lambda. It also proves the direct omega result
is `none` at every fuel, absence of a direct omega derivation, exclusion of
quoted input from `Pure`, and that interpreted outputs differ from raw source
outcomes. The general theorems are in `Circular.Correctness`.

`Circular.Closing` relates closure evaluation to closed substitution
semantics without changing the source evaluator or its domain.
`Circular.Reduction` certifies finite call-by-value reductions and counts
beta contractions in derivations. `Circular.InterpreterProof` proves the
existing fixed-point interpreter's forward simulation by induction on source
derivations, and its reverse simulation by induction on that reduction count.
The reverse simulation covers every interpreter result. The omega theorem
combines coverage, metacircular correspondence, and `omega_no_direct`.
