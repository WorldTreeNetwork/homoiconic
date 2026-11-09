# Circular kernel

This package is incomplete for `add-lean-circular-kernel`. The executable
interpreter and the direct evaluator build, but the general `metacircular`
and `coverage` theorems have not been proved or declared. In particular,
there is no proof yet that the interpreter has no derivation on omega.
A successful `lake build` alone does not satisfy this change's acceptance.

Use Lean 4.35.0, pinned in `lean-toolchain`, and run commands from this directory:

```sh
lake build
lake env lean Run.lean
lake env lean Axioms.lean
lake env lean Contract.lean
```

`Contract.lean` checks the exact general theorem types and currently exits
with missing-declaration errors. `Axioms.lean` prints dependencies of the
implemented proofs; these use only standard Lean logical axioms, with no
`sorryAx` or package-declared axioms. `Run.lean` executes both routes on the
identity application and open variable, and the interpreter on the remaining
scenarios. Its bounded omega result is an execution check, not a proof of
interpreter divergence.

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
outcomes. These concrete cases do not establish the two general theorems.
