# add-lean-circular-kernel

## Fragment

The named fragment is the pure lambda fragment. Binders are de Bruijn indices. Index `0` is the nearest binder.

- A term is `var i`, `lam body`, `app fn arg`, or `quote t`.
- `Pure t` holds when no `quote` occurs anywhere in `t`. Purity is not restricted to closed terms, typed terms, or normalizing terms.
- A pure outcome is a closure `closure body env` or `unbound i`.
- `Direct env t o` is an inductive call-by-value relation. The function is evaluated before the argument. Rules:
  - `var i` yields the value at index `i`. If `i` is past the end of `env`, the outcome is `unbound i`.
  - `lam b` yields `closure b env`.
  - `app f a` evaluates `f` to a closure, evaluates `a` to an outcome, and, when that outcome is a value, evaluates the body in the environment extended with that value. An unbound argument is the outcome of the application.
  - `quote` has no `Direct` rule.
- Divergence is the absence of a derivation. It is not an outcome constructor. The pure term `app (lam (app (var 0) (var 0))) (lam (app (var 0) (var 0)))` has no `Direct` derivation at the empty environment. The theorem has no fuel argument. A fuel-indexed function may be used as an executable witness. The theorem does not treat equal fuel as equal results.
- `Eval` is `Direct` plus one quote rule: `Eval env (quote t) (code t)`. The rule returns `t` as data and does not evaluate `t`. It does not call `Direct` on `t`.

## Interpreter term

Program encoding is Mogensen–Scott. `encode` is a Lean function from pure terms to pure terms. Continuations are bound in the order variable, abstraction, application. Payloads are shifted by those binders.

- `encode (var i) = λv. λl. λa. v ⌜i⌝`
- `encode (lam b) = λv. λl. λa. l (encode b)`
- `encode (app f a) = λv. λl. λa. a (encode f) (encode a)`
- `⌜0⌝ = λf. λx. x`, and `⌜n+1⌝ = λf. λx. f (⌜n⌝ f x)`.
- `encode` is not defined on a term that contains quote.

Encoded environments are Scott lists of encoded outcomes: `nil = λn. λc. n` and `cons h t = λn. λc. c h t`.

`interpreterBody` is one closed pure term, written with `var`, `lam`, and `app` only. Applied to `encode p`, it applies that encoding to three continuations:

- Variable: look the Church numeral up in the encoded environment. The empty list yields an encoded `unbound` outcome, not a loop.
- Abstraction: build an encoded closure from the encoded body and the current encoded environment.
- Application: decode the function outcome as a closure, evaluate the argument through this same body, and evaluate the closure body in the extended encoded environment.

`interpreterBody` contains no primitive that invokes `Direct` or `Eval`.

The interpreter-term is `quote interpreterBody`. Its payload is the constructor argument. Projecting that argument is not evaluation. The execution route for a pure program `p` is `Direct` at the empty environment on `app interpreterBody (encode p)`. Both the body and the encoding are pure, so this route uses `Direct`, not the quote rule. The quote rule is not applied to the input program.

## Theorem

`Represents o w` decodes the object-level closure `w` with the inverse of the outcome encoding below. It is not observational equivalence, and it is not a trivially true predicate. A code value does not decode.

- `encodeOutcome (value v) = λok. λbad. ok (encodeClosure v)`
- `encodeOutcome (unbound i) = λok. λbad. bad ⌜i⌝`
- `encodeClosure (closure b env)` is the Scott encoding of that closure: the abstraction tag applied to `encode b` and the Scott list of `encodeOutcome` on `env`.

```
metacircular :
  ∀ p, Pure p → ∀ o,
    Direct [] p o ↔
    ∃ w, Direct [] (app interpreterBody (encode p)) w ∧ Represents o w
```

The quantifier is every quote-free term, including open and diverging terms. Open terms derive `unbound`. Diverging terms derive nothing on either side. `Direct` is deterministic.

The theorem does not quantify over a term that fails `Pure`. It does not state that the interpreter interprets itself. One level.

## Why this fragment

It is large enough for an interpreter to be a term, and small enough that the equality is one theorem. Numbers, recursion, and effects are later languages.

## Build

The package is Lean 4, built with `lake build`. `metacircular` is a declaration in that package. Its dependencies include no `sorryAx` and no axiom declared by this package.

These facts are declarations in the same package:

- `app (lam (var 0)) (lam (var 0))` is pure. Both routes derive `closure (var 0) []`, related by `Represents`.
- The omega term in Fragment is pure and has no `Direct` derivation at the empty environment, so the interpreter route has no `Represents` witness either.
- `var 0` at the empty environment derives `unbound 0` on both routes.
- `quote (var 0)` does not satisfy `Pure`.

## Downstream

`add-zig-host` calls this package. It does not start from this contract. It starts when this kernel exports a callable entry and the host change is activated.
