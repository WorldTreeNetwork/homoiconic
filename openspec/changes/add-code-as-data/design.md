# add-code-as-data

## Library

A second library, `Reflect`, in the `kernel/` package. `Circular` is not imported by it and is not edited.

| Module | Holds |
|---|---|
| `Reflect.Syntax` | `Data`, `Term`, `reify` |
| `Reflect.Semantics` | `Value`, `Outcome`, `Direct`, `evalFuel`, determinism, fuel soundness, monotonicity, completeness |
| `Reflect.Interpreter` | the named builder and `interp` |
| `Reflect.Proof` | the simulation, both directions |
| `Reflect.Correctness` | the four contract theorems |
| `Reflect.Examples` | scenarios as checked statements |

## Language

Taken from the spike.

```
Data    = nat Nat | arr (List Data)
Term    = var Nat | lam Term | app Term Term | lit Data
        | succ Term | cons Term Term
        | dcase Term Term Term Term Term
Value   = closure Term Env | data Data
Outcome = value Value | unbound Nat | wrong
```

`dcase s z sc n c` evaluates `s`. On `nat 0` it evaluates `z`. On `nat (k+1)` it evaluates `sc` with `nat k` bound. On an empty array it evaluates `n`. On `x :: xs` it evaluates `c` with `x` bound at index 1 and `arr xs` at index 0. On a closure it is `wrong`. Only the taken branch is evaluated.

Evaluation is call-by-value, function first. A data value in function position is `wrong` and the argument is not evaluated. `succ` of anything but a number is `wrong`. `cons` evaluates its head, is `wrong` on a closure head before the tail is evaluated, and is `wrong` on a tail that is not an array. `unbound` and `wrong` propagate. Divergence is the absence of a derivation.

## Program as data

| Term | `reify` |
|---|---|
| `var i` | `nat i` |
| `app f a` | `[0, f, a]` |
| `lam b` | `[1, b]` |
| `lit d` | `[2, d]` |
| `succ t` | `[3, t]` |
| `cons a b` | `[4, a, b]` |
| `dcase s z sc n c` | `[5, s, z, sc, n, c]` |

A closure as data is `[0, body, env]`. A data value as data is `[1, d]`. An outcome as data is `[0, v]`, `[1, i]`, or `[2]`.

## Theorems

Fixed at activation in `kernel/ReflectContract.lean`, in the manner of `Contract.lean`.

```
reflective : ∀ p o,
  Direct [] p o ↔
  Direct [] (app interp (lit (reify p))) (value (data (reifyOutcome o)))

reflective_coverage : ∀ p w,
  Direct [] (app interp (lit (reify p))) w →
  ∃ o, w = value (data (reifyOutcome o))

reflective_env : ∀ env p o,
  Direct env p o ↔
  Direct [] (app (app evalTerm (lit (reify p))) (lit (arr (reifyEnv env))))
    (value (data (reifyOutcome o)))

tower : ∀ k p o, Direct [] p o ↔ Direct [] (level k p) (lift k o)
```

`level (k+1) p` is `app interp (lit (reify (level k p)))`. `lift (k+1) o` is `value (data (reifyOutcome (lift k o)))`. `tower` follows from `reflective` by induction on `k`, because `reflective` has no side condition on `p`.

## Proof route

Stay in environment semantics. The kernel's proof moved to substitution to compare closures as syntax. Here the answer is data, so that step is not needed.

- Name the run-time value of the interpreter's recursive function and prove one unrolling lemma for applying it.
- Forward: induction on the source derivation. Each case is a derivation through a known case tree, with the induction hypothesis used at each recursive call.
- Reverse: strong induction on the fuel of the interpreter's run, with one inversion lemma per term constructor.
- Coverage needs the interpreter never to answer `wrong` on its own account when its input is `reify p`.

## Who does what

- The definitions in `Reflect.Syntax` and `Reflect.Semantics`, the interpreter, and the contract file are written and frozen first, by the change's owner.
- Determinism and the three fuel theorems are proofs against frozen statements and can be handed off.
- The simulation stays with the owner until the application case and the reverse direction have each been done once.

## Unverified hypotheses

- environment-style-simulation: claim: the simulation can be proved in environment semantics without a substitution relation or a readback. The spike proved the two cases that need no induction. confidence: medium. verification: none. synthesis path: this change.
