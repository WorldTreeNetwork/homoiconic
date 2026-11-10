# Learnings

## 2026-11-09 — speed of the Lean-compiled machine

`kernel/Bench.lean`, built with `lake build reflectBench`, Lean 4.35.0, Apple M1 Max, three runs each.

| Program | Machine steps | Time | Steps per second |
|---|---|---|---|
| Count down from 1,000,000, direct | 23,000,025 | 557–584 ms | about 40 million |
| Count down from 20,000, through the interpreter | 23,801,006 | 626–629 ms | about 38 million |
| Count down from 300, through the interpreter twice | 25,373,970 | 666–673 ms | about 38 million |

- One loop iteration is 23 steps direct, about 1,190 through one interpreter, and about 84,600 through two. One interpreter level costs a factor of about 52. The second level costs about 71.
- The machine does not reuse frames for calls in tail position, so the direct run holds about three frames per iteration, roughly three million at its deepest. It still runs.
- This is the unoptimized machine on continuation-form code. No flattening, no primitive beyond `succ`, `cons`, and the case form.

## 2026-11-09 — a proof found what the scenarios missed

Eighteen programs agreed across direct evaluation, the interpreter, and the machine. The forward simulation then failed on one rule: a case form whose scrutinee errors. The interpreter's `bind` helper reused the name `rs`, which shadowed the result it was meant to pass on. Scenarios now cover it. A helper that binds names needs names no caller can use.

## 2026-11-09 — fuel does not bound machine steps

A hint given to the machine-proof worker was false: "halting in `n` steps forces `evalFuel (n+1)` to be `some`". `app (app (var 5) a) b` at the empty environment halts in one machine step and needs fuel 3. Fuel bounds derivation height. The worker proved the reverse direction by strong induction on the step count instead.

## 2026-11-09 — reverse simulation without inversion

To show that a run of the interpreter comes from a source derivation, it is enough to show that a source evaluation out of fuel leaves the interpreter out of fuel. That is a goal-directed walk, like the forward direction. Then completeness, the forward direction, and determinism finish it. The interpreter's run is never taken apart.
