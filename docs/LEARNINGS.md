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

## 2026-11-10 — the host was built without optimisation, and a check passed a crash

- The host's Lean objects had been compiled without optimisation since the host landed. Nobody noticed until `host/out/run` made the speed visible: about 3.7 million steps a second. With `-O3` it is about 34 million. Defining `NDEBUG` reaches about 45 million but removes Lean's runtime assertions on the generated C, so it stays off.
- Review of `retire-circular-kernel` found shell checks of the form "a non-zero exit is a pass". Such a check also passes a crash. `host/check.sh` now asserts the exact exit status, empty standard output, and the exact error line.

## 2026-11-10 — one statement for every operation

- The vision expected one lemma per primitive (P8). Making the operation number a runtime value and the table a typeclass parameter removed the per-operation lemma entirely: the interpreter's branch for an operation is the same construct, `prim`, applied to the evaluated parts. The cost is the shape of an operation: total, data to data, with no failure outcome.
- Lean includes an instance-implicit section variable in every theorem of the section, whether or not the theorem uses it. Theorems that do not need the table had to be marked `omit [Ops] in`.
- A contract file that imports an instance can silently check a theorem for one table only. The contracts import no table and quantify over it explicitly, `∀ [Ops], …`.

## 2026-11-10 — one driver, one simulation lemma

- The request driver was defined once, over an abstract way of evaluating (`Sys`), with one simulation lemma (`Sim.drive`) that lifts turn-by-turn agreement to whole runs. The interpreter and machine agreement theorems for requests then each cost only a turn-level equivalence, proved from the existing `reflective` and machine theorems.
- Review caught that a request carries no mark. The driver reads every function a turn ends in as a request, so `fn x -> 42` asks `42` and a driven program cannot finish with a function. The first description said such functions end as `wrong`; only some do.
