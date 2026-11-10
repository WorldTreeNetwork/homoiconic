---
spike_id: primitive-data-restatement
hypothesis_id: primitive-data-restatement
source_synthesis: openspec/changes/add-verifiable-network-vision/design.md
run_at: 2026-11-09
time_spent_min: 60
verdict: go
version-pinned: lean 4.35.0
---

# Spike: primitive data, literal as quote, interpreter over data

## Claim Tested

`metacircular` can be restated for a language with one primitive first-order data type, where a program is a value of that type and the interpreter takes that value. The claim in `design.md` also said the fixed-point simulation would not have to be redone. That part is answered below, and the answer is different from the claim.

## Minimal Test

`src/Spike.lean` is standalone. It does not import or edit the kernel.

- **Data**: natural numbers and arrays of data.
- **Terms**: variable, lambda, application, `lit d`, `succ`, `cons`, and one `dcase` with four branches (zero, successor, empty, non-empty) that binds what it takes apart.
- **Values**: a closure or a data value. **Outcomes**: a value, `unbound i`, or `wrong`.
- **`reify`**: a total function from terms to data. Quoting `p` is `lit (reify p)`. There is no quote constructor.
- **`interp`**: one closed term. It takes a program as data and an environment as data, and returns the outcome as data. Recursion is the same call-by-value fixed point as the kernel's.
- **The check**: for each program `p`, `evalFuel` on `p` gives `o`, and `evalFuel` on `app interp (lit (reify p))` gives exactly `value (data (reifyOutcome o))`. Then the same check one level up, with the interpreter interpreting itself.

## Evidence

`repro-command.sh` exits 0. Seventeen programs agree at one level and at two. They include:

- the four kernel scenarios, and `omega` with no outcome on either route;
- literals, `succ`, `cons`, and every `dcase` branch, including a closure that captures a case binder;
- all four `wrong` outcomes;
- a quoted program, and quoted `omega`, returned as data and not run;
- a program that builds the identity function's code with `cons` at run time and hands it to the interpreter.

Two statements are proved for every payload by reduction alone, with `propext` as the only axiom:

- `literal_agrees : ∀ d, evalFuel 60 [] (viaInterp (lit d)) = some (value (data (reifyOutcome (value (data d)))))`
- `lambda_agrees : ∀ b`, the same for `lam b`.

The file is 289 lines with no `sorry`. The whole run takes under three seconds. Log: `evidence.log`.

## Verdict: go

The design works and is simpler than the kernel's in three ways.

- **No quote-free restriction.** `reify` is total. A program that contains a literal, including a quoted program, is covered.
- **No encoding beside the language.** The interpreter's input is `lit (reify p)`. `encode`, Church numerals, and the Scott program encoding are gone.
- **No decoder in the theorem.** The interpreter's answer is data. `Represents` becomes an equality with `reifyOutcome o`. `readback`, `decodeOutcome`, and the round-trip theorems have nothing left to do.

## What survives of the existing proof

By reading the 2,122 lines in `kernel/Circular/`, not by porting them.

| File | Lines | Fate |
|---|---|---|
| `Syntax`, `Semantics` | 243 | Rewritten for seven constructors. Same theorems, same shape, more cases. |
| `Encoding`, `Data`, `Representation` | 348 | Not needed. |
| `Interpreter` | 107 | Rewritten; the builder and the fixed point carry over. The spike has it. |
| `Closing`, `Reduction` | 388 | Not needed if the proof stays in environment semantics. They existed to compare closures as syntax, and the answer is no longer a closure. |
| `InterpreterProof` | 785 | Redone. The structure carries: dispatch lemmas, forward by induction on the source derivation, reverse by induction on a count. The lemmas do not. |
| `Correctness`, `Examples` | 180 | Restated. |

So the claim "without redoing the fixed-point simulation" is false. The simulation is redone. What is true is that the new one has less to prove, because about 740 lines of encoding, decoding, and closure-to-syntax machinery are not needed.

## Not measured

- **The application case.** The two proved statements need no induction. The step that uses an induction hypothesis under the fixed point was not attempted. That is where the cost is.
- **The reverse direction.** Unattempted. It needs inversion on the interpreter's run with a count, as the kernel's does.
- **A new obligation.** `wrong` is an outcome of closed terms, so "the interpreter on reified input never answers `wrong` on its own account" must be proved as part of coverage. The kernel had no such case.

## Choices the change should keep

- One eliminator with binders, not four primitives taking functions. Only the taken branch is evaluated.
- Errors propagate function-first, as in the kernel: a data value in function position is `wrong` before the argument is evaluated.
- Flat tags `0`–`5` for the six compound forms. `design.md` D8 sketched a nested primitive tag; the flat form is shorter to dispatch.
- Bytes are an inert leaf for this theorem and are added with the parametric statement.
