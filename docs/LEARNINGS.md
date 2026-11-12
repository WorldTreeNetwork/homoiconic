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

## 2026-11-11 — one type for pieces, progress one place at a time

- Pieces use one type, `P`, for data, values and environments. Resolution, `Unf`, is then one inductive relation, and the store proofs go by induction on it. Mutual definitions remain only where a piece is built from the machine's own separate types.
- Progress of the lazy machine is proved by forcing one place at a time (`force`): induction on the resolution of the piece at that place, fetching until it is not a reference. No global measure on the store or the state was needed.
- The check cuts a state as a tree, with no sharing. The interpreter interpreting itself on `2`, stopped after 300 steps, gave 1,110,817 pieces. Storing by content removes the duplicates, and needs bytes.

## 2026-11-11 — a byte form for code

- `decompile` reads code that no compilation produces: `decomp` drops `checkFun`, `checkData` and `checkNat`. So "decompile, then compile" is not the identity on arbitrary code, and two different function values wrote the same bytes until review caught it. The writer now compiles the decompiled program again and compares (`Wire.blockTerm`). `decompile_compile` holds only in the other direction.
- Lean 4.35 accepted `Wire.unreify` by structural recursion over the nested type `Data` (`arr : List Data`), with patterns several list items deep, and no termination proof. `unreify_reify` was `induction t <;> simp_all [reify, unreify]`.
- In Lean 4.35 a doc comment (`/-- … -/`) directly before `#eval` is a parse error: a doc comment must precede a declaration. Use `--` there.

## 2026-11-12 — kept state

- Lean 4.35 refuses borrow annotations (`@&`) on an `@[export]` declaration ("marked as `export` but some of its parameters have borrow annotations"). An exported function therefore always uses up each Lean-object argument, and a C caller that will pass the same object again must `lean_inc` it first. The host does this through `kernel_retain` in `kernel/ffi.c` before every call that takes the session.
- A fuel counter spent on a data-dependent loop looked like success when it ran out. `Surface.Keep.advance` spent fuel following references, and at zero returned the session unchanged; with 70 references in a chain the turn ended with no text and exit 0. Review found it. References are now followed by `Keep.chase` with no limit, fuel only bounds phases that come in one order, and running out says `error: the turn did not settle`.
- Blake3, written in Lean from its specification in about 100 lines (`kernel/Wire/Blake3.lean`), matched all 22 official vectors, and the reviewer's 135 further inputs against Python's `blake3`. The file has not changed since it landed.
- Writing Lean through an unquoted shell heredoc (`<<EOF`) runs each backticked word in a doc comment as a command. Use a quoted heredoc (`<<'EOF'`) for Lean source.

## 2026-11-12 — channels

- The request driver's cases could not be reused for one turn of a process. `Drive` is indexed by the list of answers and the list of requests asked, so its four cases were restated without those lists as `Settle` (`kernel/Reflect/Channel.lean`). The cases are the same; the restatement is the cost.
- The simulation from requests, `Sim`, carried over to schedules with one added field: `PSim` is `Sim` plus `start`, which says the two ways of evaluating start a program alike. The machine agreement theorems for schedules then followed from the turn-level ones already proved for requests.
- Review found no fault in the definitions and two in what the printed text claimed. The last line, then `nothing more can happen`, described the chooser, which never offers an answer from outside and does not run the machine, not what the semantics allows. And a printed schedule replays to the same last line only when the first run was not refused and did not run out of budget.
