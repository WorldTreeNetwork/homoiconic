# add-bytecode-machine

## Code

Settled when the definitions were written, 2026-11-09. Two departures from the first sketch, both recorded here.

Code is in continuation form: each instruction carries the code that follows it, and `done` ends a block. A closure body and each case branch is a block. This is one plain inductive type, so compile and the proofs are by ordinary induction. It is not yet a flat array with offsets. Flattening is a later, invertible pass and is not in this change.

| Instruction | Does |
|---|---|
| `access i` | push the value at index `i` of the environment, or halt with `unbound i` |
| `closure body` | push a closure over `body` and the current environment |
| `literal d` | push the data value `d` |
| `checkFun` | halt with `wrong` unless the top of the stack is a closure |
| `apply` | pop argument and function, save a frame, and enter the closure body |
| `checkData` | halt with `wrong` unless the top of the stack is data |
| `succ`, `cons` | as in `Reflect.Semantics`, halting with `wrong` on misuse |
| `dcase z sc n c` | pop the scrutinee, save a frame, extend the environment as `dcase` does, and enter one of four blocks |
| `done` | end of block: return to the saved frame, or halt with the one value on the stack |

`comp t k` computes `t`, pushes it, and continues as `k`. `compile t` is `comp t done`. The two guards keep the order of `wrong` checks equal to `Direct`: `checkFun` sits between function and argument, `checkData` between head and tail.

## State

A state is running, halted with an outcome, or `fault`. A running state holds code, an environment, a value stack, and a stack of frames. `step` is total. Halted and fault states step to themselves. `fault` is not an outcome. A compiled program that halts does not pass through it. That a compiled program which never halts also avoids it is not proved here; it needs a well-formedness invariant on states and is tracked separately. `done` with no frame and anything but one value on the stack is a `fault`. `run n` applies `step` `n` times.

Machine values hold code, not terms. `readValue` turns a machine value back into a `Reflect` value by decompiling its code.

## Theorems

Fixed in `kernel/MachineContract.lean`.

```
machine_correct : ∀ t o,
  Direct [] t o ↔ ∃ n w, run n (load (compile t)) = halted w ∧ readOutcome w = some o

machine_exact : ∀ t n w,
  run n (load (compile t)) = halted w → ∃ o, Direct [] t o ∧ w = injO o

machine_never_halts : ∀ t, (∀ o, ¬ Direct [] t o) → ∀ n w, run n (load (compile t)) ≠ halted w

run_add : ∀ n m s, run (n + m) s = run m (run n s)

run_halted : ∀ n o, run n (halted o) = halted o

decompile_compile : ∀ t, decompile (compile t) = some t

depth_bound : ∀ n s, depth (run n s) ≤ depth s + n
```

`machine_correct` reads a closure back by decompiling its code, and decompiling ignores the two guards. So it does not by itself say a returned closure's code is the compiled body. `machine_exact` does: `injO` sends a source outcome to the machine outcome holding `comp b done` for each closure body. It was added after review, from the worker's own internal lemma. Pausing, moving, and disputing a run rely on the exact form.

`depth` is the value stack plus the pending frames. The bound is weak: it limits control depth and says nothing about the heap. This replaces the first sketch's `space_bound` over total state size, which is false: environments are shared between closures, so a size that counts each copy is not linear in steps. A true heap bound needs a model of allocation. That is left to the change that adds budgets to the host.

## Who does what

- The owner writes the instruction set, `step`, `compile`, and the contract file, and freezes them.
- The proofs are handed off against the frozen contract. Definition files are read-only to the worker. A proof that needs a definition changed is sent back.
- This is the first proof handed to a smaller model on this project. The result decides how later proofs are split.

## Measurement

One run file times the compiled machine on a fixed loop-heavy program and on the `Reflect` interpreter interpreting a small program. Steps per second go in `docs/LEARNINGS.md`. No target is set. The number informs the vision's `compiled-machine-speed` hypothesis.

## Hypotheses, resolved

- compiled-machine-speed: measured, not judged. About 40 million steps per second on an Apple M1 Max, unoptimized; one interpreter level costs a factor of about 52. Numbers are in `docs/LEARNINGS.md`. Whether that is enough depends on receipt sizes the vision has not fixed.
- delegated-proof: go. A smaller model proved all five contract theorems in 511 lines without editing a definition, and corrected a false hint in its brief. A fresh reader then found the contract weaker than one spec sentence; the fix used the worker's own lemma.
