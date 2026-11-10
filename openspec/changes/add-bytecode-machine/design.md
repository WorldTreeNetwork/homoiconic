# add-bytecode-machine

## Instructions

A program is an array of instructions. An instruction is a small number followed by its operands, so code is a `Data` array of numbers.

| Instruction | Does |
|---|---|
| `access i` | push the value at index `i` of the environment, or halt with `unbound i` |
| `closure n` | push a closure over the next `n` instructions and the current environment, and skip them |
| `apply` | pop argument and function; enter the closure, or halt with `wrong` on data |
| `return` | leave the current closure with the top of the stack |
| `literal d` | push the data value `d` |
| `succ`, `cons` | as in `Reflect.Semantics`, halting with `wrong` on misuse |
| `case nz ns nn nc` | pop the scrutinee, extend the environment as `dcase` does, and enter one of four blocks of the given lengths |

`compile` is the postfix flattening: function, then argument, then `apply`. Evaluation order and the order of `wrong` checks must match `Direct`. Where a check in `Direct` comes before a later subterm is evaluated, the compiled code needs a guard instruction at that point. The owner settles that list before the contract is frozen.

## State

A state is running or halted. A running state holds a code pointer, an environment, a value stack, and a stack of return frames. `step` is a total function on states. A halted state steps to itself. `run n` applies `step` `n` times.

Machine values hold code, not terms. `readValue` turns a machine value back into a `Reflect` value by decompiling its code.

## Theorems

Fixed at activation in `kernel/MachineContract.lean`.

```
machine_correct : ∀ t o,
  Direct [] t o ↔ ∃ n w, run n (load (compile t)) = halted w ∧ readOutcome w = o

run_add : ∀ n m s, run (n + m) s = run m (run n s)

decompile_compile : ∀ t, decompile (compile t) = some t

space_bound : ∀ n s, size (run n s) ≤ size s + c * n
```

`c` is a stated constant.

## Who does what

- The owner writes the instruction set, `step`, `compile`, and the contract file, and freezes them.
- The proofs are handed off against the frozen contract. Definition files are read-only to the worker. A proof that needs a definition changed is sent back.
- This is the first proof handed to a smaller model on this project. The result decides how later proofs are split.

## Measurement

One run file times the compiled machine on a fixed loop-heavy program and on the `Reflect` interpreter interpreting a small program. Steps per second go in `docs/LEARNINGS.md`. No target is set. The number informs the vision's `compiled-machine-speed` hypothesis.

## Unverified hypotheses

- compiled-machine-speed: claim: the Lean-compiled machine is fast enough to re-execute receipts of practical size. confidence: low. verification: none. synthesis path: this change measures it.
- delegated-proof: claim: a smaller model can prove `machine_correct` against a frozen contract without editing definitions. confidence: medium. verification: none. synthesis path: this change.
