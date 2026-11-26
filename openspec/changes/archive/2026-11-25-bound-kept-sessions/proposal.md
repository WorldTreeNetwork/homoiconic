# Bound a kept session's time, space and stack

> **FOLDED** 2026-11-25 into `openspec/specs/bytecode-machine`, `code-as-data`, `state-store` and `zig-host` (bases stamped by `fold_base.py`, checked clean). Was ACTIVE BUILD, 2026-11-25. Beads `homoiconic-q59.80`, `homoiconic-q59.70`, `homoiconic-q59.78` (and `homoiconic-q59.75` for a kept session only). Host-only paths: the lazy store machine and the session behind the `keep`, `vm` and `node` commands, and the walkers those commands, `ask` and `chan` use. The image links these modules but no guest reaches them.

**Rigor:** architecture (a new run of the lazy machine with a ledger of cells and its theorems in `Reflect`, a new charge on the lazy machine, a new field on the session, a new line, walks swapped in by `@[csimp]`).

## Why

The plain machine's charges bound its time per step (`charge-work-by-size`) and its cells (`add-space-budget`). A kept session runs a second machine, the lazy one (`Reflect.lstep`), and neither holds there. Measured on the tree before this change, on a Mac (`kernel/CostBench.lean`, `lazy` cases, budget 100000):

- `add x 1` with `x` data doubled 14, 16, 18 times: 32.6, 133 and 538 µs for each unit of budget, four times as long for each doubling; the plain machine takes 30 ns a unit at 40 doublings. The lazy machine converts an operation's whole argument to data (`P.toData`), a walk of the argument as a tree, and charges `add` one.
- `equal x x` on the same data, refused for its charge: 159 ms at 20 doublings, 688 ms at 22, before the step is refused (the plain machine refuses at 40 in microseconds). The charge itself is found by the full conversion and `Ops.cost`, not within the budget left.
- A literal is made into a piece (`Data.toP`) at every step that reaches it, a walk of its size charged one.
- `keep start` of `def deep x = [x, ...deep x]` at the default budget holds 542 MiB (`/usr/bin/time -l`), where `run` stops it at 4000000 cells and 116 MiB. The lazy machine has no space limit.
- `keep start` of a program whose result is a list of 90000 items, or nested 100000 deep, ends the process on a full stack in `Keep.full`; saving a waiting program that holds a list or a nest of a million ends it in `Wire.cut`; a `vm` log of 100000 entries ends it in `Keep.dataEntries`.

## What changes

- The lazy machine's charge counts the conversions its step makes: an operation is charged its table cost and one for every `convUnit` pieces of its argument; a step that hydrates the argument one for every `convUnit` pieces and one; a literal one for every `convUnit` pieces it makes and one. The charge is found within the budget left (`lstepCostWithin`, proved equal to `min (lstepCost s) (cap + 1)`), by counting pieces with a bound and converting only what the bound admits.
- `Reflect.lrunSpace`: the lazy run, priced and with a ledger of cells and a count when it is spent, as `runSpace` is for the plain machine, with its own outcomes (at a state, paused for a piece, out of space). Proved: it stops where `lrun` gets in no more steps than its fuel, a pause is a step that needs the piece it names, and the cells its steps made are within its credit or within the limit after a count.
- A kept session runs every machine run with `lrunSpace` under a space (by default `Reflect.defaultSpace`; the host gives the runtime's count, as `run` does, and adds the cells of the pieces the session has been given). A turn out of space, a result or payload too large to write in four bytes a cell, and a state too large to save are each `no result within <cells> cells of a turn`.
- Every walker on these paths that recursed once per level or per item is a loop, swapped in by `@[csimp]` with a proof that it is the definition, or bounded with its own refusal; `Keep.full` becomes a total, bounded walk.

## Not in this change

- A turn out of space inside the plain drivers (`ask`, `chan`, the crossing guest) still reads as out of steps (`homoiconic-q59.75`): the drivers' result types and proofs change, and the crossing's are being worked on by another agent.
- `Crossing.mix` (a crossing guest reaches it; the crossing's theorems are another agent's).

No new UI because this is a kernel and check change; the only new text is the space line of a kept turn.
