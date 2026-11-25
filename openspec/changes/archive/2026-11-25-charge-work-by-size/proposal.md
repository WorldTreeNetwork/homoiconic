# Charge a step by the work it does

> **FOLDED** 2026-11-25 into `openspec/specs/bytecode-machine/spec.md` (the base was diffed by hand; no `fold_base.py` stamp). Was ACTIVE BUILD, 2026-11-25. Bead `homoiconic-q59.73` and the audit it asked for. The cost table gains fields, so this was a change and not a dated edit of the living spec.

**Rigor:** architecture (new fields on the operation table `Ops`, a new charge for steps of the machine's own, the restated `runPriced_unit`, and a capped computation of the charge proved equal to the charge).

## Why

A step budget is meant to bound a guest's time. It did not. `equal` (operation 5) was charged one whatever it compared, and since `3e0635d` it compares data a million deep in one step: data built by doubling forty times is forty cells and 2^40 as a tree, so one charge of one ran for hours (measured: doubling 24 times, 1.08 s for one step on a Mac; each doubling twice that). The audit the bead asked for found four more steps whose time grows with data while their charge is one: `cons` onto a text (it turns the text into an array: 721 µs a step for a text of a million), `succ` and `case` of a large number (9.3 µs and 2.9 µs a step for a number of 1 MB), and reaching a variable deep in the environment (the walk is that long: a loop 100000 deep did not finish in 120 s at a budget of 10000000). Each of those is one charged step for work that has no bound but the data's size, and the data can be as large as the boot limit allows or, for a text, as a budget can build.

## What changes

- `Ops` holds three more fields, each with a default, so a table that does not give them is unchanged: `costWithin n d cap`, the charge or `cap + 1` when it is more, with its law `costWithin_eq` (proved for `arith`); `work d`, the charge for a step of the machine's own on the data it takes whole; `reach i`, the charge for walking `i` places of the environment.
- `stepCost` charges `Ops.reach` of how far reaching a variable walks (`reachIn`, the index or the environment's length, whichever is less), and `Ops.work` of the number `succ` or `case` takes and of the text `cons` turns into an array. Every other step is charged as before. The lazy machine's `lstepCost` charges the same `work`; its variable lookup was already a step for each place.
- `runPriced` and `runSpace` run as `runPricedWithin` and `runSpaceWithin`, which ask the charge with the fuel as its cap (`stepCostWithin`). Both are proved equal (`@[csimp]` `runPriced_eq_within`, `runSpace_eq_within`), so every definition and theorem about the runs is the one it was. A step the fuel cannot pay for is found out in no more time than the fuel pays for.
- For `arith`: `equal` costs the weight of the lighter of its two values (`Data.weight`: a number its 64-bit words, a text one more than its length, an array one more than its items, the value counted as a tree), found within the cap by weighing both values within a doubling bound, so comparing a small value with a huge one costs the small one. `work` is a number's 64-bit words (one below 2^64) and a text's length and one. `reach i` is `i / 32 + 1`. `Data.same` compares two arrays' lengths by walking both together (`lenEq`), so it takes no longer than the shorter.
- `runPriced_unit` takes the two new fields as hypotheses beside `Ops.cost`: with a table whose every charge is one, a priced run is `runUntil`. Every other theorem is unchanged in statement and proof.

## Charges that moved

On every program in `examples/` at levels 0, 1 and 2, only two totals changed: `calc.hom` 30 more and `words.hom` 3 more, at each level, both from `equal` on texts. No check moved to the other side of its threshold; the mjolnir fixture replies are byte for byte what they were.

## Not in this change

- The lazy machine of a kept session still converts an operation's argument to data (`P.toData`), and a literal to a piece (`Data.toP`), in time that grows with the data, and its charge for `equal` is not capped: filed as its own bead.
- Large numbers read and printed in time quadratic in their length: `homoiconic-q59.64`, in the same campaign but no change to the table.

No new UI because this is a kernel and check change.
