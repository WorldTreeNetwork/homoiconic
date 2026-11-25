# Give a run a space limit beside its step budget

> **FOLDED** 2026-11-24 into `openspec/specs/bytecode-machine/spec.md`, `wire-bytes`, `zig-host`, `unikernel-image` and `unikernel-net`. Was ACTIVE BUILD, 2026-11-24. Bead `homoiconic-q59.67`. The direction, option 1 of the bead (a space budget in the priced run), was chosen by the orchestrator and is still Duke's to confirm. It is built so that it can be taken out again: see "Taking it out" in `design.md`, and "Options this leaves to Duke" for what the measurements changed about that choice.

**Rigor:** architecture (a new run function and theorems in `Reflect`, a new reply, a new argument on four exports, a C function that reads what the runtime shares).

## Why

A step budget does not bound memory. `def deep x = [x, ...deep x]`, 55 bytes, ran the 512 MiB image out of memory inside the default budget of 100000000 steps (`INTERNAL PANIC: out of memory`, `unikernel/README.md`), and so does any program that keeps building data. On the network guest that panic powers the guest off, so one small message from an allowed entity ends it. `depth_bound` bounds the stack and the frames. P3, a bound on the cells a run holds, is recorded as not proved.

## What changes

- A run counts the cells it makes in a ledger, beside the steps it pays for. `Reflect.runSpace` takes the steps `runPriced` takes and stops, with its own outcome, before a step that would make more cells than it has left.
- When the ledger is spent the run asks how many cells its state holds, each object counted once, and goes on with the difference if that is at most three quarters of the limit. The count is the runtime's (`reflect_live_cells`, a walk by address); the run function and its theorems take it as a parameter, as they take the operation table. A run with no count cannot go on: its ledger is all it has.
- A new outcome, out of space: the line `no result within <n> cells` on the text paths, and the reply `[7]`, bytes `81 07`, beside the budget reply `81 01`. The reply of a run that stays within its space does not change.
- An answer is checked before it is written: one that would take more than four bytes written for each cell of the space is the space outcome too. A value is written as a tree, so forty cells built by doubling are 2^40 bytes, and the printer holds far more than a cell's bytes for each item.
- The limit is a number of cells. The kernel has a default, 4000000, chosen for the 512 MiB image. The four exports that make one run (`reflect_run`, `reflect_run_bytes`, `reflect_interp`, `reflect_reply_bytes`) take it as an argument; `host/out/run`, the boot image's command line and the network image's `reflect.space=` word can give another. The `RFL1` frame is unchanged.
- Every machine run inside a driver (requests, channels, VM, node, a guest of a crossing and its check) is a turn with a limit of its own, `turnSpace`, and no count: it may make that many cells and then is unfinished, the same on every machine that replays it.
- Proved, for every table and every count, with no `sorry` and no axiom of this package: the run takes `run`'s steps, never faults, halts only with what the program evaluates to, is the priced run when it is not stopped for space, is stopped for space only when the cells made would pass what it began with, and every state it is in was reached from the start, or from a state it counted, by steps that made no more than it had left (`MachineContract.lean`).

## What stays a hypothesis

- That the ledger covers what a step makes in memory, and that the runtime's count is the cells a state holds. The machine's state is a tree; nothing in it says a part is held once. Measured: counted as a tree, the state of a program of 20 definitions is 20 million cells while it holds a few hundred, so no function of the state alone can be the measure (`design.md`).
- What a cell is in bytes: at most 24 on the image, with the allocator's own overhead, the walk's table, an answer made before it is charged and the printer on top. The default is set by measurement, not derived.
- Past the ledger, whether a run goes on depends on what the runtime shares. Two builds of one kernel share the same; a different compiler might not. Inside the ledger nothing depends on it.

## Not in this change

- The lazy machine of a kept session (`Surface.Keep.steps`) has no space limit yet: `homoiconic-q59.70`.
- A guest of a crossing bounds each turn, not what its processes and its log hold together, so a program that starts processes can still end a guest: `homoiconic-q59.71`.
- A turn out of space has no line of its own; a driver reports it as out of steps: `homoiconic-q59.75`.
- Data nested deeper than the native stack still ends in a full stack in the printer, the writer and `equal`: `homoiconic-q59.72`. `equal` is charged one whatever it compares: `homoiconic-q59.73`.
- A count that is a function of the state (share the state when it is counted), which would make the outcome independent of the runtime: `homoiconic-q59.74`.
- mjolnir learns the reply `81 07` in its own change (a bead in its tracker).

No new UI because this is a kernel, host, image and check change.
