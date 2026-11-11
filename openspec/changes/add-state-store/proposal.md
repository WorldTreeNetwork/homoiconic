# add-state-store

> **PENDING**

**Rigor:** instrument

Depends on: `add-requests` (folded, `eeb3706`). Vision: `add-verifiable-network-vision`, the state half of stage 5 (P13's "a snapshot is a prefix") and what stage 6 needs for a closure to travel (P15). Authority: direction from the user on 2026-11-10: copy-on-write state that the substrate may move, synchronize, cache and erasure-code; partial trees with references hydrated on read; several streams of state that share history. The build waits for the user's go.

## Why

A running program is held whole, in memory, on one machine. It cannot be saved, moved, or run while part of it is somewhere else. The `ask` command replays from the start on every call because a waiting program cannot be kept.

The state is already a tree of immutable values: a function is code and the list of values it captured, and nothing is ever changed in place. So the state can be cut into pieces at any point, each piece stored once, and a missing piece fetched when the program first looks at it. The program must not be able to tell.

## What

- A **reference** names a stored piece of state. The kind of reference is a parameter, as the operation table is. The kernel does not say how a reference is made; a hash of the piece's bytes is the intended one, and is the substrate's.
- A **partial value** is a value in which any sub-value, function or data, may be a reference instead of the thing itself. A **partial state** is a machine state built from partial values.
- A **store** maps references to partial values, and may lack any of them. A partial value **resolves** to a value under a store when following every reference gives that value.
- A **lazy machine** runs a partial state against a store. When a step has to look at a value that is a reference, it fetches that one piece. If the store lacks it, the machine stops as **needing** that reference. Needing is a pause, like waiting on a request. It is not an outcome, and a program cannot observe it.
- **Saving** cuts a state into pieces and puts them in the store. Where the cuts go is the caller's choice; the theorems hold for every choice. A piece that came from the store keeps its reference, so saving writes only what is new. That is the copy-on-write.
- A **root** is a reference to a whole state or value. Two roots share every piece they have in common. A snapshot, a fork, and a separate stream of state are each a root; the kernel says no more about them.
- The request driver can end a run by handing back the root of the waiting program, and continue a run from a root.

## What is proved

For every operation table and every kind of reference, with Lean's standard axioms only.

| Theorem | Says |
|---|---|
| Saving loses nothing | A state cut into pieces in any way resolves back to the same state |
| Hydration is invisible | If a partial state resolves to `s`, the lazy machine and the plain machine agree step for step: every state the lazy machine reaches resolves to the state the plain machine reaches |
| Missing is a pause | With part of the store withheld, the lazy machine either gives what it gives with the whole store or stops needing a reference the store lacks. It never gives a different outcome, and never `wrong` for a missing piece |
| More never changes the result | Adding pieces to a store changes no result; a run that stopped needing a reference, continued after the piece arrives, gives what an uninterrupted run gives |
| Any substrate will do | Two stores that agree wherever both hold a piece give the same results |
| A stored run continues the same | A waiting run saved to a root and continued from it with an answer is the program run from the start with that answer added (lifts `interact_resume`) |

With `machine_correct` these give: a program run from stored, partly absent state has the outcome direct evaluation gives it.

## What is assumed, not proved

- **A reference names one piece, for ever.** The store is a function and is only added to. A hash gives this up to collisions; signatures and attestations say who vouches for a piece. Both are the substrate's: the network interface, the enclave, identikey. A proof about the checker that verifies an attestation is worth having and is a separate change.
- **The byte form of a piece.** That is `add-wire-bytes` (`homoiconic-q59.12`). This change keeps the store in memory.

## What the substrate is then free to do

Anything that keeps the one assumption. Move pieces off the device and pull them back on read. Keep copies on several machines. Put a caching proxy in front. Split a piece with erasure coding. Hold many roots that share pieces, as snapshots and volumes do. None of it can change what a program computes; it can only change when a run pauses.

## Design notes

- **Operations need their whole argument.** A case on data looks at one level and fetches one piece. An operation takes complete data, so its argument is fetched in full first. Operations that work on partial data are not in this change.
- **Captured scope is the whole scope.** A function keeps every value visible where it was made. Because those are references once stored, an unused one costs a reference, not a fetch.
- **A program cannot hold or make a reference.** References exist below the language. This keeps P12 open to a later proof and keeps persistence orthogonal.
- **Nothing is deleted.** Which pieces are no longer reachable from any kept root, and reclaiming them, is the substrate's.

## Not in this change

- Hashing, bytes, files, the network, synchronization, erasure coding
- Signatures and attestations
- The event log (P13 as a fold over events, P14)
- Garbage collection
- Trimming a function's captured values to the ones it uses
- A program-visible way to save, load, or name state
- Storing state on disk from the `ask` command; that follows `add-wire-bytes`

## Impact

- Capabilities: ADDED `state-store`
- New files: `kernel/Reflect/Store.lean`, `kernel/Reflect/StoreProof.lean`, `kernel/StoreContract.lean`
- `kernel/Reflect/Machine.lean`, the existing machine theorems, `ReflectContract.lean`, `MachineContract.lean` and `RequestContract.lean` are not edited
- `ARCHITECTURE.md`, `kernel/README.md`, `docs/PROOFS.md`: amended at fold

## User journey & surfaces

No new UI because the store is in memory and has no command yet. What can be seen is the check:

- **Working** — the examples, cut at every value and run with the whole store, print what they print today.
- **Partial** — run with pieces withheld, an example stops needing a named reference; given the piece it goes on to the same text.
- **Failed** — a partial run gives a different outcome from the whole run, or reports `wrong` for a missing piece.

## Out of scope

Listed under "Not in this change".
