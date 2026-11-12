# add-state-store

> **ACTIVE BUILD**

**Rigor:** instrument

Depends on: `add-requests` (folded, `eeb3706`). Vision: `add-verifiable-network-vision`, the state half of stage 5 (P13's "a snapshot is a prefix") and what stage 6 needs for a closure to travel (P15). Authority: direction from the user on 2026-11-10: copy-on-write state that the substrate may move, synchronize, cache and erasure-code; partial trees with references hydrated on read; several streams of state that share history. The user said to build it on 2026-11-11.

## Why

A running program is held whole, in memory, on one machine. It cannot be saved, moved, or run while part of it is somewhere else. The `ask` command replays from the start on every call because a waiting program cannot be kept.

The state is already a tree of immutable values: a function is code and the list of values it captured, and nothing is ever changed in place. So the state can be cut into pieces at any point, each piece stored once, and a missing piece fetched when the program first looks at it. The program must not be able to tell.

## What

- A **reference** names a stored piece of state. The kind of reference is a parameter, as the operation table is. The kernel does not say how a reference is made; a hash of the piece's bytes is the intended one, and is the substrate's.
- A **piece** (`P`) is one type for data, values and environments: a number, an empty list, a pair, a function (code and its environment), or a reference. Any part of a piece may be a reference.
- A **store** maps references to pieces and may lack any of them. A piece **resolves** to a value under a store when following every reference gives that value (`Unf`). A partial machine state resolves to a machine state the same way (`RState`).
- A **lazy machine** (`lstep`, `lrun`) runs a partial state against a store. When a step has to look at a value that is a reference, it fetches that one piece. If the store lacks it, the run is **paused**, holding the reference it needs and the state it stopped in. A pause is not an outcome, and a program cannot observe it.
- **Saving** is cutting: a piece put in the store under a reference can be replaced by that reference, anywhere, and the state still resolves to the same thing. Where the cuts go is the caller's choice.
- A **root** is a reference to a whole value. Two roots share every piece they have in common. A snapshot, a fork, and a separate stream of state are each a root; the kernel says no more about them.
- A turn of the request driver can be run from a stored continuation.

## What is proved

For every operation table and every kind of reference, with Lean's standard axioms only. Exact statements: `kernel/StoreContract.lean`.

| Theorem | Says |
|---|---|
| `saved_resolves`, `cut_resolves`, `RState.mono` | Saving loses nothing: a state held whole resolves to itself, a stored piece can be replaced by its reference, and a state that resolves still does when the store holds more |
| `Unf.unique`, `resolve_unique` | A piece resolves to one thing, and a partial outcome to one outcome |
| `lazy_simulates`, `lazy_complete` | Hydration is invisible: for every number of plain steps the lazy machine reaches a state that resolves to the plain machine's state, and it halts with what the plain machine halts with |
| `lazy_sound` | A missing piece is a pause: under any part of the store, what the lazy machine halts with is what the plain machine halts with |
| `lazy_pause` | A run pauses only on a reference the store lacks, and under any store that holds more, the run from the start passes through the paused state |
| `lrun_mono` | More pieces change nothing |
| `lazy_agree` | Any substrate will do: two stores that agree wherever both hold a piece give the same result |
| `lazy_program` | A program run through any store has exactly the outcome direct evaluation gives it |
| `lazy_turn_complete`, `lazy_turn_sound` | A turn of the request driver from a stored continuation is a turn of the machine |

The lazy machine takes extra steps to fetch, so the agreement is not step for step: `lazy_simulates` says each plain state is reached, after at least as many lazy steps.

## What is assumed, not proved

- **A reference names one piece, for ever.** The store is a function and is only added to. A hash gives this up to collisions; signatures and attestations say who vouches for a piece. Both are the substrate's: the network interface, the enclave, identikey. A proof about the checker that verifies an attestation is worth having and is a separate change.
- **The byte form of a piece.** That is `add-wire-bytes` (`homoiconic-q59.12`). This change keeps the store in memory.

## What the substrate is then free to do

Anything that keeps the one assumption. Move pieces off the device and pull them back on read. Keep copies on several machines. Put a caching proxy in front. Split a piece with erasure coding. Hold many roots that share pieces, as snapshots and volumes do. None of it can change what a program computes; it can only change when a run pauses.

## Design notes

- **The machine does not write back.** A value on the stack that was fetched is held there. A variable lookup walks the environment and fetches what it passes each time; it does not replace the references in the environment. Remembering fetched pieces is the store's.
- **Copy-on-write comes from content.** A piece never looked at stays a reference. A piece that was fetched and not changed has the bytes it had, so a store keyed by content already holds it and saving writes nothing. Only new pieces are written. The kernel does not model this; it follows from references naming content.
- **Operations need their whole argument.** A case on data looks at one level and fetches one piece. An operation takes complete data, so its argument is fetched level by level until it is whole. Operations that work on partial data are not in this change.
- **Code is held whole.** A function's code is inside its piece and is not cut further.
- **The stack and the frame list are held whole.** Their values and environments can be references.
- **Captured scope is the whole scope.** A function keeps every value visible where it was made. Because those are references once stored, an unused one costs a reference, not a fetch.
- **A program cannot hold or make a reference.** References exist below the language. This keeps P12 open to a later proof and keeps persistence orthogonal.
- **A store with a cycle** resolves nothing that reaches the cycle, so the theorems do not apply to such a state. A lazy run on one may fetch for ever.
- **Nothing is deleted.** Which pieces are no longer reachable from any kept root, and reclaiming them, is the substrate's.
- **The check does not share pieces.** It cuts a state as a tree, so a value held in two places is stored twice; one example gives over a million pieces. Storing by content removes this, and needs bytes.

## Not in this change

- Hashing, bytes, files, the network, synchronization, erasure coding
- Signatures and attestations
- The event log (P13 as a fold over events, P14)
- Garbage collection
- Trimming a function's captured values to the ones it uses
- A program-visible way to save, load, or name state
- Storing state on disk from the `ask` command; that follows `add-wire-bytes`
- An executable driver over stored state. The theorems cover each turn; `converse` still runs in memory
- A bound on the number of fetch steps

## Impact

- Capabilities: ADDED `state-store`
- New files: `kernel/Reflect/Store.lean`, `kernel/Reflect/StoreProof.lean`, `kernel/StoreContract.lean`, `kernel/StoreCheck.lean`
- `kernel/Reflect.lean` imports the two modules; `host/check.sh` runs the contract and the check
- `kernel/Reflect/Machine.lean`, the existing machine theorems, `ReflectContract.lean`, `MachineContract.lean` and `RequestContract.lean` are not edited
- `ARCHITECTURE.md`, `kernel/README.md`, `docs/PROOFS.md`: amended at fold

## User journey & surfaces

No new UI because the store is in memory and has no command yet. What can be seen is `kernel/StoreCheck.lean`, run by `host/check.sh`:

- **Working** — eight programs are each stopped after 0, 7, 40 and 300 machine steps, cut at every value, and continued by the lazy machine with the whole store. Each gives what the plain machine gives.
- **Partial** — each is run again with one piece withheld, for a spread of pieces. It either finishes the same or pauses needing exactly that piece, and continued with the piece it finishes the same.
- **Kept** — a program waiting on its second request is cut into 15 pieces and continued from its root with the answer 22. It gives 42.
- **Failed** — a line that starts with `FAIL`: a different result, a pause on some other reference, or `wrong` for a missing piece.

## Out of scope

Listed under "Not in this change".
