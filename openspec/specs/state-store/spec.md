# state-store

What is built: a running program's state can be held in pieces, in a store that may lack any of them. A lazy machine runs a partial state, fetches a piece when a step first looks at it, and pauses when the store lacks it. The kind of reference is a parameter. The definitions are in `kernel/Reflect/Store.lean`, the proofs in `kernel/Reflect/StoreProof.lean`, and the exact statements in `kernel/StoreContract.lean`.

## Purpose

State what a piece, a store and a partial state are, what the lazy machine does with them, and what is proved about it. This spec does not say how a reference is made or checked, nor how a piece is written as bytes.

## Requirements

### Requirement: State can be held in pieces

A piece SHALL be a number, an empty list, a pair, a function, or a reference, and any part of a piece MAY be a reference. A store SHALL map references to pieces and MAY lack any reference. The kind of reference SHALL be a parameter of every definition and theorem. A machine state held whole SHALL resolve to itself under every store. A piece held in the store SHALL be replaceable by its reference without changing what resolves. A piece SHALL resolve to at most one thing.

#### Scenario: Cut and resolve

- GIVEN a machine state cut at every value into a store
- WHEN its pieces are resolved
- THEN the result is the state that was cut

### Requirement: A program cannot tell that its state is stored

The lazy machine SHALL fetch a referenced piece when a step has to look at it. For a partial state that resolves to a state `s`, and for every number of steps `n`, the lazy machine with the whole store SHALL reach a state that resolves to the plain machine's state after `n` steps from `s`. A program run through any store SHALL have exactly the outcome direct evaluation gives it. No term, value, outcome or evaluation rule of the language SHALL mention a reference.

#### Scenario: The same result from stored state

- GIVEN a program stopped after some steps and cut at every value
- WHEN the lazy machine continues it with the whole store
- THEN it halts with what the plain machine halts with

### Requirement: A missing piece is a pause

When a step needs a reference the store lacks, the lazy run SHALL pause, holding that reference and the state it stopped in. A pause SHALL NOT be an outcome and SHALL NOT be reported as `wrong`. Under any part of a store, what the lazy machine halts with SHALL be what the plain machine halts with. Under any store that holds more, the run from the start SHALL pass through the paused state. Adding pieces to a store SHALL change no run that did not pause, and two stores that agree wherever both hold a piece SHALL give the same result.

#### Scenario: Withheld, then supplied

- GIVEN a stored program and a store with one needed piece withheld
- WHEN it is run, and then continued from where it paused with the whole store
- THEN it first pauses needing that piece's reference and then halts with the result of the whole run

#### Scenario: A piece that is never looked at

- GIVEN a stored program and a store with a piece withheld that no step looks at
- WHEN it is run
- THEN it halts with the result of the whole run

### Requirement: A waiting run can be kept

A turn of the request driver run by the lazy machine from a stored continuation SHALL halt with what the machine's turn on that continuation halts with, and under any part of the store SHALL halt with nothing else.

#### Scenario: Continue from a root

- GIVEN `ask [1] (fn x -> ask [2, x] (fn y -> add x y))` run with the one answer 20, and the waiting program cut into a store
- WHEN the rest is run from its root with the answer 22
- THEN it gives 42

### Requirement: What a reference means is assumed

That a reference names one piece and never another SHALL be a stated hypothesis: a store is a function, a larger store holds the same piece under every reference the smaller one holds, and two stores are compared only when they agree wherever both hold a piece. How references are made and checked SHALL be outside the kernel.

#### Scenario: The hypothesis is visible

- GIVEN `kernel/StoreContract.lean`
- WHEN a theorem relates two stores
- THEN it states `σ.le τ` or `σ.Compatible τ`
