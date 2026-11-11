# state-store

## ADDED Requirements

### Requirement: State can be held in pieces

A partial value SHALL be a value in which any sub-value may be a reference. A store SHALL map references to partial values and MAY lack any reference. The kind of reference SHALL be a parameter of every definition and theorem. Saving a state SHALL be allowed to cut it at any sub-value, and a state cut in any way SHALL resolve, under the store that holds its pieces, to the state that was saved.

#### Scenario: Save and resolve

- GIVEN any machine state and any choice of where to cut it
- WHEN it is saved and its root is resolved
- THEN the result is the state that was saved

### Requirement: A program cannot tell that its state is stored

The lazy machine SHALL fetch a referenced value when a step has to look at it. For a partial state that resolves to a state `s`, every state the lazy machine reaches SHALL resolve to the state the plain machine reaches from `s` in the same number of steps. No term, value, outcome or evaluation rule of the language SHALL mention a reference.

#### Scenario: The same result from stored state

- GIVEN an example program whose compiled state is cut at every value
- WHEN the lazy machine runs it with the whole store
- THEN it halts with what the plain machine halts with

### Requirement: A missing piece is a pause

When a step needs a reference the store lacks, the lazy machine SHALL stop as needing that reference. Needing SHALL NOT be an outcome and SHALL NOT be reported as `wrong`. A run continued after the piece is added SHALL give what an uninterrupted run with the whole store gives. Adding pieces to a store SHALL change no result, and two stores that agree wherever both hold a piece SHALL give the same results.

#### Scenario: Withheld, then supplied

- GIVEN a stored program and a store with one needed piece withheld
- WHEN it is run, the piece is added, and the run is continued
- THEN it first stops needing that piece's reference and then halts with the result of the whole run

#### Scenario: A piece that is never looked at

- GIVEN a stored program that captures a value it never uses, with that value's piece withheld
- WHEN it is run
- THEN it halts with the result of the whole run

### Requirement: A waiting run can be kept

The request driver SHALL be able to end a waiting run with the root of the waiting program, and to continue from a root with further answers. A run saved and continued with an answer SHALL be the program run from the start with that answer added.

#### Scenario: Continue from a root

- GIVEN `examples/ask.hom` run with the one answer 20 and saved while waiting
- WHEN it is continued from its root with the answer 22
- THEN it finishes with 42

### Requirement: What a reference means is assumed

That a reference names one piece and never another SHALL be a stated hypothesis of the theorems: the store is a function and is only added to. How references are made and checked SHALL be outside the kernel.

#### Scenario: The hypothesis is visible

- GIVEN `kernel/StoreContract.lean`
- WHEN a theorem compares two stores
- THEN it states that they agree wherever both hold a piece
