# state-store

What is built: a running program's state can be held in pieces, in a store that may lack any of them. A lazy machine runs a partial state, fetches a piece when a step first looks at it, and pauses when the store lacks it. The kind of reference is a parameter. A piece is a number, a text, a name, an empty list, a pair, a function or a reference; a text and a name are leaves, so the lazy machine takes a text apart, and sees a name as its number, with no fetch beyond the piece itself (`openspec/changes/archive/2026-11-17-add-data-kinds/`). The definitions are in `kernel/Reflect/Store.lean`, the proofs in `kernel/Reflect/StoreProof.lean`, and the exact statements in `kernel/StoreContract.lean`. A session runs one turn of a program against a store it is handed piece by piece, and saves the waiting program when the turn ends in a request (`kernel/Surface/Keep.lean`). There a reference is the Blake3 hash of a piece's bytes, and the session checks each piece it is given against the name it asked for. The command `host/out/keep` keeps the pieces as files in a directory (`openspec/specs/zig-host/spec.md`). The theorems still hold for every kind of reference, hashes among them. Saving stores a text whole, as one piece, when its byte form is larger than the size it cuts at. A state kept before text and names were kinds of data is not migrated: it still reads, and a number in it that was a channel name is now a plain number. The session is tested by `kernel/KeepCheck.lean` and `host/check.sh`, not proved.

## Purpose

State what a piece, a store and a partial state are, what the lazy machine does with them, what is proved about it, and what a session does to run one turn against a store. How a reference is made and how a piece is written as bytes are in `openspec/specs/wire-bytes/spec.md`.

## Requirements

### Requirement: State can be held in pieces

A piece SHALL be a number, a text, a name, an empty list, a pair, a function, or a reference, and any part of a pair or a function MAY be a reference. A text SHALL be one piece with no parts. A store SHALL map references to pieces and MAY lack any reference. The kind of reference SHALL be a parameter of every definition and theorem. A machine state held whole SHALL resolve to itself under every store. A piece held in the store SHALL be replaceable by its reference without changing what resolves. A piece SHALL resolve to at most one thing. The lazy machine SHALL take a text apart, and SHALL see a name as its number, with no fetch beyond the piece itself. The theorems of this spec SHALL hold with their statements unchanged by text and names, and `kernel/StoreContract.lean` SHALL check without having been edited.

#### Scenario: Cut and resolve

- GIVEN a machine state cut at every value into a store
- WHEN its pieces are resolved
- THEN the result is the state that was cut

#### Scenario: Text in stored state

- GIVEN a program stopped while it holds a text, and another stopped while it holds a name, each cut at every value
- WHEN the lazy machine continues each with the whole store, taking the text apart by `case` and the name by `case`, `succ` or as an operation number
- THEN each halts with what the plain machine halts with

#### Scenario: A withheld text is a pause

- GIVEN a stored program whose next step looks at a text, and a store with that text's piece withheld
- WHEN it is run
- THEN it pauses needing that piece's reference

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

That a reference names one piece and never another SHALL be a stated hypothesis: a store is a function, a larger store holds the same piece under every reference the smaller one holds, and two stores are compared only when they agree wherever both hold a piece. No theorem of this spec SHALL depend on how references are made or checked. References are made by hashing a piece's bytes and checked by the session that runs a turn (`openspec/specs/wire-bytes/spec.md`); both are Lean definitions, tested and not proved.

#### Scenario: The hypothesis is visible

- GIVEN `kernel/StoreContract.lean`
- WHEN a theorem relates two stores
- THEN it states `σ.le τ` or `σ.Compatible τ`

### Requirement: A turn runs against a store it is handed piece by piece

The kernel SHALL provide a session that runs one turn of a program on the lazy machine: the first turn from a program's source, or a later turn from the root of a waiting program and an answer. When the turn needs a piece the session does not hold, the session SHALL stop and name that piece, and SHALL continue from where it stopped when the piece is supplied. It SHALL refuse a supplied piece whose hash is not the name it asked for. When the turn ends in a request it SHALL save the waiting program and report the request's payload, the root, and the pieces to be stored, leaving out any piece it was supplied. When the turn ends in a result it SHALL report the result. The session is tested, not proved.

What a session walks besides its steps SHALL be bounded (`bound-kept-sessions`). A result, a payload, and a kept state's identifiers and results SHALL be read by `full`, a walk that counts units (`unit`: a number or a name five and its written digits, a text seven and four a character, an empty list two, a pair five, a reference one, a function one) and each reference it crosses, and refuses past `4 * cells` with the space line (`no result within <cells> cells of a turn`). A waiting program, a VM's state and a node SHALL be counted in the same units, a function's environment included, before they are saved, and one counted at more than `4 * cells` SHALL NOT be saved: `the waiting program is too large to keep within <cells> cells` or `the state is too large to keep within <cells> cells`. Saving walks a piece as a tree (`homoiconic-q59.24`), so its time is at most that many pieces and each function's code; a waiting program's environment doubles with each definition, so one of more than about 22 definitions is refused, which did not finish saving before. Reading a kept state SHALL admit `5 * cells` units, since it also crosses the references saving made. A VM's or node's identifiers are part of what is saved, so one that has acted on more than about 160000 entries cannot be kept; this is a lifetime limit. Each piece given restarts the walk the session was in, so a turn's time is bounded by its budget and the walks' limits for each piece supplied (`homoiconic-q59.88`). A VM and a node SHALL keep the identifiers they have acted on beside a hash set of them, so each entry is looked up once.

#### Scenario: Three turns are one run

- GIVEN a program that asks twice
- WHEN it is started, then answered from its root in a new session, then answered again from the new root in a third
- THEN the requests and the result are those of one run against both answers

#### Scenario: A turn reads only what it looks at

- GIVEN a waiting program that holds a long list its next turn does not use
- WHEN that turn runs
- THEN it is supplied fewer pieces than the list has, and hands back none of the list's pieces

#### Scenario: A large waiting program is saved, a larger one refused

- GIVEN a waiting program that holds a list of 500000 zeros, one that holds a nest of a million, and one that holds a list of a million zeros
- WHEN `host/out/keep` starts each
- THEN the first two print `asked: [1]` and a root, where the kernel before ended the process on a full stack in `Wire.cut`, and the third prints `the waiting program is too large to keep within 4000000 cells` (`host/check.sh`)

#### Scenario: A result too large to write

- GIVEN `fill 500 []` and a kept turn of 100 cells
- WHEN it is started
- THEN it gives `no result within 100 cells of a turn`, and with the space undone the list (`kernel/KeepCheck.lean`)
