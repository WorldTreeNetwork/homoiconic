# state-store

## MODIFIED Requirements

### Requirement: A turn runs against a store it is handed piece by piece
<!-- base: 14bfc6e6bfdba2b800c9965d3f5f455d448ac5d5 openspec/specs/state-store/spec.md -->

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
