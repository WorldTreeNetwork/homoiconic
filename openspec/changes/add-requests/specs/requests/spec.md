# requests

What is built: a program can ask the outside for something and continue from the answer. A request is a function value that holds a payload and the rest of the program. A driver outside the program answers requests from a list. The definitions are in `kernel/Reflect/Request.lean`, the proofs in `kernel/Reflect/RequestProof.lean`, and the exact statements in `kernel/RequestContract.lean`.

## Purpose

State what a request is, what a run against a list of answers is, and what is proved about it. This spec does not say what a payload means.

## ADDED Requirements

### Requirement: A request is a value

A request SHALL be a function value of the existing language. `ask payload next` SHALL be the closed term `askTerm`, a function that hands `payload` and `next` to its caller. No term, value, outcome, evaluation rule, interpreter branch or machine instruction SHALL be added for requests.

#### Scenario: Asking adds nothing to the language

- GIVEN the definitions of `Term`, `Value`, `Outcome`, `Direct`, `interp` and `step`
- WHEN this change lands
- THEN none of them has changed

### Requirement: A driver runs a program against answers

A run SHALL start from the result of evaluating the program and SHALL proceed by turns. A result that is not a function SHALL end the run with that result. A result that is a function SHALL be read as a request: its payload is evaluated, and a payload that is data SHALL be recorded as asked. A payload that is an error SHALL end the run with that error, and a payload that is a function SHALL end the run as `wrong`. With no answer left the run SHALL end waiting, holding the request. Otherwise the rest of the program SHALL run on the next answer, and its result is the next turn. Answers left over when a run ends SHALL be unused. A turn that never finishes SHALL give the run no ending.

#### Scenario: Two requests

- GIVEN the program in `examples/ask.hom` and the answers 20 and 22
- WHEN it is run
- THEN it asks `[1]`, then `[2, 20]`, and finishes with 42

#### Scenario: Waiting

- GIVEN the same program and the one answer 20
- WHEN it is run
- THEN it asks `[1]`, then `[2, 20]`, and is waiting

#### Scenario: A function that is not a request

- GIVEN the program `fn x -> x`
- WHEN it is run against any answers
- THEN the run ends as `wrong`

### Requirement: A run is a function of the program and the answers

For every operation table, a program and a list of answers SHALL have at most one list of requests and one ending (`interact_deterministic`). A waiting run continued with an answer SHALL be the run from the start with that answer, and the ones after it, added (`interact_resume`). A finished run SHALL be unchanged by more answers (`interact_extra`).

#### Scenario: Replay

- GIVEN `Interact p answers asked e` and `Interact p answers asked' e'`
- WHEN `kernel/RequestContract.lean` is checked
- THEN `asked = asked'` and `e = e'`

### Requirement: The interpreter asks what the program asks

For every operation table and every program, the run by direct evaluation and the run in which every evaluation is done by the interpreter on data SHALL make the same requests in the same order, and SHALL end the same way up to the data form of the ending (`interact_reflective`). Every interpreted run SHALL be the data form of a run of the program (`interact_coverage`). The statements SHALL have no condition on the program.

#### Scenario: Interpreted requests

- GIVEN any program `p`, answers, requests and ending
- WHEN `kernel/RequestContract.lean` is checked
- THEN `Interact p answers asked e ↔ InteractI p answers asked (e.map reifyOutcome reifyValue)` holds

### Requirement: The machine asks what the program asks

For every operation table and every program, the run on the machine SHALL make the same requests in the same order and SHALL end with the compiled form of the same ending (`interact_machine`, `interact_machine_exact`). What the executable driver `converse` reports as finished or as waiting SHALL be a run of the program by direct evaluation with exactly those requests (`converse_finished`, `converse_waiting`). `converse` SHALL give each turn its own step budget, and SHALL report a turn that does not halt within it as unfinished, which claims nothing.

#### Scenario: The driver's report is true

- GIVEN `converse budget p answers = (asked, .finished x)`
- WHEN `kernel/RequestContract.lean` is checked
- THEN there is an outcome `o` with `x` its compiled form and `Interact p answers asked (.finished o)`

### Requirement: The request theorems depend on the logic only

`kernel/RequestContract.lean` SHALL state each theorem for every operation table, SHALL NOT import a table, and SHALL print each theorem's axioms. The axioms SHALL be among `propext`, `Classical.choice` and `Quot.sound`.

#### Scenario: Axioms

- GIVEN the built kernel
- WHEN `lake env lean RequestContract.lean` runs
- THEN it exits 0 and prints no axiom outside those three
