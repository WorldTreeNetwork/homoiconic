# surface-syntax

## ADDED Requirements

### Requirement: Asking has a name

The reader SHALL resolve `ask` as a built-in name for the term `askTerm`. A binding of the same name in the program SHALL win. `Surface.converseText` SHALL read a program text and an answers text, where the answers text is a program whose result is an array and its items are the answers. It SHALL render one line `asked: <payload>` for each request, in order, followed by how the run ended: the outcome as `runText` renders it, `waiting`, or a line saying a turn had no result within the budget. An answers text that does not read SHALL render as `answers: ` followed by the syntax error, and one whose result is not an array as `answers: not an array`. These are tested against `Surface.converses`, not proved.

#### Scenario: Requests print in order

- GIVEN the program `ask [1] (fn a -> ask [2, a] (fn b -> add a b))` and the answers text `[20, 22]`
- WHEN `converseText` runs them
- THEN the text is `asked: [1]`, `asked: [2, 20]` and `42`, each on its own line

#### Scenario: An answer can be code

- GIVEN the program `ask 0 (fn code -> interpret code)` and the answers text `[quote (add 2 3)]`
- WHEN `converseText` runs them
- THEN the text is `asked: 0` and `[0, [1, 5]]`
