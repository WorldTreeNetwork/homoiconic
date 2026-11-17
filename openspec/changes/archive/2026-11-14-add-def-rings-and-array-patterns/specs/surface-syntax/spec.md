## MODIFIED Requirements

### Requirement: Programs are written with names and indentation
<!-- base: d5a02d8b50051f86d14c59f977b2d86756edce4e openspec/specs/surface-syntax/spec.md -->

The kernel package SHALL define a reader, in Lean, from program text to `Reflect` terms. Application SHALL be juxtaposition. Lines indented under a line SHALL continue it. Functions SHALL be written `fn x -> body`, bindings `let x = value` and `def f x = body`, arrays `[a, b, ...rest]`, and the successor `e + 1`. Data SHALL be taken apart by `case` with arms `pattern -> body`, where a pattern is `0`, `m + 1`, an array pattern, a name, or `_`. Names SHALL be resolved to de Bruijn indices by the reader. A program that uses a name that is not bound and that no later definition of its run defines SHALL be refused and SHALL NOT be run.

#### Scenario: Recursion by name

- GIVEN the text of the countdown program in the change's design, applied to `1000`
- WHEN it is read and run
- THEN the outcome is the number `0`

#### Scenario: An unknown name is refused

- GIVEN the text `f 1`, where `f` is not bound
- WHEN it is read
- THEN the reader reports a syntax error naming `f`, and nothing is run

## ADDED Requirements

### Requirement: Definitions of a run name one another

A run SHALL be the `def`s of one block with no `let` between them. In a definition of a run, a name that is not bound where it is used and that a later `def` of the same run defines SHALL refer to that definition, and to the nearest of them when more than one defines it. A name that is bound where it is used, by a parameter, an enclosing or earlier binding, or a name the reader resolves itself, SHALL keep that meaning, so a program that read before this requirement SHALL read to the same term. A definition that mentions no later definition and is mentioned by none in a ring SHALL be bound as a function, under the fixed point when it mentions itself. Definitions that mention one another in a ring SHALL be bound by one recursive function of a number that chooses the member. A definition above a `let` SHALL NOT see a definition below it. A quotation SHALL NOT mention a later definition, and a splice inside it MAY.

#### Scenario: Two definitions in a ring

- GIVEN `def even n` whose arm for `m + 1` is `odd m`, then `def odd n` whose arm for `m + 1` is `even m`, then `[even 10, odd 10, even 7, odd 7]`
- WHEN the host runs it, directly and through the interpreter
- THEN the printed text is `[1, 0, 0, 1]` both ways

#### Scenario: A bound name is not a later definition

- GIVEN `def f x = add x 1`, then `def add a b = 99`, then `[f 1, add 1 1]`
- WHEN it is read and run
- THEN the outcome is `[2, 99]`

#### Scenario: A let ends a run

- GIVEN `def f x = g x`, then `let y = 1`, then `def g x = 8`, then `f 1`
- WHEN it is read
- THEN the reader reports a syntax error naming `g`, and nothing is run

#### Scenario: A parser whose parts need one another

- GIVEN `examples/calc.hom`, in which `factor` names `expr` and `expr` is defined four definitions later
- WHEN the host runs it with `--text`, directly and through the interpreter
- THEN both print `2 * (3 + 4) * 5 - 100 / (7 - 2) = 50`

### Requirement: An array pattern names a length

An array pattern SHALL be `[]`, or names or `_` separated by commas in brackets, and MAY end in `, ...rest` after at least one item. Without `...rest` it SHALL take an array of exactly as many items as it names, and with it an array of at least that many, `rest` being the array of the items after them. The array arms of a `case` SHALL be tried in the order written. A scrutinee that is an array no arm takes SHALL go to the catch-all arm when the `case` has one, the catch-all's name being the whole array, and otherwise the `case` SHALL be `wrong`, as for any scrutinee with no arm. A name written twice in a pattern SHALL be the later one. The reader SHALL refuse an item that is not a name or `_`, a `...rest` that is first or is not last, two arms that take the same lengths, and an arm below an arm that takes every array it would.

#### Scenario: Exactly three items

- GIVEN `case [1, 2, 3]` with the arm `[a, b, c] -> [c, b, a]`
- WHEN the host runs it, directly and through the interpreter
- THEN the printed text is `[3, 2, 1]` both ways

#### Scenario: Another length goes to the catch-all arm

- GIVEN `case [1, 2]` with the arms `[a, b, c] -> [c, b, a]` and `other -> [9, ...other]`
- WHEN the host runs it
- THEN the printed text is `[9, 1, 2]`

#### Scenario: Another length with no catch-all arm is wrong

- GIVEN `case [1, 2]` with the one arm `[a, b, c] -> [c, b, a]`
- WHEN the host runs it
- THEN the printed text is `error: wrong`

#### Scenario: At least two items

- GIVEN `case [1, 2, 3, 4]` with the arm `[a, b, ...rest] -> [b, a, rest]`
- WHEN it is read and run
- THEN the outcome is `[2, 1, [3, 4]]`

#### Scenario: A pattern inside a pattern is refused

- GIVEN `case [1, 2]` with the arm `[a, [b]] -> a`
- WHEN it is read
- THEN the reader reports a syntax error at the inner bracket, and nothing is run
