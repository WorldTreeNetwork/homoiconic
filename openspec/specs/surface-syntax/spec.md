# surface-syntax

What is built: a Lean library, `Surface`, in the kernel package beside `Reflect`. `Surface.read` takes program text to a `Reflect` term, resolving names to de Bruijn indices and refusing unbound names, tabs in indentation, and malformed blocks. `Surface.render` prints outcomes as plain text. Both are tested against the examples in `kernel/Surface/Expect.lean` and are not proved. The export `reflect_run` runs what the reader produced on the machine in `openspec/specs/bytecode-machine/spec.md`; the host call is `openspec/specs/zig-host/spec.md`. The reader resolves `ask` as a built-in name for the request term of `openspec/specs/requests/spec.md`, and `Surface.converseText` runs a program against an answers text for the export `reflect_converse`. The reader takes `"..."` as the literal of a text, a kind of data that `case` takes apart as the list of its code points, and `'c'` as the number of one ASCII character; `text` and `codes` are built-in names of one argument (`openspec/changes/archive/2026-11-17-add-data-kinds/`). The renderer writes a text in double quotes with four escapes, which reads back, and a name as `#n`, which the reader refuses. `Surface.renderMOutcomeText` writes a result that is a text raw, for `host/out/run --text`; an array is no longer taken for text. An array pattern on a text takes code points as its items and a text as its rest. The `def`s of a run can name later ones: the reader binds each after what it mentions and reads a ring as `recur` applied to one function of a number that chooses the member. A `case` arm can take an array of a fixed length or a least length, read as nested `dcase`; a catch-all arm that no branch falls to is not read. No term or operation was added for either (`openspec/changes/archive/2026-11-14-add-def-rings-and-array-patterns/`). The syntax, its examples, and the programs these scenarios name are in `openspec/changes/archive/2026-11-10-move-host-to-reflect/design.md`.

## Purpose

Name the text people write `Reflect` programs in, and the text outcomes print as. This spec does not contain the language or the interpreter theorem (`openspec/specs/code-as-data/spec.md`), the machine (`openspec/specs/bytecode-machine/spec.md`), or the host call (`openspec/specs/zig-host/spec.md`).

## Requirements

### Requirement: Programs are written with names and indentation

The kernel package SHALL define a reader, in Lean, from program text to `Reflect` terms. Application SHALL be juxtaposition. Lines indented under a line SHALL continue it. Functions SHALL be written `fn x -> body`, bindings `let x = value` and `def f x = body`, arrays `[a, b, ...rest]`, and the successor `e + 1`. Data SHALL be taken apart by `case` with arms `pattern -> body`, where a pattern is `0`, `m + 1`, an array pattern, a name, or `_`. Names SHALL be resolved to de Bruijn indices by the reader. A program that uses a name that is not bound and that no later definition of its run defines SHALL be refused and SHALL NOT be run.

#### Scenario: Recursion by name

- GIVEN the text of the countdown program in the change's design, applied to `1000`
- WHEN it is read and run
- THEN the outcome is the number `0`

#### Scenario: An unknown name is refused

- GIVEN the text `f 1`, where `f` is not bound
- WHEN it is read
- THEN the reader reports a syntax error naming `f`, and nothing is run

### Requirement: Quotation is written in the syntax

`quote e` SHALL denote the data that is `reify` of the term `e` reads as. Inside a quotation, `~e` SHALL place the code that `e` evaluates to at that position. A quotation that mentions a name bound outside it, or a splice enclosed by a binder of its quotation, SHALL be refused.

#### Scenario: A quoted function is its code

- GIVEN the text `quote (fn x -> x)`
- WHEN it is read and run
- THEN the outcome is the data `[1, 0]`

#### Scenario: Code with a hole is filled and run

- GIVEN a program that binds `inner` to `quote 41` and applies `interpret` to `quote (~inner + 1)`
- WHEN it is read and run
- THEN the outcome is the data `[0, [1, 42]]`

#### Scenario: A splice under a binder is refused

- GIVEN the text `quote (fn x -> ~y)` with `y` bound outside
- WHEN it is read
- THEN the reader reports a syntax error, and nothing is run

### Requirement: Outcomes render as plain text

The package SHALL define a rendering of outcomes as text. A number SHALL render as its decimal digits. An array SHALL render in brackets with items separated by a comma and a space. A text SHALL render between double quotes, with a line feed, a tab, a backslash and a double quote written `\n`, `\t`, `\\` and `\"` and every other character as itself. A name SHALL render as `#` followed by the decimal digits of its number. Rendered data that holds no name SHALL read back, as a literal, to the same data. The reader SHALL NOT read `#`, so rendered data that holds a name does not read. A function SHALL render as `<function>`. `unbound i` and `wrong` SHALL render as errors that say which.

#### Scenario: Data round-trips through text

- GIVEN the data `[1, 2, [3, 4]]`
- WHEN it is rendered and the text is read as a program
- THEN the program's outcome is the data `[1, 2, [3, 4]]`

#### Scenario: Text round-trips through text

- GIVEN the array of the number 1 and a text that holds a double quote, a backslash, a line feed and `é`
- WHEN it is rendered and the rendering is read as a program
- THEN the program's outcome is that array

#### Scenario: A name does not read

- GIVEN the text `#3`
- WHEN it is read as a program
- THEN the reader reports a syntax error, and nothing is run

### Requirement: Operations have names

The reader SHALL resolve the names `add`, `sub`, `mul`, `div`, `mod`, `equal`, and `less` to functions of two arguments that run operations 0 to 6 on the two-item array of their arguments, the names `text` and `codes` to functions of one argument that run operations 7 and 8 on that argument, and the name `op` to the function of an operation number and an argument that runs that operation. A binding of the same name in the program SHALL take precedence. Each is an ordinary function, so its arguments are evaluated before the operation runs. These names SHALL be usable inside a quotation, where each stands for the code of its function. The reader SHALL NOT read infix operators other than the successor `e + 1`.

#### Scenario: Arithmetic by name

- GIVEN the program `mul (add 2 3) (sub 9 5)`
- WHEN the host runs it
- THEN the printed text is `20`

#### Scenario: A program's own name wins

- GIVEN `let add = fn a b -> a` followed by `add 7 8`
- WHEN the host runs it
- THEN the printed text is `7`

#### Scenario: An operation inside quoted code

- GIVEN `interpret (quote (add 2 3))`
- WHEN the host runs it
- THEN the printed text is `[0, [1, 5]]`

#### Scenario: Text from code points by name

- GIVEN the program `text [104, ...codes "i"]`
- WHEN the host runs it
- THEN the printed text is `"hi"`

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

### Requirement: The reader and renderer are not part of the proof

The reader and the renderer SHALL be tested against examples. They SHALL NOT be cited as proved. That the printer the compiled kernel runs is `renderData`, a walk with its work in a list, is proved (`renderData_eq_walk`); what `renderData` prints is tested. What is run SHALL be the term the reader produced, on the machine in `openspec/specs/bytecode-machine/spec.md`.

#### Scenario: The proof boundary is stated

- GIVEN a result printed by the host
- WHEN someone asks what is proved about it
- THEN the answer is that the machine's outcome for the term read is the term's outcome, and that the reading and the printing are tested

### Requirement: Text is written in quotes

The reader SHALL read `"..."` as the literal of the text between the quotes, and `'c'` as the number of one ASCII character. Inside either, `\n`, `\t`, `\\`, `\"` and `\'` SHALL stand for a line feed, a tab, a backslash, a double quote and a single quote, and any other backslash SHALL be refused. A string SHALL be UTF-8, so the text holds Unicode scalar values, and SHALL end on the line it begins on. A string is a text, not an array: a program SHALL be able to tell it from the array of the same code points by `equal`, and SHALL take it apart by `case` as it takes that array apart, with each head a number. A character literal SHALL stay a number, so that it can be compared with a head.

#### Scenario: A string is a text

- GIVEN the text `"h\\i\n"`
- WHEN it is read and run
- THEN the printed text is `"h\\i\n"`, and `equal "h\\i\n" [104, 92, 105, 10]` gives 0

#### Scenario: A string is taken apart like its code points

- GIVEN a program that counts, by `case`, the items of `"h\\i\n"` that `equal` the character literal `'i'`
- WHEN it is read and run
- THEN the outcome is 1

#### Scenario: A string that does not end is refused

- GIVEN a line that opens a string and does not close it
- WHEN it is read
- THEN the reader reports a syntax error at the opening quote, and nothing is run

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
