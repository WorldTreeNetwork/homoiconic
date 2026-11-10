# surface-syntax

What is built: a Lean library, `Surface`, in the kernel package beside `Reflect`. `Surface.read` takes program text to a `Reflect` term, resolving names to de Bruijn indices and refusing unbound names, tabs in indentation, and malformed blocks. `Surface.render` prints outcomes as plain text. Both are tested against the examples in `kernel/Surface/Expect.lean` and are not proved. The export `reflect_run` runs what the reader produced on the machine in `openspec/specs/bytecode-machine/spec.md`; the host call is `openspec/specs/zig-host/spec.md`. The reader resolves `ask` as a built-in name for the request term of `openspec/specs/requests/spec.md`, and `Surface.converseText` runs a program against an answers text for the export `reflect_converse`. The syntax, its examples, and the programs these scenarios name are in `openspec/changes/archive/2026-11-10-move-host-to-reflect/design.md`.

## Purpose

Name the text people write `Reflect` programs in, and the text outcomes print as. This spec does not contain the language or the interpreter theorem (`openspec/specs/code-as-data/spec.md`), the machine (`openspec/specs/bytecode-machine/spec.md`), or the host call (`openspec/specs/zig-host/spec.md`).

## Requirements

### Requirement: Programs are written with names and indentation

The kernel package SHALL define a reader, in Lean, from program text to `Reflect` terms. Application SHALL be juxtaposition. Lines indented under a line SHALL continue it. Functions SHALL be written `fn x -> body`, bindings `let x = value` and `def f x = body`, arrays `[a, b, ...rest]`, and the successor `e + 1`. Data SHALL be taken apart by `case` with arms `pattern -> body`, where a pattern is `0`, `m + 1`, `[]`, `[head, ...tail]`, a name, or `_`. Names SHALL be resolved to de Bruijn indices by the reader. A program that uses an unbound name SHALL be refused and SHALL NOT be run.

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

The package SHALL define a rendering of outcomes as text. A number SHALL render as its decimal digits. An array SHALL render in brackets with items separated by a comma and a space. Rendered data SHALL read back, as a bracket literal, to the same data. A function SHALL render as `<function>`. `unbound i` and `wrong` SHALL render as errors that say which.

#### Scenario: Data round-trips through text

- GIVEN the data `[1, 2, [3, 4]]`
- WHEN it is rendered and the text is read as a program
- THEN the program's outcome is the data `[1, 2, [3, 4]]`

### Requirement: Operations have names

The reader SHALL resolve the names `add`, `sub`, `mul`, `div`, `mod`, `equal`, and `less` to functions of two arguments that run operations 0 to 6 on the two-item array of their arguments, and the name `op` to the function of an operation number and an argument that runs that operation. A binding of the same name in the program SHALL take precedence. Each is an ordinary function, so both of its arguments are evaluated before the operation runs. These names SHALL be usable inside a quotation, where each stands for the code of its function. The reader SHALL NOT read infix operators other than the successor `e + 1`.

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

The reader and the renderer SHALL be tested against examples. They SHALL NOT be cited as proved. What is run SHALL be the term the reader produced, on the machine in `openspec/specs/bytecode-machine/spec.md`.

#### Scenario: The proof boundary is stated

- GIVEN a result printed by the host
- WHEN someone asks what is proved about it
- THEN the answer is that the machine's outcome for the term read is the term's outcome, and that the reading and the printing are tested
