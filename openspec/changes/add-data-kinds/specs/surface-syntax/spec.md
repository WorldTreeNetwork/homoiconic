## MODIFIED Requirements

### Requirement: Outcomes render as plain text
<!-- base: d5a02d8b50051f86d14c59f977b2d86756edce4e openspec/specs/surface-syntax/spec.md -->

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
<!-- base: d5a02d8b50051f86d14c59f977b2d86756edce4e openspec/specs/surface-syntax/spec.md -->

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

### Requirement: Text is written in quotes
<!-- base: d5a02d8b50051f86d14c59f977b2d86756edce4e openspec/specs/surface-syntax/spec.md -->

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
