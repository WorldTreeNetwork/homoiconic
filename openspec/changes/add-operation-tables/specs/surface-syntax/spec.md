# surface-syntax

## ADDED Requirements

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
