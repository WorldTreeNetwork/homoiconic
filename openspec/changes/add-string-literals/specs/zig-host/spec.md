## ADDED Requirements

### Requirement: A command prints a result as text

The run command SHALL accept `--text` before the file path, in any order with `--bytes` and `--interp`. With it, a result that is an array in which every item is the code point of a tab, a line feed, or a character from the space up other than delete SHALL be written as the text those code points spell, by the kernel, and every other outcome SHALL be written as it is without the flag. Zig SHALL NOT read the answer.

#### Scenario: A calculator answers in text

- GIVEN `examples/calc.hom`
- WHEN the command is run on it with `--text`, and with `--text --interp`
- THEN both print `2 * (3 + 4) * 5 - 100 / (7 - 2) = 50`

#### Scenario: A result that is not text is unchanged

- GIVEN `examples/append.hom`, whose result is `[1, 2, 3, 4]`
- WHEN the command is run on it with `--text`
- THEN it prints `[1, 2, 3, 4]`
