## MODIFIED Requirements

### Requirement: A command prints a result as text
<!-- base: 07350ca931ece62fd2f9ef8b3457f24248f2eb89 openspec/specs/zig-host/spec.md -->

The run command SHALL accept `--text` before the file path, in any order with `--bytes` and `--interp`. With it, the command SHALL call `reflect_interp`, at level 0 unless `--interp` gives the levels, with bit 1 of `flags` set. A result that is a text SHALL be written as that text, with no quotes and no escapes, by the kernel, and every other outcome SHALL be written as it is without the flag. An array of code points is not a text and SHALL be written as an array. Zig SHALL NOT read the answer.

#### Scenario: A calculator answers in text

- GIVEN `examples/calc.hom`, whose result is made a text with `text`
- WHEN the command is run on it with `--text`, and with `--text --interp`
- THEN both print `2 * (3 + 4) * 5 - 100 / (7 - 2) = 50`

#### Scenario: A result that is not text is unchanged

- GIVEN `examples/append.hom`, whose result is `[1, 2, 3, 4]`
- WHEN the command is run on it with `--text`
- THEN it prints `[1, 2, 3, 4]`

#### Scenario: Without the flag a text prints in quotes

- GIVEN a program whose result is the text `hé →`
- WHEN the command is run on it without `--text`, and with it
- THEN the first prints `"hé →"` and the second prints `hé →`
