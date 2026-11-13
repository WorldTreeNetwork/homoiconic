## ADDED Requirements

### Requirement: Text is written in quotes

The reader SHALL read `"..."` as the array of the code points of the text between the quotes, and `'c'` as the number of one ASCII character. Inside either, `\n`, `\t`, `\\`, `\"` and `\'` SHALL stand for a line feed, a tab, a backslash, a double quote and a single quote, and any other backslash SHALL be refused. A string SHALL be UTF-8 and SHALL end on the line it begins on. A string is an array: the reader SHALL NOT produce a value that a program can tell from the array of the same numbers.

#### Scenario: A string is its code points

- GIVEN the text `"h\\i\n"`
- WHEN it is read and run
- THEN the outcome is the data `[104, 92, 105, 10]`

#### Scenario: A string that does not end is refused

- GIVEN a line that opens a string and does not close it
- WHEN it is read
- THEN the reader reports a syntax error at the opening quote, and nothing is run
