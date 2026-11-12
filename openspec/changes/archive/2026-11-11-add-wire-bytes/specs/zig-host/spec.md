# zig-host

## ADDED Requirements

### Requirement: A command runs a program given as bytes

The run command SHALL accept `--bytes` before the file path. With it, the file SHALL be passed to `reflect_run_bytes` as a program in its byte form, and the command SHALL otherwise behave as it does for a source file. Bytes that are not the one form of a value, and a value that is no program, SHALL be the kernel's text and exit 0.

#### Scenario: The same answer from bytes

- GIVEN each example program and its byte form
- WHEN the command is run on the source, and with `--bytes` on the byte form
- THEN both print the same text

#### Scenario: Bytes in a longer form

- GIVEN a file holding the bytes `18 17`
- WHEN the command is run on it with `--bytes`
- THEN it prints `bytes error: a number or length is not in its shortest form` and exits 0

### Requirement: A command writes a program's byte form

The host SHALL provide a command that takes the path of a program file, passes its bytes to `reflect_source_bytes`, and writes the byte form that comes back to standard output, with nothing added. The host SHALL NOT make or inspect the byte form. On a syntax error it SHALL write nothing to standard output, write the kernel's text to standard error, and exit 1. It SHALL exit 2 with one line on standard error when it is called with the wrong number of arguments or cannot read the file.

#### Scenario: Three bytes

- GIVEN a file holding `fn x -> x`
- WHEN the command is run on it
- THEN standard output is the bytes `82 01 00`

#### Scenario: A syntax error

- GIVEN a file holding `fn x ->`
- WHEN the command is run on it
- THEN standard output is empty, standard error starts with `syntax error: `, and the exit is 1
