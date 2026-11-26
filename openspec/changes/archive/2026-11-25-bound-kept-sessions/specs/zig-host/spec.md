# zig-host

## MODIFIED Requirements

### Requirement: A command runs one turn with the program's state in a directory
<!-- base: 0049526bc3d762f3a7783d1c534d597c58f147de openspec/specs/zig-host/spec.md -->

The host SHALL provide a command that takes a store directory and either `start` with a program file, or `answer` with a root and an answer file, and an optional step budget. It SHALL read from the directory the file named by each piece the kernel asks for and pass its bytes to the kernel. It SHALL write each piece the kernel hands back to a file with the name the kernel gives, before printing. It SHALL print the kernel's text and a newline. The kernel runs the turn under the default space with the runtime's count (`reflect_keep_start` and `reflect_keep_answer`, `bound-kept-sessions`); the command takes no new argument, and the space lines are the kernel's text. The host SHALL NOT read, hash or name a piece. It SHALL exit 0 whenever the kernel answered. It SHALL exit 3, print one line on standard error and write nothing when the directory lacks a piece the turn needs. It SHALL exit 2 with a message on standard error for a wrong call, a file or directory it cannot read, or a file it cannot write.

#### Scenario: A program is kept between calls

- GIVEN `examples/keep.hom` and an empty directory
- WHEN it is started, answered with 20 from the root printed, and answered with 22 from the next root, each in its own call
- THEN the calls print `asked: [1]`, `asked: [2, 20]` and `[2000, 42]`

#### Scenario: A root can be answered again

- GIVEN the first root of that run
- WHEN it is answered with 30 and the next root with 22
- THEN the last call prints `[2000, 52]`, and fewer than ten files were added

#### Scenario: A piece is missing

- GIVEN a root whose file has been moved out of the directory
- WHEN it is answered
- THEN the command prints nothing on standard output, names the piece on standard error, and exits 3

#### Scenario: A piece was changed

- GIVEN a root whose file has a byte added
- WHEN it is answered
- THEN the command prints `store error: piece <name> does not match its name` and exits 0

#### Scenario: A kept turn out of space

- GIVEN `def deep x = [x, ...deep x]` applied to 0
- WHEN the command starts it with the default budget
- THEN it prints `no result within 4000000 cells of a turn` and exits 0, under 256 MiB (`host/check.sh`)
