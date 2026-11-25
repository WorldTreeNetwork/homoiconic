# zig-host

What is built: a Zig host that passes one program's text, an output buffer, a step budget and a space, in cells, to the Lean export `reflect_run`. That export reads the surface syntax (`openspec/specs/surface-syntax/spec.md`), runs the proved machine (`openspec/specs/bytecode-machine/spec.md`) for at most the budget, and writes back a plain text rendering of the outcome. The host runs with the operation table `arith` (`openspec/specs/code-as-data/spec.md`). The host links the Lean object, calls the runtime initializer, and contains no evaluator and no reader. The command `host/out/run [--bytes] [--interp[=levels]] [--text] <program-file> [step-budget]`, built by `host/check.sh`, runs a program file through `reflect_run` and prints the answer. A second export, `reflect_converse`, runs a program against a list of answers (`openspec/specs/requests/spec.md`), and the command `host/out/ask <program-file> <answers-file> [step-budget]`, also built by `host/check.sh`, prints the requests it makes and how it ends. A third, `reflect_run_bytes`, runs a program given in its byte form (`openspec/specs/wire-bytes/spec.md`); `host/out/run --bytes` calls it. The export `reflect_interp` runs a program, from source or from its byte form, through a number of levels of the closed interpreter term `interp` (`openspec/specs/code-as-data/spec.md`) on the machine, reads the answer back, and can write a result that is a text raw, as its UTF-8 with no quotes or escapes (an array is written as an array); `host/out/run --interp[=levels]` and `host/out/run --text` call it. A fourth, `reflect_source_bytes`, evaluates nothing: it reads a program's source and gives its byte form, and the command `host/out/bytes <program-file>` writes that to standard output. The `reflect_keep_*` exports run one turn of a program against a store of pieces (`openspec/specs/state-store/spec.md`), and the command `host/out/keep <store-dir> start <program-file> [step-budget]` or `host/out/keep <store-dir> answer <root> <answer-file> [step-budget]` keeps a waiting program in a directory, one file per piece, named by the kernel. The export `reflect_channels` runs a program as the first of several processes that talk over channels (`openspec/specs/channels/spec.md`), and the command `host/out/chan <program-file> [schedule-file | -] [step-budget] [event-limit]`, also built by `host/check.sh`, prints the schedule it went through, each process, and how the run stopped. The exports `reflect_vm_start` and `reflect_vm_from` run a program against a log of identified entries (`openspec/specs/event-log/spec.md`), from its beginning or from a kept state, and the command `host/out/vm <store-dir> start <program-file> <log-file> [step-budget]` or `host/out/vm <store-dir> from <root> <log-file> [step-budget]`, also built by `host/check.sh`, prints where the program stands and the root of its state. The exports `reflect_node_start` and `reflect_node_from` apply a log of identified events to several processes (`openspec/specs/logged-processes/spec.md`), from a program or from a kept node, and the command `host/out/node <store-dir> start <program-file> <log-file> [step-budget]` or `host/out/node <store-dir> from <root> <log-file> [step-budget]`, also built by `host/check.sh`, prints each process and the root of the node. The export `reflect_reply_bytes` runs a program given in its byte form for at most a budget and gives the bounded-run reply bytes (`openspec/specs/wire-bytes/spec.md`) that the network image sends (`openspec/specs/unikernel-net/spec.md`). The `reflect_cross_*` exports are a guest of a run on two machines and the check of two guests' records (`openspec/specs/crossing/spec.md`); the network guests and `unikernel/out-net/cross-check` call them. The interpreter theorems are in `openspec/specs/code-as-data/spec.md` and the machine's in `openspec/specs/bytecode-machine/spec.md`. The append program is `examples/append.hom`; the identity and self-application programs these scenarios name are in `kernel/Surface/Expect.lean`.

## Purpose

Name the host call into the kernel. This spec does not restate the surface syntax, the machine, the interpreter theorems, or the language partition.

## Requirements

### Requirement: The host returns the kernel's result

The Zig host SHALL pass one program's bytes, an output buffer, and a step budget to the Lean export `reflect_run`. That export SHALL read the surface syntax, compile the term, and run the machine for at most the budget. It SHALL write the plain text rendering of the outcome and SHALL return the number of bytes that rendering needs. The Zig sources SHALL pass and print bytes. They SHALL NOT read the syntax and SHALL NOT case-split on terms to produce an outcome. `reflect_run` SHALL NOT answer with a numeric result code. The exports that evaluate SHALL be `reflect_run`, `reflect_converse`, `reflect_run_bytes`, `reflect_interp`, `reflect_keep_start`, `reflect_keep_answer`, `reflect_keep_give`, `reflect_channels`, `reflect_vm_start`, `reflect_vm_from`, `reflect_node_start`, `reflect_node_from`, `reflect_reply_bytes`, `reflect_cross_give`, `reflect_cross_work` and `reflect_cross_check`, and each SHALL be a Lean definition.

#### Scenario: Identity

- GIVEN a program that binds the identity function and applies it to itself
- WHEN the Zig check runs it through `reflect_run`
- THEN the printed text is `<function>`

#### Scenario: An unbound index is reported in full

- GIVEN the term `var 2147483647`, which no surface text reads as
- WHEN the Lean check compiles it, runs the machine, and renders the state
- THEN the text is `error: unbound 2147483647`, and it differs from the text for a run with no result

#### Scenario: Data comes back

- GIVEN the append program in `examples/append.hom`
- WHEN the host check runs it through the command
- THEN the printed text is `[1, 2, 3, 4]`

#### Scenario: A diverging term has no result

- GIVEN the program `let w = fn x -> x x` followed by `w w`
- WHEN the Zig check runs it with a finite budget
- THEN the printed text says there is no result within that many steps, and the call returns

#### Scenario: A malformed program is refused

- GIVEN text that is not a program
- WHEN the Zig check passes it
- THEN the printed text is a syntax error with a line and column, and nothing is run

#### Scenario: A zero byte does not end a program

- GIVEN the three bytes `4`, `2`, and zero
- WHEN the Zig check passes them
- THEN the printed text is a syntax error at column 3, not `42`

#### Scenario: Bytes past the length are not read

- GIVEN a buffer holding `42invalid` and a declared length of 2
- WHEN the Zig check passes it
- THEN the printed text is `42`

### Requirement: The host contains no evaluator

The Zig tree SHALL load the Lean exports and SHALL NOT define an evaluator or a reader.

#### Scenario: One evaluator

- GIVEN the Zig sources
- WHEN they are reviewed against the partition
- THEN every outcome comes from a Lean export, and no Zig source decides an outcome

### Requirement: The link is the proved object path

The host SHALL link by the object path recorded in `docs/spikes/lean-c-abi/`. The host SHALL call the Lean runtime initializer on the path that allocates. The build SHALL NOT depend on `dlopen`.

#### Scenario: The test links

- GIVEN the Lean object and the Zig object
- WHEN `leanc` links them and the Zig test runs
- THEN the test exits 0

### Requirement: A command runs a program file

The host SHALL provide a command that takes the path of a program file and an optional step budget. It SHALL pass the file's bytes and the budget to `reflect_run` and SHALL print the bytes that come back, followed by a newline, on standard output. With no budget given it SHALL use one hundred million steps. It SHALL exit 0 whenever the kernel answered and the answer was written, whatever the answer says: a value, an error outcome, a syntax error, and a run with no result are all the kernel's text. It SHALL exit 2 and print one line on standard error, which does not repeat the arguments, when it is called with the wrong number of arguments, when the budget is not a whole number, when the file cannot be read, or when the answer cannot be written. An answer longer than the first buffer SHALL be printed in full.

#### Scenario: A program file runs

- GIVEN `examples/append.hom`
- WHEN the command is run on it
- THEN it prints `[1, 2, 3, 4]` and exits 0

#### Scenario: The budget is an argument

- GIVEN `examples/forever.hom`, which does not finish
- WHEN the command is run on it with the budget `5000`
- THEN it prints `no result within 5000 steps` and exits 0

#### Scenario: A long answer is printed in full

- GIVEN a program whose answer is an array of the numbers 20000 down to 1
- WHEN the command is run on it
- THEN it prints all 128894 bytes of the array and a newline

#### Scenario: A file that cannot be read

- GIVEN a path that names no file, or names a directory
- WHEN the command is run on it
- THEN it prints nothing on standard output, one line on standard error, and exits 2

#### Scenario: A wrong call

- GIVEN no arguments, three arguments, the budget `-1`, or a budget that contains a line break
- WHEN the command is run
- THEN it prints nothing on standard output, one line on standard error, and exits 2

### Requirement: A command runs a program against answers

The host SHALL provide a command that takes the path of a program file, the path of an answers file, and an optional step budget. It SHALL pass both files' bytes and the budget to the Lean export `reflect_converse` and SHALL print the bytes that come back, followed by a newline, on standard output. `reflect_converse` SHALL run `Surface.converseText` and SHALL return the number of bytes the rendering needs, as `reflect_run` does. With no budget given the command SHALL use one hundred million steps for each turn. It SHALL exit 0 whenever the kernel answered and the answer was written, whatever the answer says: requests, a waiting run, a value, an error, and an answers file the kernel refuses are all the kernel's text. It SHALL exit 2 and print one line on standard error, which does not repeat the arguments, when it is called with the wrong number of arguments, when the budget is not a whole number, when either file cannot be read, or when the answer cannot be written. The Zig source SHALL NOT read either file's contents. Each call SHALL run the program from the start against the whole answers file.

#### Scenario: A program asks and finishes

- GIVEN `examples/ask.hom` and `examples/ask.answers`
- WHEN the host check runs the command
- THEN it prints `asked: [1]`, `asked: [2, 20]` and `42`, and exits 0

#### Scenario: A program is left waiting

- GIVEN `examples/ask.hom` and `examples/ask-one.answers`
- WHEN the host check runs the command
- THEN it prints the two `asked:` lines and `waiting`, and exits 0

#### Scenario: A missing answers file

- GIVEN a path to an answers file that does not exist
- WHEN the command is run
- THEN it exits 2 with one line on standard error and nothing on standard output

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

### Requirement: A command runs one turn with the program's state in a directory

The host SHALL provide a command that takes a store directory and either `start` with a program file, or `answer` with a root and an answer file, and an optional step budget. It SHALL read from the directory the file named by each piece the kernel asks for and pass its bytes to the kernel. It SHALL write each piece the kernel hands back to a file with the name the kernel gives, before printing. It SHALL print the kernel's text and a newline. The host SHALL NOT read, hash or name a piece. It SHALL exit 0 whenever the kernel answered. It SHALL exit 3, print one line on standard error and write nothing when the directory lacks a piece the turn needs. It SHALL exit 2 with a message on standard error for a wrong call, a file or directory it cannot read, or a file it cannot write.

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

### Requirement: A command runs a program as processes

The host SHALL provide a command that takes a program file, an optional schedule file or `-` for none, an optional step budget and an optional event limit. It SHALL pass the program's bytes, the schedule's bytes, the budget and the limit to the Lean export `reflect_channels` and SHALL print the text that comes back and a newline. With no schedule the kernel SHALL choose the events, at most the limit. With a schedule the kernel SHALL run exactly its events and stop at the first that cannot happen. The text SHALL be the schedule that happened, in the form a schedule file is written in, then one line for each process with what it finished with or is waiting on and the names it holds, then how the run stopped. A printed schedule given back SHALL run the same events and print the same schedule and process lines; the last line SHALL be the same when the first run was not refused and did not run out of budget. The host SHALL NOT read the program or the schedule, SHALL NOT choose an event, and SHALL exit 0 whenever the kernel answered. It SHALL exit 2 with a message on standard error for a wrong call, a file it cannot read, or a schedule file that is empty.

#### Scenario: A recorded schedule replays

- GIVEN `examples/ping.hom`
- WHEN it is run with no schedule, the schedule line of the output is saved to a file, and it is run again with that file
- THEN the two outputs are the same bytes

#### Scenario: A refused event is the kernel's text

- GIVEN `examples/guess.hom` and `examples/guess.schedule`
- WHEN the command runs
- THEN the last line is `refused: [2, 0, 1] cannot happen` and the command exits 0

#### Scenario: Choosing stops at the limit

- GIVEN `examples/spawns.hom`, which starts processes without end, and an event limit of 3
- WHEN the command runs with no schedule
- THEN three events happen, four processes are listed, and the last line is `an event is offered`

### Requirement: A command runs a program against a log with its state in a directory

The host SHALL provide a command that takes a store directory and either `start` with a program file and a log file, or `from` with a root and a log file, and an optional step budget. It SHALL pass the bytes to the Lean export `reflect_vm_start` or `reflect_vm_from`, and SHALL then serve the session exactly as the command that runs one turn does: read the file named by each piece the kernel asks for, write each piece the kernel hands back under the name the kernel gives before printing, and print the kernel's text and a newline. A log file SHALL be a program whose result is an array of `[mark, answer]`; the kernel names each entry by the hash of the pair. The text SHALL be where the program stands, then `entries: N given, K acted on`, then `state: ` and the root, then the store line. The host SHALL NOT read the log, hash or compare an entry, decide what an entry does, or name the state. It SHALL exit 0 whenever the kernel answered, 3 with one line on standard error and nothing written when the directory lacks a piece that is needed, and 2 with a message on standard error for a wrong call, a file or directory it cannot read, or a file it cannot write.

#### Scenario: Stop, restart, same state

- GIVEN `examples/ask.hom` and an empty directory
- WHEN it is started on `examples/ask-one.log`, and the state printed is then handed `examples/ask.log` in another call
- THEN the first call prints `waiting on [2, 20]`, the second prints `42` and `entries: 2 given, 1 acted on`, and its state is the one a start on `examples/ask.log` prints

#### Scenario: The store is lost

- GIVEN the state a start on `examples/ask.log` printed
- WHEN the directory is emptied and the start is run again
- THEN it prints the same state

#### Scenario: A root that is not a state

- GIVEN the name of a stored piece that is not a VM state
- WHEN it is given to `from`
- THEN the command prints `store error: the root is not a kept state` and exits 0

#### Scenario: A log that is not a log

- GIVEN `examples/ask.answers` as the log file
- WHEN the command runs
- THEN it prints `log: entry 0 is not a mark and an answer` and exits 0

### Requirement: A command applies a log to processes kept in a directory

The host SHALL provide a command that takes a store directory and either `start` with a program file and a log file, or `from` with a root and a log file, and an optional step budget. It SHALL pass the bytes to the Lean export `reflect_node_start` or `reflect_node_from` and SHALL then serve the session as the command that runs one turn does. A log file SHALL be a program whose result is an array of `[mark, event]`, an event written as a schedule file writes it; the kernel names each op by the hash of the pair. The text SHALL be one line for each process, then `entries: N given, K acted on`, then the line `refused: entry K, <event>, cannot happen` when the op at place K of the log, counted from 0, could not happen, then `state: ` and the root, then the store line. The host SHALL NOT read the log, hash or compare an op, decide what an op does, choose an event, or name the node. It SHALL exit 0 whenever the kernel answered, 3 with one line on standard error and nothing written when the directory lacks a piece that is needed, and 2 with a message on standard error for a wrong call, a file or directory it cannot read, or a file it cannot write.

#### Scenario: Stop, restart, same node

- GIVEN `examples/ping.hom` and an empty directory
- WHEN it is started on `examples/ping-part.log`, and the root printed is then handed `examples/ping.log` in another call
- THEN the first call shows both processes waiting, the second prints `entries: 6 given, 3 acted on`, and its root is the one a start on `examples/ping.log` prints

#### Scenario: An op that cannot happen

- GIVEN `examples/guess.hom` and a log whose third op is `[3, [2, 0, 1]]`
- WHEN the command runs
- THEN it prints `entries: 4 given, 2 acted on` and `refused: entry 2, [2, 0, 1], cannot happen`, exits 0, and its root is the one the first two ops alone give

#### Scenario: The wrong kind of root

- GIVEN the root of a state the `vm` command kept
- WHEN it is given to `from`
- THEN the command prints `store error: the root is not a kept node` and exits 0

### Requirement: A command runs a program through the interpreter

The run command SHALL accept `--interp` and `--interp=k`, for a whole number `k`, before the file path, in any order with `--bytes` and `--text`. `--interp` SHALL mean `--interp=1`. With it, the program, from source or from its byte form, SHALL be passed to the export `reflect_interp` in place of `reflect_run` or `reflect_run_bytes`, with the number of levels and a `flags` byte whose bit 0 SHALL be set when the program is its byte form. `reflect_interp`, a Lean definition, SHALL run `level k` of the program on the machine for at most the budget: the closed interpreter term given the program as data, `k` times over; level 0 is the program itself. The export SHALL read the answer back through `k` levels of the outcome's data form and SHALL render it as `reflect_run` renders an outcome. `reflect_interp` SHALL be one of the exports that evaluate. Zig SHALL NOT read the program or the answer.

The kernel builds the tower of interpreters, and `unlift` reads the answer back by recursion on `k`, before the budget counts a step, so the levels SHALL be bounded by the kernel and not by the budget: `Surface.maxLevels`, 8. `Surface.interpBytes` and `Surface.interpText` SHALL answer `levels error: the interpreter levels must be at most 8` for more levels without reading the program, so every caller of `reflect_interp` has the bound. The export `reflect_max_levels`, which evaluates nothing, SHALL give that bound, and the run command SHALL ask for it after the kernel starts and refuse more levels before anything runs. A whole number of levels too large for 32 bits SHALL be refused the same way, not as a word that is not a number.

#### Scenario: The interpreter prints what the program prints

- GIVEN `examples/append.hom`, `examples/code.hom`, `examples/factorial.hom`, the identity function and a program whose outcome is wrong
- WHEN the command is run on each directly, and with `--interp=0`, `--interp=1` and `--interp=2`, from source and with `--bytes` on its byte form
- THEN every run prints the same text

#### Scenario: The budget counts the outermost machine

- GIVEN `examples/forever.hom`
- WHEN the command is run on it with `--interp` and a budget of 5000
- THEN it prints `no result within 5000 steps`

#### Scenario: Bad levels are refused

- WHEN the command is run with `--interp=x`
- THEN it prints `run: the interpreter levels must be a whole number` on standard error, nothing on standard output, and exits 2

#### Scenario: Too many levels are refused

- WHEN the command is run with `--interp=9`, with `--bytes --interp=4294967295` and with `--interp=4294967296`
- THEN each prints `run: the interpreter levels must be at most 8` on standard error, nothing on standard output, and exits 2; with `--interp=8` and a budget of 1000 it prints `no result within 1000 steps` (`host/check.sh`); and `Surface/Check.lean` finds that `interpText` and `interpBytes` answer `levels error: the interpreter levels must be at most 8` for 9 and for 2^32 - 1 levels and do not for 8

### Requirement: A command prints a result as text

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

### Requirement: A Lean export returns a bounded run as bytes

The Lean definition exported as `reflect_reply_bytes` SHALL take a program pointer and length, output pointer and capacity, and UInt64 step budget. It SHALL run `Surface.replyBytes`, which decodes program bytes, runs the existing compiled machine and returns `Wire.runReplyBytes` for its reply. It SHALL be an export that evaluates. It SHALL return the required length, writing nothing when capacity is insufficient, as the existing byte exports do. The caller SHALL pass and copy bytes and SHALL NOT infer an outcome from text. Machine-step budgets SHALL NOT be described as native wall-clock bounds.

#### Scenario: A complete binary answer

- GIVEN identical program bytes and budget passed to the server and the Linux comparison process
- WHEN each calls reflect_reply_bytes
- THEN each receives the identical complete wire-bytes run reply, and an insufficient buffer remains untouched

### Requirement: Lean exports carry the crossing

The Lean definitions exported from `kernel/Surface/Host.lean` SHALL be the guest and the check of `openspec/specs/crossing/spec.md`: `reflect_cross_start(flags, limit, turn, hold)` begins a guest with no process, with its own step limit, turn space and hold, 0 each for the default (bit 0: it will be given the program; bit 1: its start requests go to the peer; bit 2: it takes the newest pending send first; bit 3: it opens the exchanges and closes the run); `reflect_cross_give(guest, program, length, budget)` gives the program, in its byte form, with a budget that can only lower the guest's own, and the guest begins it as the first process once it has heard the peer; `reflect_cross_work(guest)`, `reflect_cross_take(guest, batch, length)` and `reflect_cross_batch(guest, out, capacity)` are `Guest.work`, `Guest.take` and `Guest.batch`; `reflect_cross_state(guest)` is 0 for work to do, 1 resting, 2 closed, 3 failed; `reflect_cross_record(guest, me, meLength, peer, peerLength, out, capacity)` is the record text; `reflect_cross_check(program, length, a, aLength, b, bLength, out, capacity)` is `Surface.Cross.check`; `reflect_cross_reseal(record, length, out, capacity)` is a check-only hook that makes a record's chain and head again. A guest is a Lean value the caller holds and cannot look inside; each call that takes it uses it up. `give`, `work` and `check` evaluate, each machine run they make is a priced run with the budget given, and Zig SHALL NOT make or read the bytes they exchange. `unikernel/out-net/cross-check` calls the last two.

#### Scenario: The same check outside a guest

- GIVEN `unikernel/out-net/cross-check`, linked from the objects the guests link
- WHEN `unikernel/check-wire.sh` runs it on two guests' records
- THEN it prints what `Surface.Cross.check` answers, and exits 0 only on `accepted`

### Requirement: The run command charges operation costs

`reflect_run` and `reflect_run_bytes` SHALL run the machine with `runPriced`, charging each operation its cost under `arith` (`Surface.runText`, `Surface.runBytes`). A run stopped by the budget SHALL print `no result within N steps` with `N` the budget, as before. The other exports that evaluate, `reflect_interp`, `reflect_reply_bytes`, `reflect_converse`, `reflect_channels`, `reflect_keep_*`, `reflect_vm_*`, `reflect_node_*` and `reflect_cross_*`, SHALL charge the same costs: each machine run they make is a priced run, and a kept session's lazy run charges an operation its cost too (`openspec/specs/bytecode-machine/spec.md`, `homoiconic-q59.52`). A budget SHALL mean the same on every export. Through the interpreter (`--interp`) an operation of the program is charged what it is charged directly, and the interpreter's own steps are charged on top, so a budget that stops a program stops it through the interpreter.

#### Scenario: A small product finishes

- GIVEN the program `mul 2 3`
- WHEN the run command runs it with the budget 200
- THEN it prints `6` (`host/check.sh`)

#### Scenario: A large product stops before it runs

- GIVEN the program `mul` applied to two numbers of 40 nines
- WHEN the run command runs it with the budget 200
- THEN it prints `no result within 200 steps` (`host/check.sh`)

#### Scenario: The same product finishes with more budget

- GIVEN the same program
- WHEN the run command runs it with the budget 200000
- THEN it prints the product, 80 digits (`host/check.sh`)

#### Scenario: The interpreter is charged for the operation

- GIVEN the same program
- WHEN the run command runs it with `--interp` and the budget 200, and with `--interp` and the budget 18000
- THEN both print `no result within N steps` with `N` the budget, while the direct run at 18000 prints the product (`host/check.sh`)

### Requirement: The exports that make one run take a space

`reflect_run`, `reflect_run_bytes` and `reflect_reply_bytes` SHALL take `space : u64`, a number of cells, after `budget`; `reflect_interp` SHALL take it after `budget` and before `levels`. Each SHALL run its program with `Reflect.runIn` under a `Space` of that many cells whose count is `reflect_live_cells` cut at three quarters of them (`Space.bar`), and SHALL answer the space outcome, the text `no result within <space> cells` or the reply `[7]`, for a run that ends as `full` and for an answer that written out would take more than four bytes for each cell of the space (a data answer on the text exports, any answer on `reflect_reply_bytes`). `reflect_default_space` SHALL answer `Reflect.defaultSpace`; its argument is ignored. `reflect_live_cells` (`kernel/ffi.c`) SHALL count the constructor objects reachable from a Lean value through constructor fields, each once, by address, and a number too large for a machine word so that with the box around it it is `natCells`; it SHALL stop past its cut and answer one more than the cut, SHALL answer the same when it cannot get memory for its table or stack, and SHALL change nothing. Its table SHALL start at 4096 slots and be made four times as large when three quarters full, up to the least power of two slots that is at least four thirds of the cut and two, and its stack SHALL hold at most one entry for each cell counted. A reply past the ledger therefore depends on what the runtime shares and on whether that memory can be had; the same Lean objects on the image and in a Linux process give the same count. It is the only place the kernel package reads what the runtime shares, and it is trusted, not proved. Zig SHALL NOT count cells or read a state. Every other evaluating export SHALL keep its arguments; the machine runs behind them are turns (`openspec/specs/bytecode-machine/spec.md`).

`host/out/run [--bytes] [--interp[=levels]] [--text] <program-file> [step-budget [space]]` SHALL pass the space given, or the kernel's default. A space that is not a whole number below 2^64 SHALL be refused on the host's own line with exit status 2.

#### Scenario: A run out of space is the kernel's text

- GIVEN `def deep x = [x, ...deep x]` applied to 0
- WHEN `host/out/run` runs it with the budget 100000000 through 0, 1 and 2 interpreters, at level 2 with the space 100000
- THEN each prints `no result within <space> cells` and exits 0

#### Scenario: The limit undone

- GIVEN the same program, the budget 10000000, and a space of 18446744073709551615
- WHEN `host/out/run` runs it
- THEN it prints `no result within 10000000 steps`, where with the default space the same budget ends in `no result within 4000000 cells` (`host/check.sh`): the space, not the budget, is what stops it
