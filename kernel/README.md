# Kernel

One Lean package with three libraries, and the host that calls it.

- `Reflect` is the language and its proofs. A program is a data value, and
  one closed term of the language interprets programs given as data.
- `Wire` is the byte form of data, programs, machine values and pieces of
  stored state, and Blake3, which names a stored piece. It is tested, not
  proved.
- `Surface` reads program text into `Reflect` terms and renders outcomes as
  text. It is tested, not proved.
- The Zig host in `../host` calls the exports `reflect_run`, `reflect_converse`,
  `reflect_run_bytes`, `reflect_source_bytes`, `reflect_channels` and the
  `reflect_keep_*` exports.

Use Lean 4.35.0, pinned in `lean-toolchain`, and run from this directory:

```sh
lake build
lake env lean ReflectContract.lean   # the interpreter theorems, exact statements
lake env lean MachineContract.lean   # the machine theorems, exact statements
lake env lean RequestContract.lean   # the request theorems, exact statements
lake env lean StoreContract.lean     # the stored-state theorems, exact statements
lake env lean ChannelContract.lean   # the channel theorems, exact statements
lake env lean RootContract.lean      # equal states are saved under one root, exact statements
lake env lean ReflectRun.lean        # the scenarios, executed
lake env lean Surface/Check.lean     # the reader and renderer against examples
lake env lean StoreCheck.lean        # runs cut into pieces and continued
lake env lean WireCheck.lean         # the byte form against vectors and programs
lake env lean KeepCheck.lean         # Blake3, pieces as bytes, saving, turns from a store
lake exe reflectBench                # steps per second
```

All four contract files print each theorem's axioms. They are Lean's standard
three (`propext`, `Classical.choice`, `Quot.sound`), with no admissions.

## Reflect

| File | Holds |
|---|---|
| `Reflect/Syntax.lean` | `Data` (numbers and arrays), `Term`, and `reify : Term → Data` |
| `Reflect/Semantics.lean` | `Ops`, the table of operations; `Direct`, the call-by-value relation; `evalFuel`, its total executable form |
| `Reflect/Arith.lean` | `arith`, the first table: exact arithmetic and comparison. No theorem depends on it |
| `Reflect/Interpreter.lean` | `interp`, the interpreter as one closed term; `level k` nests it |
| `Reflect/SemanticsProofs.lean` | `Direct` is deterministic; `evalFuel` agrees with it |
| `Reflect/Proof.lean`, `Correctness.lean` | `reflective`, `reflective_coverage`, `reflective_env`, `tower` |
| `Reflect/Machine.lean` | `compile`, `step`, `run`: a stack machine that can stop after any step |
| `Reflect/MachineProof.lean`, `MachineExact.lean` | `machine_correct`, `machine_exact`, `machine_never_halts`, `run_add`, `depth_bound` |
| `Reflect/MachineSafe.lean` | `machine_never_faults` and its `runUntil` and `runPriced` forms: a compiled program never reaches `fault`, halting or not |
| `Reflect/RunUntil.lean`, `RunUntilProof.lean` | `runUntil`, which stops when the machine stops, and `runUntil_eq` |
| `Reflect/Request.lean` | `askTerm`, `payloadTerm`, `resumeTerm`; `Sys`, a way of evaluating; `Drive`, the driver over any `Sys`; `Interact`, `InteractI`, `InteractM`; `driveRun` and `converse`, the executable driver |
| `Reflect/RequestProof.lean` | Determinism, resume and extra answers; `Sim.drive`, which lifts turn-by-turn agreement to runs; the interpreter and machine instances; soundness of `converse` |
| `Reflect/Channel.lean` | `classify`, which reads a payload as a channel request; `PSys`; `Settle`, `Turn`; `Event`, `Step`, `Sched`, `Network`; `stepRun`, `schedRun`, `autoRun`, the executable scheduler; `pick`, which chooses an event |
| `Reflect/ChannelProof.lean` | A schedule leads to one configuration; a process uses only names it holds, and where a held name comes from; `PSim`, agreement of two ways of evaluating on schedules; soundness of the executable scheduler |
| `Reflect/Store.lean` | `P`, a piece; `Store`; `Unf`, which resolves a piece; partial states; `lstep` and `lrun`, the lazy machine, with a pause; `RState` |
| `Reflect/StoreProof.lean` | Saving loses nothing; the lazy machine reaches every plain state; a missing piece is a pause; more pieces change nothing; stores that agree give the same result; a turn of the request driver from a stored continuation |
| `Reflect/Examples.lean` | Worked cases, checked by the kernel |

`reflective` says: for every term `p` and outcome `o`, `p` evaluates to `o`
exactly when the interpreter applied to `p` as data evaluates to the data form
of `o`. There is no fragment and no fuel in the statement. `tower` says the
same for the interpreter interpreting itself to any depth.

## Operations

`prim c x` runs operation number `c` on the data value `x`. What an operation
computes is not part of the language. It comes from a table, `Ops`, holding one
total function `op : Nat → Data → Data`, and every definition and theorem takes
the table as a parameter. The table also gives `cost`, the steps a budget
charges before the operation runs; a table that does not say charges one.
`arithCost` is that charge for `arith`. The interpreter is the same term for
every table, so adding an operation is adding a line to a table: no proof
changes.

The contract files state each theorem as `∀ [Ops], …` and do not import a
table. The host runs with `arith`.

## Requests

A request is a function value: `ask payload next` is the closed term
`askTerm`, which hands `payload` and `next` to its caller. No term, value,
outcome, rule or instruction is added. A driver, `Drive`, runs a program
against a list of answers. A turn that ends in data or an error ends the run.
A turn that ends in a function is read as a request, whether or not `ask`
built it: the driver applies it to `payloadTerm` to read the payload, which
must be data, and to `resumeTerm` to run the rest on the next answer. With no
answer left the run is waiting.

`Drive` is defined once over `Sys`, a way of evaluating, and used three times:
`Interact` (direct evaluation), `InteractI` (the interpreter on data) and
`InteractM` (the machine). `RequestContract.lean` states
`interact_deterministic`, `interact_resume`, `interact_extra`,
`interact_reflective`, `interact_coverage`, `interact_machine`,
`interact_machine_exact`, `converse_finished` and `converse_waiting`, each as
`∀ [Ops], …`. `converse` gives each machine run a fresh step budget and is
proved sound, not complete.

## Channels

Several programs run side by side as processes and talk over channels. Nothing
is added to the language: four shapes of payload are channel requests. `[0]`
makes a channel and is answered with its name, a number. `[1, name, message]`
sends, `[2, name]` receives, and `[3, program, start]` starts a quoted program
on the data `start` as a new process. Every other payload is a request to the
outside. A send and a receive on one name meet; there is no queue.

A schedule is a list of events, and `Step` says what each does and when it can
happen: a process is given a new name, a process starts a process, one process
sends to another, a process is answered from outside. The new names and the
outside answers are in the events. Each process holds a list of names: the ones
it made, the ones its starter held that occur in its start data, and the ones
its sender held that occur in a message it received. A send or a receive on a
name the process does not hold cannot happen. A name is a number, so a process
can write any name; it cannot use one it does not hold.

`ChannelContract.lean` states `network_deterministic`, `Step.comm_held`,
`Step.held_from`, `Network.held_issued`, `network_machine`,
`network_machine_exact`, `replay_true` and `auto_true`. `stepRun`, `schedRun`
and `autoRun` run events on the machine with a step budget for each machine
run, and are proved sound, not complete. `autoRun` chooses the first process,
in order, whose request has what it needs. It never offers an answer from
outside, and an event it offers may still not halt within the budget. No
theorem depends on how it chooses, and none is about what it would offer next.

## Stored state

A piece, `P R`, is a number, an empty list, a pair, a function (code and its
environment), or a reference `ref r`. One type serves for data, values and
environments. `R` is the kind of reference and is a parameter of every
definition and theorem; nothing in the kernel says how a reference is made. A
store, `Store R`, maps references to pieces and may lack any of them. `Unf`
says a piece resolves to a value by following every reference, and `RState`
says the same of a partial machine state.

The lazy machine, `lstep` and `lrun`, runs a partial state. When a step has to
look at a reference it fetches that one piece. When the store lacks it the run
pauses, holding the reference and the state it stopped in. It does not write
fetched pieces back. `StoreContract.lean` states `saved_resolves`,
`cut_resolves`, `RState.mono`, `Unf.unique`, `resolve_unique`,
`lazy_simulates`, `lazy_complete`, `lazy_sound`, `lazy_pause`, `lrun_mono`,
`lazy_agree`, `lazy_program`, `lazy_turn_complete` and `lazy_turn_sound`, for
every table and every kind of reference. `StoreCheck.lean` stops eight
programs at four points, cuts each at every value, and continues it with the
whole store and with one piece withheld; it also keeps a waiting run and
continues it from its root. A line that starts with `FAIL` fails the check.
The theorems do not say how a reference is made. `Wire` makes one: a
reference is the Blake3 hash of a piece's bytes (see Wire), and
`Surface/Keep.lean` runs a turn against a store of such pieces (see Keep). The
network and attestation are not part of the store.

## Wire

`Wire` is the byte form. It is its own library: no definition or theorem in
`Reflect` mentions bytes.

| File | Holds |
|---|---|
| `Wire/Cbor.lean` | `write : Data → ByteArray` and `read : ByteArray → Except String Data`, for the part of dCBOR that `Data` has. A number below 2^64 is a CBOR unsigned integer in its shortest form; a larger number is tag 2 over its bytes with no leading zero; an array is a definite-length CBOR array. The reader refuses every other spelling |
| `Wire/Form.lean` | `blockTerm`; `valueData` and `dataValue`, a machine value as data; `programBytes`, `readProgram`, `valueBytes`, `readValue` |
| `Wire/Blake3.lean` | `hash : ByteArray → ByteArray`, the 32-byte Blake3 hash, written from the specification in about 100 lines. No keyed mode, no key derivation, no longer output |
| `Wire/Piece.lean` | `pieceItem` and `itemPiece`, a piece of stored state as an item; `pieceBytes`, `readPiece`; `cut` and `save`, which cut a value from the leaves up and store each part whose bytes pass a size under its hash |

A program's bytes are the bytes of `reify` of it; the identity function is
`82 01 00`. A machine value is `[0, d]` for data and `[1, body, captured]` for
a function, where `body` is the program its code was compiled from. Reading
compiles `body` again. `decompile` also reads code that no compilation gives,
so `blockTerm` compiles its result and compares: a function whose code is not
exactly a compiled program has no byte form. Tag 2 for large numbers is this
project's rule; dCBOR's numeric rules stop at 64 bits.

Proved, in `Reflect/Syntax.lean`: `unreify_reify`, `unreify (reify t) = some t` for every program, with
Lean's standard axioms. Everything else in `Wire` is tested, not proved
(decision D7 of the vision). `WireCheck.lean` checks the RFC 8949 appendix A
examples that are numbers or arrays, each integer width at its edges,
twenty-six spellings that must be refused, every string of one or two bytes,
eleven programs written, read back and run from their bytes, a waiting run
kept as bytes and continued, data that is no program, and a function whose
code no program compiles to. It prints the axioms of `unreify_reify`. A line
that starts with `FAIL` fails the check.

`Wire/Cbor.lean` also reads and writes a definite-length CBOR byte string, for
references. Reading data refuses one anywhere in it. A piece is written as: a
number as itself, an empty list as `[]`, a pair as `[0, head, tail]`, a
function as `[1, body, captured]`, and a reference as a byte string of 32
bytes. A reference is the Blake3 hash of the bytes of the piece it names.
Nothing about the hash, the byte form of a piece or saving is proved; that two
different pieces do not share a hash is assumed (D5). `KeepCheck.lean` checks
the 22 official Blake3 vectors from Zig's standard library, from 0 to 102,400
bytes; eight programs stopped at three points, saved at 256 bytes and at every
value, each piece named by its hash and read back to the same bytes, and the
lazy machine continued from the pieces to the plain machine's result; a
number larger than the size stored on its own; a result behind 70
references; and three turns, each a new session, giving what one run against
both answers gives.

## The log

A VM is a program that makes requests, together with the identifiers of the
log entries it has acted on (`Reflect/Log.lean`). A log is a list of entries,
each an identifier and an answer. Handling an entry answers the request the VM
is waiting on, runs the program to its next request or its end, and records
the identifier. An entry whose identifier the VM has acted on changes nothing,
and neither does any entry once the program has finished. The state of a VM is
what handling its log from the program's first request leads to.

The theorems on handling hold whatever the identifiers are. A log that is
read is *sealed*: an entry is written `[mark, answer]`, and its identifier is
the name a function `key` gives to that pair (`Entry.seal`). The kernel's
`key` is `Surface.Keep.entryName`: the Blake3 hash of the pair's bytes, as one
number. A mark that is not a link is not read: it tells apart two entries
with one answer. A link `[0, parent]` or `[0, parent, order]` is read: the
parent is the previous entry's name, or `[]` on the first entry, and the
order, when present, is the entry's place. The host checks a signature; the
kernel does not.

`LogContract.lean` states `log_deterministic` and `log_prefix` (the state is
fixed by the program and the log, and a state part way is a prefix),
`log_again`, `log_redeliver` and `log_once` (an entry already in the log
changes nothing), `log_restart` (a state reached by a first part of the log,
given the whole log, reaches what the whole log reaches), `log_interact` (the
run is the request driver's on the answers of the first deliveries),
`log_machine`, `log_machine_exact` and `vm_true`. It also states
`sealed_same` (two sealed entries with one identifier are one entry) and
`sealed_first` (so no entry of a sealed log is passed over for a different
one). Both take as a hypothesis that `key` gives different names to different
data. For Blake3 that is assumed, not proved, as it is for stored pieces.
`vmRun` is
`List.foldl handleRun` over the log, on the machine, with a step budget for
each machine run; it reports no state when a run does not halt. `Log.lean`
also decides equality of data by a definition of its own, because nothing is
proved about the derived `==`.

## Nodes

A node is several processes whose schedule is a log (`Reflect/Node.lean`). An
op is an event with an identifier, and a node is a configuration of processes
together with the identifiers of the ops it has acted on. Applying an op the
node has acted on changes nothing; otherwise the event happens as `Step` says
and the identifier is recorded. An op whose event cannot happen has no next
node. `plan` splits an event into the machine runs it needs and the
configuration once they have ended. An op that is read is sealed as an entry
is: written `[mark, event]`, with the hash of that pair as its identifier
(`Op.seal`, `sealed_op_same`, `sealed_op_first`).

`NodeContract.lean` states `node_deterministic`, `node_prefix`, `node_again`,
`node_redeliver`, `node_restart`, `node_network` (a node's processes are where
the schedule of first deliveries leads, so the channel theorems hold of them),
`node_machine`, `node_machine_exact`, `node_true`, and `plan_step` with
`step_plan` (an event is exactly its plan's runs and the configuration the
plan then gives). `nodeRun` applies ops on the machine and stops at the first
whose event cannot happen or does not halt.

## Keep

`Surface/Keep.lean` runs one turn of a program whose state is kept in a store
between turns. `start` begins from source; `answer` begins from the root of a
waiting program and an answer. A turn runs on the lazy machine. When it needs
a piece the session does not hold, the session stops and names it; `give`
supplies the bytes, checks that they hash to that name, and carries on. When
the turn ends in a request the waiting program is saved, cut at 256 bytes, and
the root and the new pieces are reported; a piece the session was given is not
handed back. `advance`, which joins the machine runs, repeats the logic of
`Reflect.driveRun` for one turn. Each machine run in it is covered by
`lazy_turn_complete` and `lazy_turn_sound`; `advance` itself is tested, not
proved.

A session can also be a VM handling a log. `vmStart` begins from source and a
log; `vmFrom` begins from the root of a kept state and a log. The session goes
from one entry to the next as `Reflect.vmRun` does, and at the end saves the
state as the piece `[seen, status]`: the identifiers acted on (each the hash
of its entry, a number below 2^256), and `[0,
function]`, `[1, data]`, `[2, i]` or `[3]` for a waiting program, a result, an
unbound variable or `wrong`. `LogCheck.lean` compares it with `vmRun`: the
root the session saves is the root of the fold's state saved the same way,
and a kept state restarted on the whole log has the root the whole log gives
from the start. The session is tested, not proved. The saving is proved:
`RootContract.lean` states `same_root` (two partial pieces that stand for one
value, every reference in each made by saving, have one root), `cut_made`
(saving makes only such references), `lstep_good` (the lazy machine makes
none) and `restart_same_root` (so a restarted state and a replayed one have
one root, given that each session holds such a piece). Nothing is assumed of
the hash. The proofs are in `Wire/PieceProof.lean` and
`Surface/KeepProof.lean`.

A session can also be a node. `nodeStart` runs a program as the first process
and applies a log of ops; `nodeFrom` applies one to a kept node. Whether an
event can happen, what it needs run and the configuration after it come from
`Reflect.plan`; the session runs each job on the lazy machine and joins them.
The node is saved as `[seen, names, processes]`, each process `[held,
status]`, a waiting status holding the function and its payload.
`NodeCheck.lean` compares the session with `nodeRun` at every prefix of three
schedules. That is tested, not proved.

The C exports are `reflect_node_start`, `reflect_node_from`, `reflect_vm_start`, `reflect_vm_from`, `reflect_keep_start`, `reflect_keep_answer`,
`reflect_keep_need`, `reflect_keep_give`, `reflect_keep_count`,
`reflect_keep_name`, `reflect_keep_piece` and `reflect_keep_text`, in
`Surface/Host.lean`. The session is a Lean value the host holds and cannot
look inside. Each export that takes a session uses it up: Lean refuses borrow
annotations on an exported function. A caller that will use the session again
calls `kernel_retain` (`ffi.c`, which is `lean_inc`) on it first.

## Surface

`Surface/Read.lean` is the reader, `Render.lean` the renderer, `Run.lean` joins
them to the machine, `Bytes.lean` runs a program given as bytes and gives a
program's byte form from its source, `Keep.lean` runs a turn against a store,
and `Host.lean` holds the C exports. `Expect.lean` is the
specification by example that `Check.lean` runs.

## History

The first kernel, `Circular`, proved the interpreter theorem for quote-free
programs with a Mogensen–Scott encoding. `Reflect` replaced it. It is in git at
`8b23867` and earlier.
