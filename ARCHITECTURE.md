# Architecture

The settled language partition for the first system. Source of record for the partition: `openspec/specs/language-partition/spec.md`. Source of record for the host: `openspec/specs/zig-host/spec.md`. Source of record for programs as data: `openspec/specs/code-as-data/spec.md`. Source of record for the machine: `openspec/specs/bytecode-machine/spec.md`. Source of record for the surface syntax: `openspec/specs/surface-syntax/spec.md`. Source of record for requests: `openspec/specs/requests/spec.md`. Source of record for stored state: `openspec/specs/state-store/spec.md`.

## Partition

| Language | Role | Contains an evaluator? |
|---|---|---|
| Lean 4 | The only semantics language. The evaluator, `Reflect`, is Lean 4 source, and the proofs talk about that source. | Yes. This is the only one. |
| Zig | The host: the operating-system process. It handles files, allocation, and the REPL. It loads the Lean runtime and returns the kernel's result. | **No.** It never re-states the semantics or grows a second `eval`. |
| Rust | Absent. It is not a language of the first system. | n/a |

## Circularity

Circularity means the interpreter theorem. An interpreter is a term of the language. For every program, evaluating that term on the program as data equals evaluating the program directly. The theorem is `reflective`, proved about `Reflect`, the evaluator that runs, with no fragment. Its statement is in `openspec/specs/code-as-data/spec.md`.

The first kernel, `Circular` (`add-lean-circular-kernel`), proved the theorem for quote-free programs at one level; `retire-circular-kernel` deleted it, and it is in git at `8b23867` and earlier.

## Reflect

The kernel package holds two Lean libraries, `Reflect` and `Surface`. `Reflect` is the language, its one evaluator, and its proofs. In `Reflect` a program is a data value: data is natural numbers and arrays, and quoting a program is a literal of its data form. The interpreter is one closed term that takes a program as data, and the interpreter theorem holds for every term, with no fragment. A stack machine runs the same language one step at a time, and it is proved equal to direct evaluation. The statements are in `openspec/specs/code-as-data/spec.md` and `openspec/specs/bytecode-machine/spec.md`.

`prim c x` runs an operation from a table, `Ops`: one total function from an operation number and a data value to a data value. Evaluation, the interpreter theorems and the machine theorems are stated for every table. The interpreter is the same term for every table, so a new set of operations is added to a table with no new proof. The first table is exact arithmetic (`kernel/Reflect/Arith.lean`), and the host runs with it (`add-operation-tables`).

## Requests

A program can ask the outside for something and continue from the answer. A request is an ordinary value: `ask payload next` builds a function that hands its payload and the rest of the program to its caller. Nothing is added to the language, evaluation, the interpreter or the machine. A driver outside the program runs it against a list of answers: every function a turn ends in is read as a request, its payload must be data, and the rest of the program runs on the next answer. The driver is defined once, over any way of evaluating, and it is proved that a run is fixed by the program and the answers, and that direct evaluation, the interpreter on data and the machine make the same requests and end the same way. A request carries no mark, so a driven program cannot finish with a function. What a payload means is not part of this. The statements are in `openspec/specs/requests/spec.md`.

## Stored state

A running program's state can be held in pieces. A piece is a number, an empty list, a pair, a function, or a reference to another piece, and one type serves for data, values and environments. A store maps references to pieces and may lack any of them. The kind of reference is a parameter, as the operation table is; the kernel does not say how a reference is made. A lazy machine runs a partial state: when a step has to look at a reference it fetches that one piece, and when the store lacks it the run pauses, holding the reference it needs. A pause is not an outcome, and a program cannot observe it. It is proved, for every table and every kind of reference, that cutting a state into pieces loses nothing, that the lazy machine halts with what the plain machine halts with, that more pieces change nothing, and that a waiting run of the request driver can be kept and continued from its root. Hashing, the byte form of a piece, disk, the network and attestation are outside the kernel; the store is in memory. The definitions are in `kernel/Reflect/Store.lean` and `kernel/Reflect/StoreProof.lean`, the exact statements in `kernel/StoreContract.lean`, and `kernel/StoreCheck.lean` cuts and continues real runs. `host/check.sh` runs `StoreContract.lean` and `StoreCheck.lean`. The statements are in `openspec/specs/state-store/spec.md`.

## Surface

`Surface`, the package's other library, holds the reader, from program text with names and indentation to `Reflect` terms, and the renderer, from outcomes to plain text. The reader and the renderer are tested against examples. They are not proved. What runs is the term the reader produced, on the proved machine. The statements are in `openspec/specs/surface-syntax/spec.md`.

## Boundary

The proof boundary is the call from the Zig host into the Lean kernel. The `lean-c-abi` spike (`docs/spikes/lean-c-abi/finding.md`, Lean 4.35.0, Zig 0.16.0) returned `71` from one unboxed exported function to a Zig host that does not contain the formula. The spike shows the call is feasible. The object link and the runtime initializer are in `host/`. Zig passes program text to `reflect_run`, or a program and an answers text to `reflect_converse`, and prints the text it returns. These two are the only exports that evaluate; Zig reads nothing and evaluates nothing. The command `host/out/run <program-file> [step-budget]` does the same for a program file, and `host/out/ask <program-file> <answers-file> [step-budget]` runs a program file against an answers file. The host requirements are `openspec/specs/zig-host/spec.md`. The theorems are the source of record in `openspec/specs/code-as-data/spec.md` and `openspec/specs/bytecode-machine/spec.md`.

## Why

- **Lean owns semantics.** A model beside a Zig or Rust interpreter can drift. With `eval` in Lean, the program and the proof are the same artifact, and Lean 4 compiles, so the kernel can run.
- **Zig is the host.** The process needs explicit allocation, files, and a small binary. The host does not duplicate semantics.
- **Rust is out.** The borrow checker is real but is not a Lean theorem. Keeping Rust would add a third compiler to every semantics change. A translator carrying Rust into Lean would make Rust the source of the evaluator, which reverses the decision that Lean is the semantics.

## Downstream changes

- `add-lean-circular-kernel`: folded, then retired by `retire-circular-kernel`. Its kernel, `Circular`, is in git at `8b23867` and earlier.
- `add-zig-host`: folded. The object link and the runtime initializer are in `host/`. The host requirements are `openspec/specs/zig-host/spec.md`.
- `add-code-as-data`: folded. `Reflect` and the interpreter theorem for every term are `openspec/specs/code-as-data/spec.md`.
- `add-bytecode-machine`: folded. The machine and its agreement with direct evaluation are `openspec/specs/bytecode-machine/spec.md`.
- `move-host-to-reflect`: folded. `Surface` and `reflect_run`; the host runs `Reflect` programs on the machine. The syntax is `openspec/specs/surface-syntax/spec.md`, and the host call is `openspec/specs/zig-host/spec.md`.
- `retire-circular-kernel`: folded. `Circular`, `kernel_run`, and `lean-kernel` are deleted; one evaluator, `Reflect`, remains. The host calls `reflect_run` only and has a run command, `host/out/run`. The command is in `openspec/specs/zig-host/spec.md`.
- `add-operation-tables`: folded. `prim` and the `Ops` table, with exact arithmetic as the first table; every theorem holds for every table. The requirements are in `openspec/specs/code-as-data/spec.md`, `openspec/specs/bytecode-machine/spec.md` and `openspec/specs/surface-syntax/spec.md`.
- `add-requests`: folded. A request is a value and the driver is outside evaluation; `reflect_converse` and the command `host/out/ask`. The requirements are in `openspec/specs/requests/spec.md`, with additions in `openspec/specs/surface-syntax/spec.md` and `openspec/specs/zig-host/spec.md`.
- `add-state-store`: folded. State held in pieces under references, and a lazy machine that fetches on first use and pauses on a missing piece. No command uses it yet. The requirements are in `openspec/specs/state-store/spec.md`.

The partition is the landed artifact those changes cite. This kernel does not add a Zig host or a C ABI. The host landing is the call above.
