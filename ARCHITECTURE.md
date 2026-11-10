# Architecture

The settled language partition for the first system. Source of record for the partition: `openspec/specs/language-partition/spec.md`. Source of record for the kernel: `openspec/specs/lean-kernel/spec.md`. Source of record for the host: `openspec/specs/zig-host/spec.md`. Source of record for programs as data: `openspec/specs/code-as-data/spec.md`. Source of record for the machine: `openspec/specs/bytecode-machine/spec.md`.

## Partition

| Language | Role | Contains an evaluator? |
|---|---|---|
| Lean 4 | The only semantics language. The circular evaluator is Lean 4 source, and the proofs talk about that source. | Yes. This is the only one. |
| Zig | The host: the operating-system process. It handles files, allocation, and the REPL. It loads the Lean runtime and returns the kernel's result. | **No.** It never re-states the semantics or grows a second `eval`. |
| Rust | Absent. It is not a language of the first system. | n/a |

## Circularity

Circularity means the metacircular theorem. An interpreter is a term of the language. On a small, named fragment, evaluating that term on a program equals evaluating the program directly.

The kernel change, `add-lean-circular-kernel`, landed this theorem. The fragment is every quote-free term. The evaluator is Lean 4 source in `kernel/`. `metacircular` and `coverage` are proved (`46048e9`). One level. The Zig host and a C ABI are not part of that landing.

## Reflect

The kernel package now holds a second Lean library, `Reflect`, beside `Circular`. In `Reflect` a program is a data value: data is natural numbers and arrays, and quoting a program is a literal of its data form. The interpreter is one closed term that takes a program as data, and the interpreter theorem holds for every term, with no fragment. A stack machine runs the same language one step at a time, and it is proved equal to direct evaluation. The statements are in `openspec/specs/code-as-data/spec.md` and `openspec/specs/bytecode-machine/spec.md`.

`Circular` and the Zig host are unchanged. The host still calls `Circular`. For a time the package holds two evaluators, both Lean. Moving the host to `Reflect` and retiring `Circular` is a later change.

## Boundary

The proof boundary is the call from the Zig host into the Lean kernel. The `lean-c-abi` spike (`docs/spikes/lean-c-abi/finding.md`, Lean 4.35.0, Zig 0.16.0) returned `71` from one unboxed exported function to a Zig host that does not contain the formula. The spike shows the call is feasible. `add-zig-host` landed that call: Zig calls `kernel_run`, and the object link and the runtime initializer are in `host/`. The kernel theorems stay the source of record in `openspec/specs/lean-kernel/spec.md`.

## Why

- **Lean owns semantics.** A model beside a Zig or Rust interpreter can drift. With `eval` in Lean, the program and the proof are the same artifact, and Lean 4 compiles, so the kernel can run.
- **Zig is the host.** The process needs explicit allocation, files, and a small binary. The host does not duplicate semantics.
- **Rust is out.** The borrow checker is real but is not a Lean theorem. Keeping Rust would add a third compiler to every semantics change. A translator carrying Rust into Lean would make Rust the source of the evaluator, which reverses the decision that Lean is the semantics.

## Downstream changes

- `add-lean-circular-kernel`: folded. The evaluator and the metacircular theorem are `openspec/specs/lean-kernel/spec.md`.
- `add-zig-host`: folded. Zig calls `kernel_run`. The object link and the runtime initializer are in `host/`. The host requirements are `openspec/specs/zig-host/spec.md`.
- `add-code-as-data`: folded. `Reflect` and the interpreter theorem for every term are `openspec/specs/code-as-data/spec.md`.
- `add-bytecode-machine`: folded. The machine and its agreement with direct evaluation are `openspec/specs/bytecode-machine/spec.md`.

The partition is the landed artifact those changes cite. This kernel does not add a Zig host or a C ABI. The host landing is the call above.
