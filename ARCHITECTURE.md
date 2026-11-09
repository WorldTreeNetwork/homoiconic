# Architecture

The settled language partition for the first system. Source of record for the partition: `openspec/specs/language-partition/spec.md`. Source of record for the kernel: `openspec/specs/lean-kernel/spec.md`.

## Partition

| Language | Role | Contains an evaluator? |
|---|---|---|
| Lean 4 | The only semantics language. The circular evaluator is Lean 4 source, and the proofs talk about that source. | Yes. This is the only one. |
| Zig | The host: the operating-system process. It handles files, allocation, and the REPL. It loads the Lean runtime and returns the kernel's result. | **No.** It never re-states the semantics or grows a second `eval`. |
| Rust | Absent. It is not a language of the first system. | n/a |

## Circularity

Circularity means the metacircular theorem. An interpreter is a term of the language. On a small, named fragment, evaluating that term on a program equals evaluating the program directly.

The kernel change, `add-lean-circular-kernel`, landed this theorem. The fragment is every quote-free term. The evaluator is Lean 4 source in `kernel/`. `metacircular` and `coverage` are proved (`46048e9`). One level. The Zig host and a C ABI are not part of that landing.

## Boundary

The proof boundary is the call from the Zig host into the Lean kernel. The `lean-c-abi` spike (`docs/spikes/lean-c-abi/finding.md`, Lean 4.35.0, Zig 0.16.0) returned `71` from one unboxed exported function to a Zig host that does not contain the formula. The spike shows the call is feasible. It does not land the call. `add-zig-host` owns initialization, allocation, and the real interpreter ABI.

## Why

- **Lean owns semantics.** A model beside a Zig or Rust interpreter can drift. With `eval` in Lean, the program and the proof are the same artifact, and Lean 4 compiles, so the kernel can run.
- **Zig is the host.** The process needs explicit allocation, files, and a small binary. The host does not duplicate semantics.
- **Rust is out.** The borrow checker is real but is not a Lean theorem. Keeping Rust would add a third compiler to every semantics change. A translator carrying Rust into Lean would make Rust the source of the evaluator, which reverses the decision that Lean is the semantics.

## Downstream changes

- `add-lean-circular-kernel`: folded. The evaluator and the metacircular theorem are `openspec/specs/lean-kernel/spec.md`.
- `add-zig-host`: the process and the C ABI call. Not started here.

The partition is the landed artifact those changes cite. This kernel does not add a Zig host or a C ABI.
