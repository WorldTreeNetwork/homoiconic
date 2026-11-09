# add-language-partition

## Settled

- The circular evaluator is Lean 4 source. The proofs talk about that source.
- Zig is the operating-system process: files, allocation, the REPL. It loads the Lean runtime and returns the kernel's result.
- The first theorem, owned by the kernel change, is metacircular. An interpreter is a term of the language. On a small fragment, evaluating that term on a program equals evaluating the program directly.
- Rust is not a language of the first system.

## Why Lean owns semantics

A model beside a Zig or Rust interpreter can drift. Putting `eval` in Lean makes the program and the proof the same artifact. Lean 4 compiles, so the kernel can run. The host does not re-state the semantics.

## Why Zig is the host

The process needs explicit allocation, files, and a small binary. That is Zig's job. The proof boundary is the call into the Lean kernel. Zig does not grow a second `eval`.

## Why Rust is out

The borrow checker is real and it is not a Lean theorem. Keeping Rust would add a third compiler to every semantics change. The translator that would carry Rust into Lean would also make Rust the source of the evaluator, which reverses the decision that Lean is the semantics.

## Downstream

`add-lean-circular-kernel` builds the evaluator and the theorem. `add-zig-host` builds the process. Neither starts until this partition is the landed artifact they can cite.

## Unverified hypotheses

- `lean-c-abi`. A Zig host can call the compiled Lean 4 kernel through the C ABI without reimplementing `eval`. Confidence: medium. Verification: not empirically tested. Synthesis: none (`docs/spikes/lean-c-abi/finding.md` is missing). This change does not land that call. `add-zig-host` owns it, and the spike runs before that node is acted on.

## ADR

`ARCHITECTURE.md` will say: semantics are Lean 4; the host is Zig; Rust is absent; circularity means the metacircular theorem on a named fragment; the host contains no evaluator.
