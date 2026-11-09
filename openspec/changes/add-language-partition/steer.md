# steer add-language-partition

**When.** 2026-11-08
**Depth.** standard

## Decided
- Language partition: Lean kernel, Zig host (user)
  Why: The evaluator is Lean 4 source. Zig is the process and contains no eval. Rust is out of the first system.
- Circularity: Metacircular (user)
  Why: An interpreter is a term of the language. On a small fragment, evaluating it on a program equals direct evaluation.

## Skipped
- none

## Feeds change
Semantics live in Lean 4. Zig is the host. Rust is absent. The kernel change owns the metacircular theorem. The host change owns the C ABI call.
