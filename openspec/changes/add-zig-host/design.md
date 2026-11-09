# add-zig-host

## Call

`kernel_run` takes the program as a pointer and a length and returns one `uint32`. Zig holds those bytes and the `extern` declaration. Lean parses them into a `Term` and calls `evalFuel` at `[]`. The fuel is one finite value large enough for the scenarios. `omega` returns `none` at every fuel, so the same value covers it.

The product entry is `evalFuel` on the program. The metacircular route stays the theorem. This export does not apply `interpreterBody`.

## Program text

Whitespace separates tokens. The grammar is:

```
term = decimal | "[" term "]" | "(" term term ")"
```

A decimal is a de Bruijn index, nearest binder is `0`. Brackets are a lambda. Parentheses are an application of two terms. Quote has no form. Any other byte is a parse failure, and the export returns the `none` code.

| Program | Text |
|---|---|
| identity | `([0] [0])` |
| open variable | `0` |
| open lambda | `[1]` |
| unbound function, diverging argument | `(0 ([(0 0)] [(0 0)]))` |
| `omega` | `([(0 0)] [(0 0)])` |

## Result code

| `evalFuel` result | Code |
|---|---|
| `some` of a closure | `0` |
| `some` of `unbound i` | `2 * i + 1` |
| `none`, including a parse failure | `4294967295` |

`unbound 0` is code `1`.

## Link

Repeat the spike's path: `lean -c`, `leanc -c` to an object, `zig build-obj` for the host, `leanc` links the two objects. Do not pass `-lc++` to Zig. Do not ship a dylib.

The arithmetic spike did not call the runtime initializer. A parser and `evalFuel` allocate. The initializer is part of this change once the hypothesis below is `go`.

## Unverified hypotheses

- lean-runtime-init: claim: object-linking an exported Lean function that parses one program and calls evalFuel, after the host runs the package initializer, returns the codes in this design. The lean-c-abi spike linked unboxed arithmetic and did not initialize the runtime. confidence: high. verification: empirically-tested. synthesis path: add-zig-host. spike-artifact: docs/spikes/lean-runtime-init/finding.md. Validated by spike lean-runtime-init on 2026-11-08. — go
