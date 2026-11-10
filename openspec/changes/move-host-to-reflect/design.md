# move-host-to-reflect

## Syntax

Approved by the user on 2026-11-09, replacing a first Wisp-style proposal. The surface is from the ML family. Lisp is kept for one thing: a program is plain data of a fixed, simple shape.

### Rules

1. **Application is juxtaposition.** `f a b` applies `f` to `a`, then the result to `b`. It binds tighter than any operator.
2. **Indentation continues a line.** Lines indented under a line belong to it.
3. **Parentheses group.**
4. **A block** is lines at one indentation. Every line but the last is a `let` or a `def`. The last line is the block's value.
5. **`;`** starts a comment.

### Forms

| Form | Meaning | From |
|---|---|---|
| `fn x y -> body` | a function of `x`, then `y` | ML |
| `let x = value` | binds `x` for the rest of the block | ML |
| `def f x y = body` | binds `f` for the rest of the block; `f` may call itself | ML |
| `42` | a number | |
| `[a, b, ...rest]` | an array; items are expressions; `...rest` continues with an array | JavaScript, Elixir |
| `e + 1` | the successor of `e` | |
| `case e` then arms `pattern -> body` | take data apart | ML |
| `quote e` | the program `e` as data | Lisp |
| `~e` inside a quotation | put the code `e` evaluates to in this place | MetaML, Julia, Lean |
| `x \|> f` | `f x` | F#, Elixir |

Patterns in this change are one level deep: `0`, `m + 1`, `[]`, `[head, ...tail]`, and a name or `_` for anything. A `case` with no arm for the data it meets is an error when reached. `interpret` is a name bound to the interpreter term.

### Examples

```
def append xs ys =
  case xs
    [] -> ys
    [head, ...tail] -> [head, ...append tail ys]

append [1, 2] [3, 4]
```

prints `[1, 2, 3, 4]`.

```
def add a b =
  case a
    0 -> b
    m + 1 -> add m b + 1

add 2 3
```

prints `5`.

```
def countdown n =
  case n
    0 -> 0
    m + 1 -> countdown m

countdown 1000
```

```
quote (fn x -> x)
```

prints `[1, 0]`, the identity function's code.

```
; code with a hole in it
let inner = quote 41
interpret (quote (~inner + 1))
```

prints `[0, [1, 42]]`: the outcome, as data.

### Reading

The reader is a Lean function from bytes to a term, or an error message with line and column.

- Names become de Bruijn indices. An unknown name is refused.
- `def` with a self-call becomes the call-by-value fixed point the interpreter already uses.
- `[a, b, ...t]` becomes `cons a (cons b t)`. `e + 1` becomes `succ e`. Any other use of `+` is refused until arithmetic exists.
- Arms become the one case form. A missing arm becomes a term that evaluates to `wrong`.
- `quote e` with no splice becomes `lit (reify e)`. With splices it becomes code that builds that data, with each `~e` evaluated in its place.
- A quotation may not mention a name bound outside it. A splice may only appear where no binder of the quotation encloses it. Code is index-based, so a fragment moved under a binder would change meaning without warning. Both are refused. Lifting these needs index shifting and is later work.
- Tabs are refused in indentation.

### Later, in this order

Recorded so the reader is built to grow into them. None is in this change.

1. **`interpret` at native speed.** `reflective` says the interpreter and direct evaluation agree, so the machine may run code-as-data directly and skip the factor of about 52. This is a machine primitive with a proof obligation, and it is what makes metaprogramming cheap.
2. **Nested patterns and declared constructors.** `data Result = Ok x | Err e` names tagged arrays, in expressions and in patterns. Needs a pattern compiler in the reader.
3. **Quotation patterns.** `case code` with an arm `quote (~f ~a) -> ...`, so programs that transform programs never mention tag numbers. Rests on 2.
4. **Macros.** A `macro` is a function from code to code that the reader runs while reading. Index-based code cannot capture a name by accident.
5. **Languages as interpreters.** `using lang` before a block runs the block's code under a user-written interpreter. Metering, tracing, and sandboxing are written this way, and `tower` is the theorem under it.
6. **Functions rendered as code**, by decompiling, in place of `<function>`.
7. With text as a primitive: string literals, user-defined operators, and quoters for foreign syntax.
8. With requests: `send`, `receive` with pattern arms, and handlers for named operations, in direct style.

## Rendering

| Outcome | Text |
|---|---|
| a number | `42` |
| an array | `[1, 2, [3, 4]]` |
| a function | `<function>` |
| unbound index | `error: unbound 3` |
| misuse | `error: wrong` |
| budget exhausted | `no result within N steps` |
| not a program | `syntax error: ` and a message with line and column |

Data renders in the same form the reader accepts, so printed data can be pasted back as a literal.

## Call

`reflect_run` takes a pointer and length for the program, a pointer and capacity for the output, and a step budget. It returns the number of bytes the rendering needs. If that is more than the capacity, nothing useful was written and the host calls again with a larger buffer. Zig holds the bytes and prints them. Lean reads, compiles, runs `run budget (load (compile t))`, and renders.

`kernel_run` and the result code stay until `retire-circular-kernel`.

## Who does what

- The owner settles the syntax with the user, then writes the reader's specification as examples: program text and the term it must read as.
- The reader, the renderer, the export, and the Zig side are handed off. They are ordinary code with examples to meet.
- No file under `kernel/Reflect/` that a contract depends on is edited.

## Unverified hypotheses

- reader-size: claim: the reader is under 500 lines of Lean and needs no parser library. confidence: medium. verification: none. synthesis path: this change.
