# move-host-to-reflect

## Syntax

Indentation carries structure, as in Wisp. There are few parentheses to write.

### Rules

1. **A line is an application.** `f a b` applies `f` to `a`, then the result to `b`.
2. **Indented lines are further arguments** of the line above.
3. **A colon opens a group** that runs to the end of the line. `f : g x` is `f (g x)`.
4. **Parentheses group** within a line. A group of one item is that item.
5. **A block** is lines at one indentation. Every line but the last is a `let` or a `def`. The last line is the block's value.
6. **`;`** starts a comment.

### Forms

| Form | Meaning |
|---|---|
| `fn x y` then a body | a function of `x`, then `y` |
| `let x value` | binds `x` for the rest of the block |
| `def f x y` then a body | binds `f` for the rest of the block; `f` may call itself |
| `42` | a number |
| `[1 2 [3 4]]` | data, taken as written; nothing inside is evaluated |
| `quote e` | the program `e` as data |
| `succ n`, `cons head tail` | build data |
| `case e` then arms | take data apart |

`case` arms are `zero`, `succ m`, `empty`, and `cons head tail`, each followed by a colon or an indented body. A missing arm is an error if reached. `interpret` is a name bound to the interpreter term.

### Examples

```
; identity applied to itself
let id : fn x : x
id id
```

```
; count down to zero
def countdown n
  case n
    zero : 0
    succ m : countdown m

countdown 1000
```

```
; add two numbers
def add a b
  case a
    zero : b
    succ m : succ : add m b

add 2 3
```

```
; append two arrays
def append xs ys
  case xs
    empty : ys
    cons head tail
      cons head : append tail ys

append [1 2] [3 4]
```

```
; a program is data
quote : fn x : x
```

prints `[1 0]`.

```
; build a program and run it
let code : cons 3 : cons (quote 41) []
interpret code
```

builds `[3 [2 41]]`, the code of `succ 41`, and prints `[0 [1 42]]`: the outcome, as data.

### Reading

The reader is a Lean function from bytes to `Option Term`, with an error message on failure. Names become de Bruijn indices. An unknown name is refused. `def` with a self-call becomes the call-by-value fixed point the interpreter already uses. A missing `case` arm becomes a term that evaluates to `wrong`. `quote e` becomes `lit (reify e)`, with `e`'s free names resolved first; a name bound outside the quotation is refused inside it.

Tabs are refused in indentation. Indentation is spaces.

## Rendering

| Outcome | Text |
|---|---|
| a number | `42` |
| an array | `[1 2 [3 4]]` |
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

- wisp-reader-size: claim: the reader is under 300 lines of Lean and needs no parser library. confidence: medium. verification: none. synthesis path: this change.
