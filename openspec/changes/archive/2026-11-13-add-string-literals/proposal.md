# Write strings in programs and print results as text

> **FOLDED 2026-11-13** into `openspec/specs/surface-syntax/spec.md` and `openspec/specs/zig-host/spec.md`. Archived. Bead `homoiconic-q59.34`: the text below and `tasks.md` cite `q59.33`, which in the tracker is a NodeCheck task, and cite `q59.34` for a text kind of its own, which is `homoiconic-q59.35`.

## Why

Programs that read or write text had to spell it as numbers. The data type is
not changed here: a string is the array of its code points, which is what a
`case` already takes apart. A text kind of its own in `Data` is
`homoiconic-q59.34`.

## What changes

- The reader takes `"..."` as the array of the text's code points and `'c'` as
  the number of one ASCII character. Escapes are `\n`, `\t`, `\\`, `\"`, `\'`.
  A string is UTF-8 and ends on its line. Both may be used inside a quotation.
- `reflect_interp` takes `flags` where it took `bytes`: bit 0 says the program
  is its byte form, bit 1 asks for a result that is an array of code points to
  be written as the text it spells. `host/out/run` accepts `--text`.
- Examples: `calc.hom` (a calculator over text), `words.hom` (merge sort under
  orders passed as functions), `power.hom` (code built as data and run),
  `sieve.hom` (primes by a line of processes).

## What does not change

`Data`, evaluation, the interpreter, the machine, the byte form and every
theorem. An array of code points and a string are one value: nothing in a
program or on the wire tells them apart, and without `--text` a string prints
as numbers. The reader and the renderer are tested, not proved.
