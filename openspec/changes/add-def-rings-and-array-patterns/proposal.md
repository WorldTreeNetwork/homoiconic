# Let definitions name one another, and take arrays apart by length

> Disposition: ACTIVE BUILD, 2026-11-14. Beads homoiconic-q59.37, homoiconic-q59.38.

The owner asked for this work directly on 2026-11-14.

## Why

Two things made the example programs longer than what they say. A `def` saw
itself and what came before it, so `examples/calc.hom` handed `expr` down
through `factor`, `products`, `term` and `sums` as an argument. A `case` arm
could only split `[head, ...tail]`, so a tape `[left, cell, right]` or a pair
`[left, right]` was taken apart with helper functions or with one `case` for
each item.

## What changes

- **A run of definitions.** A run is the `def`s of one block with no `let`
  between them. In a run, a name that is bound nowhere else and that a later
  `def` of the run defines is that definition. A name that is bound where it is
  used, by a parameter, an earlier binding or one of the reader's own names
  (`add`, `interpret`, `ask`, ...), means what it meant before, so a program
  that read before reads to the same term.
- **How a run reads.** Each definition is bound after the ones it mentions.
  Definitions that mention one another in a ring are read as one recursive
  function of a number that chooses the member, and each member is then bound
  to its name. A definition in no ring is bound as before: a function, under
  the fixed point when it mentions itself. A run in which no definition
  mentions a later one keeps the order it was written in.
- **Array patterns.** `[a, b, c]` takes an array of exactly three items, and
  `[a, b, ...rest]` one of two or more, `rest` being the array after them. An
  item is a name or `_`. `[]` and `[head, ...tail]` are the same patterns with
  no item and with one. The array arms are tried in the order written. An array
  no arm takes goes where a scrutinee with no arm went before: to the catch-all
  arm when there is one, and otherwise the `case` is `wrong`.
- **Refused.** An item that is not a name or `_`; `...rest` with no item
  before it or with anything but `]` after it; two arms for the same length;
  an arm below an arm that takes every array it would.
- **Examples.** `examples/calc.hom` names `expr`, `term`, `products`, `sums`
  and `factor` directly. `examples/brainfuck.hom` takes the tape and a run's
  answer apart by pattern. `examples/words.hom` does the same for the pair
  `halves` answers and for a list of one item. What they print is unchanged.

## What does not change

`Data`, `Term`, evaluation, the interpreter, the machine, the byte form and
every theorem. Only the reader changes, and it is tested, not proved. No
operation or term is added: a ring is `recur` applied to a function, and an
array pattern is nested `dcase`.

## Not in this change

- An item of an array pattern that is itself a pattern or a number. The
  reader refuses it.
- Functions kept in arrays, the other half of `homoiconic-q59.38`. That is a
  decision about the language and is the owner's: `homoiconic-q59.39`.
- Definitions separated by a `let` do not see later ones. The `let` is
  evaluated where it stands, and a definition above it cannot be bound after
  it.

## Notes

- Of two later definitions of one name, a use above both means the nearer.
- A definition that takes no parameter is a value worked out where it is
  bound. In a ring it is worked out again at each use, and two of them that
  need one another at once, `def a = b` and `def b = a`, do not end.
- A name written twice in one pattern is the later one, as `fn x x -> x` is.
