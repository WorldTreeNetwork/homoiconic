# Give data two more kinds: text and channel names

> **FOLDED 2026-11-17** into `openspec/specs/code-as-data/spec.md`, `channels`, `wire-bytes`, `state-store`, `surface-syntax`, `bytecode-machine` and `zig-host`. Archived. Beads homoiconic-q59.35 (closed), homoiconic-q59.36 (closed); the unikernel image is homoiconic-q59.40, and a review suggestion is homoiconic-q59.41.
>
> Was: ACTIVE BUILD, 2026-11-14. The owner asked on 2026-11-14 for these beads to be carried through; two reads by another model family found the semantics sound and their four required fixes are answered in the documents. The implementation was accepted on 2026-11-17 with no required fix.

## Why

Data is numbers and arrays, and two things are wrong because of it.

A channel name is a number. A process is handed every name its starter or
sender holds whose number occurs anywhere in its start data or a message, so in
`examples/sieve.hom` every filter holds channel 0, which it was never given:
the number 0 occurs in the quoted code it is started on (`homoiconic-q59.36`).
A name has to be a kind of value that a number is not.

A string is the array of its code points. Nothing tells text from numbers, it
prints as numbers without `run --text`, and each character is a list cell
(`homoiconic-q59.35`).

## What changes

- `Data` gains `text` (a list of characters, each a Unicode scalar value)
  and `name` (a channel name, carrying a number). One rule covers both:
  `succ`, `cons`, `case` and the operation number of `prim` see every data
  value as a number or as a list. `case` takes an arm for every data value;
  the other three go `wrong` where the view does not fit.
  - A name is seen as its number. `case` takes the zero or successor arm,
    `succ` gives the next plain number, consing onto it is `wrong`, and as an
    operation number it runs that operation. None of these gives a name.
  - Text is seen as the list of its code points. `case` takes the empty arm
    for empty text, otherwise the head is the first code point, a number, and
    the tail is the rest, a text. Consing onto text gives an array. `succ` of
    text and text as an operation number are `wrong`.
- `interp` is the same term. `reflective`, `reflective_coverage`,
  `reflective_env` and `tower` are proved again for every term, with the same
  statements. The machine and the lazy machine gain the same cases, and their
  theorems are proved again with the same statements.
- Equality (operation 5) tells text from an array and a name from a number.
  The operands of arithmetic stay plain numbers: `add` of a name and 0 is
  `[]`, not the name's number. A name counts as a number only where `case`,
  `succ` and the operation number of `prim` look. The first table gains `text` (7) and `codes` (8), between text and the array
  of its code points.
- Channels. `[0]` is answered with a name value. A send `[1, name, message]`
  and a receive `[2, name]` take a name value; with a number there they are
  requests to the outside. A process is handed the names its starter or
  sender holds that occur as name values in its start data or a message. A
  number hands over nothing. A process holds a name at most once. Events and
  schedule files keep plain numbers.
- Bytes. Text is a CBOR text string (major type 3), definite length, valid
  UTF-8. A name is CBOR tag 39 over its number. A stored piece that is text or
  a name is written the same way, and a text is one piece, not cut.
- Surface. `"..."` denotes text. `'c'` stays a number. Text renders in quotes
  with the reader's escapes and reads back. A name renders as `#3`, which the
  reader does not read. `run --text` writes a text result raw, and an array is
  no longer guessed to be text. `text` and `codes` are names in the reader.
- Examples: `calc.hom` and `words.hom` end in `text`; `guess.hom` is rewritten
  so the second process has the name value and does not hold it;
  `number.hom` is new.

## What does not change

`Term`, `reify`, `unreify`, `interp`, `evalTerm`, the instruction set, the
request driver, `Drive`, `Settle`, `Turn`, the log, and the statement of
every theorem. `plan` changes only as the channel rules do: a new channel is
answered with a name value, and a receiver gains only names it lacks. `Event` and the text form of a schedule. The byte form of a
number, an array, a reference, and of any program with no string literal. The
Zig host: it still reads nothing.

A name value is not a key. Holding is the scheduler's list, as before, and a
process can come to have a name value it does not hold. The reader and
renderer, the byte form and saving are tested, not proved, as before.

## What is not carried over

A program with a string literal has new bytes. A kept node made before this
change holds its names as numbers, which are no longer names. Kept states are
not migrated and the fixtures are made again; an old root is neither refused
nor converted, and a send or receive in it on a number is now a request to
the outside. Text is not normalised (NFC), which dCBOR asks for: two
different sequences of Unicode scalar values are two texts. A character is
still a list cell in memory; the representation is left for later.
Byte strings as data are not in this change.
