# Design: text and names in `Data`

## 1. The rule, and why it is forced

`interp` answers a wrong outcome as the data `[2]`. It tests a value only with
its own `case`, and the theorems hold for every operation table, so it cannot
use an operation to test a kind. It then builds its answer with its own `succ`,
`cons` and `prim` on the same value. So:

> A kind that `case` sends to the zero or successor arm must be a value under
> `succ` and as an operation number, and `wrong` as the tail of `cons`. A kind
> that `case` sends to the empty or non-empty arm must be `wrong` under `succ`
> and as an operation number, and a value as the tail of `cons`. A kind that
> `case` goes wrong on cannot exist.

Any other choice makes `interp` itself go wrong where it must answer `[2]`, or
answer `[2]` where the program has a value. No change to `interp` can repair
that: going wrong cannot be caught, so a term cannot tell a name from its
number by the one way they would differ.

### D1. A name is seen as its number

`succ #k` is the plain number `k + 1`. `case #0` takes the zero arm;
`case #(k+1)` takes the successor arm and binds the plain number `k`.
`cons x #k` is `wrong`. `prim #k d` is `op k d`.

- Rejected: `succ #k` is `wrong`. `reflective` fails for `succ (lit #0)`.
- Rejected: `succ #k` is `#(k+1)`, or the predecessor is a name. `interp`
  mirrors both, but arithmetic would then make names. Holding would still be
  safe; there is no use for it.
- Not chosen (open question 2): a name seen as the empty list. Its number
  would be invisible to `case`. The rule above allows it.

### D2. Text is seen as the list of its code points

A text holds Unicode scalar values: code points with the surrogates
(U+D800 to U+DFFF) left out, which is what a Lean `Char` and valid UTF-8 hold.
Its code points, below, are the numbers of those scalar values.

`case` on empty text takes the empty arm. Otherwise it binds the first code
point, a number, at 1 and the rest, a text, at 0. `cons x t` is the array of
`x` followed by the code points of `t`. `succ t` and `prim t d` are `wrong`.

`cons (head t) (tail t)` is therefore an array, not `t`. Equality tells them
apart; `case` does not. `text` (operation 7) makes text again.

### D3. How the rules are written: new rules beside the old ones

`Direct` gains twelve rules; no existing rule changes.

    succName, consTailName, caseNameZero, caseNameSucc,
    primNameArgError, primNameArgClosure, primNameData        (names)
    succText, consText, caseTextNil, caseTextCons, primCodeText   (text)

- Rejected for now: one view function (`Data.num?`, `Data.uncons?`) with the
  thirty rules restated over it. A later kind would then need no rule. But
  every existing proof case is written against constructor patterns
  (`walk`, `sdesc`, `impossible`, `simp [step]`), and all of them would be
  rewritten. With new rules, every existing case stands and each new case is a
  copy of its neighbour. Look at this again when a third kind (byte strings)
  comes.

### D4. Text is a `List Char`, behind three functions

New file `kernel/Reflect/Text.lean`, imported by `Syntax.lean`:

    def Text.uncons? : List Char → Option (Nat × List Char)  -- first code point, rest
    def Text.codes   : List Char → List Nat
    def Text.ofCodes? : List Nat → Option (List Char)        -- none if an item is not
                                                             -- a Unicode scalar value

`Data.text : List Char → Data`. A `Char` is a Unicode scalar value, so a text
holds nothing else. The two case rules are plain patterns, as `caseNil` and
`caseCons` are:

    caseTextNil  (hs : Direct env s (.value (.data (.text []))))
                 (h : Direct env n o)
    caseTextCons (hs : Direct env s (.value (.data (.text (c :: r)))))
                 (h : Direct (.data (.text r) :: .data (.nat c.toNat) :: env) cb o)
    consText     (ha : … (.data x)) (hb : … (.data (.text t))) :
                 Direct env (.cons a b) (.value (.data (.arr (x :: (Text.codes t).map .nat))))

`evalFuel`, `step` and `lCase` match the same two patterns. `Text.uncons?` is
the same split as a function, for code that is not a proof. No proof unfolds
`Text.codes` or `Text.ofCodes?`. Nothing is proved about the three functions;
that `codes` and `uncons?` agree is tested in `ReflectRun.lean`.

Bytes are made and read only at the UTF-8 boundary, and each place converts
in the open:

- Reading bytes (the wire reader, the piece reader, the source of a program):
  `String.fromUTF8?`, which refuses bytes that are not UTF-8, then
  `String.toList`.
- Writing bytes (the wire writer, the piece writer, the renderer, `--text`):
  `String.ofList`, then `String.toUTF8`. The length written in a text's CBOR
  head is the count of those UTF-8 bytes, not of characters. The size `cut`
  compares is a different count: the whole byte form of the piece, head
  included (D7).

Nothing inside `Reflect/` but `Text.lean` mentions `String` for a text.

Cost: a step of `case` on a text is constant time and a walk is linear in the
length; `codes` is linear. A character is a list cell in memory, as it is
today in an array of code points. The bead names that cost and this change
does not answer it: the owner decided on 2026-11-12 that the representation
is optimised later. The three functions stay so that most callers need no
edit when it is; the two case rules would then be restated. A `case` walk and
a `codes` walk over a text of 100,000 characters are measured after step 2
and both numbers go in `docs/LEARNINGS.md` (a task, not a risk).

- Rejected: a Lean `String`. It saves the list cell per character. But
  `uncons?` must copy the rest (`String.drop` gives a slice in Lean 4.35 and
  must be copied to keep one form per text), so a walk by `case` is quadratic
  in the length; and the two case rules would carry a side equation
  (`Text.uncons? t = none`, `= some (c, r)`), the first premises that are not
  patterns, with extra work in `direct_deterministic`, `stuck_core` and
  `MachineProof.rev`.
- Rejected: text with a start offset. Two forms of one text; derived equality
  and the byte form would need normalising.

### D5. Equality and the first table

`Data` keeps `deriving Repr, BEq`; the derived `==` already tells the four
constructors apart, so operation 5 needs no change. Two operations are added,
each taking its operand itself, not an array of operands:

- 7, `text`: an array whose items are all numbers that are Unicode scalar
  values gives the text of those code points; a text gives itself; anything
  else gives `[]`.
- 8, `codes`: a text gives the array of its code points; an array whose items
  are all numbers that are Unicode scalar values gives itself; anything else
  gives `[]`. `codes ""` is also `[]`.

`arithNames` gains an arity so the reader can make `text` and `codes`
functions of one argument. No operation makes a name.

`arith` is not widened for names. Its arithmetic lines match on plain
numbers (`.arr [.nat a, .nat b]`), so an operand that is a name falls to the
last line: operation 0 on `[#3, 0]` answers `[]`, and on `[3, 0]` answers 3.
Operations 1 to 4 and 6 likewise. So:

- Arithmetic operands remain plain numbers.
- A name is accepted as a number only where the language's own constructs
  look: the scrutinee of `case`, the operand of `succ`, and the operation
  number of `prim` (D1). Section 1 forces those three and no more.
- Equality also tells the constructors apart: `equal #3 3` is 0.

A program can therefore tell a name from its number by arithmetic as well as
by equality. It gets the plain number of a name with `case`, or with `succ`
and operation 1.

### D6. Channels

`kernel/Reflect/Channel.lean`:

    def Data.mentions : Data → Nat → Bool
      | .name k, n => k == n
      | .arr xs, n => mentionsAny xs n
      | .nat _, _ => false
      | .text _, _ => false

    def classify
      | .arr [.nat 1, .name ch, v] => .send ch v
      | .arr [.nat 2, .name ch] => .receive ch
      …                                   -- [0] and [3, program, start] as now

    /-- Add what is handed over, leaving out what is already held. -/
    def gain (held' handed : List Nat) : List Nat :=
      handed.filter (fun n => !held'.contains n) ++ held'

- `Step.fresh` and `stepRun` answer with `.name n` where they had `.nat n`.
  `plan` in `Node.lean` likewise.
- `Step.comm`, `stepRun` and `plan` give the receiver
  `gain held' (grant held v)` where they had `grant held v ++ held'`.
- `grant`, `Step.spawn`, `Req`, `Event`, `Proc.held : List Nat` and
  `Config.names : List Nat` are unchanged. A held name is kept as its number;
  only values in programs are `name`.
- `[1, 3, m]` and `[2, 3]` with a plain number fall to `classify`'s last
  line: requests to the outside. No new kind of request.
- Events keep plain numbers: `[0, i, n]`. A schedule is the scheduler's
  record, not a message, so a number in it hands over nothing, and schedule
  files written before this change still read.
- Only start data is scanned at a start, not the program. A starter can
  therefore splice a name into a program, and the process started has the
  value and does not hold it (open question 3).
- The duplicate entries go now: the rule of holding, the printed lines and
  the roots of kept nodes all change in this step anyway. New theorem
  `Network.held_nodup`: no process of a program holds a name twice. It rests
  on an invariant that is new here: every held list has no repeat and is
  within `cfg.names`.
- A name value is not authority. `Step.comm_held`, `Step.held_from` and
  `Network.held_issued` keep their statements.

Rendering: `holds [#1, #0]`; `waiting on [1, #0, 7]`. The schedule line is
unchanged.

`examples/guess.hom` becomes (as landed; the text first written here put the
splice under the binder `fn nothing` of its quotation, which the reader
refuses, section 7):

    ask [0] (fn ch ->
      let body = quote (ask [2, ~[2, ch]] (fn x -> x))
      ask [3, [1, body], []] (fn started ->
        ask [1, ch, 7] (fn sent -> [])))

`~[2, ch]` is the code of a literal of the name, and `[1, body]` is the code
of a function with that body. Process 1 waits on `[2, #0]`
and holds `[]`. `examples/number.hom` is the old text: process 1 asks `[2, 0]`
with a number, which is the outside's. In both, `[2, 0, 1]` is refused.

### D7. Bytes

- Text: major type 3, definite length in the shortest form, then UTF-8. The
  writer goes from the `List Char` through `String.ofList` and
  `String.toUTF8`; the length is the count of those bytes. The reader refuses
  bytes that are not valid UTF-8 (`String.fromUTF8?`) and keeps
  `String.toList` of the rest. Not normalised; dCBOR asks for NFC and this project does not do it, as with
  tag 2 for large numbers.
- Name: tag 39 over the number in the number's own form (an unsigned integer,
  or tag 2 at 2^64 and above). `#3` is `d8 27 03`. Tag 39 is registered at
  IANA as "Identifier" (checked 2026-11-14), which is the meaning here. The
  registry has no private range; 6 to 15 are unassigned but in the Standards
  Action range, where a private use may later collide. The reader refuses
  tag 39 over anything but a number, and every tag but 2 and 39. Tag 39 over
  tag 39 is refused: a name's number is not a name. So are tag 2 over a
  number that fits an unsigned integer, a tag head in a longer form than it
  needs (`d9 00 27`), and an inner number in a longer form. The bytes of a
  name's number are bounded as a plain number's are: fewer than 2^64 of them
  under tag 2. Wrapping a number in a name does not lift that limit.
- No collision with a reference. A reference is a bare byte string (major
  type 2) of 32 bytes. Text is major type 3. A name and a large number are
  tags (major type 6); the byte string inside tag 2 is read by the tag's own
  branch and is never an item. Reading data still refuses a bare byte string.
- `Wire.Item` gains `text` and `name`. `Item.toData` is `none` only for
  `bytes`.
- Pieces. `Reflect.P` gains two leaves, `text : List Char → P R` and
  `name : Nat → P R`. `Data.toP`, `P.toData`, `P.hyd`, `Unf` and `UnfD` gain
  a line each. `Wire.pieceItem` writes a text piece as the text and a name
  piece as the tagged number; `itemPiece` reads them back. `Wire.Item.text`
  carries the `List Char` too, so the only conversions are the two in the
  byte reader and writer. Neither is an
  array, so neither can be taken for a pair `[0, h, t]` or a function
  `[1, body, captured]`.
- The lazy machine takes text apart with no fetch, since a text is a leaf.
  `lCase` matches `.text []` and `.text (c :: r)`, as `step` does. `lCons` with `.text t` under the
  head builds the list of code points. `lSucc` and `lCheckNat` pass `.name n`
  as the plain machine does; `lPrim` takes `.name n` as the operation number.
- Saving does not cut text. `cut` treats a text as it treats a number,
  `kept size (.text t)`: stored whole under its hash when the piece's byte
  form, the CBOR head and the UTF-8 bytes together, is larger than the size,
  and kept in place otherwise. A text of 24 ASCII characters is 26 bytes
  (`78 18` and the 24), so at size 25 it is stored. A long text is one piece
  and is fetched whole.

### D8. Surface

- `"..."` reads as `lit (text …)`; `Tk.str` carries the `List Char` the
  literal holds. The source is UTF-8 bytes; the reader decodes it once and
  the tokens hold characters from there on. `'c'` stays
  the number of one ASCII character: the head `case` gives is a number, and
  `equal c ' '` has to hold of it.
- `renderData`: a text in double quotes with `\n`, `\t`, `\\` and `\"`
  written as escapes and every other character as itself; the renderer goes
  through `String.ofList` to make the line. The reader takes
  every byte but a line feed and a backslash inside quotes, so rendered text
  reads back. A name is `#` and its number, which does not read.
- `--text` (bit 1 of `flags`): a result that is a text is written raw, as
  the UTF-8 of its characters. Every
  other result is written as without the flag. `textOf` and the rule about
  printable code points are deleted (open question 4).
- `text` and `codes` are built-in names of one argument, usable in a
  quotation. A program's own binding wins, as for `add`.

### D9. Everything else that matches on `Data`

Counts are lines that mention a `Data` constructor
(`grep -E '\.nat\b|\.arr\b'`), not match sites.

| File | Lines | What changes |
|---|---|---|
| `Reflect/Syntax.lean` | 16 | `Data` gains two constructors. `reify` unchanged. `unreify` unchanged: text and a name fall to its last line and are no program. `unreify_reify` unchanged. |
| `Reflect/Text.lean` | new | D4: three functions over `List Char`. |
| `Reflect/Semantics.lean` | 32 | Twelve rules; `evalFuel` gains their branches. `reifyValue`, `reifyOutcome` unchanged. |
| `Reflect/SemanticsProofs.lean` | 0 | A case per rule in `direct_deterministic`, `evalFuel_sound`, `evalFuel_mono`, `evalFuel_complete`. |
| `Reflect/Interpreter.lean` | 3 | Nothing. |
| `Reflect/Proof.lean` | 19 | `walk` and `sdesc` gain alternatives; `stuck_case_*` gain four lemmas; `fwd` and `stuck_core` gain cases. |
| `Reflect/Correctness.lean` | 1 | Nothing. |
| `Reflect/Machine.lean` | 14 | `step` gains cases (see the wildcard list). `Code`, `comp`, `decomp` unchanged. |
| `Reflect/MachineProof.lean` | 17 | A case per rule in `fwd`; sub-cases in `rev`. |
| `Reflect/Store.lean` | 15 | D7. |
| `Reflect/StoreProof.lean` | 32 | D7; see proofs below. |
| `Reflect/Arith.lean` | 8 | D5: operations 7 and 8 only. The arithmetic lines are not widened. |
| `Reflect/Request.lean` | 4 | Nothing; `interpreted` matches arrays `interp` builds. |
| `Reflect/RequestProof.lean` | 1 | Nothing expected. |
| `Reflect/Channel.lean` | 12 | D6. |
| `Reflect/ChannelProof.lean` | 0 | `held_from`, `step_forward`, `step_backward`, `stepRun_sound` follow `gain`; `held_nodup` is new. |
| `Reflect/Log.lean` | 6 | `Data.decEq` gains `text`/`text`, `name`/`name` and the twelve mixed pairs (`isFalse nofun`). |
| `Reflect/LogProof.lean` | 0 | Nothing expected. |
| `Reflect/Node.lean` | 3 | `plan`: `.name n`, `gain`. |
| `Reflect/NodeProof.lean` | 3 | The same two edits where `plan` is restated. |
| `Reflect/Examples.lean` | 6 | Nothing, unless a match is exhaustive. |
| `Wire/Cbor.lean` | 10 | D7. |
| `Wire/Form.lean` | 4 | Nothing. |
| `Wire/Piece.lean` | 9 | D7. |
| `Surface/Read.lean` | 5 | D8. |
| `Surface/Render.lean` | 5 | D8. |
| `Surface/Chan.lean` | 11 | Held names print as names. `eventData`, `dataEvent` unchanged. |
| `Surface/Keep.lean` | 35 | The piece-to-data reader near line 236 gains two leaves; held names print as names. The kept form of a node keeps held names and names made as numbers. |
| `Surface/Run.lean`, `Host.lean`, `Bytes.lean` | 1, 0, 4 | `--text`. |
| `Surface/Expect.lean`, `Check.lean` | 4, 2 | Expectations. |
| `ReflectRun.lean`, `WireCheck.lean`, `StoreCheck.lean`, `KeepCheck.lean`, `LogCheck.lean`, `NodeCheck.lean`, `Bench.lean` | 5, 22, 9, 7, 19, 20, 2 | New checks; old ones stand unless a match is exhaustive. |
| `ReflectContract.lean`, `MachineContract.lean`, `StoreContract.lean`, `RequestContract.lean`, `LogContract.lean`, `NodeContract.lean` | — | Not edited. They must still check: that is the acceptance test for "no statement changed". Each imports the umbrella `Reflect`, so each is checked only once every module is rebuilt (section 4). |
| `InterpGate.lean` | new | The early gate (section 4). Imports `Reflect.Correctness` alone. |
| `ChannelContract.lean` | — | Gains `held_nodup`. |
| `host/*.zig`, `host/runtime.c` | 0 | Nothing but the usage line for `--text`, if it describes the old rule. |
| `host/check.sh` | — | Expectations for strings, `--text`, held names, sieve, guess. |

Wildcards that would swallow a new kind without a compile error. Each needs
its new line placed before the wildcard:

- `Machine.step`: `.succ` (`_ :: _` gives wrong), `.cons`
  (`_ :: .data _ :: _` gives wrong), `.checkNat` (`_ :: _` gives wrong),
  `.prim` (the last line is `fault`).
- `Store`: `lSucc`, `lCons`, `lCheckNat`, `lPrim`, `P.toData`.
- `Arith.arith`, `unreify`, `classify`, `Surface.dataEvent`: the wildcard is
  the right answer for text and names. Read each once.
- `Wire.readGo`: the `else` chain.

The proved ones are caught when the machine and store theorems fail. The
`Wire` and `Surface` ones are caught only by tests.

## 2. `interp`, rule by rule

`interp` is not edited. Its data (programs, results, values, environments,
tags) is numbers and arrays as before, so its thirty existing cases stand. For
each new rule, what the unchanged term does:

| Rule | `Direct` | `interp` branch | What it does | Its answer |
|---|---|---|---|---|
| `succName` | `succ t`, `t` gives `#k`: `k + 1` | successor: `case d  A _ A  W _ _ W`, `A = ok (vdata (succ d))` | `case` on `#k` takes the zero or successor arm; its own `succ d` gives `k + 1` | `[0, [1, k+1]]` |
| `succText` | `succ t`, `t` gives text: wrong | the same | `case` on text takes the empty or non-empty arm | `[2]` |
| `consText` | `cons a b`, `b` gives text `t`: `[x, …codes t]` | construction: `case db  W _ W  built _ _ built`, `built = ok (vdata (cons da db))` | empty or non-empty arm; its own `cons` gives the array | `[0, [1, [x, …]]]` |
| `consTailName` | `cons a b`, `b` gives `#k`: wrong | the same | zero or successor arm | `[2]` |
| `caseNameZero` | scrutinee `#0`: the zero branch | analysis: `case d (self z env) m (…) (self ni env) hd tl (…)` | zero arm: `self z env` | the branch's |
| `caseNameSucc` | scrutinee `#(k+1)`: successor branch with `k` bound | the same | successor arm, `m = k`, environment `[1, k] :: env` | the branch's |
| `caseTextNil` | scrutinee `""`: the empty branch | the same | empty arm: `self ni env` | the branch's |
| `caseTextCons` | scrutinee text: non-empty branch, `c` at 1, the rest at 0 | the same | non-empty arm, environment `[1, rest] :: [1, c] :: env` | the branch's |
| `primCodeText` | `prim c x`, `c` gives text: wrong, `x` not run | operation: `case dc  argument _ argument  W _ _ W` | empty or non-empty arm; `x` is not run | `[2]` |
| `primNameArgError` | `c` gives `#k`, `x` an error: the error | the same | zero or successor arm; `argument` runs `x`; `bind` passes the error | the error's |
| `primNameArgClosure` | `c` gives `#k`, `x` a function: wrong | the same | `argument` finds the tag 0 | `[2]` |
| `primNameData` | `c` gives `#k`, `x` gives `d`: `op k d` | the same | its own `prim dc dx` | `[0, [1, op k d]]` |

The thirty existing rules need no row, but each was read, because a text or
a name can now sit wherever a rule has a data value it does not look into:

- `varBound`, `varUnbound`, `lam`, `lit`: lookup and the wrappers keep any
  data. `lit` hands `d` over without looking, so a literal that is text or a
  name is `[0, [1, d]]`, and its program form is still `[2, d]`.
- `appFunError`, `appData`, `appArgError`, `appValue`: function and data are
  told apart by the value's tag, not by the kind of data. A text or a name
  as an argument, or captured, comes through unchanged.
- `succNat`, `succArr`, `succClosure`, `succError`: the old operands and the
  error and tag checks, as before.
- `consArr`, `consHeadClosure`, `consHeadError`, `consTailNat`,
  `consTailClosure`, `consTailError`: the head `x` may now be a text or a
  name. The tag check takes either as data and `cons` keeps it. The closure
  and error paths keep their order: a head that is a function is `wrong`
  before the tail runs.
- `caseZero`, `caseSucc`, `caseNil`, `caseCons`, `caseClosure`, `caseError`:
  the old scrutinees. The head of an array may be a text or a name; the tail
  of an array is still an array.
- `primCodeError`, `primCodeArr`, `primCodeClosure`, `primArgError`,
  `primArgClosure`, `primData`: the old paths with a plain number as the
  operation number. `primData` passes any data to the table and takes any
  data back.

`interp` applied to data that is no program's form is outside the theorem, as
before. There a name is read as a variable index and a text as a list.
`unreify` refuses both.

## 3. Proofs

Mechanical: a new case that copies a neighbour.

- `direct_deterministic`: twelve cases in the form the others have. The two
  text case rules are plain patterns, so they clash as `caseNil` and
  `caseCons` do.
- `evalFuel_sound`, `evalFuel_mono`, `evalFuel_complete`: a case per rule.
- `Proof.fwd`: the error rules and the `cases k` rules are copies. The four
  new case rules go through the last `| _ =>` once `walk` knows them.
- `Proof.stuck_core`: new sub-cases under `succ`, `cons`, `prim`, `dcase`,
  and `stuck_case_name_zero`, `_name_succ`, `_text_nil`, `_text_cons`.
- `MachineProof.fwd`, `rev`: a case per rule.
- `StoreProof`: `toP_name`, `toP_text`, `rv_name`, `rv_text` and their `_mk`
  forms; a `name` and a `text` line in every `cases p' with` of `progress`,
  `lstep_mono`, `lstep_needs`, `hyd_mono`, `hyd_needs`, `UnfD.hyd`,
  `toData_unf`, `Unf.mono`, `Unf.unique`.
- `Log`, `Node`, `NodeProof`: edits of a line or two.

Needs care or a new argument:

- **`walk` commits to the first alternative that applies.** `apply
  Direct.succNat` unifies with a goal whose operand is bound to a name and
  then cannot close it. The new alternatives must name the binding and come
  first: `apply Direct.succName (Direct.varBound rfl)`,
  `refine Direct.consText ?_ (Direct.varBound rfl)`,
  `refine Direct.primNameData (Direct.varBound rfl) ?_`, and the four case
  rules with `(Direct.varBound rfl)`. Getting this order wrong shows as `fwd`
  failing in a case that passed before.
- **`stuck_core` runs at `maxHeartbeats 4000000` today.** It gains about a
  third more cases. If it times out, split it by construct into lemmas; do
  not raise the limit past 8000000.
- **`StoreProof.cons_top`.** Its `hshape` lists the shapes the second entry
  can have; it gains name and text. Its inner `cases p'` gains the text
  tail, where the result is `.cons y (listToP (Text.codes t))` and the proof needs
  `rv_data_mk` at the array of code points. `lPrim_nat`, `lPrim_mono`,
  `lPrim_needs` and `prim_top` are stated for `.nat n` under the argument and
  each needs a `.name n` twin.
- **`Network.held_nodup`.** New. Invariant: for every process, `held` has no
  repeat and every member is in `cfg.names`. `fresh`: `n ∉ cfg.names`, so
  `n ∉ held`. `spawn`: a filter of a list with no repeat. `comm`: `gain` by
  construction. About 60 lines with the `getElem?_set_cases` lemma already
  there.

Not proved, as now: the reader, the renderer, the byte form, saving, the
session.

## 4. Order of work

Two steps. The tree is green and committed after each.

**Step 1, names (fixes the P1 bug).** `Data.name`; the seven name rules;
`evalFuel`; `SemanticsProofs`; `Proof`; `Machine`; `MachineProof`; `Store`;
`StoreProof`; `Log.decEq`; `Channel`, `Node` and their proofs with `gain` and
`held_nodup`; `Wire` tag 39 and the name piece; `Render` and `Chan` and `Keep`
print `#n`; `guess.hom`, `number.hom`; `check.sh`. What compiles first:
`Syntax`, `Semantics`, `SemanticsProofs`, then `Proof` and `Correctness`.
The early gate comes there, before any other file is touched. If `interp`
needs an edit, it shows here.

**Step 2, text.** `Text.lean`; `Data.text`; the five text rules; the same
files in the same order, with the same early gate after `Proof`; `Arith` 7
and 8; `Wire` major type 3 and the text piece; the reader, the renderer,
`--text`; `calc.hom`, `words.hom`; `check.sh`.

Names first because the bug is P1, the step needs nothing from `Text.lean`,
and it is the smaller. Each proof file is opened twice; that is the price of
a green tree in between.

### The two gates

`ReflectContract.lean` cannot be the early gate. It imports the umbrella
`Reflect`, and `kernel/Reflect.lean` imports `MachineProof`, `ChannelProof`,
`NodeProof`, `StoreProof` and the rest. Once `Data` has a new constructor,
those do not compile until their own tasks are done, so a fresh check of
`ReflectContract.lean` must fail at that point whatever `interp` does, and a
check that passes there has read old `.olean` files.

**The early gate, in each step, after `Proof.lean`.** Three conditions, all
of them:

1. `lake build Reflect.Correctness` exits 0. `Correctness` imports `Proof`,
   which imports `Interpreter` and `SemanticsProofs`, and so `Semantics`,
   `Syntax` (and `Text` in step 2); nothing else. `lake` rebuilds every one
   of those whose source or imports changed, so after exit 0 their `.olean`
   files are of the edited sources.
2. `lake env lean InterpGate.lean` exits 0. `kernel/InterpGate.lean` is a new
   file, added by the implementer in step 1 and not edited in step 2. It
   imports `Reflect.Correctness` and nothing else, restates the signatures of
   `reflective`, `reflective_coverage`, `reflective_env` and `tower` exactly
   as `ReflectContract.lean` has them, and prints their axioms:

       import Reflect.Correctness

       open Reflect

       example : ∀ [Ops], ∀ p o,
           Direct [] p o ↔
           Direct [] (.app interp (.lit (reify p))) (.value (.data (reifyOutcome o))) :=
         Reflect.reflective

       example : ∀ [Ops], ∀ p w,
           Direct [] (.app interp (.lit (reify p))) w →
           ∃ o, w = .value (.data (reifyOutcome o)) :=
         Reflect.reflective_coverage

       example : ∀ [Ops], ∀ env p o,
           Direct env p o ↔
           Direct [] (.app (.app evalTerm (.lit (reify p))) (.lit (.arr (reifyEnv env))))
             (.value (.data (reifyOutcome o))) :=
         Reflect.reflective_env

       example : ∀ [Ops], ∀ k p o, Direct [] p o ↔ Direct [] (level k p) (lift k o) :=
         Reflect.tower

       #print axioms Reflect.reflective
       #print axioms Reflect.reflective_coverage
       #print axioms Reflect.reflective_env
       #print axioms Reflect.tower

   The four statements are copied from `ReflectContract.lean` character for
   character. The axioms printed are the ones `ReflectContract.lean` printed
   before the change, and `sorryAx` is not among them. The file does not
   import a table.
3. `git diff --stat <base> -- kernel/Reflect/Interpreter.lean
   kernel/Reflect/Correctness.lean` prints nothing, where `<base>` is the
   commit before step 1. Neither file is edited, in either step.

This gate reads only modules that condition 1 has just rebuilt, so the
untouched machine, channel, node and store files cannot fail it and their old
`.olean` files cannot pass it.

**The contract gate, in each step, after every module is updated.**
`ReflectContract.lean` is checked unedited, with the five other unedited
contract files, once its whole import closure compiles (`ChannelContract.lean`
is checked with them, with `held_nodup` added):

1. `lake build` exits 0. It builds `Reflect`, `Wire` and `Surface`, so every
   module `Reflect.lean` imports is rebuilt from its edited source.
2. `git diff --stat <base> -- kernel/ReflectContract.lean` prints nothing,
   and likewise for `MachineContract.lean`, `StoreContract.lean`,
   `RequestContract.lean`, `LogContract.lean` and `NodeContract.lean`.
3. `lake env lean ReflectContract.lean` exits 0, and so for each of the
   others. `host/check.sh` runs `lake build` and then these, in that order.

**No stale `.olean`.** `lake env lean F.lean` reads whatever `.olean` files
are in `.lake/build`; it builds nothing. A `lake build` that fails leaves the
old files of the modules it did not reach. So each gate runs its `lake build`
first, in the same shell, and goes on only at exit 0:

    cd kernel && lake build Reflect.Correctness && lake env lean InterpGate.lean
    cd kernel && lake build && lake env lean ReflectContract.lean

A gate whose build did not exit 0 has not been run. When in doubt, remove
`.lake/build` and build again; the result must be the same.

The contract gate shows that no statement changed. It does not show that the
definitions the statements mention mean what they did: `Data`, `Direct` and
`step` do change, by the rules of this design. So the unchanged terms
(`interp`, `evalTerm`, by condition 3 of the early gate) and the unchanged
signatures are two checks, and after both steps the definitions the
contracts mention and the axioms each contract prints are read against the
ones before the change (a task under Close).

## 5. Risks, and when to stop

- **A rule `interp` does not mirror.** The table says there is none. If the
  early gate of section 4 cannot be made to pass in step 1 without editing
  `Interpreter.lean` or `Correctness.lean`, stop: the principle in section 1 is wrong somewhere and
  the change goes back to design.
- **A contract file needs an edit.** Other than the added `held_nodup`, a
  changed statement means something moved that the proposal says did not.
  Stop and say which.
- **A gate passes on old files.** See "No stale `.olean`" in section 4. A
  gate is the build and the check together.
- **`held_nodup` runs long.** Past about 100 lines, drop the theorem, keep
  `gain`, test it in `check.sh`, and change the channels delta to say tested.
  That is a smaller change than the one proposed, not this one done. The
  channels delta now says `Network.held_nodup` SHALL hold and names a
  scenario in `ChannelContract.lean`. If the fallback is used, the
  requirement, that scenario and the `ChannelContract.lean` task are revised
  and stamped again before the change is said to be complete.
- **The other session.** `unikernel/` links the same Lean objects. Its
  sources are not touched here. Tell it when step 1 lands, since its Linux
  comparison is built from them.
- **Old kept states.** Not migrated; see the proposal and section 6
  item 10. An old root is not refused and not converted.

## 6. Open questions, as decided

Decided by the conductor on 2026-11-14 under the owner's instruction to carry
beads `homoiconic-q59.35` and `homoiconic-q59.36` through. The owner may
overrule any of them; a reviewer should say where one is wrong.

1. Text is a `List Char`, not a `String`. D4 was rewritten to it.
2. A name is seen as its number.
3. A start hands over names found in its start data only.
4. The printable-array rule of `--text` is deleted.
5. A name is CBOR tag 39.
6. Text is not normalised.
7. `[2, 0]` with a plain number is a request to the outside.
8. No `kind` operation in this change.
9. `Network.held_nodup` is proved, with the fallback in section 5. Using
   the fallback means revising the requirement before claiming completion.
10. Old kept states are not migrated. Nothing rejects an old root and
    nothing converts it. A node kept before this change is still pieces that
    read: numbers and arrays. But a number in it that was a channel name is
    now a plain number, so a process continued from it that sends or
    receives on that number is making a request to the outside. Its held
    list still reads, since held names are kept as numbers. The fixtures are
    made again; a kept node anyone depends on is run again from its program.

## 7. Found while building step 1 (2026-11-17)

- The text D6 first gave for `examples/guess.hom` did not read (D6 now shows the landed text, at fold): a splice cannot be
  under a binder of its quotation. The example quotes the body alone and builds
  the function's code as data, `[1, body]`. The run is the one D6 describes:
  the second process waits on `[2, #0]` and holds nothing.
- A log file is text and no text reads as a name, so `LogCheck.lean` checks a
  name in a log through the proved fold, not through the session.
- `Surface/Check.lean` was edited in step 1, not step 2, so the new
  expectations run.

### Found while building step 2 (2026-11-17)

- `stuck_core` did not need splitting: `Proof.lean` builds in about 24 s with
  the limit of 4000000 unchanged.
- `Machine.step` and the lazy machine needed fewer lines than the wildcard list
  suggests. `succ` of a text and a text under `checkNat` fall to the `_ :: _`
  lines, which are `wrong`, the right answer; so only `.cons` (one line) and
  `.dcase` (two) gain cases, and `lCons` and `lCase` likewise.
- `cons_top` uses a new lemma `rv_list_mk` for the array of code points, not
  `rv_data_mk`; its `hshape` gains text as D9 says.
- `Data.mentions` in `Channel.lean` gains the line D6 already shows for text.
- `Text.ofCodes?` is `List.mapM` over `Nat.isValidChar` and `Char.ofNatAux`,
  and `Text.codes` is `List.map Char.toNat`: both run in a loop, not on the
  call stack.
- `Wire.notData` now names all four kinds of data, and the line of
  `host/check.sh` that expects it follows.
- `String.fromUTF8?` in Lean 4.35.0 refuses overlong forms, surrogates and
  numbers past U+10FFFF; `WireCheck.lean` has each.
- `host/check.sh` lists the modules compiled into the host, so it gains
  `Reflect/Text`. `unikernel/build.sh` finds its modules by `lean --deps` and
  needs no edit; it was not run here.
- `host/run.zig`: the comment on `--text` is the only edit.
- Array patterns on a text follow from their reading as nested `case`: an arm
  of a fixed length takes a text of that many characters and names its code
  points; an arm of a least length names the code points it lists and the
  rest, a text, the empty text when there is no more.
- `Bench.lean` holds the two walks of the measurement task; the numbers are in
  `tasks.md`.
- `ReflectRun.lean` takes about 105 s to check where it took about 55 s.

