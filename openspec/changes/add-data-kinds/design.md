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

### D4. Text is a Lean `String`, behind three functions

New file `kernel/Reflect/Text.lean`, imported by `Syntax.lean`:

    def Text.uncons? : String → Option (Nat × String)   -- first code point, rest
    def Text.codes   : String → List Nat
    def Text.ofCodes? : List Nat → Option String        -- none if an item is not
                                                        -- a Unicode scalar value

`Data.text : String → Data`. The two case rules carry a premise:

    caseTextNil  (hs : Direct env s (.value (.data (.text t))))
                 (hu : Text.uncons? t = none) (h : Direct env n o)
    caseTextCons (hs : … (.text t)) (hu : Text.uncons? t = some (c, r))
                 (h : Direct (.data (.text r) :: .data (.nat c) :: env) cb o)
    consText     (ha : … (.data x)) (hb : … (.data (.text t))) :
                 Direct env (.cons a b) (.value (.data (.arr (x :: (Text.codes t).map .nat))))

No proof unfolds the three functions. Nothing is proved about `String`; that
`codes` and `uncons?` agree is tested in `ReflectRun.lean`.

Cost: with `String`, `uncons?` copies the rest (`String.drop` gives a slice in
Lean 4.35 and must be copied to keep one form per text). A walk by `case` is
quadratic in the length. `codes` is linear, and a program that reads long text
should use it.

- Rejected: `List Char`. The rules become plain patterns and a step is
  constant time, but a character stays a list cell in memory, which the bead
  names. It is the fallback: only `Text.lean`, `Data`'s constructor and the
  reader and writer change, and no proof.
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
functions of one argument. No operation makes a name, and none tells a name
from a number except equality.

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

`examples/guess.hom` becomes:

    ask [0] (fn ch ->
      let guesser = quote (fn nothing -> ask [2, ~[2, ch]] (fn x -> x))
      ask [3, guesser, []] (fn started ->
        ask [1, ch, 7] (fn sent -> [])))

`~[2, ch]` is the code of a literal of the name. Process 1 waits on `[2, #0]`
and holds `[]`. `examples/number.hom` is the old text: process 1 asks `[2, 0]`
with a number, which is the outside's. In both, `[2, 0, 1]` is refused.

### D7. Bytes

- Text: major type 3, definite length in the shortest form, then UTF-8. The
  reader refuses bytes that are not valid UTF-8 (`String.fromUTF8?`). Not
  normalised; dCBOR asks for NFC and this project does not do it, as with
  tag 2 for large numbers.
- Name: tag 39 over the number in the number's own form (an unsigned integer,
  or tag 2 at 2^64 and above). `#3` is `d8 27 03`. Tag 39 is registered at
  IANA as "Identifier" (checked 2026-11-14), which is the meaning here. The
  registry has no private range; 6 to 15 are unassigned but in the Standards
  Action range, where a private use may later collide. The reader refuses
  tag 39 over anything but a number, and every tag but 2 and 39.
- No collision with a reference. A reference is a bare byte string (major
  type 2) of 32 bytes. Text is major type 3. A name and a large number are
  tags (major type 6); the byte string inside tag 2 is read by the tag's own
  branch and is never an item. Reading data still refuses a bare byte string.
- `Wire.Item` gains `text` and `name`. `Item.toData` is `none` only for
  `bytes`.
- Pieces. `Reflect.P` gains two leaves, `text : String → P R` and
  `name : Nat → P R`. `Data.toP`, `P.toData`, `P.hyd`, `Unf` and `UnfD` gain
  a line each. `Wire.pieceItem` writes a text piece as the text and a name
  piece as the tagged number; `itemPiece` reads them back. Neither is an
  array, so neither can be taken for a pair `[0, h, t]` or a function
  `[1, body, captured]`.
- The lazy machine takes text apart with no fetch, since a text is a leaf.
  `lCase` on `.text t` uses `Text.uncons?`. `lCons` with `.text t` under the
  head builds the list of code points. `lSucc` and `lCheckNat` pass `.name n`
  as the plain machine does; `lPrim` takes `.name n` as the operation number.
- Saving does not cut text. `cut` treats a text as it treats a number:
  stored whole under its hash when its bytes pass the size, kept in place
  otherwise. A long text is one piece and is fetched whole.

### D8. Surface

- `"..."` reads as `lit (text …)`; `Tk.str` carries a `String`. `'c'` stays
  the number of one ASCII character: the head `case` gives is a number, and
  `equal c ' '` has to hold of it.
- `renderData`: a text in double quotes with `\n`, `\t`, `\\` and `\"`
  written as escapes and every other character as itself. The reader takes
  every byte but a line feed and a backslash inside quotes, so rendered text
  reads back. A name is `#` and its number, which does not read.
- `--text` (bit 1 of `flags`): a result that is a text is written raw. Every
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
| `Reflect/Text.lean` | new | D4. |
| `Reflect/Semantics.lean` | 32 | Twelve rules; `evalFuel` gains their branches. `reifyValue`, `reifyOutcome` unchanged. |
| `Reflect/SemanticsProofs.lean` | 0 | A case per rule in `direct_deterministic`, `evalFuel_sound`, `evalFuel_mono`, `evalFuel_complete`. |
| `Reflect/Interpreter.lean` | 3 | Nothing. |
| `Reflect/Proof.lean` | 19 | `walk` and `sdesc` gain alternatives; `stuck_case_*` gain four lemmas; `fwd` and `stuck_core` gain cases. |
| `Reflect/Correctness.lean` | 1 | Nothing. |
| `Reflect/Machine.lean` | 14 | `step` gains cases (see the wildcard list). `Code`, `comp`, `decomp` unchanged. |
| `Reflect/MachineProof.lean` | 17 | A case per rule in `fwd`; sub-cases in `rev`. |
| `Reflect/Store.lean` | 15 | D7. |
| `Reflect/StoreProof.lean` | 32 | D7; see proofs below. |
| `Reflect/Arith.lean` | 8 | D5. |
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
| `ReflectContract.lean`, `MachineContract.lean`, `StoreContract.lean`, `RequestContract.lean`, `LogContract.lean`, `NodeContract.lean` | — | Not edited. They must still check: that is the acceptance test for "no statement changed". |
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

Three rules need no row. `lit` hands `d` over without looking, so a literal
that is text or a name is `[0, [1, d]]`. `appData` looks only at the value's
tag. `primData` passes any data to the table.

`interp` applied to data that is no program's form is outside the theorem, as
before. There a name is read as a variable index and a text as a list.
`unreify` refuses both.

## 3. Proofs

Mechanical: a new case that copies a neighbour.

- `direct_deterministic`: twelve cases in the form the others have. For the
  two text case rules the clash is two equations about `Text.uncons? t`;
  `simp_all` closes it.
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
  rules with `(Direct.varBound rfl)`, the text ones also with
  `(by assumption)` for the premise. Getting this order wrong shows as `fwd`
  failing in a case that passed before.
- **`stuck_core` runs at `maxHeartbeats 4000000` today.** It gains about a
  third more cases. If it times out, split it by construct into lemmas; do
  not raise the limit past 8000000.
- **A premise that is not a pattern.** `caseTextNil` and `caseTextCons` are
  the first rules with a side equation. `evalFuel` matches on
  `Text.uncons? t`; in `stuck_core` and `MachineProof.rev` that means
  `cases hu : Text.uncons? t` and `simp only [hu]` where the other cases
  reduce by themselves.
- **`StoreProof.cons_top`.** Its `hshape` lists the shapes the second entry
  can have; it gains name and text. Its inner `cases p'` gains the text
  tail, where the result is `.cons y (listToP (codes t))` and the proof needs
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
`ReflectContract.lean` checking unchanged is the first gate, before any other
file is touched. If `interp` needs an edit, it shows here.

**Step 2, text.** `Text.lean`; `Data.text`; the five text rules; the same
files in the same order; `Arith` 7 and 8; `Wire` major type 3 and the text
piece; the reader, the renderer, `--text`; `calc.hom`, `words.hom`;
`check.sh`.

Names first because the bug is P1, the step needs nothing from `String`, and
it is the smaller. Each proof file is opened twice; that is the price of a
green tree in between.

## 5. Risks, and when to stop

- **A rule `interp` does not mirror.** The table says there is none. If
  `ReflectContract.lean` cannot be made to check in step 1 without editing
  `Interpreter.lean`, stop: the principle in section 1 is wrong somewhere and
  the change goes back to design.
- **A contract file needs an edit.** Other than the added `held_nodup`, a
  changed statement means something moved that the proposal says did not.
  Stop and say which.
- **`String` friction.** If `Text.lean` or the two premised rules cost more
  than a day, switch `Data.text` to `List Char` behind the same three
  functions and record it. No statement changes.
- **Quadratic `case` on text.** After step 2, measure a `case` walk and a
  `codes` walk over a text of 100,000 characters and put both numbers in
  `docs/LEARNINGS.md`. If the `case` walk is unusable at the sizes
  `examples/` need, take open question 1 back to the owner.
- **`held_nodup` runs long.** Past about 100 lines, drop the theorem, keep
  `gain`, test it in `check.sh`, and change the channels delta to say tested.
- **The other session.** `unikernel/` links the same Lean objects. Its
  sources are not touched here. Tell it when step 1 lands, since its Linux
  comparison is built from them.
- **Old kept states.** Not read as before; see the proposal.

## 6. Open questions, as decided

Decided by the conductor on 2026-11-14 under the owner's instruction to carry
beads `homoiconic-q59.35` and `homoiconic-q59.36` through. The owner may
overrule any of them; a reviewer should say where one is wrong.

1. **Text is a `List Char`, not a `String`.** This amends D4. A walk by `case`
   is then linear, the two text case rules are plain patterns with no side
   equation, and the risks "`String` friction" and "quadratic `case` on text"
   in section 5 fall away. A list cell per character stays in memory, as it is
   today; the owner decided on 2026-11-12 that representation is optimised
   later. `Text.lean` keeps the three functions so the representation can
   still be swapped. The byte form is unchanged: UTF-8.
2. A name is seen as its number.
3. A start hands over names found in its start data only.
4. The printable-array rule of `--text` is deleted.
5. A name is CBOR tag 39.
6. Text is not normalised.
7. `[2, 0]` with a plain number is a request to the outside.
8. No `kind` operation in this change.
9. `Network.held_nodup` is proved, with the fallback in section 5.
10. Old kept states are not migrated.
