# Tasks

- [ ] Owner: the user. Beads `homoiconic-q59.35`, `homoiconic-q59.36`. The open questions at the end of the proposal's review are answered before step 1.
- Advise 2026-11-14 by gpt-6.1-sol (`reviews/2026-11-14-advise.md`): send-back, three required fixes, answered in the documents. A second read is owed before implementation.
- [x] Second read 2026-11-14 by gpt-6.1-sol: the three fixes are answered; send-back, one required fix (the size `cut` compares for a text is the whole byte form), answered in design D4 and D7 and the text check task. Review in `reviews/2026-11-14-advise-2.md`.

## Step 1: names

- [ ] `kernel/Reflect/Syntax.lean`: `Data.name : Nat → Data`. `lake build Reflect.Syntax` passes; `unreify_reify` is unedited.
- [ ] `kernel/Reflect/Semantics.lean`: `succName`, `consTailName`, `caseNameZero`, `caseNameSucc`, `primNameArgError`, `primNameArgClosure`, `primNameData`; the same branches in `evalFuel`.
- [ ] `kernel/Reflect/SemanticsProofs.lean`: a case per rule in each of the four theorems.
- [ ] `kernel/Reflect/Proof.lean`: `walk` and `sdesc` alternatives, placed before `succNat` and `primData`; `stuck_case_name_zero`, `stuck_case_name_succ`; cases in `fwd` and `stuck_core`. `Interpreter.lean` and `Correctness.lean` are not edited.
- [ ] `kernel/InterpGate.lean`, new: imports `Reflect.Correctness` and nothing else; the signatures of `reflective`, `reflective_coverage`, `reflective_env` and `tower` copied exactly from `ReflectContract.lean`; `#print axioms` for each (design section 4).
- [ ] Early gate, all three: `cd kernel && lake build Reflect.Correctness && lake env lean InterpGate.lean` exits 0, the build first and in the same command so no old `.olean` is read; the axioms printed are those `ReflectContract.lean` printed before the change; `git diff --stat <base> -- kernel/Reflect/Interpreter.lean kernel/Reflect/Correctness.lean` prints nothing. If it cannot be made to pass, stop. `ReflectContract.lean` is not checked here: it imports `Reflect`, whose machine, channel, node and store modules do not compile yet.
- [ ] `kernel/Reflect/Machine.lean`: `step` for `.succ`, `.dcase`, `.checkNat`, `.prim` on a name, each before its wildcard. `MachineProof.lean`: cases in `fwd` and `rev`.
- [ ] `kernel/Reflect/Store.lean`: `P.name`; `Data.toP`, `P.toData`, `P.hyd`, `Unf`, `UnfD`; `lSucc`, `lCons`, `lCase`, `lCheckNat`, `lPrim`. `StoreProof.lean` follows.
- [ ] `kernel/Reflect/Log.lean`: `Data.decEq` for `name`.
- [ ] `kernel/Reflect/Channel.lean`: `mentions`, `classify`, `gain`; `.name n` in `Step.fresh` and `stepRun`; `gain` in `Step.comm` and `stepRun`. `Node.lean`: the same in `plan`.
- [ ] `kernel/Reflect/ChannelProof.lean`, `NodeProof.lean`: follow; add `Network.held_nodup`. `ChannelContract.lean` gains it with its axioms. If the fallback of design section 5 is used instead, revise the channels requirement, its scenario and this task, and stamp again, before the change is said to be complete.
- [ ] Contract gate, run once the `Wire` and `Surface` tasks of this step below are also done (the default `lake build` builds them too), after every module `Reflect.lean` imports is updated: `cd kernel && lake build` exits 0; then `lake env lean` on `ReflectContract.lean`, `MachineContract.lean`, `StoreContract.lean`, `RequestContract.lean`, `LogContract.lean` and `NodeContract.lean` each exits 0, and `git diff --stat <base>` shows none of the six. The build comes first and must exit 0, so every `.olean` read is of the edited sources.
- [ ] `kernel/ReflectRun.lean`, a regression for each of the seven name rules, each directly, through `interp` at levels 1 and 2, on the machine whole and in three slices, and on the lazy machine (`StoreCheck.lean`): `succ #3` is 4; `cons 1 #3` is wrong; `case #0` takes the zero branch; `case #3` takes the successor branch with the plain number 2 bound; `prim #0 x` with `x` an unbound variable is that `unbound`; `prim #0 x` with `x` a function is wrong; `prim #0 [2, 3]` is 5. In the two `prim` cases with a bad argument both machines halt `unbound` and `wrong`: neither falls through the last line of `.prim` to `fault`. Also `prim 0 [#3, 0]` is `[]` and `prim 0 [3, 0]` is 3 (design D5).
- [ ] `kernel/Wire/Cbor.lean`: `Item.name`; tag 39 written and read over a number in the number's form; every other tag but 2 refused. `Wire/Piece.lean`: the name piece.
- [ ] `kernel/WireCheck.lean`: `#3` is `d8 27 03`; a name of 2^64; tag 39 over an array, a text, a byte string, a long-form number are refused; tag 39 over tag 39 (`d8 27 d8 27 03`), tag 39 in a long-form head (`d9 00 27 03`) and tag 39 over tag 2 of a number below 2^64 are refused; every string of one or two bytes still has one reading. `KeepCheck.lean`: a waiting process that holds a name value is saved and continued.
- [ ] `kernel/Surface/Render.lean`: a name renders `#n`. `Chan.lean`, `Keep.lean`: held names print as names; the piece reader in `Keep.lean` takes a name leaf.
- [ ] `examples/guess.hom` rewritten (design D6); `examples/number.hom` added with `examples/number.schedule`.
- [ ] `kernel/Surface/Expect.lean`, `NodeCheck.lean`, `host/check.sh`: expectations for ping, race, guess, number, sieve. Sieve: no process holds a name twice, and no process after process 2 holds `#0`.
- [ ] Holding regressions, in `Surface/Expect.lean` or `host/check.sh`: a name inside quoted code that is in the start data, so that the start data holds `[2, #n]`, is handed to the process started; a name nested in arrays in a message (`[[[2, #n]]]`) is handed to the receiver; the same message with the number (`[[[2, n]]]`) hands over nothing; a name spliced only into the program field of a start request is not handed over (guess).
- [ ] `kernel/NodeCheck.lean` and `LogCheck.lean`, a logged node whose log makes a channel (fresh), hands the name to a second process in a message (transfer), delivers an op a second time (duplicate delivery), is saved, and is continued from the saved root (restart): the session and `nodeRun` agree after every prefix; the duplicate changes nothing; the receiver holds the name once; from every saved prefix the rest of the log reaches the same root; the saved pieces hold the name value under tag 39 and the held lists as plain numbers.
- [ ] `sh host/check.sh` exits 0. Commit.

## Step 2: text

- [ ] `kernel/Reflect/Text.lean`: `Text.uncons? : List Char → Option (Nat × List Char)`, `Text.codes : List Char → List Nat`, `Text.ofCodes? : List Nat → Option (List Char)`. `Syntax.lean`: `Data.text : List Char → Data`. No `String` in either.
- [ ] `kernel/Reflect/Semantics.lean`: `succText`, `consText`, `caseTextNil` on `.text []`, `caseTextCons` on `.text (c :: r)`, `primCodeText`; `evalFuel`.
- [ ] `SemanticsProofs.lean`, `Proof.lean` (`walk` with `consText` before `consArr`; `stuck_case_text_nil`, `stuck_case_text_cons`).
- [ ] Early gate, as in step 1, with `InterpGate.lean` unedited: `cd kernel && lake build Reflect.Correctness && lake env lean InterpGate.lean` exits 0 with the same axioms; `git diff --stat <base>` shows neither `Interpreter.lean` nor `Correctness.lean`, `<base>` being the commit before step 1. If it cannot be made to pass, stop.
- [ ] `Machine.lean`, `MachineProof.lean`; `Store.lean` (`P.text : List Char → P R`), `StoreProof.lean`; `Log.lean` (`decEq` for `text`).
- [ ] Contract gate, run once the `Wire` and `Surface` tasks of this step below are also done (the default `lake build` builds them too), as in step 1, after every module `Reflect.lean` imports is updated: `cd kernel && lake build` exits 0, then the six contract files check unedited.
- [ ] `kernel/Reflect/Arith.lean`: operations 7 and 8; `arithNames` with arity.
- [ ] `kernel/ReflectRun.lean`: `case` on `""` and on `"hé"`; `cons 1 "a"` is `[1, 97]`; `succ "a"` is wrong; `equal "a" [97]` is 0; `equal "" []` is 0; `text` and `codes` both ways and on bad input; `codes` agrees with a `case` walk; each also through `interp` at levels 1 and 2 and on the machine in three slices.
- [ ] `kernel/Wire/Cbor.lean`: `Item.text`; major type 3 written (`String.ofList`, `String.toUTF8`, the length in bytes) and read (`String.fromUTF8?`, `String.toList`); invalid UTF-8 refused. `Wire/Piece.lean`: the text piece; `cut` keeps or stores a text whole.
- [ ] `kernel/WireCheck.lean`: the RFC 8949 appendix A text strings (`""`, `"a"`, `"IETF"`, `"\"\\"`, `"ü"`, `"水"`, `"𐅑"`); `61 ff`, `62 c0 80`, `63 ed a0 80` and an indefinite text `7f` are refused; a program with a string literal round-trips. `KeepCheck.lean`, `StoreCheck.lean`: a text of 24 ASCII characters saved with cuts at 25 bytes is stored (its byte form is 26 bytes), and with cuts at 26 it is kept in place; a text longer than 256 bytes is one stored piece; the lazy machine takes it apart; with that piece withheld the run pauses on its reference.
- [ ] `kernel/Surface/Read.lean`: `Tk.str` carries the `List Char`; a literal is `lit (text …)`; `text`, `codes` built in. `Render.lean`: text in quotes with escapes; `textOf` deleted; `--text` writes a text raw.
- [ ] `examples/calc.hom`, `examples/words.hom`: the result goes through `text`.
- [ ] `kernel/Surface/Expect.lean`, `Check.lean`, `host/check.sh`: `"h\\i\n"` prints `"h\\i\n"`; rendered text reads back; `--text` on text, on an array, on a function; calc and words, plain and through `--interp`; `sameThroughInterp` still holds for every example.
- [ ] Measure a `case` walk and a `codes` walk over 100,000 characters; write both in `docs/LEARNINGS.md`.
- [ ] `sh host/check.sh` exits 0. Commit.

## Close

- [ ] `sh host/check.sh` exits 0.
- [ ] Audit, apart from the gates: read `Data`, `Direct`, `step` and the other definitions the contract files mention against the ones before the change, and the axioms each contract prints against the ones it printed before. Unchanged signatures do not show unchanged meaning.
- [ ] Advise by a reader from another model family. Asked in particular: the table in design section 2 against `Interpreter.lean`; that no contract file but `ChannelContract.lean` changed; the wildcard list.
- [ ] Fold. Stamp the MODIFIED bases; apply the deltas; edit the "What is built" paragraphs of `code-as-data`, `channels`, `wire-bytes`, `state-store`, `surface-syntax`; amend `ARCHITECTURE.md` (Reflect, Channels, Stored state, Byte form, Surface, Downstream changes) and `docs/PROOFS.md`; append `docs/LEARNINGS.md`; close both beads.
