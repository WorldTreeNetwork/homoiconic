# Tasks

- [ ] Owner: the user. Beads `homoiconic-q59.35`, `homoiconic-q59.36`. The open questions at the end of the proposal's review are answered before step 1.

## Step 1: names

- [ ] `kernel/Reflect/Syntax.lean`: `Data.name : Nat → Data`. `lake build Reflect.Syntax` passes; `unreify_reify` is unedited.
- [ ] `kernel/Reflect/Semantics.lean`: `succName`, `consTailName`, `caseNameZero`, `caseNameSucc`, `primNameArgError`, `primNameArgClosure`, `primNameData`; the same branches in `evalFuel`.
- [ ] `kernel/Reflect/SemanticsProofs.lean`: a case per rule in each of the four theorems.
- [ ] `kernel/Reflect/Proof.lean`: `walk` and `sdesc` alternatives, placed before `succNat` and `primData`; `stuck_case_name_zero`, `stuck_case_name_succ`; cases in `fwd` and `stuck_core`. `Interpreter.lean` and `Correctness.lean` are not edited.
- [ ] Gate: `lake env lean ReflectContract.lean` exits 0 with the file unedited. If it cannot, stop.
- [ ] `kernel/Reflect/Machine.lean`: `step` for `.succ`, `.dcase`, `.checkNat`, `.prim` on a name, each before its wildcard. `MachineProof.lean`: cases in `fwd` and `rev`. `MachineContract.lean` checks unedited.
- [ ] `kernel/Reflect/Store.lean`: `P.name`; `Data.toP`, `P.toData`, `P.hyd`, `Unf`, `UnfD`; `lSucc`, `lCons`, `lCase`, `lCheckNat`, `lPrim`. `StoreProof.lean` follows. `StoreContract.lean` checks unedited.
- [ ] `kernel/Reflect/Log.lean`: `Data.decEq` for `name`. `LogContract.lean` checks unedited.
- [ ] `kernel/Reflect/Channel.lean`: `mentions`, `classify`, `gain`; `.name n` in `Step.fresh` and `stepRun`; `gain` in `Step.comm` and `stepRun`. `Node.lean`: the same in `plan`.
- [ ] `kernel/Reflect/ChannelProof.lean`, `NodeProof.lean`: follow; add `Network.held_nodup`. `ChannelContract.lean` gains it with its axioms; `NodeContract.lean` checks unedited.
- [ ] `kernel/Wire/Cbor.lean`: `Item.name`; tag 39 written and read over a number in the number's form; every other tag but 2 refused. `Wire/Piece.lean`: the name piece.
- [ ] `kernel/WireCheck.lean`: `#3` is `d8 27 03`; a name of 2^64; tag 39 over an array, a text, a byte string, a long-form number are refused; every string of one or two bytes still has one reading. `KeepCheck.lean`: a waiting process that holds a name value is saved and continued.
- [ ] `kernel/Surface/Render.lean`: a name renders `#n`. `Chan.lean`, `Keep.lean`: held names print as names; the piece reader in `Keep.lean` takes a name leaf.
- [ ] `examples/guess.hom` rewritten (design D6); `examples/number.hom` added with `examples/number.schedule`.
- [ ] `kernel/Surface/Expect.lean`, `NodeCheck.lean`, `host/check.sh`: expectations for ping, race, guess, number, sieve. Sieve: no process holds a name twice, and no process after process 2 holds `#0`.
- [ ] `sh host/check.sh` exits 0. Commit.

## Step 2: text

- [ ] `kernel/Reflect/Text.lean`: `Text.uncons?`, `Text.codes`, `Text.ofCodes?`. `Syntax.lean`: `Data.text : String → Data`.
- [ ] `kernel/Reflect/Semantics.lean`: `succText`, `consText`, `caseTextNil`, `caseTextCons`, `primCodeText`; `evalFuel`.
- [ ] `SemanticsProofs.lean`, `Proof.lean` (`walk` with `consText` before `consArr`; `stuck_case_text_nil`, `stuck_case_text_cons`). Gate: `ReflectContract.lean` checks unedited.
- [ ] `Machine.lean`, `MachineProof.lean`; `Store.lean` (`P.text`), `StoreProof.lean`; `Log.lean` (`decEq` for `text`). Contracts check unedited.
- [ ] `kernel/Reflect/Arith.lean`: operations 7 and 8; `arithNames` with arity.
- [ ] `kernel/ReflectRun.lean`: `case` on `""` and on `"hé"`; `cons 1 "a"` is `[1, 97]`; `succ "a"` is wrong; `equal "a" [97]` is 0; `equal "" []` is 0; `text` and `codes` both ways and on bad input; `codes` agrees with a `case` walk; each also through `interp` at levels 1 and 2 and on the machine in three slices.
- [ ] `kernel/Wire/Cbor.lean`: `Item.text`; major type 3 written and read; invalid UTF-8 refused. `Wire/Piece.lean`: the text piece; `cut` keeps or stores a text whole.
- [ ] `kernel/WireCheck.lean`: the RFC 8949 appendix A text strings (`""`, `"a"`, `"IETF"`, `"\"\\"`, `"ü"`, `"水"`, `"𐅑"`); `61 ff`, `62 c0 80`, `63 ed a0 80` and an indefinite text `7f` are refused; a program with a string literal round-trips. `KeepCheck.lean`, `StoreCheck.lean`: a text longer than 256 bytes is one stored piece; the lazy machine takes it apart; with that piece withheld the run pauses on its reference.
- [ ] `kernel/Surface/Read.lean`: `Tk.str` carries the text; a literal is `lit (text …)`; `text`, `codes` built in. `Render.lean`: text in quotes with escapes; `textOf` deleted; `--text` writes a text raw.
- [ ] `examples/calc.hom`, `examples/words.hom`: the result goes through `text`.
- [ ] `kernel/Surface/Expect.lean`, `Check.lean`, `host/check.sh`: `"h\\i\n"` prints `"h\\i\n"`; rendered text reads back; `--text` on text, on an array, on a function; calc and words, plain and through `--interp`; `sameThroughInterp` still holds for every example.
- [ ] Measure a `case` walk and a `codes` walk over 100,000 characters; write both in `docs/LEARNINGS.md`.
- [ ] `sh host/check.sh` exits 0. Commit.

## Close

- [ ] `sh host/check.sh` exits 0.
- [ ] Advise by a reader from another model family. Asked in particular: the table in design section 2 against `Interpreter.lean`; that no contract file but `ChannelContract.lean` changed; the wildcard list.
- [ ] Fold. Stamp the MODIFIED bases; apply the deltas; edit the "What is built" paragraphs of `code-as-data`, `channels`, `wire-bytes`, `state-store`, `surface-syntax`; amend `ARCHITECTURE.md` (Reflect, Channels, Stored state, Byte form, Surface, Downstream changes) and `docs/PROOFS.md`; append `docs/LEARNINGS.md`; close both beads.
