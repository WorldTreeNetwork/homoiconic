# wire-bytes

What is built: one byte form for data, for the part of dCBOR that `Data` has: numbers, arrays, text and names. Text is a CBOR text string of UTF-8, not normalised; a name is CBOR tag 39 over its number (`openspec/changes/archive/2026-11-17-add-data-kinds/`). A program's bytes are the bytes of its quoted form, and a machine value, a waiting program among them, has a byte form too. The reader and writer are in `kernel/Wire/Cbor.lean`, the byte forms of a program and a machine value in `kernel/Wire/Form.lean`, and the tests in `kernel/WireCheck.lean`, which `host/check.sh` runs. `Wire` is its own library; no definition or theorem in `Reflect` mentions bytes. The reader and writer are tested, not proved, by decision D7 of `add-verifiable-network-vision`. One statement is proved: `Reflect.unreify_reify`. It and `unreify`, which reads a program back from its data form, are in `kernel/Reflect/Syntax.lean`, beside `reify`. Numbers of 2^64 and above are written with CBOR tag 2, and names with tag 39; those are this project's rules, not dCBOR's. A piece of stored state (`openspec/specs/state-store/spec.md`) has a byte form too, and a reference to it is the 32-byte Blake3 hash of those bytes. Blake3 is written in Lean in `kernel/Wire/Blake3.lean`; the byte form of a piece and saving by cutting are in `kernel/Wire/Piece.lean`. The reader and writer also handle byte strings, for references; reading data refuses one. A text or a name is a piece of its own kind, and saving stores a text whole, never cut. `kernel/KeepCheck.lean`, which `host/check.sh` runs, tests the hash against the official vectors and saves real runs. The hash, the byte form of a piece and saving are tested, not proved. That two different pieces do not share a hash is assumed (D5).

## Purpose

State the byte form of a data value, of a program, of a machine value and of a piece of stored state, how a reference is made, how a value is cut for saving, what the reader refuses, and what is proved and what is tested about them. It also states the byte form of a bounded run's reply (`kernel/Wire/Reply.lean`, tested by `kernel/WireReplyCheck.lean`), which the network image sends. This spec does not cover the event log, signatures or network framing; the frame is in `openspec/specs/unikernel-net/spec.md`. The host commands that use the byte form are in `openspec/specs/zig-host/spec.md`.

## Requirements

### Requirement: A data value has one byte form

The kernel SHALL provide a writer from data to bytes, for every data value in which each array has fewer than 2^64 items, each number and the number of each name fewer than 2^64 bytes, and each text fewer than 2^64 bytes of UTF-8, and a reader from bytes to data. A number below 2^64 SHALL be written as a CBOR unsigned integer in the shortest form that holds it. A number of 2^64 or more SHALL be written as CBOR tag 2 over a byte string of its bytes, most significant first, with no leading zero. An array SHALL be written as a definite-length CBOR array with its length in the shortest form. A text SHALL be written as a definite-length CBOR text string, its length in bytes in the shortest form, followed by its UTF-8. A name SHALL be written as CBOR tag 39 over its number in the form a number has: an unsigned integer below 2^64, tag 2 over its bytes from 2^64. A text SHALL hold Unicode scalar values only. Text SHALL NOT be normalised: two different sequences of scalar values are two texts with two byte forms. Tag 2 for large numbers, tag 39 for names and text without normalisation are this project's rules, not dCBOR's. The reader SHALL refuse a number or length in a longer form than it needs, an indefinite length, bytes after the value, a value cut short, a bignum with a leading zero or one that fits an unsigned integer, a text that is not valid UTF-8, tag 39 over anything but a number, tag 39 over tag 39 among them, a tag written in a longer form than it needs, every other tag, and every kind of CBOR value other than these five. The reader and writer are tested, not proved.

#### Scenario: The standard's examples

- GIVEN each example in RFC 8949 appendix A that is an unsigned number, a definite-length text string, or an array of them
- WHEN the value is written
- THEN the bytes are the standard's, and reading them gives the value

#### Scenario: Another spelling is refused

- GIVEN the bytes `18 17`, which spell 23 in two bytes
- WHEN they are read
- THEN the reader refuses them

#### Scenario: Short strings have one reading

- GIVEN every string of one or two bytes
- WHEN each is read
- THEN it is refused, or it is exactly the bytes the writer gives for the value read

#### Scenario: A name

- GIVEN the name with number 3
- WHEN it is written
- THEN the bytes are `d8 27 03`, and reading them gives the name and not the number 3

#### Scenario: Text that is not UTF-8 is refused

- GIVEN the bytes `61 ff`, `62 c0 80` and `63 ed a0 80`
- WHEN each is read
- THEN the reader refuses it

#### Scenario: A tag over the wrong thing is refused

- GIVEN the bytes `d8 27 80`, tag 39 over an empty array; `d8 27 d8 27 03`, tag 39 over tag 39; `d9 00 27 03`, tag 39 in three bytes; and `d8 28 03`, tag 40 over 3
- WHEN each is read
- THEN the reader refuses it

### Requirement: A program's bytes are the bytes of its quoted form

The byte form of a program SHALL be the byte form of the data value `reify` gives it. The kernel SHALL read a program back from that data and SHALL refuse data that is the form of no program. Reading the data form of a program SHALL give that program; this is proved, with Lean's standard axioms only.

#### Scenario: The identity function

- GIVEN the program `fn x -> x`
- WHEN its byte form is written
- THEN it is the three bytes `82 01 00`

#### Scenario: A program run from its bytes

- GIVEN a program written as bytes and read back
- WHEN it is run
- THEN it gives what the program gives

#### Scenario: Data that is no program

- GIVEN the byte `80`, an empty array
- WHEN it is read as a program
- THEN it is refused

### Requirement: A machine value has a byte form

A machine value that is data `d` SHALL have the data form `[0, d]`. A function value SHALL have the data form `[1, body, captured]`, where `body` is the quoted form of the program its code was compiled from and `captured` is the array of the forms of the values it holds. Reading SHALL compile `body`. A function whose code is not exactly the compilation of a program SHALL have no byte form. A value written, read and written again SHALL give the same bytes.

#### Scenario: A waiting run is kept as bytes

- GIVEN a program that has asked twice and been answered once
- WHEN the waiting function is written as bytes, read back, and resumed with the second answer
- THEN it gives the result the uninterrupted run gives

#### Scenario: Code that no program compiles to

- GIVEN a function value whose code is a literal followed by a check that no compilation puts there
- WHEN its byte form is asked for
- THEN there is none

### Requirement: A reference is the Blake3 hash of a piece's bytes

The kernel SHALL define the 32-byte Blake3 hash in Lean. A reference to a stored piece SHALL be the hash of that piece's byte form. The definition is tested against the official test vectors and is not proved. That two different pieces do not share a hash is assumed.

#### Scenario: The official vectors

- GIVEN each official Blake3 test input, from 0 to 102,400 bytes
- WHEN it is hashed
- THEN the result is the first 32 bytes of the published output

### Requirement: A piece has a byte form

The reader and writer SHALL handle a definite-length CBOR byte string, with its length in the shortest form. Reading data SHALL refuse a byte string anywhere in it. A piece SHALL be written as follows: a number as itself; a text as the text; a name as the name; an empty list as an empty array; a pair as `[0, head, tail]`; a function as `[1, body, captured]`, where `body` is the quoted form of the program its code was compiled from; a reference as a byte string of 32 bytes. A function whose code is not exactly the compilation of a program SHALL have no byte form. A byte string of another length SHALL NOT be read as a piece. A text of any length, 32 bytes among them, SHALL NOT be read as a reference, and the byte string inside a large number SHALL NOT be read as one.

#### Scenario: A stored piece reads back

- GIVEN a machine state saved into pieces
- WHEN each piece's bytes are read and written again
- THEN the bytes are the same, and the piece's name is the hash of them

#### Scenario: A text of 32 bytes is not a reference

- GIVEN a piece that is a text of 32 ASCII characters
- WHEN its bytes are written and read as a piece
- THEN the bytes begin `78 20` and the piece read is that text

### Requirement: Saving cuts a value by size

Saving SHALL cut a value from the leaves up, store each part whose byte form is larger than a given size under its hash, and replace it by its reference. It SHALL leave a part that is already a reference as it is. It SHALL store the top of the value whatever its size, and give its reference as the root. A root can therefore name a piece of at most the size, which a turn holds in place (see "A turn holds the piece under a small root in place").

#### Scenario: A run continues from saved pieces

- GIVEN a program stopped after some steps and saved, cut at 256 bytes or at every value
- WHEN the lazy machine continues from the stored pieces
- THEN it halts with what the plain machine halts with

### Requirement: Equal values are saved under one root

What saving leaves and the root it gives SHALL be a function of the value a partial piece stands for, when every reference in the piece is one saving made. `Wire.Made size σ p q` SHALL say so: the partial piece `p` resolves to the whole piece `q` in the store `σ`, and each reference in `p`, and in the pieces `σ` holds under them, is the reference cutting at `size` gives the value it stands for. It SHALL be proved, with no axiom beyond Lean's own, that a piece with no reference in it is `Made` (`Made.whole`); that two pieces `Made` for one value are cut to the same piece and saved under the same root, whatever their stores hold (`cut_function`, `same_root`); that what `cut` leaves is `Made` for the same value in any store that holds the old pieces and the pieces it stored (`cut_made`); that a step of the lazy machine, on any part of the store, keeps every reference one that saving made (`lstep_good`); and that the root resolves to the value in such a store (`save_resolves`). The hash SHALL be used as the function it is: these statements assume nothing of it, and do not say that different values have different roots. The proofs are in `kernel/Wire/PieceProof.lean` and the exact statements in `kernel/RootContract.lean`, which `host/check.sh` runs.

Three things are not proved. A store that holds two different pieces under one hash does not exist, so `cut_made`, `save_resolves` and `save_opened` say nothing when two stored pieces collide. That a piece read from its bytes is the piece that was written is tested (`kernel/KeepCheck.lean`). And the session of a VM and of a node is tested: `Surface.Keep.full` and `parts` are `partial`, so Lean proves nothing of them, and `openState` and `openNode` are not covered. The session of one turn of a program is proved to hold and save only references that saving made; see the next requirement.

A root is not always a reference saving would make inside a value: the top is stored whatever its size, and a part of at most `size` bytes is otherwise left in place. So the statement does not hold of a piece that holds the root of a small piece. Until 2026-11-23 `Surface.Keep.answer` started a turn from the root itself, and a waiting program that keeps hold of the function it was resumed from was then saved under another root than the same value held whole (`homoiconic-q59.47`: `fn f -> f 5 (fn x -> ask 7 (fn y -> f))`, whose first turn waits with a function of 36 bytes, answered with 0, was saved under `af0852f8…` and held whole under `c53dc525…`). A turn no longer does that; see the next requirement. A VM and a node are opened through the pieces under the root, so the root does not enter their state; that is read off `openState` and `openNode` and borne out by `kernel/LogCheck.lean` and `kernel/NodeCheck.lean`, not proved.

#### Scenario: The statements are checked

- GIVEN `kernel/RootContract.lean`
- WHEN it is checked
- THEN every statement holds as written and each depends on no axiom but `propext`, `Classical.choice` and `Quot.sound`

### Requirement: A turn holds the piece under a small root in place

A turn that answers the waiting program under a root SHALL fetch the piece under the root before it runs, and SHALL hold that piece in place when its byte form is at most the size saving cuts at, and hold the root as a reference when it is larger (`Wire.opened`, `Surface.Keep.answer`). That is what saving would have left of the value inside a larger one, so the root of a small piece does not enter the state the turn saves. Saving itself SHALL NOT change: it stores the top of a value whatever its size, and the root of a value is the root it had before. A state that an earlier build saved with the root of a small piece inside it SHALL still read and run; it is not rewritten, and its root stays the one it was saved under.

It SHALL be proved, with no axiom beyond Lean's own, that the piece a turn starts from is `Made` for the value saved, in any store that holds the old pieces and the pieces saving stored (`Wire.save_opened`); that following references through a part of the store gives a reference saving made (`Surface.Keep.chase_good`, for which `chase` takes a bound, the number of pieces the session holds and one more, and is no longer `partial`); and that a session of one turn, begun by `start` or `answer` and carried on by `give`, holds only references saving made in every phase, and at its end has saved a function every reference of which saving made, or has stored nothing (`Inv`, `Turn`, `advance_turn`, `start_turn`, `answer_turn`, `give_turn`). Such a function resolves to a whole value and is saved under the root that value is saved under (`waits_root`). The proofs are in `kernel/Wire/PieceProof.lean` and `kernel/Surface/KeepProof.lean`, and the exact statements in `kernel/RootContract.lean`.

What this leaves unproved of `keep`, each a hypothesis of a statement above and none an axiom:

- `give_turn` assumes that the pieces the session holds, with the piece just read among them, are part of the store. That needs reading a piece's bytes to give the piece that was written, which is tested, and the session's map to give back what was put in it, for which Lean 4.35 has no lawful equality and hash on `ByteArray`.
- `answer_turn` assumes the root's name reads back to the root (`unhex` of `hex`), and takes from `save_opened` that the store holds each saved piece under its reference, which fails only when two pieces share a hash.
- That the function a turn saves is the one the request theorems speak of (`Reflect.lazy_turn_complete`) is not joined to this. What is proved is about its references: whatever value it resolves to, its root is that value's root.
- A VM and a node (`vmStart`, `vmFrom`, `nodeStart`, `nodeFrom`) are not covered: `Inv` is false of their phases (`homoiconic-q59.54`).

#### Scenario: A program that keeps hold of the function it was resumed from

- GIVEN `fn f -> f 5 (fn x -> ask 7 (fn y -> f))`, started, and its root answered with 0
- WHEN the second turn saves the waiting program
- THEN the root it reports is the root the same value has when it is held whole and saved (`kernel/KeepCheck.lean`)

#### Scenario: The statements are checked

- GIVEN `kernel/RootContract.lean`
- WHEN it is checked
- THEN `save_opened`, `advance_turn`, `start_turn`, `answer_turn`, `give_turn` and `waits_root` hold as written and each depends on no axiom but `propext`, `Classical.choice` and `Quot.sound`

### Requirement: A text is stored whole

Saving SHALL treat a text as it treats a number: a text whose byte form is larger than the given size SHALL be stored under its hash as one piece and replaced by its reference, and a smaller one SHALL be left in place. Saving SHALL NOT cut a text into parts.

#### Scenario: A long text is one piece

- GIVEN a waiting program that holds a text of 1,000 characters, saved with cuts at 256 bytes
- WHEN the pieces are listed
- THEN exactly one of them is that text, and its next turn, which does not look at the text, is not supplied it

### Requirement: A bounded run reply has a byte form

The Wire library SHALL define `Wire.RunReply`, its data encoder `Wire.runReplyData`, byte encoder `Wire.runReplyBytes` and strict inverse `Wire.readRunReply` in `kernel/Wire/Reply.lean`. Reply bytes SHALL be `Wire.write` of exactly one of these data shapes:

- `[0, value]`, where value is the existing `Wire.valueData` form of a resulting machine value;
- `[1]` for a still-running machine at its step budget;
- `[2]` for refused program bytes;
- `[3, index]` for an unbound outcome;
- `[4]` for a wrong outcome;
- `[5]` for machine fault;
- `[6]` for an unrepresentable machine value.

Tags 5 and 6 SHALL be internal errors, not language outcomes. A value whose Wire.valueData is absent SHALL encode as tag 6. Reading SHALL use the existing strict data reader and Wire.dataValue for the value field, reject unknown tags, wrong arities or invalid values, and preserve byte identity on read/write of every accepted reply. The run-reply envelope SHALL be independent of network framing. Its additional decode/budget/internal statuses and the compiled-machine value wire form SHALL NOT change `Reflect.reifyOutcome`, which remains the semantic outcome encoding used inside the metacircular interpreter. This wire format is tested, not proved.

#### Scenario: Outcomes have one complete envelope

- GIVEN each response kind, including a known factorial value and a closure
- WHEN its reply bytes are read as data and by Wire.readRunReply, then written again
- THEN the expected tag and complete fields are obtained and the same bytes are written; closure code and its captured values use the existing machine-value wire form

#### Scenario: Alternate or malformed reply forms

- GIVEN noncanonical CBOR, trailing bytes, an unknown reply tag, wrong arity or invalid value form
- WHEN Wire.readRunReply reads it
- THEN it is refused
