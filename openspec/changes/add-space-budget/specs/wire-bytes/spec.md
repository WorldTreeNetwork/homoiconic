# wire-bytes

## MODIFIED Requirements

### Requirement: A bounded run reply has a byte form
<!-- base: 4f575f0206c62cd7be99f27c1de262bde85caca4 openspec/specs/wire-bytes/spec.md -->

The Wire library SHALL define `Wire.RunReply`, its data encoder `Wire.runReplyData`, byte encoder `Wire.runReplyBytes` and strict inverse `Wire.readRunReply` in `kernel/Wire/Reply.lean`. Reply bytes SHALL be `Wire.write` of exactly one of these data shapes:

- `[0, value]`, where value is the existing `Wire.valueData` form of a resulting machine value;
- `[1]` for a still-running machine at its step budget;
- `[2]` for refused program bytes;
- `[3, index]` for an unbound outcome;
- `[4]` for a wrong outcome;
- `[5]` for machine fault;
- `[6]` for an unrepresentable machine value;
- `[7]` for a run stopped at its space limit, or whose answer written out is larger than four bytes for each cell of it (`add-space-budget`).

Tags 5 and 6 SHALL be internal errors, not language outcomes. A value whose Wire.valueData is absent SHALL encode as tag 6. Reading SHALL use the existing strict data reader and Wire.dataValue for the value field, reject unknown tags, wrong arities or invalid values, and preserve byte identity on read/write of every accepted reply. The run-reply envelope SHALL be independent of network framing. Its additional decode/budget/internal statuses and the compiled-machine value wire form SHALL NOT change `Reflect.reifyOutcome`, which remains the semantic outcome encoding used inside the metacircular interpreter. This wire format is tested, not proved. Adding tag 7 SHALL NOT change the reply of a run that stays within its space and whose answer fits: the reply to `examples/factorial.hom` at the budget 100000000 SHALL be `82008200c24e0d13f6370f96865df5dd54000000` and the reply to `examples/forever.hom` at 5000 SHALL be `8101` (`kernel/WireReplyCheck.lean`), as mjolnir's fixtures have them.

`Reflect.Data.written d` SHALL be an upper bound on the bytes of `d` written as text and as CBOR: a number or a name a third of its bits and two, a text two and four for each character, an array two and, for each item, two and the item. `Reflect.Data.writes d n` SHALL answer whether `Data.written d ≤ n`, looking at no more than that much of `d`, with a work list and no recursion on the nesting of `d`. `Wire.fitsValue v n` SHALL answer the same for the data form of the machine value `v` without building it: data as `Data.writes`, and a function as two, a hundred for each instruction of its code, the literals in it, and each captured value where it is held; it SHALL NOT recurse on the nesting of data or of captured values. `Surface.replyBytes` SHALL answer `[7]` for a halted value `v` for which `Wire.fitsValue v (4 * cells)` is false, before `Wire.valueData` is called on it. These bounds are tested, not proved.

#### Scenario: Outcomes have one complete envelope

- GIVEN each response kind, including a known factorial value and a closure
- WHEN its reply bytes are read as data and by Wire.readRunReply, then written again
- THEN the expected tag and complete fields are obtained and the same bytes are written; closure code and its captured values use the existing machine-value wire form

#### Scenario: Alternate or malformed reply forms

- GIVEN noncanonical CBOR, trailing bytes, an unknown reply tag, wrong arity or invalid value form
- WHEN Wire.readRunReply reads it
- THEN it is refused

#### Scenario: An answer larger written than held

- GIVEN a program that doubles an array forty times and answers it, and a program of thirty definitions that answers a function
- WHEN `Surface.replyBytes` runs each with the default space
- THEN each reply is `81 07`, and neither builds the bytes of the answer
