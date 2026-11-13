# wire-bytes

## ADDED Requirements

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
