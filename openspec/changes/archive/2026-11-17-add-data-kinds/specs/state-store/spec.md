## MODIFIED Requirements

### Requirement: State can be held in pieces
<!-- base: e1d861ed3af608030f7f602a24587bed88775585 openspec/specs/state-store/spec.md -->

A piece SHALL be a number, a text, a name, an empty list, a pair, a function, or a reference, and any part of a pair or a function MAY be a reference. A text SHALL be one piece with no parts. A store SHALL map references to pieces and MAY lack any reference. The kind of reference SHALL be a parameter of every definition and theorem. A machine state held whole SHALL resolve to itself under every store. A piece held in the store SHALL be replaceable by its reference without changing what resolves. A piece SHALL resolve to at most one thing. The lazy machine SHALL take a text apart, and SHALL see a name as its number, with no fetch beyond the piece itself. The theorems of this spec SHALL hold with their statements unchanged by text and names, and `kernel/StoreContract.lean` SHALL check without having been edited.

#### Scenario: Cut and resolve

- GIVEN a machine state cut at every value into a store
- WHEN its pieces are resolved
- THEN the result is the state that was cut

#### Scenario: Text in stored state

- GIVEN a program stopped while it holds a text and a name, cut at every value
- WHEN the lazy machine continues it with the whole store, and takes the text apart by `case`
- THEN it halts with what the plain machine halts with

#### Scenario: A withheld text is a pause

- GIVEN a stored program whose next step looks at a text, and a store with that text's piece withheld
- WHEN it is run
- THEN it pauses needing that piece's reference
