# logged-processes

At fold, the Purpose stops saying that this spec does not say where an identifier comes from.

## ADDED Requirements

### Requirement: An op that is read is named by its hash

An op of a log that is read SHALL be written as a mark and an event, and its identifier SHALL be the name `Surface.Keep.entryName` gives to that pair as written (`Reflect.Op.seal`). The kernel SHALL compute the name. For every function `key` that gives different names to different data and every way of reading an event from data, two sealed ops with one identifier SHALL be one op (`sealed_op_same`), and every op of a log whose ops are all sealed SHALL be among the log's first deliveries (`sealed_op_first`). An op that cannot happen SHALL be reported by its place in the log, counted from 0, and its event.

#### Scenario: The statement

- GIVEN `Function.Injective key`, two ops sealed under `key` and one `read`, and equal identifiers
- WHEN `kernel/NodeContract.lean` is checked
- THEN the ops are equal

#### Scenario: The session and nodeRun agree on sealed ops

- GIVEN the logs of `kernel/NodeCheck.lean`, each op sealed for `nodeRun` as the session seals it
- WHEN `kernel/NodeCheck.lean` runs
- THEN every line starts with `ok`
