# event-log

At fold, the overview and the Purpose stop saying that this spec does not say where an identifier comes from: for a log that is read, it does.

## ADDED Requirements

### Requirement: An entry that is read is named by its hash

An entry of a log that is read SHALL be written as a mark and an answer, both data, and its identifier SHALL be the name of that pair: `Reflect.Entry.seal key mark answer`, with `key` being `Surface.Keep.entryName`, the Blake3 hash of the bytes `Wire.write` gives the pair, as one number with the first byte highest. The kernel SHALL compute the name; a log SHALL NOT supply it. The mark SHALL NOT be read for anything else. For every function `key` that gives different names to different data, two sealed entries with one identifier SHALL be one entry (`sealed_same`), and every entry of a log whose entries are all sealed SHALL be among the log's first deliveries (`sealed_first`). That Blake3 gives different names to different data SHALL be a stated assumption, not a theorem and not an axiom of any proof. Reading a log and sealing its entries SHALL be tested, not proved.

#### Scenario: Two answers under one mark

- GIVEN `examples/ask.hom` and the log `[[1, 20], [1, 22]]`
- WHEN the VM handles the log
- THEN it acts on both entries, finishes with 42, and its state has another root than `examples/ask.log` gives

#### Scenario: The statement

- GIVEN `Function.Injective key`, two entries sealed under `key`, and equal identifiers
- WHEN `kernel/LogContract.lean` is checked
- THEN the entries are equal, and the axioms printed for `sealed_same` and `sealed_first` are among `propext`, `Classical.choice` and `Quot.sound`

#### Scenario: The name is the hash

- GIVEN the entry `[1, 20]`
- WHEN `kernel/LogCheck.lean` runs
- THEN its name is below 2^256, its highest byte is the first byte of the Blake3 hash of the entry's bytes and its lowest the last, and the fold given sealed entries saves the root the session saves

## MODIFIED Requirements

### Requirement: An entry already in the log changes nothing
<!-- base: c4df19c74e0c445275ca2539a754fd11339496b0 openspec/specs/event-log/spec.md -->

For every operation table, handling an entry that is in the log a state was reached by SHALL leave that state as it is, and SHALL lead nowhere else (`log_again`). A log with an entry of its first part delivered again later SHALL lead to the states the log without that delivery leads to (`log_redeliver`). A log SHALL lead to the states its first deliveries, in their order, lead to (`log_once`, with `firsts`). Two entries SHALL be the same delivery when their identifiers are equal, whatever their answers.

#### Scenario: Delivered again

- GIVEN `examples/ask.hom` and `examples/ask-again.log`, which holds five deliveries of two entries
- WHEN the VM handles the log
- THEN it acts on two entries and its state has the root that `examples/ask.log` gives

#### Scenario: The statement

- GIVEN `Logged sourceP p log v` and `e ∈ log`
- WHEN `kernel/LogContract.lean` is checked
- THEN `Handle source v e v' ↔ v' = v` holds
