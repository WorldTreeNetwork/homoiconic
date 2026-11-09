## ADDED Requirements

### Requirement: The host returns the kernel's result

The Zig host SHALL pass one program's bytes to the Lean export `kernel_run`. That export SHALL parse the concrete syntax and SHALL call `evalFuel` at the empty environment. The returned code SHALL be `0` for a closure, `2 * i + 1` for `unbound i`, and `4294967295` for `none`. The Zig sources SHALL pass those bytes and SHALL NOT case-split on variable, lambda, and application to produce an outcome.

#### Scenario: Identity

- GIVEN the text `([0] [0])`
- WHEN the Zig test runs it through `kernel_run`
- THEN the code is `0`

#### Scenario: An open variable is unbound

- GIVEN the text `0`
- WHEN the Zig test runs it through `kernel_run`
- THEN the code is `1`

#### Scenario: An open lambda is a closure

- GIVEN the text `[1]`
- WHEN the Zig test runs it through `kernel_run`
- THEN the code is `0`

#### Scenario: An unbound function skips a diverging argument

- GIVEN the text `(0 ([(0 0)] [(0 0)]))`
- WHEN the Zig test runs it through `kernel_run`
- THEN the code is `1` and the call returns

#### Scenario: A diverging term has no outcome

- GIVEN the text `([(0 0)] [(0 0)])`
- WHEN the Zig test runs it through `kernel_run`
- THEN the code is `4294967295` and the call returns

### Requirement: The host contains no evaluator

The Zig tree SHALL load the Lean export and SHALL NOT define an evaluator.

#### Scenario: One evaluator

- GIVEN the Zig sources
- WHEN they are reviewed against the partition
- THEN the outcome comes from `kernel_run`

### Requirement: The link is the proved object path

The host SHALL link by the object path recorded in `docs/spikes/lean-c-abi/`. The host SHALL call the Lean runtime initializer on the path that allocates. The build SHALL NOT depend on `dlopen`.

#### Scenario: The test links

- GIVEN the Lean object and the Zig object
- WHEN `leanc` links them and the Zig test runs
- THEN the test exits 0
