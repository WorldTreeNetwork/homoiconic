# lean-kernel

All four requirements are removed, so the capability has none left. At fold, delete `openspec/specs/lean-kernel/`.

## REMOVED Requirements

### Requirement: The kernel is executable Lean
<!-- base: c9c2d96ad7c94d644c07226360d7281a65e104ad openspec/specs/lean-kernel/spec.md -->

**Reason:** the `Circular` library is deleted. The executable entry for the remaining language is `Reflect.evalFuel` and the machine, in `openspec/specs/code-as-data/spec.md` and `openspec/specs/bytecode-machine/spec.md`.

#### Scenario: The package builds without the first kernel

- GIVEN the kernel package after this change
- WHEN `lake build` runs
- THEN the build exits 0 and no module named `Circular` is built

### Requirement: Terms include quote
<!-- base: c9c2d96ad7c94d644c07226360d7281a65e104ad openspec/specs/lean-kernel/spec.md -->

**Reason:** `Circular.Term` is deleted. In `Reflect`, quoting is a literal of the program's data, stated in `code-as-data` under "A literal is a quotation".

#### Scenario: Quotation is stated elsewhere

- GIVEN a reader who asks how a program is quoted
- WHEN they read the living specs
- THEN the answer is in `code-as-data`, and no spec names a `quote` constructor

### Requirement: The pure fragment is metacircular
<!-- base: c9c2d96ad7c94d644c07226360d7281a65e104ad openspec/specs/lean-kernel/spec.md -->

**Reason:** `metacircular` and `coverage` are deleted with the library. `reflective` and `reflective_coverage` state the agreement for every `Reflect` term, with no fragment, in `code-as-data` under "The interpreter takes a program as data". Nothing in the tree is proved about the Mogensen–Scott encoding after this change.

#### Scenario: The theorem that remains has no fragment

- GIVEN a program that contains a quotation
- WHEN someone asks whether the interpreter theorem covers it
- THEN it does, by `reflective`, and no theorem named `metacircular` exists

### Requirement: The theorem's dependencies are the logic, not an assumption of correctness
<!-- base: c9c2d96ad7c94d644c07226360d7281a65e104ad openspec/specs/lean-kernel/spec.md -->

**Reason:** it names `metacircular` and `coverage`. The same requirement holds for the remaining theorems in `code-as-data` and `bytecode-machine`, each under "The theorems depend on the logic only".

#### Scenario: The remaining contracts are the check

- GIVEN `ReflectContract.lean` and `MachineContract.lean`
- WHEN `sh host/check.sh` runs
- THEN both are checked and both exit 0
