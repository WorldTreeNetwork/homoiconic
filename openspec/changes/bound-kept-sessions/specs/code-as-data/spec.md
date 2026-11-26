# code-as-data

## MODIFIED Requirements

### Requirement: Nesting is bounded by memory, not by the native stack
<!-- base: ad346fa30d8e28c6fc00a44346fa0db007d87161 openspec/specs/code-as-data/spec.md -->

A function the compiled kernel runs on data, a program, compiled code or a machine value SHALL NOT call itself once for each level of nesting or each item of a list (`homoiconic-q59.72`). Where a function that a theorem mentions would, the kernel SHALL keep its definition and run a walk that keeps its work in a list on the heap and calls itself only in tail position, with a `@[csimp]` theorem that the walk equals the definition: `reify`, `unreify`, `comp`, `decomp` and `Data.mentions` in `Reflect`, `valueData` and `codeFits` in `Wire`, and `renderData`, `chain` and `numbers` in `Surface`; and on the paths behind `keep`, `vm`, `node`, `ask` and `chan` (`bound-kept-sessions`, `homoiconic-q59.78`): `Data.toP`, `Data.listToP`, `MValue.toP`, `envToP`, `P.toData`, `P.hyd`, `P.nodes`, `Data.nodes` and `Data.decEq` (by `Data.same`) in `Reflect`, `pieceItem`, `itemPiece` and `cut` in `Wire`, the drivers' loops `driveRun`, `schedIn` and `autoRun`, and the readers `Keep.parts`, `openProcs`, `renderNodeProcs`, `dataEntries`, `dataOps`, `dataEvents`, `renderProcs`, `Cross.readLines` and `Cross.readChain` in `Surface`, each a loop proved equal to its definition. `Keep.full`, which was `partial`, SHALL be a walk bounded by the units it may count, with its own refusal. `P.nodesWithin` and `Data.nodesWithin` SHALL be restated with their laws. Equality of data (`==`, and operation 5) SHALL be `Data.same` and equality of code in `blockTerm` `Code.same`, each a walk proved to decide equality. `kernel/WalkContract.lean` SHALL restate each of these and print its axioms, which SHALL be Lean's standard three at most. The source reader and the derived `Repr` instances are outside this requirement: the reader still recurses on how deep a source nests and, past about 100000 items, on how long a literal is (`homoiconic-q59.77`, `homoiconic-q59.84`), and an image reads only the source built into it. `Crossing.mix`, which a crossing guest reaches, is outside it as well.

#### Scenario: Data a million arrays deep

- GIVEN a program that builds an array nested a million deep and answers it, and one that compares such an array with itself by operation 5
- WHEN each runs under the run command with an 8 MiB stack, or in the image
- THEN the first prints the million brackets, the zero and the million brackets, and the second prints `1`

#### Scenario: A program a million functions deep

- GIVEN the byte form of a million functions each inside the last, and of a list of 419429 zeros
- WHEN each is read back and compiled, and the first is also quoted through one interpreter
- THEN the functions print `<function>` and the list runs out of its 1000 steps

#### Scenario: Long results, saves and logs on the host

- GIVEN a kept turn whose result is a list of 200000 numbers, one whose result is nested a million deep, waiting programs that hold 500000 numbers and a nest of a million, a `vm` log of 100000 entries and a `node` log of 70000 ops
- WHEN `host/out/keep`, `host/out/vm` and `host/out/node` run them with an 8 MiB stack
- THEN each prints its result, its root or its state, where the kernel before ended the process on a full stack for each but the node log, which the turn's space limits before its depth matters (`host/check.sh`)

#### Scenario: The walks are the definitions

- GIVEN `kernel/WalkContract.lean`
- WHEN it is checked
- THEN each walk is restated as equal to its definition, or as deciding equality, and no axiom but `propext`, `Classical.choice` and `Quot.sound` is printed
