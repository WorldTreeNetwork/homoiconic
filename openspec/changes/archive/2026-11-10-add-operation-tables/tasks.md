# Tasks

- [x] Owner: direction from the user, 2026-11-10.
- [x] `Term.prim`, `reify` tag 6, the `Ops` class, six `Direct` rules and the `evalFuel` case.
- [x] The interpreter's `operation` branch.
- [x] `Reflect/SemanticsProofs.lean`, `Proof.lean`, `Correctness.lean`: all theorems restated for every table and proved.
- [x] Machine instructions `checkNat` and `prim`; `MachineProof.lean`, `MachineExact.lean`, `RunUntilProof.lean` proved for every table.
- [x] Theorems that do not involve a table (`decompile_compile`, `reify_inj`, and others) do not take one.
- [x] `Reflect/Arith.lean`: the first table and its names.
- [x] The reader resolves the built-in names; a program's own binding of the same name wins.
- [x] Ten operation scenarios in `kernel/ReflectRun.lean`, each run directly, interpreted once and twice, on the machine, sliced, and decompiled.
- [x] Nineteen surface examples in `kernel/Surface/Expect.lean`; `examples/factorial.hom` in the host check.
- [x] `lake build`, both contracts, `ReflectRun.lean`, `Surface/Check.lean` and `sh host/check.sh` exit 0.
- [x] Advise by a reader from another model family. Accepted, 2026-11-10; three notes, answered in `52ce1c8`; notes in `reviews/`.
- [x] Fold: apply the deltas to `code-as-data`, `bytecode-machine` and `surface-syntax`, note the table in the `zig-host` overview, amend `ARCHITECTURE.md`, and note P8 in the vision.
