# Tasks

- [x] Owner: the user, asked directly on 2026-11-14. Beads `homoiconic-q59.37`, `homoiconic-q59.38`.
- [x] `kernel/Surface/Read.lean`: a run of `def`s reads each body once and binds the definitions after what they mention, a ring as one function of a number (`assemble`, `emit`, `trRun`).
- [x] `kernel/Surface/Read.lean`: array patterns `[a, b, c]` and `[a, b, ...rest]` (`parseArrayPattern`, `arrayNode`), and what is refused.
- [x] `kernel/Surface/Expect.lean`: the terms a ring, a later definition and the new patterns read as; texts refused; texts printed.
- [x] Every file of `examples/` reads to the byte form it had before the reader changed (compared 2026-11-14 against the bytes the earlier `host/out/bytes` wrote).
- [x] `examples/calc.hom`, `examples/brainfuck.hom`, `examples/words.hom` rewritten; what they print is unchanged.
- [x] `host/check.sh`: a ring, a later definition, a bound name, a fixed length, another length with and without a catch-all arm, a least length, three refusals; each through the interpreter.
- [x] Functions kept in arrays split to `homoiconic-q59.39` for the owner's decision.
- [x] `sh host/check.sh` exits 0 (2026-11-14, macOS arm64).
- [x] Advise by a reader from another model family (gpt-6.1-sol), 2026-11-14, on `8f26fd2`. Send-back, one required fix: a catch-all arm that nothing falls to was being read, so an old program with an unbound name there was refused. It is not read now. Review in `reviews/`.
- [x] `sh host/check.sh` exits 0 after the fix (2026-11-14).
- [x] Fold. 2026-11-14, after the send-back was answered in `95ba66e`: the MODIFIED requirement "Programs are written with names and indentation" and the two ADDED requirements are in `openspec/specs/surface-syntax/spec.md`.
