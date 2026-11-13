# Run a program through the metacircular interpreter

> **FOLDED 2026-11-13** into `openspec/specs/zig-host/spec.md`. Archived. Bead `homoiconic-q59.31`.

## Why

`Reflect.reflective` says the closed term `interp`, given a program as data,
answers the data form of the program's outcome, and `Reflect.tower` says the
same through any number of interpreters. Nothing ran it. A program's byte form
is already its data form (`reify`), so bytes can be handed to `interp` as they
are, and the proved machine can run the interpreter on them.

## What changes

- `Surface.interpBytes` and `Surface.interpText` (`kernel/Surface/Bytes.lean`)
  run `level k t` on the machine and read the answer back through `k` levels of
  `reifyOutcome` (`unreifyOutcome`, `unlift`), then render it as a direct run
  renders. An answer that is not an outcome's data form renders as an internal
  error; the theorems say it does not occur.
- The export `reflect_interp` (`kernel/Surface/Host.lean`) takes the program,
  the output buffer, the budget, the number of levels and whether the program
  is bytes or source.
- `host/out/run` accepts `--interp` (one level) and `--interp=k`, with or
  without `--bytes`.
- `host/check.sh` checks that every example, an identity function and a
  program that goes wrong print the same through 0, 1 and 2 interpreters as
  run directly, from source and from bytes.

## What does not change

The language, evaluation, the interpreter, the machine and every theorem. The
read-back and the rendering are tested, not proved, as the renderer is. The
step budget counts machine steps of the outermost run, so a program that
finishes directly within a budget may not finish through the interpreter.

## Not here

The machine image still embeds source and calls `reflect_run`. Loading a byte
form into the image at boot is `homoiconic-q59.32`.
