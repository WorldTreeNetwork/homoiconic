# retire-circular-kernel

> **ACTIVE BUILD**

**Rigor:** change

Depends on: `move-host-to-reflect` (folded, `8b23867`). Vision: `add-verifiable-network-vision`. Fixes beads `homoiconic-3gx` and `homoiconic-q59.5`. Approved by the user, 2026-11-10 ("go").

## Why

The package holds two evaluators. `Circular` is the first one: quote-free programs only, one interpreter level, and a host export that answers with an ambiguous 32-bit code. `Reflect` covers every program, at any environment and any interpreter depth, and the host already runs it. Keeping both means two semantics to read and two host paths to maintain. Separately, there is still no way to run a program file: programs reach the kernel only through the check.

## What

- REMOVE the `Circular` library, `Contract.lean`, `Run.lean`, `Axioms.lean`, the export `kernel_run`, its result code, and the Zig checks that call it
- REMOVE capability `lean-kernel`. Its statements are superseded by `code-as-data`
- ADD a host command, `host/out/run <program-file> [step-budget]`, that prints what `reflect_run` writes
- The host objects are now compiled with optimisation. They were not, and the run command measured about 3.7 million steps a second; with `-O3` it measures about 34 million. Lean's runtime assertions stay on; defining `NDEBUG` reaches about 45 million and removes checks on the generated C, so it is not used
- `host/check.sh` checks `ReflectContract.lean` and `MachineContract.lean` in place of `Contract.lean`

## What is lost

`metacircular` and `coverage` for the Mogensen–Scott encoding are deleted from the tree. They stay in git at `8b23867` and earlier. `reflective` and `reflective_coverage` state the same agreement for a larger language, with no fragment. They do not say anything about the Scott encoding, and nothing after this change does.

The old host check passed a program with an embedded zero byte. That case is kept, now through `reflect_run`.

## Impact

- Capabilities: REMOVED `lean-kernel`; MODIFIED `zig-host`, `language-partition` (at fold)
- `ARCHITECTURE.md`: every section that names `Circular`, `kernel_run`, `lean-kernel`, two evaluators, or a third library changes at fold: the opening source-of-record line, Partition, Circularity, Reflect, Surface, Boundary, and the downstream list
- Overview paragraphs of `code-as-data` and `surface-syntax` say `Reflect` and `Surface` sit beside `Circular`. They are corrected at fold; no requirement in either changes
- `add-verifiable-network-vision/design.md`: a note at the top says the document was written on 2026-11-09 against the first kernel and maps its names to the ones that landed; `proposal.md` there names `reflective` as the theorem in place
- `docs/spikes/` is history and is not edited
- The Lake package keeps the name `circularKernel`, so the initializer symbol is unchanged

## User journey & surfaces

The surface is a terminal command.

- **Working** — `host/out/run examples/append.hom` prints `[1, 2, 3, 4]`. A second argument sets the step budget.
- **Empty** — with no argument, the command prints how to call it and exits 2.
- **Failed** — a file that cannot be read gives one line with the reason, and exit 2. The line does not repeat the path. So does an answer that cannot be written, for example to a closed pipe. A program that is not valid text, or that ends in an error, prints the kernel's own text and exits 0: the command reports what the kernel said and does not judge it.
- **Off** — before `sh host/check.sh` has built it, the command does not exist.

## Out of scope

- A REPL, reading from standard input, or an installed binary on the path.
- Exit codes that depend on the program's outcome. That needs Zig to read the answer, or a second export.
- The file extension. `.hom` is a placeholder in `examples/`; the command reads any path.
- Renaming the Lake package.
