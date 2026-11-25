# zig-host

## ADDED Requirements

### Requirement: The exports that make one run take a space

`reflect_run`, `reflect_run_bytes` and `reflect_reply_bytes` SHALL take `space : u64`, a number of cells, after `budget`; `reflect_interp` SHALL take it after `budget` and before `levels`. Each SHALL run its program with `Reflect.runIn` under a `Space` of that many cells whose count is `reflect_live_cells` cut at three quarters of them (`Space.bar`), and SHALL answer the space outcome, the text `no result within <space> cells` or the reply `[7]`, for a run that ends as `full` and for an answer that written out would take more than four bytes for each cell of the space (a data answer on the text exports, any answer on `reflect_reply_bytes`). `reflect_default_space` SHALL answer `Reflect.defaultSpace`; its argument is ignored. `reflect_live_cells` (`kernel/ffi.c`) SHALL count the constructor objects reachable from a Lean value through constructor fields, each once, by address, and a number too large for a machine word so that with the box around it it is `natCells`; it SHALL stop past its cut and answer one more than the cut, SHALL answer the same when it cannot get memory for its table or stack, and SHALL change nothing. Its table SHALL start at 4096 slots and be made four times as large when three quarters full, up to the least power of two slots that is at least four thirds of the cut and two, and its stack SHALL hold at most one entry for each cell counted. A reply past the ledger therefore depends on what the runtime shares and on whether that memory can be had; the same Lean objects on the image and in a Linux process give the same count. It is the only place the kernel package reads what the runtime shares, and it is trusted, not proved. Zig SHALL NOT count cells or read a state. Every other evaluating export SHALL keep its arguments; the machine runs behind them are turns (`openspec/specs/bytecode-machine/spec.md`).

`host/out/run [--bytes] [--interp[=levels]] [--text] <program-file> [step-budget [space]]` SHALL pass the space given, or the kernel's default. A space that is not a whole number below 2^64 SHALL be refused on the host's own line with exit status 2.

#### Scenario: A run out of space is the kernel's text

- GIVEN `def deep x = [x, ...deep x]` applied to 0
- WHEN `host/out/run` runs it with the budget 100000000 through 0, 1 and 2 interpreters, at level 2 with the space 100000
- THEN each prints `no result within <space> cells` and exits 0

#### Scenario: The limit undone

- GIVEN the same program and a space of 18446744073709551615
- WHEN `host/out/run` runs it with the budget 100000000
- THEN the run is not stopped for space: it ends in the budget line with peak resident memory above 256 MiB, which the check refuses
