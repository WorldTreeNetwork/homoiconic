# Tasks

- [x] Export `kernel_run` from the Lean package. It parses the concrete syntax in `design.md`, calls `evalFuel` at the empty environment, and returns the result code. `lake build` and `lake env lean Contract.lean` still exit 0.
- [x] On the allocating path, call the Lean runtime initializer the package emits.
- [x] Link the Zig object and the Lean object the way `docs/spikes/lean-c-abi/` does. Leave `dlopen` unused.
- [x] A Zig test passes `([0] [0])`, `0`, `[1]`, `(0 ([(0 0)] [(0 0)]))`, and `([(0 0)] [(0 0)])`, and checks the codes in the spec. The Zig sources pass bytes and do not case-split on variable, lambda, and application to produce an outcome.
