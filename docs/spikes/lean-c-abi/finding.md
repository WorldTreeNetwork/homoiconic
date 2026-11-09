---
spike_id: lean-c-abi
hypothesis_id: null
source_synthesis: null
run_at: 2026-11-08T18:15:00-08:00
time_spent_min: 25
verdict: go
version-pinned: lean 4.35.0, zig 0.16.0
---

# Spike: Zig calls a compiled Lean function through the C ABI

## Claim Tested

A Zig host can call the compiled Lean 4 kernel through the C ABI without reimplementing eval.

## Minimal Test

`src/Kernel.lean` exports `kernel_eval`, which computes `n * 17 + 3`. `lean -c` emits C. `leanc -c` compiles that C to an object. `host.zig` only declares `extern fn kernel_eval(n: u32) u32` and prints `kernel_eval(4)`. `zig build-obj` compiles the host. `leanc` links the two objects. The formula appears only in the Lean source.

## Evidence

`repro-command.sh` printed `71`, which is `4 * 17 + 3`. `host.zig` contains neither `17` nor `+ 3`. The generated C in `out/kernel.c` is `uint32_t kernel_eval(uint32_t)` and holds the constants. Log: `evidence.log`.

`leanc -shared` on the C file produced a dylib with no exported code (dead strip). Zig 0.16 `build-exe` then failed to parse that dylib (`EndOfStream`). The working link is the object file, not a dlopen'd library. This call did not run `initialize_src_Kernel`. That is enough for this unboxed arithmetic function and is not a claim about a Lean runtime that allocates.

## Verdict: go

Zig 0.16.0 called Lean 4.35.0's exported C function and got the Lean-computed result. The host did not reimplement the function. The real interpreter ABI, initialization, and allocation stay on `add-zig-host`.
