---
spike_id: lean-runtime-init
hypothesis_id: lean-runtime-init
source_synthesis: null
run_at: 2026-11-08T20:29:51-08:00
time_spent_min: 30
verdict: go
version-pinned: lean 4.35.0, zig 0.16.0
---

# Spike: object-link evalFuel after Lean runtime init

## Claim Tested

Object-linking an exported Lean function that parses one program and calls `evalFuel`, after the host runs the package initializer, returns the codes in `openspec/changes/add-zig-host/design.md`. The `lean-c-abi` spike linked unboxed arithmetic and did not initialize the runtime.

## Minimal Test

`src/Spike.lean` exports `kernel_run`. It parses the design grammar and calls `Circular.evalFuel` at the empty environment with fuel 8. The Zig host calls `initialize_src_Spike(0)`, marks the end of initialization, builds a Lean string with `lean_mk_string`, and passes that string in. The host compares the returned codes. It does not case-split on variable, lambda, or application.

`Syntax.lean` and `Semantics.lean` are copied into the spike's build directory and compiled outside the kernel package, so `lean -c` emits `Circular.*` symbols. `leanc` links those objects with the Zig object. The kernel package is unchanged. The link is not a dylib.

## Evidence

`repro-command.sh` printed:

```
([0] [0]) 0
0 1
[1] 0
(0 ([(0 0)] [(0 0)])) 1
([(0 0)] [(0 0)]) 4294967295
bad 4294967295
```

Those are the design codes: closure `0`, unbound `0` as `1`, and `none` as `4294967295`. The diverging argument returns. `omega` returns. The exit code is 0.

`out/host` defines `_l_Circular_evalFuel` and `_initialize_src_Spike`. `kernel_run` is an undefined reference to `_l_Circular_evalFuel` in `out/spike.o` until the link. Log: `evidence.log`.

## Verdict: go

Lean 4.35.0 allocated the program text, parsed it, and ran the kernel's `evalFuel`. Zig 0.16.0 received the codes and does not contain the evaluator. The object link from `lean-c-abi` still holds once the host initializes the runtime. This spike does not add the host to the kernel package.
