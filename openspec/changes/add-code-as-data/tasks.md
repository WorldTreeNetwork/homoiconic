# Tasks

- [x] Add the `Reflect` library to the kernel package with `Syntax` and `Semantics` as in `design.md`. `lake build` exits 0. `Circular` and `Contract.lean` are unchanged.
- [x] Prove `Direct` deterministic, and `evalFuel` sound, monotone, and complete for it.
- [x] Add `Reflect.Interpreter`: one closed term built from variables, lambdas, applications, literals, `succ`, `cons`, and `dcase`. It does not mention `Direct` or `evalFuel`.
- [x] Write `kernel/ReflectContract.lean` with the four signatures in `design.md`. It fails to compile until they exist.
- [x] Prove `reflective` and `reflective_coverage`.
- [x] Prove `reflective_env` and `tower`.
- [x] `Reflect.Examples`: the spike's seventeen scenarios as checked statements, including the program that builds and runs another program at two interpreter levels.
- [x] `lake env lean ReflectContract.lean` prints no `sorryAx` and no package axiom.
