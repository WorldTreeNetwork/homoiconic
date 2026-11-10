import Reflect

open Reflect

-- Acceptance check for `add-bytecode-machine`. It fails to compile until the
-- theorems exist with exactly these signatures.
example : ∀ t o,
    Direct [] t o ↔
    ∃ n w, run n (load (compile t)) = .halted w ∧ readOutcome w = some o :=
  Reflect.machine_correct

example : ∀ t n w,
    run n (load (compile t)) = .halted w → ∃ o, Direct [] t o ∧ w = MP.injO o :=
  Reflect.machine_exact

example : ∀ t, (∀ o, ¬ Direct [] t o) → ∀ n w, run n (load (compile t)) ≠ .halted w :=
  Reflect.machine_never_halts

example : ∀ n m s, run (n + m) s = run m (run n s) := Reflect.run_add

example : ∀ n o, run n (.halted o) = .halted o := Reflect.run_halted

example : ∀ t, decompile (compile t) = some t := Reflect.decompile_compile

example : ∀ n s, depth (run n s) ≤ depth s + n := Reflect.depth_bound

#print axioms Reflect.machine_correct
#print axioms Reflect.machine_exact
#print axioms Reflect.machine_never_halts
#print axioms Reflect.run_add
#print axioms Reflect.run_halted
#print axioms Reflect.decompile_compile
#print axioms Reflect.depth_bound
