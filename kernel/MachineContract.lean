import Reflect

open Reflect

-- Acceptance check for `add-bytecode-machine`. It fails to compile until the
-- theorems exist with exactly these signatures, for every table of operations.
example : ∀ [Ops], ∀ t o,
    Direct [] t o ↔
    ∃ n w, run n (load (compile t)) = .halted w ∧ readOutcome w = some o :=
  Reflect.machine_correct

example : ∀ [Ops], ∀ t n w,
    run n (load (compile t)) = .halted w → ∃ o, Direct [] t o ∧ w = MP.injO o :=
  Reflect.machine_exact

example : ∀ [Ops], ∀ t, (∀ o, ¬ Direct [] t o) → ∀ n w, run n (load (compile t)) ≠ .halted w :=
  Reflect.machine_never_halts

example : ∀ [Ops], ∀ n m s, run (n + m) s = run m (run n s) := Reflect.run_add

example : ∀ [Ops], ∀ n o, run n (.halted o) = .halted o := Reflect.run_halted

example : ∀ [Ops], ∀ n s, runUntil n s = run n s := Reflect.runUntil_eq

example : ∀ t, decompile (compile t) = some t := Reflect.decompile_compile

example : ∀ [Ops], ∀ n s, depth (run n s) ≤ depth s + n := Reflect.depth_bound

example : ∀ [Ops], ∀ t n, run n (load (compile t)) ≠ .fault := Reflect.machine_never_faults

example : ∀ [Ops], ∀ t n, runUntil n (load (compile t)) ≠ .fault :=
  Reflect.machine_never_faults_until

example : ∀ [Ops], ∀ t fuel, runPriced fuel (load (compile t)) ≠ .fault :=
  Reflect.machine_never_faults_priced

#print axioms Reflect.machine_correct
#print axioms Reflect.machine_exact
#print axioms Reflect.machine_never_halts
#print axioms Reflect.run_add
#print axioms Reflect.run_halted
#print axioms Reflect.decompile_compile
#print axioms Reflect.depth_bound
#print axioms Reflect.runUntil_eq
#print axioms Reflect.machine_never_faults
#print axioms Reflect.machine_never_faults_until
#print axioms Reflect.machine_never_faults_priced
