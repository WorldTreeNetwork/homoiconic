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

example : ∀ [Ops], ∀ fuel s, ∃ n, n ≤ fuel ∧ runPriced fuel s = run n s :=
  Reflect.runPriced_run

example : ∀ [Ops], ∀ {fuel : Nat} {s t : State}, runPriced fuel s = t → ∃ n, run n s = t :=
  Reflect.runPriced_reach

example : ∀ [Ops], (∀ n d, Ops.cost n d = 1) → (∀ d, Ops.work d = 1) → (∀ i, Ops.reach i = 1) →
    ∀ fuel s, runPriced fuel s = runUntil fuel s :=
  Reflect.runPriced_unit

example : ∀ [Ops], ∀ t fuel w,
    runPriced fuel (load (compile t)) = .halted w → ∃ o, Direct [] t o ∧ w = MP.injO o :=
  Reflect.machine_exact_priced

-- A tail loop runs in a bounded set of states (`homoiconic-q59.65`): a block
-- entered in tail position pushes no frame.
example : ∀ [Ops], ∀ {s : State} {a p : Nat}, 0 < p → run (a + p) s = run a s →
    ∀ n, ∃ j, j < a + p ∧ run n s = run j s :=
  Reflect.run_cycle

example : ∀ [Ops], ∀ {s : State} {a p : Nat}, 0 < p → run (a + p) s = run a s →
    ∀ fuel, ∃ j, j < a + p ∧ runPriced fuel s = run j s :=
  Reflect.runPriced_cycle

example : ∀ [Ops], run (4 + 4) (load (compile omega)) = run 4 (load (compile omega)) :=
  Reflect.omega_cycle

example : ∀ [Ops], run (21 + 17) (load (compile loopForever)) = run 21 (load (compile loopForever)) :=
  Reflect.forever_cycle

example : ∀ fuel,
    (∃ j, j < 38 ∧ runPriced fuel (load (compile loopForever)) =
      run j (load (compile loopForever))) ∧
    (∃ j, j < 1685 ∧ runPriced fuel (load (compile (level 1 loopForever))) =
      run j (load (compile (level 1 loopForever)))) :=
  Reflect.forever_bounded

-- A space limit beside the step budget (`add-space-budget`, `homoiconic-q59.67`),
-- for every table and every count a host might supply. These bound the cells a
-- run makes; none says what a state holds.
example : ∀ [Ops], ∀ (sp : Space) fuel credit s,
    ∃ n, n ≤ fuel ∧ (runSpace sp fuel credit s).state = run n s :=
  Reflect.runSpace_run

example : ∀ [Ops], ∀ (sp : Space) fuel credit s t,
    runSpace sp fuel credit s = .reached t → t = runPriced fuel s :=
  Reflect.runSpace_priced

example : ∀ [Ops], ∀ (sp : Space) fuel credit s t,
    runSpace sp fuel credit s = .full t →
      ∃ k, k < fuel ∧ run k s = t ∧ credit < madeIn (k + 1) s :=
  Reflect.runSpace_full

example : ∀ [Ops], ∀ (sp : Space) fuel credit s,
    madeIn fuel s ≤ credit → runSpace sp fuel credit s = .reached (runPriced fuel s) :=
  Reflect.runSpace_within

example : ∀ (sp : Space), sp.bar = sp.cells - sp.cells / 4 := fun _ => rfl

example : ∀ [Ops], ∀ (sp : Space) (credit : Nat) (s u : State),
    Held sp credit s u ↔
      ((∃ k, run k s = u ∧ madeIn k s ≤ credit) ∨
       (∃ j k, run k (run j s) = u ∧ sp.count (run j s) ≤ sp.bar ∧
         sp.count (run j s) + madeIn k (run j s) ≤ sp.cells)) :=
  fun _ _ _ _ => Iff.rfl

example : ∀ [Ops], ∀ (sp : Space) fuel credit s,
    (trail sp fuel credit s).getLast? = some (runSpace sp fuel credit s).state :=
  Reflect.trail_last

example : ∀ [Ops], ∀ (sp : Space) fuel credit s u,
    u ∈ trail sp fuel credit s → Held sp credit s u :=
  Reflect.trail_held

example : ∀ [Ops], ∀ (sp : Space) fuel credit s,
    Held sp credit s (runSpace sp fuel credit s).state :=
  Reflect.runSpace_ledger

example : ∀ [Ops], ∀ cells fuel s,
    ∃ k, run k s = (runIn (.ledger cells) fuel s).state ∧ madeIn k s ≤ cells :=
  Reflect.runIn_ledger

example : ∀ [Ops], ∀ (sp : Space) t fuel credit,
    (runSpace sp fuel credit (load (compile t))).state ≠ .fault :=
  Reflect.machine_never_faults_space

example : ∀ [Ops], ∀ (sp : Space) t fuel credit w,
    (runSpace sp fuel credit (load (compile t))).state = .halted w →
      ∃ o, Direct [] t o ∧ w = MP.injO o :=
  Reflect.machine_exact_space

example : ∀ [Ops], ∀ {budget : Nat} {s t : State}, runTurn budget s = t → ∃ n, run n s = t :=
  Reflect.runTurn_reach

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
#print axioms Reflect.runPriced_run
#print axioms Reflect.runPriced_reach
#print axioms Reflect.runPriced_unit
#print axioms Reflect.machine_exact_priced
#print axioms Reflect.run_cycle
#print axioms Reflect.runPriced_cycle
#print axioms Reflect.omega_cycle
#print axioms Reflect.forever_cycle
#print axioms Reflect.forever_cycle_interp
#print axioms Reflect.forever_bounded
#print axioms Reflect.runSpace_run
#print axioms Reflect.runSpace_priced
#print axioms Reflect.runSpace_full
#print axioms Reflect.runSpace_within
#print axioms Reflect.trail_last
#print axioms Reflect.trail_held
#print axioms Reflect.runSpace_ledger
#print axioms Reflect.runIn_ledger
#print axioms Reflect.machine_never_faults_space
#print axioms Reflect.machine_exact_space
#print axioms Reflect.runTurn_reach
