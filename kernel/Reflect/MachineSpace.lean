import Reflect.Examples
import Reflect.RunUntilProof
import Reflect.Arith

/-!
What the step budget does and does not bound in memory.

`depth_bound` bounds the value stack plus the pending frames by the steps
taken. A block entered in tail position pushes no frame (`push`), so a loop
whose calls are all in tail position keeps no frame per call. The theorems
here show it for two such loops: from some step on, the machine repeats a
state exactly, so a run of any length holds one of finitely many states. Its
memory does not grow with the budget.

Nothing here bounds memory in general. A recursion whose calls wait on each
other keeps a frame per pending call (as `depth_bound` allows), and a program
that builds data keeps the data. Both grow with the steps taken.
-/

namespace Reflect
variable [Ops]

/-- A run that comes back to a state it held repeats from there: after any
    number of steps it is in one of the first `a + p` states. -/
theorem run_cycle {s : State} {a p : Nat} (hp : 0 < p) (h : run (a + p) s = run a s) :
    ∀ n, ∃ j, j < a + p ∧ run n s = run j s := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n < a + p
    · exact ⟨n, hn, rfl⟩
    · have e1 : run n s = run (n - (a + p)) (run (a + p) s) := by
        rw [← run_add]; congr 1; omega
      have e2 : run (n - (a + p)) (run a s) = run (n - p) s := by
        rw [← run_add]; congr 1; omega
      obtain ⟨j, hj, hr⟩ := ih (n - p) (by omega)
      exact ⟨j, hj, by rw [e1, h, e2, hr]⟩

/-- The same for a priced run: whatever the fuel, it stops in one of the
    first `a + p` states. -/
theorem runPriced_cycle {s : State} {a p : Nat} (hp : 0 < p) (h : run (a + p) s = run a s) :
    ∀ fuel, ∃ j, j < a + p ∧ runPriced fuel s = run j s := by
  intro fuel
  obtain ⟨n, _, hn⟩ := runPriced_run fuel s
  obtain ⟨j, hj, hr⟩ := run_cycle hp h n
  exact ⟨j, hj, hn.trans hr⟩

/-- `examples/forever.hom` (`def loop x = loop x`, then `loop 0`) as the term it
    reads to; `Surface/Check.lean` checks that it does. -/
def loopForever : Term :=
  .app (.lam (.app (.var 0) (.lit (.nat 0))))
    (.app (.lam (.app (.lam (.app (.var 1) (.lam (.app (.app (.var 1) (.var 1)) (.var 0)))))
                      (.lam (.app (.var 1) (.lam (.app (.app (.var 1) (.var 1)) (.var 0)))))))
          (.lam (.lam (.app (.var 1) (.var 0)))))

/-- `omega` calls itself in tail position: after 4 steps the machine is back in
    the state it held at step 4. With a frame per call it never would be. -/
theorem omega_cycle : run (4 + 4) (load (compile omega)) = run 4 (load (compile omega)) := rfl

/-- `forever.hom` on the machine repeats every 17 steps from step 21. -/
theorem forever_cycle :
    run (21 + 17) (load (compile loopForever)) = run 21 (load (compile loopForever)) := by
  rfl

end Reflect

namespace Reflect

set_option maxRecDepth 100000 in
/-- And through one interpreter, every 832 steps from step 853: the
    interpreter's own calls on the loop are in tail position too. Stated for
    the host's table (`arithOps`); the loop calls no operation. -/
theorem forever_cycle_interp :
    run (853 + 832) (load (compile (level 1 loopForever))) =
      run 853 (load (compile (level 1 loopForever))) := by
  rfl

/-- Whatever the budget, a priced run of `forever.hom` stops in one of 38
    states, and through one interpreter in one of 1685. -/
theorem forever_bounded (fuel : Nat) :
    (∃ j, j < 38 ∧ runPriced fuel (load (compile loopForever)) =
      run j (load (compile loopForever))) ∧
    (∃ j, j < 1685 ∧ runPriced fuel (load (compile (level 1 loopForever))) =
      run j (load (compile (level 1 loopForever)))) :=
  ⟨runPriced_cycle (by decide) forever_cycle fuel,
    runPriced_cycle (by decide) forever_cycle_interp fuel⟩

end Reflect
