import Reflect.RunUntil
import Reflect.MachineProof

namespace Reflect
variable [Ops]

theorem run_fault : ∀ n, run n .fault = .fault := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, step] using ih

/-- Stopping early changes nothing: a budget larger than needed costs no time. -/
theorem runUntil_eq : ∀ n s, runUntil n s = run n s := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    cases s with
    | halted o => rw [run_halted]; rfl
    | fault => rw [run_fault]; rfl
    | running c e stk frs => exact ih _

/-- A priced run is a prefix of `run`: it takes some number of steps, no more
    than the fuel, and stops at the state `run` reaches after them. The
    charge decides only how far it gets, never which step is taken. -/
theorem runPriced_run : ∀ fuel s, ∃ n, n ≤ fuel ∧ runPriced fuel s = run n s := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro s
    cases fuel with
    | zero => exact ⟨0, Nat.le_refl _, by rw [runPriced]; rfl⟩
    | succ fuel =>
      cases s with
      | halted o => exact ⟨0, Nat.zero_le _, by rw [runPriced]; rfl⟩
      | fault => exact ⟨0, Nat.zero_le _, by rw [runPriced]; rfl⟩
      | running c e stk frs =>
        rw [runPriced]
        case x_2 => intro o h'; cases h'
        case x_3 => intro h'; cases h'
        split
        · obtain ⟨m, hm, h⟩ := ih fuel (by omega) (step (.running c e stk frs))
          exact ⟨m + 1, by omega, h⟩
        · split
          · rename_i c' _ hc
            obtain ⟨m, hm, h⟩ := ih (fuel - c') (by omega) (step (.running c e stk frs))
            exact ⟨m + 1, by omega, h⟩
          · exact ⟨0, Nat.zero_le _, rfl⟩

/-- Where a priced run stops, `run` gets to. Every theorem about what a run
    reaches holds of what a priced run reaches. -/
theorem runPriced_reach {fuel : Nat} {s t : State} (h : runPriced fuel s = t) :
    ∃ n, run n s = t := by
  obtain ⟨n, _, hn⟩ := runPriced_run fuel s
  exact ⟨n, hn ▸ h⟩

/-- With a table that charges one for every operation, a priced run is
    `runUntil`: the budget counts steps. -/
theorem runPriced_unit (h : ∀ n d, Ops.cost n d = 1) : ∀ fuel s, runPriced fuel s = runUntil fuel s := by
  have hc : ∀ s, stepCost s = 1 := by
    intro s; unfold stepCost; split <;> first | rfl | exact h _ _
  intro fuel
  induction fuel with
  | zero => intro s; rw [runPriced]; rfl
  | succ fuel ih =>
    intro s
    cases s with
    | halted o => rw [runPriced]; rfl
    | fault => rw [runPriced]; rfl
    | running c e stk frs =>
      rw [runPriced, runUntil]
      case x_2 => intro o h'; cases h'
      case x_3 => intro h'; cases h'
      rw [hc]
      simp only [Nat.zero_add, Nat.le_add_left, ite_true, Nat.sub_zero]
      exact ih _

end Reflect
