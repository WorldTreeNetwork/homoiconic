import Reflect.RunUntil
import Reflect.MachineProof

namespace Reflect

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

end Reflect
