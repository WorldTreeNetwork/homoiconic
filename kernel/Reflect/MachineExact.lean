import Reflect.MachineProof
import Reflect.Examples

namespace Reflect
open MP

/-- A source outcome as the machine outcome that carries its compiled code. -/
def MP.injO : Outcome → MOutcome
  | .value v => .value (injV v)
  | .unbound i => .unbound i
  | .wrong => .wrong

/-- A halted machine holds exactly the compiled form of a source outcome. This
    is stronger than reading the outcome back: a returned closure's code is the
    compiled body, guards included, so it behaves as the body if run further. -/
theorem machine_exact : ∀ t n w,
    run n (load (compile t)) = .halted w → ∃ o, Direct [] t o ∧ w = MP.injO o := by
  intro t n w h
  rcases rev n t [] .done [] [] w h with ⟨e, he, hd⟩ | ⟨m, v, hd, hm⟩
  · cases he with
    | unbound i => exact ⟨_, hd, rfl⟩
    | wrong => exact ⟨_, hd, rfl⟩
  · have h1 : run (m + 1) (load (compile t)) = .halted (.value (injV v)) := by
      have : run m (load (compile t)) = .running .done [] [injV v] [] := hm
      rw [run_add, this]; rfl
    exact ⟨_, hd, (halted_unique h1 h).symm⟩

/-- A term with no derivation never halts. -/
theorem machine_never_halts : ∀ t, (∀ o, ¬ Direct [] t o) →
    ∀ n w, run n (load (compile t)) ≠ .halted w := by
  intro t hno n w h
  obtain ⟨o, hd, _⟩ := machine_exact t n w h
  exact hno o hd

theorem omega_never_halts (n : Nat) (w : MOutcome) :
    run n (load (compile omega)) ≠ .halted w :=
  machine_never_halts _ (fun _ => omega_no_direct) n w

theorem identity_halts :
    run 7 (load (compile (.app identity identity))) =
      .halted (MP.injO (.value (.closure (.var 0) []))) := rfl

end Reflect
