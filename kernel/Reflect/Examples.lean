import Reflect.Correctness

namespace Reflect
variable [Ops]

abbrev identity : Term := .lam (.var 0)
abbrev deltaBody : Term := .app (.var 0) (.var 0)
abbrev delta : Term := .lam deltaBody
abbrev omega : Term := .app delta delta

/-- Builds the identity function's code `[1, 0]` with `cons` at run time and
    hands it to the interpreter. -/
def buildsAndRuns : Term :=
  .app interp (.cons (.lit (.nat 1)) (.cons (.lit (.nat 0)) (.lit (.arr []))))

theorem identity_direct :
    Direct [] (.app identity identity) (.value (.closure (.var 0) [])) :=
  .appValue .lam .lam (.varBound rfl)

theorem data_is_built :
    Direct [] (.cons (.lit (.nat 1)) (.cons (.succ (.lit (.nat 1))) (.lit (.arr []))))
      (.value (.data (.arr [.nat 1, .nat 2]))) :=
  .consArr .lit (.consArr (.succNat .lit) .lit)

theorem data_is_taken_apart :
    Direct [] (.dcase (.lit (.arr [.nat 4, .nat 5])) (.var 9) (.var 9) (.var 9)
        (.cons (.var 1) (.var 0)))
      (.value (.data (.arr [.nat 4, .nat 5]))) :=
  .caseCons .lit (.consArr (.varBound rfl) (.varBound rfl))

theorem misuse_skips_the_argument : Direct [] (.app (.lit (.nat 1)) omega) .wrong :=
  .appData .lit

/-- A quoted program is data. It is not run, even when running it would diverge. -/
theorem quoted_omega_is_data :
    Direct [] (.lit (reify omega)) (.value (.data (reify omega))) := .lit

/-- A program that is a quotation, seen through the interpreter. -/
theorem quoted_program_interpreted :
    Direct [] (level 1 (.lit (reify (.app identity identity))))
      (lift 1 (.value (.data (reify (.app identity identity))))) :=
  (tower 1 _ _).mp .lit

/-- The interpreter interpreting itself on the identity application. -/
theorem identity_two_levels :
    Direct [] (level 2 (.app identity identity)) (lift 2 (.value (.closure (.var 0) []))) :=
  (tower 2 _ _).mp identity_direct

theorem deltaBody_fuel_none (n : Nat) :
    evalFuel n [.closure deltaBody []] deltaBody = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simpa [evalFuel] using ih

theorem omega_fuel_none (n : Nat) : evalFuel n [] omega = none := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      have := deltaBody_fuel_none (n + 1)
      simpa [evalFuel] using this

theorem omega_no_direct {o : Outcome} : ¬ Direct [] omega o := by
  intro h
  obtain ⟨n, hn⟩ := evalFuel_complete h
  rw [omega_fuel_none] at hn
  cases hn

/-- The interpreter has no answer on a diverging program, at any depth. -/
theorem omega_no_interpreter : ∀ (k : Nat) (w : Outcome), ¬ Direct [] (level k omega) w := by
  intro k
  induction k with
  | zero => intro w; exact omega_no_direct
  | succ k ih =>
    intro w h
    obtain ⟨o, rfl⟩ := reflective_coverage (level k omega) w h
    exact ih o ((reflective (level k omega) o).mpr h)

set_option maxRecDepth 100000 in
/-- A program that builds another program's code and runs it. -/
theorem builds_and_runs_direct :
    Direct [] buildsAndRuns
      (.value (.data (reifyOutcome (.value (.closure (.var 0) []))))) :=
  evalFuel_sound (n := 100) (by with_unfolding_all rfl)

/-- The same program, seen through the interpreter interpreting itself. -/
theorem builds_and_runs_two_levels :
    Direct [] (level 2 buildsAndRuns)
      (lift 2 (.value (.data (reifyOutcome (.value (.closure (.var 0) [])))))) :=
  (tower 2 _ _).mp builds_and_runs_direct

end Reflect
