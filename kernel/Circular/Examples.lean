import Circular.Correctness

namespace Circular

abbrev identity : Term := .lam (.var 0)
abbrev identityApplication : Term := .app identity identity
abbrev deltaBody : Term := .app (.var 0) (.var 0)
abbrev delta : Term := .lam deltaBody
abbrev deltaValue : Value := .closure deltaBody []
abbrev omega : Term := .app delta delta

theorem omega_pure : Pure omega := .app (.lam (.app (.var 0) (.var 0)))
    (.lam (.app (.var 0) (.var 0)))

theorem deltaBody_fuel_none (n : Nat) : evalFuel n [deltaValue] deltaBody = none := by
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
    | succ n => simpa [evalFuel] using deltaBody_fuel_none (n + 1)

theorem omega_no_direct : ¬ Direct [] omega o := by
  intro h
  obtain ⟨n, hn⟩ := evalFuel_complete h
  rw [omega_fuel_none] at hn
  contradiction

/-- Coverage rules out every interpreter outcome on omega, not just outcomes
    selected in advance or results observed at a bounded amount of fuel. -/
theorem omega_interpreter_no_direct :
    ¬ Direct [] (.app interpreterBody (encode omega omega_pure)) w := by
  intro h
  obtain ⟨o, hr⟩ := coverage omega omega_pure w h
  have hd := (metacircular omega omega_pure o).mpr ⟨w, h, hr⟩
  exact omega_no_direct hd

theorem identity_direct : Direct [] identityApplication (.value (.closure (.var 0) [])) :=
  .appValue .lam .lam (.varBound rfl)

theorem open_variable_direct : Direct [] (.var 0) (.unbound 0) := .varUnbound rfl

theorem unbound_function_skips_omega : Direct [] (.app (.var 0) omega) (.unbound 0) :=
  .appUnbound (.varUnbound rfl)

theorem open_lambda_direct : Direct [] (.lam (.var 1)) (.value (.closure (.var 1) [])) := .lam

theorem identity_fuel : evalFuel 3 [] identityApplication = some (.value (.closure (.var 0) [])) := rfl
theorem open_variable_fuel : evalFuel 1 [] (.var 0) = some (.unbound 0) := rfl
theorem skip_omega_fuel : evalFuel 2 [] (.app (.var 0) omega) = some (.unbound 0) := rfl
theorem open_lambda_fuel : evalFuel 1 [] (.lam (.var 1)) = some (.value (.closure (.var 1) [])) := rfl

theorem quoted_input_excluded : ¬ Pure (.quote (.var 0)) := not_pure_quote
theorem quote_is_data : Eval [] (.quote (.var 0)) (.code (.var 0)) := .quote

section ExecutionChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

-- These are concrete executable witnesses, not an assumption of general
-- interpreter correctness. Their equations are checked by kernel reduction.
def openVariableInterpreted : Outcome :=
  (evalFuel 100 [] (interpreterApplication (.var 0) (.var 0))).getD (.unbound 0)

theorem open_variable_interpreter_fuel :
    evalFuel 100 [] (interpreterApplication (.var 0) (.var 0)) = some openVariableInterpreted := by
  with_unfolding_all rfl

theorem open_variable_interpreter_represents : Represents (.unbound 0) openVariableInterpreted := by
  cbv

def identityInterpreted : Outcome :=
  (evalFuel 100 [] (interpreterApplication identityApplication
    (.app (.lam (.var 0)) (.lam (.var 0))))).getD (.unbound 0)

theorem identity_interpreter_fuel :
    evalFuel 100 [] (interpreterApplication identityApplication
      (.app (.lam (.var 0)) (.lam (.var 0)))) = some identityInterpreted := by
  with_unfolding_all rfl

theorem identity_interpreter_represents :
    Represents (.value (.closure (.var 0) [])) identityInterpreted := by
  cbv

def skipOmegaInterpreted : Outcome :=
  (evalFuel 100 [] (interpreterApplication (.app (.var 0) omega)
    (.app (.var 0) omega_pure))).getD (.unbound 0)

theorem skip_omega_interpreter_fuel :
    evalFuel 100 [] (interpreterApplication (.app (.var 0) omega)
      (.app (.var 0) omega_pure)) = some skipOmegaInterpreted := by
  with_unfolding_all rfl

theorem skip_omega_interpreter_represents : Represents (.unbound 0) skipOmegaInterpreted := by
  cbv

def openLambdaInterpreted : Outcome :=
  (evalFuel 100 [] (interpreterApplication (.lam (.var 1)) (.lam (.var 1)))).getD (.unbound 0)

theorem open_lambda_interpreter_fuel :
    evalFuel 100 [] (interpreterApplication (.lam (.var 1)) (.lam (.var 1))) = some openLambdaInterpreted := by
  with_unfolding_all rfl

theorem open_lambda_interpreter_represents :
    Represents (.value (.closure (.var 1) [])) openLambdaInterpreted := by
  cbv

theorem open_variable_interpreter :
    Direct [] (interpreterApplication (.var 0) (.var 0)) openVariableInterpreted :=
  evalFuel_sound open_variable_interpreter_fuel

theorem identity_interpreter :
    Direct [] (interpreterApplication identityApplication
      (.app (.lam (.var 0)) (.lam (.var 0)))) identityInterpreted :=
  evalFuel_sound identity_interpreter_fuel

theorem skip_omega_interpreter :
    Direct [] (interpreterApplication (.app (.var 0) omega)
      (.app (.var 0) omega_pure)) skipOmegaInterpreted :=
  evalFuel_sound skip_omega_interpreter_fuel

theorem open_lambda_interpreter :
    Direct [] (interpreterApplication (.lam (.var 1)) (.lam (.var 1))) openLambdaInterpreted :=
  evalFuel_sound open_lambda_interpreter_fuel

end ExecutionChecks
end Circular

namespace Circular

theorem interpreter_unbound_is_encoded : openVariableInterpreted ≠ .unbound 0 := by
  intro h
  have hr := open_variable_interpreter_represents
  rw [h] at hr
  exact hr

set_option maxRecDepth 100000 in
theorem interpreter_identity_is_encoded : identityInterpreted ≠ .value (.closure (.var 0) []) := by
  intro h
  have hr := identity_interpreter_represents
  rw [h] at hr
  cbv at hr
  contradiction

end Circular
