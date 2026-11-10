import Reflect.Machine

/-!
The renderer: outcomes and machine states as plain text. Data renders in the
form the reader accepts, so printed data can be pasted back as a literal.
Tested against examples; not proved.
-/
namespace Surface
open Reflect

mutual
  /-- Numbers in decimal; arrays in brackets, items separated by a comma and a space. -/
  def renderData : Data → String
    | .nat n => toString n
    | .arr xs => "[" ++ ", ".intercalate (renderItems xs) ++ "]"

  def renderItems : List Data → List String
    | [] => []
    | x :: xs => renderData x :: renderItems xs
end

/-- A source outcome as text. -/
def render : Outcome → String
  | .value (.data d) => renderData d
  | .value (.closure _ _) => "<function>"
  | .unbound i => s!"error: unbound {i}"
  | .wrong => "error: wrong"

/-- A machine outcome as text; the same text as `render` of the same outcome. -/
def renderMOutcome : MOutcome → String
  | .value (.data d) => renderData d
  | .value (.closure _ _) => "<function>"
  | .unbound i => s!"error: unbound {i}"
  | .wrong => "error: wrong"

/-- The machine's state after running with `budget` steps. A state that is still
    running has no result. `fault` is not an outcome; a compiled program that
    halts never reaches it, and it renders as an internal error. -/
def renderState (budget : Nat) : State → String
  | .halted o => renderMOutcome o
  | .running .. => s!"no result within {budget} steps"
  | .fault => "error: machine fault"

def renderSyntaxError (msg : String) : String := "syntax error: " ++ msg

end Surface
