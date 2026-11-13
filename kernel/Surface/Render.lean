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

/-- The text an array spells, when every item is the code point of a tab, a
    line feed, or a character from the space up other than delete. Smaller
    numbers are control characters, and an array of them is not taken for text. -/
def textOf : List Data → Option (List Char)
  | [] => some []
  | .nat n :: rest =>
    if h : n.isValidChar then
      if n == 9 || n == 10 || (32 ≤ n && n != 127) then
        (textOf rest).map (Char.ofNatAux n h :: ·)
      else none
    else none
  | _ :: _ => none

/-- As `renderMOutcome`, but an array of code points is written as the text it
    spells. Every other outcome is written as `renderMOutcome` writes it, so the
    empty array is the empty text. -/
def renderMOutcomeText : MOutcome → String
  | .value (.data (.arr xs)) =>
    match textOf xs with
    | some cs => String.ofList cs
    | none => renderData (.arr xs)
  | o => renderMOutcome o

def renderSyntaxError (msg : String) : String := "syntax error: " ++ msg

end Surface
