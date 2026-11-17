import Reflect.Machine

/-!
The renderer: outcomes and machine states as plain text. Data renders in the
form the reader accepts, so printed data can be pasted back as a literal.
Tested against examples; not proved.
-/
namespace Surface
open Reflect

/-- A text between double quotes, as the reader takes a string literal: a line
    feed, a tab, a backslash and a double quote are written `\n`, `\t`, `\\`
    and `\"`, and every other character as itself. -/
def renderText (t : List Char) : String :=
  String.ofList ('"' :: t.foldr (fun c acc =>
    if c == '\n' then '\\' :: 'n' :: acc
    else if c == '\t' then '\\' :: 't' :: acc
    else if c == '\\' then '\\' :: '\\' :: acc
    else if c == '"' then '\\' :: '"' :: acc
    else c :: acc) ['"'])

mutual
  /-- Numbers in decimal; arrays in brackets, items separated by a comma and a
      space; a text in quotes with the reader's escapes; a name as `#` and its
      number, which the reader does not read. -/
  def renderData : Data → String
    | .nat n => toString n
    | .name n => "#" ++ toString n
    | .text t => renderText t
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

/-- As `renderMOutcome`, but a result that is a text is written raw: its
    characters, with no quotes and no escapes. Every other outcome is written
    as `renderMOutcome` writes it; an array of code points is not a text. -/
def renderMOutcomeText : MOutcome → String
  | .value (.data (.text t)) => String.ofList t
  | o => renderMOutcome o

def renderSyntaxError (msg : String) : String := "syntax error: " ++ msg

end Surface
