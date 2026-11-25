import Reflect.Machine
import Surface.Read

/-!
The renderer: outcomes and machine states as plain text. Data renders in the
form the reader accepts, so printed data can be pasted back as a literal.
Tested against examples; not proved, but for numbers: a number is written by
`decimalGo`, proved to write what `Nat.repr` writes (`decimal_eq_go`).
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
    | .nat n => decimal n
    | .name n => "#" ++ decimal n
    | .text t => renderText t
    | .arr xs => "[" ++ ", ".intercalate (renderItems xs) ++ "]"

  /-- One recursive call per item overflowed the stack on a long array.
      The walk is a tail call; `renderData` on an item is smaller than the list. -/
  def renderItems (xs : List Data) : List String :=
    go xs []
  where
    go : List Data → List String → List String
      | [], acc => acc.reverse
      | y :: yt, acc =>
        let s := renderData y
        go yt (s :: acc)
end

/-- What is still to print in `renderGo`. -/
inductive PAct where
  | data : Data → PAct
  /-- The items after an array's first, each after a comma and a space. -/
  | items : List Data → PAct
  | close : PAct

mutual
  /-- How many steps `renderGo` takes on a data value. -/
  def stepsData : Data → Nat
    | .arr (x :: xs) => stepsData x + stepsItems xs + 2
    | _ => 1
  def stepsItems : List Data → Nat
    | [] => 1
    | y :: ys => stepsData y + stepsItems ys + 1
end

def PAct.steps : PAct → Nat
  | .data d => stepsData d
  | .items ys => stepsItems ys
  | .close => 1

def PAct.total : List PAct → Nat
  | [] => 0
  | a :: as => a.steps + PAct.total as

/-- `acc` and then the text of each thing in the list. What is still to print
    waits in the list, so nothing here recurses on how deep the data is
    nested. -/
def renderGo (acc : String) : List PAct → String
  | [] => acc
  | .close :: as => renderGo (acc ++ "]") as
  | .items [] :: as => renderGo acc as
  | .items (y :: ys) :: as => renderGo (acc ++ ", ") (.data y :: .items ys :: as)
  | .data (.nat n) :: as => renderGo (acc ++ decimal n) as
  | .data (.name n) :: as => renderGo (acc ++ ("#" ++ decimal n)) as
  | .data (.text t) :: as => renderGo (acc ++ renderText t) as
  | .data (.arr []) :: as => renderGo (acc ++ "[]") as
  | .data (.arr (x :: xs)) :: as => renderGo (acc ++ "[") (.data x :: .items xs :: .close :: as)
termination_by as => PAct.total as
decreasing_by all_goals simp_wf; all_goals (simp only [PAct.total, PAct.steps, stepsData, stepsItems]; omega)

theorem renderItems_eq (xs : List Data) : renderItems xs = xs.map renderData := by
  suffices h : ∀ acc, renderItems.go xs acc = acc.reverse ++ xs.map renderData by
    simp [renderItems, h]
  induction xs with
  | nil => intro acc; simp [renderItems.go]
  | cons x xs ih => intro acc; simp [renderItems.go, ih]

theorem intercalate_cons (x : String) (xs : List String) :
    ", ".intercalate (x :: xs) = x ++ String.join (xs.map (", " ++ ·)) := by
  induction xs generalizing x with
  | nil => simp only [List.map_nil, String.join_nil, String.append_empty]; rfl
  | cons y ys ih =>
    rw [String.intercalate_cons_cons, ih]; simp [String.join_cons, String.append_assoc]


mutual
  theorem renderGo_data (d : Data) (acc : String) (as : List PAct) :
      renderGo acc (.data d :: as) = renderGo (acc ++ renderData d) as := by
    match d with
    | .nat n => rw [renderGo]; simp [renderData]
    | .name n => rw [renderGo]; simp [renderData]
    | .text t => rw [renderGo]; simp [renderData]
    | .arr [] => rw [renderGo]; simp [renderData, renderItems_eq, String.intercalate]
    | .arr (x :: xs) =>
      rw [renderGo, renderGo_data x, renderGo_items xs, renderGo]
      simp only [renderData, renderItems_eq, List.map_cons, intercalate_cons, String.append_assoc, List.map_map, Function.comp_def]
  theorem renderGo_items (ys : List Data) (acc : String) (as : List PAct) :
      renderGo acc (.items ys :: as) =
        renderGo (acc ++ String.join (ys.map (fun y => ", " ++ renderData y))) as := by
    match ys with
    | [] => rw [renderGo]; simp
    | y :: ys =>
      rw [renderGo, renderGo_data y, renderGo_items ys]
      simp [String.join_cons, String.append_assoc]
end

/-- `renderData`, as a walk; the compiler runs it (`renderData_eq_walk`), so
    data nested a million deep prints in constant native stack
    (`homoiconic-q59.72`). -/
def renderWalk (d : Data) : String := renderGo "" [.data d]

@[csimp] theorem renderData_eq_walk : @renderData = @renderWalk := by
  funext d; simp only [renderWalk, renderGo_data]; rw [renderGo]; simp

/-- A source outcome as text. -/
def render : Outcome → String
  | .value (.data d) => renderData d
  | .value (.closure _ _) => "<function>"
  | .unbound i => "error: unbound " ++ decimal i
  | .wrong => "error: wrong"

/-- A machine outcome as text; the same text as `render` of the same outcome. -/
def renderMOutcome : MOutcome → String
  | .value (.data d) => renderData d
  | .value (.closure _ _) => "<function>"
  | .unbound i => "error: unbound " ++ decimal i
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

/-- The line for a run that passed its space, or whose answer is too large to
    write within it. -/
def renderSpace (cells : Nat) : String := s!"no result within {cells} cells"

end Surface
