import Reflect.Machine

/-!
The renderer: outcomes and machine states as plain text. Data renders in the
form the reader accepts, so printed data can be pasted back as a literal.
Tested against examples; not proved, but for numbers: a number is written by
`decimalGo`, proved to write what `Nat.repr` writes (`decimal_eq_go`).
-/
namespace Surface
open Reflect

/-- The last `m` decimal digits of `r`, with leading zeros. -/
def padDigits : Nat → Nat → List Char
  | 0, _ => []
  | m + 1, r => padDigits m (r / 10) ++ [Nat.digitChar (r % 10)]

theorem toDigits_split (m : Nat) : ∀ q r, 0 < q → r < 10 ^ m →
    Nat.toDigits 10 (q * 10 ^ m + r) = Nat.toDigits 10 q ++ padDigits m r := by
  induction m with
  | zero => intro q r _ hr; simp at hr; subst hr; simp [padDigits]
  | succ m ih =>
    intro q r hq hr
    have hp : 10 ^ (m + 1) = 10 ^ m * 10 := by rw [Nat.pow_succ]
    have h10 : 10 ≤ q * 10 ^ (m + 1) + r := by
      have : 1 ≤ 10 ^ m := Nat.pow_pos (by omega)
      rw [hp, ← Nat.mul_assoc]
      have := Nat.mul_le_mul hq this
      omega
    rw [Nat.toDigits_of_base_le (by omega) h10]
    have e1 : (q * 10 ^ (m + 1) + r) / 10 = q * 10 ^ m + r / 10 := by
      rw [hp, ← Nat.mul_assoc]; omega
    have e2 : (q * 10 ^ (m + 1) + r) % 10 = r % 10 := by
      rw [hp, ← Nat.mul_assoc]; omega
    have hr' : r / 10 < 10 ^ m := by rw [hp] at hr; omega
    rw [e1, e2, ih q (r / 10) hq hr', padDigits, List.append_assoc]

theorem padDigits_split (a : Nat) : ∀ b n,
    padDigits (a + b) n = padDigits a (n / 10 ^ b) ++ padDigits b (n % 10 ^ b) := by
  intro b
  induction b with
  | zero => intro n; simp [padDigits]
  | succ b ih =>
    intro n
    rw [← Nat.add_assoc, padDigits, ih, padDigits, List.append_assoc]
    have e1 : n / 10 / 10 ^ b = n / 10 ^ (b + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    have e2 : n / 10 % 10 ^ b = n % 10 ^ (b + 1) / 10 := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    have e3 : n % 10 = n % 10 ^ (b + 1) % 10 := by
      rw [Nat.pow_succ, Nat.mod_mul_left_mod]
    rw [e1, e2, ← e3]

/-- `acc` and then the last `w` digits of `r`, with leading zeros. The digits
    are split in halves by a power of ten, so the work is that of a few
    multiplications of the whole number, not one division for each digit. -/
def padInto (acc : String) (w r : Nat) : String :=
  if w ≤ 19 then acc ++ String.ofList (padDigits w r)
  else
    let p := 10 ^ (w / 2)
    padInto (padInto acc (w - w / 2) (r / p)) (w / 2) (r % p)
termination_by w
decreasing_by all_goals omega

theorem padInto_eq (w : Nat) : ∀ acc r, padInto acc w r = acc ++ String.ofList (padDigits w r) := by
  induction w using Nat.strongRecOn with
  | _ w ih =>
    intro acc r
    rw [padInto]
    split
    · rfl
    · rw [ih _ (by omega), ih _ (by omega), String.append_assoc, ← String.ofList_append,
        ← padDigits_split, Nat.sub_add_cancel (by omega)]

/-- A number in decimal, as `Nat.repr` writes it (`decimalGo_eq`). Below
    10^19 it is `Nat.repr`; above, the number is split by a power of ten into
    its high digits and about half of its low ones, so a number of `n` digits
    is written in the time of a few multiplications of `n` digits, where
    `Nat.repr` divides by ten once for each digit (`homoiconic-q59.64`). -/
def decimalGo (n : Nat) : String :=
  if n < 10 ^ 19 then n.repr
  else
    let m := max 1 (Nat.log2 n * 3 / 20)
    let p := 10 ^ m
    if n / p = 0 then n.repr
    else padInto (decimalGo (n / p)) m (n % p)
termination_by n
decreasing_by
  exact Nat.div_lt_self (by omega) (Nat.one_lt_pow (by omega) (by omega))

theorem decimalGo_eq (n : Nat) : decimalGo n = n.repr := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decimalGo]
    split
    · rfl
    · simp only
      split
      · rfl
      · rename_i h1 h2
        have hm : 0 < 10 ^ max 1 (Nat.log2 n * 3 / 20) := Nat.pow_pos (by omega)
        have hq : 0 < n / 10 ^ max 1 (Nat.log2 n * 3 / 20) := Nat.pos_of_ne_zero h2
        rw [padInto_eq, ih _ (Nat.div_lt_self (by omega) (Nat.one_lt_pow (by omega) (by omega))),
          Nat.repr_eq_ofList_toDigits, Nat.repr_eq_ofList_toDigits, ← String.ofList_append,
          ← toDigits_split _ _ _ hq (Nat.mod_lt _ hm), Nat.mul_comm, Nat.div_add_mod]

/-- A number in decimal: `Nat.repr`, which is what runs nowhere; the compiler
    runs `decimalGo` (`decimal_eq_go`). -/
def decimal (n : Nat) : String := n.repr

@[csimp] theorem decimal_eq_go : @decimal = @decimalGo := by
  funext n; rw [decimal, decimalGo_eq]

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
