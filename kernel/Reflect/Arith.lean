import Reflect.Semantics

namespace Reflect

/-- The text an array of code points spells, or `none` if an item is not a
    number or is not a Unicode scalar value. -/
def scalars? (xs : List Data) : Option (List Char) :=
  (xs.mapM fun | Data.nat n => some n | _ => none).bind Text.ofCodes?

/-- The first set of operations: exact arithmetic and comparison on natural
    numbers of any size. An operation takes its operands as one array. A number
    that is not an operation, or operands of the wrong shape, give `[]`. Of the
    operations here only `codes` gives `[]` otherwise, for the empty text and
    for `[]`.

    Division by zero is 0 and the remainder by zero is the dividend. Subtraction
    stops at 0. Comparison answers 1 or 0. `equal` compares any two data values,
    and tells a text from an array and a name from a number. It answers 1
    exactly when they are equal (`Data.same_iff`), by a walk that does not
    recurse on how deep they are nested (`homoiconic-q59.72`).

    `text` (7) and `codes` (8) take their operand itself, not an array of
    operands. They go between a text and the array of its code points, and each
    leaves its own kind as it is. An array with an item that is not the number
    of a Unicode scalar value is neither, and gives `[]`. -/
def arith : Nat → Data → Data
  | 0, .arr [.nat a, .nat b] => .nat (a + b)
  | 1, .arr [.nat a, .nat b] => .nat (a - b)
  | 2, .arr [.nat a, .nat b] => .nat (a * b)
  | 3, .arr [.nat a, .nat b] => .nat (a / b)
  | 4, .arr [.nat a, .nat b] => .nat (a % b)
  | 5, .arr [x, y] => .nat (if Data.same x y then 1 else 0)
  | 6, .arr [.nat a, .nat b] => .nat (if a < b then 1 else 0)
  | 7, .text t => .text t
  | 7, .arr xs =>
      match scalars? xs with
      | some t => .text t
      | none => .arr []
  | 8, .text t => .arr ((Text.codes t).map .nat)
  | 8, .arr xs =>
      match scalars? xs with
      | some _ => .arr xs
      | none => .arr []
  | _, _ => .arr []

/-- The names the surface syntax gives these operations: the name, the
    operation's number, and how many arguments the named function takes. With
    two it hands the operation the array of both; with one, the argument itself. -/
def arithNames : List (String × Nat × Nat) :=
  [("add", 0, 2), ("sub", 1, 2), ("mul", 2, 2), ("div", 3, 2), ("mod", 4, 2), ("equal", 5, 2),
   ("less", 6, 2), ("text", 7, 1), ("codes", 8, 1)]

/-- Bits of a number. Zero costs one, the same as one. -/
def bits (n : Nat) : Nat := Nat.log2 n + 1

/-- 64-bit words of a number: one below 2^64. -/
def natWords (n : Nat) : Nat := Nat.log2 n / 64 + 1

mutual
  /-- What comparing a value costs at most: a number or a name its words, a
      text one more than its length, an array one more than its items. It is
      the value counted as a tree, so a value built by doubling weighs 2^k
      after k steps, and so many pairs is what `Data.same` may compare. -/
  def Data.weight : Data → Nat
    | .nat n => natWords n
    | .name n => natWords n
    | .text cs => cs.length + 1
    | .arr xs => Data.weightList xs + 1
  def Data.weightList : List Data → Nat
    | [] => 0
    | x :: xs => x.weight + Data.weightList xs
end

/-- The weight of every list in a list of work. -/
def weightWork : List (List Data) → Nat
  | [] => 0
  | xs :: ws => Data.weightList xs + weightWork ws

/-- Whether a list has at most `k` items, looking at no more than `k + 1`. -/
def lenAtMost {α : Type} : Nat → List α → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | k + 1, _ :: xs => lenAtMost k xs

theorem lenAtMost_iff {α : Type} : ∀ (k : Nat) (xs : List α), lenAtMost k xs = true ↔ xs.length ≤ k
  | _, [] => by simp [lenAtMost]
  | 0, _ :: _ => by simp [lenAtMost]
  | k + 1, _ :: xs => by simp [lenAtMost, lenAtMost_iff k xs]

/-- What is left of `left` once the weight of the work is taken from it, or
    `none` when the weight is more. Lists still to weigh wait in the work, so
    nothing here recurses on how deep the data is nested, and no more of the
    data is looked at than `left` pays for (`weighGo_eq`). -/
def weighGo : Nat → List (List Data) → Option Nat
  | left, [] => some left
  | left, [] :: ws => weighGo left ws
  | left, (.arr xs :: ds) :: ws =>
      if 1 ≤ left then weighGo (left - 1) (xs :: ds :: ws) else none
  | left, (.text cs :: ds) :: ws =>
      if 1 ≤ left ∧ lenAtMost (left - 1) cs = true then
        weighGo (left - (cs.length + 1)) (ds :: ws)
      else none
  | left, (.nat n :: ds) :: ws =>
      if natWords n ≤ left then weighGo (left - natWords n) (ds :: ws) else none
  | left, (.name n :: ds) :: ws =>
      if natWords n ≤ left then weighGo (left - natWords n) (ds :: ws) else none
termination_by _ ws => 2 * weightWork ws + ws.length
decreasing_by
  all_goals simp only [weightWork, Data.weightList, Data.weight, natWords, List.length_cons]
  all_goals omega

theorem weightWork_cons (d : Data) (ds : List Data) (ws : List (List Data)) :
    weightWork ((d :: ds) :: ws) = d.weight + weightWork (ds :: ws) := by
  simp only [weightWork, Data.weightList]; omega

/-- The step `weighGo_eq` takes for each case: `left` less `w` goes on to the
    rest of the work. -/
private theorem weigh_step (left w rest : Nat) (h : w ≤ left) :
    (if rest ≤ left - w then some (left - w - rest) else none) =
      (if w + rest ≤ left then some (left - (w + rest)) else none) := by
  by_cases h2 : rest ≤ left - w
  · rw [ite_eq_left h2, ite_eq_left (by omega)]; congr 1; omega
  · rw [ite_eq_right h2, ite_eq_right (by omega)]

private theorem weigh_none (left w rest : Nat) (h : ¬ w ≤ left) :
    (none : Option Nat) = (if w + rest ≤ left then some (left - (w + rest)) else none) := by
  rw [ite_eq_right (by omega)]

theorem weighGo_eq (left : Nat) (ws : List (List Data)) :
    weighGo left ws = if weightWork ws ≤ left then some (left - weightWork ws) else none := by
  induction left, ws using weighGo.induct with
  | case1 left => simp [weighGo, weightWork]
  | case2 left ws ih => rw [weighGo, ih]; simp [weightWork, Data.weightList]
  | case3 left xs ds ws h ih =>
    rw [weighGo, ite_eq_left h, ih, weightWork_cons]
    have e : weightWork (xs :: ds :: ws) = Data.weightList xs + weightWork (ds :: ws) := rfl
    have e2 : (Data.arr xs).weight = 1 + Data.weightList xs := by simp [Data.weight]; omega
    rw [e, e2, weigh_step _ _ _ h]; congr 2 <;> omega
  | case4 left xs ds ws h =>
    rw [weighGo, ite_eq_right h, weightWork_cons]; exact weigh_none _ _ _ (by simp [Data.weight]; omega)
  | case5 left cs ds ws h ih =>
    have h1 := (lenAtMost_iff _ _).1 h.2
    rw [weighGo, ite_eq_left h, ih, weightWork_cons]
    exact weigh_step _ _ _ (show cs.length + 1 ≤ left by omega)
  | case6 left cs ds ws h =>
    rw [weighGo, ite_eq_right h, weightWork_cons]
    refine weigh_none _ _ _ ?_
    show ¬ (cs.length + 1 ≤ left); intro h2
    exact h ⟨by omega, (lenAtMost_iff _ _).2 (by omega)⟩
  | case7 left n ds ws h ih =>
    rw [weighGo, ite_eq_left h, ih, weightWork_cons]; exact weigh_step _ _ _ h
  | case8 left n ds ws h =>
    rw [weighGo, ite_eq_right h, weightWork_cons]; exact weigh_none _ _ _ h
  | case9 left n ds ws h ih =>
    rw [weighGo, ite_eq_left h, ih, weightWork_cons]; exact weigh_step _ _ _ h
  | case10 left n ds ws h =>
    rw [weighGo, ite_eq_right h, weightWork_cons]; exact weigh_none _ _ _ h

/-- The weight of `d`, or `k + 1` when it is more than `k`, found by looking
    at no more of `d` than `k` pays for. -/
def weighWithin (k : Nat) (d : Data) : Nat :=
  match weighGo k [[d]] with
  | some r => k - r
  | none => k + 1

theorem weighWithin_eq (k : Nat) (d : Data) : weighWithin k d = min d.weight (k + 1) := by
  unfold weighWithin
  have e : weightWork [[d]] = d.weight := by simp [weightWork, Data.weightList]
  rw [weighGo_eq, e]
  by_cases h : d.weight ≤ k
  · rw [ite_eq_left h]; simp only; omega
  · rw [ite_eq_right h]; simp only; omega

/-- The smaller of two weights, or `cap + 1` when both are more than `cap`.
    Both are weighed within `k`, and `k` doubles until one of them is found
    or `k` reaches `cap`, so this looks at no more than about four times the
    smaller weight, or the cap: comparing a small value
    with a large one costs what the small one weighs. -/
def minWeightGo (cap : Nat) (x y : Data) (k : Nat) : Nat :=
  let a := weighWithin k x
  let b := weighWithin k y
  if a ≤ k ∨ b ≤ k ∨ cap ≤ k then min (min a b) (cap + 1)
  else minWeightGo cap x y (min (2 * k + 1) cap)
termination_by cap + 1 - k
decreasing_by omega

theorem minWeightGo_eq (cap : Nat) (x y : Data) (k : Nat) :
    minWeightGo cap x y k = min (min x.weight y.weight) (cap + 1) := by
  rw [minWeightGo]
  rw [weighWithin_eq, weighWithin_eq]
  by_cases h : min x.weight (k + 1) ≤ k ∨ min y.weight (k + 1) ≤ k ∨ cap ≤ k
  · rw [ite_eq_left h]; omega
  · rw [ite_eq_right h]; exact minWeightGo_eq cap x y (min (2 * k + 1) cap)
termination_by cap + 1 - k
decreasing_by omega

/-- What a step budget charges for an operation. Addition and subtraction cost
    the bits of the operands. Multiplication, division and remainder cost the
    product of those bits. `less` costs the sum of the bits, `text` and
    `codes` one more than the length of a text or an array of code points,
    and `equal` the weight of the lighter of its two values, which bounds the
    pairs it compares (`homoiconic-q59.73`). Anything else costs one. The
    charge is read off the argument; it does not run the operation. -/
def arithCost : Nat → Data → Nat
  | 0, .arr [.nat a, .nat b] => bits a + bits b
  | 1, .arr [.nat a, .nat b] => bits a + bits b
  | 2, .arr [.nat a, .nat b] => bits a * bits b
  | 3, .arr [.nat a, .nat b] => bits a * bits b
  | 4, .arr [.nat a, .nat b] => bits a * bits b
  | 5, .arr [x, y] => min x.weight y.weight
  | 6, .arr [.nat a, .nat b] => bits a + bits b
  | 7, .text t => t.length + 1
  | 7, .arr xs => xs.length + 1
  | 8, .text t => t.length + 1
  | 8, .arr xs => xs.length + 1
  | _, _ => 1

/-- `arithCost`, or `cap + 1` when it is more than `cap`. `equal` weighs its
    values within the cap, so a comparison the budget cannot pay for is found
    out in no more time than the budget pays for. -/
def arithCostWithin : Nat → Data → Nat → Nat
  | 5, .arr [x, y], cap => minWeightGo cap x y 1
  | n, d, cap => min (arithCost n d) (cap + 1)

theorem arithCostWithin_eq (n : Nat) (d : Data) (cap : Nat) :
    arithCostWithin n d cap = min (arithCost n d) (cap + 1) := by
  unfold arithCostWithin
  split
  · rw [minWeightGo_eq]; rfl
  · rfl

/-- What a step of the machine's own costs for the data it takes whole:
    `succ` or `case` of a number its words, `cons` onto a text one more than
    the text's length, as `codes` costs. -/
def arithWork : Data → Nat
  | .nat n => natWords n
  | .name n => natWords n
  | .text cs => cs.length + 1
  | _ => 1

/-- What reaching a variable costs when the machine walks `i` places of the
    environment to it: one, and one more for each 32 places. -/
def arithReach (i : Nat) : Nat := i / 32 + 1

/-- The table the host runs with. The theorems do not mention it: they hold
    for every table. -/
instance arithOps : Ops where
  op := arith
  cost := arithCost
  costWithin := arithCostWithin
  costWithin_eq := arithCostWithin_eq
  work := arithWork
  reach := arithReach

end Reflect
