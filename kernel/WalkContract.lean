import Reflect
import Wire
import Surface

open Reflect

/-! The walks the compiler runs in place of functions that would recurse once
for each level of nesting (`homoiconic-q59.72`). Each `@[csimp]` theorem says
the walk is the function: the definitions the other theorems mention are
unchanged, and the compiled kernel runs a loop over a list of work on the heap
instead of a call for each level. The two equalities that are not walks of an
existing definition say what they decide. -/

-- The language and the machine.
example : @reify = @reifyWalk := Reflect.reify_eq_walk
example : @unreify = @unreifyWalk := Reflect.unreify_eq_walk
example : @comp = @compWalk := Reflect.comp_eq_walk
example : @decomp = @decompWalk := Reflect.decomp_eq_walk
example : @Data.mentions = @Data.mentionsWalk := Reflect.mentions_eq_walk

-- `equal` (operation 5 of `arith`) and every `==` on data.
example : ∀ x y : Data, Data.same x y = true ↔ x = y := Reflect.Data.same_iff
example : ∀ x y : Data, (x == y) = Data.same x y := fun _ _ => rfl

-- The byte form of a machine value, and what it is counted at before it is built.
example : @Wire.valueData = @Wire.valueDataWalk := Wire.valueData_eq_walk
example : @Wire.codeFits = @Wire.codeFitsWalk := Wire.codeFits_eq_walk
example : ∀ a b : Code, Wire.Code.same a b = true ↔ a = b := Wire.Code.same_iff

-- The printer, and a crossing guest's record.
example : @Surface.renderData = @Surface.renderWalk := Surface.renderData_eq_walk
example : @Surface.Cross.chain = @Surface.Cross.chainWalk := Surface.Cross.chain_eq_walk
example : @Surface.Cross.numbers = @Surface.Cross.numbersWalk := Surface.Cross.numbers_eq_walk

-- A run asks each charge within the fuel it has left (`homoiconic-q59.73`):
-- what it runs is the priced run and the space-limited run, and an operation's
-- charge found within a cap is the charge, or more than the cap.
example : @runPriced = @runPricedWithin := Reflect.runPriced_eq_within
example : @runSpace = @runSpaceWithin := Reflect.runSpace_eq_within
example : ∀ [Ops] (s : State) (cap : Nat), stepCostWithin s cap = min (stepCost s) (cap + 1) :=
  Reflect.stepCostWithin_eq
example : ∀ n d cap, arithCostWithin n d cap = min (arithCost n d) (cap + 1) :=
  Reflect.arithCostWithin_eq
example : ∀ (k : Nat) (d : Data), weighWithin k d = min d.weight (k + 1) := Reflect.weighWithin_eq

-- Numbers read and written by halves (`homoiconic-q59.64`): the printed
-- digits, the source reader's digits, a token, and a number's byte form.
example : @Surface.decimal = @Surface.decimalGo := Surface.decimal_eq_go
example : ∀ n, Surface.decimalGo n = n.repr := Surface.decimalGo_eq
example : @Surface.Read.digitsValue = @Surface.Read.digitsSplit := Surface.Read.digitsValue_eq_split
example : @Surface.Read.takeWhileB = @Surface.Read.takeWhileWalk := Surface.Read.takeWhileB_eq_walk
example : ∀ b pos k, Wire.bigBE b pos k = Wire.takeBE b pos k 0 := fun b pos k => Wire.bigBE_eq b k pos
example : ∀ k n out, Wire.pushBig k n out = Wire.pushBE k n out := Wire.pushBig_eq

#print axioms Reflect.runPriced_eq_within
#print axioms Reflect.runSpace_eq_within
#print axioms Reflect.arithCostWithin_eq
#print axioms Surface.decimal_eq_go
#print axioms Surface.Read.digitsValue_eq_split
#print axioms Surface.Read.takeWhileB_eq_walk
#print axioms Wire.bigBE_eq
#print axioms Wire.pushBig_eq
#print axioms Reflect.reify_eq_walk
#print axioms Reflect.unreify_eq_walk
#print axioms Reflect.comp_eq_walk
#print axioms Reflect.decomp_eq_walk
#print axioms Reflect.mentions_eq_walk
#print axioms Reflect.Data.same_iff
#print axioms Wire.valueData_eq_walk
#print axioms Wire.codeFits_eq_walk
#print axioms Wire.Code.same_iff
#print axioms Surface.renderData_eq_walk
#print axioms Surface.Cross.chain_eq_walk
#print axioms Surface.Cross.numbers_eq_walk
