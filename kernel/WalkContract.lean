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
