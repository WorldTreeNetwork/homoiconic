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

-- A kept session's machine and the paths behind `keep`, `vm`, `node`, `ask`
-- and `chan` (`bound-kept-sessions`, `homoiconic-q59.78`): pieces made from
-- data and machine values, data read back from pieces, a piece's references
-- replaced, the pieces of a partial value counted (and counted within a cap),
-- equality on data, a piece and its byte form, saving, and the drivers' and
-- readers' loops over answers, events, entries and lines.
example : @Data.toP = @Data.toPWalk := Reflect.Data.toP_eq_walk
example : @Data.listToP = @Data.listToPWalk := Reflect.Data.listToP_eq_walk
example : @MValue.toP = @MValue.toPWalk := Reflect.MValue.toP_eq_walk
example : @envToP = @envToPWalk := Reflect.envToP_eq_walk
example : @P.toData = @P.toDataWalk := Reflect.P.toData_eq_walk
example : @P.hyd = @P.hydWalk := Reflect.P.hyd_eq_walk
example : @P.nodes = @P.nodesWalk := Reflect.P.nodes_eq_walk
example : @Data.nodes = @Data.nodesWalk := Reflect.Data.nodes_eq_walk
example : ∀ {R : Type} (p : P R) (cap : Nat), p.nodesWithin cap = min p.nodes (cap + 1) :=
  Reflect.P.nodesWithin_eq
example : ∀ (d : Data) (cap : Nat), d.nodesWithin cap = min d.nodes (cap + 1) :=
  Reflect.Data.nodesWithin_eq
example : @Data.decEq = @Data.decEqWalk := Reflect.Data.decEq_eq_walk
example : @Wire.pieceItem = @Wire.pieceItemWalk := Wire.pieceItem_eq_walk
example : @Wire.itemPiece = @Wire.itemPieceWalk := Wire.itemPiece_eq_walk
example : @Wire.cut = @Wire.cutWalk := Wire.cut_eq_walk
example : @driveRun = @driveRunWalk := Reflect.driveRun_eq_walk
example : @schedIn = @schedInWalk := Reflect.schedIn_eq_walk
example : @autoRun = @autoRunWalk := Reflect.autoRun_eq_walk
example : @Surface.Keep.parts = @Surface.Keep.partsWalk := Surface.Keep.parts_eq_walk
example : @Surface.Keep.openProcs = @Surface.Keep.openProcsWalk := Surface.Keep.openProcs_eq_walk
example : @Surface.Keep.renderNodeProcs = @Surface.Keep.renderNodeProcsWalk :=
  Surface.Keep.renderNodeProcs_eq_walk
example : @Surface.Keep.dataEntries = @Surface.Keep.dataEntriesWalk := Surface.Keep.dataEntries_eq_walk
example : @Surface.Keep.dataOps = @Surface.Keep.dataOpsWalk := Surface.Keep.dataOps_eq_walk
example : @Surface.dataEvents = @Surface.dataEventsWalk := Surface.dataEvents_eq_walk
example : @Surface.renderProcs = @Surface.renderProcsWalk := Surface.renderProcs_eq_walk
example : @Surface.Cross.readLines = @Surface.Cross.readLinesWalk := Surface.Cross.readLines_eq_walk
example : @Surface.Cross.readChain = @Surface.Cross.readChainWalk := Surface.Cross.readChain_eq_walk

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
#print axioms Reflect.Data.toP_eq_walk
#print axioms Reflect.Data.listToP_eq_walk
#print axioms Reflect.MValue.toP_eq_walk
#print axioms Reflect.envToP_eq_walk
#print axioms Reflect.P.toData_eq_walk
#print axioms Reflect.P.hyd_eq_walk
#print axioms Reflect.P.nodes_eq_walk
#print axioms Reflect.Data.nodes_eq_walk
#print axioms Reflect.P.nodesWithin_eq
#print axioms Reflect.Data.nodesWithin_eq
#print axioms Reflect.Data.decEq_eq_walk
#print axioms Wire.pieceItem_eq_walk
#print axioms Wire.itemPiece_eq_walk
#print axioms Wire.cut_eq_walk
#print axioms Reflect.driveRun_eq_walk
#print axioms Reflect.schedIn_eq_walk
#print axioms Reflect.autoRun_eq_walk
#print axioms Surface.Keep.parts_eq_walk
#print axioms Surface.Keep.openProcs_eq_walk
#print axioms Surface.Keep.renderNodeProcs_eq_walk
#print axioms Surface.Keep.dataEntries_eq_walk
#print axioms Surface.Keep.dataOps_eq_walk
#print axioms Surface.dataEvents_eq_walk
#print axioms Surface.renderProcs_eq_walk
#print axioms Surface.Cross.readLines_eq_walk
#print axioms Surface.Cross.readChain_eq_walk
