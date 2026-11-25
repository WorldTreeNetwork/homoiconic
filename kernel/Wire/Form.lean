import Wire.Cbor
import Reflect.Machine
import Reflect.Space

/-! What a program and a machine value are as data, so that each has a byte
    form through `Wire.write`.

    A program is its quoted form, `reify`. A function value is the program of
    its body and the values it captured, so code has one form on the wire. -/

namespace Wire
open Reflect

deriving instance BEq for Reflect.Code

/-- The program a block of code was compiled from, when it is exactly the
    compilation of one. `decompile` alone also reads code no compilation
    gives, so the result is compiled again and compared. -/
def blockTerm (c : Code) : Option Term :=
  match decompile c with
  | some t => if compile t == c then some t else none
  | none => none

mutual
  /-- A machine value as data: `[0, d]` for data, `[1, body, captured]` for a
      function, where `body` is the quoted program of its code. `none` for a
      function whose code is not the compilation of a program; no compiled
      program makes such a value. -/
  def valueData : MValue → Option Data
    | .data d => some (.arr [.nat 0, d])
    | .closure c env =>
        match blockTerm c, valuesData env with
        | some t, some ds => some (.arr [.nat 1, reify t, .arr ds])
        | _, _ => none
  def valuesData : List MValue → Option (List Data)
    | [] => some []
    | v :: vs =>
        match valueData v, valuesData vs with
        | some d, some ds => some (d :: ds)
        | _, _ => none
end

mutual
  def dataValue : Data → Option MValue
    | .arr [.nat 0, d] => some (.data d)
    | .arr [.nat 1, body, .arr ds] =>
        match unreify body, dataValues ds with
        | some t, some env => some (.closure (compile t) env)
        | _, _ => none
    | _ => none
  def dataValues : List Data → Option (List MValue)
    | [] => some []
    | d :: ds =>
        match dataValue d, dataValues ds with
        | some v, some vs => some (v :: vs)
        | _, _ => none
end

/-- What is left of `left` after a block of code is counted as its data form
    is built: a hundred for each instruction (its quoted program is about
    seven cells an instruction), and a literal as it is written. `none` when
    it takes more. The code that follows an instruction is a tail call. -/
def codeFits : Code → Nat → Option Nat
  | .done, left => some left
  | .access _ k, left => if 100 ≤ left then codeFits k (left - 100) else none
  | .closure b k, left =>
      if 100 ≤ left then
        match codeFits b (left - 100) with
        | some l => codeFits k l
        | none => none
      else none
  | .literal d k, left =>
      if 100 ≤ left then
        match writesGo (left - 100) [] [d] with
        | some l => codeFits k l
        | none => none
      else none
  | .checkFun k, left => codeFits k left
  | .apply k, left => if 100 ≤ left then codeFits k (left - 100) else none
  | .checkData k, left => codeFits k left
  | .succ k, left => if 100 ≤ left then codeFits k (left - 100) else none
  | .cons k, left => if 100 ≤ left then codeFits k (left - 100) else none
  | .dcase z sc n c k, left =>
      if 100 ≤ left then
        match codeFits z (left - 100) with
        | none => none
        | some l =>
          match codeFits sc l with
          | none => none
          | some l =>
            match codeFits n l with
            | none => none
            | some l =>
              match codeFits c l with
              | none => none
              | some l => codeFits k l
      else none
  | .checkNat k, left => codeFits k left
  | .prim k, left => if 100 ≤ left then codeFits k (left - 100) else none

/-- What is left of `left` after the values of `cur` and then of each list of
    `work` are counted as their data forms are written: data as `writesGo`
    counts it, a function two, its code as `codeFits` counts it, and the
    values it captured where they are held. Captured values wait in `work`,
    so nothing here recurses on how deep functions are nested. -/
def valuesFit : (left : Nat) → (work : List (List MValue)) → (cur : List MValue) → Option Nat
  | left, [], [] => some left
  | left, w :: work, [] => valuesFit left work w
  | left, work, .data d :: vs =>
      if _h : 2 ≤ left then
        match writesGo (left - 2) [] [d] with
        | some l => valuesFit (min l (left - 2)) work vs
        | none => none
      else none
  | left, work, .closure c env :: vs =>
      if _h : 2 ≤ left then
        match codeFits c (left - 2) with
        | some l => valuesFit (min l (left - 2)) (vs :: work) env
        | none => none
      else none
termination_by left work => (left, work.length)
decreasing_by
  all_goals simp_wf
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)
  all_goals (apply Prod.Lex.left; omega)

/-- Whether the data form of a machine value can be written in `n` bytes,
    found without building it. `valueData` writes each captured value where it
    is held, so the form of a function can be far larger than what it holds. -/
def fitsValue (v : MValue) (n : Nat) : Bool := (valuesFit n [] [v]).isSome

/-- The byte form of a program: the bytes of its quoted form. -/
def programBytes (t : Term) : ByteArray := write (reify t)

def readProgram (b : ByteArray) : Except String Term := do
  match unreify (← read b) with
  | some t => .ok t
  | none => .error "the value is not a program"

/-- The byte form of a machine value, a waiting program among them. -/
def valueBytes (v : MValue) : Option ByteArray := (valueData v).map write

def readValue (b : ByteArray) : Except String MValue := do
  match dataValue (← read b) with
  | some v => .ok v
  | none => .error "the value is not a machine value"

end Wire
