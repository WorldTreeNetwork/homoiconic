import Wire.Cbor
import Reflect.Machine

/-! What a program and a machine value are as data, so that each has a byte
    form through `Wire.write`.

    A program is its quoted form, `reify`. A function value is the program of
    its body and the values it captured, so code has one form on the wire. -/

namespace Wire
open Reflect

/-- Read a program back from its data form. The inverse of `reify`
    (`unreify_reify`). Data that is no program's form is refused. -/
def unreify : Data → Option Term
  | .nat i => some (.var i)
  | .arr [.nat 0, f, a] => do pure (.app (← unreify f) (← unreify a))
  | .arr [.nat 1, b] => do pure (.lam (← unreify b))
  | .arr [.nat 2, d] => some (.lit d)
  | .arr [.nat 3, t] => do pure (.succ (← unreify t))
  | .arr [.nat 4, a, b] => do pure (.cons (← unreify a) (← unreify b))
  | .arr [.nat 5, s, z, sc, n, c] => do
      pure (.dcase (← unreify s) (← unreify z) (← unreify sc) (← unreify n) (← unreify c))
  | .arr [.nat 6, c, x] => do pure (.prim (← unreify c) (← unreify x))
  | _ => none

theorem unreify_reify : ∀ t : Term, unreify (reify t) = some t := by
  intro t
  induction t <;> simp_all [reify, unreify]

mutual
  /-- A machine value as data: `[0, d]` for data, `[1, body, captured]` for a
      function, where `body` is the quoted program of its code. `none` only
      for code that is not a compiled block, which no compiled program makes. -/
  def valueData : MValue → Option Data
    | .data d => some (.arr [.nat 0, d])
    | .closure c env =>
        match decompile c, valuesData env with
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
