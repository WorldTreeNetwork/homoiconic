import Wire.Cbor
import Reflect.Machine

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
