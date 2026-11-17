import Wire.Form
import Wire.Blake3
import Reflect.Store

/-! The byte form of a piece of stored state, and saving: cutting a piece and
    naming each part by the hash of its bytes.

    A reference is the 32-byte Blake3 hash of the bytes of the piece it names.
    Nothing here is proved. `Reflect.StoreProof` says that where the cuts go
    cannot change what a program computes; that a hash names one piece is
    assumed. -/

namespace Wire
open Reflect

/-- A reference: 32 bytes. -/
abbrev Ref := ByteArray

/-- A piece as an item. A number is itself, a name is the name, a text is the
    text, an empty list is `[]`, a pair is
    `[0, head, tail]`, a function is `[1, body, captured]` with `body` the
    quoted program of its code, and a reference is a byte string. `none` for a
    function whose code is not a compiled program. -/
def pieceItem : P Ref → Option Item
  | .nat n => some (.nat n)
  | .name n => some (.name n)
  | .text t => some (.text t)
  | .nil => some (.arr [])
  | .cons h t =>
      match pieceItem h, pieceItem t with
      | some a, some b => some (.arr [.nat 0, a, b])
      | _, _ => none
  | .closure c e =>
      match blockTerm c, pieceItem e with
      | some t, some b => some (.arr [.nat 1, .ofData (reify t), b])
      | _, _ => none
  | .ref r => some (.bytes r)

def itemPiece : Item → Option (P Ref)
  | .nat n => some (.nat n)
  | .name n => some (.name n)
  | .text t => some (.text t)
  | .arr [] => some .nil
  | .arr [.nat 0, h, t] =>
      match itemPiece h, itemPiece t with
      | some a, some b => some (.cons a b)
      | _, _ => none
  | .arr [.nat 1, body, e] =>
      match body.toData.bind unreify, itemPiece e with
      | some t, some b => some (.closure (compile t) b)
      | _, _ => none
  | .bytes r => if r.size == 32 then some (.ref r) else none
  | _ => none

def pieceBytes (p : P Ref) : Option ByteArray := (pieceItem p).map writeItem

def readPiece (b : ByteArray) : Except String (P Ref) := do
  match itemPiece (← readItem b) with
  | some p => .ok p
  | none => .error "the value is not a piece"

/-- Pieces to be stored, each under the hash of its bytes, newest last. -/
abbrev Saver := StateT (Array (Ref × ByteArray)) Option

/-- Store a piece and give its reference. -/
def stored (p : P Ref) : Saver (P Ref) := do
  let b ← (pieceBytes p : Option ByteArray)
  let r := Blake3.hash b
  modify (·.push (r, b))
  pure (.ref r)

/-- Keep a piece where it is when its bytes are at most `size`; otherwise
    store it and leave its reference. -/
def kept (size : Nat) (p : P Ref) : Saver (P Ref) := do
  let b ← (pieceBytes p : Option ByteArray)
  if b.size ≤ size then pure p else stored p

/-- Cut a piece from the leaves up. A part that is already a reference is left
    alone: it was stored before and is not written again. A long list ends up
    as a chain of stored runs, each a little over `size` bytes. -/
def cut (size : Nat) : P Ref → Saver (P Ref)
  | .nat n => kept size (.nat n)
  | .name n => kept size (.name n)
  -- A text is one piece, as a number is: kept or stored whole, never cut. What
  -- is compared with `size` is its whole byte form, the head and the UTF-8.
  | .text t => kept size (.text t)
  | .nil => kept size .nil
  | .ref r => pure (.ref r)
  | .cons h t => do
      let h' ← cut size h
      let t' ← cut size t
      kept size (.cons h' t')
  | .closure c e => do
      let e' ← cut size e
      kept size (.closure c e')

/-- Save a whole value: cut it, and store what is left at the top. The result
    is the root reference and every piece that was stored. -/
def save (size : Nat) (p : P Ref) : Option (Ref × Array (Ref × ByteArray)) :=
  let run : Saver Ref := do
    match ← cut size p with
    | .ref r => pure r
    | top =>
        match ← stored top with
        | .ref r => pure r
        | _ => failure
  run.run #[]

end Wire
