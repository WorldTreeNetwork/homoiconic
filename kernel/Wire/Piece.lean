import Wire.Form
import Wire.Blake3
import Reflect.Store

/-! The byte form of a piece of stored state, and saving: cutting a piece and
    naming each part by the hash of its bytes.

    A reference is the 32-byte Blake3 hash of the bytes of the piece it names.
    Nothing is proved in this file. `Reflect.StoreProof` says that where the
    cuts go cannot change what a program computes; that a hash names one piece
    is assumed. `Wire.PieceProof` says that what `cut` leaves and the root
    `save` gives depend only on the value, when every reference in the piece
    was made by `cut`, and that `opened` gives such a piece for a root. -/

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

/-! `pieceItem`, `itemPiece` and `cut` recurse once for each level and each
    item of a piece; the compiler runs loops over a list of work on the heap,
    proved equal (`homoiconic-q59.78`: saving a waiting program that held a
    list or a nest of a million ended the process on a full stack in `cut`). -/

/-- What is still to do in `pieceItemGo`. -/
inductive IAct where
  | piece : P Ref → IAct
  | cons : IAct
  | close : Term → IAct
  | closeCode : Code → IAct

noncomputable def IAct.weight : IAct → Nat
  | .piece p => 3 * sizeOf p
  | _ => 0

noncomputable def IAct.weights : List IAct → Nat
  | [] => 0
  | a :: as => a.weight + 1 + IAct.weights as

def pieceItemGo : List IAct → List Item → Option Item
  | [], i :: _ => some i
  | [], [] => none
  | .piece (.nat n) :: as, st => pieceItemGo as (.nat n :: st)
  | .piece (.name n) :: as, st => pieceItemGo as (.name n :: st)
  | .piece (.text t) :: as, st => pieceItemGo as (.text t :: st)
  | .piece .nil :: as, st => pieceItemGo as (.arr [] :: st)
  | .piece (.cons h t) :: as, st => pieceItemGo (.piece h :: .piece t :: .cons :: as) st
  | .piece (.closure c e) :: as, st =>
      match blockTerm c with
      | some t => pieceItemGo (.piece e :: .close t :: as) st
      | none => none
  | .piece (.ref r) :: as, st => pieceItemGo as (.bytes r :: st)
  | .cons :: as, b :: a :: st => pieceItemGo as (.arr [.nat 0, a, b] :: st)
  | .close t :: as, b :: st => pieceItemGo as (.arr [.nat 1, .ofData (reify t), b] :: st)
  | _ :: as, st => pieceItemGo as st
termination_by as => IAct.weights as
decreasing_by all_goals simp_wf; all_goals (simp [IAct.weights, IAct.weight] <;> omega)

theorem pieceItemGo_piece (p : P Ref) : ∀ (as : List IAct) (st : List Item),
    pieceItemGo (.piece p :: as) st =
      match pieceItem p with
      | some i => pieceItemGo as (i :: st)
      | none => none := by
  induction p with
  | nat n => intro as st; rw [pieceItemGo]; rfl
  | name n => intro as st; rw [pieceItemGo]; rfl
  | text t => intro as st; rw [pieceItemGo]; rfl
  | nil => intro as st; rw [pieceItemGo]; rfl
  | ref r => intro as st; rw [pieceItemGo]; rfl
  | cons h t ihh iht =>
    intro as st
    rw [pieceItemGo, ihh]
    simp only [pieceItem]
    cases pieceItem h with
    | none => rfl
    | some a =>
      simp only []
      rw [iht]
      cases pieceItem t with
      | none => rfl
      | some b => simp only []; rw [pieceItemGo]
  | closure c e ih =>
    intro as st
    rw [pieceItemGo]
    simp only [pieceItem]
    cases blockTerm c with
    | none => rfl
    | some t =>
      simp only []
      rw [ih]
      cases pieceItem e with
      | none => rfl
      | some b => simp only []; rw [pieceItemGo]

def pieceItemWalk (p : P Ref) : Option Item := pieceItemGo [.piece p] []

@[csimp] theorem pieceItem_eq_walk : @pieceItem = @pieceItemWalk := by
  funext p
  simp only [pieceItemWalk, pieceItemGo_piece]
  cases pieceItem p <;> simp [pieceItemGo]

/-- What is still to do in `itemPieceGo`. -/
inductive JAct where
  | item : Item → JAct
  | cons : JAct
  | close : Code → JAct

noncomputable def JAct.weight : JAct → Nat
  | .item i => 3 * sizeOf i
  | _ => 0

noncomputable def JAct.weights : List JAct → Nat
  | [] => 0
  | a :: as => a.weight + 1 + JAct.weights as

def itemPieceGo : List JAct → List (P Ref) → Option (P Ref)
  | [], p :: _ => some p
  | [], [] => none
  | .item (.nat n) :: as, st => itemPieceGo as (.nat n :: st)
  | .item (.name n) :: as, st => itemPieceGo as (.name n :: st)
  | .item (.text t) :: as, st => itemPieceGo as (.text t :: st)
  | .item (.arr []) :: as, st => itemPieceGo as (.nil :: st)
  | .item (.arr [.nat 0, h, t]) :: as, st => itemPieceGo (.item h :: .item t :: .cons :: as) st
  | .item (.arr [.nat 1, body, e]) :: as, st =>
      match body.toData.bind unreify with
      | some t => itemPieceGo (.item e :: .close (compile t) :: as) st
      | none => none
  | .item (.bytes r) :: as, st => if r.size == 32 then itemPieceGo as (.ref r :: st) else none
  | .item _ :: _, _ => none
  | .cons :: as, b :: a :: st => itemPieceGo as (.cons a b :: st)
  | .close c :: as, b :: st => itemPieceGo as (.closure c b :: st)
  | _ :: as, st => itemPieceGo as st
termination_by as => JAct.weights as
decreasing_by all_goals simp_wf; all_goals (simp [JAct.weights, JAct.weight] <;> omega)

theorem itemPieceGo_item (i : Item) (as : List JAct) (st : List (P Ref)) :
    itemPieceGo (.item i :: as) st =
      match itemPiece i with
      | some p => itemPieceGo as (p :: st)
      | none => none := by
  by_cases h0 : ∃ h t, i = .arr [.nat 0, h, t]
  · obtain ⟨h, t, he⟩ := h0
    rw [he, itemPieceGo, itemPieceGo_item h]
    simp only [itemPiece]
    cases itemPiece h with
    | none => rfl
    | some a =>
      simp only []
      rw [itemPieceGo_item t]
      cases itemPiece t with
      | none => rfl
      | some b => simp only []; rw [itemPieceGo]
  by_cases h1 : ∃ body e, i = .arr [.nat 1, body, e]
  · obtain ⟨body, e, he⟩ := h1
    rw [he, itemPieceGo]
    simp only [itemPiece]
    cases body.toData.bind unreify with
    | none => rfl
    | some t =>
      simp only []
      rw [itemPieceGo_item e]
      cases itemPiece e with
      | none => rfl
      | some b => simp only []; rw [itemPieceGo]
  have n0 : ∀ h t, i = .arr [.nat 0, h, t] → False := fun h t e => h0 ⟨h, t, e⟩
  have n1 : ∀ b e, i = .arr [.nat 1, b, e] → False := fun b e x => h1 ⟨b, e, x⟩
  cases i with
  | nat n => rw [itemPieceGo]; rfl
  | name n => rw [itemPieceGo]; rfl
  | text t => rw [itemPieceGo]; rfl
  | bytes r => rw [itemPieceGo]; simp only [itemPiece]; split <;> rfl
  | arr xs =>
    by_cases he : xs = []
    · subst he; rw [itemPieceGo]; rfl
    · have ne : Item.arr xs = .arr [] → False := fun e => he (Item.arr.inj e)
      rw [itemPieceGo.eq_10 _ _ _ (fun _ e => by cases e) (fun _ e => by cases e)
          (fun _ e => by cases e) ne n0 n1 (fun _ e => by cases e),
        itemPiece.eq_8 _ (fun _ e => by cases e) (fun _ e => by cases e)
          (fun _ e => by cases e) ne n0 n1 (fun _ e => by cases e)]
termination_by sizeOf i
decreasing_by all_goals (simp_wf; subst_vars; simp; omega)

def itemPieceWalk (i : Item) : Option (P Ref) := itemPieceGo [.item i] []

@[csimp] theorem itemPiece_eq_walk : @itemPiece = @itemPieceWalk := by
  funext i
  simp only [itemPieceWalk, itemPieceGo_item]
  cases itemPiece i <;> simp [itemPieceGo]

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

/-- `cut`'s walk: pieces still to cut, or a pair or a function to build and
    keep from the parts on top of the stack, already cut, in the order `cut`
    cuts them, so the pieces are stored in the same order. -/
def cutGo (size : Nat) : List IAct → List (P Ref) → Saver (P Ref)
  | [], p :: _ => pure p
  | [], [] => failure
  | .piece (.nat n) :: as, st => do let p ← kept size (.nat n); cutGo size as (p :: st)
  | .piece (.name n) :: as, st => do let p ← kept size (.name n); cutGo size as (p :: st)
  | .piece (.text t) :: as, st => do let p ← kept size (.text t); cutGo size as (p :: st)
  | .piece .nil :: as, st => do let p ← kept size .nil; cutGo size as (p :: st)
  | .piece (.ref r) :: as, st => cutGo size as (.ref r :: st)
  | .piece (.cons h t) :: as, st => cutGo size (.piece h :: .piece t :: .cons :: as) st
  | .piece (.closure c e) :: as, st => cutGo size (.piece e :: .closeCode c :: as) st
  | .cons :: as, t :: h :: st => do let p ← kept size (.cons h t); cutGo size as (p :: st)
  | .closeCode c :: as, e :: st => do let p ← kept size (.closure c e); cutGo size as (p :: st)
  | _ :: as, st => cutGo size as st
termination_by as => IAct.weights as
decreasing_by all_goals simp_wf; all_goals (simp [IAct.weights, IAct.weight] <;> omega)

theorem cutGo_piece (size : Nat) (p : P Ref) : ∀ (as : List IAct) (st : List (P Ref)),
    cutGo size (.piece p :: as) st = (do let q ← cut size p; cutGo size as (q :: st)) := by
  induction p with
  | nat n => intro as st; rw [cutGo, cut]
  | name n => intro as st; rw [cutGo, cut]
  | text t => intro as st; rw [cutGo, cut]
  | nil => intro as st; rw [cutGo, cut]
  | ref r => intro as st; rw [cutGo, cut]; simp
  | cons h t ihh iht =>
    intro as st
    rw [cutGo, ihh, cut]
    simp only [bind_assoc]
    congr 1; funext h'
    rw [iht]
    congr 1; funext t'
    rw [cutGo]
  | closure c e ih =>
    intro as st
    rw [cutGo, ih, cut]
    simp only [bind_assoc]
    congr 1; funext e'
    rw [cutGo]

def cutWalk (size : Nat) (p : P Ref) : Saver (P Ref) := cutGo size [.piece p] []

@[csimp] theorem cut_eq_walk : @cut = @cutWalk := by
  funext size p
  rw [cutWalk, cutGo_piece]
  have h : ∀ q, cutGo size [] [q] = pure q := fun q => by rw [cutGo.eq_def]
  simp only [h, bind_pure]

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

/-- What a turn holds of the value saved under the root `r`, given the piece
    `p` stored there. `save` stores the top piece whatever its size, so a root
    can name a piece of at most `size` bytes, which `cut` would have left in
    place inside a value. Such a piece is held as it is, and the root is held
    as a reference only when `cut` would have made that reference. -/
def opened (size : Nat) (r : Ref) (p : P Ref) : P Ref :=
  match pieceBytes p with
  | some b => if b.size ≤ size then p else .ref r
  | none => .ref r

end Wire
