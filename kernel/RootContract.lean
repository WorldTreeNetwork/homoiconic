import Reflect
import Wire
import Surface

open Reflect Wire Surface.Keep

-- Acceptance check for `homoiconic-q59.29`: equal states are saved under one
-- root. It fails to compile until the theorems exist with exactly these
-- signatures. The hash is `Wire.Blake3.hash`, used as the function it is;
-- nothing is assumed of it. This file does not import a table.

-- `Made size σ p q`: the partial piece `p` stands for the whole piece `q`, and
-- every reference in it is the one `cut` gives the value it stands for. It is
-- the same as: every reference was made by `cut`, and `p` resolves to `q`.
example : ∀ {size : Nat} {σ : Store Ref} {p q : P Ref},
    Made size σ p q ↔ Good size σ p ∧ Unf σ p q := Wire.made_iff

-- A piece with no reference in it is `Made`, under any store.
example : ∀ {size : Nat} {σ σ' : Store Ref} {p q : P Ref}, Unf σ' p q → Made size σ q q :=
  Wire.Made.whole

-- `cut` is a function of the value: two partial pieces that stand for one
-- value are cut to the same piece, whatever their stores hold and whatever was
-- stored before.
example : ∀ {size : Nat} {σ σ' : Store Ref} {p p' q : P Ref}, Made size σ p q →
    Made size σ' p' q → ∀ (acc acc' : Array (Ref × ByteArray)),
    ((cut size p).run acc).map (·.1) = ((cut size p').run acc').map (·.1) :=
  Wire.cut_function

-- `cut` makes only such references. What it leaves is what cutting the whole
-- value leaves, every piece it stored is under the hash of its bytes, and in
-- any store that holds the old pieces and those, what it leaves is `Made`.
example : ∀ {size : Nat} {σ : Store Ref} {p q c : P Ref} {acc acc' : Array (Ref × ByteArray)},
    Made size σ p q → (cut size p).run acc = some (c, acc') →
    norm size q = some c ∧ ∃ w : List Stored, acc' = acc ++ bytesOf w ∧
      (∀ t ∈ w, pieceBytes t.2.2 = some t.2.1 ∧ t.1 = Blake3.hash t.2.1) ∧
      ∀ τ : Store Ref, σ.le τ → (∀ t ∈ w, τ t.1 = some t.2.2) → Made size τ c q :=
  Wire.cut_made

-- The lazy machine makes no reference: a step, on any part of the store, keeps
-- every reference in the state one that `cut` made.
example : ∀ {size : Nat} {σ : Store Ref} [Ops] {σ' : Store Ref}, σ'.le σ →
    ∀ {ps ps' : PState Ref}, GoodS size σ ps → lstep σ' ps = .next ps' → GoodS size σ ps' :=
  Wire.lstep_good

-- Equal values are saved under one root.
example : ∀ {size : Nat} {σ σ' : Store Ref} {p p' q : P Ref}, Made size σ p q →
    Made size σ' p' q → (save size p).map (·.1) = (save size p').map (·.1) :=
  Wire.same_root

-- What is saved under the root is the value.
example : ∀ {size : Nat} {σ : Store Ref} {p q : P Ref} {r : Ref} {w : Array (Ref × ByteArray)},
    Made size σ p q → save size p = some (r, w) →
    ∃ ps : List Stored, w = bytesOf ps ∧
      (∀ t ∈ ps, pieceBytes t.2.2 = some t.2.1 ∧ t.1 = Blake3.hash t.2.1) ∧
      ∀ τ : Store Ref, σ.le τ → (∀ t ∈ ps, τ t.1 = some t.2.2) → Unf τ (.ref r) q :=
  Wire.save_resolves

-- A state kept after a first part of the log and restarted on the whole log
-- has the root a replay of the whole log from the start has.
example : ∀ {size : Nat} {σ σ' : Store Ref} [Ops] {p : Term} {l₁ l₂ : List Entry}
    {s v v' : Vm Value Outcome},
    Logged sourceP p l₁ s → Replay source s (l₁ ++ l₂) v → Logged sourceP p (l₁ ++ l₂) v' →
    ∀ {a b : P Ref}, Made size σ a (wholeState (v.map MP.injO MP.injV)) →
    Made size σ' b (wholeState (v'.map MP.injO MP.injV)) →
    (save size a).map (·.1) = (save size b).map (·.1) :=
  Surface.Keep.restart_same_root

#print axioms Wire.made_iff
#print axioms Wire.Made.whole
#print axioms Wire.cut_function
#print axioms Wire.cut_made
#print axioms Wire.lstep_good
#print axioms Wire.lrun_good
#print axioms Wire.same_root
#print axioms Wire.save_resolves
#print axioms Surface.Keep.state_same_root
#print axioms Surface.Keep.restart_same_root
