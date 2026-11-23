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

-- `homoiconic-q59.47`: a turn of `keep` saves only references that `cut` made.

-- A root is not always a reference `cut` would make inside a value: `save`
-- stores the top piece whatever its size. A turn that starts from a root holds
-- the piece under it as `opened` gives it, and that is `Made` for the value
-- saved, in any store that holds the old pieces and the pieces `save` stored.
example : ∀ {size : Nat} {σ : Store Ref} {p q : P Ref} {r : Ref} {w : Array (Ref × ByteArray)},
    Made size σ p q → save size p = some (r, w) →
    ∃ ps : List Stored, w = bytesOf ps ∧
      (∀ t ∈ ps, pieceBytes t.2.2 = some t.2.1 ∧ t.1 = Blake3.hash t.2.1) ∧
      ∀ τ : Store Ref, σ.le τ → (∀ t ∈ ps, τ t.1 = some t.2.2) →
        ∃ top, τ r = some top ∧ Made size τ (opened size r top) q :=
  Wire.save_opened

-- A piece every reference of which was made by `cut` resolves to a whole
-- value and is saved under the root that value is saved under.
example : ∀ {size : Nat} {σ : Store Ref} {p : P Ref}, Good size σ p →
    ∃ q, Unf σ p q ∧ (save size p).map (·.1) = (save size q).map (·.1) :=
  Wire.good_root

-- The invariant of a session that runs one turn, and where such a session can
-- be after it was carried on. These are the definitions, restated.
example : ∀ {σ : Store Ref} {s : Session}, Inv σ s ↔
    s.store.le σ ∧ PhaseGood σ s.phase ∧ s.vm = none ∧ s.node = none ∧ s.written = #[] :=
  fun {_ _} => ⟨fun h => ⟨h.le, h.good, h.vm, h.node, h.written⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩
example : ∀ {σ : Store Ref} {s : Session}, Turn σ s ↔
    Inv σ s ∨ (∃ (s' : Session) (d : Data) (k : P Ref), Good pieceSize σ k ∧ s = s'.wait d k) ∨
      (s.phase = .done ∧ s.written = #[]) :=
  fun {_ _} => ⟨fun h => by
      cases h with
      | holds h => exact .inl h
      | waits h => exact .inr (.inl ⟨_, _, _, h, rfl⟩)
      | over a b => exact .inr (.inr ⟨a, b⟩),
    fun h => by
      rcases h with h | ⟨_, _, _, h, rfl⟩ | ⟨a, b⟩
      · exact .holds h
      · exact .waits h
      · exact .over a b⟩
example : ∀ {σ : Store Ref} {st : PState Ref}, PhaseGood σ (.run st) ↔ GoodS pieceSize σ st :=
  Iff.rfl
example : ∀ {σ : Store Ref} {r : Ref} {d : Data}, PhaseGood σ (.resuming r d) ↔
    ∃ p, σ r = some p ∧ Good pieceSize σ (opened pieceSize r p) := Iff.rfl

-- Carrying a turn on keeps the invariant, until the turn saves a function
-- every reference of which was made by `cut`, or ends with nothing stored.
example : ∀ {σ : Store Ref} (fuel : Nat) {s : Session}, Inv σ s → Turn σ (advance fuel s) :=
  Surface.Keep.advance_turn

-- The first turn of a program.
example : ∀ {σ : Store Ref} (src : ByteArray) (budget : Nat), Turn σ (start src budget) :=
  Surface.Keep.start_turn

-- A turn that answers the program under a root. `save_opened` gives the
-- hypothesis for a root that saving gave.
example : ∀ {σ : Store Ref} {root : String} {r : Ref}, unhex root = some r →
    (∃ p, σ r = some p ∧ Good pieceSize σ (opened pieceSize r p)) →
    ∀ (src : ByteArray) (budget : Nat), Turn σ (answer root src budget) :=
  Surface.Keep.answer_turn

-- Supplying a piece. That the session's pieces, with the piece read from the
-- bytes among them, are still part of the store is a hypothesis.
example : ∀ {σ : Store Ref} {s : Session} {bytes : ByteArray}, Inv σ s →
    (∀ r p, s.need = some r → readPiece bytes = .ok p →
      ∀ x q, (s.pieces.insert r p)[x]? = some q → σ x = some q) →
    Turn σ (give s bytes) :=
  Surface.Keep.give_turn

-- What a turn that waits saved has the root of the same value held whole.
example : ∀ {σ : Store Ref} {k : P Ref}, Good pieceSize σ k →
    ∃ q, Unf σ k q ∧ (save pieceSize k).map (·.1) = (save pieceSize q).map (·.1) :=
  Surface.Keep.waits_root

#print axioms Wire.save_opened
#print axioms Wire.good_root
#print axioms Wire.norm_small
#print axioms Surface.Keep.chase_good
#print axioms Surface.Keep.steps_good
#print axioms Surface.Keep.advance_turn
#print axioms Surface.Keep.start_turn
#print axioms Surface.Keep.answer_turn
#print axioms Surface.Keep.give_turn
#print axioms Surface.Keep.waits_root
