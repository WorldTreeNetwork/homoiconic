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

-- `homoiconic-q59.54`: a VM's and a node's session save only references that
-- `cut` made.

-- The parts of a list piece are found with a bound on the references the
-- whole list passes through, so `parts` is a function Lean can prove things
-- of. These are its cases.
example : ∀ (σ : Store Ref) (n : Nat), parts σ n .nil = .ok (some []) := fun _ _ => by
  simp [parts]
example : ∀ (σ : Store Ref) (n : Nat) (h t : P Ref), parts σ n (.cons h t) =
    match parts σ n t with
    | .ok (some xs) => .ok (some (h :: xs))
    | .ok none => .ok none
    | .error r => .error r := fun σ n _ t => by
  rw [parts]
  cases parts σ n t with
  | error _ => rfl
  | ok x => cases x <;> rfl
example : ∀ (σ : Store Ref) (n : Nat) (r : Ref), parts σ (n + 1) (.ref r) =
    match σ r with
    | some p => parts σ n p
    | none => .error r := fun σ _ r => by
  rw [parts]
  cases σ r <;> rfl
example : ∀ (σ : Store Ref) (r : Ref), parts σ 0 (.ref r) = .ok none := fun _ _ => by
  simp [parts]

-- What a session of any kind holds. These are the definitions, restated.
example : ∀ {σ : Store Ref} {r : Ref}, RootGood σ (.ref r) ↔
    ∃ p, σ r = some p ∧ Good pieceSize σ (opened pieceSize r p) := Iff.rfl
example : ∀ {σ : Store Ref} {k : P Ref} {d : Data}, StatusGood σ (.waiting k d) ↔
    Good pieceSize σ k := Iff.rfl
example : ∀ {σ : Store Ref} {cfg : LConfig}, CfgGood σ cfg ↔
    ∀ q ∈ cfg.procs, StatusGood σ q.status := Iff.rfl
example : ∀ {σ : Store Ref} {k : P Ref} {a : Data}, JobGood σ (.turn k a) ↔
    Good pieceSize σ k := Iff.rfl
example : ∀ {σ : Store Ref} {d : Doing}, DoingGood σ d ↔
    (∀ j ∈ d.jobs, JobGood σ j) ∧ (∀ st ∈ d.got, StatusGood σ st) ∧
      ∀ got cfg, (∀ st ∈ got, StatusGood σ st) → d.done got = some cfg → CfgGood σ cfg :=
  fun {_ _} => ⟨fun h => ⟨h.jobs, h.got, h.done⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩
example : ∀ {σ : Store Ref} {part : NodePart}, NodeGood σ part ↔
    CfgGood σ part.cfg ∧ ∀ d, part.doing = some d → DoingGood σ d :=
  fun {_ _} => ⟨fun h => ⟨h.cfg, h.doing⟩, fun h => ⟨h.1, h.2⟩⟩
example : ∀ {σ : Store Ref} {s : Session}, Held σ s ↔
    s.store.le σ ∧ PhaseHeld σ s.phase ∧ (∀ part, s.node = some part → NodeGood σ part) ∧
      s.written = #[] :=
  fun {_ _} => ⟨fun h => ⟨h.le, h.good, h.node, h.written⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩
example : ∀ {σ : Store Ref} {st : PState Ref}, PhaseHeld σ (.run st) ↔ GoodS pieceSize σ st :=
  Iff.rfl
example : ∀ {σ : Store Ref} {k : P Ref} {st : PState Ref}, PhaseHeld σ (.payload k st) ↔
    Good pieceSize σ k ∧ GoodS pieceSize σ st := Iff.rfl
example : ∀ {σ : Store Ref} {root : P Ref}, PhaseHeld σ (.opening root) ↔ RootGood σ root :=
  Iff.rfl
example : ∀ {σ : Store Ref} {root : P Ref}, PhaseHeld σ (.openingNode root) ↔ RootGood σ root :=
  Iff.rfl
example : ∀ {σ : Store Ref} {st : Status (P Ref) Final}, PhaseHeld σ (.landed st) ↔
    StatusGood σ st := Iff.rfl
-- On the phases of one turn it is `PhaseGood`, and a session of one turn is a
-- session.
example : ∀ {σ : Store Ref} {ph : Phase}, PhaseGood σ ph → PhaseHeld σ ph :=
  Surface.Keep.PhaseGood.held
example : ∀ {σ : Store Ref} {s : Session}, Inv σ s → Held σ s := Surface.Keep.Inv.held

-- Where a session can be after it was carried on: it still holds only such
-- references; or it saved a waiting function, a VM's state or a node, every
-- reference of which `cut` made; or it is over and stored nothing.
example : ∀ {σ : Store Ref} {s : Session}, Kept σ s ↔
    Held σ s ∨
    (∃ (s' : Session) (d : Data) (k : P Ref), Good pieceSize σ k ∧ s = s'.wait d k) ∨
    (∃ (s' : Session) (part : VmPart) (line : String) (status : P Ref),
      Good pieceSize σ (vmState part.seen status) ∧ s = s'.keepState part line status) ∨
    (∃ (s' : Session) (part : NodePart) (refused : Option (Nat × Op)),
      Good pieceSize σ (nodePiece part.seen part.cfg) ∧ s = s'.keepNode part refused) ∨
    (s.phase = .done ∧ s.written = #[]) :=
  fun {_ _} => ⟨fun h => by
      cases h with
      | holds h => exact .inl h
      | waits h => exact .inr (.inl ⟨_, _, _, h, rfl⟩)
      | state h => exact .inr (.inr (.inl ⟨_, _, _, _, h, rfl⟩))
      | node h => exact .inr (.inr (.inr (.inl ⟨_, _, _, h, rfl⟩)))
      | over a b => exact .inr (.inr (.inr (.inr ⟨a, b⟩))),
    fun h => by
      rcases h with h | ⟨_, _, _, h, rfl⟩ | ⟨_, _, _, _, h, rfl⟩ | ⟨_, _, _, h, rfl⟩ | ⟨a, b⟩
      · exact .holds h
      · exact .waits h
      · exact .state h
      · exact .node h
      · exact .over a b⟩

-- Reading a kept state and a kept node, on any part of the store, gives only
-- functions every reference of which `cut` made.
example : ∀ {σ σ' : Store Ref}, σ'.le σ → ∀ (n : Nat) {root : P Ref} {seen : List Data}
    {stands : Stands}, RootGood σ root → openState σ' n root = .ok (some (seen, stands)) →
    StandsGood σ stands := Surface.Keep.openState_good
example : ∀ {σ σ' : Store Ref}, σ'.le σ → ∀ (n : Nat) {root : P Ref} {seen : List Data}
    {cfg : LConfig}, RootGood σ root → openNode σ' n root = .ok (some (seen, cfg)) →
    CfgGood σ cfg := Surface.Keep.openNode_good

-- The runs an event needs take only functions the configuration held, and the
-- configuration it ends in holds those and where the runs ended.
example : ∀ {σ : Store Ref} {cfg : LConfig} {ev : Event} {jobs : List (Job (P Ref))}
    {done : List (Status (P Ref) Final) → Option LConfig}, CfgGood σ cfg →
    plan cfg ev = some (jobs, done) →
    (∀ j ∈ jobs, JobGood σ j) ∧
      ∀ got cfg', (∀ st ∈ got, StatusGood σ st) → done got = some cfg' → CfgGood σ cfg' :=
  Surface.Keep.plan_good

-- Carrying any session on.
example : ∀ {σ : Store Ref} (fuel : Nat) {s : Session}, Held σ s → Kept σ (advance fuel s) :=
  Surface.Keep.advance_kept

-- A VM and a node from a program: nothing is assumed.
example : ∀ {σ : Store Ref} (program log : ByteArray) (budget : Nat),
    Kept σ (vmStart program log budget) := Surface.Keep.vmStart_kept
example : ∀ {σ : Store Ref} (program log : ByteArray) (budget : Nat),
    Kept σ (nodeStart program log budget) := Surface.Keep.nodeStart_kept

-- A VM and a node from a kept root. `save_opened` gives the second hypothesis
-- for a root that saving gave; the first is `answer_turn`'s.
example : ∀ {σ : Store Ref} {root : String} {r : Ref}, unhex root = some r →
    (∃ p, σ r = some p ∧ Good pieceSize σ (opened pieceSize r p)) →
    ∀ (log : ByteArray) (budget : Nat), Kept σ (vmFrom root log budget) :=
  Surface.Keep.vmFrom_kept
example : ∀ {σ : Store Ref} {root : String} {r : Ref}, unhex root = some r →
    (∃ p, σ r = some p ∧ Good pieceSize σ (opened pieceSize r p)) →
    ∀ (log : ByteArray) (budget : Nat), Kept σ (nodeFrom root log budget) :=
  Surface.Keep.nodeFrom_kept

-- Supplying a piece to any session, under `give_turn`'s hypothesis.
example : ∀ {σ : Store Ref} {s : Session} {bytes : ByteArray}, Held σ s →
    (∀ r p, s.need = some r → readPiece bytes = .ok p →
      ∀ x q, (s.pieces.insert r p)[x]? = some q → σ x = some q) →
    Kept σ (give s bytes) :=
  Surface.Keep.give_kept

-- `restart_same_root` with `Made` taken apart. `Kept` gives the `Good` half of
-- what a session saved. That the piece stands for the state the log theorems
-- speak of, the `Unf` half, is still a hypothesis: nothing here says what a
-- session computes.
example : ∀ {size : Nat} {σ σ' : Store Ref} [Ops] {p : Term} {l₁ l₂ : List Entry}
    {s v v' : Vm Value Outcome},
    Logged sourceP p l₁ s → Replay source s (l₁ ++ l₂) v → Logged sourceP p (l₁ ++ l₂) v' →
    ∀ {a b : P Ref}, Good size σ a → Unf σ a (wholeState (v.map MP.injO MP.injV)) →
    Good size σ' b → Unf σ' b (wholeState (v'.map MP.injO MP.injV)) →
    (save size a).map (·.1) = (save size b).map (·.1) :=
  Surface.Keep.restart_root

-- A node as a whole piece, and the piece a session saves for it.
example : ∀ (n : MNode), wholeNode n =
    plist [Data.toP (.arr n.seen), Data.toP (.arr (n.cfg.names.map .nat)),
      plist (n.cfg.procs.map fun q =>
        plist [Data.toP (.arr (q.held.map .nat)), wholeStatus q.status])] := fun _ => rfl
example : ∀ (c : MValue) (d : Data),
    wholeStatus (.waiting c d) = plist [.nat 0, c.toP, d.toP] := fun _ _ => rfl
example : ∀ (v : MValue), wholeStatus (.finished (.value v)) = plist [.nat 1, v.toP] :=
  fun _ => rfl
example : ∀ (i : Nat), wholeStatus (.finished (.unbound i)) = plist [.nat 2, .nat i] :=
  fun _ => rfl
example : wholeStatus (.finished .wrong) = plist [.nat 3] := rfl
example : ∀ {size : Nat} {σ : Store Ref} {seen : List Data} {cfg : LConfig} {w : MConfig},
    cfg.names = w.names →
    All2 (fun q m => q.held = m.held ∧ StatusMade size σ q.status m.status) cfg.procs w.procs →
    Made size σ (nodePiece seen cfg) (wholeNode ⟨w, seen⟩) :=
  Surface.Keep.made_node

-- One node has one root, and a node kept after a first part of the log and
-- restarted on the whole log has the root a run of the whole log has.
example : ∀ {size : Nat} {σ σ' : Store Ref} {w : MNode} {a b : P Ref},
    Made size σ a (wholeNode w) → Made size σ' b (wholeNode w) →
    (save size a).map (·.1) = (save size b).map (·.1) :=
  Surface.Keep.node_same_root
example : ∀ {size : Nat} {σ σ' : Store Ref} [Ops] {p : Term} {l₁ l₂ : List Op}
    {s n n' : Node Value Outcome},
    Ran sourceP p l₁ s → Applied sourceP s (l₁ ++ l₂) n → Ran sourceP p (l₁ ++ l₂) n' →
    ∀ {a b : P Ref}, Made size σ a (wholeNode (n.map MP.injO MP.injV)) →
    Made size σ' b (wholeNode (n'.map MP.injO MP.injV)) →
    (save size a).map (·.1) = (save size b).map (·.1) :=
  Surface.Keep.node_restart_same_root
example : ∀ {size : Nat} {σ σ' : Store Ref} [Ops] {p : Term} {l₁ l₂ : List Op}
    {s n n' : Node Value Outcome},
    Ran sourceP p l₁ s → Applied sourceP s (l₁ ++ l₂) n → Ran sourceP p (l₁ ++ l₂) n' →
    ∀ {a b : P Ref}, Good size σ a → Unf σ a (wholeNode (n.map MP.injO MP.injV)) →
    Good size σ' b → Unf σ' b (wholeNode (n'.map MP.injO MP.injV)) →
    (save size a).map (·.1) = (save size b).map (·.1) :=
  Surface.Keep.node_restart_root

#print axioms Surface.Keep.parts
#print axioms Surface.Keep.parts_good
#print axioms Surface.Keep.openState_good
#print axioms Surface.Keep.openNode_good
#print axioms Surface.Keep.plan_good
#print axioms Surface.Keep.advance_kept
#print axioms Surface.Keep.vmStart_kept
#print axioms Surface.Keep.vmFrom_kept
#print axioms Surface.Keep.nodeStart_kept
#print axioms Surface.Keep.nodeFrom_kept
#print axioms Surface.Keep.give_kept
#print axioms Surface.Keep.restart_root
#print axioms Surface.Keep.made_node
#print axioms Surface.Keep.node_same_root
#print axioms Surface.Keep.node_restart_same_root
#print axioms Surface.Keep.node_restart_root
