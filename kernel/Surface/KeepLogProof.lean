import Surface.KeepProof
import Reflect.NodeProof

/-! A VM's and a node's session save only references that saving made.

    `Surface/KeepProof.lean` proves it for a session that runs one turn of a
    program. Here the same is proved for every session: a turn, a VM handling
    a log and a node applying one, begun from a program or from a kept root.
    In every phase the session holds only references that `cut` made
    (`Held`), and what it saves at the end, a waiting function, a VM's state
    or a node, is such a piece (`Kept`). So the root it reports is the root
    of the value held whole (`Wire.good_root`).

    What this does not say: that the piece saved stands for the state the log
    theorems speak of (`Reflect.Logged`, `Reflect.Ran`). That is still a
    hypothesis of `restart_root` and `node_restart_root`, as `Unf`; the half of
    `Made` that is about how the references were made is proved here.

    `full` is `partial` and nothing is known of it but its type. It gives
    data, so no reference comes out of it, and that is all that is used. -/

namespace Surface.Keep
open Reflect Wire

variable {σ σ' : Store Ref}

/-- Take the match in `h` apart and drop the cases `h` cannot be. -/
local macro "step " h:ident : tactic =>
  `(tactic| (split at $h:ident <;> try (simp at $h:ident; done)))

/-! ## Reading a kept state -/

/-- Following references gives a piece every reference of which was made by
    saving. -/
theorem chase_good_piece (hle : σ'.le σ) (n : Nat) {v k x : P Ref}
    (hg : Good pieceSize σ v) (h : chase σ' n v = .ok (k, x)) : Good pieceSize σ x := by
  induction n generalizing v with
  | zero =>
    cases v <;> simp only [chase, Except.ok.injEq, Prod.mk.injEq] at h <;> exact h.2 ▸ hg
  | succ n ih =>
    cases v with
    | ref r =>
      simp only [chase] at h
      cases hr : σ' r with
      | none => simp [hr] at h
      | some p =>
        obtain ⟨p', hr', hp'⟩ := good_ref hg
        cases (hle _ _ hr).symm.trans hr'
        cases p with
        | ref r' =>
          simp only [hr] at h
          exact ih hp' h
        | _ =>
          simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
          exact h.2 ▸ hp'
    | _ => simp only [chase, Except.ok.injEq, Prod.mk.injEq] at h; exact h.2 ▸ hg

/-- The parts of a list are pieces every reference of which was made by
    saving. -/
theorem parts_good (hle : σ'.le σ) : ∀ (n : Nat) (p : P Ref) {xs : List (P Ref)},
    Good pieceSize σ p → parts σ' n p = .ok (some xs) → ∀ x ∈ xs, Good pieceSize σ x := by
  intro n
  induction n with
  | zero =>
    intro p
    induction p with
    | nil => intro xs _ h; simp [parts] at h; subst h; simp
    | cons a b _ ihb =>
      intro xs hg h
      rw [good_cons] at hg
      unfold parts at h
      split at h
      · rename_i ys hys
        simp only [Except.ok.injEq, Option.some.injEq] at h
        subst h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hg.1
        · exact ihb hg.2 hys x hx
      · simp at h
      · simp at h
    | _ => intro xs _ h; simp [parts] at h
  | succ n ih =>
    intro p
    induction p with
    | nil => intro xs _ h; simp [parts] at h; subst h; simp
    | cons a b _ ihb =>
      intro xs hg h
      rw [good_cons] at hg
      unfold parts at h
      split at h
      · rename_i ys hys
        simp only [Except.ok.injEq, Option.some.injEq] at h
        subst h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hg.1
        · exact ihb hg.2 hys x hx
      · simp at h
      · simp at h
    | ref r =>
      intro xs hg h
      unfold parts at h
      obtain ⟨p', hr', hp'⟩ := good_ref hg
      split at h
      · rename_i p hr
        cases (hle _ _ hr).symm.trans hr'
        exact ih _ hp' h
      · simp at h
    | _ => intro xs _ h; simp [parts] at h

/-- The piece under a root, as `opened` holds it, has only references that
    saving made. A root is not always a reference `cut` would make inside a
    value (`Wire.save_opened`). -/
def RootGood (σ : Store Ref) : P Ref → Prop
  | .ref r => ∃ p, σ r = some p ∧ Good pieceSize σ (opened pieceSize r p)
  | _ => False

/-- The piece a root names has only references that saving made. -/
theorem RootGood.piece {r : Ref} (h : RootGood σ (.ref r)) :
    ∃ p, σ r = some p ∧ Good pieceSize σ p := by
  obtain ⟨p, hr, hp⟩ := h
  refine ⟨p, hr, ?_⟩
  rcases opened_cases (size := pieceSize) r p with e | e
  · rw [e] at hp; exact hp
  · rw [e] at hp
    obtain ⟨p', hr', hp'⟩ := good_ref hp
    cases hr.symm.trans hr'
    exact hp'

theorem RootGood.chase (hle : σ'.le σ) (n : Nat) {root k x : P Ref} (hg : RootGood σ root)
    (h : chase σ' n root = .ok (k, x)) : RootGood σ x ∨ Good pieceSize σ x := by
  cases root with
  | ref r =>
    obtain ⟨p, hr, hp⟩ := hg.piece
    cases n with
    | zero =>
      simp only [Surface.Keep.chase, Except.ok.injEq, Prod.mk.injEq] at h
      exact .inl (h.2 ▸ hg)
    | succ n =>
      simp only [Surface.Keep.chase] at h
      cases hr' : σ' r with
      | none => simp [hr'] at h
      | some p' =>
        cases (hle _ _ hr').symm.trans hr
        cases p with
        | ref r' =>
          simp only [hr'] at h
          exact .inr (chase_good_piece hle n hp h)
        | _ =>
          simp only [hr', Except.ok.injEq, Prod.mk.injEq] at h
          exact .inr (h.2 ▸ hp)
  | _ => exact hg.elim

theorem RootGood.parts (hle : σ'.le σ) (n : Nat) {root : P Ref} {xs : List (P Ref)}
    (hg : RootGood σ root) (h : parts σ' n root = .ok (some xs)) :
    ∀ x ∈ xs, Good pieceSize σ x := by
  cases root with
  | ref r =>
    obtain ⟨p, hr, hp⟩ := hg.piece
    cases n with
    | zero => simp [Surface.Keep.parts] at h
    | succ n =>
      unfold Surface.Keep.parts at h
      split at h
      · rename_i p' hr'
        cases (hle _ _ hr').symm.trans hr
        exact parts_good hle n _ hp h
      · simp at h
  | _ => exact hg.elim

/-- Where a kept VM's program stands holds only references that saving made. -/
def StandsGood (σ : Store Ref) : Stands → Prop
  | .waiting k => Good pieceSize σ k
  | _ => True

theorem openState_good (hle : σ'.le σ) (n : Nat) {root : P Ref} {seen : List Data}
    {stands : Stands} (hg : RootGood σ root)
    (h : openState σ' n root = .ok (some (seen, stands))) : StandsGood σ stands := by
  unfold openState at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i v hv
    obtain ⟨k, top⟩ := v
    simp only at h
    iterate 11 step h
    rename_i seenP rest _ _ seen0 hfull _ _ _ statusP last hrest _ _ _ _ _ _ _ tagP body hstatus
      _ vt htag _ vb hbody
    have h0 : Good pieceSize σ (.cons seenP rest) := (hg.chase hle n hv).resolve_left (fun x => x)
    rw [good_cons] at h0
    have h1 := chase_good_piece hle n h0.2 hrest
    rw [good_cons] at h1
    have h2 := chase_good_piece hle n h1.1 hstatus
    rw [good_cons] at h2
    have h3 : Good pieceSize σ vb.snd := chase_good_piece hle n h2.2 hbody
    split at h
    · rename_i k last' _ hk
      rw [hk, good_cons] at h3
      iterate 4 step h
      rename_i hheld
      simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact chase_good hle n h3.1 hheld
    all_goals repeat step h
    all_goals first
      | (simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨_, rfl⟩ := h
         trivial)
      | (simp at h; done)

/-! ## A node's processes -/

/-- Where a process stands holds only references that saving made. -/
def StatusGood (σ : Store Ref) : Status (P Ref) Final → Prop
  | .waiting k _ => Good pieceSize σ k
  | .finished _ => True

def ProcsGood (σ : Store Ref) (procs : List (Proc (P Ref) Final)) : Prop :=
  ∀ q ∈ procs, StatusGood σ q.status

/-- Every function a process of the configuration waits with holds only
    references that saving made. -/
def CfgGood (σ : Store Ref) (cfg : LConfig) : Prop := ProcsGood σ cfg.procs

def JobGood (σ : Store Ref) : Job (P Ref) → Prop
  | .turn k _ => Good pieceSize σ k
  | .start _ => True

/-- An event part way through: the runs to do, the statuses got, and every
    configuration the event can end in from such statuses. -/
structure DoingGood (σ : Store Ref) (d : Doing) : Prop where
  jobs : ∀ j ∈ d.jobs, JobGood σ j
  got : ∀ st ∈ d.got, StatusGood σ st
  done : ∀ got cfg, (∀ st ∈ got, StatusGood σ st) → d.done got = some cfg → CfgGood σ cfg

structure NodeGood (σ : Store Ref) (part : NodePart) : Prop where
  cfg : CfgGood σ part.cfg
  doing : ∀ d, part.doing = some d → DoingGood σ d

theorem openStatus_good (hle : σ'.le σ) (n : Nat) {p : P Ref} {st : Status (P Ref) Final}
    (hg : Good pieceSize σ p) (h : openStatus σ' n p = .ok (some st)) : StatusGood σ st := by
  unfold openStatus at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' step h
  all_goals (simp only [Except.ok.injEq, Option.some.injEq] at h; subst h)
  all_goals first | trivial | skip
  rename_i tag a b hparts _ _ _ _ _ held _ _ _ hheld _ _ _ _
  exact chase_good hle n (parts_good hle n p hg hparts a (by simp)) hheld

theorem openProcs_good (hle : σ'.le σ) (n : Nat) : ∀ (qs : List (P Ref))
    {procs : List (Proc (P Ref) Final)}, (∀ q ∈ qs, Good pieceSize σ q) →
    openProcs σ' n qs = .ok (some procs) → ProcsGood σ procs
  | [], procs, _, h => by
    simp only [openProcs, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
    subst h
    intro q hq
    simp at hq
  | q :: qs, procs, hg, h => by
    unfold openProcs at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    repeat' step h
    rename_i heldP statusP hparts _ _ _ _ _ _ _ _ _ status hstatus _ _ rest hrest
    simp only [Except.ok.injEq, Option.some.injEq] at h
    subst h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact openStatus_good hle n
        (parts_good hle n q (hg q (by simp)) hparts statusP (by simp)) hstatus
    · exact openProcs_good hle n qs (fun y hy => hg y (List.mem_cons_of_mem _ hy)) hrest x hx

theorem openNode_good (hle : σ'.le σ) (n : Nat) {root : P Ref} {seen : List Data} {cfg : LConfig}
    (hg : RootGood σ root) (h : openNode σ' n root = .ok (some (seen, cfg))) : CfgGood σ cfg := by
  unfold openNode at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' step h
  rename_i seenP namesP procsP hroot _ _ _ _ _ _ _ _ _ _ _ _ _ ps hps _ _ rest hrest
  simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  exact openProcs_good hle n ps
    (parts_good hle n procsP (hg.parts hle n hroot procsP (by simp)) hps) hrest

/-! ## What an event leaves -/

theorem ProcsGood.waiting {procs : List (Proc (P Ref) Final)} (h : ProcsGood σ procs) {i : Nat}
    {k : P Ref} {d : Data} {held : List Nat} (hi : procs[i]? = some ⟨.waiting k d, held⟩) :
    Good pieceSize σ k :=
  h _ (List.mem_of_getElem? hi)

theorem ProcsGood.set {procs : List (Proc (P Ref) Final)} (h : ProcsGood σ procs) (i : Nat)
    {st : Status (P Ref) Final} (held : List Nat) (hst : StatusGood σ st) :
    ProcsGood σ (procs.set i ⟨st, held⟩) := by
  intro q hq
  rcases List.mem_or_eq_of_mem_set hq with hq | rfl
  · exact h q hq
  · exact hst

theorem ProcsGood.append {a b : List (Proc (P Ref) Final)} (ha : ProcsGood σ a)
    (hb : ProcsGood σ b) : ProcsGood σ (a ++ b) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact ha q hq
  · exact hb q hq

/-- The runs an event needs take only functions the configuration held, and
    the configuration the event ends in holds those and where the runs
    ended. -/
theorem plan_good {cfg : LConfig} {ev : Event} {jobs : List (Job (P Ref))}
    {done : List (Status (P Ref) Final) → Option LConfig} (hc : CfgGood σ cfg)
    (h : plan cfg ev = some (jobs, done)) :
    (∀ j ∈ jobs, JobGood σ j) ∧
      ∀ got cfg', (∀ st ∈ got, StatusGood σ st) → done got = some cfg' → CfgGood σ cfg' := by
  have hw : ∀ (i : Nat) (k : P Ref) (d : Data) (held : List Nat),
      cfg.procs[i]? = some ⟨.waiting k d, held⟩ → Good pieceSize σ k :=
    fun _ _ _ _ hi => ProcsGood.waiting hc hi
  cases ev <;> simp only [plan] at h <;> repeat' step h
  all_goals
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, ?_⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, JobGood,
        true_and]
      first
        | exact hw _ _ _ _ (by assumption)
        | exact ⟨hw _ _ _ _ (by assumption), hw _ _ _ _ (by assumption)⟩
    · intro got cfg' hgot hd
      dsimp only at hd
      split at hd
      · simp only [Option.some.injEq] at hd
        subst hd
        simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hgot
        first
          | exact ProcsGood.set hc _ _ hgot
          | exact (ProcsGood.set hc _ _ hgot.2).append
              (by intro q hq; simp only [List.mem_singleton] at hq; subst hq; exact hgot.1)
          | exact (ProcsGood.set hc _ _ hgot.1).set _ _ hgot.2
      · simp at hd

/-! ## What is saved -/

theorem plist_good {xs : List (P Ref)} (h : ∀ x ∈ xs, Good pieceSize σ x) :
    Good pieceSize σ (plist xs) := by
  induction xs with
  | nil => exact good_nil
  | cons x xs ih =>
    exact good_cons.mpr ⟨h x (by simp), ih fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

theorem statusPiece_good {st : Status (P Ref) Final} (h : StatusGood σ st) :
    Good pieceSize σ (statusPiece st) := by
  cases st with
  | waiting k d => simpa [statusPiece, plist, StatusGood] using h
  | finished f => cases f <;> simp [statusPiece, plist]

/-- A node whose waiting functions hold only references that saving made is
    saved as a piece that holds only such references. -/
theorem nodePiece_good (seen : List Data) {cfg : LConfig} (h : CfgGood σ cfg) :
    Good pieceSize σ (nodePiece seen cfg) := by
  refine plist_good fun x hx => ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact good_data _
  · exact good_data _
  · refine plist_good fun y hy => ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
    refine plist_good fun z hz => ?_
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · exact good_data _
    · exact statusPiece_good (h q hq)

/-- A VM's state whose status piece holds only references that saving made. -/
theorem vmState_good (seen : List Data) {status : P Ref} (h : Good pieceSize σ status) :
    Good pieceSize σ (vmState seen status) :=
  good_cons.mpr ⟨good_data _, good_cons.mpr ⟨h, good_nil⟩⟩

/-! ## Every session -/

/-- Every reference a phase holds was made by saving. On the phases of one
    turn this is `PhaseGood`. -/
def PhaseHeld (σ : Store Ref) : Phase → Prop
  | .run st => GoodS pieceSize σ st
  | .classify v => Good pieceSize σ v
  | .payload k st => Good pieceSize σ k ∧ GoodS pieceSize σ st
  | .ask k _ => Good pieceSize σ k
  | .result _ => True
  | .resuming r _ => ∃ p, σ r = some p ∧ Good pieceSize σ (opened pieceSize r p)
  | .opening root => RootGood σ root
  | .openingNode root => RootGood σ root
  | .landed st => StatusGood σ st
  | .step => True
  | .done => True

/-- A session, of any kind: what it holds is part of `σ`, every reference in
    its phase and in its node was made by saving, and it has stored nothing
    yet. A VM's part holds data only. -/
structure Held (σ : Store Ref) (s : Session) : Prop where
  le : s.store.le σ
  good : PhaseHeld σ s.phase
  node : ∀ part, s.node = some part → NodeGood σ part
  written : s.written = #[]

/-- Where a session can be after it was carried on. -/
inductive Kept (σ : Store Ref) : Session → Prop where
  /-- It goes on, or needs a piece, and still holds only such references. -/
  | holds {s : Session} : Held σ s → Kept σ s
  /-- A turn ended in a request and saved the function `k`. -/
  | waits {s : Session} {d : Data} {k : P Ref} : Good pieceSize σ k → Kept σ (s.wait d k)
  /-- A VM handled its log and saved its state. -/
  | state {s : Session} {part : VmPart} {line : String} {status : P Ref} :
      Good pieceSize σ (vmState part.seen status) → Kept σ (s.keepState part line status)
  /-- A node applied its log, or met an op that cannot happen, and was saved. -/
  | node {s : Session} {part : NodePart} {refused : Option (Nat × Op)} :
      Good pieceSize σ (nodePiece part.seen part.cfg) → Kept σ (s.keepNode part refused)
  /-- It is over and stored nothing. -/
  | over {s : Session} : s.phase = .done → s.written = #[] → Kept σ s

theorem PhaseGood.held {ph : Phase} (h : PhaseGood σ ph) : PhaseHeld σ ph := by
  cases ph <;> first | exact h | exact h.elim

/-- A session of one turn is a session. -/
theorem Inv.held {s : Session} (h : Inv σ s) : Held σ s :=
  ⟨h.le, h.good.held, fun _ e => (by rw [h.node] at e; cases e), h.written⟩

variable {s : Session}

theorem ended_kept (hw : s.written = #[]) (line : String) {status : P Ref}
    (hst : Good pieceSize σ status) : Kept σ (s.ended line status) := by
  unfold Session.ended
  split
  · exact .over rfl hw
  · exact .state (vmState_good _ hst)

theorem stopped_kept (hw : s.written = #[]) (st : PState Ref) : Kept σ (s.stopped st) := by
  unfold Session.stopped
  split
  · exact ended_kept hw _ (by simp)
  · exact ended_kept hw _ (by simp)
  · exact .over rfl hw
  · exact .over rfl hw

/-- Carrying a session on keeps the invariant, until it saves a piece every
    reference of which was made by saving, or ends with nothing stored. -/
theorem advance_kept : ∀ (fuel : Nat) {s : Session}, Held σ s → Kept σ (advance fuel s)
  | 0, s, h => .over rfl h.written
  | fuel + 1, s, h => by
    obtain ⟨hle, hg, hnode, hw⟩ := h
    have hg' := hg
    cases hph : s.phase with
    | run st =>
      rw [hph] at hg'
      simp only [advance, hph]
      cases hst : steps s.store s.left st with
      | mk out left =>
        have good := steps_good hle s.left hg' hst
        split
        · rename_i r st' left' heq
          cases heq
          exact .holds ⟨hle, good.2 _ _ rfl, hnode, hw⟩
        · rename_i v _ heq
          cases heq
          exact advance_kept fuel ⟨hle, good.1 _ rfl, hnode, hw⟩
        · split
          · exact advance_kept fuel ⟨hle, trivial, hnode, hw⟩
          · exact advance_kept fuel ⟨hle, trivial, hnode, hw⟩
          · exact stopped_kept hw _
    | classify v =>
      rw [hph] at hg'
      simp only [advance, hph]
      split
      · exact .holds ⟨hle, hg', hnode, hw⟩
      · rename_i k _ _ heq
        have hk : Good pieceSize σ k := chase_good hle _ hg' heq
        exact advance_kept fuel ⟨hle, ⟨hk, by simp [GoodS, hk]⟩, hnode, hw⟩
      · exact advance_kept fuel ⟨hle, trivial, hnode, hw⟩
    | payload k st =>
      rw [hph] at hg'
      simp only [advance, hph]
      cases hst : steps s.store s.left st with
      | mk out left =>
        have good := steps_good hle s.left hg'.2 hst
        split
        · rename_i r st' left' heq
          cases heq
          exact .holds ⟨hle, ⟨hg'.1, good.2 _ _ rfl⟩, hnode, hw⟩
        · rename_i v _ heq
          cases heq
          exact advance_kept fuel ⟨hle, hg'.1, hnode, hw⟩
        · split
          · exact advance_kept fuel ⟨hle, trivial, hnode, hw⟩
          · exact advance_kept fuel ⟨hle, trivial, hnode, hw⟩
          · exact stopped_kept hw _
    | ask k p =>
      rw [hph] at hg'
      have hk : Good pieceSize σ k := hg'
      simp only [advance, hph]
      split
      · exact .holds ⟨hle, hg', hnode, hw⟩
      · split
        · exact advance_kept fuel ⟨hle, hg', hnode, hw⟩
        · exact .waits hg'
        · split
          · exact .state (vmState_good _ (by simp [hk]))
          · exact advance_kept fuel ⟨hle, by simp [PhaseHeld, GoodS, hk], hnode, hw⟩
      · split
        · exact advance_kept fuel ⟨hle, trivial, hnode, hw⟩
        · exact ended_kept hw _ (by simp)
    | result p =>
      simp only [advance, hph]
      split
      · exact .holds ⟨hle, trivial, hnode, hw⟩
      · split
        · exact advance_kept fuel ⟨hle, trivial, hnode, hw⟩
        · exact ended_kept hw _ (by simp)
      · exact .over rfl hw
    | resuming r d =>
      rw [hph] at hg'
      simp only [advance, hph]
      obtain ⟨p, hr, hp⟩ := hg'
      split
      · exact .holds ⟨hle, ⟨p, hr, hp⟩, hnode, hw⟩
      · rename_i p' heq
        cases (hle _ _ heq).symm.trans hr
        exact advance_kept fuel ⟨hle, by simp [PhaseHeld, GoodS, hp], hnode, hw⟩
    | opening root =>
      rw [hph] at hg'
      simp only [advance, hph]
      split
      · exact .holds ⟨hle, hg', hnode, hw⟩
      · exact .over rfl hw
      · rename_i seen stands heq
        have hs := openState_good hle _ hg' heq
        split
        · have hk : Good pieceSize σ _ := hs
          exact advance_kept fuel ⟨hle, ⟨hk, by simp [GoodS, hk]⟩, hnode, hw⟩
        · exact advance_kept fuel ⟨hle, trivial, hnode, hw⟩
        · refine stopped_kept ?_ _
          exact hw
        · refine stopped_kept ?_ _
          exact hw
    | openingNode root =>
      rw [hph] at hg'
      simp only [advance, hph]
      split
      · exact .holds ⟨hle, hg', hnode, hw⟩
      · rename_i seen cfg part heq hpart
        refine advance_kept fuel ⟨hle, trivial, ?_, hw⟩
        intro _ e
        cases e
        exact ⟨openNode_good hle _ hg' heq, (hnode _ hpart).doing⟩
      · exact .over rfl hw
    | landed st =>
      rw [hph] at hg'
      simp only [advance, hph]
      split
      · rename_i part hpart
        split
        · rename_i d hd
          have dg := (hnode _ hpart).doing d hd
          refine advance_kept fuel ⟨hle, trivial, ?_, hw⟩
          intro _ e
          cases e
          refine ⟨(hnode _ hpart).cfg, ?_⟩
          intro _ e
          cases e
          refine ⟨dg.jobs, ?_, dg.done⟩
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact dg.got x hx
          · simp only [List.mem_singleton] at hx
            exact hx ▸ hg'
        · exact .over rfl hw
      · exact .over rfl hw
    | step =>
      simp only [advance, hph]
      split
      · exact .over rfl hw
      · rename_i part hpart
        have ng := hnode _ hpart
        split
        · rename_i d hd
          have dg := ng.doing d hd
          split
          · rename_i job jobs hjobs
            have hjob : JobGood σ job := dg.jobs job (by rw [hjobs]; simp)
            refine advance_kept fuel ⟨hle, ?_, ?_, hw⟩
            · cases job with
              | turn k a => simp only [PhaseHeld, GoodS]; simpa [JobGood] using hjob
              | start t => exact goodS_whole (size := pieceSize) (σ := σ) (load (compile t))
            · intro _ e
              cases e
              refine ⟨ng.cfg, ?_⟩
              intro _ e
              cases e
              exact ⟨fun j hj => dg.jobs j (by rw [hjobs]; exact List.mem_cons_of_mem _ hj),
                dg.got, dg.done⟩
          · split
            · exact .over rfl hw
            · rename_i cfg hcfg
              have hc := dg.done _ _ dg.got hcfg
              refine advance_kept fuel ⟨hle, trivial, ?_, hw⟩
              intro _ e
              cases e
              split <;> exact ⟨hc, fun _ e => by cases e⟩
        · split
          · exact .node (nodePiece_good _ ng.cfg)
          · rename_i o rest _
            split
            · exact .node (nodePiece_good _ ng.cfg)
            · rename_i jobs done hplan
              have pg := plan_good ng.cfg hplan
              refine advance_kept fuel ⟨hle, trivial, ?_, hw⟩
              intro _ e
              cases e
              refine ⟨ng.cfg, ?_⟩
              intro _ e
              cases e
              exact ⟨pg.1, fun _ h => by simp at h, pg.2⟩
    | done =>
      simp only [advance, hph]
      exact .over hph hw

/-! ## Where a session begins -/

/-- A VM begun from its program: it holds no reference. -/
theorem vmStart_kept (program log : ByteArray) (budget : Nat) :
    Kept σ (vmStart program log budget) := by
  unfold vmStart
  split
  · exact .over rfl rfl
  · split
    · exact .over rfl rfl
    · rename_i t _ _ _ _
      have hg : PhaseHeld σ (Phase.run (load (compile t)).toP) := by
        simp only [PhaseHeld]
        exact goodS_whole _
      exact advance_kept _
        ⟨fun r p h => (by simp [Session.store] at h), hg, fun _ e => (by cases e), rfl⟩

/-- A VM begun from a kept state, when the piece under the root, as a turn
    holds it, has only references that saving made. `Wire.save_opened` says it
    has, for a root saving gave. -/
theorem vmFrom_kept {root : String} {r : Ref} (hr : unhex root = some r)
    (h : ∃ p, σ r = some p ∧ Good pieceSize σ (opened pieceSize r p)) (log : ByteArray)
    (budget : Nat) : Kept σ (vmFrom root log budget) := by
  unfold vmFrom
  simp only [hr]
  split
  · exact .over rfl rfl
  · exact advance_kept _
      ⟨fun r p h => (by simp [Session.store] at h), h, fun _ e => (by cases e), rfl⟩

/-- A node begun from its program: it holds no reference. -/
theorem nodeStart_kept (program log : ByteArray) (budget : Nat) :
    Kept σ (nodeStart program log budget) := by
  unfold nodeStart
  split
  · exact .over rfl rfl
  · split
    · exact .over rfl rfl
    · refine advance_kept _
        ⟨fun r p h => (by simp [Session.store] at h), trivial, ?_, rfl⟩
      intro _ e
      cases e
      refine ⟨fun _ h => (by simp at h), ?_⟩
      intro _ e
      cases e
      refine ⟨fun j hj => ?_, fun _ h => (by simp at h), ?_⟩
      · simp only [List.mem_singleton] at hj
        subst hj
        trivial
      · intro got cfg hgot hd
        dsimp only at hd
        split at hd
        · simp only [Option.some.injEq] at hd
          subst hd
          intro q hq
          simp only [List.mem_singleton] at hq
          subst hq
          exact hgot _ (by simp)
        · simp at hd

/-- A node begun from a kept one, when the piece under the root has only
    references that saving made. -/
theorem nodeFrom_kept {root : String} {r : Ref} (hr : unhex root = some r)
    (h : ∃ p, σ r = some p ∧ Good pieceSize σ (opened pieceSize r p)) (log : ByteArray)
    (budget : Nat) : Kept σ (nodeFrom root log budget) := by
  unfold nodeFrom
  simp only [hr]
  split
  · exact .over rfl rfl
  · refine advance_kept _
      ⟨fun r p h => (by simp [Session.store] at h), h, ?_, rfl⟩
    intro _ e
    cases e
    exact ⟨fun _ h => (by simp at h), fun _ e => (by cases e)⟩

/-- Supplying a piece to any session. The hypothesis is `give_turn`'s: the
    pieces the session holds, with the piece read from the bytes among them,
    are still part of `σ`. -/
theorem give_kept {bytes : ByteArray} (h : Held σ s)
    (hin : ∀ r p, s.need = some r → readPiece bytes = .ok p →
      ∀ x q, (s.pieces.insert r p)[x]? = some q → σ x = some q) :
    Kept σ (give s bytes) := by
  unfold give
  split
  · exact .holds h
  · rename_i r hneed
    split
    · exact .over rfl rfl
    · split
      · exact .over rfl rfl
      · rename_i p hread
        exact advance_kept _
          ⟨fun x q hx => hin r p hneed hread x q hx, h.good, h.node, h.written⟩

/-! ## The root of what was saved -/

variable {size : Nat}

section
variable [Ops]

/-- `restart_same_root`, with `Made` taken apart: `Good`, which `Kept` gives
    of what a session saved, and `Unf`, that the piece stands for the state.
    The second is not proved of a session. -/
theorem restart_root {p : Term} {l₁ l₂ : List Entry} {s v v' : Vm Value Outcome}
    (h : Logged sourceP p l₁ s) (hr : Replay source s (l₁ ++ l₂) v)
    (hl : Logged sourceP p (l₁ ++ l₂) v') {a b : P Ref}
    (ga : Good size σ a) (ua : Unf σ a (wholeState (v.map MP.injO MP.injV)))
    (gb : Good size σ' b) (ub : Unf σ' b (wholeState (v'.map MP.injO MP.injV))) :
    (save size a).map (·.1) = (save size b).map (·.1) :=
  restart_same_root h hr hl (made_iff.mpr ⟨ga, ua⟩) (made_iff.mpr ⟨gb, ub⟩)

end

/-- Where a process stands, as the whole piece a session saves for it. -/
def wholeStatus : Status MValue MOutcome → P Ref
  | .waiting c d => plist [.nat 0, c.toP, d.toP]
  | .finished (.value v) => plist [.nat 1, v.toP]
  | .finished (.unbound i) => plist [.nat 2, .nat i]
  | .finished .wrong => plist [.nat 3]

/-- A node as a whole piece, with no reference in it. -/
def wholeNode (n : MNode) : P Ref :=
  plist [Data.toP (.arr n.seen), Data.toP (.arr (n.cfg.names.map .nat)),
    plist (n.cfg.procs.map fun q =>
      plist [Data.toP (.arr (q.held.map .nat)), wholeStatus q.status])]

/-- A session's status stands for a process's: the same payload and result,
    and a function that stands for the process's function. -/
def StatusMade (size : Nat) (σ : Store Ref) :
    Status (P Ref) Final → Status MValue MOutcome → Prop
  | .waiting k d, .waiting c d' => d = d' ∧ Made size σ k c.toP
  | .finished (.value d), .finished (.value v) => v = .data d
  | .finished (.unbound i), .finished (.unbound j) => i = j
  | .finished .wrong, .finished .wrong => True
  | _, _ => False

theorem made_status {st : Status (P Ref) Final} {w : Status MValue MOutcome}
    (h : StatusMade size σ st w) : Made size σ (statusPiece st) (wholeStatus w) := by
  cases st with
  | waiting k d =>
    cases w with
    | waiting c d' =>
      obtain ⟨rfl, hk⟩ := h
      exact .cons .nat (.cons hk (.cons (Made.data _) .nil))
    | finished _ => exact h.elim
  | finished f =>
    cases w with
    | waiting _ _ => cases f <;> exact h.elim
    | finished o =>
      cases f <;> cases o <;> first
        | exact h.elim
        | (cases h; exact .cons .nat (.cons (Made.data _) .nil))
        | (cases h; exact .cons .nat (.cons .nat .nil))
        | exact .cons .nat .nil

theorem made_procs : ∀ {qs : List (Proc (P Ref) Final)} {ws : List (Proc MValue MOutcome)},
    All2 (fun q w => q.held = w.held ∧ StatusMade size σ q.status w.status) qs ws →
    Made size σ
      (plist (qs.map fun q => plist [Data.toP (.arr (q.held.map .nat)), statusPiece q.status]))
      (plist (ws.map fun q => plist [Data.toP (.arr (q.held.map .nat)), wholeStatus q.status]))
  | _, _, .nil => .nil
  | _, _, .cons h rest => by
    refine .cons ?_ (made_procs rest)
    simp only [plist, List.foldr]
    rw [h.1]
    exact .cons (Made.data _) (.cons (made_status h.2) .nil)

/-- A session's node piece stands for the node when each of its processes
    stands for the node's. The identifiers and the names are held whole. -/
theorem made_node {seen : List Data} {cfg : LConfig} {w : MConfig}
    (hn : cfg.names = w.names)
    (hp : All2 (fun q m => q.held = m.held ∧ StatusMade size σ q.status m.status)
      cfg.procs w.procs) :
    Made size σ (nodePiece seen cfg) (wholeNode ⟨w, seen⟩) :=
  .cons (Made.data _) (.cons (hn ▸ Made.data _) (.cons (made_procs hp) .nil))

/-- One node has one root. -/
theorem node_same_root {w : MNode} {a b : P Ref} (ha : Made size σ a (wholeNode w))
    (hb : Made size σ' b (wholeNode w)) :
    (save size a).map (·.1) = (save size b).map (·.1) :=
  same_root ha hb

section
variable [Ops]

/-- A node kept after a first part of the log and restarted on the whole log
    is saved under the root a run of the whole log from the start is saved
    under. `a` is what the restarted session holds at the end and `b` what the
    other holds; the stores may differ. -/
theorem node_restart_same_root {p : Term} {l₁ l₂ : List Op} {s n n' : Node Value Outcome}
    (h : Ran sourceP p l₁ s) (hr : Applied sourceP s (l₁ ++ l₂) n)
    (hl : Ran sourceP p (l₁ ++ l₂) n') {a b : P Ref}
    (ha : Made size σ a (wholeNode (n.map MP.injO MP.injV)))
    (hb : Made size σ' b (wholeNode (n'.map MP.injO MP.injV))) :
    (save size a).map (·.1) = (save size b).map (·.1) := by
  cases node_deterministic ((node_restart h).mp hr) hl
  exact same_root ha hb

/-- The same, with `Made` taken apart as in `restart_root`. -/
theorem node_restart_root {p : Term} {l₁ l₂ : List Op} {s n n' : Node Value Outcome}
    (h : Ran sourceP p l₁ s) (hr : Applied sourceP s (l₁ ++ l₂) n)
    (hl : Ran sourceP p (l₁ ++ l₂) n') {a b : P Ref}
    (ga : Good size σ a) (ua : Unf σ a (wholeNode (n.map MP.injO MP.injV)))
    (gb : Good size σ' b) (ub : Unf σ' b (wholeNode (n'.map MP.injO MP.injV))) :
    (save size a).map (·.1) = (save size b).map (·.1) :=
  node_restart_same_root h hr hl (made_iff.mpr ⟨ga, ua⟩) (made_iff.mpr ⟨gb, ub⟩)

end

end Surface.Keep
