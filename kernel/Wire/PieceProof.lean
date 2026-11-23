import Wire.Piece
import Reflect.StoreProof

/-! Saving is a function of the value.

    `cut` leaves a reference alone, so what it gives depends on which parts of
    a partial piece are references. This file says when that does not matter:
    when every reference in the piece is the one `cut` gives the value the
    reference stands for (`Made`). Under that condition a partial piece is cut
    to what the whole value is cut to (`Made.norm_eq`), and saved under the root
    the whole value is saved under (`same_root`). `cut` makes only such
    references (`Made.after_cut`), and the lazy machine makes none (`lstep_good`).

    The hash is used as the function it is. Nothing is assumed of it: that
    equal values get one root does not need different pieces to have different
    hashes. -/

namespace Wire
open Reflect

/-- A piece that was stored: its reference, its bytes, and the piece. -/
abbrev Stored := Ref × ByteArray × P Ref

/-- What the saver holds for a list of stored pieces. -/
def bytesOf (w : List Stored) : Array (Ref × ByteArray) := (w.map fun t => (t.1, t.2.1)).toArray

/-- What `kept` leaves where `p` was. -/
def keptv (size : Nat) (p : P Ref) : Option (P Ref) :=
  (pieceBytes p).map fun b => if b.size ≤ size then p else .ref (Blake3.hash b)

/-- What `kept` stores. -/
def keptw (size : Nat) (p : P Ref) : List Stored :=
  match pieceBytes p with
  | some b => if b.size ≤ size then [] else [(Blake3.hash b, b, p)]
  | none => []

/-- What `cut` leaves where `p` was: `cut` without the pieces it stores. -/
def norm (size : Nat) : P Ref → Option (P Ref)
  | .nat n => keptv size (.nat n)
  | .name n => keptv size (.name n)
  | .text t => keptv size (.text t)
  | .nil => keptv size .nil
  | .ref r => some (.ref r)
  | .cons h t =>
      match norm size h, norm size t with
      | some h', some t' => keptv size (.cons h' t')
      | _, _ => none
  | .closure c e =>
      match norm size e with
      | some e' => keptv size (.closure c e')
      | none => none

/-- The pieces `cut` stores, oldest first. -/
def wrote (size : Nat) : P Ref → List Stored
  | .nat n => keptw size (.nat n)
  | .name n => keptw size (.name n)
  | .text t => keptw size (.text t)
  | .nil => keptw size .nil
  | .ref _ => []
  | .cons h t =>
      match norm size h, norm size t with
      | some h', some t' => wrote size h ++ wrote size t ++ keptw size (.cons h' t')
      | _, _ => []
  | .closure c e =>
      match norm size e with
      | some e' => wrote size e ++ keptw size (.closure c e')
      | none => []

theorem bytesOf_append (acc : Array (Ref × ByteArray)) (a b : List Stored) :
    acc ++ bytesOf (a ++ b) = acc ++ bytesOf a ++ bytesOf b := by
  simp [bytesOf, Array.append_assoc]

theorem kept_run (size : Nat) (p : P Ref) (acc : Array (Ref × ByteArray)) :
    (kept size p).run acc = (keptv size p).map fun c => (c, acc ++ bytesOf (keptw size p)) := by
  unfold kept keptv keptw stored bytesOf
  cases h : pieceBytes p with
  | none => simp [StateT.run, bind, StateT.bind, liftM, monadLift, MonadLift.monadLift, StateT.lift]
  | some b =>
    by_cases hb : b.size ≤ size
    · simp [StateT.run, bind, StateT.bind, liftM, monadLift, MonadLift.monadLift, StateT.lift, hb,
        pure, StateT.pure]
    · simp [StateT.run, bind, StateT.bind, liftM, monadLift, MonadLift.monadLift, StateT.lift, hb,
        pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

/-- `cut` gives `norm` and stores `wrote`, after whatever was stored before. -/
theorem cut_run (size : Nat) : ∀ (p : P Ref) (acc : Array (Ref × ByteArray)),
    (cut size p).run acc = (norm size p).map fun c => (c, acc ++ bytesOf (wrote size p))
  | .nat n, acc => by simp [cut, norm, wrote, kept_run]
  | .name n, acc => by simp [cut, norm, wrote, kept_run]
  | .text t, acc => by simp [cut, norm, wrote, kept_run]
  | .nil, acc => by simp [cut, norm, wrote, kept_run]
  | .ref r, acc => by simp [cut, norm, wrote, bytesOf, pure, StateT.pure, StateT.run]
  | .cons h t, acc => by
      simp only [cut, norm, wrote, StateT.run_bind, cut_run size h]
      cases hh : norm size h with
      | none => simp
      | some h' =>
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, cut_run size t]
        cases ht : norm size t with
        | none => simp
        | some t' => simp [kept_run, bytesOf_append]
  | .closure c e, acc => by
      simp only [cut, norm, wrote, StateT.run_bind, cut_run size e]
      cases he : norm size e with
      | none => simp
      | some e' => simp [kept_run, bytesOf_append]

/-- Every stored piece is under the hash of its own bytes. -/
theorem keptw_named {size : Nat} {p : P Ref} {t : Stored} (h : t ∈ keptw size p) :
    pieceBytes t.2.2 = some t.2.1 ∧ t.1 = Blake3.hash t.2.1 := by
  unfold keptw at h
  split at h
  · rename_i b hb
    split at h
    · simp at h
    · simp at h; subst h; exact ⟨hb, rfl⟩
  · simp at h

theorem wrote_named {size : Nat} : ∀ {p : P Ref} {t : Stored}, t ∈ wrote size p →
    pieceBytes t.2.2 = some t.2.1 ∧ t.1 = Blake3.hash t.2.1
  | .nat _, _, h => keptw_named (by simpa [wrote] using h)
  | .name _, _, h => keptw_named (by simpa [wrote] using h)
  | .text _, _, h => keptw_named (by simpa [wrote] using h)
  | .nil, _, h => keptw_named (by simpa [wrote] using h)
  | .ref _, _, h => by simp [wrote] at h
  | .cons a b, _, h => by
      simp only [wrote] at h
      split at h
      · simp only [List.mem_append] at h
        rcases h with (h | h) | h
        · exact wrote_named h
        · exact wrote_named h
        · exact keptw_named h
      · simp at h
  | .closure _ e, _, h => by
      simp only [wrote] at h
      split at h
      · simp only [List.mem_append] at h
        rcases h with h | h
        · exact wrote_named h
        · exact keptw_named h
      · simp at h

/-- `Made size σ p q`: the partial piece `p` stands for the whole piece `q`,
    and every reference in `p`, and in the pieces `σ` holds under them, is the
    reference `cut` gives the value it stands for. -/
inductive Made (size : Nat) (σ : Store Ref) : P Ref → P Ref → Prop where
  | nat {n} : Made size σ (.nat n) (.nat n)
  | name {n} : Made size σ (.name n) (.name n)
  | text {t} : Made size σ (.text t) (.text t)
  | nil : Made size σ .nil .nil
  | cons {h t h' t'} (hh : Made size σ h h') (ht : Made size σ t t') :
      Made size σ (.cons h t) (.cons h' t')
  | closure {c e e'} (he : Made size σ e e') : Made size σ (.closure c e) (.closure c e')
  | ref {r p q} (hr : σ r = some p) (hp : Made size σ p q)
      (hc : norm size q = some (.ref r)) : Made size σ (.ref r) q

/-- Every reference in `p` was made by `cut`. -/
def Good (size : Nat) (σ : Store Ref) (p : P Ref) : Prop := ∃ q, Made size σ p q

variable {size : Nat} {σ τ : Store Ref}

/-- A piece that is `Made` for `q` resolves to `q`. -/
theorem Made.unf {p q : P Ref} (h : Made size σ p q) : Unf σ p q := by
  induction h with
  | nat => exact .nat
  | name => exact .name
  | text => exact .text
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂
  | closure _ ih => exact .closure ih
  | ref hr _ _ ih => exact .ref hr ih

/-- `Made` is: every reference was made by `cut`, and the piece resolves. -/
theorem made_iff {p q : P Ref} : Made size σ p q ↔ Good size σ p ∧ Unf σ p q := by
  constructor
  · intro h; exact ⟨⟨q, h⟩, h.unf⟩
  · intro ⟨⟨q', h⟩, hu⟩
    cases Unf.unique h.unf hu
    exact h

theorem Made.mono (hle : σ.le τ) {p q : P Ref} (h : Made size σ p q) : Made size τ p q := by
  induction h with
  | nat => exact .nat
  | name => exact .name
  | text => exact .text
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂
  | closure _ ih => exact .closure ih
  | ref hr _ hc ih => exact .ref (hle _ _ hr) ih hc

/-- A piece with no reference in it is `Made`, under any store. What a piece
    resolves to has no reference in it. -/
theorem Made.whole {σ' : Store Ref} {p q : P Ref} (h : Unf σ' p q) : Made size σ q q := by
  induction h with
  | nat => exact .nat
  | name => exact .name
  | text => exact .text
  | nil => exact .nil
  | cons _ _ ih₁ ih₂ => exact .cons ih₁ ih₂
  | closure _ ih => exact .closure ih
  | ref _ _ ih => exact ih

theorem Made.data (d : Data) : Made size σ d.toP d.toP := Made.whole (unf_data σ d)
theorem Made.value (v : MValue) : Made size σ v.toP v.toP := Made.whole (unf_value σ v)

/-- `cut` is a function of the value: a partial piece every reference of which
    was made by `cut` is cut to what the whole value is cut to. -/
theorem Made.norm_eq {p q : P Ref} (h : Made size σ p q) : norm size p = norm size q := by
  induction h with
  | nat => rfl
  | name => rfl
  | text => rfl
  | nil => rfl
  | cons _ _ ih₁ ih₂ => simp only [Wire.norm, ih₁, ih₂]
  | closure _ ih => simp only [Wire.norm, ih]
  | ref _ _ hc _ => simpa [Wire.norm] using hc.symm

theorem keptv_made {p q c : P Ref} (hp : Made size τ p q) (hn : norm size q = some c)
    (hk : keptv size p = some c) (hτ : ∀ t ∈ keptw size p, τ t.1 = some t.2.2) :
    Made size τ c q := by
  unfold keptv at hk
  unfold keptw at hτ
  cases hb : pieceBytes p with
  | none => simp [hb] at hk
  | some b =>
    simp only [hb, Option.map_some, Option.some.injEq] at hk
    simp only [hb] at hτ
    by_cases hs : b.size ≤ size
    · simp only [hs, ite_true] at hk
      exact hk ▸ hp
    · simp only [hs, ite_false] at hk hτ
      subst hk
      exact .ref (hτ (Blake3.hash b, b, p) (by simp)) hp hn

/-- `cut` makes only such references: what it leaves is `Made` for the same
    value, under any store that holds the old pieces and the pieces it stored. -/
theorem Made.after_cut {p q : P Ref} (h : Made size σ p q) : ∀ {c : P Ref}, norm size p = some c →
    σ.le τ → (∀ t ∈ wrote size p, τ t.1 = some t.2.2) → Made size τ c q := by
  induction h with
  | nat => intro c hc _ hτ; exact keptv_made .nat hc hc hτ
  | name => intro c hc _ hτ; exact keptv_made .name hc hc hτ
  | text => intro c hc _ hτ; exact keptv_made .text hc hc hτ
  | nil => intro c hc _ hτ; exact keptv_made .nil hc hc hτ
  | @cons h t qh qt hh ht ih₁ ih₂ =>
    intro c hc hle hτ
    simp only [Wire.norm] at hc
    simp only [wrote] at hτ
    cases h₁ : Wire.norm size h with
    | none => simp [h₁] at hc
    | some h' =>
      cases h₂ : Wire.norm size t with
      | none => simp [h₁, h₂] at hc
      | some t' =>
        simp only [h₁, h₂] at hc hτ
        have m₁ := ih₁ h₁ hle (fun x hx => hτ x (by simp [hx]))
        have m₂ := ih₂ h₂ hle (fun x hx => hτ x (by simp [hx]))
        refine keptv_made (.cons m₁ m₂) ?_ hc (fun x hx => hτ x (by simp [hx]))
        simp only [Wire.norm, ← hh.norm_eq, ← ht.norm_eq, h₁, h₂, hc]
  | @closure k e qe he ih =>
    intro c hc hle hτ
    simp only [Wire.norm] at hc
    simp only [wrote] at hτ
    cases h₁ : Wire.norm size e with
    | none => simp [h₁] at hc
    | some e' =>
      simp only [h₁] at hc hτ
      have m₁ := ih h₁ hle (fun x hx => hτ x (by simp [hx]))
      refine keptv_made (.closure m₁) ?_ hc (fun x hx => hτ x (by simp [hx]))
      simp only [Wire.norm, ← he.norm_eq, h₁, hc]
  | @ref r p q hr hp hn _ =>
    intro c hc hle _
    simp only [Wire.norm, Option.some.injEq] at hc
    subst hc
    exact (Made.ref hr hp hn).mono hle

/-- The two together, on `cut` as it runs: what it leaves is what cutting the
    whole value leaves, and is `Made` for that value once the pieces it stored
    are in the store. -/
theorem cut_made {p q c : P Ref} {acc acc' : Array (Ref × ByteArray)} (h : Made size σ p q)
    (hc : (cut size p).run acc = some (c, acc')) :
    norm size q = some c ∧ ∃ w : List Stored, acc' = acc ++ bytesOf w ∧
      (∀ t ∈ w, pieceBytes t.2.2 = some t.2.1 ∧ t.1 = Blake3.hash t.2.1) ∧
      ∀ τ : Store Ref, σ.le τ → (∀ t ∈ w, τ t.1 = some t.2.2) → Made size τ c q := by
  rw [cut_run] at hc
  cases hn : Wire.norm size p with
  | none => simp [hn] at hc
  | some c' =>
    simp only [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨h.norm_eq ▸ hn, wrote size p, rfl, fun t ht => wrote_named ht,
      fun τ hle hτ => h.after_cut hn hle hτ⟩

/-- Two partial pieces that stand for one value, every reference in each made
    by `cut`, are cut to the same piece. The stores and the pieces stored
    before may differ. -/
theorem cut_function {σ' : Store Ref} {p p' q : P Ref} (h : Made size σ p q)
    (h' : Made size σ' p' q) (acc acc' : Array (Ref × ByteArray)) :
    ((cut size p).run acc).map (·.1) = ((cut size p').run acc').map (·.1) := by
  rw [cut_run, cut_run, h.norm_eq, h'.norm_eq]
  cases Wire.norm size q <;> rfl

/-- The root `save` reports, from what `cut` leaves. -/
def rootOf : Option (P Ref) → Option Ref
  | none => none
  | some (.ref r) => some r
  | some top => (pieceBytes top).map Blake3.hash

/-- The pieces `save` stores: those `cut` stores, then the top one. -/
def saved (size : Nat) (p : P Ref) : List Stored :=
  wrote size p ++
    match norm size p with
    | none => []
    | some (.ref _) => []
    | some top =>
        match pieceBytes top with
        | some b => [(Blake3.hash b, b, top)]
        | none => []

theorem stored_run (p : P Ref) (acc : Array (Ref × ByteArray)) :
    (stored p).run acc =
      (pieceBytes p).map fun b => (.ref (Blake3.hash b), acc.push (Blake3.hash b, b)) := by
  unfold stored
  cases h : pieceBytes p <;>
    simp [StateT.run, bind, StateT.bind, liftM, monadLift, MonadLift.monadLift, StateT.lift,
      pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]

/-- `save` gives the root of what `cut` leaves, and the pieces `saved` lists. -/
theorem save_eq (size : Nat) (p : P Ref) :
    save size p = (rootOf (norm size p)).map fun r => (r, bytesOf (saved size p)) := by
  simp only [save, StateT.run_bind, cut_run, saved]
  cases hn : norm size p with
  | none => simp [rootOf]
  | some c =>
    cases c with
    | ref r =>
      simp [rootOf, bytesOf, pure, StateT.pure, StateT.run]
    | _ =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, rootOf, StateT.run_bind,
        stored_run]
      generalize pieceBytes _ = o
      cases o <;> simp [bytesOf, pure, StateT.pure, StateT.run]

/-- The root is a function of the value: a partial piece every reference of
    which was made by `cut` is saved under the root of the whole value. -/
theorem Made.root {p q : P Ref} (h : Made size σ p q) :
    (save size p).map (·.1) = (save size q).map (·.1) := by
  rw [save_eq, save_eq, h.norm_eq]
  cases rootOf (Wire.norm size q) <;> rfl

/-- Equal values are saved under one root: two partial pieces that stand for
    one value, every reference in each made by `cut`, have the same root. -/
theorem same_root {σ' : Store Ref} {p p' q : P Ref} (h : Made size σ p q)
    (h' : Made size σ' p' q) : (save size p).map (·.1) = (save size p').map (·.1) :=
  h.root.trans h'.root.symm

/-- What is saved under the root is the value: in any store that holds the old
    pieces and the pieces `save` stored, the root resolves to it. -/
theorem save_resolves {p q : P Ref} {r : Ref} {w : Array (Ref × ByteArray)}
    (h : Made size σ p q) (hs : save size p = some (r, w)) :
    ∃ ps : List Stored, w = bytesOf ps ∧
      (∀ t ∈ ps, pieceBytes t.2.2 = some t.2.1 ∧ t.1 = Blake3.hash t.2.1) ∧
      ∀ τ : Store Ref, σ.le τ → (∀ t ∈ ps, τ t.1 = some t.2.2) → Unf τ (.ref r) q := by
  rw [save_eq] at hs
  cases hn : Wire.norm size p with
  | none => simp [hn, rootOf] at hs
  | some c =>
    have key : ∀ τ : Store Ref, σ.le τ → (∀ t ∈ saved size p, τ t.1 = some t.2.2) →
        Made size τ c q := fun τ hle hτ =>
      h.after_cut hn hle (fun t ht => hτ t (by simp [saved, ht]))
    by_cases hc : ∃ r', c = .ref r'
    · obtain ⟨r', rfl⟩ := hc
      simp only [hn, rootOf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨saved size p, rfl, ?_, fun τ hle hτ => (key τ hle hτ).unf⟩
      intro t ht
      simp only [saved, hn, List.append_nil] at ht
      exact wrote_named ht
    · have hroot : rootOf (some c) = (pieceBytes c).map Blake3.hash := by
        cases c <;> first | rfl | exact absurd ⟨_, rfl⟩ hc
      have hsaved : saved size p = wrote size p ++
          match pieceBytes c with
          | some b => [(Blake3.hash b, b, c)]
          | none => [] := by
        simp only [saved, hn]
        cases c <;> first | rfl | exact absurd ⟨_, rfl⟩ hc
      cases hb : pieceBytes c with
      | none => simp [hn, hroot, hb] at hs
      | some b =>
        simp only [hn, hroot, hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        refine ⟨saved size p, rfl, ?_, fun τ hle hτ => ?_⟩
        · intro t ht
          simp only [hsaved, hb, List.mem_append, List.mem_singleton] at ht
          rcases ht with ht | rfl
          · exact wrote_named ht
          · exact ⟨hb, rfl⟩
        · exact .ref (hτ (Blake3.hash b, b, c) (by simp [hsaved, hb])) (key τ hle hτ).unf

/-! ## The lazy machine makes no reference

    A step moves pieces, fetches them and builds new ones from whole data. So
    when every reference in a state was made by `cut`, the same holds of the
    next state. The store `σ` here is the whole store; the machine may run on
    any part of it. -/

@[simp] theorem good_nat {n : Nat} : Good size σ (.nat n) := ⟨_, .nat⟩
@[simp] theorem good_name {n : Nat} : Good size σ (.name n) := ⟨_, .name⟩
@[simp] theorem good_text {t : List Char} : Good size σ (.text t) := ⟨_, .text⟩
@[simp] theorem good_nil : Good size σ .nil := ⟨_, .nil⟩

@[simp] theorem good_cons {h t : P Ref} :
    Good size σ (.cons h t) ↔ Good size σ h ∧ Good size σ t := by
  constructor
  · intro ⟨_, m⟩; cases m with | cons hh ht => exact ⟨⟨_, hh⟩, ⟨_, ht⟩⟩
  · intro ⟨⟨_, hh⟩, ⟨_, ht⟩⟩; exact ⟨_, .cons hh ht⟩

@[simp] theorem good_closure {c : Code} {e : P Ref} :
    Good size σ (.closure c e) ↔ Good size σ e := by
  constructor
  · intro ⟨_, m⟩; cases m with | closure he => exact ⟨_, he⟩
  · intro ⟨_, he⟩; exact ⟨_, .closure he⟩

theorem good_ref {r : Ref} (h : Good size σ (.ref r)) : ∃ p, σ r = some p ∧ Good size σ p := by
  obtain ⟨_, m⟩ := h
  cases m with | ref hr hp _ => exact ⟨_, hr, _, hp⟩

@[simp] theorem good_data (d : Data) : Good size σ d.toP := ⟨_, Made.data d⟩
@[simp] theorem good_list (xs : List Data) : Good size σ (Data.listToP xs) := good_data (.arr xs)
@[simp] theorem good_value (v : MValue) : Good size σ v.toP := ⟨_, Made.value v⟩
@[simp] theorem good_env (vs : List MValue) : Good size σ (envToP vs) :=
  ⟨_, Made.whole (unf_env σ vs)⟩

theorem Good.mono (hle : σ.le τ) {p : P Ref} (h : Good size σ p) : Good size τ p :=
  h.imp fun _ m => m.mono hle

/-- Every reference in a machine state was made by `cut`. -/
def GoodS (size : Nat) (σ : Store Ref) : PState Ref → Prop
  | .running _ env stk frs =>
      Good size σ env ∧ (∀ p ∈ stk, Good size σ p) ∧ ∀ f ∈ frs, Good size σ f.env
  | .seeking _ _ cur _ env stk frs =>
      Good size σ cur ∧ Good size σ env ∧ (∀ p ∈ stk, Good size σ p) ∧
        ∀ f ∈ frs, Good size σ f.env
  | .halted (.value v) => Good size σ v
  | .halted _ => True
  | .fault => True

/-- A state held whole has no reference in it. -/
theorem goodS_whole (s : State) : GoodS size σ s.toP := by
  cases s with
  | running c env stk frs =>
    refine ⟨good_env env, ?_, ?_⟩
    · intro p hp
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp
      exact good_value v
    · intro f hf
      obtain ⟨m, _, rfl⟩ := List.mem_map.mp hf
      exact good_env m.env
  | halted o =>
    cases o with
    | value v => exact good_value v
    | unbound i => trivial
    | wrong => trivial
  | fault => trivial

theorem good_fetch {r : Ref} {F : P Ref → PState Ref} {ps' : PState Ref}
    (hg : Good size σ (.ref r)) (h : fetch σ r F = .next ps') :
    ∃ p, Good size σ p ∧ ps' = F p := by
  obtain ⟨p, hr, hp⟩ := good_ref hg
  unfold fetch at h
  simp only [hr, LStep.next.injEq] at h
  exact ⟨p, hp, h.symm⟩

theorem good_hyd : ∀ (p : P Ref) {p' : P Ref}, Good size σ p → p.hyd σ = .ok p' →
    Good size σ p'
  | .nat _, _, _, h => by simp only [P.hyd, Except.ok.injEq] at h; subst h; simp
  | .name _, _, _, h => by simp only [P.hyd, Except.ok.injEq] at h; subst h; simp
  | .text _, _, _, h => by simp only [P.hyd, Except.ok.injEq] at h; subst h; simp
  | .nil, _, _, h => by simp only [P.hyd, Except.ok.injEq] at h; subst h; simp
  | .cons a b, _, hg, h => by
    simp only [P.hyd] at h
    rw [good_cons] at hg
    cases ha : a.hyd σ with
    | error r => simp [ha] at h
    | ok a' =>
      cases hb : b.hyd σ with
      | error r => simp [ha, hb] at h
      | ok b' =>
        simp only [ha, hb, Except.ok.injEq] at h
        subst h
        exact good_cons.mpr ⟨good_hyd a hg.1 ha, good_hyd b hg.2 hb⟩
  | .closure c e, _, hg, h => by
    simp only [P.hyd] at h
    rw [good_closure] at hg
    cases he : e.hyd σ with
    | error r => simp [he] at h
    | ok e' =>
      simp only [he, Except.ok.injEq] at h
      subst h
      exact good_closure.mpr (good_hyd e hg he)
  | .ref r, _, hg, h => by
    obtain ⟨p, hr, hp⟩ := good_ref hg
    simp only [P.hyd, hr, Except.ok.injEq] at h
    exact h ▸ hp

/-- Close a case of a step: the next state is given outright, or by a fetch. -/
local macro "good_step" hg:ident h:ident : tactic =>
  `(tactic| first
    | (cases $h:ident; simp_all [GoodS]; done)
    | (obtain ⟨_, hp, rfl⟩ := good_fetch (by simp_all [GoodS]) $h
       simp_all [GoodS]; done)
    | (simp only [GoodS, List.forall_mem_cons] at $hg:ident
       obtain ⟨_, hp, rfl⟩ := good_fetch (by first | exact $hg.2.1.1 | exact $hg.2.1.2.1 | exact $hg.1) $h
       simp_all [GoodS]; done))

variable [Ops]

theorem lPrim_good {k : Code} {env : P Ref} {stk : List (P Ref)} {frs : List (PFrame Ref)}
    {ps' : PState Ref} (hg : GoodS size σ (.running (.prim k) env stk frs))
    (h : lPrim σ k env stk frs = .next ps') : GoodS size σ ps' := by
  rcases stk with _ | ⟨x, _ | ⟨y, stk⟩⟩
  · good_step hg h
  · good_step hg h
  · have hx : Good size σ x := hg.2.1 x (by simp)
    cases y with
    | ref r => good_step hg h
    | nat n =>
      by_cases hc : ∀ b cap, x ≠ .closure b cap
      · rw [lPrim_nat _ _ _ _ _ _ _ hc] at h
        cases hd : x.toData with
        | some d => simp only [hd] at h; good_step hg h
        | none =>
          simp only [hd] at h
          cases hh : x.hyd σ with
          | ok x' =>
            simp only [hh] at h
            have := good_hyd x hx hh
            good_step hg h
          | error r => simp [hh] at h
      · cases x with
        | closure b cap => good_step hg h
        | _ => exact absurd (by intro b cap hc; cases hc) hc
    | name n =>
      by_cases hc : ∀ b cap, x ≠ .closure b cap
      · rw [lPrim_name _ _ _ _ _ _ _ hc] at h
        cases hd : x.toData with
        | some d => simp only [hd] at h; good_step hg h
        | none =>
          simp only [hd] at h
          cases hh : x.hyd σ with
          | ok x' =>
            simp only [hh] at h
            have := good_hyd x hx hh
            good_step hg h
          | error r => simp [hh] at h
      · cases x with
        | closure b cap => good_step hg h
        | _ => exact absurd (by intro b cap hc; cases hc) hc
    | _ => cases x <;> good_step hg h

theorem lstep_good_same {ps ps' : PState Ref} (hg : GoodS size σ ps)
    (h : lstep σ ps = .next ps') : GoodS size σ ps' := by
  cases ps with
  | halted o => cases h; exact hg
  | fault => cases h; exact hg
  | seeking j i cur k env stk frs =>
    cases cur <;> cases i <;> good_step hg h
  | running c env stk frs =>
    cases c with
    | done =>
      rcases frs with _ | ⟨f, frs⟩
      · rcases stk with _ | ⟨v, _ | ⟨w, stk⟩⟩ <;> good_step hg h
      · rcases stk with _ | ⟨v, _ | ⟨w, stk⟩⟩ <;> good_step hg h
    | access i k => good_step hg h
    | closure b k => good_step hg h
    | literal d k => good_step hg h
    | prim k => exact lPrim_good hg h
    | checkFun k =>
      rcases stk with _ | ⟨x, stk⟩
      · good_step hg h
      · cases x <;> good_step hg h
    | checkData k =>
      rcases stk with _ | ⟨x, stk⟩
      · good_step hg h
      · cases x <;> good_step hg h
    | succ k =>
      rcases stk with _ | ⟨x, stk⟩
      · good_step hg h
      · cases x <;> good_step hg h
    | checkNat k =>
      rcases stk with _ | ⟨x, stk⟩
      · good_step hg h
      · cases x <;> good_step hg h
    | dcase z sc n c k =>
      rcases stk with _ | ⟨x, stk⟩
      · good_step hg h
      · cases x with
        | nat m => cases m <;> good_step hg h
        | name m => cases m <;> good_step hg h
        | text t => cases t <;> good_step hg h
        | _ => good_step hg h
    | apply k =>
      rcases stk with _ | ⟨a, _ | ⟨x, stk⟩⟩
      · good_step hg h
      · good_step hg h
      · cases x <;> good_step hg h
    | cons k =>
      rcases stk with _ | ⟨a, _ | ⟨x, stk⟩⟩
      · good_step hg h
      · good_step hg h
      · cases x <;> cases a <;> good_step hg h

/-- A step of the lazy machine, on any part `σ'` of the store, keeps every
    reference one that `cut` made. -/
theorem lstep_good {σ' : Store Ref} (hle : σ'.le σ) {ps ps' : PState Ref}
    (hg : GoodS size σ ps) (h : lstep σ' ps = .next ps') : GoodS size σ ps' :=
  lstep_good_same hg (lstep_mono hle h)

/-- So does a run, whether it is at a state or paused at one. -/
theorem lrun_good {σ' : Store Ref} (hle : σ'.le σ) : ∀ (n : Nat) {ps ps' : PState Ref},
    GoodS size σ ps → (lrun σ' n ps = .at ps' ∨ ∃ r, lrun σ' n ps = .paused r ps') →
    GoodS size σ ps' := by
  intro n
  induction n with
  | zero =>
    intro ps ps' hg h
    rcases h with h | ⟨r, h⟩
    · cases h; exact hg
    · cases h
  | succ n ih =>
    intro ps ps' hg h
    simp only [lrun] at h
    cases hl : lstep σ' ps with
    | next s' =>
      simp only [hl] at h
      exact ih (lstep_good hle hg hl) h
    | needs r =>
      simp only [hl] at h
      rcases h with h | ⟨r', h⟩
      · cases h
      · cases h; exact hg

end Wire
