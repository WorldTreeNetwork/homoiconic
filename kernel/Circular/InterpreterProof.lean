import Circular.Reduction

namespace Circular
namespace InterpreterProof

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

abbrev ap := Term.app
abbrev v := Term.var
abbrev lam := Term.lam

def functional : Term := Builder.compile [] Builder.functional

def core : Term := match functional with
  | .lam (.lam (.lam b)) => b
  | _ => .var 0

theorem functional_eq : functional = lam (lam (lam core)) := rfl

theorem functional_closed : Closed functional := by decide +kernel

/-- The two finite pieces of the CBV fixed point after substitution. -/
def arm : Term := lam (ap functional (lam (ap (ap (v 1) (v 1)) (v 0))))
def self : Term := lam (ap (ap arm arm) (v 0))

theorem arm_closed : Closed arm := by
  exact ⟨scoped_mono functional_closed (by omega), ⟨⟨by decide, by decide⟩, by decide⟩⟩
theorem self_closed : Closed self := by
  exact ⟨⟨scoped_mono arm_closed (by omega), scoped_mono arm_closed (by omega)⟩, by decide⟩

@[simp] theorem plug_functional : plug es d functional = functional := plug_closed_id functional_closed
@[simp] theorem plug_arm : plug es d arm = arm := plug_closed_id arm_closed
@[simp] theorem plug_self : plug es d self = self := plug_closed_id self_closed
@[simp] theorem plug_church : plug es d (church i) = church i := plug_closed_id (church_closed i)
@[simp] theorem plug_encode (h : Pure p) : plug es d (encode p h) = encode p h :=
  plug_closed_id (encode_closed h)
@[simp] theorem plug_environment (h : PureEnv e) :
    plug es d (encodeEnvironment e h) = encodeEnvironment e h :=
  plug_closed_id (encodeEnvironment_properties e h).2
@[simp] theorem plug_closure (h : PureValue c) :
    plug es d (encodeClosure c h) = encodeClosure c h :=
  plug_closed_id (encodeClosure_properties c h).2
@[simp] theorem plug_outcome (h : PureOutcome o) :
    plug es d (encodeOutcome o h) = encodeOutcome o h :=
  plug_closed_id (encodeOutcome_closed h)

@[simp] theorem encode_var : encode (.var i) h = lam (lam (lam (ap (v 2) (church i)))) := by
  simp [encode, shift_eq_self_of_scoped (church_closed i)]
@[simp] theorem encode_lam : encode (.lam b) h = lam (lam (lam (ap (v 1) (encode b (pure_lam.mp h))))) := by
  simp [encode, shift_eq_self_of_scoped (encode_closed _)]
@[simp] theorem encode_app : encode (.app f a) h =
    lam (lam (lam (ap (ap (v 0) (encode f (pure_app.mp h).1)) (encode a (pure_app.mp h).2)))) := by
  simp [encode, shift_eq_self_of_scoped (encode_closed _)]

theorem encode_lambda (h : Pure p) : IsLambda (encode p h) := by
  cases h <;> simp only [encode_var, encode_lam, encode_app] <;> exact .lam

theorem environment_lambda (h : PureEnv e) : IsLambda (encodeEnvironment e h) := by
  cases e with
  | nil => rw [encodeEnvironment]; exact .lam
  | cons c e => rw [encodeEnvironment]; exact .lam

theorem outcome_lambda (h : PureOutcome o) : IsLambda (encodeOutcome o h) := by
  cases o <;> exact .lam

def run (p e : Term) : Term := ap (ap self p) e
def dispatch (p e : Term) : Term := plug [e, p, self] 0 core

theorem self_step (vp : IsLambda p) : Step (ap self p) (ap (ap arm arm) p) := by
  have h := Step.beta (b := ap (ap arm arm) (v 0)) vp
  simpa [plug, self] using h

theorem arm_step : Step (ap arm arm) (ap functional self) := by
  have h := Step.beta (b := ap functional (lam (ap (ap (v 1) (v 1)) (v 0))))
    (IsLambda.lam (b := ap functional (lam (ap (ap (v 1) (v 1)) (v 0)))))
  simpa [plug, self, arm] using h

theorem functional_step : Step (ap functional self) (lam (lam (plug [self] 2 core))) := by
  rw [functional_eq]
  exact .beta .lam

theorem run_unroll (hp : Closed p) (he : Closed e) (vp : IsLambda p) (ve : IsLambda e) :
    Red (run p e) (dispatch p e) := by
  have ep : ClosedTerms [p] := by simpa [ClosedTerms] using hp
  have ee : ClosedTerms [e] := by simpa [ClosedTerms] using he
  have es : ClosedTerms [self] := by simpa [ClosedTerms] using self_closed
  refine .cons (.left (self_step vp)) (.cons (.left (.left arm_step))
    (.cons (.left (.left functional_step)) ?_))
  have sp := Step.beta (b := lam (plug [self] 2 core)) vp
  have eqp : plug [p] 1 (plug [self] 2 core) = plug [p, self] 1 core := by
    exact plug_comp ep es
  simp only [plug, eqp] at sp
  refine .cons (.left sp) ?_
  have se := Step.beta (b := plug [p, self] 1 core) ve
  have eqe : plug [e] 0 (plug [p, self] 1 core) = dispatch p e := by
    exact plug_comp ee (by simpa [ClosedTerms] using And.intro hp self_closed)
  rw [eqe] at se
  exact .cons se .refl

/-- The Scott constructor functions are the builder's existing lambda terms. -/
def nilC : Term := Builder.compile [] Builder.nil
def consC : Term := Builder.compile [] Builder.cons
def okC : Term := Builder.compile [] Builder.ok
def badC : Term := Builder.compile [] Builder.bad
def closureC : Term := Builder.compile [] Builder.closure
def tailC : Term := Builder.compile [] Builder.tail
def lookupC : Term := Builder.compile [] Builder.lookup

theorem nilC_closed : Closed nilC := by decide +kernel
theorem consC_closed : Closed consC := by decide +kernel
theorem okC_closed : Closed okC := by decide +kernel
theorem badC_closed : Closed badC := by decide +kernel
theorem closureC_closed : Closed closureC := by decide +kernel
theorem tailC_closed : Closed tailC := by decide +kernel
theorem lookupC_closed : Closed lookupC := by decide +kernel

@[simp] theorem plug_nilC : plug es d nilC = nilC := plug_closed_id nilC_closed
@[simp] theorem plug_consC : plug es d consC = consC := plug_closed_id consC_closed
@[simp] theorem plug_okC : plug es d okC = okC := plug_closed_id okC_closed
@[simp] theorem plug_badC : plug es d badC = badC := plug_closed_id badC_closed
@[simp] theorem plug_closureC : plug es d closureC = closureC := plug_closed_id closureC_closed
@[simp] theorem plug_tailC : plug es d tailC = tailC := plug_closed_id tailC_closed
@[simp] theorem plug_lookupC : plug es d lookupC = lookupC := plug_closed_id lookupC_closed

def select (t good bad : Term) : Term := ap (ap t good) bad
def badH : Term := lam (ap badC (v 0))
def argH : Term := lam (run (v 2) (ap (ap consC (ap okC (v 0))) (v 1)))
def closureH (a e : Term) : Term := lam (lam (select (run a e) argH badH))
def goodH (a e : Term) : Term := lam (ap (ap (ap (v 0) nilC) (closureH a e)) nilC)
def appCore (f a e : Term) : Term := select (run f e) (goodH a e) badH

theorem ok_step (ht : Closed t) (vt : IsLambda t) : Step (ap okC t) (Data.ok t) := by
  have h := Step.beta (b := lam (lam (ap (v 1) (v 2)))) vt
  simpa [okC, Builder.compile, Builder.ok, Builder.lams, Builder.apps,
    Builder.ap, Builder.v, List.idxOf_cons, Data.ok, plug,
    shift_eq_self_of_scoped ht] using h

theorem bad_step (i : Nat) : Step (ap badC (church i)) (Data.bad i) := by
  have vi : IsLambda (church i) := by cases i <;> exact .lam
  have h := Step.beta (b := lam (lam (ap (v 0) (v 2)))) vi
  simpa [badC, Builder.compile, Builder.bad, Builder.lams, Builder.apps,
    Builder.ap, Builder.v, List.idxOf_cons, Data.bad, plug,
    shift_eq_self_of_scoped (church_closed i)] using h

theorem closure_red (hb : Closed b) (he : Closed e) (vb : IsLambda b) (ve : IsLambda e) :
    Red (ap (ap closureC b) e) (Data.closure b e) := by
  have s1 := Step.beta (b := lam (lam (lam (lam (ap (ap (v 1) (v 4)) (v 3)))))) vb
  simp only [plug] at s1
  have sb : ∀ es d, plug es d b = b := fun _ _ => plug_closed_id hb
  simp at s1
  have s2 := Step.beta (b := lam (lam (lam (ap (ap (v 1) b) (v 3))))) ve
  simp [plug, sb] at s2
  have hs : Red (ap (ap closureC b) e) (lam (lam (lam (ap (ap (v 1) b) e)))) := by
    simpa [closureC, Builder.compile, Builder.closure, Builder.lams, Builder.apps,
      Builder.ap, Builder.v, List.idxOf_cons] using Red.cons (.left s1) (.cons s2 .refl)
  simpa [Data.closure, shift_eq_self_of_scoped hb, shift_eq_self_of_scoped he] using hs

theorem cons_red (hh : Closed h) (ht : Closed t) (vh : IsLambda h) (vt : IsLambda t) :
    Red (ap (ap consC h) t) (Data.cons h t) := by
  have s1 := Step.beta (b := lam (lam (lam (ap (ap (v 0) (v 3)) (v 2))))) vh
  have sh : ∀ es d, plug es d h = h := fun _ _ => plug_closed_id hh
  simp [plug] at s1
  have s2 := Step.beta (b := lam (lam (ap (ap (v 0) h) (v 2)))) vt
  simp [plug, sh] at s2
  have hs : Red (ap (ap consC h) t) (lam (lam (ap (ap (v 0) h) t))) := by
    simpa [consC, Builder.compile, Builder.cons, Builder.lams, Builder.apps,
      Builder.ap, Builder.v, List.idxOf_cons] using Red.cons (.left s1) (.cons s2 .refl)
  simpa [Data.cons, shift_eq_self_of_scoped hh, shift_eq_self_of_scoped ht] using hs

macro "dispatch_simp" : tactic => `(tactic|
  simp [reduce, next, dispatch, core, functional, Builder.functional, Builder.compile,
    Builder.lams, Builder.apps, Builder.lookup, Builder.tail, Builder.nil,
    Builder.ok, Builder.bad, Builder.closure, Builder.cons, Builder.ap, Builder.v,
    plug, nilC, consC, okC, badC, closureC, tailC, lookupC, List.idxOf_cons])


theorem dispatch_app (hf : Pure f) (ha : Pure a) (he : PureEnv e) :
    Red (dispatch (encode (.app f a) (.app hf ha)) (encodeEnvironment e he))
      (appCore (encode f hf) (encode a ha) (encodeEnvironment e he)) := by
  have h := reduce_sound 3
    (dispatch (encode (.app f a) (.app hf ha)) (encodeEnvironment e he))
  apply h.trans
  simp [reduce, next, dispatch, core, functional, Builder.functional, Builder.compile,
    Builder.lams, Builder.apps, Builder.lookup, Builder.tail, Builder.nil,
    Builder.ok, Builder.bad, Builder.closure, Builder.cons, Builder.ap, Builder.v,
    plug, appCore, select, run, goodH, closureH, argH, badH, nilC, consC, okC,
    badC, List.idxOf_cons]
  refine .cons (.left (.beta (encode_lambda hf))) ?_
  simp [plug]
  refine .cons (.beta (encode_lambda ha)) ?_
  simp [plug]
  exact .refl

theorem beta_select (ht : Beta t w) (hr : Beta (select w g b) r) :
    Beta (select t g b) r := by
  cases hr with
  | app hf hb hr =>
    cases hf with
    | app hw hg hi =>
      have hv := beta_value ht
      obtain ⟨bw, rfl⟩ := hv
      cases hw
      exact .app (.app ht hg hi) hb hr

theorem select_ok (hp : Closed p) (hg : Closed g) (vg : IsLambda g) (vb : IsLambda b) :
    Red (select (Data.ok p) g b) (ap g p) := by
  have s1 := Step.beta (b := lam (ap (v 1) p)) vg
  have sp : ∀ es d, plug es d p = p := fun _ _ => plug_closed_id hp
  have sg : ∀ es d, plug es d g = g := fun _ _ => plug_closed_id hg
  simp [plug, sp] at s1
  have s2 := Step.beta (b := ap g p) vb
  simp [plug, sp, sg] at s2
  simpa [select, Data.ok, shift_eq_self_of_scoped hp] using
    Red.cons (.left s1) (.cons s2 .refl)

theorem select_bad (i : Nat) (vg : IsLambda g) (vb : IsLambda b) :
    Red (select (Data.bad i) g b) (ap b (church i)) := by
  have s1 := Step.beta (b := lam (ap (v 0) (church i))) vg
  simp [plug] at s1
  have s2 := Step.beta (b := ap (v 0) (church i)) vb
  simp [plug] at s2
  simpa [select, Data.bad, shift_eq_self_of_scoped (church_closed i)] using
    Red.cons (.left s1) (.cons s2 .refl)

theorem select_nil (hn : Closed n) (vn : IsLambda n) (vc : IsLambda c) :
    Red (select Data.nil n c) n := by
  have s1 := Step.beta (b := lam (v 1)) vn
  simp [plug] at s1
  have s2 := Step.beta (b := n) vc
  rw [plug_closed_id hn] at s2
  exact .cons (.left s1) (.cons s2 .refl)

theorem select_cons (hh : Closed h) (ht : Closed t) (_hc : Closed c)
    (vn : IsLambda n) (vc : IsLambda c) :
    Red (select (Data.cons h t) n c) (ap (ap c h) t) := by
  have s1 := Step.beta (b := lam (ap (ap (v 0) h) t)) vn
  have sh : ∀ es d, plug es d h = h := fun _ _ => plug_closed_id hh
  have st : ∀ es d, plug es d t = t := fun _ _ => plug_closed_id ht
  simp [plug, sh, st] at s1
  have s2 := Step.beta (b := ap (ap (v 0) h) t) vc
  simp [plug, sh, st] at s2
  simpa [select, Data.cons, shift_eq_self_of_scoped hh, shift_eq_self_of_scoped ht]
    using Red.cons (.left s1) (.cons s2 .refl)

theorem dispatch_var (i : Nat) (he : PureEnv e) :
    Red (dispatch (encode (.var i) (.var i)) (encodeEnvironment e he))
      (ap (ap lookupC (church i)) (encodeEnvironment e he)) := by
  apply (reduce_sound 3 _).trans
  dispatch_simp
  have vi : IsLambda (church i) := by cases i <;> exact .lam
  refine .cons (.beta vi) ?_
  simp [plug]
  exact .refl

theorem dispatch_lam (hb : Pure b) (he : PureEnv e) :
    Red (dispatch (encode (.lam b) (.lam hb)) (encodeEnvironment e he))
      (encodeOutcome (.value (.closure b e)) (.closure hb he)) := by
  have hl : Red (dispatch (encode (.lam b) (.lam hb)) (encodeEnvironment e he))
      (ap okC (ap (ap closureC (encode b hb)) (encodeEnvironment e he))) := by
    apply (reduce_sound 3 _).trans
    dispatch_simp
    refine .cons (.beta (encode_lambda hb)) ?_
    simp [plug]
    exact .refl
  apply hl.trans
  apply (Red.right (IsLambda.lam (b := _))
    (closure_red (encode_closed hb) (encodeEnvironment_properties e he).2
      (encode_lambda hb) (environment_lambda he))).trans
  have hs := ok_step (Data.closure_closed (encode_closed hb) (encodeEnvironment_properties e he).2)
    (IsLambda.lam (b := _))
  simpa [encodeOutcome, encodeClosure, okC, Builder.compile, Builder.ok, Builder.lams,
    Builder.apps, Builder.ap, Builder.v, List.idxOf_cons] using Red.single hs

theorem beta_arg (ha : Beta a va) (h : Beta (ap f va) r) : Beta (ap f a) r := by
  obtain ⟨b, rfl⟩ := beta_value ha
  cases h with
  | app hf hv hb => cases hv; exact .app hf ha hb

def tailH : Term := lam (lam (v 0))
def headH : Term := lam (lam (v 1))

theorem tail_step (ve : IsLambda e) : Step (ap tailC e) (select e nilC tailH) := by
  have h := Step.beta (b := select (v 0) nilC tailH) ve
  simpa [plug, select, tailH, tailC, nilC, Builder.compile, Builder.lams,
    Builder.apps, Builder.ap, Builder.v, Builder.tail, Builder.nil, List.idxOf_cons] using h

theorem pureTail (he : PureEnv e) : PureEnv e.tail := by
  cases e with
  | nil => exact .nil
  | cons v e => exact he.tail

theorem pureDrop (he : PureEnv e) (n : Nat) : PureEnv (e.drop n) := by
  induction n generalizing e with
  | zero => exact he
  | succ n ih =>
    cases e with
    | nil => exact .nil
    | cons v e => exact ih he.tail

theorem tail_beta (he : PureEnv e) :
    Beta (ap tailC (encodeEnvironment e he)) (encodeEnvironment e.tail (pureTail he)) := by
  apply Beta.step_back (tail_step (environment_lambda he))
  cases e with
  | nil =>
    rw [encodeEnvironment]
    apply Beta.red_back (select_nil nilC_closed .lam .lam)
    simpa [List.tail_nil, encodeEnvironment, Data.nil, nilC, Builder.compile, Builder.nil, Builder.lams,
      Builder.v, List.idxOf_cons] using (Beta.lam (b := lam (v 1)))
  | cons c e =>
    rw [encodeEnvironment]
    apply Beta.red_back (select_cons (Data.ok_closed (encodeClosure_properties c he.head).2)
      (encodeEnvironment_properties e he.tail).2 (by decide : Closed tailH) .lam .lam)
    have s1 := Step.beta (v := Data.ok (encodeClosure c he.head)) (b := lam (v 0))
      (IsLambda.lam (b := _))
    have s2 := Step.beta (b := v 0) (environment_lambda he.tail)
    have hr : Red (ap (ap tailH (Data.ok (encodeClosure c he.head)))
      (encodeEnvironment e he.tail)) (encodeEnvironment e he.tail) := by
      simpa [tailH, plug] using Red.cons (.left s1) (.cons s2 .refl)
    exact (Beta.of_lambda (environment_lambda he.tail)).red_back hr

theorem church_beta (n : Nat) (he : PureEnv e) :
    Beta (ap (ap (church n) tailC) (encodeEnvironment e he))
      (encodeEnvironment (e.drop n) (pureDrop he n)) := by
  induction n with
  | zero =>
    have s1 := Step.beta (v := tailC) (b := lam (v 0)) (IsLambda.lam (b := _))
    have s2 := Step.beta (b := v 0) (environment_lambda he)
    have hr : Red (ap (ap (church 0) tailC) (encodeEnvironment e he))
        (encodeEnvironment e he) := by
      simpa [church, plug, tailC] using Red.cons (.left s1) (.cons s2 .refl)
    exact (Beta.of_lambda (environment_lambda he)).red_back hr
  | succ n ih =>
    have s1 := Step.beta (v := tailC) (b := lam (ap (v 1) (ap (ap (church n) (v 1)) (v 0))))
      (IsLambda.lam (b := _))
    simp [plug] at s1
    have s2 := Step.beta (b := ap tailC (ap (ap (church n) tailC) (v 0)))
      (environment_lambda he)
    simp [plug] at s2
    have hr : Red (ap (ap (church (n + 1)) tailC) (encodeEnvironment e he))
        (ap tailC (ap (ap (church n) tailC) (encodeEnvironment e he))) := by
      simpa [church, shift_eq_self_of_scoped (church_closed n)] using
        Red.cons (.left s1) (.cons s2 .refl)
    apply Beta.red_back hr
    apply beta_arg ih
    simpa only [List.tail_drop] using tail_beta (pureDrop he n)

theorem beta_select_congr (ht : Beta t wt) (hg : Beta g wg) (hb : Beta b wb)
    (hr : Beta (select wt wg wb) r) : Beta (select t g b) r := by
  obtain ⟨bt, rfl⟩ := beta_value ht
  obtain ⟨bg, rfl⟩ := beta_value hg
  obtain ⟨bb, rfl⟩ := beta_value hb
  cases hr with
  | app hf hbad hout =>
    cases hf with
    | app hval hgood hin =>
      cases hval
      cases hgood
      cases hbad
      exact .app (.app ht hg hin) hb hout

def lookupResult (e : Env) (i : Nat) : Outcome :=
  match e[i]? with
  | some c => .value c
  | none => .unbound i

theorem lookup_direct (e : Env) (i : Nat) : Direct e (.var i) (lookupResult e i) := by
  unfold lookupResult
  split
  next h => exact .varBound h
  next h => exact .varUnbound h

theorem lookup_pure (he : PureEnv e) : PureOutcome (lookupResult e i) :=
  direct_pure (lookup_direct e i) (.var i) he

def headResult (e : Env) (i : Nat) : Outcome :=
  match e with
  | [] => .unbound i
  | c :: _ => .value c

theorem head_pure (he : PureEnv e) : PureOutcome (headResult e i) := by
  cases e with
  | nil => trivial
  | cons => exact he.head

theorem lookup_head : headResult (e.drop i) i = lookupResult e i := by
  have h : ∀ (j : Nat) (e : Env),
      (match e.drop j with | [] => none | c :: _ => some c) = e[j]? := by
    intro j
    induction j with
    | zero => intro e; cases e <;> rfl
    | succ j ih => intro e; cases e <;> simp_all
  have hh := h i e
  cases hd : e.drop i with
  | nil => simp only [hd] at hh; simp [headResult, lookupResult, ← hh]
  | cons c t => simp only [hd] at hh; simp [headResult, lookupResult, ← hh]

theorem head_beta (he : PureEnv e) (i : Nat) :
    Beta (select (encodeEnvironment e he) (Data.bad i) headH)
      (encodeOutcome (headResult e i) (head_pure he)) := by
  cases e with
  | nil =>
    rw [encodeEnvironment]
    apply Beta.red_back (select_nil (Data.bad_closed i) .lam .lam)
    exact .lam
  | cons c e =>
    rw [encodeEnvironment]
    apply Beta.red_back (select_cons (Data.ok_closed (encodeClosure_properties c he.head).2)
      (encodeEnvironment_properties e he.tail).2 (by decide : Closed headH) .lam .lam)
    have s1 := Step.beta (v := Data.ok (encodeClosure c he.head)) (b := lam (v 1)) .lam
    simp [plug] at s1
    have s2 := Step.beta (b := Data.ok (encodeClosure c he.head)) (environment_lambda he.tail)
    rw [plug_closed_id (Data.ok_closed (encodeClosure_properties c he.head).2)] at s2
    have hr : Red (ap (ap headH (Data.ok (encodeClosure c he.head)))
      (encodeEnvironment e he.tail)) (Data.ok (encodeClosure c he.head)) := by
      simpa [headH] using Red.cons (.left s1) (.cons s2 .refl)
    exact (Beta.lam).red_back hr

theorem lookup_beta (he : PureEnv e) (i : Nat) :
    Beta (ap (ap lookupC (church i)) (encodeEnvironment e he))
      (encodeOutcome (lookupResult e i) (lookup_pure he)) := by
  have vi : IsLambda (church i) := by cases i <;> exact .lam
  have s1 := Step.beta (b := lam (select (ap (ap (v 1) tailC) (v 0))
    (ap badC (v 1)) headH)) vi
  have sh : ∀ es d, plug es d headH = headH := fun _ _ => plug_closed_id (by decide)
  simp [plug, select, sh] at s1
  have s2 := Step.beta (b := select (ap (ap (church i) tailC) (v 0))
    (ap badC (church i)) headH) (environment_lambda he)
  simp [plug, select, sh] at s2
  have hr : Red (ap (ap lookupC (church i)) (encodeEnvironment e he))
    (select (ap (ap (church i) tailC) (encodeEnvironment e he)) (ap badC (church i)) headH) := by
    simpa [select, ap, v, lam, lookupC, tailC, badC, headH, nilC, Builder.compile, Builder.lookup,
      Builder.tail, Builder.bad, Builder.nil, Builder.lams, Builder.apps,
      Builder.ap, Builder.v, List.idxOf_cons] using Red.cons (.left s1) (.cons s2 .refl)
  apply Beta.red_back hr
  have hh := head_beta (pureDrop he i) i
  have hh' : Beta (select (encodeEnvironment (e.drop i) (pureDrop he i)) (Data.bad i) headH)
      (encodeOutcome (lookupResult e i) (lookup_pure he)) := by
    simpa only [lookup_head] using hh
  exact beta_select_congr (church_beta i he) ((Beta.lam).step_back (bad_step i)) .lam hh'


def argCont (b cap : Term) : Term := lam (run b (ap (ap consC (ap okC (v 0))) cap))

theorem badH_closed : Closed badH := by
  exact ⟨scoped_mono badC_closed (by decide), by decide⟩

theorem argCont_closed (hb : Closed b) (hc : Closed cap) : Closed (argCont b cap) := by
  have bs : ∀ n, Scoped n b := fun _ => scoped_mono hb (Nat.zero_le _)
  have cs : ∀ n, Scoped n cap := fun _ => scoped_mono hc (Nat.zero_le _)
  have ss : ∀ n, Scoped n self := fun _ => scoped_mono self_closed (Nat.zero_le _)
  have cc : ∀ n, Scoped n consC := fun _ => scoped_mono consC_closed (Nat.zero_le _)
  have oc : ∀ n, Scoped n okC := fun _ => scoped_mono okC_closed (Nat.zero_le _)
  simp [Closed, Scoped, argCont, run, bs, cs, ss, cc, oc]

theorem goodH_closed (ha : Closed a) (he : Closed e) : Closed (goodH a e) := by
  have as : ∀ n, Scoped n a := fun _ => scoped_mono ha (Nat.zero_le _)
  have es : ∀ n, Scoped n e := fun _ => scoped_mono he (Nat.zero_le _)
  have ss : ∀ n, Scoped n self := fun _ => scoped_mono self_closed (Nat.zero_le _)
  have cc : ∀ n, Scoped n consC := fun _ => scoped_mono consC_closed (Nat.zero_le _)
  have oc : ∀ n, Scoped n okC := fun _ => scoped_mono okC_closed (Nat.zero_le _)
  have bc : ∀ n, Scoped n badC := fun _ => scoped_mono badC_closed (Nat.zero_le _)
  have nc : ∀ n, Scoped n nilC := fun _ => scoped_mono nilC_closed (Nat.zero_le _)
  simp [Closed, Scoped, goodH, closureH, argH, badH, select, run, as, es, ss, cc, oc, bc, nc]

theorem bad_handler_red (i : Nat) : Red (ap badH (church i)) (Data.bad i) := by
  have vi : IsLambda (church i) := by cases i <;> exact .lam
  have hs := Step.beta (b := ap badC (v 0)) vi
  simp [plug] at hs
  exact .cons hs (Red.single (bad_step i))

theorem function_bad_red (_ha : Closed a) (_he : Closed e) (i : Nat) :
    Red (select (Data.bad i) (goodH a e) badH) (Data.bad i) :=
  (select_bad i .lam .lam).trans (bad_handler_red i)

theorem argument_bad_red (_hb : Closed b) (_hc : Closed cap) (i : Nat) :
    Red (select (Data.bad i) (argCont b cap) badH) (Data.bad i) :=
  (select_bad i .lam .lam).trans (bad_handler_red i)

theorem run_positive (h : BetaN n (run p e) r) : 0 < n := by
  cases h with
  | app => omega

theorem select_run_inv (h : BetaN n (select (run p e) g b) r) :
    ∃ w nt nk, nt < n ∧ nk < n ∧ BetaN nt (run p e) w ∧ BetaN nk (select w g b) r := by
  cases h with
  | app hf hb hr =>
    cases hf with
    | app ht hg hi =>
      have hp := run_positive ht
      exact ⟨_, _, _, by omega, by omega, ht, .app (.app .lam hg hi) hb hr⟩


theorem closureH_closed (ha : Closed a) (he : Closed e) : Closed (closureH a e) := by
  have as : ∀ n, Scoped n a := fun _ => scoped_mono ha (Nat.zero_le _)
  have es : ∀ n, Scoped n e := fun _ => scoped_mono he (Nat.zero_le _)
  have ss : ∀ n, Scoped n self := fun _ => scoped_mono self_closed (Nat.zero_le _)
  have cc : ∀ n, Scoped n consC := fun _ => scoped_mono consC_closed (Nat.zero_le _)
  have oc : ∀ n, Scoped n okC := fun _ => scoped_mono okC_closed (Nat.zero_le _)
  have bc : ∀ n, Scoped n badC := fun _ => scoped_mono badC_closed (Nat.zero_le _)
  simp [Closed, Scoped, closureH, argH, badH, select, run, as, es, ss, cc, oc, bc]

theorem closure_select (hb : Closed b) (he : Closed e) (hl : Closed l)
    (vv : IsLambda tv) (vl : IsLambda l) (va : IsLambda ta) :
    Red (ap (ap (ap (Data.closure b e) tv) l) ta) (ap (ap l b) e) := by
  have sb : ∀ es d, plug es d b = b := fun _ _ => plug_closed_id hb
  have se : ∀ es d, plug es d e = e := fun _ _ => plug_closed_id he
  have sl : ∀ es d, plug es d l = l := fun _ _ => plug_closed_id hl
  have s1 := Step.beta (b := lam (lam (ap (ap (v 1) b) e))) vv
  simp [plug, sb, se] at s1
  have s2 := Step.beta (b := lam (ap (ap (v 1) b) e)) vl
  simp [plug, sb, se] at s2
  have s3 := Step.beta (b := ap (ap l b) e) va
  simp [plug, sb, se, sl] at s3
  simpa [Data.closure, shift_eq_self_of_scoped hb, shift_eq_self_of_scoped he]
    using Red.cons (.left (.left s1)) (.cons (.left s2) (.cons s3 .refl))

theorem function_good_red (ha : Closed a) (he : Closed e) (hb : Closed b) (hc : Closed cap)
    (vb : IsLambda b) (vc : IsLambda cap) :
    Red (select (Data.ok (Data.closure b cap)) (goodH a e) badH)
      (select (run a e) (argCont b cap) badH) := by
  have sa : ∀ es d, plug es d a = a := fun _ _ => plug_closed_id ha
  have se : ∀ es d, plug es d e = e := fun _ _ => plug_closed_id he
  have sb : ∀ es d, plug es d b = b := fun _ _ => plug_closed_id hb
  have sc : ∀ es d, plug es d cap = cap := fun _ _ => plug_closed_id hc
  have sch : ∀ es d, plug es d (closureH a e) = closureH a e :=
    fun _ _ => plug_closed_id (closureH_closed ha he)
  have sh : ∀ es d, plug es d badH = badH := fun _ _ => plug_closed_id badH_closed
  apply (select_ok (Data.closure_closed hb hc) (goodH_closed ha he) .lam .lam).trans
  have s1 := Step.beta (v := Data.closure b cap)
    (b := ap (ap (ap (v 0) nilC) (closureH a e)) nilC) .lam
  simp [plug, sch] at s1
  have hr : Red (ap (goodH a e) (Data.closure b cap))
      (ap (ap (ap (Data.closure b cap) nilC) (closureH a e)) nilC) := by
    simpa only [goodH] using Red.single s1
  apply hr.trans
  apply (closure_select hb hc (closureH_closed ha he) .lam .lam .lam).trans
  have s2 := Step.beta (b := lam (select (run a e) argH badH)) vb
  simp [plug, select, run, argH, sh, sa, se] at s2
  have s3 := Step.beta (b := select (run a e)
    (lam (run b (ap (ap consC (ap okC (v 0))) (v 1)))) badH) vc
  simp [plug, select, run, sh, sa, se, sb] at s3
  simpa [closureH, argH, argCont, select, run] using Red.cons (.left s2) (.cons s3 .refl)

def extend (payload cap : Term) : Term := ap (ap consC (ap okC payload)) cap

theorem argument_good_red (hb : Closed b) (hc : Closed cap) (hv : Closed payload)
    (vv : IsLambda payload) :
    Red (select (Data.ok payload) (argCont b cap) badH)
      (run b (extend payload cap)) := by
  apply (select_ok hv (argCont_closed hb hc) .lam .lam).trans
  have sb : ∀ es d, plug es d b = b := fun _ _ => plug_closed_id hb
  have sc : ∀ es d, plug es d cap = cap := fun _ _ => plug_closed_id hc
  have hs := Step.beta (b := run b (ap (ap consC (ap okC (v 0))) cap)) vv
  simpa [plug, sb, sc, run, argCont, extend] using Red.single hs

theorem extend_red (hv : PureValue c) (he : PureEnv e) :
    Red (extend (encodeClosure c hv) (encodeEnvironment e he))
      (encodeEnvironment (c :: e) (.cons hv he)) := by
  have vh : IsLambda (encodeClosure c hv) := by cases c; rw [encodeClosure]; exact .lam
  have ho := ok_step (encodeClosure_properties c hv).2 vh
  apply ((Red.right (IsLambda.lam (b := _)) (Red.single ho)).left).trans
  simpa [encodeEnvironment, extend, consC, Builder.compile, Builder.cons, Builder.lams,
    Builder.apps, Builder.ap, Builder.v, List.idxOf_cons] using cons_red
    (Data.ok_closed (encodeClosure_properties c hv).2) (encodeEnvironment_properties e he).2
    .lam (environment_lambda he)

theorem arg_inv (h : BetaN n (ap f a) r) :
    ∃ va na nk, nk ≤ n ∧ BetaN na a va ∧ BetaN nk (ap f va) r := by
  cases h with
  | app hf ha hb =>
    obtain ⟨b, heq⟩ := beta_value ha.forget
    cases heq
    exact ⟨_, _, _, by omega, ha, .app hf .lam hb⟩

theorem run_red (hp : Pure p) (he : PureEnv e) :
    Red (run (encode p hp) (encodeEnvironment e he))
      (dispatch (encode p hp) (encodeEnvironment e he)) :=
  run_unroll (encode_closed hp) (encodeEnvironment_properties e he).2
    (encode_lambda hp) (environment_lambda he)

theorem variable_beta (he : PureEnv e) (i : Nat) :
    Beta (run (encode (.var i) (.var i)) (encodeEnvironment e he))
      (encodeOutcome (lookupResult e i) (lookup_pure he)) :=
  (lookup_beta he i).red_back ((run_red (.var i) he).trans (dispatch_var i he))

theorem lambda_beta (hb : Pure b) (he : PureEnv e) :
    Beta (run (encode (.lam b) (.lam hb)) (encodeEnvironment e he))
      (encodeOutcome (.value (.closure b e)) (.closure hb he)) :=
  (Beta.of_lambda (outcome_lambda _)).red_back
    ((run_red (.lam hb) he).trans (dispatch_lam hb he))

theorem source_beta (h : Direct e p o) (hp : Pure p) (he : PureEnv e) :
    Beta (run (encode p hp) (encodeEnvironment e he)) (encodeOutcome o (direct_pure h hp he)) := by
  induction h with
  | @varBound env i v hv => simpa only [lookupResult, hv] using variable_beta he i
  | @varUnbound env i hv => simpa only [lookupResult, hv] using variable_beta he i
  | lam => exact lambda_beta (pure_lam.mp hp) he
  | appUnbound hf ihf =>
    obtain ⟨hpf, hpa⟩ := pure_app.mp hp
    apply Beta.red_back ((run_red hp he).trans (dispatch_app hpf hpa he))
    apply beta_select (ihf hpf he)
    exact (Beta.of_lambda (outcome_lambda (o := .unbound _) trivial)).red_back
      (function_bad_red (encode_closed hpa) (encodeEnvironment_properties _ he).2 _)
  | appArgUnbound hf ha ihf iha =>
    obtain ⟨hpf, hpa⟩ := pure_app.mp hp
    have hfv := direct_pure hf hpf he
    apply Beta.red_back ((run_red hp he).trans (dispatch_app hpf hpa he))
    apply beta_select (ihf hpf he)
    simp only [encodeOutcome, encodeClosure]
    apply Beta.red_back (function_good_red (encode_closed hpa) (encodeEnvironment_properties _ he).2
      (encode_closed hfv.body) (encodeEnvironment_properties _ hfv.environment).2
      (encode_lambda hfv.body) (environment_lambda hfv.environment))
    apply beta_select (iha hpa he)
    exact (Beta.of_lambda (outcome_lambda (o := .unbound _) trivial)).red_back
      (argument_bad_red (encode_closed hfv.body) (encodeEnvironment_properties _ hfv.environment).2 _)
  | appValue hf ha hb ihf iha ihb =>
    obtain ⟨hpf, hpa⟩ := pure_app.mp hp
    have hfv := direct_pure hf hpf he
    have hav := direct_pure ha hpa he
    apply Beta.red_back ((run_red hp he).trans (dispatch_app hpf hpa he))
    apply beta_select (ihf hpf he)
    simp only [encodeOutcome, encodeClosure]
    apply Beta.red_back (function_good_red (encode_closed hpa) (encodeEnvironment_properties _ he).2
      (encode_closed hfv.body) (encodeEnvironment_properties _ hfv.environment).2
      (encode_lambda hfv.body) (environment_lambda hfv.environment))
    apply beta_select (iha hpa he)
    rw [encodeOutcome]
    apply Beta.red_back (argument_good_red (encode_closed hfv.body)
      (encodeEnvironment_properties _ hfv.environment).2 (encodeClosure_properties _ hav).2
      (by cases hav; rw [encodeClosure]; exact .lam))
    apply beta_arg ((Beta.of_lambda (environment_lambda (.cons hav hfv.environment))).red_back
      (extend_red hav hfv.environment))
    exact ihb hfv.body (.cons hav hfv.environment)

/-- Reflection uses the number of beta contractions, so it applies to every
    terminating interpreter derivation, rather than a selected witness. -/
theorem source_of_betaN (hp : Pure p) (he : PureEnv e)
    (h : BetaN n (run (encode p hp) (encodeEnvironment e he)) r) :
    ∃ o, ∃ ho : PureOutcome o, Direct e p o ∧ r = encodeOutcome o ho := by
  induction n using Nat.strongRecOn generalizing p e r with
  | ind n ih =>
    cases hp with
    | var i =>
      exact ⟨lookupResult e i, lookup_pure he, lookup_direct e i,
        beta_deterministic h.forget (variable_beta he i)⟩
    | lam hb =>
      exact ⟨.value (.closure _ e), .closure hb he, .lam,
        beta_deterministic h.forget (lambda_beta hb he)⟩
    | @app f a hpf hpa =>
      obtain ⟨nd, hd, hdispatch⟩ := h.red (run_red (.app hpf hpa) he)
      obtain ⟨nc, hc, hcore⟩ := hdispatch.red (dispatch_app hpf hpa he)
      obtain ⟨wf, ntf, nkf, htf, hkf, hf, hcont⟩ := select_run_inv hcore
      obtain ⟨of, pof, df, ef⟩ := ih ntf (by omega) hpf he hf
      rw [ef] at hcont
      cases of with
      | unbound i =>
        obtain ⟨nf, hnf, hfinal⟩ := hcont.red
          (function_bad_red (encode_closed hpa) (encodeEnvironment_properties _ he).2 i)
        exact ⟨.unbound i, trivial, .appUnbound df,
          beta_deterministic hfinal.forget (Beta.of_lambda (outcome_lambda (o := .unbound i) trivial))⟩
      | value vf =>
        cases vf with
        | closure b cap =>
          simp only [encodeOutcome, encodeClosure] at hcont
          obtain ⟨ng, hng, harg⟩ := hcont.red
            (function_good_red (encode_closed hpa) (encodeEnvironment_properties _ he).2
              (encode_closed pof.body) (encodeEnvironment_properties _ pof.environment).2
              (encode_lambda pof.body) (environment_lambda pof.environment))
          obtain ⟨wa, nta, nka, hta, hka, ha, hargcont⟩ := select_run_inv harg
          obtain ⟨oa, poa, da, ea⟩ := ih nta (by omega) hpa he ha
          rw [ea] at hargcont
          cases oa with
          | unbound i =>
            obtain ⟨nf, hnf, hfinal⟩ := hargcont.red
              (argument_bad_red (encode_closed pof.body)
                (encodeEnvironment_properties _ pof.environment).2 i)
            exact ⟨.unbound i, trivial, .appArgUnbound df da,
              beta_deterministic hfinal.forget (Beta.of_lambda (outcome_lambda (o := .unbound i) trivial))⟩
          | value va =>
            rw [encodeOutcome] at hargcont
            have vv : IsLambda (encodeClosure va poa) := by
              cases va; rw [encodeClosure]; exact .lam
            obtain ⟨nb, hnb, hbody⟩ := hargcont.red
              (argument_good_red (encode_closed pof.body)
                (encodeEnvironment_properties _ pof.environment).2 (encodeClosure_properties _ poa).2 vv)
            obtain ⟨ev, ne, nk, hk, henv, hcall⟩ := arg_inv hbody
            have er := beta_deterministic henv.forget
              ((Beta.of_lambda (environment_lambda (.cons poa pof.environment))).red_back
                (extend_red poa pof.environment))
            rw [er] at hcall
            obtain ⟨ob, pob, db, eb⟩ := ih nk (by omega) pof.body
              (.cons poa pof.environment) hcall
            exact ⟨ob, pob, .appValue df da db, eb⟩

theorem source_of_beta (hp : Pure p) (he : PureEnv e)
    (h : Beta (run (encode p hp) (encodeEnvironment e he)) r) :
    ∃ o, ∃ ho : PureOutcome o, Direct e p o ∧ r = encodeOutcome o ho := by
  obtain ⟨n, hn⟩ := BetaN.of_beta h
  exact source_of_betaN hp he hn

def fixC : Term := Builder.compile [] Builder.fix

theorem fixC_closed : Closed fixC := by decide +kernel
@[simp] theorem plug_fixC : plug es d fixC = fixC := plug_closed_id fixC_closed

theorem fix_step : Step (ap fixC functional) (ap arm arm) := by
  let rawArm := lam (ap (v 1) (lam (ap (ap (v 1) (v 1)) (v 0))))
  have h := Step.beta (v := functional) (b := ap rawArm rawArm) .lam
  simpa [rawArm, plug, fixC, arm, Builder.compile, Builder.fix, Builder.lams,
    Builder.apps, Builder.ap, Builder.v, List.idxOf_cons] using h

theorem interpreter_eq : interpreterBody = lam (ap (ap (ap fixC functional) (v 0)) nilC) := by
  decide +kernel

theorem fixed_apply_red (hp : Closed p) (he : Closed e) (vp : IsLambda p) (ve : IsLambda e) :
    Red (ap (ap (ap arm arm) p) e) (dispatch p e) := by
  have ep : ClosedTerms [p] := by simpa [ClosedTerms] using hp
  have ee : ClosedTerms [e] := by simpa [ClosedTerms] using he
  have es : ClosedTerms [self] := by simpa [ClosedTerms] using self_closed
  refine .cons (.left (.left arm_step)) (.cons (.left (.left functional_step)) ?_)
  have sp := Step.beta (b := lam (plug [self] 2 core)) vp
  have eqp : plug [p] 1 (plug [self] 2 core) = plug [p, self] 1 core := plug_comp ep es
  simp only [plug, eqp] at sp
  refine .cons (.left sp) ?_
  have se := Step.beta (b := plug [p, self] 1 core) ve
  have eqe : plug [e] 0 (plug [p, self] 1 core) = dispatch p e := by
    exact plug_comp ee (by simpa [ClosedTerms] using And.intro hp self_closed)
  rw [eqe] at se
  exact .cons se .refl

theorem initial_red (hp : Pure p) :
    Red (.app interpreterBody (encode p hp)) (dispatch (encode p hp) (encodeEnvironment [] .nil)) := by
  have hs := Step.beta (b := ap (ap (ap fixC functional) (v 0)) nilC) (encode_lambda hp)
  simp [plug] at hs
  have hstart : Red (.app interpreterBody (encode p hp))
      (ap (ap (ap fixC functional) (encode p hp)) nilC) := by
    simpa only [interpreter_eq] using Red.single hs
  apply hstart.trans
  apply (Red.single (.left (.left fix_step))).trans
  have hr := fixed_apply_red (encode_closed hp) nilC_closed (encode_lambda hp)
    (IsLambda.lam (b := _))
  simpa [encodeEnvironment, nilC, Data.nil, Builder.compile, Builder.nil,
    Builder.lams, Builder.v, List.idxOf_cons] using hr

theorem beta_red_forward (h : Beta t r) (hr : Red t u) : Beta u r := by
  obtain ⟨n, hn⟩ := BetaN.of_beta h
  obtain ⟨_, _, hu⟩ := hn.red hr
  exact hu.forget

theorem interpreter_beta (hp : Pure p) :
    Beta (.app interpreterBody (encode p hp)) r ↔
      ∃ o, ∃ ho : PureOutcome o, Direct [] p o ∧ r = encodeOutcome o ho := by
  constructor
  · intro h
    have hd := beta_red_forward h (initial_red hp)
    exact source_of_beta hp .nil (hd.red_back (run_red hp .nil))
  · rintro ⟨o, ho, hd, rfl⟩
    have hs := source_beta hd hp .nil
    exact (beta_red_forward hs (run_red hp .nil)).red_back (initial_red hp)

end InterpreterProof

/-- Every source derivation is realized by an interpreter result with the exact
    existing data representation. -/
theorem interpreter_complete (hp : Pure p) (h : Direct [] p o) :
    ∃ w, Direct [] (.app interpreterBody (encode p hp)) w ∧ Represents o w := by
  have ho := direct_pure h hp .nil
  have hb := (InterpreterProof.interpreter_beta hp).mpr ⟨o, ho, h, rfl⟩
  obtain ⟨v, hd, hr⟩ := beta_direct_closed hb ⟨interpreterBody_closed, encode_closed hp⟩
  exact ⟨.value v, hd, Represents_of_readback ho hr⟩

/-- Every interpreter derivation decodes to a source derivation. In particular,
    raw errors and malformed encoded outputs cannot arise on pure input. -/
theorem interpreter_sound (hp : Pure p)
    (h : Direct [] (.app interpreterBody (encode p hp)) w) :
    ∃ o, Direct [] p o ∧ Represents o w := by
  obtain ⟨v, rfl, _, hb⟩ := direct_beta h .nil ⟨interpreterBody_closed, encode_closed hp⟩
  have hb' : Beta (.app interpreterBody (encode p hp)) (readback v) := by
    simpa only [List.map_nil, plug_closed_id (t := .app interpreterBody (encode p hp))
      ⟨interpreterBody_closed, encode_closed hp⟩] using hb
  obtain ⟨o, ho, hd, hr⟩ := (InterpreterProof.interpreter_beta hp).mp hb'
  exact ⟨o, hd, Represents_of_readback ho hr⟩

end Circular
