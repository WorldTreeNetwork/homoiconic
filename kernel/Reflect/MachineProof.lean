import Reflect.Machine

namespace Reflect
variable [Ops]

theorem run_add : ∀ n m s, run (n + m) s = run m (run n s) := by
  intro n m
  induction n with
  | zero => intro s; simp [run]
  | succ n ih =>
    intro s
    have : n + 1 + m = (n + m) + 1 := by omega
    rw [this]
    simp only [run]
    exact ih (step s)

theorem run_halted : ∀ n o, run n (.halted o) = .halted o := by
  intro n o
  induction n with
  | zero => rfl
  | succ n ih => simp [run, step, ih]

omit [Ops] in
theorem decomp_comp : ∀ t k stk, decomp (comp t k) stk = decomp k (t :: stk) := by
  intro t
  induction t with
  | var i => intro k stk; simp [comp, decomp]
  | lam b ihb => intro k stk; simp [comp, decomp, ihb]
  | app f a ihf iha => intro k stk; simp [comp, decomp, ihf, iha]
  | lit d => intro k stk; simp [comp, decomp]
  | succ t iht => intro k stk; simp [comp, decomp, iht]
  | cons a b iha ihb => intro k stk; simp [comp, decomp, iha, ihb]
  | prim c x ihc ihx => intro k stk; simp [comp, decomp, ihc, ihx]
  | dcase s z sc n c ihs ihz ihsc ihn ihc =>
    intro k stk; simp [comp, decomp, ihs, ihz, ihsc, ihn, ihc]

omit [Ops] in
theorem decompile_compile : ∀ t, decompile (compile t) = some t := by
  intro t
  simp [decompile, compile, decomp_comp, decomp]

theorem depth_step (s : State) : depth (step s) ≤ depth s + 1 := by
  unfold step
  split <;> (try split) <;> simp_all [depth] <;> omega

theorem depth_bound : ∀ n s, depth (run n s) ≤ depth s + n := by
  intro n
  induction n with
  | zero => intro s; simp [run]
  | succ n ih =>
    intro s
    have h1 := ih (step s)
    have h2 := depth_step s
    simp only [run]
    omega

namespace MP

-- Compile a source value to the machine value that represents it.
mutual
  def injV : Value → MValue
    | .closure b env => .closure (comp b .done) (injE env)
    | .data d => .data d
  def injE : List Value → List MValue
    | [] => []
    | v :: vs => injV v :: injE vs
end

omit [Ops] in
mutual
  theorem readValue_injV : ∀ v : Value, readValue (injV v) = some v
    | .closure b env => by
      have h1 : decomp (comp b .done) [] = some b := decompile_compile b
      have h2 := readEnv_injE env
      simp [injV, readValue, h1, h2]
    | .data d => by simp [injV, readValue]
  theorem readEnv_injE : ∀ vs : List Value, readEnv (injE vs) = some vs
    | [] => by simp [injE, readEnv]
    | v :: vs => by
      have h1 := readValue_injV v
      have h2 := readEnv_injE vs
      simp [injE, readEnv, h1, h2]
end

omit [Ops] in
theorem injE_get : ∀ (env : List Value) (i : Nat), (injE env)[i]? = (env[i]?).map injV := by
  intro env
  induction env with
  | nil => intro i; simp [injE]
  | cons v vs ih =>
    intro i
    cases i with
    | zero => simp [injE]
    | succ i => simp [injE, ih]

inductive ErrM : MOutcome → Outcome → Prop
  | unbound (i : Nat) : ErrM (.unbound i) (.unbound i)
  | wrong : ErrM .wrong .wrong

omit [Ops] in
theorem ErrM.isError {w e} (h : ErrM w e) : e.IsError := by
  cases h <;> simp [Outcome.IsError]

omit [Ops] in
theorem ErrM.read {w e} (h : ErrM w e) : readOutcome w = some e := by
  cases h <;> rfl

theorem run_one (s : State) : run 1 s = step s := rfl

theorem run_to {a b S S1 S2} (h1 : run a S = S1) (h2 : run b S1 = S2) :
    run (a + b) S = S2 := by
  rw [run_add, h1, h2]

theorem halted_unique {n m S w1 w2} (h1 : run n S = .halted w1) (h2 : run m S = .halted w2) :
    w1 = w2 := by
  rcases Nat.le_total n m with h | h
  · have : run m S = run (m - n) (run n S) := by
      rw [← run_add]; congr 1; omega
    rw [this, h1, run_halted] at h2
    injection h2
  · have : run n S = run (n - m) (run m S) := by
      rw [← run_add]; congr 1; omega
    rw [this, h2, run_halted] at h1
    injection h1 with h1; exact h1.symm

/-- Started at `S`, the machine reaches the continuation `k` with the result of
    evaluating to `o` pushed, or halts with the matching error. -/
@[reducible] def Reach (S : State) (o : Outcome) (k : Code) (M : MEnv)
    (stk : List MValue) (frs : List Frame) : Prop :=
  match o with
  | .value v => ∃ n, run n S = .running k M (injV v :: stk) frs
  | .unbound i => ∃ n, run n S = .halted (.unbound i)
  | .wrong => ∃ n, run n S = .halted .wrong

theorem Reach.of_run {a S S1 o k M stk frs} (h : run a S = S1)
    (r : Reach S1 o k M stk frs) : Reach S o k M stk frs := by
  cases o with
  | value v => obtain ⟨n, hn⟩ := r; exact ⟨a + n, run_to h hn⟩
  | unbound i => obtain ⟨n, hn⟩ := r; exact ⟨a + n, run_to h hn⟩
  | wrong => obtain ⟨n, hn⟩ := r; exact ⟨a + n, run_to h hn⟩

theorem Reach.step {S o k M stk frs} (r : Reach (step S) o k M stk frs) :
    Reach S o k M stk frs := Reach.of_run (a := 1) rfl r

theorem Reach.lift_err {S e k M stk frs k' M' stk' frs'} (he : e.IsError)
    (r : Reach S e k M stk frs) : Reach S e k' M' stk' frs' := by
  cases e with
  | value v => exact he.elim
  | unbound i => exact r
  | wrong => exact r

theorem step_done_frame (E : MEnv) (stk : List MValue) (k : Code) (M : MEnv) (frs : List Frame) :
    step (.running .done E stk (⟨k, M⟩ :: frs)) = .running k M stk frs := by
  rcases stk with _ | ⟨a, _ | ⟨b, stk⟩⟩ <;> rfl

theorem Reach.block {Sb o k M E stk frs} (r : Reach Sb o .done E stk (⟨k, M⟩ :: frs)) :
    Reach Sb o k M stk frs := by
  cases o with
  | value v =>
    obtain ⟨n, hn⟩ := r
    exact ⟨n + 1, by rw [run_add, hn, run_one, step_done_frame]⟩
  | unbound i => exact r
  | wrong => exact r

theorem fwd {env t o} (h : Direct env t o) :
    ∀ k stk frs, Reach (.running (comp t k) (injE env) stk frs) o k (injE env) stk frs := by
  induction h with
  | varBound hb =>
    intro k stk frs
    exact ⟨1, by rw [run_one]; simp [comp, step, injE_get, hb]⟩
  | varUnbound hb =>
    intro k stk frs
    exact ⟨1, by rw [run_one]; simp [comp, step, injE_get, hb]⟩
  | lam => intro k stk frs; exact ⟨1, rfl⟩
  | lit => intro k stk frs; exact ⟨1, rfl⟩
  | appFunError hf he ihf =>
    intro k stk frs
    exact (ihf (.checkFun (comp _ (.apply k))) stk frs).lift_err he
  | appData hf ihf =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihf (.checkFun (comp _ (.apply k))) stk frs
    exact Reach.of_run h1 (Reach.step ⟨0, rfl⟩)
  | appArgError hf ha he ihf iha =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihf (.checkFun (comp _ (.apply k))) stk frs
    refine Reach.of_run h1 (Reach.step ?_)
    exact (iha (.apply k) _ frs).lift_err he
  | appValue hf ha hb ihf iha ihb =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihf (.checkFun (comp _ (.apply k))) stk frs
    obtain ⟨n2, h2⟩ := iha (.apply k) _ frs
    refine Reach.of_run h1 (Reach.step (Reach.of_run h2 (Reach.step ?_)))
    exact Reach.block (ihb .done stk (⟨k, _⟩ :: frs))
  | succNat h ih =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ih (.succ k) stk frs
    exact ⟨n1 + 1, run_to h1 rfl⟩
  | succArr h ih =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ih (.succ k) stk frs
    exact Reach.of_run h1 (Reach.step ⟨0, rfl⟩)
  | succName h ih =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ih (.succ k) stk frs
    exact ⟨n1 + 1, run_to h1 rfl⟩
  | succClosure h ih =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ih (.succ k) stk frs
    exact Reach.of_run h1 (Reach.step ⟨0, rfl⟩)
  | succError h he ih =>
    intro k stk frs
    exact (ih (.succ k) stk frs).lift_err he
  | consArr ha hb iha ihb =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := iha (.checkData (comp _ (.cons k))) stk frs
    obtain ⟨n2, h2⟩ := ihb (.cons k) (.data _ :: stk) frs
    exact ⟨n1 + 1 + (n2 + 1), run_to (run_to h1 rfl) (run_to h2 rfl)⟩
  | consHeadClosure ha iha =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := iha (.checkData (comp _ (.cons k))) stk frs
    exact Reach.of_run h1 (Reach.step ⟨0, rfl⟩)
  | consHeadError ha he iha =>
    intro k stk frs
    exact (iha (.checkData (comp _ (.cons k))) stk frs).lift_err he
  | consTailNat ha hb iha ihb =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := iha (.checkData (comp _ (.cons k))) stk frs
    obtain ⟨n2, h2⟩ := ihb (.cons k) (.data _ :: stk) frs
    exact Reach.of_run h1 (Reach.step (Reach.of_run h2 (Reach.step ⟨0, rfl⟩)))
  | consTailName ha hb iha ihb =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := iha (.checkData (comp _ (.cons k))) stk frs
    obtain ⟨n2, h2⟩ := ihb (.cons k) (.data _ :: stk) frs
    exact Reach.of_run h1 (Reach.step (Reach.of_run h2 (Reach.step ⟨0, rfl⟩)))
  | consTailClosure ha hb iha ihb =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := iha (.checkData (comp _ (.cons k))) stk frs
    obtain ⟨n2, h2⟩ := ihb (.cons k) (.data _ :: stk) frs
    exact Reach.of_run h1 (Reach.step (Reach.of_run h2 (Reach.step ⟨0, rfl⟩)))
  | consTailError ha hb he iha ihb =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := iha (.checkData (comp _ (.cons k))) stk frs
    refine Reach.of_run h1 (Reach.step ?_)
    exact (ihb (.cons k) (.data _ :: stk) frs).lift_err he
  | primData hc hx ihc ihx =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihc (.checkNat (comp _ (.prim k))) stk frs
    obtain ⟨n2, h2⟩ := ihx (.prim k) (.data _ :: stk) frs
    exact ⟨n1 + 1 + (n2 + 1), run_to (run_to h1 rfl) (run_to h2 rfl)⟩
  | primCodeArr hc ihc =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihc (.checkNat (comp _ (.prim k))) stk frs
    exact Reach.of_run h1 (Reach.step ⟨0, rfl⟩)
  | primCodeClosure hc ihc =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihc (.checkNat (comp _ (.prim k))) stk frs
    exact Reach.of_run h1 (Reach.step ⟨0, rfl⟩)
  | primCodeError hc he ihc =>
    intro k stk frs
    exact (ihc (.checkNat (comp _ (.prim k))) stk frs).lift_err he
  | primArgClosure hc hx ihc ihx =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihc (.checkNat (comp _ (.prim k))) stk frs
    obtain ⟨n2, h2⟩ := ihx (.prim k) (.data _ :: stk) frs
    exact Reach.of_run h1 (Reach.step (Reach.of_run h2 (Reach.step ⟨0, rfl⟩)))
  | primArgError hc hx he ihc ihx =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihc (.checkNat (comp _ (.prim k))) stk frs
    refine Reach.of_run h1 (Reach.step ?_)
    exact (ihx (.prim k) (.data _ :: stk) frs).lift_err he
  | primNameData hc hx ihc ihx =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihc (.checkNat (comp _ (.prim k))) stk frs
    obtain ⟨n2, h2⟩ := ihx (.prim k) (.data _ :: stk) frs
    exact ⟨n1 + 1 + (n2 + 1), run_to (run_to h1 rfl) (run_to h2 rfl)⟩
  | primNameArgClosure hc hx ihc ihx =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihc (.checkNat (comp _ (.prim k))) stk frs
    obtain ⟨n2, h2⟩ := ihx (.prim k) (.data _ :: stk) frs
    exact Reach.of_run h1 (Reach.step (Reach.of_run h2 (Reach.step ⟨0, rfl⟩)))
  | primNameArgError hc hx he ihc ihx =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihc (.checkNat (comp _ (.prim k))) stk frs
    refine Reach.of_run h1 (Reach.step ?_)
    exact (ihx (.prim k) (.data _ :: stk) frs).lift_err he
  | caseNameZero hs hz ihs ihz =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihs (.dcase (comp _ .done) (comp _ .done) (comp _ .done) (comp _ .done) k) stk frs
    refine Reach.of_run h1 (Reach.step ?_)
    exact Reach.block (ihz .done stk (⟨k, _⟩ :: frs))
  | caseNameSucc hs hsc ihs ihsc =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihs (.dcase (comp _ .done) (comp _ .done) (comp _ .done) (comp _ .done) k) stk frs
    refine Reach.of_run h1 (Reach.step ?_)
    exact Reach.block (ihsc .done stk (⟨k, _⟩ :: frs))
  | caseZero hs hz ihs ihz =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihs (.dcase (comp _ .done) (comp _ .done) (comp _ .done) (comp _ .done) k) stk frs
    refine Reach.of_run h1 (Reach.step ?_)
    exact Reach.block (ihz .done stk (⟨k, _⟩ :: frs))
  | caseSucc hs hsc ihs ihsc =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihs (.dcase (comp _ .done) (comp _ .done) (comp _ .done) (comp _ .done) k) stk frs
    refine Reach.of_run h1 (Reach.step ?_)
    exact Reach.block (ihsc .done stk (⟨k, _⟩ :: frs))
  | caseNil hs hn ihs ihn =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihs (.dcase (comp _ .done) (comp _ .done) (comp _ .done) (comp _ .done) k) stk frs
    refine Reach.of_run h1 (Reach.step ?_)
    exact Reach.block (ihn .done stk (⟨k, _⟩ :: frs))
  | caseCons hs hc ihs ihc =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihs (.dcase (comp _ .done) (comp _ .done) (comp _ .done) (comp _ .done) k) stk frs
    refine Reach.of_run h1 (Reach.step ?_)
    exact Reach.block (ihc .done stk (⟨k, _⟩ :: frs))
  | caseClosure hs ihs =>
    intro k stk frs
    obtain ⟨n1, h1⟩ := ihs (.dcase (comp _ .done) (comp _ .done) (comp _ .done) (comp _ .done) k) stk frs
    exact Reach.of_run h1 (Reach.step ⟨0, rfl⟩)
  | caseError hs he ihs =>
    intro k stk frs
    exact (ihs (.dcase (comp _ .done) (comp _ .done) (comp _ .done) (comp _ .done) k) stk frs).lift_err he

theorem lt_of_halt {n m S w c e s f} (h : run n S = .halted w)
    (h1 : run m S = .running c e s f) : m < n := by
  rcases Nat.lt_or_ge m n with hlt | hle
  · exact hlt
  exfalso
  have : run m S = run (m - n) (run n S) := by
    rw [← run_add]; congr 1; omega
  rw [this, h, run_halted] at h1
  cases h1

theorem advance {n m S w c e s f} (h : run n S = .halted w)
    (h1 : run m S = .running c e s f) :
    ∃ n', n' < n ∧ run n' (step (.running c e s f)) = .halted w ∧
      run (m + 1) S = step (.running c e s f) := by
  have hlt := lt_of_halt h h1
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt hlt
  have h2 : run (m + 1) S = step (.running c e s f) := by
    rw [run_add m 1, h1]; rfl
  refine ⟨j, by omega, ?_, h2⟩
  have : n = (m + 1) + j := by omega
  rw [this, run_add, h2] at h
  exact h

def Concl (w : MOutcome) (env : Env) (t : Term) (k : Code) (stk : List MValue)
    (frs : List Frame) : Prop :=
  (∃ e, ErrM w e ∧ Direct env t e) ∨
  (∃ m v, Direct env t (.value v) ∧
    run m (.running (comp t k) (injE env) stk frs) =
      .running k (injE env) (injV v :: stk) frs)

def Rev (n : Nat) : Prop :=
  ∀ t env k stk frs w, run n (.running (comp t k) (injE env) stk frs) = .halted w →
    Concl w env t k stk frs

theorem blk {n n'} (ihn : ∀ n' < n, Rev n') (hlt : n' < n) {w env' b stk k M frs}
    (h : run n' (.running (comp b .done) (injE env') stk (⟨k, M⟩ :: frs)) = .halted w) :
    (∃ e, ErrM w e ∧ Direct env' b e) ∨
    (∃ m v, Direct env' b (.value v) ∧
      run m (.running (comp b .done) (injE env') stk (⟨k, M⟩ :: frs)) =
        .running k M (injV v :: stk) frs) := by
  rcases ihn n' hlt b env' .done stk _ w h with hc | ⟨m, v, hd, hm⟩
  · exact Or.inl hc
  · exact Or.inr ⟨m + 1, v, hd, by rw [run_add, hm, run_one, step_done_frame]⟩

theorem rev : ∀ n, Rev n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    intro t
    induction t with
    | var i =>
      intro env k stk frs w h
      cases hg : env[i]? with
      | some v =>
        refine Or.inr ⟨1, v, Direct.varBound hg, ?_⟩
        rw [run_one]; simp [comp, step, injE_get, hg]
      | none =>
        refine Or.inl ?_
        obtain ⟨n', _, hn', _⟩ := advance (m := 0) h rfl
        have hst : step (.running (comp (.var i) k) (injE env) stk frs) = .halted (.unbound i) := by
          simp [comp, step, injE_get, hg]
        rw [hst, run_halted] at hn'
        cases hn'
        exact ⟨.unbound i, .unbound i, Direct.varUnbound hg⟩
    | lam b ihb =>
      intro env k stk frs w h
      exact Or.inr ⟨1, .closure b env, Direct.lam, rfl⟩
    | lit d =>
      intro env k stk frs w h
      exact Or.inr ⟨1, .data d, Direct.lit, rfl⟩
    | succ t iht =>
      intro env k stk frs w h
      rcases iht env (.succ k) stk frs w h with ⟨e, he, hd⟩ | ⟨m, v, hd, hm⟩
      · exact Or.inl ⟨e, he, Direct.succError hd he.isError⟩
      · obtain ⟨n', hlt, hn', hrun⟩ := advance h hm
        cases v with
        | closure b cap =>
          have hst : step (.running (.succ k) (injE env) (injV (.closure b cap) :: stk) frs) =
              .halted .wrong := rfl
          rw [hst, run_halted] at hn'
          cases hn'
          exact Or.inl ⟨.wrong, .wrong, Direct.succClosure hd⟩
        | data d =>
          cases d with
          | arr xs =>
            have hst : step (.running (.succ k) (injE env) (injV (.data (.arr xs)) :: stk) frs) =
                .halted .wrong := rfl
            rw [hst, run_halted] at hn'
            cases hn'
            exact Or.inl ⟨.wrong, .wrong, Direct.succArr hd⟩
          | nat j => exact Or.inr ⟨m + 1, .data (.nat (j + 1)), Direct.succNat hd, hrun⟩
          | name j => exact Or.inr ⟨m + 1, .data (.nat (j + 1)), Direct.succName hd, hrun⟩
    | app f a ihf iha =>
      intro env k stk frs w h
      rcases ihf env (.checkFun (comp a (.apply k))) stk frs w h with
        ⟨e, he, hd⟩ | ⟨m1, vf, hdf, hm1⟩
      · exact Or.inl ⟨e, he, Direct.appFunError hd he.isError⟩
      · obtain ⟨n1, hlt1, hn1, hrun1⟩ := advance h hm1
        cases vf with
        | data d =>
          have hst : step (.running (.checkFun (comp a (.apply k))) (injE env)
              (injV (.data d) :: stk) frs) = .halted .wrong := rfl
          rw [hst, run_halted] at hn1
          cases hn1
          exact Or.inl ⟨.wrong, .wrong, Direct.appData hdf⟩
        | closure b cap =>
          have hst : step (.running (.checkFun (comp a (.apply k))) (injE env)
              (injV (.closure b cap) :: stk) frs) =
              .running (comp a (.apply k)) (injE env) (injV (.closure b cap) :: stk) frs := rfl
          rw [hst] at hn1 hrun1
          rcases ihn n1 hlt1 a env (.apply k) (injV (.closure b cap) :: stk) frs w hn1 with
            ⟨e, he, hd⟩ | ⟨m2, va, hda, hm2⟩
          · exact Or.inl ⟨e, he, Direct.appArgError hdf hd he.isError⟩
          · obtain ⟨n2, hlt2, hn2, hrun2⟩ := advance hn1 hm2
            have hst2 : step (.running (.apply k) (injE env)
                (injV va :: injV (.closure b cap) :: stk) frs) =
                .running (comp b .done) (injE (va :: cap)) stk (⟨k, injE env⟩ :: frs) := rfl
            rw [hst2] at hn2 hrun2
            rcases blk ihn (Nat.lt_trans hlt2 hlt1) hn2 with ⟨e, he, hd⟩ | ⟨m3, vb, hdb, hm3⟩
            · exact Or.inl ⟨e, he, Direct.appValue hdf hda hd⟩
            · exact Or.inr ⟨(m1 + 1) + ((m2 + 1) + m3), vb, Direct.appValue hdf hda hdb,
                run_to hrun1 (run_to hrun2 hm3)⟩
    | cons a b iha ihb =>
      intro env k stk frs w h
      rcases iha env (.checkData (comp b (.cons k))) stk frs w h with
        ⟨e, he, hd⟩ | ⟨m1, va, hda, hm1⟩
      · exact Or.inl ⟨e, he, Direct.consHeadError hd he.isError⟩
      · obtain ⟨n1, hlt1, hn1, hrun1⟩ := advance h hm1
        cases va with
        | closure c cap =>
          have hst : step (.running (.checkData (comp b (.cons k))) (injE env)
              (injV (.closure c cap) :: stk) frs) = .halted .wrong := rfl
          rw [hst, run_halted] at hn1
          cases hn1
          exact Or.inl ⟨.wrong, .wrong, Direct.consHeadClosure hda⟩
        | data x =>
          have hst : step (.running (.checkData (comp b (.cons k))) (injE env)
              (injV (.data x) :: stk) frs) =
              .running (comp b (.cons k)) (injE env) (.data x :: stk) frs := rfl
          rw [hst] at hn1 hrun1
          rcases ihn n1 hlt1 b env (.cons k) (.data x :: stk) frs w hn1 with
            ⟨e, he, hd⟩ | ⟨m2, vb, hdb, hm2⟩
          · exact Or.inl ⟨e, he, Direct.consTailError hda hd he.isError⟩
          · obtain ⟨n2, hlt2, hn2, hrun2⟩ := advance hn1 hm2
            cases vb with
            | closure c cap =>
              have hst2 : step (.running (.cons k) (injE env)
                  (injV (.closure c cap) :: .data x :: stk) frs) = .halted .wrong := rfl
              rw [hst2, run_halted] at hn2
              cases hn2
              exact Or.inl ⟨.wrong, .wrong, Direct.consTailClosure hda hdb⟩
            | data d =>
              cases d with
              | nat j =>
                have hst2 : step (.running (.cons k) (injE env)
                    (injV (.data (.nat j)) :: .data x :: stk) frs) = .halted .wrong := rfl
                rw [hst2, run_halted] at hn2
                cases hn2
                exact Or.inl ⟨.wrong, .wrong, Direct.consTailNat hda hdb⟩
              | name j =>
                have hst2 : step (.running (.cons k) (injE env)
                    (injV (.data (.name j)) :: .data x :: stk) frs) = .halted .wrong := rfl
                rw [hst2, run_halted] at hn2
                cases hn2
                exact Or.inl ⟨.wrong, .wrong, Direct.consTailName hda hdb⟩
              | arr xs =>
                exact Or.inr ⟨(m1 + 1) + (m2 + 1), .data (.arr (x :: xs)),
                  Direct.consArr hda hdb, run_to hrun1 hrun2⟩
    | prim c x ihc ihx =>
      intro env k stk frs w h
      rcases ihc env (.checkNat (comp x (.prim k))) stk frs w h with
        ⟨e, he, hd⟩ | ⟨m1, vc, hdc, hm1⟩
      · exact Or.inl ⟨e, he, Direct.primCodeError hd he.isError⟩
      · obtain ⟨n1, hlt1, hn1, hrun1⟩ := advance h hm1
        cases vc with
        | closure b cap =>
          have hst : step (.running (.checkNat (comp x (.prim k))) (injE env)
              (injV (.closure b cap) :: stk) frs) = .halted .wrong := rfl
          rw [hst, run_halted] at hn1
          cases hn1
          exact Or.inl ⟨.wrong, .wrong, Direct.primCodeClosure hdc⟩
        | data dc =>
          cases dc with
          | arr xs =>
            have hst : step (.running (.checkNat (comp x (.prim k))) (injE env)
                (injV (.data (.arr xs)) :: stk) frs) = .halted .wrong := rfl
            rw [hst, run_halted] at hn1
            cases hn1
            exact Or.inl ⟨.wrong, .wrong, Direct.primCodeArr hdc⟩
          | nat j =>
            have hst : step (.running (.checkNat (comp x (.prim k))) (injE env)
                (injV (.data (.nat j)) :: stk) frs) =
                .running (comp x (.prim k)) (injE env) (.data (.nat j) :: stk) frs := rfl
            rw [hst] at hn1 hrun1
            rcases ihn n1 hlt1 x env (.prim k) (.data (.nat j) :: stk) frs w hn1 with
              ⟨e, he, hd⟩ | ⟨m2, vx, hdx, hm2⟩
            · exact Or.inl ⟨e, he, Direct.primArgError hdc hd he.isError⟩
            · obtain ⟨n2, hlt2, hn2, hrun2⟩ := advance hn1 hm2
              cases vx with
              | closure b cap =>
                have hst2 : step (.running (.prim k) (injE env)
                    (injV (.closure b cap) :: .data (.nat j) :: stk) frs) = .halted .wrong := rfl
                rw [hst2, run_halted] at hn2
                cases hn2
                exact Or.inl ⟨.wrong, .wrong, Direct.primArgClosure hdc hdx⟩
              | data d =>
                exact Or.inr ⟨(m1 + 1) + (m2 + 1), .data (Ops.op j d),
                  Direct.primData hdc hdx, run_to hrun1 hrun2⟩
          | name j =>
            have hst : step (.running (.checkNat (comp x (.prim k))) (injE env)
                (injV (.data (.name j)) :: stk) frs) =
                .running (comp x (.prim k)) (injE env) (.data (.name j) :: stk) frs := rfl
            rw [hst] at hn1 hrun1
            rcases ihn n1 hlt1 x env (.prim k) (.data (.name j) :: stk) frs w hn1 with
              ⟨e, he, hd⟩ | ⟨m2, vx, hdx, hm2⟩
            · exact Or.inl ⟨e, he, Direct.primNameArgError hdc hd he.isError⟩
            · obtain ⟨n2, hlt2, hn2, hrun2⟩ := advance hn1 hm2
              cases vx with
              | closure b cap =>
                have hst2 : step (.running (.prim k) (injE env)
                    (injV (.closure b cap) :: .data (.name j) :: stk) frs) = .halted .wrong := rfl
                rw [hst2, run_halted] at hn2
                cases hn2
                exact Or.inl ⟨.wrong, .wrong, Direct.primNameArgClosure hdc hdx⟩
              | data d =>
                exact Or.inr ⟨(m1 + 1) + (m2 + 1), .data (Ops.op j d),
                  Direct.primNameData hdc hdx, run_to hrun1 hrun2⟩
    | dcase s z sc nl c ihs ihz ihsc ihnl ihc =>
      intro env k stk frs w h
      rcases ihs env (.dcase (comp z .done) (comp sc .done) (comp nl .done) (comp c .done) k)
          stk frs w h with ⟨e, he, hd⟩ | ⟨m1, vs, hds, hm1⟩
      · exact Or.inl ⟨e, he, Direct.caseError hd he.isError⟩
      · obtain ⟨n1, hlt1, hn1, hrun1⟩ := advance h hm1
        cases vs with
        | closure b cap =>
          have hst : step (.running (.dcase (comp z .done) (comp sc .done) (comp nl .done)
              (comp c .done) k) (injE env) (injV (.closure b cap) :: stk) frs) =
              .halted .wrong := rfl
          rw [hst, run_halted] at hn1
          cases hn1
          exact Or.inl ⟨.wrong, .wrong, Direct.caseClosure hds⟩
        | data d =>
          cases d with
          | nat j =>
            cases j with
            | zero =>
              have hst : step (.running (.dcase (comp z .done) (comp sc .done) (comp nl .done)
                  (comp c .done) k) (injE env) (injV (.data (.nat 0)) :: stk) frs) =
                  .running (comp z .done) (injE env) stk (⟨k, injE env⟩ :: frs) := rfl
              rw [hst] at hn1 hrun1
              rcases blk ihn hlt1 hn1 with ⟨e, he, hd⟩ | ⟨m2, vz, hdz, hm2⟩
              · exact Or.inl ⟨e, he, Direct.caseZero hds hd⟩
              · exact Or.inr ⟨(m1 + 1) + m2, vz, Direct.caseZero hds hdz, run_to hrun1 hm2⟩
            | succ j =>
              have hst : step (.running (.dcase (comp z .done) (comp sc .done) (comp nl .done)
                  (comp c .done) k) (injE env) (injV (.data (.nat (j + 1))) :: stk) frs) =
                  .running (comp sc .done) (.data (.nat j) :: injE env) stk
                    (⟨k, injE env⟩ :: frs) := rfl
              rw [hst] at hn1 hrun1
              rcases blk (env' := .data (.nat j) :: env) ihn hlt1 hn1 with
                ⟨e, he, hd⟩ | ⟨m2, vz, hdz, hm2⟩
              · exact Or.inl ⟨e, he, Direct.caseSucc hds hd⟩
              · exact Or.inr ⟨(m1 + 1) + m2, vz, Direct.caseSucc hds hdz, run_to hrun1 hm2⟩
          | name j =>
            cases j with
            | zero =>
              have hst : step (.running (.dcase (comp z .done) (comp sc .done) (comp nl .done)
                  (comp c .done) k) (injE env) (injV (.data (.name 0)) :: stk) frs) =
                  .running (comp z .done) (injE env) stk (⟨k, injE env⟩ :: frs) := rfl
              rw [hst] at hn1 hrun1
              rcases blk ihn hlt1 hn1 with ⟨e, he, hd⟩ | ⟨m2, vz, hdz, hm2⟩
              · exact Or.inl ⟨e, he, Direct.caseNameZero hds hd⟩
              · exact Or.inr ⟨(m1 + 1) + m2, vz, Direct.caseNameZero hds hdz, run_to hrun1 hm2⟩
            | succ j =>
              have hst : step (.running (.dcase (comp z .done) (comp sc .done) (comp nl .done)
                  (comp c .done) k) (injE env) (injV (.data (.name (j + 1))) :: stk) frs) =
                  .running (comp sc .done) (.data (.nat j) :: injE env) stk
                    (⟨k, injE env⟩ :: frs) := rfl
              rw [hst] at hn1 hrun1
              rcases blk (env' := .data (.nat j) :: env) ihn hlt1 hn1 with
                ⟨e, he, hd⟩ | ⟨m2, vz, hdz, hm2⟩
              · exact Or.inl ⟨e, he, Direct.caseNameSucc hds hd⟩
              · exact Or.inr ⟨(m1 + 1) + m2, vz, Direct.caseNameSucc hds hdz, run_to hrun1 hm2⟩
          | arr xs =>
            cases xs with
            | nil =>
              have hst : step (.running (.dcase (comp z .done) (comp sc .done) (comp nl .done)
                  (comp c .done) k) (injE env) (injV (.data (.arr [])) :: stk) frs) =
                  .running (comp nl .done) (injE env) stk (⟨k, injE env⟩ :: frs) := rfl
              rw [hst] at hn1 hrun1
              rcases blk ihn hlt1 hn1 with ⟨e, he, hd⟩ | ⟨m2, vz, hdz, hm2⟩
              · exact Or.inl ⟨e, he, Direct.caseNil hds hd⟩
              · exact Or.inr ⟨(m1 + 1) + m2, vz, Direct.caseNil hds hdz, run_to hrun1 hm2⟩
            | cons x xs =>
              have hst : step (.running (.dcase (comp z .done) (comp sc .done) (comp nl .done)
                  (comp c .done) k) (injE env) (injV (.data (.arr (x :: xs))) :: stk) frs) =
                  .running (comp c .done) (.data (.arr xs) :: .data x :: injE env) stk
                    (⟨k, injE env⟩ :: frs) := rfl
              rw [hst] at hn1 hrun1
              rcases blk (env' := .data (.arr xs) :: .data x :: env) ihn hlt1 hn1 with
                ⟨e, he, hd⟩ | ⟨m2, vz, hdz, hm2⟩
              · exact Or.inl ⟨e, he, Direct.caseCons hds hd⟩
              · exact Or.inr ⟨(m1 + 1) + m2, vz, Direct.caseCons hds hdz, run_to hrun1 hm2⟩

end MP

open MP in
theorem machine_correct : ∀ t o,
    Direct [] t o ↔
    ∃ n w, run n (load (compile t)) = .halted w ∧ readOutcome w = some o := by
  intro t o
  constructor
  · intro h
    have r := fwd h .done [] []
    cases o with
    | value v =>
      obtain ⟨n, hn⟩ := r
      refine ⟨n + 1, .value (injV v), ?_, ?_⟩
      · have : run n (load (compile t)) = .running .done [] [injV v] [] := hn
        rw [run_add, this]; rfl
      · simp [readOutcome, readValue_injV]
    | unbound i =>
      obtain ⟨n, hn⟩ := r
      exact ⟨n, _, hn, rfl⟩
    | wrong =>
      obtain ⟨n, hn⟩ := r
      exact ⟨n, _, hn, rfl⟩
  · rintro ⟨n, w, hn, hr⟩
    rcases rev n t [] .done [] [] w hn with ⟨e, he, hd⟩ | ⟨m, v, hd, hm⟩
    · rw [he.read] at hr
      cases hr
      exact hd
    · have h1 : run (m + 1) (load (compile t)) = .halted (.value (injV v)) := by
        have : run m (load (compile t)) = .running .done [] [injV v] [] := hm
        rw [run_add, this]; rfl
      have := halted_unique h1 hn
      subst this
      simp [readOutcome, readValue_injV] at hr
      cases hr
      exact hd

end Reflect
