import Reflect.Space
import Reflect.RunUntilProof
import Reflect.MachineSafe
import Reflect.MachineExact

/-!
What a space-limited run is proved to do (`add-space-budget`).

It takes `run`'s steps (`runSpace_run`), so it never faults and halts only
with what the program evaluates to. Not stopped for space, it is the priced
run (`runSpace_priced`). It is stopped for space only when the cells made
would pass the credit it began with (`runSpace_full`), so a run whose steps
stay inside its credit is the priced run whatever the count
(`runSpace_within`). Every state it is in was reached from the start by steps
that made no more than its credit, or from a state it counted at no more than
three quarters of the limit by steps that made no more than the rest
(`trail_held`).

These bound the cells a run makes. They say nothing of what a state holds:
the state has no such notion.
-/

namespace Reflect
variable [Ops]

theorem madeIn_succ (n : Nat) (s : State) :
    madeIn (n + 1) s = charge s (step s) + madeIn n (step s) := rfl

/-- More steps make no fewer cells. -/
theorem madeIn_mono : ∀ {n m : Nat} (s : State), n ≤ m → madeIn n s ≤ madeIn m s := by
  intro n
  induction n with
  | zero => intro m s _; exact Nat.zero_le _
  | succ n ih =>
    intro m s h
    cases m with
    | zero => omega
    | succ m =>
      have := ih (step s) (Nat.le_of_succ_le_succ h)
      rw [madeIn_succ, madeIn_succ]
      omega

/-- One step of a priced run from a running state, written as `runSpace`
    writes it. -/
theorem runPriced_running (fuel : Nat) (c : Code) (e : MEnv) (stk : List MValue)
    (frs : List Frame) :
    runPriced (fuel + 1) (.running c e stk frs) =
      if stepCost (.running c e stk frs) - 1 ≤ fuel then
        runPriced (fuel - (stepCost (.running c e stk frs) - 1)) (step (.running c e stk frs))
      else .running c e stk frs := by
  rw [runPriced]
  case x_2 => intro o h'; cases h'
  case x_3 => intro h'; cases h'
  split
  · next h => rw [h]; simp
  · next k h =>
    rw [h]
    by_cases hk : k ≤ fuel
    · simp [hk]
    · have : ¬ (k + 1 ≤ fuel + 1) := by omega
      simp [hk, this]

/-- A space-limited run is a prefix of `run`: it stops at the state `run`
    reaches after some number of steps, no more than the fuel. -/
theorem runSpace_run (sp : Space) :
    ∀ fuel credit s, ∃ n, n ≤ fuel ∧ (runSpace sp fuel credit s).state = run n s := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro credit s
    cases fuel with
    | zero => exact ⟨0, Nat.le_refl _, by rw [runSpace]; rfl⟩
    | succ fuel =>
      cases s with
      | halted o => exact ⟨0, Nat.zero_le _, by rw [runSpace]; rfl⟩
      | fault => exact ⟨0, Nat.zero_le _, by rw [runSpace]; rfl⟩
      | running c e stk frs =>
        rw [runSpace_running]
        split
        · split
          · obtain ⟨m, hm, h⟩ := ih (fuel - (stepCost (.running c e stk frs) - 1)) (by omega)
              (credit - charge (.running c e stk frs) (step (.running c e stk frs)))
              (step (.running c e stk frs))
            exact ⟨m + 1, by omega, h⟩
          · split
            · obtain ⟨m, hm, h⟩ := ih (fuel - (stepCost (.running c e stk frs) - 1)) (by omega)
                (sp.cells - sp.count (.running c e stk frs) -
                  charge (.running c e stk frs) (step (.running c e stk frs)))
                (step (.running c e stk frs))
              exact ⟨m + 1, by omega, h⟩
            · exact ⟨0, Nat.zero_le _, rfl⟩
        · exact ⟨0, Nat.zero_le _, rfl⟩

/-- Where a space-limited run stops, `run` gets to. -/
theorem runSpace_reach {sp : Space} {fuel credit : Nat} {s t : State}
    (h : (runSpace sp fuel credit s).state = t) : ∃ n, run n s = t := by
  obtain ⟨n, _, hn⟩ := runSpace_run sp fuel credit s
  exact ⟨n, hn ▸ h⟩

/-- A run that is not stopped for space is the priced run: the ledger decides
    only whether a run goes on, never which step it takes. -/
theorem runSpace_priced (sp : Space) :
    ∀ fuel credit s t, runSpace sp fuel credit s = .reached t → t = runPriced fuel s := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro credit s t h
    cases fuel with
    | zero =>
      rw [runSpace] at h
      rw [runPriced]
      cases h; rfl
    | succ fuel =>
      cases s with
      | halted o =>
        rw [runSpace] at h
        rw [runPriced]
        cases h; rfl
      | fault =>
        rw [runSpace] at h
        rw [runPriced]
        cases h; rfl
      | running c e stk frs =>
        rw [runSpace_running] at h
        rw [runPriced_running]
        split at h
        · next hc =>
          simp only [hc, ↓reduceIte]
          split at h
          · exact ih _ (by omega) _ _ _ h
          · split at h
            · exact ih _ (by omega) _ _ _ h
            · cases h
        · next hc =>
          simp only [hc, ↓reduceIte]
          cases h; rfl

/-- A run is stopped for space only when the cells made, with the step it
    stopped before, pass the credit it began with. No count can stop it
    sooner. -/
theorem runSpace_full (sp : Space) :
    ∀ fuel credit s t, runSpace sp fuel credit s = .full t →
      ∃ k, k < fuel ∧ run k s = t ∧ credit < madeIn (k + 1) s := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro credit s t h
    cases fuel with
    | zero => rw [runSpace] at h; cases h
    | succ fuel =>
      cases s with
      | halted o => rw [runSpace] at h; cases h
      | fault => rw [runSpace] at h; cases h
      | running c e stk frs =>
        rw [runSpace_running] at h
        split at h
        · split at h
          · next ha =>
            obtain ⟨k, hk, hr, hm⟩ := ih _ (by omega) _ _ _ h
            refine ⟨k + 1, by omega, hr, ?_⟩
            rw [madeIn_succ]
            omega
          · next ha =>
            split at h
            · obtain ⟨k, hk, hr, _⟩ := ih _ (by omega) _ _ _ h
              refine ⟨k + 1, by omega, hr, ?_⟩
              rw [madeIn_succ]
              omega
            · cases h
              refine ⟨0, Nat.succ_pos _, rfl, ?_⟩
              rw [madeIn_succ]
              simp only [madeIn]
              omega
        · cases h

/-- A run whose first `fuel` steps make no more than its credit is the priced
    run, whatever the count: inside its ledger a run's outcome depends on
    nothing a host supplies. -/
theorem runSpace_within (sp : Space) (fuel credit : Nat) (s : State)
    (h : madeIn fuel s ≤ credit) :
    runSpace sp fuel credit s = .reached (runPriced fuel s) := by
  cases hr : runSpace sp fuel credit s with
  | reached t => rw [runSpace_priced sp fuel credit s t hr]
  | full t =>
    obtain ⟨k, hk, _, hm⟩ := runSpace_full sp fuel credit s t hr
    have := madeIn_mono s (show k + 1 ≤ fuel by omega)
    omega

/-- What the ledger says of a state `u` of a run begun at `s` with `credit`:
    `u` was reached from `s` by steps that made no more than `credit`, or
    from a state the run passed through, counted at no more than `sp.bar`, by
    steps that made no more than the rest of the limit. -/
def Held (sp : Space) (credit : Nat) (s u : State) : Prop :=
  (∃ k, run k s = u ∧ madeIn k s ≤ credit) ∨
  (∃ j k, run k (run j s) = u ∧ sp.count (run j s) ≤ sp.bar ∧
    sp.count (run j s) + madeIn k (run j s) ≤ sp.cells)

theorem held_start (sp : Space) (credit : Nat) (s : State) : Held sp credit s s :=
  .inl ⟨0, rfl, Nat.zero_le _⟩

/-- A step the credit covers. -/
theorem held_step {sp : Space} {credit : Nat} {s u : State}
    (ha : charge s (step s) ≤ credit)
    (h : Held sp (credit - charge s (step s)) (step s) u) : Held sp credit s u := by
  rcases h with ⟨k, hr, hm⟩ | ⟨j, k, hr, hc, hm⟩
  · exact .inl ⟨k + 1, hr, by rw [madeIn_succ]; omega⟩
  · exact .inr ⟨j + 1, k, hr, hc, hm⟩

/-- A step taken after a count. -/
theorem held_count {sp : Space} {credit : Nat} {s u : State}
    (hc : sp.count s ≤ sp.bar) (ha : charge s (step s) ≤ sp.cells - sp.count s)
    (h : Held sp (sp.cells - sp.count s - charge s (step s)) (step s) u) :
    Held sp credit s u := by
  rcases h with ⟨k, hr, hm⟩ | ⟨j, k, hr, hc', hm⟩
  · refine .inr ⟨0, k + 1, hr, hc, ?_⟩
    show sp.count s + madeIn (k + 1) s ≤ sp.cells
    have : sp.bar ≤ sp.cells := Nat.sub_le _ _
    rw [madeIn_succ]
    omega
  · exact .inr ⟨j + 1, k, hr, hc', hm⟩

/-- The space bound: every state a run is in is `Held`. -/
theorem trail_held (sp : Space) :
    ∀ fuel credit s u, u ∈ trail sp fuel credit s → Held sp credit s u := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro credit s u hu
    cases fuel with
    | zero =>
      rw [trail] at hu
      cases List.mem_singleton.mp hu
      exact held_start sp credit _
    | succ fuel =>
      cases s with
      | halted o =>
        rw [trail] at hu
        cases List.mem_singleton.mp hu
        exact held_start sp credit _
      | fault =>
        rw [trail] at hu
        cases List.mem_singleton.mp hu
        exact held_start sp credit _
      | running c e stk frs =>
        rw [trail] at hu
        split at hu
        · split at hu
          · next ha =>
            rcases List.mem_cons.mp hu with rfl | hu
            · exact held_start sp credit _
            · exact held_step ha (ih _ (by omega) _ _ _ hu)
          · split at hu
            · next hc =>
              rcases List.mem_cons.mp hu with rfl | hu
              · exact held_start sp credit _
              · exact held_count hc.1 hc.2 (ih _ (by omega) _ _ _ hu)
            · cases List.mem_singleton.mp hu
              exact held_start sp credit _
        · cases List.mem_singleton.mp hu
          exact held_start sp credit _

omit [Ops] in
theorem getLast?_cons_of_some {α : Type} {a x : α} {l : List α}
    (h : l.getLast? = some x) : (a :: l).getLast? = some x := by
  cases l with
  | nil => cases h
  | cons b l => rw [List.getLast?_cons_cons]; exact h

/-- The last state of the trail is where `runSpace` ends: `trail` and
    `runSpace` are one recursion. -/
theorem trail_last (sp : Space) :
    ∀ fuel credit s,
      (trail sp fuel credit s).getLast? = some (runSpace sp fuel credit s).state := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro credit s
    cases fuel with
    | zero => rw [trail, runSpace]; rfl
    | succ fuel =>
      cases s with
      | halted o => rw [trail, runSpace]; rfl
      | fault => rw [trail, runSpace]; rfl
      | running c e stk frs =>
        rw [trail, runSpace_running]
        split
        · split
          · exact getLast?_cons_of_some (ih _ (by omega) _ _)
          · split
            · exact getLast?_cons_of_some (ih _ (by omega) _ _)
            · rfl
        · rfl

/-- The state a run ends at is `Held`. -/
theorem runSpace_ledger (sp : Space) (fuel credit : Nat) (s : State) :
    Held sp credit s (runSpace sp fuel credit s).state :=
  trail_held sp fuel credit s _ (List.mem_of_getLast? (trail_last sp fuel credit s))

/-- With no count the ledger is the whole bound: the run stops at a state its
    steps reached having made no more than the limit. -/
theorem runIn_ledger (cells fuel : Nat) (s : State) :
    ∃ k, run k s = (runIn (.ledger cells) fuel s).state ∧ madeIn k s ≤ cells := by
  rcases runSpace_ledger (.ledger cells) fuel cells s with ⟨k, hr, hm⟩ | ⟨j, k, _, hc, _⟩
  · exact ⟨k, hr, hm⟩
  · have : cells + 1 ≤ cells - cells / 4 := hc
    omega

/-- A space-limited run of a compiled program is never at the fault state. -/
theorem machine_never_faults_space (sp : Space) (t : Term) (fuel credit : Nat) :
    (runSpace sp fuel credit (load (compile t))).state ≠ .fault := by
  obtain ⟨n, _, hn⟩ := runSpace_run sp fuel credit (load (compile t))
  rw [hn]
  exact machine_never_faults t n

/-- What a space-limited run of a compiled program halts with is what the
    program evaluates to. -/
theorem machine_exact_space (sp : Space) (t : Term) (fuel credit : Nat) (w : MOutcome)
    (h : (runSpace sp fuel credit (load (compile t))).state = .halted w) :
    ∃ o, Direct [] t o ∧ w = MP.injO o := by
  obtain ⟨n, hn⟩ := runSpace_reach h
  exact machine_exact t n w hn

/-- Where a turn is left, `run` gets to, for every turn space. -/
theorem runTurnIn_reach {cells budget : Nat} {s t : State} (h : runTurnIn cells budget s = t) :
    ∃ n, run n s = t := by
  unfold runTurnIn at h
  split at h
  · next u hu => exact runSpace_reach (by rw [runIn] at hu; rw [hu]; exact h)
  · next d hu =>
    split at h
    · exact runSpace_reach (by rw [runIn] at hu; rw [hu]; exact h)
    · exact ⟨0, h⟩
  · next u _ hu => exact runSpace_reach (by rw [runIn] at hu; rw [hu]; exact h)

/-- Where a turn is left, `run` gets to. This stands where `runPriced_reach`
    stood in the driver proofs. -/
theorem runTurn_reach {budget : Nat} {s t : State} (h : runTurn budget s = t) :
    ∃ n, run n s = t := runTurnIn_reach h

end Reflect
