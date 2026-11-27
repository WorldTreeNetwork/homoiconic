import Surface.CrossActs

/-!
Two guests that follow the protocol: their logs combine, and the replay is
their state.

`Inv` is what holds of every state two honest guests can reach (`Reach.inv`).
Until guest `a` begins its program neither guest has done anything
(`Before`). After, `Core` holds: `Dir` of each guest beside the other, each
log a `Reflect.SideRun` from its guest's first state, the entries in the order
they were recorded a path on shapes (`Reflect.SPath`), and the two budgets as
far as they are agreed.

From these: where nothing is in flight the path ends settled, so by
`Reflect.spath_combine` (the greedy walk is complete) the logs combine, and by
`Reflect.replay_agrees` the check accepts them and replays to what the guests
hold (`honest_combine`, `honest_accept`). A guest that has run anything runs
with the other's budgets (`honest_budget`), and each guest's acknowledgements
are in the order the other took its crossings (`honest_acks`).
-/
namespace Surface.Cross
open Reflect

/-! What the proofs read of a guest after `take`, `batch` and `give`. -/

/-- One packet of a batch: queued when it is the next and there is room. -/
def takeOne (g : Guest) (p : Data) : Guest :=
  match p with
  | .arr [.nat seq, pkt] =>
    if seq == g.got && g.inbox.length + g.pending.length < queueLimit then
      { g with inbox := g.inbox ++ [pkt], got := g.got + 1, resting := false }
    else g
  | _ => g

/-- A guest after the head of a batch is taken, before its packets. -/
def Guest.counted (g : Guest) (flag got steps cells : Nat) (pkts : List Data) : Guest :=
  { g with sent := g.sent.drop (min got (g.sentBase + g.sent.length) - g.sentBase),
           sentBase := max g.sentBase (min got (g.sentBase + g.sent.length)),
           peerQuiet := flag ≥ 1 && pkts.isEmpty,
           heard := true,
           budget := if g.fixed then g.budget else min g.budget steps,
           cells := if g.fixed then g.cells else min g.cells cells }

theorem takeData_arr (g : Guest) (flag got steps cells : Nat) (pkts : List Data) :
    g.takeData (.arr [.nat flag, .nat got, .nat steps, .nat cells, .arr pkts]) =
      (fun (g₂ : Guest) => if flag == 2 then { g₂ with closed := true } else g₂)
        (pkts.foldl takeOne (g.counted flag got steps cells pkts)) := rfl

theorem takeOne_spec (g : Guest) (p : Data) :
    takeOne g p = g ∨ ∃ pkt, p = Data.arr [.nat g.got, pkt] ∧
      takeOne g p = { g with inbox := g.inbox ++ [pkt], got := g.got + 1, resting := false } := by
  unfold takeOne
  split
  · next seq pkt =>
    split
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, _⟩ := hc
      exact .inr ⟨pkt, rfl, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

theorem drop_of_getElem? {α : Type} {l : List α} {n : Nat} {x : α} (h : l[n]? = some x) :
    l.drop n = x :: l.drop (n + 1) := by
  induction l generalizing n with
  | nil => simp at h
  | cons y l ih =>
    cases n with
    | zero => simp at h; simp [h]
    | succ n => simp at h; simpa using ih h

/-- The packets of a batch that are queued are the next ones the peer made. -/
theorem fold_take (posted : List Data) : ∀ (pkts : List Data) (g : Guest),
    (∀ (seq : Nat) (pkt : Data), Data.arr [.nat seq, pkt] ∈ pkts → posted[seq]? = some pkt) →
    ∃ new t, posted.drop g.got = new ++ t ∧ (pkts = [] → new = []) ∧
      (pkts.foldl takeOne g).view = { g.view with inbox := g.inbox ++ new, got := g.got + new.length } := by
  intro pkts
  induction pkts with
  | nil => intro g _; exact ⟨[], posted.drop g.got, rfl, fun _ => rfl, by simp [Guest.view]⟩
  | cons p ps ih =>
    intro g hp
    have hps : ∀ (seq : Nat) (pkt : Data), Data.arr [.nat seq, pkt] ∈ ps → posted[seq]? = some pkt :=
      fun seq pkt h => hp seq pkt (List.mem_cons_of_mem _ h)
    rw [List.foldl_cons]
    rcases takeOne_spec g p with he | ⟨pkt, rfl, he⟩
    · rw [he]
      obtain ⟨new, t, hd, _, hv⟩ := ih g hps
      exact ⟨new, t, hd, by simp, hv⟩
    · rw [he]
      obtain ⟨new, t, hd, _, hv⟩ :=
        ih { g with inbox := g.inbox ++ [pkt], got := g.got + 1, resting := false } hps
      have hpk := hp g.got pkt (by simp)
      refine ⟨pkt :: new, t, ?_, by simp, ?_⟩
      · rw [drop_of_getElem? hpk]
        have hd' : posted.drop (g.got + 1) = new ++ t := hd
        rw [hd']
        rfl
      · rw [hv]
        simp [Guest.view, Nat.add_assoc, Nat.add_comm 1]

/-- What a guest is after it takes a batch whose packets are ones the peer
    made, each under its number. -/
theorem takeData_view (g : Guest) (flag got steps cells : Nat) {pkts posted : List Data}
    (hp : ∀ (seq : Nat) (pkt : Data), Data.arr [.nat seq, pkt] ∈ pkts → posted[seq]? = some pkt) :
    ∃ new t, posted.drop g.got = new ++ t ∧ (pkts = [] → new = []) ∧
      (g.takeData (.arr [.nat flag, .nat got, .nat steps, .nat cells, .arr pkts])).view =
        { g.view with
          sent := g.view.sent.drop (min got (g.view.sentBase + g.view.sent.length) - g.view.sentBase)
          sentBase := max g.view.sentBase (min got (g.view.sentBase + g.view.sent.length))
          heard := true
          budget := if g.view.fixed then g.view.budget else min g.view.budget steps
          cells := if g.view.fixed then g.view.cells else min g.view.cells cells
          inbox := g.view.inbox ++ new
          got := g.view.got + new.length } := by
  rw [takeData_arr]
  obtain ⟨new, t, hd, hnil, hv⟩ := fold_take posted pkts (g.counted flag got steps cells pkts) hp
  refine ⟨new, t, hd, hnil, ?_⟩
  have hclose : ∀ g₂ : Guest, (if flag == 2 then { g₂ with closed := true } else g₂).view = g₂.view := by
    intro g₂
    split <;> rfl
  show (if flag == 2 then { (pkts.foldl takeOne (g.counted flag got steps cells pkts)) with closed := true }
    else pkts.foldl takeOne (g.counted flag got steps cells pkts)).view = _
  rw [hclose, hv]
  rfl

/-- One packet of a batch being made: added while there is room. -/
def batchStep (room : Nat) (acc : List Data × Nat × Bool × Nat) (pkt : Data) :
    List Data × Nat × Bool × Nat :=
  let size := (Wire.write pkt).size + 16
  if acc.2.2.1 || acc.2.1 + size > room then (acc.1, acc.2.1, true, acc.2.2.2 + 1)
  else (acc.1 ++ [.arr [.nat acc.2.2.2, pkt]], acc.2.1 + size, false, acc.2.2.2 + 1)

theorem batchData_fold (g : Guest) (room : Nat) : g.batchData room =
    .arr [.nat (if g.closing then 2 else if g.idle then 1 else 0), .nat g.got, .nat g.budget,
      .nat g.cells, .arr (g.sent.foldl (batchStep room) ([], 64, false, g.sentBase)).1] := rfl

theorem batchFold (room base : Nat) (sent : List Data) :
    ∀ (l : List Data) (acc : List Data × Nat × Bool × Nat) (n : Nat),
    acc.2.2.2 = base + n → (∀ (i : Nat) (x : Data), l[i]? = some x → sent[n + i]? = some x) →
    (∀ (seq : Nat) (pkt : Data), Data.arr [.nat seq, pkt] ∈ acc.1 →
      ∃ i, seq = base + i ∧ sent[i]? = some pkt) →
    ∀ (seq : Nat) (pkt : Data), Data.arr [.nat seq, pkt] ∈ (l.foldl (batchStep room) acc).1 →
      ∃ i, seq = base + i ∧ sent[i]? = some pkt := by
  intro l
  induction l with
  | nil => intro acc n _ _ h; exact h
  | cons x l ih =>
    intro acc n hn hl hacc
    rw [List.foldl_cons]
    refine ih (batchStep room acc x) (n + 1) ?_ ?_ ?_
    · unfold batchStep
      simp only
      split <;> simp [hn] <;> omega
    · intro i y hy
      have := hl (i + 1) y (by simpa using hy)
      rw [← this]
      congr 1
      omega
    · intro seq pkt hm
      unfold batchStep at hm
      simp only at hm
      split at hm
      · exact hacc seq pkt hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact hacc seq pkt hm
        · simp only [List.mem_singleton, Data.arr.injEq, List.cons.injEq, Data.nat.injEq, and_true] at hm
          obtain ⟨rfl, rfl⟩ := hm
          exact ⟨n, hn, by simpa using hl 0 pkt (by simp)⟩

/-- A batch says what its guest had accepted and runs with, and carries
    packets the guest keeps to send, each under its number. -/
theorem batchData_shape (g : Guest) (room : Nat) : ∃ flag pkts,
    g.batchData room = .arr [.nat flag, .nat g.got, .nat g.budget, .nat g.cells, .arr pkts] ∧
    (g.sent = [] → pkts = []) ∧
    ∀ (seq : Nat) (pkt : Data), Data.arr [.nat seq, pkt] ∈ pkts →
      ∃ i, seq = g.sentBase + i ∧ g.sent[i]? = some pkt := by
  refine ⟨_, _, batchData_fold g room, ?_, ?_⟩
  · intro hs
    rw [hs]
    rfl
  · exact batchFold room g.sentBase g.sent g.sent _ 0 rfl (fun i x h => by simpa using h)
      (by intro seq pkt h; simp at h)

theorem give_awake {g : Guest} (h : g.waiting = false) (bytes : ByteArray) (budget : Nat)
    (old : Option Term) : g.give bytes budget = g ∧ handed g bytes old = old := by
  simp [Guest.give, handed, h]

/-- Giving a guest a program changes nothing the proofs read, or gives the
    waiting guest the program read and lowers its step budget. -/
theorem give_view (g : Guest) (bytes : ByteArray) (budget : Nat) (old : Option Term) :
    ((g.give bytes budget).view = g.view ∧ handed g bytes old = old) ∨
    ∃ t, handed g bytes old = some t ∧
      (g.give bytes budget).view =
        { g.view with program := some t,
                      budget := if g.view.fixed then g.view.budget else min g.view.budget budget } := by
  by_cases hc : (!g.waiting || g.program.isSome) = true
  · exact .inl (by simp [Guest.give, handed, hc])
  · cases hr : Wire.readProgram bytes with
    | error e => exact .inl (by simp [Guest.give, handed, hc, hr, Guest.view])
    | ok t => exact .inr ⟨t, by simp [handed, hc, hr], by simp [Guest.give, hc, hr, Guest.view]; rfl⟩

/-! What a step leaves alone. -/

structure Keeps (v v' : View) : Prop where
  side : v'.side = v.side
  budget : v'.budget = v.budget
  cells : v'.cells = v.cells
  got : v'.got = v.got
  waiting : v'.waiting = v.waiting
  /-- A guest that has run something stays so, and comes to it only by
      working a packet. -/
  fixed : v.fixed = true → v'.fixed = true
  fixes : v'.fixed = true → v.fixed = true ∨ v.inbox ≠ []

theorem Acts.keeps {v v' : View} (act : Acts v v') : Keeps v v' := by
  cases act with
  | same hv => subst hv; exact ⟨rfl, rfl, rfl, rfl, rfl, id, .inl⟩
  | drop hin hno hfix hv =>
    subst hv
    exact ⟨rfl, rfl, rfl, rfl, rfl, hfix, fun _ => .inr (by rw [hin]; simp)⟩
  | lost hin ha hk hq hv =>
    subst hv
    exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => .inr (by rw [hin]; simp)⟩
  | queue hin hv =>
    subst hv
    exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => .inr (by rw [hin]; simp)⟩
  | unqueue hv => subst hv; exact ⟨rfl, rfl, rfl, rfl, rfl, id, .inl⟩
  | did h free inside par hx hv => subst hv; exact ⟨rfl, rfl, rfl, rfl, rfl, id, .inl⟩
  | out hi free hw hp ht hx hv => subst hv; exact ⟨rfl, rfl, rfl, rfl, rfl, id, .inl⟩
  | spawnIn hin hu hn hr hc hx hv =>
    subst hv
    exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => .inr (by rw [hin]; simp)⟩
  | sendIn hp hj free hrecv ht hx hv => subst hv; exact ⟨rfl, rfl, rfl, rfl, rfl, id, .inl⟩
  | ack hin ha hk hq hx hv =>
    subst hv
    exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => .inr (by rw [hin]; simp)⟩

/-- A guest with no process, no packet and no pending send can do nothing. -/
theorem Acts.idle {v v' : View} (act : Acts v v') (hc : v.cfg.procs = []) (hp : v.pending = [])
    (hi : v.inbox = []) : v' = v := by
  cases act with
  | same hv => exact hv
  | drop hin hno hfix hv => rw [hi] at hin; cases hin
  | lost hin ha hk hq hv => rw [hi] at hin; cases hin
  | queue hin hv => rw [hi] at hin; cases hin
  | unqueue hv =>
    subst hv
    cases v
    simp_all
  | did h free inside par hx hv => exact absurd h (stepIn_nil hc inside)
  | out hi' free hw hp' ht hx hv => rw [hc] at hi'; simp at hi'
  | spawnIn hin hu hn hr hc' hx hv => rw [hi] at hin; cases hin
  | sendIn hp' hj free hrecv ht hx hv => rw [hp] at hp'; cases hp'
  | ack hin ha hk hq hx hv => rw [hi] at hin; cases hin

/-- A guest with no process and no pending send that has still run nothing
    after a step has recorded nothing. -/
theorem Acts.fresh {v v' : View} (act : Acts v v') (hc : v.cfg.procs = []) (hp : v.pending = [])
    (hf : v'.fixed = false) : v'.log = v.log ∧ v'.cfg.procs = [] ∧ v'.pending = [] := by
  cases act with
  | same hv => subst hv; exact ⟨rfl, hc, hp⟩
  | drop hin hno hfix hv => subst hv; exact ⟨rfl, hc, hp⟩
  | lost hin ha hk hq hv => subst hv; cases hf
  | queue hin hv => subst hv; cases hf
  | unqueue hv => subst hv; exact ⟨rfl, hc, by simp [hp]⟩
  | did h free inside par hx hv => exact absurd h (stepIn_nil hc inside)
  | out hi' free hw hp' ht hx hv => rw [hc] at hi'; simp at hi'
  | spawnIn hin hu hn hr hc' hx hv => subst hv; cases hf
  | sendIn hp' hj free hrecv ht hx hv => rw [hp] at hp'; cases hp'
  | ack hin ha hk hq hx hv => subst hv; cases hf

/-! Batches. -/

section
variable {v v' w : View} {L M : Local} {rs rw : List (Note × Data)} {W Ww to tw : List Data}
  {h hw : Half}

/-- A guest takes a batch its peer made. -/
theorem Dir.takes {got budget cells : Nat} {new : List Data} {heard : Bool}
    (me : Dir v w L M rs W to h) (peer : Dir w v M L rw Ww tw hw) (hgot : got ≤ w.got)
    (hnew : ∃ t, M.posted.drop v.got = new ++ t)
    (hv : v' = { v with
      sent := v.sent.drop (min got (v.sentBase + v.sent.length) - v.sentBase)
      sentBase := max v.sentBase (min got (v.sentBase + v.sent.length))
      heard := heard
      budget := budget
      cells := cells
      inbox := v.inbox ++ new
      got := v.got + new.length }) :
    Dir v' w L M rs W to h ∧ Dir w v' M L rw Ww tw hw := by
  subst hv
  refine ⟨{ me with
      sent := by
        show v.sent.drop (min got (v.sentBase + v.sent.length) - v.sentBase) =
          L.posted.drop (max v.sentBase (min got (v.sentBase + v.sent.length)))
        rw [me.sent, List.drop_drop]
        congr 1
        omega
      base := by
        show max v.sentBase (min got (v.sentBase + v.sent.length)) ≤ w.got
        have := me.base
        omega
      split := by
        obtain ⟨rest, hr, hg⟩ := me.split
        obtain ⟨t, ht⟩ := hnew
        have hrest : M.posted.drop v.got = rest := by
          rw [hr, hg, ← List.length_append, List.drop_left]
        rw [hrest] at ht
        refine ⟨t, ?_, ?_⟩
        · show M.posted = W ++ (v.inbox ++ new) ++ t
          rw [hr, ht]
          simp
        · show v.got + new.length = W.length + (v.inbox ++ new).length
          rw [hg]
          simp
          omega
      batches := by
        intro d hd
        obtain ⟨flag, got', steps, cells', pkts, rfl, hg, hpk⟩ := me.batches d hd
        exact ⟨flag, got', steps, cells', pkts, rfl, Nat.le_trans hg (Nat.le_add_right _ _), hpk⟩ },
    peer.frame (Nat.le_add_right _ _) ⟨[], by simp⟩ (fun _ _ h => h) rfl⟩

/-- A guest makes a batch. -/
theorem Dir.sends (me : Dir v w L M rs W to h) {d : Data} {flag steps cells : Nat} {pkts : List Data}
    (hd : d = .arr [.nat flag, .nat v.got, .nat steps, .nat cells, .arr pkts])
    (hp : ∀ (seq : Nat) (pkt : Data), Data.arr [.nat seq, pkt] ∈ pkts →
      ∃ i, seq = v.sentBase + i ∧ v.sent[i]? = some pkt) :
    Dir v w L M rs W (d :: to) h :=
  { me with
    batches := by
      intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · refine ⟨flag, v.got, steps, cells, pkts, hd, Nat.le_refl _, ?_⟩
        intro seq pkt hm
        obtain ⟨i, rfl, hi⟩ := hp seq pkt hm
        rw [me.sent, List.getElem?_drop] at hi
        exact hi
      · exact me.batches d' hd' }

/-- A guest that has done nothing, with the processes it starts with. -/
theorem Dir.init {procs procsw : List (Proc MValue MOutcome)} (hc : v.cfg = ⟨procs, []⟩)
    (ha : v.asked = []) (ho : v.outs = 0) (hs : v.sent = []) (hi : v.inbox = [])
    (hp : v.pending = []) (hl : v.log = []) (hb : v.sentBase = 0) (hg : v.got = 0)
    (hto : ∀ d ∈ to, ∃ flag steps cells,
      d = Data.arr [.nat flag, .nat 0, .nat steps, .nat cells, .arr []]) :
    Dir v w (Local.init procs) (Local.init procsw) [] [] to ⟨procs.length, []⟩ where
  log := by simp [hl]
  procs := by simp [Local.init, hc]
  names := by simp [Local.init, hc]
  asked := by simp [Local.init, ha]
  outs := by simp [Local.init, ho]
  took := rfl
  posted := Local.Posted.init procs
  sent := by simp [Local.init, hs]
  base := by rw [hb]; exact Nat.zero_le _
  split := ⟨[], by simp [Local.init, hi], by simp [hg, hi]⟩
  link := by intro r hr; cases hr
  pend := by intro p hp'; rw [hp] at hp'; cases hp'
  acked := by intro k hk; rw [ho] at hk; omega
  unacked := by intro a ha'; rw [ha] at ha'; cases ha'
  acks := by simp [hl, acksOf]
  batches := by
    intro d hd
    obtain ⟨flag, steps, cells, rfl⟩ := hto d hd
    exact ⟨flag, 0, steps, cells, [], rfl, Nat.zero_le _, by intro seq pkt hm; cases hm⟩
  hn := rfl
  hlen := by simp [ho]
  live := by intro a ha'; rw [ha] at ha'; cases ha'
  dead := by intro k c hc'; simp at hc'

/-- Where the peer keeps nothing to send and the guest has nothing accepted
    and not worked, the guest has worked every packet the peer made. -/
theorem Dir.all (me : Dir v w L M rs W to h) (peer : Dir w v M L rw Ww tw hw) (hs : w.sent = [])
    (hi : v.inbox = []) : M.posted = W := by
  obtain ⟨rest, hr, hg⟩ := me.split
  rw [hi] at hr hg
  have hlen : M.posted.length ≤ w.sentBase := by
    have := peer.sent
    rw [hs] at this
    exact List.drop_eq_nil_iff.mp this.symm
  have hb := peer.base
  have hl : M.posted.length = W.length + rest.length := by rw [hr]; simp
  have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by simp at hg; omega)
  rw [hr, hrest]
  simp

/-- And then none of its crossings is taken and not acknowledged. -/
theorem Dir.calm (me : Dir v w L M rs W to h) (peer : Dir w v M L rw Ww tw hw) (hs : w.sent = [])
    (hi : v.inbox = []) : ∀ c ∈ h.outs, c.state ≠ .taken := by
  intro c hc
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hc
  by_cases hex : ∃ a ∈ v.asked, a.k = k
  · obtain ⟨a, ha, rfl⟩ := hex
    obtain ⟨st, hst, _, hoff⟩ := me.live a ha
    rw [hst] at hk
    cases hk
    have hnt : a.k ∉ M.took := by
      intro htk
      have := peer.posted.ack_of htk
      rw [me.all peer hs hi] at this
      exact me.unacked a ha this
    simp [hoff hnt]
  · simp [me.dead k c hk (fun a ha he => hex ⟨a, ha, he⟩)]

end

/-! After guest `a` has begun. -/

/-- What holds of two guests once `a` has begun the program `t`, as `c₀`. -/
structure Core (va vb : View) (toA toB : List Data) (t : Term) (c₀ : MConfig)
    (ra rb : List (Note × Data)) (La Lb : Local) (Wa Wb : List Data) (ha hb : Half) : Prop where
  awake : va.waiting = false
  bwake : vb.waiting = false
  sideA : va.side = .a
  sideB : vb.side = .b
  begun : beginIn va.cells va.budget t = some c₀
  /-- Each log, read alone with its guest's budgets, from its guest's first
      state. -/
  runA : SideRun va.cells va.budget .a (Local.init c₀.procs) ra La
  runB : SideRun vb.cells vb.budget .b (Local.init []) rb Lb
  dirA : Dir va vb La Lb ra Wa toB ha
  dirB : Dir vb va Lb La rb Wb toA hb
  /-- The entries, in the order they were recorded, are a path on shapes. -/
  path : SPath Shape.first va.log.reverse vb.log.reverse ⟨ha, hb⟩
  /-- `a`'s budgets no longer change; `b`'s are at least `a`'s until it runs
      something, at most `a`'s once it has a packet, and `a`'s from then. -/
  afixed : va.fixed = true
  low : vb.fixed = false → va.budget ≤ vb.budget ∧ va.cells ≤ vb.cells
  got : 0 < vb.got → vb.budget ≤ va.budget ∧ vb.cells ≤ va.cells
  fixed : vb.fixed = true → vb.budget = va.budget ∧ vb.cells = va.cells
  fresh : vb.fixed = false → vb.log = [] ∧ vb.cfg.procs = [] ∧ vb.pending = []
  /-- A batch of `a`'s announces at least `a`'s budgets, and exactly them when
      it carries a packet. -/
  ann : ∀ d ∈ toB, ∀ (flag got steps cells : Nat) (pkts : List Data),
    d = Data.arr [.nat flag, .nat got, .nat steps, .nat cells, .arr pkts] →
    va.budget ≤ steps ∧ va.cells ≤ cells ∧ (pkts ≠ [] → steps = va.budget ∧ cells = va.cells)

def Alive (va vb : View) (toA toB : List Data) (t : Term) : Prop :=
  ∃ c₀ ra rb La Lb Wa Wb ha hb, Core va vb toA toB t c₀ ra rb La Lb Wa Wb ha hb

section
variable {va vb va' vb' : View} {toA toB : List Data} {t : Term} {c₀ : MConfig}
  {ra rb : List (Note × Data)} {La Lb : Local} {Wa Wb : List Data} {ha hb : Half}

/-- Guest `a` changed in what it sends and accepts only. -/
theorem Core.setA (c : Core va vb toA toB t c₀ ra rb La Lb Wa Wb ha hb)
    (dA : Dir va' vb La Lb ra Wa toB ha) (dB : Dir vb va' Lb La rb Wb toA hb)
    (hw : va'.waiting = va.waiting) (hs : va'.side = va.side) (hbu : va'.budget = va.budget)
    (hc : va'.cells = va.cells) (hf : va'.fixed = va.fixed) (hl : va'.log = va.log) :
    Core va' vb toA toB t c₀ ra rb La Lb Wa Wb ha hb where
  awake := by rw [hw]; exact c.awake
  bwake := c.bwake
  sideA := by rw [hs]; exact c.sideA
  sideB := c.sideB
  begun := by rw [hc, hbu]; exact c.begun
  runA := by rw [hc, hbu]; exact c.runA
  runB := c.runB
  dirA := dA
  dirB := dB
  path := by rw [hl]; exact c.path
  afixed := by rw [hf]; exact c.afixed
  low := by rw [hc, hbu]; exact c.low
  got := by rw [hc, hbu]; exact c.got
  fixed := by rw [hc, hbu]; exact c.fixed
  fresh := c.fresh
  ann := by rw [hc, hbu]; exact c.ann

/-- Guest `a` recorded entries. -/
theorem Core.outA (c : Core va vb toA toB t c₀ ra rb La Lb Wa Wb ha hb) (k : Keeps va va')
    (o : Out .a va va' vb La Lb ra rb Wb toB toA ha hb) : Alive va' vb toA toB t := by
  obtain ⟨new, La', Wa', ha', hb', run, hpath, me, peer⟩ := o
  have hlog : va'.log.reverse = va.log.reverse ++ new.map (·.1) := by
    rw [← me.log, ← c.dirA.log, List.map_append]
  refine ⟨c₀, ra ++ new, rb, La', Lb, Wa', Wb, ha', hb', ?_⟩
  exact
    { awake := by rw [k.waiting]; exact c.awake
      bwake := c.bwake
      sideA := by rw [k.side]; exact c.sideA
      sideB := c.sideB
      begun := by rw [k.cells, k.budget]; exact c.begun
      runA := by rw [k.cells, k.budget]; exact c.runA.append run
      runB := c.runB
      dirA := me
      dirB := peer
      path := by rw [hlog]; exact SPath.addA hpath c.path
      afixed := k.fixed c.afixed
      low := by rw [k.cells, k.budget]; exact c.low
      got := by rw [k.cells, k.budget]; exact c.got
      fixed := by rw [k.cells, k.budget]; exact c.fixed
      fresh := c.fresh
      ann := by rw [k.cells, k.budget]; exact c.ann }

theorem Core.actA (c : Core va vb toA toB t c₀ ra rb La Lb Wa Wb ha hb) (act : Acts va va') :
    Alive va' vb toA toB t :=
  c.outA act.keeps (act.dir c.sideA (c.runA.ok (Local.Ok.init _ _ _ _)) c.dirA c.dirB)

theorem Core.actB (c : Core va vb toA toB t c₀ ra rb La Lb Wa Wb ha hb) (act : Acts vb vb') :
    Alive va vb' toA toB t := by
  have k := act.keeps
  obtain ⟨new, Lb', Wb', hb', ha', run, hpath, me, peer⟩ :=
    act.dir c.sideB (c.runB.ok (Local.Ok.init _ _ _ _)) c.dirB c.dirA
  have hlog : vb'.log.reverse = vb.log.reverse ++ new.map (·.1) := by
    rw [← me.log, ← c.dirB.log, List.map_append]
  have hmono : vb'.fixed = false → vb.fixed = false := by
    intro h
    cases hf : vb.fixed with
    | false => rfl
    | true => rw [k.fixed hf] at h; cases h
  refine ⟨c₀, ra, rb ++ new, La, Lb', Wa, Wb', ha', hb', ?_⟩
  exact
    { awake := c.awake
      bwake := by rw [k.waiting]; exact c.bwake
      sideA := c.sideA
      sideB := by rw [k.side]; exact c.sideB
      begun := c.begun
      runA := c.runA
      runB := by rw [k.cells, k.budget]; exact c.runB.append run
      dirA := peer
      dirB := me
      path := by rw [hlog]; exact SPath.addB hpath c.path
      afixed := c.afixed
      low := by intro h; rw [k.budget, k.cells]; exact c.low (hmono h)
      got := by rw [k.got, k.budget, k.cells]; exact c.got
      fixed := by
        intro h
        rw [k.budget, k.cells]
        cases hf : vb.fixed with
        | true => exact c.fixed hf
        | false =>
          rcases k.fixes h with h' | h'
          · rw [hf] at h'; cases h'
          · have hpos : 0 < vb.got := by
              obtain ⟨rest, _, hg⟩ := c.dirB.split
              rw [hg]
              cases hi : vb.inbox with
              | nil => exact absurd hi h'
              | cons x xs => simp; omega
            obtain ⟨l1, l2⟩ := c.low hf
            obtain ⟨g1, g2⟩ := c.got hpos
            exact ⟨Nat.le_antisymm g1 l1, Nat.le_antisymm g2 l2⟩
      fresh := by
        intro h
        obtain ⟨hl, hp, hq⟩ := c.fresh (hmono h)
        obtain ⟨h1, h2, h3⟩ := act.fresh hp hq h
        exact ⟨by rw [h1]; exact hl, h2, h3⟩
      ann := c.ann }

/-- Guest `b` takes a batch `a` made. -/
theorem Core.takeB (c : Core va vb toA toB t c₀ ra rb La Lb Wa Wb ha hb) {flag got steps cells : Nat}
    {pkts new : List Data}
    (hd : Data.arr [.nat flag, .nat got, .nat steps, .nat cells, .arr pkts] ∈ toB) (hg : got ≤ va.got)
    (hnew : ∃ t, La.posted.drop vb.got = new ++ t) (hnil : pkts = [] → new = [])
    (hv : vb' = { vb with
      sent := vb.sent.drop (min got (vb.sentBase + vb.sent.length) - vb.sentBase)
      sentBase := max vb.sentBase (min got (vb.sentBase + vb.sent.length))
      heard := true
      budget := if vb.fixed then vb.budget else min vb.budget steps
      cells := if vb.fixed then vb.cells else min vb.cells cells
      inbox := vb.inbox ++ new
      got := vb.got + new.length }) :
    Core va vb' toA toB t c₀ ra rb La Lb Wa Wb ha hb := by
  obtain ⟨dB, dA⟩ := c.dirB.takes c.dirA hg hnew hv
  obtain ⟨a1, a2, a3⟩ := c.ann _ hd flag got steps cells pkts rfl
  subst hv
  exact
    { awake := c.awake
      bwake := c.bwake
      sideA := c.sideA
      sideB := c.sideB
      begun := c.begun
      runA := c.runA
      runB := by
        show SideRun (if vb.fixed then vb.cells else min vb.cells cells)
          (if vb.fixed then vb.budget else min vb.budget steps) .b (Local.init []) rb Lb
        cases hf : vb.fixed with
        | true => exact c.runB
        | false =>
          have hrb : rb = [] := by
            have := c.dirB.log
            rw [(c.fresh hf).1] at this
            simpa using this
          subst hrb
          have := c.runB.nil_inv
          subst this
          exact .nil
      dirA := dA
      dirB := dB
      path := c.path
      afixed := c.afixed
      low := by
        intro h
        have h' : vb.fixed = false := h
        obtain ⟨l1, l2⟩ := c.low h'
        show va.budget ≤ (if vb.fixed then vb.budget else min vb.budget steps) ∧
          va.cells ≤ (if vb.fixed then vb.cells else min vb.cells cells)
        rw [h']
        exact ⟨Nat.le_min.mpr ⟨l1, a1⟩, Nat.le_min.mpr ⟨l2, a2⟩⟩
      got := by
        intro h
        have h' : 0 < vb.got + new.length := h
        show (if vb.fixed then vb.budget else min vb.budget steps) ≤ va.budget ∧
          (if vb.fixed then vb.cells else min vb.cells cells) ≤ va.cells
        cases hf : vb.fixed with
        | true =>
          obtain ⟨e1, e2⟩ := c.fixed hf
          exact ⟨Nat.le_of_eq e1, Nat.le_of_eq e2⟩
        | false =>
          by_cases hn : new = []
          · rw [hn] at h'
            obtain ⟨g1, g2⟩ := c.got (by simpa using h')
            exact ⟨Nat.le_trans (Nat.min_le_left _ _) g1, Nat.le_trans (Nat.min_le_left _ _) g2⟩
          · obtain ⟨e1, e2⟩ := a3 (fun hp => hn (hnil hp))
            exact ⟨by rw [e1]; exact Nat.min_le_right _ _, by rw [e2]; exact Nat.min_le_right _ _⟩
      fixed := by
        intro h
        have h' : vb.fixed = true := h
        show (if vb.fixed then vb.budget else min vb.budget steps) = va.budget ∧
          (if vb.fixed then vb.cells else min vb.cells cells) = va.cells
        rw [h']
        exact c.fixed h'
      fresh := c.fresh
      ann := c.ann }

/-- Guest `a` makes a batch. -/
theorem Core.sendA (c : Core va vb toA toB t c₀ ra rb La Lb Wa Wb ha hb) {d : Data} {flag : Nat}
    {pkts : List Data}
    (hd : d = .arr [.nat flag, .nat va.got, .nat va.budget, .nat va.cells, .arr pkts])
    (hp : ∀ (seq : Nat) (pkt : Data), Data.arr [.nat seq, pkt] ∈ pkts →
      ∃ i, seq = va.sentBase + i ∧ va.sent[i]? = some pkt) :
    Core va vb toA (d :: toB) t c₀ ra rb La Lb Wa Wb ha hb :=
  { c with
    dirA := c.dirA.sends hd hp
    ann := by
      intro d' hd' flag' got' steps' cells' pkts' he
      rcases List.mem_cons.mp hd' with rfl | hd'
      · rw [hd] at he
        simp only [Data.arr.injEq, List.cons.injEq, Data.nat.injEq, and_true] at he
        obtain ⟨_, _, rfl, rfl, _⟩ := he
        exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ => ⟨rfl, rfl⟩⟩
      · exact c.ann d' hd' flag' got' steps' cells' pkts' he }

/-- Guest `b` makes a batch. -/
theorem Core.sendB (c : Core va vb toA toB t c₀ ra rb La Lb Wa Wb ha hb) {d : Data} {flag : Nat}
    {pkts : List Data}
    (hd : d = .arr [.nat flag, .nat vb.got, .nat vb.budget, .nat vb.cells, .arr pkts])
    (hp : ∀ (seq : Nat) (pkt : Data), Data.arr [.nat seq, pkt] ∈ pkts →
      ∃ i, seq = vb.sentBase + i ∧ vb.sent[i]? = some pkt) :
    Core va vb (d :: toA) toB t c₀ ra rb La Lb Wa Wb ha hb :=
  { c with dirB := c.dirB.sends hd hp }

end

/-! Before guest `a` begins. -/

/-- A guest that has done nothing. -/
structure Blank (v : View) : Prop where
  cfg : v.cfg = ⟨[], []⟩
  asked : v.asked = []
  outs : v.outs = 0
  sent : v.sent = []
  inbox : v.inbox = []
  pending : v.pending = []
  log : v.log = []
  sentBase : v.sentBase = 0
  got : v.got = 0
  fixed : v.fixed = false

/-- A blank guest that takes a batch with no packet is blank. -/
theorem Blank.take {v : View} (bl : Blank v) {got budget cells : Nat} {heard : Bool} :
    Blank { v with
      sent := v.sent.drop (min got (v.sentBase + v.sent.length) - v.sentBase)
      sentBase := max v.sentBase (min got (v.sentBase + v.sent.length))
      heard := heard
      budget := budget
      cells := cells
      inbox := v.inbox ++ []
      got := v.got + ([] : List Data).length } where
  cfg := bl.cfg
  asked := bl.asked
  outs := bl.outs
  sent := by simp [bl.sent]
  inbox := by simp [bl.inbox]
  pending := bl.pending
  log := bl.log
  sentBase := by simp [bl.sentBase, bl.sent]
  got := by simp [bl.got]
  fixed := bl.fixed

/-- Until `a` begins: neither guest has done anything, no batch carries a
    packet, and the budgets are as the announcements leave them. -/
structure Before (va vb : View) (toA toB : List Data) (prog : Option Term) : Prop where
  awaits : va.waiting = true
  bwake : vb.waiting = false
  sideA : va.side = .a
  sideB : vb.side = .b
  prog : va.program = prog
  blankA : Blank va
  blankB : Blank vb
  toA : ∀ d ∈ toA, ∃ flag steps cells,
    d = Data.arr [.nat flag, .nat 0, .nat steps, .nat cells, .arr []] ∧
      steps ≤ vb.limit ∧ cells ≤ vb.turnLimit
  toB : ∀ d ∈ toB, ∃ flag steps cells,
    d = Data.arr [.nat flag, .nat 0, .nat steps, .nat cells, .arr []] ∧
      va.budget ≤ steps ∧ va.cells ≤ cells
  ble : vb.budget ≤ vb.limit ∧ vb.cells ≤ vb.turnLimit
  heard : va.heard = true → va.budget ≤ vb.limit ∧ va.cells ≤ vb.turnLimit
  low : min vb.limit va.budget ≤ vb.budget ∧ min vb.turnLimit va.cells ≤ vb.cells

section
variable {va vb va' vb' : View} {toA toB : List Data} {prog : Option Term}

theorem Before.setA (b : Before va vb toA toB prog) {prog' : Option Term} (hw : va'.waiting = true)
    (hs : va'.side = va.side) (hp : va'.program = prog') (hbl : Blank va')
    (hbu : va'.budget ≤ va.budget) (hc : va'.cells ≤ va.cells)
    (hh : va'.heard = true → va'.budget ≤ vb.limit ∧ va'.cells ≤ vb.turnLimit) :
    Before va' vb toA toB prog' where
  awaits := hw
  bwake := b.bwake
  sideA := by rw [hs]; exact b.sideA
  sideB := b.sideB
  prog := hp
  blankA := hbl
  blankB := b.blankB
  toA := b.toA
  toB := by
    intro d hd
    obtain ⟨flag, steps, cells, he, h1, h2⟩ := b.toB d hd
    exact ⟨flag, steps, cells, he, Nat.le_trans hbu h1, Nat.le_trans hc h2⟩
  ble := b.ble
  heard := hh
  low := by
    have := b.low
    omega

theorem Before.setB (b : Before va vb toA toB prog) (hw : vb'.waiting = false) (hs : vb'.side = vb.side)
    (hbl : Blank vb') (hl : vb'.limit = vb.limit) (ht : vb'.turnLimit = vb.turnLimit)
    (hbu : vb'.budget ≤ vb.budget) (hc : vb'.cells ≤ vb.cells)
    (hlow : min vb.limit va.budget ≤ vb'.budget ∧ min vb.turnLimit va.cells ≤ vb'.cells) :
    Before va vb' toA toB prog where
  awaits := b.awaits
  bwake := hw
  sideA := b.sideA
  sideB := by rw [hs]; exact b.sideB
  prog := b.prog
  blankA := b.blankA
  blankB := hbl
  toA := by rw [hl, ht]; exact b.toA
  toB := b.toB
  ble := by
    have := b.ble
    rw [hl, ht]
    omega
  heard := by rw [hl, ht]; exact b.heard
  low := by rw [hl, ht]; exact hlow

theorem Before.takeA (b : Before va vb toA toB prog) {got steps cells : Nat} {new : List Data}
    (hst : steps ≤ vb.limit) (hce : cells ≤ vb.turnLimit) (hn : new = [])
    (hv : va' = { va with
      sent := va.sent.drop (min got (va.sentBase + va.sent.length) - va.sentBase)
      sentBase := max va.sentBase (min got (va.sentBase + va.sent.length))
      heard := true
      budget := if va.fixed then va.budget else min va.budget steps
      cells := if va.fixed then va.cells else min va.cells cells
      inbox := va.inbox ++ new
      got := va.got + new.length }) :
    Before va' vb toA toB prog := by
  subst hn
  subst hv
  refine b.setA b.awaits rfl b.prog b.blankA.take ?_ ?_ ?_
  · show (if va.fixed then va.budget else min va.budget steps) ≤ va.budget
    rw [b.blankA.fixed]
    exact Nat.min_le_left _ _
  · show (if va.fixed then va.cells else min va.cells cells) ≤ va.cells
    rw [b.blankA.fixed]
    exact Nat.min_le_left _ _
  · intro _
    show (if va.fixed then va.budget else min va.budget steps) ≤ vb.limit ∧
      (if va.fixed then va.cells else min va.cells cells) ≤ vb.turnLimit
    rw [b.blankA.fixed]
    exact ⟨Nat.le_trans (Nat.min_le_right _ _) hst, Nat.le_trans (Nat.min_le_right _ _) hce⟩

theorem Before.takeB (b : Before va vb toA toB prog) {got steps cells : Nat} {new : List Data}
    (hst : va.budget ≤ steps) (hce : va.cells ≤ cells) (hn : new = [])
    (hv : vb' = { vb with
      sent := vb.sent.drop (min got (vb.sentBase + vb.sent.length) - vb.sentBase)
      sentBase := max vb.sentBase (min got (vb.sentBase + vb.sent.length))
      heard := true
      budget := if vb.fixed then vb.budget else min vb.budget steps
      cells := if vb.fixed then vb.cells else min vb.cells cells
      inbox := vb.inbox ++ new
      got := vb.got + new.length }) :
    Before va vb' toA toB prog := by
  subst hn
  subst hv
  have hlow := b.low
  refine b.setB b.bwake rfl b.blankB.take rfl rfl ?_ ?_ ?_
  · show (if vb.fixed then vb.budget else min vb.budget steps) ≤ vb.budget
    rw [b.blankB.fixed]
    exact Nat.min_le_left _ _
  · show (if vb.fixed then vb.cells else min vb.cells cells) ≤ vb.cells
    rw [b.blankB.fixed]
    exact Nat.min_le_left _ _
  · show min vb.limit va.budget ≤ (if vb.fixed then vb.budget else min vb.budget steps) ∧
      min vb.turnLimit va.cells ≤ (if vb.fixed then vb.cells else min vb.cells cells)
    rw [b.blankB.fixed]
    refine ⟨Nat.le_min.mpr ⟨hlow.1, ?_⟩, Nat.le_min.mpr ⟨hlow.2, ?_⟩⟩
    · exact Nat.le_trans (Nat.min_le_right _ _) hst
    · exact Nat.le_trans (Nat.min_le_right _ _) hce

theorem Before.giveA (b : Before va vb toA toB prog) {t : Term} {budget : Nat}
    (hv : va' = { va with program := some t,
                          budget := if va.fixed then va.budget else min va.budget budget }) :
    Before va' vb toA toB (some t) := by
  subst hv
  have bl := b.blankA
  refine b.setA b.awaits rfl rfl
    ⟨bl.cfg, bl.asked, bl.outs, bl.sent, bl.inbox, bl.pending, bl.log, bl.sentBase, bl.got, bl.fixed⟩
    ?_ (Nat.le_refl _) ?_
  · show (if va.fixed then va.budget else min va.budget budget) ≤ va.budget
    rw [bl.fixed]
    exact Nat.min_le_left _ _
  · intro h
    obtain ⟨h1, h2⟩ := b.heard h
    refine ⟨?_, h2⟩
    show (if va.fixed then va.budget else min va.budget budget) ≤ vb.limit
    rw [bl.fixed]
    exact Nat.le_trans (Nat.min_le_left _ _) h1

theorem Before.sendA (b : Before va vb toA toB prog) {d : Data} {flag : Nat} {pkts : List Data}
    (hd : d = .arr [.nat flag, .nat va.got, .nat va.budget, .nat va.cells, .arr pkts])
    (hp : va.sent = [] → pkts = []) : Before va vb toA (d :: toB) prog :=
  { b with
    toB := by
      intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · exact ⟨flag, va.budget, va.cells, by rw [hd, hp b.blankA.sent, b.blankA.got],
          Nat.le_refl _, Nat.le_refl _⟩
      · exact b.toB d' hd' }

theorem Before.sendB (b : Before va vb toA toB prog) {d : Data} {flag : Nat} {pkts : List Data}
    (hd : d = .arr [.nat flag, .nat vb.got, .nat vb.budget, .nat vb.cells, .arr pkts])
    (hp : vb.sent = [] → pkts = []) : Before va vb (d :: toA) toB prog :=
  { b with
    toA := by
      intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · exact ⟨flag, vb.budget, vb.cells, by rw [hd, hp b.blankB.sent, b.blankB.got], b.ble.1, b.ble.2⟩
      · exact b.toA d' hd' }

/-- Guest `a` has just begun: the first state of `Core`. -/
theorem Before.born (b : Before va vb toA toB prog) {t : Term} {st : Status MValue MOutcome}
    {v₀ : View} (hh : va.heard = true)
    (hb : beginIn va.cells va.budget t = some ⟨[⟨st, []⟩], []⟩)
    (hv : v₀ = { va with cfg := ⟨[⟨st, []⟩], []⟩, waiting := false, program := none, fixed := true }) :
    Core v₀ vb toA toB t ⟨[⟨st, []⟩], []⟩ [] [] (Local.init [⟨st, []⟩]) (Local.init []) [] []
      ⟨1, []⟩ ⟨0, []⟩ := by
  subst hv
  have bA := b.blankA
  have bB := b.blankB
  exact
    { awake := rfl
      bwake := b.bwake
      sideA := b.sideA
      sideB := b.sideB
      begun := hb
      runA := .nil
      runB := .nil
      dirA := Dir.init rfl bA.asked bA.outs bA.sent bA.inbox bA.pending bA.log bA.sentBase bA.got
        (fun d hd => by obtain ⟨f, s, c, he, _⟩ := b.toB d hd; exact ⟨f, s, c, he⟩)
      dirB := Dir.init (procs := []) bB.cfg bB.asked bB.outs bB.sent bB.inbox bB.pending bB.log
        bB.sentBase bB.got
        (fun d hd => by obtain ⟨f, s, c, he, _⟩ := b.toA d hd; exact ⟨f, s, c, he⟩)
      path := by
        show SPath Shape.first va.log.reverse vb.log.reverse _
        rw [bA.log, bB.log]
        exact .done
      afixed := rfl
      low := fun _ => by
        obtain ⟨h1, h2⟩ := b.heard hh
        obtain ⟨l1, l2⟩ := b.low
        show va.budget ≤ vb.budget ∧ va.cells ≤ vb.cells
        omega
      got := fun h => by rw [bB.got] at h; omega
      fixed := fun h => by rw [bB.fixed] at h; cases h
      fresh := fun _ => ⟨bB.log, by rw [bB.cfg], bB.pending⟩
      ann := by
        intro d hd flag got steps cells pkts he
        obtain ⟨f, s, c, he', h1, h2⟩ := b.toB d hd
        rw [he'] at he
        simp only [Data.arr.injEq, List.cons.injEq, Data.nat.injEq, and_true] at he
        obtain ⟨_, _, rfl, rfl, rfl⟩ := he
        exact ⟨h1, h2, fun h => absurd rfl h⟩ }

/-- Guest `a` begins its program, or fails to. -/
theorem Before.begin (b : Before va vb toA toB prog) (hbeg : Begins va va') :
    Before va' vb toA toB prog ∨ ∃ t, prog = some t ∧ Alive va' vb toA toB t := by
  cases hbeg with
  | fail hv => subst hv; exact .inl b
  | @ok t cfg log' hw hh hp hb hl hv =>
    right
    refine ⟨t, by rw [← b.prog, hp], ?_⟩
    obtain ⟨st, rfl⟩ := beginIn_inv hb
    have core₀ := b.born hh hb rfl
    obtain ⟨extra, hx, rfl⟩ : ∃ extra, Counted extra ∧ log' = extra ++ va.log := by
      rcases hl with rfl | ⟨m, rfl | rfl⟩
      · exact ⟨[], .inl rfl, rfl⟩
      · exact ⟨[.held m], .inr ⟨m, .inl rfl⟩, by rw [b.blankA.log]; rfl⟩
      · exact ⟨[.full m], .inr ⟨m, .inr rfl⟩, by rw [b.blankA.log]; rfl⟩
    subst hv
    exact core₀.outA ⟨rfl, rfl, rfl, rfl, rfl, id, .inl⟩
      (Out.counted (Out.same core₀.dirA core₀.dirB) hx)

end

/-! What two guests that follow the protocol can reach. -/

/-- Before `a` begins, or after. -/
def InvV (va vb : View) (toA toB : List Data) (prog : Option Term) : Prop :=
  Before va vb toA toB prog ∨ ∃ t, prog = some t ∧ Alive va vb toA toB t

section
variable {va vb va' vb' : View} {toA toB : List Data} {prog : Option Term}

theorem InvV.stepA (i : InvV va vb toA toB prog) (h : Begins va va' ∨ Acts va va') :
    InvV va' vb toA toB prog := by
  rcases i with b | ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c⟩
  · rcases h with hbeg | hact
    · exact b.begin hbeg
    · rw [hact.idle (by rw [b.blankA.cfg]) b.blankA.pending b.blankA.inbox]
      exact .inl b
  · right
    refine ⟨t, hp, ?_⟩
    rcases h with hbeg | hact
    · cases hbeg with
      | ok hw hh hp' hb' hl hv => rw [c.awake] at hw; cases hw
      | fail hv => rw [hv]; exact ⟨_, _, _, _, _, _, _, _, _, c⟩
    · exact c.actA hact

theorem InvV.stepB (i : InvV va vb toA toB prog) (h : Begins vb vb' ∨ Acts vb vb') :
    InvV va vb' toA toB prog := by
  rcases i with b | ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c⟩
  · have hsame : vb' = vb := by
      rcases h with hbeg | hact
      · cases hbeg with
        | ok hw hh hp' hb' hl hv => rw [b.bwake] at hw; cases hw
        | fail hv => exact hv
      · exact hact.idle (by rw [b.blankB.cfg]) b.blankB.pending b.blankB.inbox
    rw [hsame]
    exact .inl b
  · right
    refine ⟨t, hp, ?_⟩
    rcases h with hbeg | hact
    · cases hbeg with
      | ok hw hh hp' hb' hl hv => rw [c.bwake] at hw; cases hw
      | fail hv => rw [hv]; exact ⟨_, _, _, _, _, _, _, _, _, c⟩
    · exact c.actB hact

theorem InvV.takeA {g : Guest} {d : Data} (i : InvV g.view vb toA toB prog) (hd : d ∈ toA) :
    InvV (g.takeData d).view vb toA toB prog := by
  rcases i with b | ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c⟩
  · obtain ⟨flag, steps, cells, rfl, h1, h2⟩ := b.toA d hd
    obtain ⟨new, t, _, hnil, hv⟩ := takeData_view g flag 0 steps cells (pkts := []) (posted := [])
      (by intro seq pkt hm; cases hm)
    exact .inl (b.takeA h1 h2 (hnil rfl) hv)
  · obtain ⟨flag, got, steps, cells, pkts, rfl, hg, hpk⟩ := c.dirB.batches d hd
    obtain ⟨new, t', hdrop, hnil, hv⟩ := takeData_view g flag got steps cells hpk
    obtain ⟨dA, dB⟩ := c.dirA.takes c.dirB hg ⟨t', hdrop⟩ hv
    have hfix : g.view.fixed = true := c.afixed
    exact .inr ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb,
      c.setA dA dB (by rw [hv]) (by rw [hv]) (by rw [hv]; simp [hfix]) (by rw [hv]; simp [hfix])
        (by rw [hv]) (by rw [hv])⟩

theorem InvV.takeB {g : Guest} {d : Data} (i : InvV va g.view toA toB prog) (hd : d ∈ toB) :
    InvV va (g.takeData d).view toA toB prog := by
  rcases i with b | ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c⟩
  · obtain ⟨flag, steps, cells, rfl, h1, h2⟩ := b.toB d hd
    obtain ⟨new, t, _, hnil, hv⟩ := takeData_view g flag 0 steps cells (pkts := []) (posted := [])
      (by intro seq pkt hm; cases hm)
    exact .inl (b.takeB h1 h2 (hnil rfl) hv)
  · obtain ⟨flag, got, steps, cells, pkts, rfl, hg, hpk⟩ := c.dirA.batches d hd
    obtain ⟨new, t', hdrop, hnil, hv⟩ := takeData_view g flag got steps cells hpk
    exact .inr ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c.takeB hd hg ⟨t', hdrop⟩ hnil hv⟩

theorem InvV.sendA {g : Guest} (i : InvV g.view vb toA toB prog) (room : Nat) :
    InvV g.view vb toA (g.batchData room :: toB) prog := by
  obtain ⟨flag, pkts, hd, hnil, hpk⟩ := batchData_shape g room
  rcases i with b | ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c⟩
  · exact .inl (b.sendA hd hnil)
  · exact .inr ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c.sendA hd hpk⟩

theorem InvV.sendB {g : Guest} (i : InvV va g.view toA toB prog) (room : Nat) :
    InvV va g.view (g.batchData room :: toA) toB prog := by
  obtain ⟨flag, pkts, hd, hnil, hpk⟩ := batchData_shape g room
  rcases i with b | ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c⟩
  · exact .inl (b.sendB hd hnil)
  · exact .inr ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c.sendB hd hpk⟩

theorem InvV.giveA {g : Guest} (i : InvV g.view vb toA toB prog) (bytes : ByteArray) (budget : Nat) :
    InvV (g.give bytes budget).view vb toA toB (handed g bytes prog) := by
  rcases i with b | ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c⟩
  · rcases give_view g bytes budget prog with ⟨hv, hh⟩ | ⟨t, hh, hv⟩
    · rw [hv, hh]
      exact .inl b
    · rw [hh]
      exact .inl (b.giveA hv)
  · obtain ⟨h1, h2⟩ := give_awake (g := g) c.awake bytes budget prog
    rw [h1, h2]
    exact .inr ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c⟩

theorem InvV.giveB {g : Guest} (i : InvV va g.view toA toB prog) (bytes : ByteArray) (budget : Nat) :
    InvV va (g.give bytes budget).view toA toB prog := by
  have hw : g.waiting = false := by
    rcases i with b | ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c⟩
    · exact b.bwake
    · exact c.bwake
  rw [(give_awake hw bytes budget none).1]
  exact i

end

/-- Every state two guests that follow the protocol can reach. -/
theorem Reach.inv {s : Pair} (h : Reach s) : InvV s.a.view s.b.view s.toA s.toB s.prog := by
  induction h with
  | first ka kb =>
    exact .inl
      { awaits := rfl
        bwake := rfl
        sideA := rfl
        sideB := rfl
        prog := rfl
        blankA := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        blankB := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        toA := by intro d hd; cases hd
        toB := by intro d hd; cases hd
        ble := ⟨Nat.le_refl _, Nat.le_refl _⟩
        heard := by intro h; cases h
        low := ⟨Nat.min_le_left _ _, Nat.min_le_left _ _⟩ }
  | move _ m ih =>
    cases m with
    | stepA cnt hs => exact ih.stepA (step_view cnt hs)
    | restA cnt hs => exact ih
    | giveA bytes budget => exact ih.giveA bytes budget
    | sendA room => exact ih.sendA room
    | takeA hd => exact ih.takeA hd
    | stepB cnt hs => exact ih.stepB (step_view cnt hs)
    | restB cnt hs => exact ih
    | giveB bytes budget => exact ih.giveB bytes budget
    | sendB room => exact ih.sendB room
    | takeB hd => exact ih.takeB hd

/-! The theorems. -/

section
variable {v w : View} {L M : Local} {rs rw : List (Note × Data)} {W Ww to tw : List Data} {h hw : Half}

/-- Where nothing is in flight toward a guest, its acknowledgements are, in
    order, the crossings its peer took. -/
theorem Dir.acks_eq (me : Dir v w L M rs W to h) (peer : Dir w v M L rw Ww tw hw) (hs : w.sent = [])
    (hi : v.inbox = []) : acksOf v.log.reverse = takingsOf w.log.reverse := by
  rw [me.acks, ← me.all peer hs hi, peer.posted.acks, peer.took, ← peer.log, takingsOf,
    List.filterMap_map]
  rfl

end

/-- A guest that has run anything runs with the other guest's step budget and
    turn space. -/
theorem honest_budget {s : Pair} (h : Reach s) (hf : s.b.fixed = true) :
    s.b.budget = s.a.budget ∧ s.b.cells = s.a.cells := by
  rcases h.inv with b | ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c⟩
  · have hb : s.b.fixed = false := b.blankB.fixed
    rw [hf] at hb
    cases hb
  · exact c.fixed hf

/-- Where nothing is in flight, the two logs combine. -/
theorem honest_combine {s : Pair} (h : Reach s) (hq : s.Quiet) :
    ∃ t last, combineTrace s.a.log.reverse s.b.log.reverse = some (t, last) := by
  obtain ⟨hsa, hsb, hia, hib⟩ := hq
  rcases h.inv with b | ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c⟩
  · have h1 : s.a.log = [] := b.blankA.log
    have h2 : s.b.log = [] := b.blankB.log
    rw [h1, h2]
    exact spath_combine .done rfl
  · refine spath_combine c.path ?_
    simp only [Shape.settled, List.all_eq_true, decide_eq_true_eq]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact c.dirA.calm c.dirB hsb hia x hx
    · exact c.dirB.calm c.dirA hsa hib x hx

/-- Where nothing is in flight and `a` has begun the program it was given,
    `accept` accepts the two logs with the budgets `a` ran with; the check's
    own replay (`traceRun`, from where the program begins) runs to the end, to
    the same configuration; and what the replay reaches is, at each guest's
    places, the processes that guest holds: as many places as processes, and
    the same processes in order. -/
theorem honest_accept {s : Pair} {t : Term} (h : Reach s) (hq : s.Quiet) (hp : s.prog = some t)
    (hb : s.a.waiting = false) :
    ∃ tr last c₀ cfg,
      combineTrace s.a.log.reverse s.b.log.reverse = some (tr, last) ∧
      beginIn s.a.cells s.a.budget t = some c₀ ∧
      accept s.a.cells s.a.budget t s.a.log.reverse s.b.log.reverse = some (traceEvents tr, cfg) ∧
      (∀ (places : Side → List Nat) (pa pb : Nat),
        (traceRun s.a.cells s.a.budget places c₀ pa pb tr).stopped = .ran ∧
        (traceRun s.a.cells s.a.budget places c₀ pa pb tr).cfg = cfg) ∧
      last.placeA.length = s.a.cfg.procs.length ∧ last.placeB.length = s.b.cfg.procs.length ∧
      last.placeA.filterMap (cfg.procs[·]?) = s.a.cfg.procs ∧
      last.placeB.filterMap (cfg.procs[·]?) = s.b.cfg.procs := by
  obtain ⟨tr, last, hc⟩ := honest_combine h hq
  rcases h.inv with b | ⟨t', hp', c₀, ra, rb, La, Lb, Wa, Wb, ha, hb', c⟩
  · have hw : s.a.waiting = true := b.awaits
    rw [hb] at hw
    cases hw
  · rw [hp] at hp'
    cases hp'
    have runB : SideRun s.a.cells s.a.budget .b (Local.init []) rb Lb := by
      cases hf : s.b.fixed with
      | true =>
        obtain ⟨e1, e2⟩ : s.b.budget = s.a.budget ∧ s.b.cells = s.a.cells := c.fixed hf
        have hr : SideRun s.b.cells s.b.budget .b (Local.init []) rb Lb := c.runB
        rw [e1, e2] at hr
        exact hr
      | false =>
        have hl : s.b.log = [] := (c.fresh hf).1
        have hrb : rb = [] := by
          have := c.dirB.log
          rw [show s.b.view.log = s.b.log from rfl, hl] at this
          simpa using this
        subst hrb
        have := c.runB.nil_inv
        subst this
        exact .nil
    have hla : ra.map (·.1) = s.a.log.reverse := c.dirA.log
    have hlb : rb.map (·.1) = s.b.log.reverse := c.dirB.log
    rw [← hla, ← hlb] at hc ⊢
    obtain ⟨cfg, hacc, htr, hna, hnb, hpa, hpb⟩ := replay_agrees c.begun c.runA runB
      (fun r hr k hk => (c.dirA.link r hr k hk).1) (fun r hr k hk => (c.dirB.link r hr k hk).1) hc
    exact ⟨tr, last, c₀, cfg, hc, c.begun, hacc, htr,
      by rw [hna]; exact congrArg List.length c.dirA.procs,
      by rw [hnb]; exact congrArg List.length c.dirB.procs,
      by rw [hpa]; exact c.dirA.procs, by rw [hpb]; exact c.dirB.procs⟩

/-- Where nothing is in flight, each guest's acknowledgements are in the order
    the other took its crossings. -/
theorem honest_acks {s : Pair} (h : Reach s) (hq : s.Quiet) :
    acksOf s.b.log.reverse = takingsOf s.a.log.reverse ∧
    acksOf s.a.log.reverse = takingsOf s.b.log.reverse := by
  obtain ⟨hsa, hsb, hia, hib⟩ := hq
  rcases h.inv with b | ⟨t, hp, c₀, ra, rb, La, Lb, Wa, Wb, ha, hb, c⟩
  · have h1 : s.a.log = [] := b.blankA.log
    have h2 : s.b.log = [] := b.blankB.log
    rw [h1, h2]
    exact ⟨rfl, rfl⟩
  · exact ⟨c.dirB.acks_eq c.dirA hsa hib, c.dirA.acks_eq c.dirB hsb hia⟩

end Surface.Cross
