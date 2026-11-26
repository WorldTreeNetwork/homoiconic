import Surface.CrossModel
import Reflect.CrossingLocal

/-!
What one step of a guest does.

`Guest.view` is what the proofs read of a guest. `Acts` and `Begins` say, case
by case, how a step changes it: every case of `Guest.begin`, `Guest.takeIn`,
`Guest.takeSend` and `Guest.act` is one constructor, with what the guest
checked on the way as its premises. `step_view` says a step is one of them.
Nothing here is about two guests.
-/
namespace Surface.Cross
open Reflect

/-- What the proofs read of a guest. -/
structure View where
  side : Side
  cfg : MConfig
  asked : List Asked
  outs : Nat
  sent : List Data
  inbox : List Data
  pending : List Pending
  log : List Note
  sentBase : Nat
  got : Nat
  budget : Nat
  cells : Nat
  limit : Nat
  turnLimit : Nat
  fixed : Bool
  waiting : Bool
  heard : Bool
  program : Option Term

def Guest.view (g : Guest) : View :=
  ⟨g.side, g.cfg, g.asked, g.outs, g.sent, g.inbox, g.pending, g.log, g.sentBase, g.got, g.budget,
    g.cells, g.limit, g.turnLimit, g.fixed, g.waiting, g.heard, g.program⟩

/-- The packet a pending send came as. -/
def Pending.pkt (p : Pending) : Data :=
  .arr [.nat 1, .nat p.k, .nat p.name, p.message, .arr (p.held.map .nat)]

/-- What `Guest.note` records after an entry: nothing, or one count. -/
def Counted (extra : List Note) : Prop := extra = [] ∨ ∃ m, extra = [.held m] ∨ extra = [.full m]

/-- A step other than beginning the program. -/
inductive Acts : View → View → Prop where
  /-- Nothing the proofs read changed. -/
  | same {v v' : View} (hv : v' = v) : Acts v v'
  /-- A packet was worked and nothing recorded: a start or a send dropped, or
      something that is no packet. It is not the acknowledgement of a crossing
      still out. -/
  | drop {v v' : View} {pkt : Data} {rest : List Data} {fixed : Bool} (hin : v.inbox = pkt :: rest)
      (hno : ∀ a ∈ v.asked, pkt ≠ ackPacket a.k) (hfix : v.fixed = true → fixed = true)
      (hv : v' = { v with inbox := rest, fixed := fixed }) : Acts v v'
  /-- An acknowledgement whose asker has no process. (It does not happen.) -/
  | lost {v v' : View} {k : Nat} {rest : List Data} {a : Asked} (hin : v.inbox = .arr [.nat 2, .nat k] :: rest)
      (ha : a ∈ v.asked) (hk : a.k = k) (hq : v.cfg.procs[a.place]? = none)
      (hv : v' = { v with inbox := rest, fixed := true }) : Acts v v'
  /-- The peer's send was queued until a receiver can take it. -/
  | queue {v v' : View} {rest : List Data} {p : Pending} (hin : v.inbox = p.pkt :: rest)
      (hv : v' = { v with inbox := rest, pending := v.pending ++ [p], fixed := true }) : Acts v v'
  /-- A pending send was dropped: its receiver's turn did not finish. -/
  | unqueue {v v' : View} {k : Nat} (hv : v' = { v with pending := v.pending.filter (·.k != k) }) :
      Acts v v'
  | did {v v' : View} {ev : Event} {cfg : MConfig} {extra : List Note}
      (h : stepIn v.cells v.budget v.cfg ev = .ok cfg)
      (free : ∀ i ∈ ev.places, v.asked.any (·.place == i) = false) (inside : ev.isAnswer = false)
      (par : ∀ i n, ev = .fresh i n → n % 2 = v.side.parity) (hx : Counted extra)
      (hv : v' = { v with cfg := cfg, log := extra ++ .did ev :: v.log }) : Acts v v'
  | out {v v' : View} {i : Nat} {c : MValue} {p : Data} {held : List Nat} {pkt : Data}
      {next : Status MValue MOutcome} {extra : List Note}
      (hi : v.cfg.procs[i]? = some ⟨.waiting c p, held⟩)
      (free : v.asked.any (·.place == i) = false) (hw : wantsOut ⟨.waiting c p, held⟩ = true)
      (hp : packetOf v.outs held p = some pkt) (ht : turnIn v.cells v.budget c (.arr []) = some next)
      (hx : Counted extra)
      (hv : v' = { v with asked := ⟨i, v.outs, next⟩ :: v.asked, outs := v.outs + 1,
                          sent := v.sent ++ [pkt], log := extra ++ .out i v.outs :: v.log }) : Acts v v'
  | spawnIn {v v' : View} {k : Nat} {prog start : Data} {held rest : List Data} {t : Term}
      {hs : List Nat} {w : MOutcome} {child : Status MValue MOutcome} {extra : List Note}
      (hin : v.inbox = .arr [.nat 0, .nat k, prog, start, .arr held] :: rest)
      (hu : unreify prog = some t) (hn : packetNats held = some hs)
      (hr : runTurnIn v.cells v.budget (load (compile (.app t (.lit start)))) = .halted w)
      (hc : settleIn v.cells v.budget w = some child) (hx : Counted extra)
      (hv : v' = { v with cfg := ⟨v.cfg.procs ++ [⟨child, hs⟩], v.cfg.names⟩,
                          sent := v.sent ++ [ackPacket k], inbox := rest, fixed := true,
                          log := extra ++ .spawnIn k :: v.log }) : Acts v v'
  | sendIn {v v' : View} {p : Pending} {j : Nat} {c : MValue} {pl : Data} {held' : List Nat}
      {st : Status MValue MOutcome} {extra : List Note}
      (hp : p ∈ v.pending) (hj : v.cfg.procs[j]? = some ⟨.waiting c pl, held'⟩)
      (free : v.asked.any (·.place == j) = false)
      (hrecv : receivesOn p.name ⟨.waiting c pl, held'⟩ = true)
      (ht : turnIn v.cells v.budget c p.message = some st) (hx : Counted extra)
      (hv : v' = { v with cfg := ⟨v.cfg.procs.set j ⟨st, gain held' p.held⟩, v.cfg.names⟩,
                          sent := v.sent ++ [ackPacket p.k],
                          pending := v.pending.filter (·.k != p.k),
                          log := extra ++ .sendIn p.k j :: v.log }) : Acts v v'
  | ack {v v' : View} {k : Nat} {rest : List Data} {a : Asked} {q : Proc MValue MOutcome}
      {extra : List Note} (hin : v.inbox = .arr [.nat 2, .nat k] :: rest)
      (ha : a ∈ v.asked) (hk : a.k = k) (hq : v.cfg.procs[a.place]? = some q) (hx : Counted extra)
      (hv : v' = { v with cfg := ⟨v.cfg.procs.set a.place ⟨a.next, q.held⟩, v.cfg.names⟩,
                          asked := v.asked.filter (·.k != k), inbox := rest, fixed := true,
                          log := extra ++ .ack k a.place :: v.log }) : Acts v v'

/-- Side `a` begins its program, or fails to. -/
inductive Begins : View → View → Prop where
  | ok {v v' : View} {t : Term} {cfg : MConfig} {log' : List Note} (hw : v.waiting = true)
      (hh : v.heard = true) (hp : v.program = some t) (hb : beginIn v.cells v.budget t = some cfg)
      (hl : log' = v.log ∨ ∃ m, log' = [.held m] ∨ log' = [.full m])
      (hv : v' = { v with cfg := cfg, waiting := false, program := none, fixed := true, log := log' }) :
      Begins v v'
  | fail {v v' : View} (hv : v' = v) : Begins v v'

/-! `Guest.note`. -/

theorem note_view (count : Guest → Nat) (g : Guest) (n : Note) (cost : Nat) :
    ∃ extra, Counted extra ∧
      (g.note count n cost).view = { g.view with log := extra ++ n :: g.log } := by
  unfold Guest.note
  simp only
  split
  · exact ⟨[], .inl rfl, rfl⟩
  · split
    · exact ⟨[], .inl rfl, rfl⟩
    · generalize count _ = m
      split
      · next hc => exact ⟨[.held m], .inr ⟨m, .inl rfl⟩, by simp [Guest.view]⟩
      · next hc => exact ⟨[.full m], .inr ⟨m, .inr rfl⟩, by simp [Guest.view]⟩

/-! Names and lists. -/

theorem numbers_eq (ds : List Data) : numbers ds = packetNats ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [numbers, packetNats, ih]

theorem findProc_some {ok : Proc MValue MOutcome → Bool} {procs : List (Proc MValue MOutcome)}
    {j : Nat} (h : findProc ok procs = some j) : ∃ q, procs[j]? = some q ∧ ok q = true := by
  unfold findProc at h
  simp only at h
  split at h
  · next hlt =>
    cases h
    exact ⟨_, List.getElem?_eq_getElem hlt, List.findIdx_getElem⟩
  · cases h

/-- A process the masked configuration shows waiting is the guest's own
    process, and is not held. -/
theorem masked_waiting {g : Guest} {i : Nat} {c : MValue} {p : Data} {held : List Nat}
    (h : g.masked.procs[i]? = some ⟨.waiting c p, held⟩) :
    g.cfg.procs[i]? = some ⟨.waiting c p, held⟩ ∧ g.asked.any (·.place == i) = false := by
  simp only [Guest.masked, List.getElem?_mapIdx] at h
  cases hq : g.cfg.procs[i]? with
  | none => simp [hq] at h
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at h
    split at h
    · cases h
    · next hc =>
      subst h
      refine ⟨rfl, ?_⟩
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
      exact hc.1.1

def isWaiting (q : Proc MValue MOutcome) : Bool :=
  match q.status with
  | .waiting _ _ => true
  | .finished _ => false

theorem receivesOn_waiting {ch : Nat} {q : Proc MValue MOutcome} (h : receivesOn ch q = true) :
    isWaiting q = true := by
  unfold receivesOn at h
  unfold isWaiting
  split at h
  · next hs => rw [hs]
  · cases h

theorem sendsOn_waiting {ch : Nat} {q : Proc MValue MOutcome} (h : sendsOn ch q = true) :
    isWaiting q = true := by
  unfold sendsOn at h
  unfold isWaiting
  split at h
  · next hs => rw [hs]
  · cases h

/-- What `offer` offers names only waiting processes: the one that offers,
    and the partner it found. -/
theorem offer_waiting {cfg : MConfig} {i : Nat} {q : Proc MValue MOutcome} {ev : Event}
    (hq : cfg.procs[i]? = some q) (h : offer cfg i q = some ev) :
    ∀ x ∈ ev.places, ∃ q', cfg.procs[x]? = some q' ∧ isWaiting q' = true := by
  have hwq : isWaiting q = true := by
    unfold offer at h
    unfold isWaiting
    split at h
    · next hs => rw [hs]
    · cases h
  unfold offer at h
  split at h
  · next c p hs =>
    split at h
    · cases h
      intro x hx
      simp only [Event.places, List.mem_singleton] at hx
      subst hx
      exact ⟨q, hq, hwq⟩
    · cases h
      intro x hx
      simp only [Event.places, List.mem_singleton] at hx
      subst hx
      exact ⟨q, hq, hwq⟩
    · next ch v hc =>
      split at h
      · cases hf : findProc (receivesOn ch) cfg.procs with
        | none => simp [hf] at h
        | some j =>
          simp [hf] at h
          subst h
          obtain ⟨q', hq', hr⟩ := findProc_some hf
          intro x hx
          simp only [Event.places, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact ⟨q, hq, hwq⟩
          · exact ⟨q', hq', receivesOn_waiting hr⟩
      · cases h
    · next ch hc =>
      split at h
      · cases hf : findProc (sendsOn ch) cfg.procs with
        | none => simp [hf] at h
        | some j =>
          simp [hf] at h
          subst h
          obtain ⟨q', hq', hr⟩ := findProc_some hf
          intro x hx
          simp only [Event.places, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact ⟨q', hq', sendsOn_waiting hr⟩
          · exact ⟨q, hq, hwq⟩
      · cases h
    · cases h
  · cases h

theorem pickFrom_waiting {cfg : MConfig} : ∀ (qs : List (Proc MValue MOutcome)) (k : Nat) {ev : Event},
    (∀ j q, qs[j]? = some q → cfg.procs[k + j]? = some q) → pickFrom cfg k qs = some ev →
    ∀ x ∈ ev.places, ∃ q', cfg.procs[x]? = some q' ∧ isWaiting q' = true := by
  intro qs
  induction qs with
  | nil => intro k ev _ h; simp [pickFrom] at h
  | cons q qs ih =>
    intro k ev hqs h
    simp only [pickFrom] at h
    split at h
    · next ev' ho =>
      cases h
      exact offer_waiting (by simpa using hqs 0 q (by simp)) ho
    · exact ih (k + 1) (fun j q' hj => by
        have := hqs (j + 1) q' (by simpa using hj)
        rw [← this]; congr 1; omega) h

theorem pick_waiting {cfg : MConfig} {ev : Event} (h : pick cfg = some ev) :
    ∀ x ∈ ev.places, ∃ q', cfg.procs[x]? = some q' ∧ isWaiting q' = true :=
  pickFrom_waiting cfg.procs 0 (fun j q hj => by simpa using hj) h

/-- What `pick` on the masked configuration names is not held. -/
theorem pick_free {g : Guest} {ev : Event} (h : pick g.masked = some ev) :
    ∀ x ∈ ev.places, g.asked.any (·.place == x) = false := by
  intro x hx
  obtain ⟨q', hq', hw⟩ := pick_waiting h x hx
  obtain ⟨st, held⟩ := q'
  cases st with
  | waiting c p => exact (masked_waiting hq').2
  | finished r => simp [isWaiting] at hw

/-- `pickFrom` gives what some process offers. -/
theorem pickFrom_offer {cfg : MConfig} : ∀ (qs : List (Proc MValue MOutcome)) (k : Nat) {ev : Event},
    (∀ j q, qs[j]? = some q → cfg.procs[k + j]? = some q) → pickFrom cfg k qs = some ev →
    ∃ i q, cfg.procs[i]? = some q ∧ offer cfg i q = some ev := by
  intro qs
  induction qs with
  | nil => intro k ev _ h; simp [pickFrom] at h
  | cons q qs ih =>
    intro k ev hqs h
    simp only [pickFrom] at h
    split at h
    · next ev' ho =>
      cases h
      exact ⟨k, q, by simpa using hqs 0 q (by simp), ho⟩
    · exact ih (k + 1) (fun j q' hj => by
        have := hqs (j + 1) q' (by simpa using hj)
        rw [← this]; congr 1; omega) h

/-- A start that `pick` offers is offered by a process that waits on a start
    request. -/
theorem pick_spawn {cfg : MConfig} {i : Nat} (h : pick cfg = some (.spawn i)) :
    ∃ q, cfg.procs[i]? = some q ∧ wantsOut q = true := by
  obtain ⟨k, q, hq, ho⟩ := pickFrom_offer cfg.procs 0 (fun j q hj => by simpa using hj) h
  unfold offer at ho
  split at ho
  · next c p hs =>
    split at ho
    · cases ho
    · next t arg hc =>
      cases ho
      exact ⟨q, hq, by simp [wantsOut, hs, hc]⟩
    · next ch v hc =>
      split at ho
      · cases hf : findProc (receivesOn ch) cfg.procs <;> simp [hf] at ho
      · cases ho
    · next ch hc =>
      split at ho
      · cases hf : findProc (sendsOn ch) cfg.procs <;> simp [hf] at ho
      · cases ho
    · cases ho
  · cases ho

theorem wantsSend_out {q : Proc MValue MOutcome} (h : wantsSend q = true) : wantsOut q = true := by
  unfold wantsSend at h
  unfold wantsOut
  split at h
  · next c p hs =>
    rw [hs]
    simp only
    split at h
    · next ch v hc => rw [hc]; exact h
    · cases h
  · cases h

theorem wantsOut_waiting {q : Proc MValue MOutcome} (h : wantsOut q = true) : isWaiting q = true := by
  unfold wantsOut at h
  unfold isWaiting
  split at h
  · next hs => rw [hs]
  · cases h

/-- A process the masked configuration shows wanting to put a request out is
    the guest's own, wants the same, and is not held. -/
theorem masked_wants {g : Guest} {i : Nat} {q₀ : Proc MValue MOutcome}
    (h : g.masked.procs[i]? = some q₀) (hw : wantsOut q₀ = true) :
    g.asked.any (·.place == i) = false ∧ ∀ q, g.cfg.procs[i]? = some q → wantsOut q = true := by
  obtain ⟨st, held⟩ := q₀
  cases st with
  | finished r => have := wantsOut_waiting hw; simp [isWaiting] at this
  | waiting c p =>
    obtain ⟨hreal, hfree⟩ := masked_waiting h
    refine ⟨hfree, ?_⟩
    intro q hq
    rw [hreal] at hq
    cases hq
    exact hw

/-! The steps. -/

/-- A goal about a guest after `Guest.note` is a goal about it before, with
    the entry and what the count added. -/
theorem acts_note {v : View} (count : Guest → Nat) (x : Guest) (n : Note) (cost : Nat)
    (f : ∀ extra, Counted extra → Acts v { x.view with log := extra ++ n :: x.log }) :
    Acts v (x.note count n cost).view := by
  obtain ⟨extra, hx, hv⟩ := note_view count x n cost
  rw [hv]
  exact f extra hx

theorem begin_view (count : Guest → Nat) {g g' : Guest} (h : g.begin count = some g') :
    Begins g.view g'.view := by
  unfold Guest.begin at h
  split at h
  · cases h
  · next hc =>
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hc
    split at h
    · cases h
    · next t hp =>
      simp only at h
      split at h
      · next cfg hb =>
        rw [beginMade_fst] at hb
        split at h
        · cases h
          exact .ok hc.1 hc.2 hp hb (.inl rfl) rfl
        · generalize count _ = m at h
          split at h
          · next hm =>
            cases h
            exact .ok hc.1 hc.2 hp hb (.inr ⟨m, .inl rfl⟩) (by simp [Guest.view])
          · next hm =>
            cases h
            exact .ok hc.1 hc.2 hp hb (.inr ⟨m, .inr rfl⟩) (by simp [Guest.view])
      · cases h
        exact .fail rfl

theorem happen_view (count : Guest → Nat) (g : Guest) (i : Nat) (ev : Event) :
    (g.happen count i ev).view = g.view ∨
    ∃ cfg extra, stepIn g.cells g.budget g.cfg ev = .ok cfg ∧ Counted extra ∧
      (g.happen count i ev).view = { g.view with cfg := cfg, log := extra ++ .did ev :: g.log } := by
  unfold Guest.happen
  simp only
  split
  · next cfg hs =>
    rw [stepMade_fst] at hs
    obtain ⟨extra, hx, hv⟩ := note_view count { g with cfg := cfg } (.did ev)
      (didCharge g.cfg ev (stepMade g.cells g.budget g.cfg ev).2.1 (stepMade g.cells g.budget g.cfg ev).2.2)
    exact .inr ⟨cfg, extra, hs, hx, hv⟩
  · exact .inl rfl

theorem ask_view (count : Guest → Nat) {g g' : Guest} {i : Nat} (h : g.ask count i = some g')
    (free : g.asked.any (·.place == i) = false)
    (hw : ∀ q, g.cfg.procs[i]? = some q → wantsOut q = true) : Acts g.view g'.view := by
  unfold Guest.ask at h
  split at h
  · cases h
  · split at h
    · next c p held hi =>
      split at h
      · next pkt hp =>
        split at h
        · cases h; exact .same rfl
        · simp only at h
          split at h
          · next next ht =>
            cases h
            rw [turnMade_fst] at ht
            apply acts_note
            intro extra hx
            exact .out hi free (hw _ hi) hp ht hx rfl
          · cases h; exact .same rfl
      · cases h
    · cases h

theorem takeIn_view (count : Guest → Nat) {g g' : Guest} (h : g.takeIn count = some g') :
    Acts g.view g'.view := by
  unfold Guest.takeIn at h
  split at h
  · cases h
  · next pkt rest hin =>
    split at h
    · next k prog start held =>
      have hdrop : Acts g.view ({ g with inbox := rest, fixed := true } : Guest).view :=
        .drop (fixed := true) hin (by intro a _; simp [ackPacket]) (fun _ => rfl) rfl
      split at h
      · cases h
      · try simp only at h
        split at h
        · cases h; exact hdrop
        · split at h
          · next t hs hu hn =>
            try simp only at h
            split at h
            · next w hr =>
              rw [runTurnMade_fst] at hr
              split at h
              · next child hc =>
                cases h
                rw [settleMade_fst] at hc
                rw [numbers_eq] at hn
                apply acts_note
                intro extra hx
                exact .spawnIn hin hu hn hr hc hx rfl
              · cases h; exact hdrop
            · cases h; exact hdrop
          · cases h; exact hdrop
    · next k name message held =>
      try simp only at h
      split at h
      · cases h
        exact .drop (fixed := true) hin (by intro a _; simp [ackPacket]) (fun _ => rfl) rfl
      · split at h
        · next hs hn =>
          cases h
          rw [numbers_eq] at hn
          have hp : (Data.arr [.nat 1, .nat k, .nat name, message, .arr held]) =
              Pending.pkt ⟨k, name, message, hs⟩ := by
            simp [Pending.pkt, packetNats_eq hn]
          rw [hp] at hin
          exact .queue hin rfl
        · cases h
          exact .drop (fixed := true) hin (by intro a _; simp [ackPacket]) (fun _ => rfl) rfl
    · next k =>
      try simp only at h
      split at h
      · next a hf =>
        have ha : a ∈ g.asked := List.mem_of_find?_eq_some hf
        have hk : a.k = k := by simpa using List.find?_some hf
        split at h
        · next q hq =>
          cases h
          apply acts_note
          intro extra hx
          exact .ack hin ha hk hq hx rfl
        · next hq =>
          cases h
          exact .lost hin ha hk hq rfl
      · next hf =>
        cases h
        refine .drop (fixed := true) hin ?_ (fun _ => rfl) rfl
        intro a ha he
        simp only [ackPacket, Data.arr.injEq, List.cons.injEq, Data.nat.injEq, true_and, and_true] at he
        have := List.find?_eq_none.mp hf a ha
        simp [he] at this
    · next h₀ h₁ h₂ =>
      cases h
      refine .drop (fixed := g.fixed) hin ?_ (fun h => h) rfl
      intro a _ he
      exact h₂ a.k he

theorem takeSend_view (count : Guest → Nat) {g g' : Guest} (h : g.takeSend count = some g') :
    Acts g.view g'.view := by
  unfold Guest.takeSend at h
  split at h
  · cases h
  · try simp only at h
    split at h
    · cases h
    · next p hsel =>
      have hp : p ∈ g.pending := by
        have : p ∈ g.pending.filter fun p => (findProc (receivesOn p.name) g.masked.procs).isSome := by
          split at hsel
          · exact List.mem_of_getLast? hsel
          · exact List.mem_of_head? hsel
        exact (List.mem_filter.mp this).1
      have hun : Acts g.view ({ g with pending := g.pending.filter (·.k != p.k) } : Guest).view :=
        .unqueue rfl
      split at h
      · next j hf =>
        obtain ⟨q₀, hq₀, hr⟩ := findProc_some hf
        split at h
        · next c pl held hj =>
          try simp only at h
          have hreal : g.cfg.procs[j]? = some ⟨.waiting c pl, held⟩ := hj
          have hmask : g.masked.procs[j]? = some ⟨.waiting c pl, held⟩ := by
            obtain ⟨st₀, held₀⟩ := q₀
            cases st₀ with
            | finished r => have := receivesOn_waiting hr; simp [isWaiting] at this
            | waiting c₀ p₀ =>
              obtain ⟨h₁, _⟩ := masked_waiting hq₀
              rw [hreal] at h₁
              cases h₁
              exact hq₀
          have hrecv : receivesOn p.name ⟨.waiting c pl, held⟩ = true := by
            rw [hmask] at hq₀
            cases hq₀
            exact hr
          split at h
          · next st ht =>
            cases h
            rw [turnMade_fst] at ht
            apply acts_note
            intro extra hx
            exact .sendIn hp hreal (masked_waiting hmask).2 hrecv ht hx rfl
          · cases h; exact hun
        · cases h; exact hun
      · cases h; exact hun

theorem act_view (count : Guest → Nat) {g g' : Guest} (h : g.act count = some g') :
    Acts g.view g'.view := by
  unfold Guest.act at h
  split at h
  · cases h
  · simp only at h
    split at h
    · next i n hpk =>
      cases h
      have hfree := pick_free hpk
      rcases happen_view count { g with made := g.made + 1 } i
        (.fresh i (2 * g.made + if g.side = .a then 0 else 1)) with hv | ⟨cfg, extra, hs, hx, hv⟩
      · exact .same hv
      · refine .did hs (fun x hx => hfree x (by simpa [Event.places] using hx)) rfl ?_ hx hv
        intro i' n' he
        cases he
        show _ % 2 = g.side.parity
        cases g.side <;> simp [Side.parity] <;> omega
    · next i hpk =>
      split at h
      · obtain ⟨q₀, hq₀, hw⟩ := pick_spawn hpk
        obtain ⟨hfree, hwants⟩ := masked_wants hq₀ hw
        exact ask_view count h hfree hwants
      · cases h
        have hfree := pick_free hpk
        rcases happen_view count g i (.spawn i) with hv | ⟨cfg, extra, hs, hx, hv⟩
        · exact .same hv
        · exact .did hs hfree rfl (by intro _ _ he; cases he) hx hv
    · next i j hpk =>
      cases h
      have hfree := pick_free hpk
      rcases happen_view count g i (.comm i j) with hv | ⟨cfg, extra, hs, hx, hv⟩
      · exact .same hv
      · exact .did hs hfree rfl (by intro _ _ he; cases he) hx hv
    · cases h
    · split at h
      · next i hf =>
        obtain ⟨q₀, hq₀, hw⟩ := findProc_some hf
        obtain ⟨hfree, hwants⟩ := masked_wants hq₀ (wantsSend_out hw)
        exact ask_view count h hfree hwants
      · cases h

/-- A step of a guest is one of the cases of `Begins` and `Acts`. -/
theorem step_view (count : Guest → Nat) {g g' : Guest} (h : g.step count = some g') :
    Begins g.view g'.view ∨ Acts g.view g'.view := by
  unfold Guest.step at h
  split at h
  · next g₁ hb => cases h; exact .inl (begin_view count hb)
  · split at h
    · next g₁ ht => cases h; exact .inr (takeIn_view count ht)
    · split at h
      · next g₁ ht => cases h; exact .inr (takeSend_view count ht)
      · exact .inr (act_view count h)

end Surface.Cross
