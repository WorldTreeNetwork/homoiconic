import Reflect.CrossingComplete
import Reflect.HoldProof

/-!
What one guest's log means by itself, and why any order the table allows
replays to it.

`SideStep` is one entry of a guest's log read alone: what the entry needs of
that guest's own processes and what it does to them, with the machine runs
`stepIn` and `turnIn` make. An entry that takes a crossing comes with the
packet it took. `SideRun` is a log read so.

`Walk.replay`: take two logs that are each a `SideRun`, where every crossing
taken was taken as the packet its guest made for it. Then for *any* walk the
table allows over them, the one-machine replay of the walk's events runs to
the end, and where no crossing is left taken and unacknowledged, each guest's
processes are the replay's at that guest's places (`Agree.procs`).

The reason is the one the design of `add-recorded-crossing` gives in prose: a
process that asked is touched by no entry of its own guest from its `out` to
its `ack`, so the turn its guest ran at `out` is the turn the replay runs at
the taking.
-/
namespace Reflect

variable [Ops]

/-! What `stepIn` needs and gives, event by event. -/

theorem stepIn_fresh_inv {cells budget : Nat} {cfg cfg' : MConfig} {i n : Nat}
    (h : stepIn cells budget cfg (.fresh i n) = .ok cfg') :
    ∃ c p held st, cfg.procs[i]? = some ⟨.waiting c p, held⟩ ∧ classify p = .fresh ∧
      cfg.names.contains n = false ∧ turnIn cells budget c (.name n) = some st ∧
      cfg' = ⟨cfg.procs.set i ⟨st, n :: held⟩, n :: cfg.names⟩ := by
  simp only [stepIn] at h
  split at h
  · next c p held hi =>
    split at h
    · next hq =>
      split at h
      · cases h
      · next hn =>
        split at h
        · next st ht =>
          cases h
          exact ⟨c, p, held, st, hi, hq, by simpa using hn, ht, rfl⟩
        · cases h
    · cases h
  · cases h

theorem stepIn_fresh_ok {cells budget : Nat} {cfg : MConfig} {i n : Nat} {c : MValue} {p : Data}
    {held : List Nat} {st : Status MValue MOutcome}
    (hi : cfg.procs[i]? = some ⟨.waiting c p, held⟩) (hq : classify p = .fresh)
    (hn : cfg.names.contains n = false) (ht : turnIn cells budget c (.name n) = some st) :
    stepIn cells budget cfg (.fresh i n) = .ok ⟨cfg.procs.set i ⟨st, n :: held⟩, n :: cfg.names⟩ := by
  have hn' : n ∉ cfg.names := by simpa using hn
  simp [stepIn, hi, hq, hn', ht]

theorem stepIn_spawn_inv {cells budget : Nat} {cfg cfg' : MConfig} {i : Nat}
    (h : stepIn cells budget cfg (.spawn i) = .ok cfg') :
    ∃ c p held t arg w child st, cfg.procs[i]? = some ⟨.waiting c p, held⟩ ∧
      classify p = .spawn t arg ∧
      runTurnIn cells budget (load (compile (.app t (.lit arg)))) = .halted w ∧
      settleIn cells budget w = some child ∧ turnIn cells budget c (.arr []) = some st ∧
      cfg' = ⟨cfg.procs.set i ⟨st, held⟩ ++ [⟨child, grant held arg⟩], cfg.names⟩ := by
  simp only [stepIn] at h
  split at h
  · next c p held hi =>
    split at h
    · next t arg hq =>
      split at h
      · next w hw =>
        split at h
        · next child st hc ht =>
          cases h
          exact ⟨c, p, held, t, arg, w, child, st, hi, hq, hw, hc, ht, rfl⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem stepIn_spawn_ok {cells budget : Nat} {cfg : MConfig} {i : Nat} {c : MValue} {p arg : Data}
    {held : List Nat} {t : Term} {w : MOutcome} {child st : Status MValue MOutcome}
    (hi : cfg.procs[i]? = some ⟨.waiting c p, held⟩) (hq : classify p = .spawn t arg)
    (hw : runTurnIn cells budget (load (compile (.app t (.lit arg)))) = .halted w)
    (hc : settleIn cells budget w = some child) (ht : turnIn cells budget c (.arr []) = some st) :
    stepIn cells budget cfg (.spawn i) =
      .ok ⟨cfg.procs.set i ⟨st, held⟩ ++ [⟨child, grant held arg⟩], cfg.names⟩ := by
  simp [stepIn, hi, hq, hw, hc, ht]

theorem stepIn_comm_inv {cells budget : Nat} {cfg cfg' : MConfig} {i j : Nat}
    (h : stepIn cells budget cfg (.comm i j) = .ok cfg') :
    ∃ c p held c' p' held' ch v st st', cfg.procs[i]? = some ⟨.waiting c p, held⟩ ∧
      cfg.procs[j]? = some ⟨.waiting c' p', held'⟩ ∧ classify p = .send ch v ∧
      classify p' = .receive ch ∧ held.contains ch = true ∧ held'.contains ch = true ∧
      turnIn cells budget c (.arr []) = some st ∧ turnIn cells budget c' v = some st' ∧
      cfg' = ⟨(cfg.procs.set i ⟨st, held⟩).set j ⟨st', gain held' (grant held v)⟩, cfg.names⟩ := by
  simp only [stepIn] at h
  split at h
  · next c p held c' p' held' hi hj =>
    split at h
    · next ch v ch' hq hq' =>
      split at h
      · next hcond =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨⟨rfl, hh⟩, hh'⟩ := hcond
        split at h
        · next st st' ht ht' =>
          cases h
          exact ⟨c, p, held, c', p', held', ch, v, st, st', hi, hj, hq, hq', hh, hh', ht, ht', rfl⟩
        · cases h
      · cases h
    · cases h
  · cases h

theorem stepIn_comm_ok {cells budget : Nat} {cfg : MConfig} {i j : Nat} {c c' : MValue} {p p' v : Data}
    {held held' : List Nat} {ch : Nat} {st st' : Status MValue MOutcome}
    (hi : cfg.procs[i]? = some ⟨.waiting c p, held⟩) (hj : cfg.procs[j]? = some ⟨.waiting c' p', held'⟩)
    (hq : classify p = .send ch v) (hq' : classify p' = .receive ch)
    (hh : held.contains ch = true) (hh' : held'.contains ch = true)
    (ht : turnIn cells budget c (.arr []) = some st) (ht' : turnIn cells budget c' v = some st') :
    stepIn cells budget cfg (.comm i j) =
      .ok ⟨(cfg.procs.set i ⟨st, held⟩).set j ⟨st', gain held' (grant held v)⟩, cfg.names⟩ := by
  have h1 : ch ∈ held := by simpa using hh
  have h2 : ch ∈ held' := by simpa using hh'
  simp [stepIn, hi, hj, hq, hq', h1, h2, ht, ht']

theorem schedIn_one {cells budget : Nat} {cfg cfg' : MConfig} {ev : Event}
    (h : stepIn cells budget cfg ev = .ok cfg') :
    schedIn cells budget cfg [ev] = ([ev], cfg', .ran) := by
  simp [schedIn, h]

/-! The packets. -/

/-- The names a packet hands over, as numbers. -/
def packetNats : List Data → Option (List Nat)
  | [] => some []
  | .nat n :: ds => (packetNats ds).map (n :: ·)
  | _ :: _ => none

omit [Ops] in
theorem packetNats_map (l : List Nat) : packetNats (l.map .nat) = some l := by
  induction l with
  | nil => rfl
  | cons n l ih => simp [packetNats, ih]

omit [Ops] in
theorem packetNats_eq : ∀ {ds : List Data} {l : List Nat}, packetNats ds = some l → ds = l.map .nat := by
  intro ds
  induction ds with
  | nil => intro l h; simp [packetNats] at h; subst h; rfl
  | cons d ds ih =>
    intro l h
    cases d with
    | nat n =>
      simp only [packetNats] at h
      cases hr : packetNats ds with
      | none => simp [hr] at h
      | some l' =>
        simp [hr] at h
        subst h
        simp [ih hr]
    | name n => simp [packetNats] at h
    | text t => simp [packetNats] at h
    | arr xs => simp [packetNats] at h

omit [Ops] in
/-- A start's packet says what its request says. -/
theorem packetOf_start {k k' : Nat} {held : List Nat} {p prog start : Data} {hd : List Data}
    (h : packetOf k held p = some (.arr [.nat 0, .nat k', prog, start, .arr hd])) :
    ∃ t, classify p = .spawn t start ∧ unreify prog = some t ∧ hd = (grant held start).map .nat := by
  unfold packetOf at h
  split at h
  · next prog' arg' t' a' hq =>
    simp only [Option.some.injEq, Data.arr.injEq, List.cons.injEq, and_true] at h
    obtain ⟨_, _, rfl, rfl, rfl⟩ := h
    cases hu : unreify prog' with
    | none => simp [classify, hu] at hq
    | some t => exact ⟨t, by simp [classify, hu], rfl, rfl⟩
  · simp at h
  · cases h

omit [Ops] in
/-- A send's packet says what its request says. -/
theorem packetOf_send {k k' ch : Nat} {held : List Nat} {p v : Data} {hd : List Data}
    (h : packetOf k held p = some (.arr [.nat 1, .nat k', .nat ch, v, .arr hd])) :
    classify p = .send ch v ∧ hd = (grant held v).map .nat := by
  unfold packetOf at h
  split at h
  · simp at h
  · next ch' v' hq =>
    simp only [Option.some.injEq, Data.arr.injEq, List.cons.injEq, Data.nat.injEq, and_true] at h
    obtain ⟨_, _, rfl, rfl, rfl⟩ := h
    exact ⟨hq, rfl⟩
  · cases h

/-! One guest's log, read alone. -/

def Side.parity : Side → Nat
  | .a => 0
  | .b => 1

/-- A crossing a guest put out and has not had acknowledged: the local place
    of the process that asked, the crossing's number, and where its turn on
    `[]` leaves it. -/
structure Ask where
  place : Nat
  k : Nat
  next : Status MValue MOutcome

/-- What a guest's log says of the guest: its processes, the names it made,
    the crossings it has out, the packet of each crossing it ever put out, the
    peer's crossings it took, and every packet it made, in order. -/
structure Local where
  procs : List (Proc MValue MOutcome)
  names : List Nat
  asked : List Ask
  outPkts : List Data
  took : List Nat
  posted : List Data

def Local.init (procs : List (Proc MValue MOutcome)) : Local := ⟨procs, [], [], [], [], []⟩

def Local.held (L : Local) (i : Nat) : Bool := L.asked.any (·.place == i)

def Event.places : Event → List Nat
  | .fresh i _ => [i]
  | .spawn i => [i]
  | .comm i j => [i, j]
  | .answer i _ => [i]

def Event.isAnswer : Event → Bool
  | .answer _ _ => true
  | _ => false

/-- The process waits on a start request, or to send on a name it holds. -/
def wantsOut (q : Proc MValue MOutcome) : Bool :=
  match q.status with
  | .waiting _ p =>
    match classify p with
    | .send ch _ => q.held.contains ch
    | .spawn _ _ => true
    | _ => false
  | _ => false

/-- One entry of guest `s`'s log, with the packet it took when it took one. -/
inductive SideStep (cells budget : Nat) (s : Side) : Local → Note × Data → Local → Prop where
  /-- A local event: one the machine runs on this guest's processes, on
      processes that are not held, and not an answer from outside. A name it
      makes has the guest's parity. -/
  | did {L : Local} {ev : Event} {cfg : MConfig} {d : Data}
      (h : stepIn cells budget ⟨L.procs, L.names⟩ ev = .ok cfg)
      (free : ∀ i ∈ ev.places, L.held i = false) (inside : ev.isAnswer = false)
      (par : ∀ i n, ev = .fresh i n → n % 2 = s.parity) :
      SideStep cells budget s L (.did ev, d) { L with procs := cfg.procs, names := cfg.names }
  /-- A request put out: the process is not held, the crossing's number is the
      count so far, and the asker's turn on `[]` is run and kept. -/
  | out {L : Local} {i k : Nat} {c : MValue} {p : Data} {held : List Nat} {pkt : Data}
      {next : Status MValue MOutcome} {d : Data}
      (hi : L.procs[i]? = some ⟨.waiting c p, held⟩) (free : L.held i = false)
      (hk : k = L.outPkts.length) (hw : wantsOut ⟨.waiting c p, held⟩ = true)
      (hp : packetOf k held p = some pkt) (ht : turnIn cells budget c (.arr []) = some next) :
      SideStep cells budget s L (.out i k, d)
        { L with asked := ⟨i, k, next⟩ :: L.asked, outPkts := L.outPkts ++ [pkt],
                 posted := L.posted ++ [pkt] }
  /-- The peer's start taken: the child is begun and is the next process. -/
  | spawnIn {L : Local} {k : Nat} {prog start : Data} {held : List Data} {t : Term} {hs : List Nat}
      {w : MOutcome} {child : Status MValue MOutcome}
      (hu : unreify prog = some t) (hn : packetNats held = some hs)
      (hr : runTurnIn cells budget (load (compile (.app t (.lit start)))) = .halted w)
      (hc : settleIn cells budget w = some child) :
      SideStep cells budget s L (.spawnIn k, .arr [.nat 0, .nat k, prog, start, .arr held])
        { L with procs := L.procs ++ [⟨child, hs⟩], took := L.took ++ [k],
                 posted := L.posted ++ [ackPacket k] }
  /-- The peer's send taken by a local receiver that is not held. -/
  | sendIn {L : Local} {k j name : Nat} {message : Data} {held : List Data} {hs : List Nat}
      {c : MValue} {p : Data} {held' : List Nat} {st : Status MValue MOutcome}
      (hn : packetNats held = some hs) (hj : L.procs[j]? = some ⟨.waiting c p, held'⟩)
      (free : L.held j = false) (hrecv : receivesOn name ⟨.waiting c p, held'⟩ = true)
      (ht : turnIn cells budget c message = some st) :
      SideStep cells budget s L (.sendIn k j, .arr [.nat 1, .nat k, .nat name, message, .arr held])
        { L with procs := L.procs.set j ⟨st, gain held' hs⟩, took := L.took ++ [k],
                 posted := L.posted ++ [ackPacket k] }
  /-- The peer took a crossing: the turn kept at `out` is the process now. -/
  | ack {L : Local} {k i : Nat} {a : Ask} {q : Proc MValue MOutcome} {d : Data}
      (ha : a ∈ L.asked) (hk : a.k = k) (hp : a.place = i) (hq : L.procs[i]? = some q) :
      SideStep cells budget s L (.ack k i, d)
        { L with procs := L.procs.set i ⟨a.next, q.held⟩, asked := L.asked.filter (·.k != k) }
  | held {L : Local} {m : Nat} {d : Data} : SideStep cells budget s L (.held m, d) L
  | full {L : Local} {m : Nat} {d : Data} : SideStep cells budget s L (.full m, d) L

/-- A guest's log, read alone, entry by entry. -/
inductive SideRun (cells budget : Nat) (s : Side) : Local → List (Note × Data) → Local → Prop where
  | nil {L : Local} : SideRun cells budget s L [] L
  | cons {L M F : Local} {r : Note × Data} {rs : List (Note × Data)}
      (h : SideStep cells budget s L r M) (rest : SideRun cells budget s M rs F) :
      SideRun cells budget s L (r :: rs) F

theorem SideRun.snoc {cells budget : Nat} {s : Side} {L M F : Local} {rs : List (Note × Data)}
    {r : Note × Data} (h : SideRun cells budget s L rs M) (hr : SideStep cells budget s M r F) :
    SideRun cells budget s L (rs ++ [r]) F := by
  induction h with
  | nil => exact .cons hr .nil
  | cons h _ ih => exact .cons h (ih hr)

theorem SideRun.append {cells budget : Nat} {s : Side} {L M F : Local} {rs rs' : List (Note × Data)}
    (h : SideRun cells budget s L rs M) (h' : SideRun cells budget s M rs' F) :
    SideRun cells budget s L (rs ++ rs') F := by
  induction h with
  | nil => exact h'
  | cons h _ ih => exact .cons h (ih h')

/-- The packets of a guest's crossings are only added to. -/
theorem SideStep.outPkts {cells budget : Nat} {s : Side} {L M : Local} {r : Note × Data}
    (h : SideStep cells budget s L r M) {k : Nat} {pkt : Data} (hk : L.outPkts[k]? = some pkt) :
    M.outPkts[k]? = some pkt := by
  cases h with
  | out => simp only; rw [List.getElem?_append_left (lt_of_getElem? hk)]; exact hk
  | _ => exact hk

theorem SideRun.outPkts {cells budget : Nat} {s : Side} {L F : Local} {rs : List (Note × Data)}
    (h : SideRun cells budget s L rs F) {k : Nat} {pkt : Data} (hk : L.outPkts[k]? = some pkt) :
    F.outPkts[k]? = some pkt := by
  induction h with
  | nil => exact hk
  | cons h _ ih => exact ih (h.outPkts hk)

/-! What is true of one guest's state however its log goes on. -/

/-- Each name made here has the guest's parity; each crossing out has its
    process waiting where its request left it, its packet, and its kept turn;
    and no two crossings out share a number or a process. -/
structure Local.Ok (cells budget : Nat) (s : Side) (L : Local) : Prop where
  parity : ∀ n ∈ L.names, n % 2 = s.parity
  asked : ∀ a ∈ L.asked, ∃ c p held pkt, L.procs[a.place]? = some ⟨.waiting c p, held⟩ ∧
    wantsOut ⟨.waiting c p, held⟩ = true ∧ packetOf a.k held p = some pkt ∧
    L.outPkts[a.k]? = some pkt ∧ turnIn cells budget c (.arr []) = some a.next
  uniqK : ∀ a ∈ L.asked, ∀ a' ∈ L.asked, a.k = a'.k → a = a'
  uniqP : ∀ a ∈ L.asked, ∀ a' ∈ L.asked, a.place = a'.place → a = a'

omit [Ops] in
theorem Local.not_held {L : Local} {i : Nat} (h : L.held i = false) : ∀ a ∈ L.asked, a.place ≠ i := by
  intro a ha he
  simp only [Local.held, List.any_eq_false] at h
  exact h a ha (by simp [he])

omit [Ops] in
theorem Local.is_held {L : Local} {a : Ask} (ha : a ∈ L.asked) : L.held a.place = true := by
  simp only [Local.held, List.any_eq_true]
  exact ⟨a, ha, by simp⟩

theorem Local.Ok.init (cells budget : Nat) (s : Side) (procs : List (Proc MValue MOutcome)) :
    Local.Ok cells budget s (Local.init procs) where
  parity := by intro n hn; simp [Local.init] at hn
  asked := by intro a ha; simp [Local.init] at ha
  uniqK := by intro a ha; simp [Local.init] at ha
  uniqP := by intro a ha; simp [Local.init] at ha

/-- An event leaves alone the processes it does not name. -/
theorem stepIn_frame {cells budget : Nat} {cfg cfg' : MConfig} {ev : Event}
    (h : stepIn cells budget cfg ev = .ok cfg') {x : Nat} {q : Proc MValue MOutcome}
    (hx : x ∉ ev.places) (hq : cfg.procs[x]? = some q) : cfg'.procs[x]? = some q := by
  have hlt := lt_of_getElem? hq
  cases ev with
  | fresh i n =>
    obtain ⟨c, p, held, st, _, _, _, _, rfl⟩ := stepIn_fresh_inv h
    simp only [Event.places, List.mem_singleton] at hx
    simp only
    rw [List.getElem?_set_ne (Ne.symm hx)]; exact hq
  | spawn i =>
    obtain ⟨c, p, held, t, arg, w, child, st, _, _, _, _, _, rfl⟩ := stepIn_spawn_inv h
    simp only [Event.places, List.mem_singleton] at hx
    simp only
    rw [List.getElem?_append_left (by rw [List.length_set]; exact hlt),
      List.getElem?_set_ne (Ne.symm hx)]
    exact hq
  | comm i j =>
    obtain ⟨c, p, held, c', p', held', ch, v, st, st', _, _, _, _, _, _, _, _, rfl⟩ := stepIn_comm_inv h
    simp only [Event.places, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only
    rw [List.getElem?_set_ne (Ne.symm hx.2), List.getElem?_set_ne (Ne.symm hx.1)]
    exact hq
  | answer i a =>
    have hs := stepIn_sound h
    cases hs with
    | answer hi hq' ht =>
      simp only [Event.places, List.mem_singleton] at hx
      simp only
      rw [List.getElem?_set_ne (Ne.symm hx)]; exact hq

/-- An event's new names: none, or the one it was given. -/
theorem stepIn_names {cells budget : Nat} {cfg cfg' : MConfig} {ev : Event}
    (h : stepIn cells budget cfg ev = .ok cfg') :
    cfg'.names = cfg.names ∨ ∃ i n, ev = .fresh i n ∧ cfg'.names = n :: cfg.names := by
  have hs := stepIn_sound h
  cases hs with
  | fresh => exact .inr ⟨_, _, rfl, rfl⟩
  | spawn => exact .inl rfl
  | comm => exact .inl rfl
  | answer => exact .inl rfl

/-- What is true of a guest's state stays true through an entry. -/
theorem SideStep.ok {cells budget : Nat} {s : Side} {L M : Local} {r : Note × Data}
    (h : SideStep cells budget s L r M) (ok : Local.Ok cells budget s L) :
    Local.Ok cells budget s M := by
  cases h with
  | @did ev cfg d h free inside par =>
    refine ⟨?_, ?_, ok.uniqK, ok.uniqP⟩
    · intro n hn
      rcases stepIn_names h with hnm | ⟨i, n', rfl, hnm⟩
      · simp only at hn hnm; rw [hnm] at hn; exact ok.parity n hn
      · simp only at hn hnm
        rw [hnm] at hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact par i n rfl
        · exact ok.parity n hn
    · intro a ha
      have ha : a ∈ L.asked := ha
      obtain ⟨c, p, held, pkt, hp, hw, hpk, ho, ht⟩ := ok.asked a ha
      refine ⟨c, p, held, pkt, ?_, hw, hpk, ho, ht⟩
      refine stepIn_frame h ?_ hp
      intro hmem
      have := free a.place hmem
      rw [Local.is_held ha] at this
      cases this
  | @out i k c p held pkt next d hi free hk hw hp ht =>
    refine ⟨ok.parity, ?_, ?_, ?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨c, p, held, pkt, hi, hw, hp, by simp [hk], ht⟩
      · obtain ⟨c', p', held', pkt', hp', hw', hpk', ho', ht'⟩ := ok.asked a ha
        exact ⟨c', p', held', pkt', hp', hw', hpk', by
          rw [List.getElem?_append_left (lt_of_getElem? ho')]; exact ho', ht'⟩
    · intro a ha a' ha' hkk
      have old : ∀ x ∈ L.asked, x.k ≠ k := by
        intro x hx he
        obtain ⟨_, _, _, _, _, _, _, ho, _⟩ := ok.asked x hx
        have := lt_of_getElem? ho
        omega
      rcases List.mem_cons.mp ha with rfl | ha
      · rcases List.mem_cons.mp ha' with rfl | ha'
        · rfl
        · exact absurd hkk.symm (old a' ha')
      · rcases List.mem_cons.mp ha' with rfl | ha'
        · exact absurd hkk (old a ha)
        · exact ok.uniqK a ha a' ha' hkk
    · intro a ha a' ha' hpp
      have old := Local.not_held free
      rcases List.mem_cons.mp ha with rfl | ha
      · rcases List.mem_cons.mp ha' with rfl | ha'
        · rfl
        · exact absurd hpp.symm (old a' ha')
      · rcases List.mem_cons.mp ha' with rfl | ha'
        · exact absurd hpp (old a ha)
        · exact ok.uniqP a ha a' ha' hpp
  | spawnIn hu hn hr hc =>
    refine ⟨ok.parity, ?_, ok.uniqK, ok.uniqP⟩
    intro a ha
    obtain ⟨c, p, held, pkt, hp, hw, hpk, ho, ht⟩ := ok.asked a ha
    exact ⟨c, p, held, pkt, by
      simp only; rw [List.getElem?_append_left (lt_of_getElem? hp)]; exact hp, hw, hpk, ho, ht⟩
  | @sendIn k j name message held hs c p held' st hn hj free hrecv ht =>
    refine ⟨ok.parity, ?_, ok.uniqK, ok.uniqP⟩
    intro a ha
    obtain ⟨c', p', held'', pkt, hp, hw, hpk, ho, ht'⟩ := ok.asked a ha
    exact ⟨c', p', held'', pkt, by
      simp only; rw [List.getElem?_set_ne (Ne.symm (Local.not_held free a ha))]; exact hp,
      hw, hpk, ho, ht'⟩
  | @ack k i a q d ha hk hp hq =>
    have sub : ∀ x, x ∈ L.asked.filter (·.k != k) → x ∈ L.asked ∧ x.k ≠ k := by
      intro x hx
      rw [List.mem_filter] at hx
      exact ⟨hx.1, by simpa using hx.2⟩
    refine ⟨ok.parity, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨hx, hne⟩ := sub x hx
      obtain ⟨c, p, held, pkt, hp', hw, hpk, ho, ht⟩ := ok.asked x hx
      have hpl : x.place ≠ i := by
        intro he
        have := ok.uniqP x hx a ha (by rw [he, hp])
        rw [this] at hne
        exact hne hk
      exact ⟨c, p, held, pkt, by simp only; rw [List.getElem?_set_ne (Ne.symm hpl)]; exact hp',
        hw, hpk, ho, ht⟩
    · intro x hx x' hx' he
      exact ok.uniqK x (sub x hx).1 x' (sub x' hx').1 he
    · intro x hx x' hx' he
      exact ok.uniqP x (sub x hx).1 x' (sub x' hx').1 he
  | held => exact ok
  | full => exact ok

theorem SideRun.ok {cells budget : Nat} {s : Side} {L F : Local} {rs : List (Note × Data)}
    (h : SideRun cells budget s L rs F) (ok : Local.Ok cells budget s L) : Local.Ok cells budget s F := by
  induction h with
  | nil => exact ok
  | cons h _ ih => exact ih (h.ok ok)

/-! The replay beside the two guests' states. -/

/-- The two guests' states with guest `s`'s replaced. -/
def setSide (L : Side → Local) (s : Side) (x : Local) : Side → Local :=
  fun u => if u = s then x else L u

omit [Ops] in
theorem setSide_same (L : Side → Local) (s : Side) (x : Local) : setSide L s x s = x := by
  simp [setSide]

omit [Ops] in
theorem setSide_other (L : Side → Local) {s u : Side} (x : Local) (h : u ≠ s) :
    setSide L s x u = L u := by
  simp [setSide, h]

omit [Ops] in
theorem setSide_procs_of {L : Side → Local} {s : Side} {x : Local} (h : x.procs = (L s).procs)
    (u : Side) : (setSide L s x u).procs = (L u).procs := by
  by_cases hu : u = s
  · subst hu; rw [setSide_same]; exact h
  · rw [setSide_other _ _ hu]

omit [Ops] in
theorem setSide_asked_of {L : Side → Local} {s : Side} {x : Local} (h : x.asked = (L s).asked)
    (u : Side) : (setSide L s x u).asked = (L u).asked := by
  by_cases hu : u = s
  · subst hu; rw [setSide_same]; exact h
  · rw [setSide_other _ _ hu]

omit [Ops] in
theorem setSide_outPkts_of {L : Side → Local} {s : Side} {x : Local} (h : x.outPkts = (L s).outPkts)
    (u : Side) : (setSide L s x u).outPkts = (L u).outPkts := by
  by_cases hu : u = s
  · subst hu; rw [setSide_same]; exact h
  · rw [setSide_other _ _ hu]

omit [Ops] in
theorem setSide_names_of {L : Side → Local} {s : Side} {x : Local} (h : x.names = (L s).names)
    (u : Side) : (setSide L s x u).names = (L u).names := by
  by_cases hu : u = s
  · subst hu; rw [setSide_same]; exact h
  · rw [setSide_other _ _ hu]

omit [Ops] in
theorem Side.parity_inj {u s : Side} (h : u.parity = s.parity) : u = s := by
  cases u <;> cases s <;> first | rfl | cases h

omit [Ops] in
theorem Mix.free_some {m : Mix} {s : Side} {i g : Nat} (h : m.free s i = some g) :
    (m.places s)[i]? = some g := by
  unfold Mix.free at h
  split at h
  · next g' hg =>
    split at h
    · cases h
    · cases h; exact hg
  · cases h

/-- The walk's state `m`, the replay's configuration `R` and the two guests'
    states say the same. Each guest's processes are the replay's at that
    guest's places, but for a process whose crossing was taken and is not yet
    acknowledged: there the replay has already run the turn the guest keeps
    aside. Each crossing not acknowledged is one the guest has out, asked by
    the process at the place the walk has for it. -/
structure Agree (m : Mix) (R : MConfig) (L : Side → Local) : Prop where
  shaped : ∃ sh, Shaped m sh
  total : m.total = R.procs.length
  len : ∀ s, (m.places s).length = (L s).procs.length
  names : ∀ n ∈ R.names, ∃ s, n ∈ (L s).names
  outsLen : ∀ s, (m.outs s).length = (L s).outPkts.length
  live : ∀ (s : Side) (k : Nat) (c : Crossing), (m.outs s)[k]? = some c → c.state ≠ .acked →
    ∃ a ∈ (L s).asked, a.k = k ∧ (m.places s)[a.place]? = some c.asker
  same : ∀ (s : Side) (i g : Nat), (m.places s)[i]? = some g →
    (∀ a ∈ (L s).asked, a.place = i → ∀ c : Crossing, (m.outs s)[a.k]? = some c → c.state ≠ .taken) →
    R.procs[g]? = (L s).procs[i]?
  moved : ∀ (s : Side), ∀ a ∈ (L s).asked, ∀ c : Crossing, (m.outs s)[a.k]? = some c →
    c.state = .taken →
    ∃ q, (L s).procs[a.place]? = some q ∧ (m.places s)[a.place]? = some c.asker ∧
      R.procs[c.asker]? = some ⟨a.next, q.held⟩

section
variable {m : Mix} {R : MConfig} {L : Side → Local}

omit [Ops] in
theorem Agree.ne (ag : Agree m R L) {s u : Side} {i x g g' : Nat} (hi : (m.places s)[i]? = some g)
    (hx : (m.places u)[x]? = some g') (h : u ≠ s ∨ x ≠ i) : g' ≠ g := by
  obtain ⟨sh, hs⟩ := ag.shaped
  intro he
  subst he
  obtain ⟨rfl, rfl⟩ := hs.inj hx hi
  rcases h with h | h <;> exact h rfl

omit [Ops] in
theorem Agree.below (ag : Agree m R L) {s : Side} {i g : Nat} (hi : (m.places s)[i]? = some g) :
    g < R.procs.length := by
  obtain ⟨sh, hs⟩ := ag.shaped
  rw [← ag.total]
  exact hs.below g ((m.places_all g).mpr ⟨s, List.mem_of_getElem? hi⟩)

omit [Ops] in
/-- Only a guest's processes, names, crossings out and their packets matter. -/
theorem Agree.retarget (ag : Agree m R L) {L' : Side → Local}
    (h : ∀ u, (L' u).procs = (L u).procs ∧ (L' u).names = (L u).names ∧
      (L' u).asked = (L u).asked ∧ (L' u).outPkts = (L u).outPkts) : Agree m R L' where
  shaped := ag.shaped
  total := ag.total
  len := by intro s; rw [(h s).1]; exact ag.len s
  names := by intro n hn; obtain ⟨s, hs⟩ := ag.names n hn; exact ⟨s, by rw [(h s).2.1]; exact hs⟩
  outsLen := by intro s; rw [(h s).2.2.2]; exact ag.outsLen s
  live := by intro s k c hk hst; rw [(h s).2.2.1]; exact ag.live s k c hk hst
  same := by
    intro s i g hi hyp
    rw [(h s).1]
    rw [(h s).2.2.1] at hyp
    exact ag.same s i g hi hyp
  moved := by
    intro s a ha c hk hst
    rw [(h s).2.2.1] at ha
    rw [(h s).1]
    exact ag.moved s a ha c hk hst

omit [Ops] in
/-- A process that is not held is set, on its guest and in the replay. -/
theorem Agree.setProc (ag : Agree m R L) {s : Side} {i g : Nat} (q : Proc MValue MOutcome)
    (hi : (m.places s)[i]? = some g) (hfree : (L s).held i = false) :
    Agree m ⟨R.procs.set g q, R.names⟩ (setSide L s { L s with procs := (L s).procs.set i q }) := by
  have hgl := ag.below hi
  have hil : i < (L s).procs.length := by rw [← ag.len s]; exact lt_of_getElem? hi
  have hasked : ∀ u, (setSide L s { L s with procs := (L s).procs.set i q } u).asked = (L u).asked := by
    intro u; by_cases hu : u = s
    · subst hu; rw [setSide_same]
    · rw [setSide_other _ _ hu]
  refine ⟨ag.shaped, by simpa using ag.total, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    by_cases hu : u = s
    · subst hu; rw [setSide_same]; simp [ag.len u]
    · rw [setSide_other _ _ hu]; exact ag.len u
  · intro n hn
    obtain ⟨u, hu⟩ := ag.names n hn
    refine ⟨u, ?_⟩
    by_cases h : u = s
    · subst h; rw [setSide_same]; exact hu
    · rw [setSide_other _ _ h]; exact hu
  · intro u
    by_cases hu : u = s
    · subst hu; rw [setSide_same]; exact ag.outsLen u
    · rw [setSide_other _ _ hu]; exact ag.outsLen u
  · intro u k c hk hst
    rw [hasked]
    exact ag.live u k c hk hst
  · intro u x g' hx hyp
    rw [hasked] at hyp
    by_cases h : u = s
    · subst h
      rw [setSide_same]
      by_cases hxi : x = i
      · subst hxi
        rw [hi] at hx; cases hx
        simp only
        rw [List.getElem?_set_self hgl, List.getElem?_set_self hil]
      · have hne := ag.ne hi hx (.inr hxi)
        simp only
        rw [List.getElem?_set_ne (Ne.symm hne), List.getElem?_set_ne (Ne.symm hxi)]
        exact ag.same u x g' hx hyp
    · have hne := ag.ne hi hx (.inl h)
      rw [setSide_other _ _ h]
      simp only
      rw [List.getElem?_set_ne (Ne.symm hne)]
      exact ag.same u x g' hx hyp
  · intro u a ha c hk hst
    rw [hasked] at ha
    obtain ⟨q0, hq0, hpl, hR⟩ := ag.moved u a ha c hk hst
    have hne : c.asker ≠ g := by
      refine ag.ne hi hpl ?_
      by_cases h : u = s
      · subst h; exact .inr (Local.not_held hfree a ha)
      · exact .inl h
    refine ⟨q0, ?_, hpl, ?_⟩
    · by_cases h : u = s
      · subst h
        rw [setSide_same]
        simp only
        rw [List.getElem?_set_ne (Ne.symm (Local.not_held hfree a ha))]
        exact hq0
      · rw [setSide_other _ _ h]; exact hq0
    · simp only
      rw [List.getElem?_set_ne (Ne.symm hne)]
      exact hR

omit [Ops] in
/-- A name is made, on its guest and in the replay. -/
theorem Agree.addName (ag : Agree m R L) (s : Side) (n : Nat) :
    Agree m ⟨R.procs, n :: R.names⟩ (setSide L s { L s with names := n :: (L s).names }) := by
  have h : ∀ u, (setSide L s { L s with names := n :: (L s).names } u).procs = (L u).procs ∧
      (setSide L s { L s with names := n :: (L s).names } u).asked = (L u).asked ∧
      (setSide L s { L s with names := n :: (L s).names } u).outPkts = (L u).outPkts := by
    intro u; by_cases hu : u = s
    · subst hu; rw [setSide_same]; exact ⟨rfl, rfl, rfl⟩
    · rw [setSide_other _ _ hu]; exact ⟨rfl, rfl, rfl⟩
  refine ⟨ag.shaped, ag.total, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u; rw [(h u).1]; exact ag.len u
  · intro n' hn'
    rcases List.mem_cons.mp hn' with rfl | hn'
    · exact ⟨s, by rw [setSide_same]; exact List.mem_cons_self⟩
    · obtain ⟨u, hu⟩ := ag.names n' hn'
      refine ⟨u, ?_⟩
      by_cases h' : u = s
      · subst h'; rw [setSide_same]; exact List.mem_cons_of_mem _ hu
      · rw [setSide_other _ _ h']; exact hu
  · intro u; rw [(h u).2.2]; exact ag.outsLen u
  · intro u k c hk hst; rw [(h u).2.1]; exact ag.live u k c hk hst
  · intro u i g hi hyp
    rw [(h u).1]
    rw [(h u).2.1] at hyp
    exact ag.same u i g hi hyp
  · intro u a ha c hk hst
    rw [(h u).2.1] at ha
    rw [(h u).1]
    exact ag.moved u a ha c hk hst

omit [Ops] in
/-- A process is added, on its guest and in the replay. -/
theorem Agree.addProc (ag : Agree m R L) (s : Side) (q : Proc MValue MOutcome) :
    Agree (m.grow s) ⟨R.procs ++ [q], R.names⟩
      (setSide L s { L s with procs := (L s).procs ++ [q] }) := by
  have hasked : ∀ u, (setSide L s { L s with procs := (L s).procs ++ [q] } u).asked = (L u).asked := by
    intro u; by_cases hu : u = s
    · subst hu; rw [setSide_same]
    · rw [setSide_other _ _ hu]
  have hplaces : ∀ (u : Side) (i g : Nat), (m.places u)[i]? = some g →
      ((m.grow s).places u)[i]? = some g := by
    intro u i g hi
    by_cases hu : u = s
    · subst hu
      rw [Mix.places_grow_same, List.getElem?_append_left (lt_of_getElem? hi)]; exact hi
    · rw [Mix.places_grow_other _ hu]; exact hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨sh, hs⟩ := ag.shaped; exact ⟨_, hs.grow s⟩
  · rw [Mix.total_grow]; simp [ag.total]
  · intro u
    by_cases hu : u = s
    · subst hu; rw [setSide_same, Mix.places_grow_same]; simp [ag.len u]
    · rw [setSide_other _ _ hu, Mix.places_grow_other _ hu]; exact ag.len u
  · intro n hn
    obtain ⟨u, hu⟩ := ag.names n hn
    refine ⟨u, ?_⟩
    by_cases h : u = s
    · subst h; rw [setSide_same]; exact hu
    · rw [setSide_other _ _ h]; exact hu
  · intro u
    rw [Mix.outs_grow]
    by_cases hu : u = s
    · subst hu; rw [setSide_same]; exact ag.outsLen u
    · rw [setSide_other _ _ hu]; exact ag.outsLen u
  · intro u k c hk hst
    rw [Mix.outs_grow] at hk
    rw [hasked]
    obtain ⟨a, ha, hak, hpl⟩ := ag.live u k c hk hst
    exact ⟨a, ha, hak, hplaces u _ _ hpl⟩
  · intro u x g' hx hyp
    rw [hasked] at hyp
    simp only [Mix.outs_grow] at hyp
    by_cases h : u = s
    · subst h
      rw [setSide_same]
      rw [Mix.places_grow_same] at hx
      by_cases hlt : x < (m.places u).length
      · rw [List.getElem?_append_left hlt] at hx
        simp only
        rw [List.getElem?_append_left (ag.below hx),
          List.getElem?_append_left (by rw [← ag.len u]; exact hlt)]
        exact ag.same u x g' hx hyp
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hx
        have hz : x - (m.places u).length = 0 := by
          rcases Nat.eq_zero_or_pos (x - (m.places u).length) with hz | hz
          · exact hz
          · rw [List.getElem?_eq_none (by simp only [List.length_singleton]; exact hz)] at hx; cases hx
        rw [hz] at hx
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        have hxe : x = (L u).procs.length := by rw [← ag.len u]; omega
        subst hxe
        simp [ag.total]
    · rw [setSide_other _ _ h]
      rw [Mix.places_grow_other _ h] at hx
      simp only
      rw [List.getElem?_append_left (ag.below hx)]
      exact ag.same u x g' hx hyp
  · intro u a ha c hk hst
    rw [hasked] at ha
    rw [Mix.outs_grow] at hk
    obtain ⟨q0, hq0, hpl, hR⟩ := ag.moved u a ha c hk hst
    refine ⟨q0, ?_, hplaces u _ _ hpl, ?_⟩
    · by_cases h : u = s
      · subst h
        rw [setSide_same]
        simp only
        rw [List.getElem?_append_left (lt_of_getElem? hq0)]; exact hq0
      · rw [setSide_other _ _ h]; exact hq0
    · simp only
      rw [List.getElem?_append_left (lt_of_getElem? hR)]; exact hR

omit [Ops] in
/-- A request is put out. -/
theorem Agree.out (ag : Agree m R L) {s : Side} {i g : Nat} (a : Ask) (pkt : Data)
    (hi : (m.places s)[i]? = some g) (hk : a.k = (m.outs s).length) (hp : a.place = i) :
    Agree (m.setOuts s (m.outs s ++ [⟨g, .offered⟩])) R
      (setSide L s { L s with asked := a :: (L s).asked, outPkts := (L s).outPkts ++ [pkt] }) := by
  have hlast : ∀ {k : Nat} {c : Crossing}, (m.outs s ++ [(⟨g, .offered⟩ : Crossing)])[k]? = some c →
      (m.outs s)[k]? = some c ∨ (k = (m.outs s).length ∧ c = ⟨g, .offered⟩) := by
    intro k c hk'
    by_cases hlt : k < (m.outs s).length
    · rw [List.getElem?_append_left hlt] at hk'; exact .inl hk'
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hk'
      have hz : k - (m.outs s).length = 0 := by
        rcases Nat.eq_zero_or_pos (k - (m.outs s).length) with hz | hz
        · exact hz
        · rw [List.getElem?_eq_none (by simp only [List.length_singleton]; exact hz)] at hk'; cases hk'
      rw [hz] at hk'
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk'
      exact .inr ⟨by omega, hk'.symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨sh, hs⟩ := ag.shaped; exact ⟨_, hs.out hi⟩
  · rw [Mix.total_setOuts]; exact ag.total
  · intro u; rw [Mix.places_setOuts, setSide_procs_of (by rfl)]; exact ag.len u
  · intro n hn
    obtain ⟨u, hu⟩ := ag.names n hn
    refine ⟨u, ?_⟩
    by_cases h : u = s
    · subst h; rw [setSide_same]; exact hu
    · rw [setSide_other _ _ h]; exact hu
  · intro u
    by_cases hu : u = s
    · subst hu; rw [setSide_same, Mix.outs_setOuts_same]; simp [ag.outsLen u]
    · rw [setSide_other _ _ hu, Mix.outs_setOuts_other _ _ hu]; exact ag.outsLen u
  · intro u k c hk' hst
    rw [Mix.places_setOuts]
    by_cases hu : u = s
    · subst hu
      rw [setSide_same]
      rw [Mix.outs_setOuts_same] at hk'
      rcases hlast hk' with hold | ⟨hkl, rfl⟩
      · obtain ⟨a', ha', hak', hpl⟩ := ag.live u k c hold hst
        exact ⟨a', List.mem_cons_of_mem _ ha', hak', hpl⟩
      · exact ⟨a, List.mem_cons_self, by rw [hk, hkl], by rw [hp]; exact hi⟩
    · rw [setSide_other _ _ hu]
      rw [Mix.outs_setOuts_other _ _ hu] at hk'
      exact ag.live u k c hk' hst
  · intro u x g' hx hyp
    rw [Mix.places_setOuts] at hx
    rw [setSide_procs_of (by rfl)]
    refine ag.same u x g' hx ?_
    intro a' ha' hpl c hc
    by_cases hu : u = s
    · subst hu
      rw [setSide_same] at hyp
      refine hyp a' (List.mem_cons_of_mem _ ha') hpl c ?_
      rw [Mix.outs_setOuts_same, List.getElem?_append_left (lt_of_getElem? hc)]; exact hc
    · rw [setSide_other _ _ hu] at hyp
      refine hyp a' ha' hpl c ?_
      rw [Mix.outs_setOuts_other _ _ hu]; exact hc
  · intro u a' ha' c hk' hst
    rw [Mix.places_setOuts, setSide_procs_of (by rfl)]
    by_cases hu : u = s
    · subst hu
      rw [setSide_same] at ha'
      rw [Mix.outs_setOuts_same] at hk'
      rcases hlast hk' with hold | ⟨_, rfl⟩
      · rcases List.mem_cons.mp ha' with rfl | ha'
        · rw [hk] at hold
          rw [List.getElem?_eq_none (Nat.le_refl _)] at hold; cases hold
        · exact ag.moved u a' ha' c hold hst
      · cases hst
    · rw [setSide_other _ _ hu] at ha'
      rw [Mix.outs_setOuts_other _ _ hu] at hk'
      exact ag.moved u a' ha' c hk' hst

/-- A crossing is taken: the replay runs the asker's kept turn; its guest does
    not yet know. -/
theorem Agree.take {cells budget : Nat} (ag : Agree m R L) {u : Side}
    (ok : Local.Ok cells budget u (L u)) {k g : Nat} {a : Ask} {q : Proc MValue MOutcome}
    (hk : (m.outs u)[k]? = some ⟨g, .offered⟩) (ha : a ∈ (L u).asked) (hak : a.k = k)
    (hq : (L u).procs[a.place]? = some q) (hpl : (m.places u)[a.place]? = some g) :
    Agree (m.setOuts u ((m.outs u).set k ⟨g, .taken⟩)) ⟨R.procs.set g ⟨a.next, q.held⟩, R.names⟩ L := by
  have hgl := ag.below hpl
  have hklt := lt_of_getElem? hk
  refine ⟨?_, ?_, ?_, ag.names, ?_, ?_, ?_, ?_⟩
  · obtain ⟨sh, hs⟩ := ag.shaped
    obtain ⟨i, _, _, hs'⟩ := hs.move hk .taken
    exact ⟨_, hs'⟩
  · rw [Mix.total_setOuts]; simpa using ag.total
  · intro v; rw [Mix.places_setOuts]; exact ag.len v
  · intro v
    by_cases hv : v = u
    · subst hv; rw [Mix.outs_setOuts_same, List.length_set]; exact ag.outsLen v
    · rw [Mix.outs_setOuts_other _ _ hv]; exact ag.outsLen v
  · intro v k' c hk' hst
    rw [Mix.places_setOuts]
    by_cases hv : v = u
    · subst hv
      rw [Mix.outs_setOuts_same] at hk'
      by_cases hkk : k = k'
      · subst hkk
        rw [List.getElem?_set_self hklt] at hk'
        cases hk'
        exact ⟨a, ha, hak, hpl⟩
      · rw [List.getElem?_set_ne hkk] at hk'
        exact ag.live v k' c hk' hst
    · rw [Mix.outs_setOuts_other _ _ hv] at hk'
      exact ag.live v k' c hk' hst
  · intro v x g' hx hyp
    rw [Mix.places_setOuts] at hx
    by_cases hv : v = u
    · subst hv
      rw [Mix.outs_setOuts_same] at hyp
      by_cases hxa : x = a.place
      · subst hxa
        have := hyp a ha rfl ⟨g, .taken⟩ (by rw [hak, List.getElem?_set_self hklt])
        exact absurd rfl this
      · have hne := ag.ne hpl hx (.inr hxa)
        simp only
        rw [List.getElem?_set_ne (Ne.symm hne)]
        refine ag.same v x g' hx ?_
        intro a' ha' hpl' c hc
        have hkne : k ≠ a'.k := by
          intro he
          have := ok.uniqK a' ha' a ha (by rw [hak, he])
          rw [this] at hpl'
          exact hxa hpl'.symm
        exact hyp a' ha' hpl' c (by rw [List.getElem?_set_ne hkne]; exact hc)
    · have hne := ag.ne hpl hx (.inl hv)
      simp only
      rw [List.getElem?_set_ne (Ne.symm hne)]
      refine ag.same v x g' hx ?_
      intro a' ha' hpl' c hc
      exact hyp a' ha' hpl' c (by rw [Mix.outs_setOuts_other _ _ hv]; exact hc)
  · intro v a' ha' c hk' hst
    rw [Mix.places_setOuts]
    by_cases hv : v = u
    · subst hv
      rw [Mix.outs_setOuts_same] at hk'
      by_cases hkk : k = a'.k
      · have hae : a' = a := ok.uniqK a' ha' a ha (by rw [hak, hkk])
        subst hae
        rw [← hkk, List.getElem?_set_self hklt] at hk'
        cases hk'
        exact ⟨q, hq, hpl, by simp only; rw [List.getElem?_set_self hgl]⟩
      · rw [List.getElem?_set_ne hkk] at hk'
        obtain ⟨q0, hq0, hpl', hR⟩ := ag.moved v a' ha' c hk' hst
        have hpne : a'.place ≠ a.place := by
          intro he
          have := ok.uniqP a' ha' a ha he
          rw [this, hak] at hkk
          exact hkk rfl
        have hne := ag.ne hpl hpl' (.inr hpne)
        exact ⟨q0, hq0, hpl', by simp only; rw [List.getElem?_set_ne (Ne.symm hne)]; exact hR⟩
    · rw [Mix.outs_setOuts_other _ _ hv] at hk'
      obtain ⟨q0, hq0, hpl', hR⟩ := ag.moved v a' ha' c hk' hst
      have hne := ag.ne hpl hpl' (.inl hv)
      exact ⟨q0, hq0, hpl', by simp only; rw [List.getElem?_set_ne (Ne.symm hne)]; exact hR⟩

/-- A crossing is acknowledged: its guest's process becomes what the replay
    already has. -/
theorem Agree.ack {cells budget : Nat} (ag : Agree m R L) {s : Side}
    (ok : Local.Ok cells budget s (L s)) {k g : Nat} {a : Ask} {q : Proc MValue MOutcome}
    (hk : (m.outs s)[k]? = some ⟨g, .taken⟩) (ha : a ∈ (L s).asked) (hak : a.k = k)
    (hq : (L s).procs[a.place]? = some q) :
    Agree (m.setOuts s ((m.outs s).set k ⟨g, .acked⟩)) R
      (setSide L s { L s with procs := (L s).procs.set a.place ⟨a.next, q.held⟩,
                              asked := (L s).asked.filter (·.k != k) }) := by
  have hklt := lt_of_getElem? hk
  obtain ⟨q0, hq0, hpl, hR⟩ := ag.moved s a ha ⟨g, .taken⟩ (by rw [hak]; exact hk) rfl
  rw [hq] at hq0
  cases hq0
  have hil := lt_of_getElem? hq
  have hfil : ∀ x, x ∈ (L s).asked.filter (·.k != k) ↔ x ∈ (L s).asked ∧ x.k ≠ k := by
    intro x; rw [List.mem_filter]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨sh, hs⟩ := ag.shaped
    obtain ⟨i, _, _, hs'⟩ := hs.move hk .acked
    exact ⟨_, hs'⟩
  · rw [Mix.total_setOuts]; exact ag.total
  · intro u
    rw [Mix.places_setOuts]
    by_cases hu : u = s
    · subst hu; rw [setSide_same]; simp [ag.len u]
    · rw [setSide_other _ _ hu]; exact ag.len u
  · intro n hn
    obtain ⟨u, hu⟩ := ag.names n hn
    refine ⟨u, ?_⟩
    by_cases h : u = s
    · subst h; rw [setSide_same]; exact hu
    · rw [setSide_other _ _ h]; exact hu
  · intro u
    rw [setSide_outPkts_of (by rfl)]
    by_cases hu : u = s
    · subst hu; rw [Mix.outs_setOuts_same, List.length_set]; exact ag.outsLen u
    · rw [Mix.outs_setOuts_other _ _ hu]; exact ag.outsLen u
  · intro u k' c hk' hst
    rw [Mix.places_setOuts]
    by_cases hu : u = s
    · subst hu
      rw [setSide_same]
      rw [Mix.outs_setOuts_same] at hk'
      by_cases hkk : k = k'
      · subst hkk
        rw [List.getElem?_set_self hklt] at hk'
        cases hk'
        exact absurd rfl hst
      · rw [List.getElem?_set_ne hkk] at hk'
        obtain ⟨a', ha', hak', hpl'⟩ := ag.live u k' c hk' hst
        exact ⟨a', (hfil a').mpr ⟨ha', by rw [hak']; exact Ne.symm hkk⟩, hak', hpl'⟩
    · rw [setSide_other _ _ hu]
      rw [Mix.outs_setOuts_other _ _ hu] at hk'
      exact ag.live u k' c hk' hst
  · intro u x g' hx hyp
    rw [Mix.places_setOuts] at hx
    by_cases hu : u = s
    · subst hu
      rw [setSide_same] at hyp ⊢
      rw [Mix.outs_setOuts_same] at hyp
      by_cases hxa : x = a.place
      · subst hxa
        rw [hpl] at hx
        cases hx
        simp only
        rw [List.getElem?_set_self hil]
        exact hR
      · simp only
        rw [List.getElem?_set_ne (Ne.symm hxa)]
        refine ag.same u x g' hx ?_
        intro a' ha' hpl' c hc
        have hkne : a'.k ≠ k := by
          intro he
          have := ok.uniqK a' ha' a ha (by rw [hak, he])
          rw [this] at hpl'
          exact hxa hpl'.symm
        exact hyp a' ((hfil a').mpr ⟨ha', hkne⟩) hpl' c (by
          rw [List.getElem?_set_ne (Ne.symm hkne)]; exact hc)
    · rw [setSide_other _ _ hu] at hyp ⊢
      refine ag.same u x g' hx ?_
      intro a' ha' hpl' c hc
      exact hyp a' ha' hpl' c (by rw [Mix.outs_setOuts_other _ _ hu]; exact hc)
  · intro u a' ha' c hk' hst
    rw [Mix.places_setOuts]
    by_cases hu : u = s
    · subst hu
      rw [setSide_same] at ha' ⊢
      rw [Mix.outs_setOuts_same] at hk'
      obtain ⟨ha', hkne⟩ := (hfil a').mp ha'
      rw [List.getElem?_set_ne (Ne.symm hkne)] at hk'
      obtain ⟨q0, hq0, hpl', hR'⟩ := ag.moved u a' ha' c hk' hst
      have hpne : a'.place ≠ a.place := by
        intro he
        have := ok.uniqP a' ha' a ha he
        rw [this, hak] at hkne
        exact hkne rfl
      exact ⟨q0, by simp only; rw [List.getElem?_set_ne (Ne.symm hpne)]; exact hq0, hpl', hR'⟩
    · rw [setSide_other _ _ hu] at ha' ⊢
      rw [Mix.outs_setOuts_other _ _ hu] at hk'
      exact ag.moved u a' ha' c hk' hst

end

/-! One entry, placed by the walk and run by the replay. -/

omit [Ops] in
theorem receivesOn_inv {name : Nat} {c : MValue} {p : Data} {held : List Nat}
    (h : receivesOn name ⟨.waiting c p, held⟩ = true) :
    classify p = .receive name ∧ held.contains name = true := by
  simp only [receivesOn] at h
  split at h
  · next ch' hq =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hh⟩ := h
    exact ⟨hq, hh⟩
  · cases h

theorem SideRun.cons_inv {cells budget : Nat} {s : Side} {L F : Local} {r : Note × Data}
    {rs : List (Note × Data)} (h : SideRun cells budget s L (r :: rs) F) :
    ∃ M, SideStep cells budget s L r M ∧ SideRun cells budget s M rs F := by
  cases h with
  | cons h rest => exact ⟨_, h, rest⟩

theorem SideRun.nil_inv {cells budget : Nat} {s : Side} {L F : Local}
    (h : SideRun cells budget s L [] F) : F = L := by
  cases h; rfl

/-- The walk places an entry of guest `s` that its guest's log allows, and the
    crossing it takes, if any, was taken as the packet made for it. Then the
    replay runs the entry's events, and the walk, the replay and the guests
    still say the same. -/
theorem Agree.step {cells budget : Nat} {m m' : Mix} {R : MConfig} {L : Side → Local} {s : Side}
    {r : Note × Data} {M : Local} {evs : List Event}
    (ag : Agree m R L) (ok : ∀ u, Local.Ok cells budget u (L u))
    (hp : m.place s r.1 = some (m', evs)) (hl : SideStep cells budget s (L s) r M)
    (link : ∀ k, r.1.taking = some k → ∀ pkt, (L s.other).outPkts[k]? = some pkt → pkt = r.2) :
    ∃ R', schedIn cells budget R evs = (evs, R', .ran) ∧ Agree m' R' (setSide L s M) := by
  generalize hLs : L s = Ls at hl
  cases hl with
  | @did ev cfg d h free inside par =>
    subst hLs
    cases ev with
    | fresh i n =>
      obtain ⟨c, p, held, st, hi, hq, hn, ht, rfl⟩ := stepIn_fresh_inv h
      simp only [Mix.place] at hp
      cases hf : m.free s i with
      | none => simp [hf] at hp
      | some g =>
        simp [hf] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have hpl := Mix.free_some hf
        have hfree : (L s).held i = false := free i (by simp [Event.places])
        have hR : R.procs[g]? = some ⟨.waiting c p, held⟩ := by
          rw [ag.same s i g hpl (fun a ha he => absurd he (Local.not_held hfree a ha))]; exact hi
        have hnR : R.names.contains n = false := by
          cases hc : R.names.contains n with
          | false => rfl
          | true =>
            obtain ⟨u, hu⟩ := ag.names n (by simpa using hc)
            have hpu := (ok u).parity n hu
            have := Side.parity_inj (hpu.symm.trans (par i n rfl))
            subst this
            have hn' : n ∉ (L u).names := by simpa using hn
            exact absurd hu hn'
        refine ⟨_, schedIn_one (stepIn_fresh_ok hR hq hnR ht), ?_⟩
        refine ((ag.setProc ⟨st, n :: held⟩ hpl hfree).addName s n).retarget ?_
        intro u
        by_cases hu : u = s
        · subst hu; simp [setSide]
        · simp [setSide, hu]
    | spawn i =>
      obtain ⟨c, p, held, t, arg, w, child, st, hi, hq, hw, hc, ht, rfl⟩ := stepIn_spawn_inv h
      simp only [Mix.place] at hp
      cases hf : m.free s i with
      | none => simp [hf] at hp
      | some g =>
        simp [hf] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have hpl := Mix.free_some hf
        have hfree : (L s).held i = false := free i (by simp [Event.places])
        have hR : R.procs[g]? = some ⟨.waiting c p, held⟩ := by
          rw [ag.same s i g hpl (fun a ha he => absurd he (Local.not_held hfree a ha))]; exact hi
        refine ⟨_, schedIn_one (stepIn_spawn_ok hR hq hw hc ht), ?_⟩
        refine ((ag.setProc ⟨st, held⟩ hpl hfree).addProc s ⟨child, grant held arg⟩).retarget ?_
        intro u
        by_cases hu : u = s
        · subst hu; simp [setSide]
        · simp [setSide, hu]
    | comm i j =>
      obtain ⟨c, p, held, c', p', held', ch, v, st, st', hi, hj, hq, hq', hh, hh', ht, ht', rfl⟩ :=
        stepIn_comm_inv h
      simp only [Mix.place] at hp
      split at hp
      · next g g₂ hg hg₂ =>
        cases hp
        have hpli := Mix.free_some hg
        have hplj := Mix.free_some hg₂
        have hfi : (L s).held i = false := free i (by simp [Event.places])
        have hfj : (L s).held j = false := free j (by simp [Event.places])
        have hRi : R.procs[g]? = some ⟨.waiting c p, held⟩ := by
          rw [ag.same s i g hpli (fun a ha he => absurd he (Local.not_held hfi a ha))]; exact hi
        have hRj : R.procs[g₂]? = some ⟨.waiting c' p', held'⟩ := by
          rw [ag.same s j g₂ hplj (fun a ha he => absurd he (Local.not_held hfj a ha))]; exact hj
        refine ⟨_, schedIn_one (stepIn_comm_ok hRi hRj hq hq' hh hh' ht ht'), ?_⟩
        have ag₁ := ag.setProc ⟨st, held⟩ hpli hfi
        have hfj' : (setSide L s { L s with procs := (L s).procs.set i ⟨st, held⟩ } s).held j = false := by
          rw [setSide_same]; exact hfj
        refine (ag₁.setProc ⟨st', gain held' (grant held v)⟩ hplj hfj').retarget ?_
        intro u
        by_cases hu : u = s
        · subst hu; simp [setSide]
        · simp [setSide, hu]
      · cases hp
    | answer i x => simp [Event.isAnswer] at inside
  | @out i k c p held pkt next d hi free hk hw hpk ht =>
    subst hLs
    simp only [Mix.place] at hp
    split at hp
    · next g hg =>
      split at hp
      · next hkk =>
        cases hp
        refine ⟨R, rfl, ?_⟩
        refine (ag.out ⟨i, k, next⟩ pkt (Mix.free_some hg) hkk rfl).retarget ?_
        intro u
        by_cases hu : u = s
        · subst hu; simp [setSide]
        · simp [setSide, hu]
      · cases hp
    · cases hp
  | @spawnIn k prog start held t hs w child hu hn hr hc =>
    subst hLs
    simp only [Mix.place] at hp
    split at hp
    · next g hg =>
      cases hp
      obtain ⟨a, ha, hak, hpl⟩ := ag.live s.other k _ hg (by simp)
      obtain ⟨c, p, held', pkt, hproc, hw, hpk, ho, ht⟩ := (ok s.other).asked a ha
      rw [hak] at ho hpk
      have hpe := link k rfl pkt ho
      subst hpe
      obtain ⟨t', hq, hu', rfl⟩ := packetOf_start hpk
      rw [hu] at hu'
      cases hu'
      rw [packetNats_map] at hn
      cases hn
      have hsame := ag.same s.other a.place g hpl (by
        intro a' ha' he c' hc'
        have := (ok s.other).uniqP a' ha' a ha he
        subst this
        rw [hak, hg] at hc'
        cases hc'
        simp)
      have hR : R.procs[g]? = some ⟨.waiting c p, held'⟩ := by rw [hsame]; exact hproc
      refine ⟨_, schedIn_one (stepIn_spawn_ok hR hq hr hc ht), ?_⟩
      refine ((ag.take (ok s.other) hg ha hak hproc hpl).addProc s ⟨child, grant held' start⟩).retarget ?_
      intro u
      by_cases hu : u = s
      · subst hu; simp [setSide]
      · simp [setSide, hu]
    · cases hp
  | @sendIn k j name message held hs c p held' st hn hj free hrecv ht =>
    subst hLs
    simp only [Mix.place] at hp
    split at hp
    · next g g₂ hg hf =>
      cases hp
      obtain ⟨a, ha, hak, hpl⟩ := ag.live s.other k _ hg (by simp)
      obtain ⟨c₀, p₀, held₀, pkt, hproc, hw, hpk, ho, ht₀⟩ := (ok s.other).asked a ha
      rw [hak] at ho hpk
      have hpe := link k rfl pkt ho
      subst hpe
      obtain ⟨hq, rfl⟩ := packetOf_send hpk
      rw [packetNats_map] at hn
      cases hn
      have hh₀ : held₀.contains name = true := by simpa [wantsOut, hq] using hw
      obtain ⟨hq', hh'⟩ := receivesOn_inv hrecv
      have hplj := Mix.free_some hf
      have hsame := ag.same s.other a.place g hpl (by
        intro a' ha' he c' hc'
        have := (ok s.other).uniqP a' ha' a ha he
        subst this
        rw [hak, hg] at hc'
        cases hc'
        simp)
      have hRg : R.procs[g]? = some ⟨.waiting c₀ p₀, held₀⟩ := by rw [hsame]; exact hproc
      have hRj : R.procs[g₂]? = some ⟨.waiting c p, held'⟩ := by
        rw [ag.same s j g₂ hplj (fun a' ha' he => absurd he (Local.not_held free a' ha'))]; exact hj
      refine ⟨_, schedIn_one (stepIn_comm_ok hRg hRj hq hq' hh₀ hh' ht₀ ht), ?_⟩
      have ag₁ := ag.take (ok s.other) hg ha hak hproc hpl
      refine (ag₁.setProc ⟨st, gain held' (grant held₀ message)⟩
        (by rw [Mix.places_setOuts]; exact hplj) free).retarget ?_
      intro u
      by_cases hu : u = s
      · subst hu; simp [setSide]
      · simp [setSide, hu]
    · cases hp
  | @ack k i a q d ha hk hpa hq =>
    subst hLs
    simp only [Mix.place] at hp
    split at hp
    · next g g' hg hg' =>
      split at hp
      · next heq =>
        cases hp
        subst hpa
        subst hk
        refine ⟨R, rfl, ?_⟩
        refine (ag.ack (ok s) hg ha rfl hq).retarget ?_
        intro u
        by_cases hu : u = s
        · subst hu; simp [setSide]
        · simp [setSide, hu]
      · cases hp
    · cases hp
  | held =>
    subst hLs
    simp only [Mix.place] at hp
    cases hp
    refine ⟨R, rfl, ag.retarget ?_⟩
    intro u
    by_cases hu : u = s
    · subst hu; simp [setSide]
    · simp [setSide, hu]
  | full =>
    subst hLs
    simp only [Mix.place] at hp
    cases hp
    refine ⟨R, rfl, ag.retarget ?_⟩
    intro u
    by_cases hu : u = s
    · subst hu; simp [setSide]
    · simp [setSide, hu]

omit [Ops] in
theorem Walk.settled {m last : Mix} {a b : List Note} {tr : List (Side × Note)} {evs : List Event}
    (h : Walk m a b tr evs last) : last.settled = true := by
  induction h with
  | done h => exact h
  | left _ _ ih => exact ih
  | right _ _ ih => exact ih

/-- Any walk the table allows over two logs that are each what a guest's log
    allows, with every crossing taken as the packet made for it, replays to
    the end, and the walk, the replay and the two guests' last states say the
    same. -/
theorem Walk.replay {cells budget : Nat} {m last : Mix} {a b : List Note} {tr : List (Side × Note)}
    {evs : List Event} (hw : Walk m a b tr evs last) :
    ∀ {R : MConfig} {L : Side → Local} {FA FB : Local} {ra rb : List (Note × Data)},
      ra.map (·.1) = a → rb.map (·.1) = b →
      SideRun cells budget .a (L .a) ra FA → SideRun cells budget .b (L .b) rb FB →
      (∀ r ∈ ra, ∀ k, r.1.taking = some k → FB.outPkts[k]? = some r.2) →
      (∀ r ∈ rb, ∀ k, r.1.taking = some k → FA.outPkts[k]? = some r.2) →
      Agree m R L → (∀ u, Local.Ok cells budget u (L u)) →
      ∃ R', schedIn cells budget R evs = (evs, R', .ran) ∧
        Agree last R' (fun u => match u with | .a => FA | .b => FB) := by
  induction hw with
  | done hset =>
    intro R L FA FB ra rb ha hb runA runB _ _ ag _
    cases ra with
    | cons r ra' => simp at ha
    | nil =>
      cases rb with
      | cons r rb' => simp at hb
      | nil =>
        have h₁ := runA.nil_inv
        have h₂ := runB.nil_inv
        subst h₁
        subst h₂
        exact ⟨R, rfl, ag.retarget (by intro u; cases u <;> exact ⟨rfl, rfl, rfl, rfl⟩)⟩
  | @left m m' x xs ys tr evs evs' last hp rest ih =>
    intro R L FA FB ra rb ha hb runA runB linkA linkB ag ok
    cases ra with
    | nil => simp at ha
    | cons r ra' =>
      simp only [List.map_cons, List.cons.injEq] at ha
      obtain ⟨hx, hxs⟩ := ha
      obtain ⟨M, hstep, hrest⟩ := runA.cons_inv
      subst hx
      obtain ⟨R₁, hs₁, ag₁⟩ := ag.step ok hp hstep (by
        intro k hk pkt hpkt
        have h₁ := runB.outPkts hpkt
        have h₂ := linkA r List.mem_cons_self k hk
        rw [h₁] at h₂
        exact Option.some.inj h₂)
      have ok₁ : ∀ u, Local.Ok cells budget u (setSide L .a M u) := by
        intro u
        cases u
        · rw [setSide_same]; exact hstep.ok (ok .a)
        · rw [setSide_other _ _ (by decide)]; exact ok .b
      obtain ⟨R₂, hs₂, ag₂⟩ := ih hxs hb (by rw [setSide_same]; exact hrest)
        (by rw [setSide_other _ _ (by decide)]; exact runB)
        (fun r' hr' => linkA r' (List.mem_cons_of_mem _ hr')) linkB ag₁ ok₁
      refine ⟨R₂, ?_, ag₂⟩
      rw [schedIn_append cells budget R R₁ evs evs' hs₁, hs₂]
  | @right m m' y xs ys tr evs evs' last hp rest ih =>
    intro R L FA FB ra rb ha hb runA runB linkA linkB ag ok
    cases rb with
    | nil => simp at hb
    | cons r rb' =>
      simp only [List.map_cons, List.cons.injEq] at hb
      obtain ⟨hy, hys⟩ := hb
      obtain ⟨M, hstep, hrest⟩ := runB.cons_inv
      subst hy
      obtain ⟨R₁, hs₁, ag₁⟩ := ag.step ok hp hstep (by
        intro k hk pkt hpkt
        have h₁ := runA.outPkts hpkt
        have h₂ := linkB r List.mem_cons_self k hk
        rw [h₁] at h₂
        exact Option.some.inj h₂)
      have ok₁ : ∀ u, Local.Ok cells budget u (setSide L .b M u) := by
        intro u
        cases u
        · rw [setSide_other _ _ (by decide)]; exact ok .a
        · rw [setSide_same]; exact hstep.ok (ok .b)
      obtain ⟨R₂, hs₂, ag₂⟩ := ih ha hys
        (by rw [setSide_other _ _ (by decide)]; exact runA) (by rw [setSide_same]; exact hrest)
        linkA (fun r' hr' => linkB r' (List.mem_cons_of_mem _ hr')) ag₁ ok₁
      refine ⟨R₂, ?_, ag₂⟩
      rw [schedIn_append cells budget R R₁ evs evs' hs₁, hs₂]

/-! From the first state to the last. -/

omit [Ops] in
theorem filterMap_places {α : Type} (R : List α) : ∀ (l : List Nat) (p : List α),
    l.length = p.length → (∀ (i g : Nat), l[i]? = some g → R[g]? = p[i]?) →
    l.filterMap (R[·]?) = p := by
  intro l
  induction l with
  | nil => intro p hl _; cases p with
    | nil => rfl
    | cons q p => simp at hl
  | cons g l ih =>
    intro p hl h
    cases p with
    | nil => simp at hl
    | cons q p =>
      have h0 : R[g]? = some q := by simpa using h 0 g (by simp)
      rw [List.filterMap_cons, h0]
      simp only [List.cons.injEq, true_and]
      exact ih p (by simpa using hl) (fun i g' hi => by simpa using h (i + 1) g' (by simpa using hi))

omit [Ops] in
theorem Mix.not_taken {m : Mix} (h : m.settled = true) {s : Side} {k : Nat} {c : Crossing}
    (hk : (m.outs s)[k]? = some c) : c.state ≠ .taken := by
  simp only [Mix.settled, List.all_eq_true, decide_eq_true_eq] at h
  exact h c ((m.outs_all c).mpr ⟨s, List.mem_of_getElem? hk⟩)

omit [Ops] in
/-- Where no crossing is left taken and unacknowledged, each guest's
    processes are the replay's at that guest's places, in order. -/
theorem Agree.procs {m : Mix} {R : MConfig} {L : Side → Local} (ag : Agree m R L)
    (hset : m.settled = true) (s : Side) :
    (m.places s).filterMap (R.procs[·]?) = (L s).procs := by
  refine filterMap_places R.procs _ _ (ag.len s) ?_
  intro i g hi
  exact ag.same s i g hi (fun a _ _ c hc => Mix.not_taken hset hc)

theorem beginIn_inv {cells budget : Nat} {p : Term} {c₀ : MConfig}
    (h : beginIn cells budget p = some c₀) : ∃ st, c₀ = ⟨[⟨st, []⟩], []⟩ := by
  simp only [beginIn] at h
  split at h
  · split at h
    · next st _ => cases h; exact ⟨st, rfl⟩
    · cases h
  · cases h

omit [Ops] in
/-- At the start: guest `a` has the program as its one process, `b` has none. -/
theorem Agree.first {c₀ : MConfig} {st : Status MValue MOutcome} (h : c₀ = ⟨[⟨st, []⟩], []⟩) :
    Agree Mix.first c₀ (fun u => match u with | .a => Local.init c₀.procs | .b => Local.init []) := by
  subst h
  refine ⟨⟨Shape.first, Shaped.first⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s; cases s <;> rfl
  · intro n hn; simp at hn
  · intro s; cases s <;> rfl
  · intro s k c hk; cases s <;> simp [Mix.first, Mix.outs] at hk
  · intro s i g hi _
    cases s
    · cases i with
      | zero =>
        simp [Mix.first, Mix.places] at hi
        subst hi
        rfl
      | succ i => simp [Mix.first, Mix.places] at hi
    · simp [Mix.first, Mix.places] at hi
  · intro s a ha; cases s <;> simp [Local.init] at ha

/-- Two logs, each what a guest's log allows from that guest's first state,
    every crossing taken as the packet made for it. If they combine, the check
    accepts them with the budget they were run with, and what the replay
    reaches, at each guest's places, is that guest's processes. -/
theorem replay_agrees {cells budget : Nat} {p : Term} {c₀ : MConfig} {ra rb : List (Note × Data)}
    {FA FB : Local} {t : List (Side × Note × List Event)} {last : Mix}
    (hb : beginIn cells budget p = some c₀)
    (runA : SideRun cells budget .a (Local.init c₀.procs) ra FA)
    (runB : SideRun cells budget .b (Local.init []) rb FB)
    (linkA : ∀ r ∈ ra, ∀ k, r.1.taking = some k → FB.outPkts[k]? = some r.2)
    (linkB : ∀ r ∈ rb, ∀ k, r.1.taking = some k → FA.outPkts[k]? = some r.2)
    (ht : combineTrace (ra.map (·.1)) (rb.map (·.1)) = some (t, last)) :
    ∃ cfg, accept cells budget p (ra.map (·.1)) (rb.map (·.1)) = some (traceEvents t, cfg) ∧
      last.placeA.filterMap (cfg.procs[·]?) = FA.procs ∧
      last.placeB.filterMap (cfg.procs[·]?) = FB.procs := by
  obtain ⟨hw, hc⟩ := combineTrace_walk ht
  obtain ⟨st, hst⟩ := beginIn_inv hb
  obtain ⟨R', hs, ag⟩ := hw.replay (cells := cells) (budget := budget)
    (L := fun u => match u with | .a => Local.init c₀.procs | .b => Local.init [])
    rfl rfl runA runB linkA linkB (Agree.first hst)
    (by intro u; cases u <;> exact Local.Ok.init _ _ _ _)
  refine ⟨R', ?_, ag.procs hw.settled .a, ag.procs hw.settled .b⟩
  simp [accept, hc, hb, hs]

end Reflect
