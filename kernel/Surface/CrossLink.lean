import Surface.CrossStep

/-!
One guest beside its peer: what ties a guest's state to its own log and to the
packets the peer made, and why a step keeps it.

`Dir v w L M rs W to h` is everything that is said of guest `v` with peer `w`:

* its processes, names, crossings out and packets are what its log `rs` says
  (`L`, a `Reflect.Local`);
* the packets it has worked are `W`, the first of those the peer made, in the
  order the peer made them, and its inbox is the next ones;
* each crossing it took, it took as the packet the peer made for it, and each
  acknowledgement it worked is of a crossing it had out;
* its half `h` of the shape (`Reflect.Shape`) is its crossings as its log and
  the peer's takings leave them.

`Acts.out`: a step of a guest keeps `Dir` of both guests, and what it recorded
is a step of its own log (`Reflect.SideRun`) and can be placed on the two
halves (`HPath`). Nothing here is about budgets or about beginning.
-/

namespace Reflect

variable [Ops]

/-! The packets a log says its guest made. -/

/-- A packet that puts crossing `k` out: a start or a send, not an
    acknowledgement. -/
def IsOut (k : Nat) (p : Data) : Prop := ∃ tag rest, p = .arr (.nat tag :: .nat k :: rest) ∧ tag ≠ 2

omit [Ops] in
theorem packetOf_isOut {k : Nat} {held : List Nat} {p pkt : Data}
    (h : packetOf k held p = some pkt) : IsOut k pkt := by
  unfold packetOf at h
  split at h
  · cases h; exact ⟨0, _, rfl, by decide⟩
  · cases h; exact ⟨1, _, rfl, by decide⟩
  · cases h

omit [Ops] in
theorem IsOut.not_ack {k k' : Nat} (h : IsOut k (ackPacket k')) : False := by
  obtain ⟨tag, rest, he, hne⟩ := h
  simp only [ackPacket, Data.arr.injEq, List.cons.injEq, Data.nat.injEq] at he
  exact hne he.1.symm

omit [Ops] in
theorem IsOut.num {k k' : Nat} {p : Data} (h : IsOut k p) (h' : IsOut k' p) : k = k' := by
  obtain ⟨tag, rest, he, _⟩ := h
  obtain ⟨tag', rest', he', _⟩ := h'
  rw [he] at he'
  simp only [Data.arr.injEq, List.cons.injEq, Data.nat.injEq] at he'
  exact he'.2.1

omit [Ops] in
theorem ackPacket_inj {k k' : Nat} (h : ackPacket k = ackPacket k') : k = k' := by
  simpa [ackPacket] using h

/-- The crossing a packet acknowledges, when it is an acknowledgement. -/
def ackNum : Data → Option Nat
  | .arr [.nat 2, .nat k] => some k
  | _ => none

omit [Ops] in
theorem ackNum_ack (k : Nat) : ackNum (ackPacket k) = some k := rfl

omit [Ops] in
theorem ackNum_some {p : Data} {k : Nat} (h : ackNum p = some k) : p = ackPacket k := by
  unfold ackNum at h
  split at h
  · cases h; rfl
  · cases h

omit [Ops] in
theorem IsOut.no_ack {k : Nat} {p : Data} (h : IsOut k p) : ackNum p = none := by
  cases hn : ackNum p with
  | none => rfl
  | some k' => rw [ackNum_some hn] at h; exact absurd h IsOut.not_ack

/-- Every packet made is the packet of a crossing put out or the
    acknowledgement of a crossing taken; each crossing's packet was made and
    carries its number; the acknowledgements made are, in order, the crossings
    taken; and no packet was made twice. -/
structure Local.Posted (L : Local) : Prop where
  src : ∀ p ∈ L.posted, (∃ k : Nat, L.outPkts[k]? = some p) ∨ (∃ k ∈ L.took, p = ackPacket k)
  outs : ∀ (k : Nat) (p : Data), L.outPkts[k]? = some p → p ∈ L.posted ∧ IsOut k p
  acks : L.posted.filterMap ackNum = L.took
  nodup : L.posted.Nodup

omit [Ops] in
theorem Local.Posted.init (procs : List (Proc MValue MOutcome)) : (Local.init procs).Posted where
  src := by intro p hp; simp [Local.init] at hp
  outs := by intro k p hk; simp [Local.init] at hk
  acks := rfl
  nodup := List.nodup_nil

omit [Ops] in
theorem getElem?_snoc {α : Type} {l : List α} {x y : α} {k : Nat} (h : (l ++ [x])[k]? = some y) :
    l[k]? = some y ∨ (k = l.length ∧ y = x) := by
  by_cases hlt : k < l.length
  · rw [List.getElem?_append_left hlt] at h; exact .inl h
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at h
    have hz : k - l.length = 0 := by
      rcases Nat.eq_zero_or_pos (k - l.length) with hz | hz
      · exact hz
      · rw [List.getElem?_eq_none (by simp only [List.length_singleton]; exact hz)] at h; cases h
    rw [hz] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact .inr ⟨by omega, h.symm⟩

omit [Ops] in
/-- A packet made that puts a crossing out is that crossing's packet. -/
theorem Local.Posted.out_of {L : Local} (hp : L.Posted) {p : Data} {k : Nat} (hm : p ∈ L.posted)
    (ho : IsOut k p) : L.outPkts[k]? = some p := by
  rcases hp.src p hm with ⟨k', hk'⟩ | ⟨k', _, rfl⟩
  · have := (hp.outs k' p hk').2.num ho
    subst this
    exact hk'
  · exact absurd ho IsOut.not_ack

omit [Ops] in
/-- An acknowledgement made is of a crossing taken. -/
theorem Local.Posted.took_of {L : Local} (hp : L.Posted) {k : Nat} (hm : ackPacket k ∈ L.posted) :
    k ∈ L.took := by
  rcases hp.src _ hm with ⟨k', hk'⟩ | ⟨k', hk', he⟩
  · exact absurd (hp.outs k' _ hk').2 IsOut.not_ack
  · rw [ackPacket_inj he]; exact hk'

omit [Ops] in
/-- A crossing taken was acknowledged. -/
theorem Local.Posted.ack_of {L : Local} (hp : L.Posted) {k : Nat} (hk : k ∈ L.took) :
    ackPacket k ∈ L.posted := by
  rw [← hp.acks] at hk
  obtain ⟨p, hm, hn⟩ := List.mem_filterMap.mp hk
  rw [← ackNum_some hn]
  exact hm

/-- An entry keeps `Posted`, when the crossing it takes was not taken before. -/
theorem SideStep.posted {cells budget : Nat} {s : Side} {L M : Local} {r : Note × Data}
    (h : SideStep cells budget s L r M) (hp : L.Posted)
    (hf : ∀ k, r.1.taking = some k → k ∉ L.took) : M.Posted := by
  cases h with
  | did => exact ⟨hp.src, hp.outs, hp.acks, hp.nodup⟩
  | @out i k c p held pkt next d hi free hk hw hpk ht =>
    have hout : IsOut L.outPkts.length pkt := by rw [← hk]; exact packetOf_isOut hpk
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases hp.src x hx with ⟨k', hk'⟩ | ⟨k', hk', rfl⟩
        · exact .inl ⟨k', by
            show (L.outPkts ++ [pkt])[k']? = some x
            rw [List.getElem?_append_left (lt_of_getElem? hk')]; exact hk'⟩
        · exact .inr ⟨k', hk', rfl⟩
      · simp only [List.mem_singleton] at hx
        subst hx
        exact .inl ⟨L.outPkts.length, by simp⟩
    · intro k' x hx
      rcases getElem?_snoc hx with hold | ⟨hkl, rfl⟩
      · obtain ⟨hm, ho⟩ := hp.outs k' x hold
        exact ⟨List.mem_append_left _ hm, ho⟩
      · refine ⟨List.mem_append_right _ (by simp), ?_⟩
        rw [hkl]
        exact hout
    · show (L.posted ++ [pkt]).filterMap ackNum = L.took
      rw [List.filterMap_append, hp.acks]
      simp [hout.no_ack]
    · show (L.posted ++ [pkt]).Nodup
      refine List.nodup_append.mpr ⟨hp.nodup, (by simp), ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      intro he
      subst he
      have := lt_of_getElem? (hp.out_of hx hout)
      omega
  | @spawnIn k prog start held t hs w child hu hn hr hc =>
    have hk : k ∉ L.took := hf k rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases hp.src x hx with ⟨k', hk'⟩ | ⟨k', hk', rfl⟩
        · exact .inl ⟨k', hk'⟩
        · exact .inr ⟨k', List.mem_append_left _ hk', rfl⟩
      · simp only [List.mem_singleton] at hx
        subst hx
        exact .inr ⟨k, by simp, rfl⟩
    · intro k' x hx
      obtain ⟨hm, ho⟩ := hp.outs k' x hx
      exact ⟨List.mem_append_left _ hm, ho⟩
    · show (L.posted ++ [ackPacket k]).filterMap ackNum = L.took ++ [k]
      rw [List.filterMap_append, hp.acks]
      simp [ackNum_ack]
    · show (L.posted ++ [ackPacket k]).Nodup
      refine List.nodup_append.mpr ⟨hp.nodup, (by simp), ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      intro he
      subst he
      exact hk (hp.took_of hx)
  | @sendIn k j name message held hs c p held' st hn hj free hrecv ht =>
    have hk : k ∉ L.took := hf k rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases hp.src x hx with ⟨k', hk'⟩ | ⟨k', hk', rfl⟩
        · exact .inl ⟨k', hk'⟩
        · exact .inr ⟨k', List.mem_append_left _ hk', rfl⟩
      · simp only [List.mem_singleton] at hx
        subst hx
        exact .inr ⟨k, by simp, rfl⟩
    · intro k' x hx
      obtain ⟨hm, ho⟩ := hp.outs k' x hx
      exact ⟨List.mem_append_left _ hm, ho⟩
    · show (L.posted ++ [ackPacket k]).filterMap ackNum = L.took ++ [k]
      rw [List.filterMap_append, hp.acks]
      simp [ackNum_ack]
    · show (L.posted ++ [ackPacket k]).Nodup
      refine List.nodup_append.mpr ⟨hp.nodup, (by simp), ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      intro he
      subst he
      exact hk (hp.took_of hx)
  | ack => exact ⟨hp.src, hp.outs, hp.acks, hp.nodup⟩
  | held => exact hp
  | full => exact hp

/-! Paths on shapes, a guest's entries at a time at the end. -/

omit [Ops] in
theorem SPath.snocA {sh fin fin' : Shape} {a b : List Note} {x : Note} (h : SPath sh a b fin)
    (hp : fin.place .a x = some fin') : SPath sh (a ++ [x]) b fin' := by
  induction h with
  | done => exact .left hp .done
  | left h _ ih => exact .left h (ih hp)
  | right h _ ih => exact .right h (ih hp)

omit [Ops] in
theorem SPath.snocB {sh fin fin' : Shape} {a b : List Note} {y : Note} (h : SPath sh a b fin)
    (hp : fin.place .b y = some fin') : SPath sh a (b ++ [y]) fin' := by
  induction h with
  | done => exact .right hp .done
  | left h _ ih => exact .left h (ih hp)
  | right h _ ih => exact .right h (ih hp)

/-- Entries of one guest placed one after another on its own half `h` and the
    other guest's half `hw`. -/
inductive HPath : Half → Half → List Note → Half → Half → Prop where
  | nil {h hw : Half} : HPath h hw [] h hw
  | cons {h hw h₁ hw₁ h' hw' : Half} {e : Note} {es : List Note} (ho : h.own e.own = some h₁)
      (ht : hw.take e.taking = some hw₁) (rest : HPath h₁ hw₁ es h' hw') :
      HPath h hw (e :: es) h' hw'

omit [Ops] in
theorem HPath.append {h hw h₁ hw₁ h' hw' : Half} {es es' : List Note} (p : HPath h hw es h₁ hw₁)
    (q : HPath h₁ hw₁ es' h' hw') : HPath h hw (es ++ es') h' hw' := by
  induction p with
  | nil => exact q
  | cons ho ht _ ih => exact .cons ho ht (ih q)

omit [Ops] in
theorem SPath.addA {sh : Shape} {b ns : List Note} {h hw h' hw' : Half} (hp : HPath h hw ns h' hw') :
    ∀ {a : List Note}, SPath sh a b ⟨h, hw⟩ → SPath sh (a ++ ns) b ⟨h', hw'⟩ := by
  induction hp with
  | nil => intro a p; simpa using p
  | @cons h hw h₁ hw₁ h' hw' e es ho ht rest ih =>
    intro a p
    have hpl : (⟨h, hw⟩ : Shape).place .a e = some ⟨h₁, hw₁⟩ := Shape.place_of (sh' := ⟨h₁, hw₁⟩) ho ht
    have := ih (p.snocA hpl)
    simpa using this

omit [Ops] in
theorem SPath.addB {sh : Shape} {a ns : List Note} {h hw h' hw' : Half} (hp : HPath h hw ns h' hw') :
    ∀ {b : List Note}, SPath sh a b ⟨hw, h⟩ → SPath sh a (b ++ ns) ⟨hw', h'⟩ := by
  induction hp with
  | nil => intro b p; simpa using p
  | @cons h hw h₁ hw₁ h' hw' e es ho ht rest ih =>
    intro b p
    have hpl : (⟨hw, h⟩ : Shape).place .b e = some ⟨hw₁, h₁⟩ := Shape.place_of (sh' := ⟨hw₁, h₁⟩) ho ht
    have := ih (p.snocB hpl)
    simpa using this

/-! What a local event needs of a half. -/

theorem stepIn_nil {cells budget : Nat} {cfg cfg' : MConfig} {ev : Event} (hp : cfg.procs = [])
    (hin : ev.isAnswer = false) : stepIn cells budget cfg ev ≠ .ok cfg' := by
  intro h
  cases ev with
  | fresh i n => obtain ⟨c, p, held, st, hi, _⟩ := stepIn_fresh_inv h; simp [hp] at hi
  | spawn i => obtain ⟨c, p, held, t, arg, w, child, st, hi, _⟩ := stepIn_spawn_inv h; simp [hp] at hi
  | comm i j => obtain ⟨c, p, held, c', p', held', ch, v, st, st', hi, _⟩ := stepIn_comm_inv h; simp [hp] at hi
  | answer i x => simp [Event.isAnswer] at hin

/-- A local event of processes that are not held can be placed on its guest's
    half, and leaves the half with as many processes as the guest has. -/
theorem did_own {cells budget : Nat} {cfg cfg' : MConfig} {ev : Event} {h : Half}
    (hs : stepIn cells budget cfg ev = .ok cfg') (hin : ev.isAnswer = false)
    (free : ∀ i ∈ ev.places, h.held i = false) (hn : h.n = cfg.procs.length) :
    ∃ h', h.own (Note.did ev).own = some h' ∧ h'.n = cfg'.procs.length ∧ h'.outs = h.outs := by
  cases ev with
  | fresh i n =>
    obtain ⟨c, p, held, st, hi, _, _, _, rfl⟩ := stepIn_fresh_inv hs
    have hlt := lt_of_getElem? hi
    refine ⟨h, ?_, by simp [hn], rfl⟩
    simp [Note.own, Half.own, Half.free, free i (by simp [Event.places]), hn, hlt]
  | spawn i =>
    obtain ⟨c, p, held, t, arg, w, child, st, hi, _, _, _, _, rfl⟩ := stepIn_spawn_inv hs
    have hlt := lt_of_getElem? hi
    refine ⟨{ h with n := h.n + 1 }, ?_, by simp [hn], rfl⟩
    simp [Note.own, Half.own, Half.free, free i (by simp [Event.places]), hn, hlt]
  | comm i j =>
    obtain ⟨c, p, held, c', p', held', ch, v, st, st', hi, hj, _, _, _, _, _, _, rfl⟩ := stepIn_comm_inv hs
    have hlt := lt_of_getElem? hi
    have hlt' := lt_of_getElem? hj
    refine ⟨h, ?_, by simp [hn], rfl⟩
    simp [Note.own, Half.own, Half.free, free i (by simp [Event.places]),
      free j (by simp [Event.places]), hn, hlt, hlt']
  | answer i x => simp [Event.isAnswer] at hin

end Reflect

namespace Surface.Cross
open Reflect

/-- A crossing a guest has out, as its log's reading has it. -/
def Asked.ask (a : Asked) : Ask := ⟨a.place, a.k, a.next⟩

/-- Guest `v` beside its peer `w`. `L` is what `v`'s log `rs` says of it and
    `M` what `w`'s says of `w`; `W` is the packets of `w` that `v` has worked;
    `to` is every batch `v` has made; `h` is `v`'s half of the shape. -/
structure Dir (v w : View) (L M : Local) (rs : List (Note × Data)) (W to : List Data) (h : Half) :
    Prop where
  /-- The guest is what its log says. -/
  log : rs.map (·.1) = v.log.reverse
  procs : L.procs = v.cfg.procs
  names : L.names = v.cfg.names
  asked : L.asked = v.asked.map Asked.ask
  outs : L.outPkts.length = v.outs
  took : L.took = rs.filterMap (·.1.taking)
  posted : L.Posted
  /-- What it keeps to send is what the peer has not counted. -/
  sent : v.sent = L.posted.drop v.sentBase
  base : v.sentBase ≤ w.got
  /-- What it has worked and what it has accepted are the first packets the
      peer made, in order. -/
  split : ∃ rest, M.posted = W ++ v.inbox ++ rest ∧ v.got = W.length + v.inbox.length
  /-- A crossing taken was taken as the packet made for it, one worked. -/
  link : ∀ r ∈ rs, ∀ k, r.1.taking = some k → M.outPkts[k]? = some r.2 ∧ r.2 ∈ W
  pend : ∀ p ∈ v.pending, p.pkt ∈ W ∧ p.k ∉ L.took
  /-- A crossing is out until its acknowledgement is worked. -/
  acked : ∀ k, k < v.outs → (∀ a ∈ v.asked, a.k ≠ k) → ackPacket k ∈ W
  unacked : ∀ a ∈ v.asked, ackPacket a.k ∉ W
  acks : acksOf v.log.reverse = W.filterMap ackNum
  /-- A batch it made says what it had accepted and carries packets it made,
      each under its number. -/
  batches : ∀ d ∈ to, ∃ flag got steps cells pkts,
    d = .arr [.nat flag, .nat got, .nat steps, .nat cells, .arr pkts] ∧ got ≤ v.got ∧
    ∀ (seq : Nat) (pkt : Data), Data.arr [.nat seq, pkt] ∈ pkts → L.posted[seq]? = some pkt
  /-- Its half of the shape. -/
  hn : h.n = L.procs.length
  hlen : h.outs.length = v.outs
  live : ∀ a ∈ v.asked, ∃ st, h.outs[a.k]? = some (⟨a.place, st⟩ : SCross) ∧
    (a.k ∈ M.took → st = .taken) ∧ (a.k ∉ M.took → st = .offered)
  dead : ∀ (k : Nat) (c : SCross), h.outs[k]? = some c → (∀ a ∈ v.asked, a.k ≠ k) → c.state = .acked

section
variable {v v' w : View} {L L' M : Local} {rs rw : List (Note × Data)} {W Ww to tw : List Data}
  {h hw : Half}

/-- What a guest's peer does leaves the guest's side as it was, when the peer
    only makes packets and accepts them. -/
theorem Dir.frame (d : Dir w v M L rw Ww tw hw) (hgot : v.got ≤ v'.got)
    (hpost : ∃ add, L'.posted = L.posted ++ add)
    (hout : ∀ (k : Nat) (p : Data), L.outPkts[k]? = some p → L'.outPkts[k]? = some p)
    (htook : L'.took = L.took) : Dir w v' M L' rw Ww tw hw :=
  { d with
    base := Nat.le_trans d.base hgot
    split := by
      obtain ⟨rest, hr, hg⟩ := d.split
      obtain ⟨add, ha⟩ := hpost
      exact ⟨rest ++ add, by rw [ha, hr]; simp, hg⟩
    link := fun r hr k hk => ⟨hout _ _ (d.link r hr k hk).1, (d.link r hr k hk).2⟩
    live := by rw [htook]; exact d.live }

/-- The peer takes crossing `k`, which is out and was not taken: the guest's
    half goes from offered to taken. -/
theorem Dir.taken {k : Nat} (d : Dir w v M L rw Ww tw hw) (hgot : v.got ≤ v'.got)
    (hpost : ∃ add, L'.posted = L.posted ++ add)
    (hout : ∀ (k : Nat) (p : Data), L.outPkts[k]? = some p → L'.outPkts[k]? = some p)
    (htook : L'.took = L.took ++ [k]) (hfresh : k ∉ L.took) (hk : ∃ a ∈ w.asked, a.k = k) :
    ∃ hw', hw.take (some k) = some hw' ∧ Dir w v' M L' rw Ww tw hw' := by
  obtain ⟨a, ha, rfl⟩ := hk
  obtain ⟨st, hst, _, hoff⟩ := d.live a ha
  have := hoff hfresh
  subst this
  have hlt := lt_of_getElem? hst
  refine ⟨{ hw with outs := hw.outs.set a.k ⟨a.place, .taken⟩ }, ?_, ?_⟩
  · simp [Half.take, hst]
  · exact
    { d with
      base := Nat.le_trans d.base hgot
      split := by
        obtain ⟨rest, hr, hg⟩ := d.split
        obtain ⟨add, hadd⟩ := hpost
        exact ⟨rest ++ add, by rw [hadd, hr]; simp, hg⟩
      link := fun r hr k hk => ⟨hout _ _ (d.link r hr k hk).1, (d.link r hr k hk).2⟩
      hn := d.hn
      hlen := by simp [d.hlen]
      live := by
        intro a' ha'
        obtain ⟨st', hst', ht', ho'⟩ := d.live a' ha'
        by_cases hkk : a'.k = a.k
        · rw [hkk, hst] at hst'
          simp only [Option.some.injEq, SCross.mk.injEq] at hst'
          refine ⟨.taken, ?_, fun _ => rfl, fun hn => absurd (by rw [htook, hkk]; simp) hn⟩
          show (hw.outs.set a.k ⟨a.place, .taken⟩)[a'.k]? = _
          rw [hkk, List.getElem?_set_self hlt, hst'.1]
        · refine ⟨st', ?_, ?_, ?_⟩
          · show (hw.outs.set a.k ⟨a.place, .taken⟩)[a'.k]? = _
            rw [List.getElem?_set_ne (fun h => hkk h.symm)]
            exact hst'
          · intro hm
            rw [htook] at hm
            rcases List.mem_append.mp hm with hm | hm
            · exact ht' hm
            · simp at hm; exact absurd hm hkk
          · intro hm
            exact ho' (fun h => hm (by rw [htook]; exact List.mem_append_left _ h))
      dead := by
        intro k' c hc hno
        have hne : a.k ≠ k' := hno a ha
        have hc' : hw.outs[k']? = some c := by
          have : (hw.outs.set a.k ⟨a.place, .taken⟩)[k']? = some c := hc
          rwa [List.getElem?_set_ne hne] at this
        exact d.dead k' c hc' hno }

end

end Surface.Cross
