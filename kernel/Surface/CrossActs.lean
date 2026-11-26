import Surface.CrossLink

/-!
A step of a guest keeps `Dir` of both guests (`Acts.dir`): what it recorded is
a run of its own log from where it stood, and can be placed, entry by entry, on
its own half and its peer's.
-/
namespace Surface.Cross
open Reflect

theorem acksOf_append (a b : List Note) : acksOf (a ++ b) = acksOf a ++ acksOf b := by
  simp [acksOf]

theorem link_snoc {M : Local} {rs : List (Note × Data)} {W W' : List Data} {r : Note × Data}
    (old : ∀ r ∈ rs, ∀ k, r.1.taking = some k → M.outPkts[k]? = some r.2 ∧ r.2 ∈ W)
    (hsub : ∀ p ∈ W, p ∈ W')
    (new : ∀ k, r.1.taking = some k → M.outPkts[k]? = some r.2 ∧ r.2 ∈ W') :
    ∀ r' ∈ rs ++ [r], ∀ k, r'.1.taking = some k → M.outPkts[k]? = some r'.2 ∧ r'.2 ∈ W' := by
  intro r' hr' k hk
  rcases List.mem_append.mp hr' with hr' | hr'
  · exact ⟨(old r' hr' k hk).1, hsub _ (old r' hr' k hk).2⟩
  · simp only [List.mem_singleton] at hr'
    subst hr'
    exact new k hk

section
variable {sd : Side} {v v' w : View} {L M : Local} {rs rw : List (Note × Data)}
  {W Ww to tw : List Data} {h hw : Half}

theorem Dir.sub (me : Dir v w L M rs W to h) {p : Data} (hp : p ∈ W) : p ∈ M.posted := by
  obtain ⟨rest, hr, _⟩ := me.split
  rw [hr]
  simp [hp]

/-- The packet a guest works next is one the peer made, and not one worked. -/
theorem Dir.head (me : Dir v w L M rs W to h) (hM : M.posted.Nodup) {pkt : Data} {rest : List Data}
    (hin : v.inbox = pkt :: rest) : pkt ∈ M.posted ∧ pkt ∉ W := by
  obtain ⟨rest0, hr, _⟩ := me.split
  rw [hin] at hr
  refine ⟨by rw [hr]; simp, ?_⟩
  intro hw
  rw [hr, List.append_assoc] at hM
  exact (List.nodup_append.mp hM).2.2 pkt hw pkt (by simp) rfl

theorem Dir.pop (me : Dir v w L M rs W to h) {pkt : Data} {rest : List Data}
    (hin : v.inbox = pkt :: rest) :
    ∃ rest0, M.posted = (W ++ [pkt]) ++ rest ++ rest0 ∧ v.got = (W ++ [pkt]).length + rest.length := by
  obtain ⟨rest0, hr, hg⟩ := me.split
  refine ⟨rest0, by rw [hr, hin]; simp, ?_⟩
  rw [hg, hin]
  simp
  omega

/-- A crossing a guest took, it took as a packet it worked. -/
theorem Dir.took_in (me : Dir v w L M rs W to h) {k : Nat} (hk : k ∈ L.took) :
    ∃ p ∈ W, M.outPkts[k]? = some p := by
  rw [me.took] at hk
  obtain ⟨r, hr, hk⟩ := List.mem_filterMap.mp hk
  exact ⟨r.2, (me.link r hr k hk).2, (me.link r hr k hk).1⟩

/-- A crossing the peer took is one this guest put out. -/
theorem Dir.took_lt (peer : Dir w v M L rw Ww tw hw) {k : Nat} (hk : k ∈ M.took) :
    k < L.outPkts.length := by
  obtain ⟨p, _, hp⟩ := peer.took_in hk
  exact lt_of_getElem? hp

/-- A packet that puts a crossing out and is not yet worked: the crossing was
    not taken. -/
theorem Dir.fresh (me : Dir v w L M rs W to h) (peer : Dir w v M L rw Ww tw hw) {pkt : Data} {k : Nat}
    (hm : pkt ∈ M.posted) (hn : pkt ∉ W) (ho : IsOut k pkt) : k ∉ L.took := by
  intro hk
  obtain ⟨p, hp, hpk⟩ := me.took_in hk
  rw [peer.posted.out_of hm ho] at hpk
  cases hpk
  exact hn hp

/-- A crossing put out and not taken is still out on the guest that put it
    out. -/
theorem Dir.out_asked (me : Dir v w L M rs W to h) (peer : Dir w v M L rw Ww tw hw) {pkt : Data}
    {k : Nat} (hm : pkt ∈ M.posted) (ho : IsOut k pkt) (hf : k ∉ L.took) : ∃ a ∈ w.asked, a.k = k := by
  have hlt : k < w.outs := by rw [← peer.outs]; exact lt_of_getElem? (peer.posted.out_of hm ho)
  refine Classical.byContradiction fun hno => ?_
  have hall : ∀ a ∈ w.asked, a.k ≠ k := fun a ha he => hno ⟨a, ha, he⟩
  exact hf (me.posted.took_of (peer.sub (peer.acked k hlt hall)))

/-- A process the guest does not hold is not held on its half. -/
theorem Dir.not_held (me : Dir v w L M rs W to h) {i : Nat}
    (free : v.asked.any (·.place == i) = false) : h.held i = false := by
  unfold Half.held
  rw [List.any_eq_false]
  intro c hc
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hc
  by_cases hex : ∃ a ∈ v.asked, a.k = k
  · obtain ⟨a, ha, rfl⟩ := hex
    obtain ⟨st, hst, _⟩ := me.live a ha
    rw [hst] at hk
    cases hk
    have hne : a.place ≠ i := by simpa using List.any_eq_false.mp free a ha
    simp [hne]
  · have := me.dead k c hk (fun a ha he => hex ⟨a, ha, he⟩)
    simp [this]

theorem Dir.sent_snoc (me : Dir v w L M rs W to h) (peer : Dir w v M L rw Ww tw hw) (x : Data) :
    v.sent ++ [x] = (L.posted ++ [x]).drop v.sentBase := by
  have hbase : v.sentBase ≤ L.posted.length := by
    obtain ⟨rest, hr, hg⟩ := peer.split
    have := me.base
    rw [hg] at this
    rw [hr]
    simp
    omega
  rw [List.drop_append_of_le_length hbase, me.sent]

theorem Dir.batches_snoc (me : Dir v w L M rs W to h) (x : Data) :
    ∀ d ∈ to, ∃ flag got steps cells pkts,
      d = .arr [.nat flag, .nat got, .nat steps, .nat cells, .arr pkts] ∧ got ≤ v.got ∧
      ∀ (seq : Nat) (pkt : Data), Data.arr [.nat seq, pkt] ∈ pkts → (L.posted ++ [x])[seq]? = some pkt := by
  intro d hd
  obtain ⟨flag, got, steps, cells, pkts, rfl, hg, hpk⟩ := me.batches d hd
  refine ⟨flag, got, steps, cells, pkts, rfl, hg, fun seq y hy => ?_⟩
  rw [List.getElem?_append_left (lt_of_getElem? (hpk seq y hy))]
  exact hpk seq y hy

/-- What a step leaves: the entries it recorded, read as the guest's log
    reads them and placed on the two halves, and `Dir` of both guests. -/
def Out (sd : Side) (v v' w : View) (L M : Local) (rs rw : List (Note × Data))
    (Ww to tw : List Data) (h hw : Half) : Prop :=
  ∃ new L' W' h' hw', SideRun v.cells v.budget sd L new L' ∧ HPath h hw (new.map (·.1)) h' hw' ∧
    Dir v' w L' M (rs ++ new) W' to h' ∧ Dir w v' M L' rw Ww tw hw'

theorem Out.same (me : Dir v w L M rs W to h) (peer : Dir w v M L rw Ww tw hw) :
    Out sd v v w L M rs rw Ww to tw h hw :=
  ⟨[], L, W, h, hw, .nil, .nil, by simpa using me, peer⟩

/-- A count recorded changes nothing but the log. -/
theorem Dir.count (me : Dir v w L M rs W to h) (peer : Dir w v M L rw Ww tw hw) {n : Note}
    (hn : (∃ m, n = .held m) ∨ ∃ m, n = .full m) :
    Dir { v with log := n :: v.log } w L M (rs ++ [(n, .arr [])]) W to h ∧
      Dir w { v with log := n :: v.log } M L rw Ww tw hw := by
  have htk : n.taking = none := by rcases hn with ⟨m, rfl⟩ | ⟨m, rfl⟩ <;> rfl
  have hack : acksOf [n] = [] := by rcases hn with ⟨m, rfl⟩ | ⟨m, rfl⟩ <;> rfl
  refine ⟨{ me with
      log := by simp [me.log]
      took := by simp [me.took, List.filterMap_append, htk]
      link := link_snoc me.link (fun _ h => h) (by intro k hk; rw [htk] at hk; cases hk)
      acks := by
        show acksOf (n :: v.log).reverse = _
        rw [List.reverse_cons, acksOf_append, me.acks, hack, List.append_nil] },
    peer.frame (Nat.le_refl _) ⟨[], by simp⟩ (fun _ _ h => h) rfl⟩

theorem Out.counted {v₁ : View} {extra : List Note} (o : Out sd v v₁ w L M rs rw Ww to tw h hw)
    (hx : Counted extra) : Out sd v { v₁ with log := extra ++ v₁.log } w L M rs rw Ww to tw h hw := by
  obtain ⟨new, L', W', h', hw', run, path, me, peer⟩ := o
  rcases hx with rfl | ⟨m, rfl | rfl⟩
  · exact ⟨new, L', W', h', hw', run, path, me, peer⟩
  · obtain ⟨me', peer'⟩ := me.count peer (n := .held m) (.inl ⟨m, rfl⟩)
    refine ⟨new ++ [(.held m, .arr [])], L', W', h', hw', run.snoc .held, ?_,
      by rw [← List.append_assoc]; exact me', peer'⟩
    rw [List.map_append]
    exact path.append (.cons (by simp [Note.own, Half.own]) rfl .nil)
  · obtain ⟨me', peer'⟩ := me.count peer (n := .full m) (.inr ⟨m, rfl⟩)
    refine ⟨new ++ [(.full m, .arr [])], L', W', h', hw', run.snoc .full, ?_,
      by rw [← List.append_assoc]; exact me', peer'⟩
    rw [List.map_append]
    exact path.append (.cons (by simp [Note.own, Half.own]) rfl .nil)

/-- A step of a guest, other than beginning its program, keeps `Dir` of both
    guests. -/
theorem Acts.dir (act : Acts v v') (hside : v.side = sd) (ok : Local.Ok v.cells v.budget sd L)
    (me : Dir v w L M rs W to h) (peer : Dir w v M L rw Ww tw hw) :
    Out sd v v' w L M rs rw Ww to tw h hw := by
  have still : ∀ {u : View} {N : Local}, u.got = v.got → N.posted = L.posted →
      N.outPkts = L.outPkts → N.took = L.took → Dir w u M N rw Ww tw hw := by
    intro u N hg hp ho ht
    exact peer.frame (Nat.le_of_eq hg.symm) ⟨[], by simp [hp]⟩ (fun k p hk => by rw [ho]; exact hk) ht
  cases act with
  | same hv => subst hv; exact Out.same me peer
  | @drop pkt rest fixed hin hno hfix hv =>
    subst hv
    obtain ⟨hm, hnw⟩ := me.head peer.posted.nodup hin
    obtain ⟨rest0, hsp, hgot⟩ := me.pop hin
    have hnum : ackNum pkt = none := by
      cases hk : ackNum pkt with
      | none => rfl
      | some k =>
        have hpk := ackNum_some hk
        subst hpk
        have hlt : k < v.outs := by rw [← me.outs]; exact peer.took_lt (peer.posted.took_of hm)
        exact absurd (me.acked k hlt (fun a ha he => hno a ha (by rw [he]))) hnw
    refine ⟨[], L, W ++ [pkt], h, hw, .nil, .nil, ?_, still rfl rfl rfl rfl⟩
    rw [List.append_nil]
    exact { me with
      split := ⟨rest0, hsp, hgot⟩
      link := fun r hr k hk => ⟨(me.link r hr k hk).1, List.mem_append_left _ (me.link r hr k hk).2⟩
      pend := fun p hp => ⟨List.mem_append_left _ (me.pend p hp).1, (me.pend p hp).2⟩
      acked := fun k hk hno' => List.mem_append_left _ (me.acked k hk hno')
      unacked := by
        intro a ha hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact me.unacked a ha hmem
        · simp only [List.mem_singleton] at hmem
          exact hno a ha hmem.symm
      acks := by rw [List.filterMap_append, ← me.acks]; simp [hnum] }
  | @lost k rest a hin ha hk hq hv =>
    exfalso
    obtain ⟨c, p, held, pkt, hp, _⟩ := ok.asked a.ask (by rw [me.asked]; exact List.mem_map_of_mem ha)
    rw [me.procs] at hp
    have hp' : v.cfg.procs[a.place]? = some ⟨.waiting c p, held⟩ := hp
    rw [hq] at hp'
    cases hp'
  | @queue rest p hin hv =>
    subst hv
    obtain ⟨hm, hnw⟩ := me.head peer.posted.nodup hin
    obtain ⟨rest0, hsp, hgot⟩ := me.pop hin
    have hout : IsOut p.k p.pkt := ⟨1, _, rfl, by decide⟩
    refine ⟨[], L, W ++ [p.pkt], h, hw, .nil, .nil, ?_, still rfl rfl rfl rfl⟩
    rw [List.append_nil]
    exact { me with
      split := ⟨rest0, hsp, hgot⟩
      link := fun r hr k hk => ⟨(me.link r hr k hk).1, List.mem_append_left _ (me.link r hr k hk).2⟩
      pend := by
        intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact ⟨List.mem_append_left _ (me.pend q hq).1, (me.pend q hq).2⟩
        · simp only [List.mem_singleton] at hq
          subst hq
          exact ⟨by simp, me.fresh peer hm hnw hout⟩
      acked := fun k hk hno' => List.mem_append_left _ (me.acked k hk hno')
      unacked := by
        intro a ha hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact me.unacked a ha hmem
        · simp only [List.mem_singleton] at hmem
          rw [← hmem] at hout
          exact hout.not_ack
      acks := by rw [List.filterMap_append, ← me.acks]; simp [hout.no_ack] }
  | @unqueue k hv =>
    subst hv
    refine ⟨[], L, W, h, hw, .nil, .nil, ?_, still rfl rfl rfl rfl⟩
    rw [List.append_nil]
    exact { me with pend := fun p hp => me.pend p (List.mem_filter.mp hp).1 }
  | @did ev cfg extra hs free inside par hx hv =>
    subst hv
    refine Out.counted (v₁ := { v with cfg := cfg, log := .did ev :: v.log }) ?_ hx
    have hstep : SideStep v.cells v.budget sd L (.did ev, .arr [])
        { L with procs := cfg.procs, names := cfg.names } := by
      refine .did (by rw [me.procs, me.names]; exact hs) ?_ inside ?_
      · intro i hi
        rw [Local.held, me.asked, List.any_map]
        exact free i hi
      · intro i n he
        rw [← hside]
        exact par i n he
    obtain ⟨h', hown, hn', houts⟩ := did_own hs inside (fun i hi => me.not_held (free i hi))
      (by rw [me.hn, me.procs])
    refine ⟨[(.did ev, .arr [])], _, W, h', hw, .cons hstep .nil, .cons hown rfl .nil, ?_,
      still rfl rfl rfl rfl⟩
    exact { me with
      log := by simp [me.log]
      procs := rfl
      names := rfl
      took := by simp [me.took, List.filterMap_append, Note.taking]
      posted := hstep.posted me.posted (by intro k hk; cases hk)
      link := link_snoc me.link (fun _ h => h) (by intro k hk; cases hk)
      acks := by
        show acksOf (Note.did ev :: v.log).reverse = _
        rw [List.reverse_cons, acksOf_append, me.acks]
        simp [acksOf]
      hn := hn'
      hlen := by rw [houts]; exact me.hlen
      live := by rw [houts]; exact me.live
      dead := by rw [houts]; exact me.dead }
  | @out i c p held pkt next extra hi free hwant hp ht hx hv =>
    subst hv
    refine Out.counted (v₁ := { v with
          asked := ⟨i, v.outs, next⟩ :: v.asked, outs := v.outs + 1,
          sent := v.sent ++ [pkt], log := .out i v.outs :: v.log }) ?_ hx
    have hstep : SideStep v.cells v.budget sd L (.out i v.outs, .arr [])
        { L with
              asked := ⟨i, v.outs, next⟩ :: L.asked, outPkts := L.outPkts ++ [pkt],
              posted := L.posted ++ [pkt] } :=
      .out (by rw [me.procs]; exact hi) (by rw [Local.held, me.asked, List.any_map]; exact free)
        me.outs.symm hwant hp ht
    have hlt : i < h.n := by rw [me.hn, me.procs]; exact lt_of_getElem? hi
    have hfree : h.free i = true := by simp [Half.free, hlt, me.not_held free]
    have hnew : v.outs ∉ M.took := fun hk => by
      have := peer.took_lt hk
      rw [me.outs] at this
      omega
    refine ⟨[(.out i v.outs, .arr [])], _, W, { h with outs := h.outs ++ [⟨i, .offered⟩] }, hw,
      .cons hstep .nil, .cons (by simp [Note.own, Half.own, hfree, me.hlen]) rfl .nil, ?_,
      peer.frame (Nat.le_refl _) ⟨[pkt], rfl⟩ (fun k p hk => by
        show (L.outPkts ++ [pkt])[k]? = some p
        rw [List.getElem?_append_left (lt_of_getElem? hk)]
        exact hk) rfl⟩
    exact { me with
      log := by simp [me.log]
      asked := by simp [me.asked, Asked.ask]
      outs := by simp [me.outs]
      took := by simp [me.took, List.filterMap_append, Note.taking]
      posted := hstep.posted me.posted (by intro k hk; cases hk)
      sent := me.sent_snoc peer pkt
      link := link_snoc me.link (fun _ h => h) (by intro k hk; cases hk)
      acked := by
        intro k hk hno
        have hne : k ≠ v.outs := fun he => hno ⟨i, v.outs, next⟩ (by simp) he.symm
        have hk' : k < v.outs + 1 := hk
        exact me.acked k (by omega) (fun a ha => hno a (List.mem_cons_of_mem _ ha))
      unacked := by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · intro hmem
          exact hnew (peer.posted.took_of (me.sub hmem))
        · exact me.unacked a ha
      acks := by
        show acksOf (Note.out i v.outs :: v.log).reverse = _
        rw [List.reverse_cons, acksOf_append, me.acks]
        simp [acksOf]
      batches := me.batches_snoc pkt
      hlen := by simp [me.hlen]
      live := by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · refine ⟨.offered, ?_, fun hk => absurd hk hnew, fun _ => rfl⟩
          show (h.outs ++ [⟨i, .offered⟩])[v.outs]? = _
          rw [← me.hlen]
          simp
        · obtain ⟨st, hst, h1, h2⟩ := me.live a ha
          refine ⟨st, ?_, h1, h2⟩
          show (h.outs ++ [⟨i, .offered⟩])[a.k]? = _
          rw [List.getElem?_append_left (lt_of_getElem? hst)]
          exact hst
      dead := by
        intro k c hc hno
        rcases getElem?_snoc hc with hold | ⟨hkl, _⟩
        · exact me.dead k c hold (fun a ha => hno a (List.mem_cons_of_mem _ ha))
        · exact absurd (by rw [hkl, me.hlen]) (hno ⟨i, v.outs, next⟩ (by simp)) }
  | @spawnIn k prog start held rest t hs wo child extra hin hu hn hr hc hx hv =>
    subst hv
    refine Out.counted (v₁ := { v with
          cfg := ⟨v.cfg.procs ++ [⟨child, hs⟩], v.cfg.names⟩,
          sent := v.sent ++ [ackPacket k], inbox := rest, fixed := true, log := .spawnIn k :: v.log }) ?_ hx
    obtain ⟨hm, hnw⟩ := me.head peer.posted.nodup hin
    obtain ⟨rest0, hsp, hgot⟩ := me.pop hin
    have hout : IsOut k (.arr [.nat 0, .nat k, prog, start, .arr held]) := ⟨0, _, rfl, by decide⟩
    have hfresh : k ∉ L.took := me.fresh peer hm hnw hout
    have hstep : SideStep v.cells v.budget sd L (.spawnIn k, .arr [.nat 0, .nat k, prog, start, .arr held])
        { L with
              procs := L.procs ++ [⟨child, hs⟩], took := L.took ++ [k],
              posted := L.posted ++ [ackPacket k] } :=
      .spawnIn hu hn hr hc
    obtain ⟨hw', htake, peer'⟩ := peer.taken
      (v' := { v with
            cfg := ⟨v.cfg.procs ++ [⟨child, hs⟩], v.cfg.names⟩,
            sent := v.sent ++ [ackPacket k], inbox := rest, fixed := true, log := .spawnIn k :: v.log })
      (L' := { L with
            procs := L.procs ++ [⟨child, hs⟩], took := L.took ++ [k],
            posted := L.posted ++ [ackPacket k] })
      (Nat.le_refl _) ⟨[ackPacket k], rfl⟩ (fun _ _ h => h) rfl hfresh (me.out_asked peer hm hout hfresh)
    refine ⟨[(.spawnIn k, .arr [.nat 0, .nat k, prog, start, .arr held])], _,
      W ++ [.arr [.nat 0, .nat k, prog, start, .arr held]], { h with n := h.n + 1 }, hw',
      .cons hstep .nil, .cons (by simp [Note.own, Half.own]) htake .nil, ?_, peer'⟩
    exact { me with
      log := by simp [me.log]
      procs := by
        show L.procs ++ [⟨child, hs⟩] = v.cfg.procs ++ [⟨child, hs⟩]
        rw [me.procs]
      took := by simp [me.took, List.filterMap_append, Note.taking]
      posted := hstep.posted me.posted (by intro k' hk'; cases hk'; exact hfresh)
      sent := me.sent_snoc peer _
      split := ⟨rest0, hsp, hgot⟩
      link := link_snoc me.link (fun _ h => List.mem_append_left _ h)
        (by intro k' hk'; cases hk'; exact ⟨peer.posted.out_of hm hout, by simp⟩)
      pend := by
        intro p hp
        obtain ⟨hpw, hpt⟩ := me.pend p hp
        refine ⟨List.mem_append_left _ hpw, ?_⟩
        intro hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact hpt hmem
        · simp only [List.mem_singleton] at hmem
          have h1 := peer.posted.out_of (me.sub hpw) (⟨1, _, rfl, by decide⟩ : IsOut p.k p.pkt)
          rw [hmem, peer.posted.out_of hm hout] at h1
          simp [Pending.pkt] at h1
      acked := fun k' hk' hno => List.mem_append_left _ (me.acked k' hk' hno)
      unacked := by
        intro a ha hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact me.unacked a ha hmem
        · simp [ackPacket] at hmem
      acks := by
        show acksOf (Note.spawnIn k :: v.log).reverse = _
        rw [List.reverse_cons, acksOf_append, me.acks, List.filterMap_append]
        simp [acksOf, hout.no_ack]
      batches := me.batches_snoc _
      hn := by
        show h.n + 1 = (L.procs ++ [(⟨child, hs⟩ : Proc MValue MOutcome)]).length
        simp [me.hn] }
  | @sendIn p j c pl held' st extra hp hj free hrecv ht hx hv =>
    subst hv
    refine Out.counted (v₁ := { v with
          cfg := ⟨v.cfg.procs.set j ⟨st, gain held' p.held⟩, v.cfg.names⟩,
          sent := v.sent ++ [ackPacket p.k], pending := v.pending.filter (·.k != p.k),
          log := .sendIn p.k j :: v.log }) ?_ hx
    obtain ⟨hpw, hfresh⟩ := me.pend p hp
    have hm := me.sub hpw
    have hout : IsOut p.k p.pkt := ⟨1, _, rfl, by decide⟩
    have hstep : SideStep v.cells v.budget sd L
        (.sendIn p.k j, .arr [.nat 1, .nat p.k, .nat p.name, p.message, .arr (p.held.map .nat)])
        { L with
              procs := L.procs.set j ⟨st, gain held' p.held⟩, took := L.took ++ [p.k],
              posted := L.posted ++ [ackPacket p.k] } :=
      .sendIn (packetNats_map p.held) (by rw [me.procs]; exact hj)
        (by rw [Local.held, me.asked, List.any_map]; exact free) hrecv ht
    have hlt : j < h.n := by rw [me.hn, me.procs]; exact lt_of_getElem? hj
    obtain ⟨hw', htake, peer'⟩ := peer.taken
      (v' := { v with
            cfg := ⟨v.cfg.procs.set j ⟨st, gain held' p.held⟩, v.cfg.names⟩,
            sent := v.sent ++ [ackPacket p.k], pending := v.pending.filter (·.k != p.k),
            log := .sendIn p.k j :: v.log })
      (L' := { L with
            procs := L.procs.set j ⟨st, gain held' p.held⟩, took := L.took ++ [p.k],
            posted := L.posted ++ [ackPacket p.k] })
      (Nat.le_refl _) ⟨[ackPacket p.k], rfl⟩ (fun _ _ h => h) rfl hfresh (me.out_asked peer hm hout hfresh)
    refine ⟨[(.sendIn p.k j, p.pkt)], _, W, h, hw', .cons hstep .nil,
      .cons (by simp [Note.own, Half.own, Half.free, hlt, me.not_held free]) htake .nil, ?_, peer'⟩
    exact { me with
      log := by simp [me.log]
      procs := by
        show L.procs.set j ⟨st, gain held' p.held⟩ = v.cfg.procs.set j ⟨st, gain held' p.held⟩
        rw [me.procs]
      took := by simp [me.took, List.filterMap_append, Note.taking]
      posted := hstep.posted me.posted (by intro k' hk'; cases hk'; exact hfresh)
      sent := me.sent_snoc peer _
      link := link_snoc me.link (fun _ h => h)
        (by intro k' hk'; cases hk'; exact ⟨peer.posted.out_of hm hout, hpw⟩)
      pend := by
        intro q hq
        obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
        obtain ⟨hqw, hqt⟩ := me.pend q hq1
        refine ⟨hqw, ?_⟩
        intro hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact hqt hmem
        · simp only [List.mem_singleton] at hmem
          simp [hmem] at hq2
      acks := by
        show acksOf (Note.sendIn p.k j :: v.log).reverse = _
        rw [List.reverse_cons, acksOf_append, me.acks]
        simp [acksOf]
      batches := me.batches_snoc _
      hn := by
        show h.n = (L.procs.set j ⟨st, gain held' p.held⟩).length
        simp [me.hn] }
  | @ack k rest a q extra hin ha hk hq hx hv =>
    subst hv
    subst hk
    refine Out.counted (v₁ := { v with
          cfg := ⟨v.cfg.procs.set a.place ⟨a.next, q.held⟩, v.cfg.names⟩,
          asked := v.asked.filter (·.k != a.k), inbox := rest, fixed := true,
          log := .ack a.k a.place :: v.log }) ?_ hx
    obtain ⟨hm, hnw⟩ := me.head peer.posted.nodup hin
    obtain ⟨rest0, hsp, hgot⟩ := me.pop hin
    have hmem : a.ask ∈ L.asked := by rw [me.asked]; exact List.mem_map_of_mem ha
    have hstep : SideStep v.cells v.budget sd L (.ack a.k a.place, .arr [])
        { L with
              procs := L.procs.set a.place ⟨a.next, q.held⟩,
              asked := L.asked.filter (·.k != a.k) } :=
      .ack hmem rfl rfl (by rw [me.procs]; exact hq)
    have htk : a.k ∈ M.took := peer.posted.took_of hm
    obtain ⟨st, hst, htaken, _⟩ := me.live a ha
    have hst' := htaken htk
    subst hst'
    have hlt : a.place < h.n := by rw [me.hn, me.procs]; exact lt_of_getElem? hq
    refine ⟨[(.ack a.k a.place, .arr [])], _, W ++ [ackPacket a.k],
      { h with outs := h.outs.set a.k ⟨a.place, .acked⟩ }, hw, .cons hstep .nil,
      .cons (by simp [Note.own, Half.own, hst, hlt]) rfl .nil, ?_, still rfl rfl rfl rfl⟩
    exact { me with
      log := by simp [me.log]
      procs := by
        show L.procs.set a.place ⟨a.next, q.held⟩ = v.cfg.procs.set a.place ⟨a.next, q.held⟩
        rw [me.procs]
      asked := by
        show L.asked.filter (·.k != a.k) = (v.asked.filter (·.k != a.k)).map Asked.ask
        rw [me.asked, List.filter_map]
        rfl
      took := by simp [me.took, List.filterMap_append, Note.taking]
      posted := hstep.posted me.posted (by intro k hk; cases hk)
      split := ⟨rest0, hsp, hgot⟩
      link := link_snoc me.link (fun _ h => List.mem_append_left _ h) (by intro k hk; cases hk)
      pend := fun p hp => ⟨List.mem_append_left _ (me.pend p hp).1, (me.pend p hp).2⟩
      acked := by
        intro k hk hno
        by_cases he : k = a.k
        · subst he
          simp
        · refine List.mem_append_left _ (me.acked k hk ?_)
          intro a' ha' he'
          exact hno a' (List.mem_filter.mpr ⟨ha', by simp [he', he]⟩) he'
      unacked := by
        intro a' ha' hmem'
        obtain ⟨ha1, ha2⟩ := List.mem_filter.mp ha'
        rcases List.mem_append.mp hmem' with hmem' | hmem'
        · exact me.unacked a' ha1 hmem'
        · simp only [List.mem_singleton] at hmem'
          have := ackPacket_inj hmem'
          simp [this] at ha2
      acks := by
        show acksOf (Note.ack a.k a.place :: v.log).reverse = _
        rw [List.reverse_cons, acksOf_append, me.acks, List.filterMap_append]
        simp [acksOf, ackNum_ack]
      hn := by
        show h.n = (L.procs.set a.place ⟨a.next, q.held⟩).length
        simp [me.hn]
      hlen := by simp [me.hlen]
      live := by
        intro a' ha'
        obtain ⟨ha1, ha2⟩ := List.mem_filter.mp ha'
        have hne : a.k ≠ a'.k := by intro he; simp [he] at ha2
        obtain ⟨st', hst', h1, h2⟩ := me.live a' ha1
        refine ⟨st', ?_, h1, h2⟩
        show (h.outs.set a.k ⟨a.place, .acked⟩)[a'.k]? = _
        rw [List.getElem?_set_ne hne]
        exact hst'
      dead := by
        intro k c hc hno
        by_cases he : k = a.k
        · subst he
          have hc' : (h.outs.set a.k ⟨a.place, .acked⟩)[a.k]? = some c := hc
          rw [List.getElem?_set_self (lt_of_getElem? hst)] at hc'
          cases hc'
          rfl
        · have hc' : h.outs[k]? = some c := by
            have hc₀ : (h.outs.set a.k ⟨a.place, .acked⟩)[k]? = some c := hc
            rwa [List.getElem?_set_ne (fun h => he h.symm)] at hc₀
          refine me.dead k c hc' ?_
          intro a' ha' he'
          exact hno a' (List.mem_filter.mpr ⟨ha', by simp [he', he]⟩) he' }

end

end Surface.Cross
