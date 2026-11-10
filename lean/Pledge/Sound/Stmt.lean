import Pledge.Sound.Expr

namespace Pledge

mutual
theorem Term.close_append {ρ : List Value} (ρ' : List Value) :
    ∀ t : Term, t.entriesBelow ρ.length = true → t.close (ρ ++ ρ') = t.close ρ
  | .entry i, h => by
    simp only [Term.entriesBelow, decide_eq_true_eq] at h
    simp [Term.close, List.getElem?_append_left h]
  | .bound _, _ => rfl
  | .app _ as, h => by simp only [Term.close, Term.closeList_append ρ' as h]
theorem Term.closeList_append {ρ : List Value} (ρ' : List Value) :
    ∀ as : List Term, Term.entriesBelowList ρ.length as = true → Term.closeList (ρ ++ ρ') as = Term.closeList ρ as
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.entriesBelowList, Bool.and_eq_true] at h
    simp only [Term.closeList, Term.close_append ρ' a h.1, Term.closeList_append ρ' as h.2]
end

theorem Sig.close_append {ρ : List Value} (ρ' : List Value) {sig : Sig} (h : sig.entriesBelow ρ.length = true) :
    sig.close (ρ ++ ρ') = sig.close ρ := by
  simp only [Sig.entriesBelow, Bool.and_eq_true, List.all_eq_true] at h
  simp only [Sig.close, Term.close_append ρ' _ h.2, Sig.mk.injEq, and_true, true_and]
  refine List.map_congr_left fun b hb => ?_
  have hb' := h.1 b hb
  simp only [TBinder.entriesBelow, Bool.and_eq_true, Option.all_eq_true] at hb'
  simp only [TBinder.close, Term.close_append ρ' _ hb'.1, TBinder.mk.injEq, true_and]
  cases hi : b.is with
  | none => simp
  | some e => simp [Term.close_append ρ' e (hb'.2 e hi)]

theorem SigsOk.mono {n m : Nat} {S : Sigs} (hnm : n ≤ m) (h : SigsOk n S) : SigsOk m S := fun sig hs =>
  let ⟨h1, h2⟩ := h sig hs
  ⟨Sig.entriesBelow_mono hnm h1, h2⟩

theorem GlobalsOk.mono {n m phase : Nat} {gs : List Global} {fn : Option FnCtx} {S : Sigs} {W : World} {act : Act}
    (hnm : n ≤ m) (h : GlobalsOk n phase gs fn S W act) : GlobalsOk m phase gs fn S W act := by
  intro x g hg
  have := h x g hg
  match g, this with
  | .fn _ none, _ => trivial
  | .fn _ (some _), ⟨h1, h2, h3, h4, h5⟩ =>
    refine ⟨fun b hb => TBinder.entriesBelow_mono hnm (h1 b hb), fun b hb => TBinder.entriesBelow_mono hnm (h2 b hb),
      fun ρ' hρ' => h3 ρ' ?_, h4, h5⟩
    have := congrArg (List.take n) hρ'
    simpa [List.take_take, Nat.min_eq_left hnm] using this
  | .type .., h' => exact h'
  | .ctor _, h' => exact h'

theorem GoalBelow.mono {n m : Nat} {g : CheckedGoal} (hnm : n ≤ m) (h : GoalBelow n g) : GoalBelow m g := by
  unfold GoalBelow at h ⊢
  split at h
  · exact Term.entriesBelow_mono hnm _ h
  · exact fun b hb => TBinder.entriesBelow_mono hnm (h b hb)

theorem World.Le.extend (W : World) (ρ' : List Value) : W.Le { W with ρ := W.ρ ++ ρ' } :=
  ⟨Prog.Ext.refl _, Sigs.Sub.refl _, List.prefix_append _ _, fun _ _ _ _ _ h h' => (by
    simp only at h'; rw [h] at h'; cases h'), id⟩

theorem TopState.world_extend {st st' : TopState} {ρ : List Value} (ρ' : List Value)
    (hok : SigsOk ρ.length st.sc.sigs) (hs : st'.sc.sigs = st.sc.sigs) (hf : st'.fns = st.fns)
    (hg : st'.globals = st.globals) : st'.world (ρ ++ ρ') = { st.world ρ with ρ := ρ ++ ρ' } := by
  simp only [TopState.world, TopState.prog, hs, hf, hg, World.mk.injEq, and_true, true_and]
  exact List.map_congr_left fun sig hsig => Sig.close_append ρ' (hok sig hsig).1

theorem Act.top_group {F : Fns} {d : FnDef} (h : d ∈ F) : d.group < (Act.top F).group := by
  simp only [Act.top]
  induction F with
  | nil => cases h
  | cons e F ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem TopInv.sigsClose {st : TopState} {ρ : List Value} (hI : TopInv st ρ) :
    SigsClose st.sc.sigs ρ (st.world ρ).Sc :=
  SigsClose.close hI.noRemoved

/-- Top-level code in an untainted scope is checked under the main lemma's invariant, in the world of the state. -/
theorem TopInv.inv {st : TopState} {ρ : List Value} {C : Ctx} (hI : TopInv st ρ) (ht : st.sc.taintedBy = none)
    (hph : C.phase = st.phase) (hgl : C.globals = st.globals) (hfn : C.fn = none) :
    Inv C st.sc st.sc.Γ.length (st.world ρ) ρ (Act.top st.fns) := by
  have hL := hI.live ht
  refine ⟨hI.holes, ht, hL.sat, by simp [TopState.world, hI.len], rfl, fun ρ' hρ' => ?_, hI.sigsOk, ?_,
    hL.names, ?_, fun f hf => by simp [hfn] at hf⟩
  · refine hI.sigsClose.of_entriesBelow (n := st.sc.Γ.length) ?_ fun sig hs => (hI.sigsOk sig hs).1
    simpa [TopState.world] using hρ'.symm
  · simp [TopState.world, Sigs.find_map_close, hI.noJunk]
  · rw [hgl, hfn, hph]
    exact hL.globals _ (World.Le.refl _) _ fun d hd => Act.top_group hd

namespace TopStmt

mutual
theorem eval_noRemoved {ρ : List Value} (hρ : ∀ v ∈ ρ, v.noRemoved = true) :
    ∀ (t : Term) {v : Value}, t.eval ρ [] = some v → v.noRemoved = true
  | .entry _, _, h => by simp only [Term.eval] at h; exact hρ _ (List.mem_of_getElem? h)
  | .bound _, _, h => by simp [Term.eval] at h
  | .app _ as, _, h => by
    obtain ⟨vs, hvs, rfl⟩ := Term.eval_app.1 h
    exact evalList_noRemoved hρ as hvs
theorem evalList_noRemoved {ρ : List Value} (hρ : ∀ v ∈ ρ, v.noRemoved = true) :
    ∀ (as : List Term) {vs : List Value}, Term.evalList ρ [] as = some vs → Value.noRemovedList vs = true
  | [], _, h => by cases h; rfl
  | a :: as, _, h => by
    obtain ⟨v, vs, hv, hvs, rfl⟩ := Term.evalList_cons_eq_some.1 h
    simp only [Value.noRemovedList, eval_noRemoved hρ a hv, evalList_noRemoved hρ as hvs, Bool.and_self]
end

theorem none_of {a b : Option Pos} (h : a.isSome → b.isSome) (hb : b = none) : a = none := by
  cases a <;> simp_all

theorem world_eq {st st' : TopState} {ρ : List Value} (ρ' : List Value) (hI : TopInv st ρ)
    (hs : st'.sc.sigs = st.sc.sigs) (hf : st'.fns = st.fns) (hg : st'.globals = st.globals) :
    st'.world (ρ ++ ρ') = { st.world ρ with ρ := ρ ++ ρ' } :=
  TopState.world_extend ρ' (by rw [hI.len]; exact hI.sigsOk) hs hf hg

/-- A top-level item that keeps the signatures, globals, functions, groups and goal keeps the invariant for the
valuation extended by `ρ'`, given the new scope's shape and, when it is untainted, the main lemma's invariant and a
related environment. -/
theorem step {st st' : TopState} {ρ ρ' : List Value} (hI : TopInv st ρ) (hs : st'.sc.sigs = st.sc.sigs)
    (hph : st'.phase = st.phase) (hgl : st'.globals = st.globals) (hf : st'.fns = st.fns)
    (hgr : st'.groups = st.groups) (hgoal : st'.goal = st.goal) (hh : st'.sc.holes = [])
    (hlen : (ρ ++ ρ').length = st'.sc.Γ.length) (hnr : ∀ v ∈ ρ', v.noRemoved = true)
    (htaint : st.sc.taintedBy.isSome → st'.sc.taintedBy.isSome)
    (hpr : st'.proved = true → ∃ g, st'.goal = some g ∧ ∀ W', (st.world ρ).Le W' →
      GoalHolds W' st'.phase g st'.qedFn)
    (hlive : st'.sc.taintedBy = none → st.sc.taintedBy = none →
      (∃ C n0 act, Inv C st'.sc n0 (st.world ρ) (ρ ++ ρ') act) ∧
      EnvRel (st.world ρ).Sc st.phase st'.sc (ρ ++ ρ') st'.env) :
    (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  have hw := world_eq ρ' hI hs hf hgl
  have hle : (st.world ρ).Le (st'.world (ρ ++ ρ')) := by rw [hw]; exact World.Le.extend _ ρ'
  have hn : st.sc.Γ.length ≤ st'.sc.Γ.length := by
    have := hI.len; simp only [List.length_append] at hlen; omega
  refine ⟨hle, hlen, fun v hv => (List.mem_append.1 hv).elim (hI.noRemoved v) (hnr v), hh,
    by rw [hs]; exact hI.sigsOk.mono hn, by rw [hs]; exact hI.noJunk, by rw [hs]; exact hI.rets,
    by rw [hs, hgl]; exact hI.sigNames, by rw [hf, hgl]; exact hI.fnNames, by rw [hf, hgr]; exact hI.groups,
    by rw [hs]; exact hI.typeSig, fun g hg => ?_, fun hp => ?_, fun ht' => ?_⟩
  · obtain ⟨h1, h2⟩ := hI.goal g (by rw [← hgoal]; exact hg)
    exact ⟨h1.mono hn, fun ht' => h2 (none_of htaint ht')⟩
  · obtain ⟨g, hg, hh⟩ := hpr hp
    exact ⟨g, hg, fun W' hW => hh W' (hle.trans hW)⟩
  · have ht := none_of htaint ht'
    obtain ⟨⟨C, n0, act, hI'⟩, hE⟩ := hlive ht' ht
    refine ⟨by rw [hw]; exact hI'.sat, by rw [hw]; exact hI'.names, by rw [hw, hph]; exact hE,
      fun W' hW act' hact => ?_⟩
    rw [hph, hgl, hs]
    exact ((hI.live ht).globals W' (hle.trans hW) act' (hf ▸ hact)).mono hn

/-- `step` once the scope is tainted, the new entries taking `junk` values (§12). -/
theorem tainted {st st' : TopState} {ρ : List Value} (hI : TopInv st ρ) (hs : st'.sc.sigs = st.sc.sigs)
    (hph : st'.phase = st.phase) (hgl : st'.globals = st.globals) (hf : st'.fns = st.fns)
    (hgr : st'.groups = st.groups) (hgoal : st'.goal = st.goal) (hh : st'.sc.holes = [])
    (hpre : st.sc.Γ.eraseRules <+: st'.sc.Γ.eraseRules) (ht : st'.sc.taintedBy.isSome)
    (hpr : st'.proved = true → ∃ g, st'.goal = some g ∧ ∀ W', (st.world ρ).Le W' →
      GoalHolds W' st'.phase g st'.qedFn) :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  have hn : st.sc.Γ.length ≤ st'.sc.Γ.length := by simpa [Entries.eraseRules] using hpre.length_le
  exact ⟨List.replicate (st'.sc.Γ.length - st.sc.Γ.length) (Value.junk Value.TYPE),
    step hI hs hph hgl hf hgr hgoal hh (by simp [hI.len]; omega)
      (fun v hv => by rw [List.eq_of_mem_replicate hv]; rfl) (fun _ => ht) hpr fun ht' => by simp [ht'] at ht⟩

theorem keepProved {st st' : TopState} {ρ : List Value} (hI : TopInv st ρ) (hp : st'.proved = st.proved)
    (hg : st'.goal = st.goal) (hq : st'.qedFn = st.qedFn) (hph : st'.phase = st.phase) :
    st'.proved = true → ∃ g, st'.goal = some g ∧ ∀ W', (st.world ρ).Le W' → GoalHolds W' st'.phase g st'.qedFn := by
  rw [hp, hg, hq, hph]; exact hI.proved

/-- `step` in an untainted scope, from the main lemma's invariant for it. -/
theorem stepInv {st st' : TopState} {ρ ρ' : List Value} {C : Ctx} {n0 : Nat} {act : Act} (hI : TopInv st ρ)
    (hs : st'.sc.sigs = st.sc.sigs) (hph : st'.phase = st.phase) (hgl : st'.globals = st.globals)
    (hf : st'.fns = st.fns) (hgr : st'.groups = st.groups) (hgoal : st'.goal = st.goal) (hh : st'.sc.holes = [])
    (htaint : st.sc.taintedBy.isSome → st'.sc.taintedBy.isSome)
    (hpr : st'.proved = true → ∃ g, st'.goal = some g ∧ ∀ W', (st.world ρ).Le W' →
      GoalHolds W' st'.phase g st'.qedFn)
    (hI' : Inv C st'.sc n0 (st.world ρ) (ρ ++ ρ') act)
    (hE : st.sc.taintedBy = none → EnvRel (st.world ρ).Sc st.phase st'.sc (ρ ++ ρ') st'.env) :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') :=
  ⟨ρ', step hI hs hph hgl hf hgr hgoal hh hI'.sat.1.1 (fun v hv => hI'.sat.noRemoved v (List.mem_append_right _ hv))
    htaint hpr fun _ ht => ⟨⟨C, n0, act, hI'⟩, hE ht⟩⟩

end TopStmt

/-- A top-level statement other than a `comptime` pattern `let` keeps the invariant for the valuation extended by
ideal values of its new entries (§11, §12): in an untainted scope by `Stmt.sound`, the run giving the new
environment; in a tainted one, by any values, nothing being run. -/
theorem topStmt_sound {st st' : TopState} {ρ : List Value} {s : Stmt} (hI : TopInv st ρ) (hp : s.holeFree = true)
    (hc : ∀ p m pat rhs, s ≠ .patlet p true m pat rhs) (h : topItem st (.stmt s) = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  have hst : topItem st (.stmt s) = (do
      let o ← checkStmt st.ctx st.sc s
      let env ← keep o.snaps (if o.sc.taintedBy.isSome then pure st.env else st.run o.tree)
      pure { st with sc := o.sc, env := env, snaps := st.snaps ++ o.snaps } : CheckM TopState) := by
    cases s with
    | patlet p ct m pat rhs =>
      cases ct
      · rfl
      · exact absurd rfl (hc p m pat rhs)
    | _ => rfl
  rw [hst] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
  obtain ⟨env, henv, h⟩ := bind_eq_ok.1 h
  cases h
  rw [keep_ok] at henv
  obtain ⟨hsig, hh, hpre, htnt⟩ := Stmt.shape s hp st.ctx st.sc o hI.holes ho
  cases hto : o.sc.taintedBy with
  | some q =>
    rw [hto] at henv
    simp only [Option.isSome_some, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at henv
    subst henv
    exact TopStmt.tainted hI hsig rfl rfl rfl rfl rfl hh hpre (by simp [hto])
      (TopStmt.keepProved hI rfl rfl rfl rfl)
  | none =>
    rw [hto] at henv
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at henv
    have ht := TopStmt.none_of htnt hto
    obtain ⟨ρ', hI', hrun⟩ := Stmt.sound s hp _ _ _ _ _ _ _ (hI.inv (C := st.ctx) ht rfl rfl rfl) ho hto
    obtain ⟨env', hev, hE⟩ := hrun rfl st.env (hI.live ht).env
    cases EvalStmt.det (TopState.run_cert henv) hev
    exact TopStmt.stepInv hI hsig rfl rfl rfl rfl rfl hh htnt (TopStmt.keepProved hI rfl rfl rfl rfl) hI'
      fun _ => hE

namespace TopStmt

theorem bind_fields (s : Scope) (ids : List Id) (rs : List Res) : (s.bind ids rs).sigs = s.sigs ∧
    (s.bind ids rs).Γ = s.Γ ∧ (s.bind ids rs).holes = s.holes ∧ (s.bind ids rs).taintedBy = s.taintedBy := by
  rw [Scope.bind_eq]; exact ⟨rfl, rfl, rfl, rfl⟩

/-- A forcing only adds entries and rules to the scrutinee's scope. -/
theorem forcings_prefix {C : Ctx} {sc : Scope} {t : Term} {sp at_ : Pos} {pats : List Pattern} {erased : Bool}
    {fs : List Forcing} {f : Forcing} {Γ : Entries} {ids : List Nat} (h : forcings C sc t sp pats at_ erased = .ok fs)
    (hf : f ∈ fs) (hfo : f.forced = .ok Γ ids) : sc.Γ.eraseRules <+: Γ.eraseRules := by
  obtain ⟨_, -, -, -, hfs⟩ := forcings_spec h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
  obtain ⟨sig, mk, -, hforced, -⟩ := hfs i _ (List.getElem?_eq_getElem hi)
  rw [hfo] at hforced
  exact (force_eraseRules hforced.symm).2.1

end TopStmt

/-- A `comptime` pattern `let` (§11) keeps the invariant: with an untainted scrutinee, the run's value, related to
the ideal one, is headed by the pattern's value constructor, so the ideal value is too and its forcing survived. -/
theorem comptimeLet_sound {st st' : TopState} {ρ : List Value} {p : Pos} {m : Option Mult} {pat : Pattern}
    {rhs : Expr} (hI : TopInv st ρ) (hp : rhs.holeFree = true) (h : comptimeLet st p m pat rhs = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  unfold comptimeLet at h
  simp only at h
  split at h
  · simp [failAt_eq, bind, Except.bind] at h
  rename_i hm
  obtain ⟨-, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
  rw [keep_ok] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
  obtain ⟨fs, hfs, h⟩ := bind_eq_ok.1 h
  obtain ⟨v', hv', h⟩ := bind_eq_ok.1 h
  obtain ⟨hsig0, hnm, hh0, hpre0, htnt⟩ := Expr.shape rhs hp _ st.sc none o hI.holes ho
  have hT : ∀ sc, patBind o.sc r rhs.pos true pat fs = .ok sc → sc.taintedBy.isSome →
      ∃ ρ', (st.world ρ).Le (({ st with sc, env := st.env, snaps := st.snaps ++ o.snaps } : TopState).world
        (ρ ++ ρ')) ∧ TopInv { st with sc, env := st.env, snaps := st.snaps ++ o.snaps } (ρ ++ ρ') := by
    intro sc hsc hts
    obtain ⟨Γ, ids, ⟨f, hf, hfo⟩, -, rfl⟩ := patBind_spec hsc
    obtain ⟨h1, h2, h3, -⟩ := TopStmt.bind_fields { o.sc with Γ, taintedBy := reach o.sc r rhs.pos } pat.fields
      (fieldRes ids)
    exact TopStmt.tainted hI (h1.trans hsig0) rfl rfl rfl rfl rfl (h3.trans hh0)
      (by rw [h2]; exact hpre0.trans (TopStmt.forcings_prefix hfs (List.mem_of_find?_eq_some hf) hfo)) hts
      (TopStmt.keepProved hI rfl rfl rfl rfl)
  have hU : ∀ sc v env, patBind o.sc r rhs.pos true pat fs = .ok sc → sc.taintedBy = none → v' = some v →
      v.headName = pat.ctor.name → bindPattern st.env m pat v = .ok env →
      ∃ ρ', (st.world ρ).Le (({ st with sc, env, snaps := st.snaps ++ o.snaps } : TopState).world (ρ ++ ρ')) ∧
        TopInv { st with sc, env, snaps := st.snaps ++ o.snaps } (ρ ++ ρ') := by
    intro sc v env hsc hts hv hhead henv
    obtain ⟨Γ, ids, ⟨f, hf, hfo⟩, -, rfl⟩ := patBind_spec hsc
    obtain ⟨h1, h2, h3, h4⟩ := TopStmt.bind_fields { o.sc with Γ, taintedBy := reach o.sc r rhs.pos } pat.fields
      (fieldRes ids)
    have htb : reach o.sc r rhs.pos = none := h4.symm.trans hts
    have hto : o.sc.taintedBy = none := by
      cases h : o.sc.taintedBy
      · rfl
      · simp [reach, h] at htb
    have hrt : r.tainted = false := by simpa [reach, hto] using htb
    have ht := TopStmt.none_of htnt hto
    obtain ⟨ρ₁, vs, hI₁, hvs, hres, -, hrun⟩ :=
      (Expr.sound rhs hp _ _ _ _ _ _ _ _ (hI.inv ht rfl rfl rfl) (fun _ h => by cases h) ho).1 hto
    have hor := single_ok hr
    rw [hor] at hvs hres
    obtain ⟨vi, hvi, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs)
    obtain ⟨-, -, hV⟩ := hres 0 r vi rfl rfl
    obtain ⟨V, hV⟩ := hV hrt
    rw [hrt] at hv'
    obtain ⟨v'', rfl, hcert⟩ := TopState.eval_cert hv'
    cases hv
    obtain ⟨us, hev, us', htk, hrel⟩ := hrun st.env (hI.live ht).env
    cases Eval.det hev hcert
    rw [take_of_length (by rw [hor]; rfl)] at htk
    cases htk
    have hR : Rel (st.world ρ).Sc st.phase v vi := by
      have := hrel 0 r v vi (by rw [hor]; rfl) rfl rfl hrt
      simpa [Ctx.posMult, TopState.ctx, MultRel] using this
    obtain ⟨c, ws, sig, Γ', ids', pat', rfl, hfc, hsig, hws, hsat, hpre, -, hids, -, hent⟩ :=
      forcings_value hI₁ hfs hvi hV
    obtain ⟨as, rfl⟩ : ∃ as, v = .app ⟨.ctor, c⟩ as := by cases hR; exact ⟨_, rfl⟩
    simp only [Value.headName] at hhead
    subst hhead
    rw [hfc] at hf
    cases hf
    have hfo' : Γ' = Γ ∧ ids' = ids := by injection hfo with e1 e2; exact ⟨e1, e2⟩
    rw [hfo'.1] at hsat hpre hent
    rw [hfo'.2] at hids
    have hI₃ := Inv.pattern (fields := pat.fields) hI₁ hsat hids hws htb hh0
    have hfl := forcings_fields hfs (List.mem_singleton_self _) hsig hws
    obtain ⟨sig', hsig', hmult⟩ := SigsClose.mults (hI₁.sigs _ hI₁.agree) hsig
    have hent' : ∀ (k : Nat) (b' : TBinder), sig'.params[k]? = some b' → ∃ en, Γ[o.sc.Γ.length + k]? = some en ∧
        en.erased = (b'.mult == .erased || m == some .erased) := by
      intro k b' hb'
      have : (sig.params.map (·.mult))[k]? = some b'.mult := by rw [← hmult]; simp [hb']
      simp only [List.getElem?_map, Option.map_eq_some_iff] at this
      obtain ⟨b, hb, hbm⟩ := this
      obtain ⟨en, hen, -, her⟩ := hent k b hb
      refine ⟨en, hen, ?_⟩
      simp only [Bool.not_eq_true] at hm
      rw [her, hbm, hm]
    obtain ⟨env', hb, hE⟩ := EnvRel.pattern (tb := reach o.sc r rhs.pos) (hs := o.sc.holes)
      (EnvRel.extend ρ₁ (hI.live ht).env hnm hpre0 hI.len) hI₁.sat.1.1 hpre hids hfl hsig' hent' (fun _ => hR) rfl
      (by rw [hws.length_eq]; simpa using (congrArg List.length hmult).symm)
    rw [henv] at hb
    cases hb
    rw [List.append_assoc] at hI₃ hE
    exact TopStmt.stepInv hI (h1.trans hsig0) rfl rfl rfl rfl rfl (h3.trans hh0) (fun h => by simp [ht] at h)
      (TopStmt.keepProved hI rfl rfl rfl rfl) hI₃ fun _ => hE
  cases v' with
  | none =>
    simp only at h
    obtain ⟨sc, hsc, h⟩ := bind_eq_ok.1 h
    split at h
    · cases h; exact hT sc hsc ‹_›
    · rename_i hts
      obtain ⟨Γ, ids, -, -, rfl⟩ := patBind_spec hsc
      have htb := (TopStmt.bind_fields { o.sc with Γ, taintedBy := reach o.sc r rhs.pos } pat.fields
        (fieldRes ids)).2.2.2
      have hrt : r.tainted = false := by
        cases hr' : r.tainted
        · rfl
        · have := htb.symm.trans (by simpa using hts)
          simp [reach, hr'] at this
      rw [hrt] at hv'
      obtain ⟨_, h', -⟩ := TopState.eval_cert hv'
      cases h'
  | some v =>
    simp only at h
    split at h
    · simp [failAt_eq, bind, Except.bind] at h
    rename_i hhead
    obtain ⟨sc, hsc, h⟩ := bind_eq_ok.1 h
    split at h
    · cases h; exact hT sc hsc ‹_›
    · rename_i hts
      split at h
      · rename_i env henv
        cases h
        exact hU sc v env hsc (by simpa using hts) rfl (by simpa using hhead) henv
      · simp [failAt_eq, bind, Except.bind] at h

/-- `print` keeps the invariant. -/
theorem print_sound {st st' : TopState} {ρ : List Value} {p : Pos} {e : Expr} (hI : TopInv st ρ)
    (hp : e.holeFree = true) (h : topItem st (.print p e) = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  simp only [topItem] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
  obtain ⟨v, -, h⟩ := bind_eq_ok.1 h
  cases h
  obtain ⟨hsig, hnm, hh, hpre, htnt⟩ := Expr.shape e hp _ st.sc none o hI.holes ho
  cases hto : o.sc.taintedBy with
  | some q =>
    exact TopStmt.tainted hI hsig rfl rfl rfl rfl rfl hh hpre (by simp [hto]) (TopStmt.keepProved hI rfl rfl rfl rfl)
  | none =>
    have ht := TopStmt.none_of htnt hto
    obtain ⟨ρ₁, -, hI₁, -⟩ := (Expr.sound e hp _ _ _ _ _ _ _ _ (hI.inv ht rfl rfl rfl) (fun _ h => by cases h) ho).1 hto
    exact TopStmt.stepInv hI hsig rfl rfl rfl rfl rfl hh htnt (TopStmt.keepProved hI rfl rfl rfl rfl) hI₁
      fun ht => EnvRel.extend ρ₁ (hI.live ht).env hnm hpre hI.len

theorem GoalBelow.type {n : Nat} {g : CheckedGoal} {t : Term} (h : GoalBelow n g) (hk : g.kind = .type t) :
    t.entriesBelow n = true := by
  unfold GoalBelow at h; rw [hk] at h; exact h

theorem GoalBelow.fn {n : Nat} {g : CheckedGoal} {ps rs : Telescope} (h : GoalBelow n g) (hk : g.kind = .fn ps rs) :
    ∀ b ∈ ps ++ rs, b.entriesBelow n = true := by
  unfold GoalBelow at h; rw [hk] at h; exact h

namespace TopStmt

theorem given_eq {goal : CheckedGoal} {t : Term} (hk : goal.kind = .type t) :
    goal.given =
      { wants := [⟨none, some t, none, .many⟩], whole := true, label := some fun _ => "the goal's proof" } := by
  simp [CheckedGoal.given, hk]

/-- What a type goal's `qed` is given, in an untainted scope: the goal's type has a value. -/
theorem given_ok {st : TopState} {ρ : List Value} {goal : CheckedGoal} {t : Term} (hI : TopInv st ρ)
    (ht : st.sc.taintedBy = none) (hgoal : st.goal = some goal) (hk : goal.kind = .type t) :
    goal.given.Ok (st.world ρ).Sc ρ := by
  have hb := (hI.goal goal hgoal).1.type hk
  obtain ⟨A, hA⟩ := Term.eval_isSome (env := []) t (by rw [hI.len]; exact hb) ((hI.goal goal hgoal).2 ht t hk)
  rw [given_eq hk]
  refine ⟨⟨[], rfl⟩, fun _ envv henv => ?_⟩
  cases henv
  exact ⟨fun T hT => by cases hT; exact ⟨A, hA, eval_noRemoved (hI.live ht).sat.noRemoved t hA⟩,
    fun e he => (by cases he), fun _ _ => trivial⟩

end TopStmt

/-- `qed e;` against a type goal (§12): if it proves the goal, `e`'s untainted result has an ideal value of the goal's
type, in an untainted scope. -/
theorem typeQed_sound {st st' : TopState} {ρ : List Value} {p : Pos} {e : Expr} {goal : CheckedGoal} {t : Term}
    (hI : TopInv st ρ) (hp : e.holeFree = true) (hgoal : st.goal = some goal) (hk : goal.kind = .type t)
    (h : (do
        let o ← checkExpr st.ctx st.sc (some goal.given) e
        let _ ← keep o.snaps (st.eval p o.tree (o.res.any fun x => x.tainted))
        let st ← pure { st with sc := o.sc, proved := !o.res.any fun x => x.tainted, snaps := st.snaps ++ o.snaps }
        pure { st with qedChecks := true, proved := st.proved && st.sc.taintedBy.isNone && !goal.tainted } :
        CheckM TopState) = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
  obtain ⟨-, -, h⟩ := bind_eq_ok.1 h
  cases h
  obtain ⟨hsig, hnm, hh, hpre, htnt⟩ := Expr.shape e hp _ st.sc _ o hI.holes ho
  cases hto : o.sc.taintedBy with
  | some q =>
    exact TopStmt.tainted hI hsig rfl rfl rfl rfl rfl hh hpre (by simp [hto]) fun hpr => by simp at hpr
  | none =>
    have ht := TopStmt.none_of htnt hto
    obtain ⟨ρ₁, vs, hI₁, -, -, hw, -⟩ := (Expr.sound e hp _ _ _ _ _ _ _ _ (hI.inv ht rfl rfl rfl)
      (fun g' hg' => by cases hg'; exact TopStmt.given_ok hI ht hgoal hk) ho).1 hto
    refine TopStmt.stepInv hI hsig rfl rfl rfl rfl rfl hh htnt (fun hpr => ⟨goal, hgoal, fun W' hW => ?_⟩) hI₁
      fun ht => EnvRel.extend ρ₁ (hI.live ht).env hnm hpre hI.len
    have hall : (o.res.any fun x => x.tainted) = false := by simp_all
    have hws := hw _ rfl [] (by rw [TopStmt.given_eq hk]; rfl)
    rw [TopStmt.given_eq hk] at hws
    obtain ⟨v, hv⟩ : ∃ v, WantSat (st.world ρ).Sc (ρ ++ ρ₁) ⟨none, some t, none, .many⟩ [] true v := by
      generalize o.res = rs at hall hws
      rcases rs with _ | ⟨r, rs⟩ <;> rcases vs with _ | ⟨v, vs⟩
      all_goals first | exact hws.elim | skip
      have hr : r.tainted = false := by simp_all
      exact ⟨v, by simpa [hr] using hws.1⟩
    obtain ⟨A, hA, -, -, hvA⟩ := hv.1 t rfl
    have hb := (hI.goal goal hgoal).1.type hk
    have hρ : (ρ ++ ρ₁).take st.sc.Γ.length = W'.ρ.take st.sc.Γ.length := by
      rw [hW.take_of_le (by simp [TopState.world, hI.len])]
      simp [TopState.world, ← hI.len]
    simp only [GoalHolds, hk]
    exact ⟨v, A, by rw [← Term.eval_entriesBelow hρ [] t hb, hA], (hvA rfl).mono_sigs hW.sigs⟩

/-- Telescopes with no `difference` agree by value, binder by binder, under a valuation satisfying the scope's rules,
multiplicities included. -/
theorem difference_agree {Γ : Entries} {ρ : List Value} (hΓ : RulesHold Γ ρ) :
    ∀ {Δ Δ' : Telescope}, difference Γ Δ Δ' = none → Telescope.Agree ρ ρ Δ Δ'
  | [], [], _ => trivial
  | ⟨xn, xt, xi, xm⟩ :: xs, ⟨yn, yt, yi, ym⟩ :: ys, h => by
    cases xi <;> cases yi <;> simp [difference] at h <;> split at h <;> try cases h
    · rename_i hc
      exact ⟨⟨fun env => identical.eval_eq hΓ hc.2, fun env => rfl, hc.1⟩, difference_agree hΓ (by simpa using h)⟩
    · rename_i hc
      exact ⟨⟨fun env => identical.eval_eq hΓ hc.2.1, fun env => by simp [identical.eval_eq hΓ hc.2.2], hc.1⟩,
        difference_agree hΓ (by simpa using h)⟩
  | [], _ :: _, h | _ :: _, [], h => by simp [difference] at h

theorem Telescope.Agree.append {ρ ρ' : List Value} : ∀ {Δ₁ Δ₁' Δ₂ Δ₂' : Telescope}, Δ₁.length = Δ₁'.length →
    Telescope.Agree ρ ρ' (Δ₁ ++ Δ₂) (Δ₁' ++ Δ₂') → Telescope.Agree ρ ρ' Δ₁ Δ₁' ∧ Telescope.Agree ρ ρ' Δ₂ Δ₂'
  | [], [], _, _, _, h => ⟨trivial, h⟩
  | _ :: _, _ :: _, _, _, hl, h =>
    let ⟨h1, h2⟩ := Telescope.Agree.append (by simpa using hl) h.2
    ⟨⟨h.1, h1⟩, h2⟩
  | [], _ :: _, _, _, hl, _ | _ :: _, [], _, _, hl, _ => by simp at hl

theorem TopStmt.mults {ρ ρ' : List Value} :
    ∀ {Δ Δ' : Telescope}, Telescope.Agree ρ ρ' Δ Δ' → Δ.map (·.mult) = Δ'.map (·.mult)
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨h, hs⟩ => by simp [h.mult, TopStmt.mults hs]
  | [], _ :: _, h | _ :: _, [], h => h.elim

/-- A function whose telescopes have no `difference` from a function goal's, and that is untainted, proves it in every
later world (§12): its specification gives the returns, and its run on related arguments related results. -/
theorem fnGoal_holds {st : TopState} {ρ : List Value} {g : CheckedGoal} {ps rs : Telescope} {n m : String}
    {sig : FnSig} {W' : World} (hI : TopInv st ρ) (hk : g.kind = .fn ps rs) (ht : st.sc.taintedBy = none)
    (hb : ∀ b ∈ ps ++ rs, b.entriesBelow st.sc.Γ.length = true)
    (hg : st.globals.find? (·.name == n) = some (.fn m (some sig))) (hst : sig.tainted = false)
    (hpl : sig.params.length = ps.length)
    (hd : difference st.sc.Γ (ps ++ rs) (sig.params ++ sig.returns) = none) (hW : (st.world ρ).Le W') :
    GoalHolds W' st.phase g (some n) := by
  have hF := ((hI.live ht).globals W' hW (Act.top st.fns) fun d hd => Act.top_group hd).fn hg
  obtain ⟨d, hdf, -, -, -, -, hcall, hgrp⟩ := hF.defn hst
  simp only [Option.any_none, Bool.false_eq_true, ↓reduceIte] at hgrp
  have hρ : W'.ρ.take st.sc.Γ.length = ρ.take st.sc.Γ.length := hW.take_of_le (by simp [TopState.world, hI.len])
  have hsig : ∀ b ∈ sig.params ++ sig.returns, b.entriesBelow st.sc.Γ.length = true := fun b hb' =>
    (List.mem_append.1 hb').elim (hF.params b) (hF.returns b)
  have hA : Telescope.Agree W'.ρ W'.ρ (ps ++ rs) (sig.params ++ sig.returns) :=
    ((Telescope.agree_of_entriesBelow hρ (List.all_eq_true.2 hb)).trans
      (difference_agree (hI.live ht).sat.rulesHold hd)).trans
      (Telescope.agree_of_entriesBelow hρ.symm (List.all_eq_true.2 hsig))
  obtain ⟨hA1, hA2⟩ := hA.append hpl.symm
  simp only [GoalHolds, hk]
  refine ⟨n, d, rfl, hdf, fun vs hvs => ?_⟩
  obtain ⟨ws, hws, hrun⟩ := hcall vs ((TeleSat.congr hA1).1 hvs) (Act.lt_of_group (by simpa [calleeAct] using hgrp))
  refine ⟨ws, (TeleSat.congr hA2).2 hws, fun as has => ?_⟩
  obtain ⟨ws', hc, hr⟩ := hrun as (by rwa [← TopStmt.mults hA1])
  exact ⟨ws', hc, by rwa [TopStmt.mults hA2]⟩

theorem qedFnGoal_spec {st st' : TopState} {ps rs : Telescope} {e : Expr} (h : qedFnGoal st ps rs e = .ok st') :
    ∃ n m sig, st.globals.find? (·.name == n) = some (.fn m (some sig)) ∧ sig.params.length = ps.length ∧
      sig.returns.length = rs.length ∧ difference st.sc.Γ (ps ++ rs) (sig.params ++ sig.returns) = none ∧
      st' = { st with qedFn := some n, proved := !sig.tainted } := by
  unfold qedFnGoal at h
  simp only at h
  split at h
  · rename_i n pos
    split at h
    · rename_i name sig hgl
      split at h
      · simp [failAt_eq, bind, Except.bind] at h
      · rename_i hlen
        split at h
        · simp [failAt_eq, bind, Except.bind] at h
        · rename_i hdiff
          simp only [pure, Except.pure, Except.ok.injEq] at h
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, ne_eq, Decidable.not_not] at hlen
          refine ⟨n, name, sig, hgl, hlen.1, hlen.2, ?_, h.symm⟩
          cases hd : difference st.sc.Γ (ps ++ rs) (sig.params ++ sig.returns) with
          | none => rfl
          | some i => exact (hdiff i hd).elim
    · simp [failAt_eq] at h
  · simp [failAt_eq] at h

/-- A `qed` keeps the invariant, and, if it proves the goal, the goal holds in every later world (§12). -/
theorem qed_sound {st st' : TopState} {ρ : List Value} {p : Pos} {e : Expr} (hI : TopInv st ρ)
    (hp : e.holeFree = true) (h : topItem st (.qed p e) = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  simp only [topItem] at h
  split at h
  · simp [failAt_eq, bind, Except.bind] at h
  split at h
  · rename_i goal hgoal
    split at h
    · rename_i ps rs hk
      obtain ⟨st₁, h₁, h⟩ := bind_eq_ok.1 h
      cases h
      obtain ⟨n, m, sig, hg, hpl, -, hd, rfl⟩ := qedFnGoal_spec h₁
      cases hto : st.sc.taintedBy with
      | some q =>
        exact TopStmt.tainted hI rfl rfl rfl rfl rfl rfl hI.holes (List.prefix_refl _) (by simp [hto])
          fun hpr => by simp at hpr
      | none =>
        have hI' : Inv st.ctx st.sc st.sc.Γ.length (st.world ρ) (ρ ++ []) (Act.top st.fns) := by
          rw [List.append_nil]; exact hI.inv hto rfl rfl rfl
        refine TopStmt.stepInv hI rfl rfl rfl rfl rfl rfl hI.holes id (fun hpr => ⟨goal, hgoal, fun W' hW =>
          fnGoal_holds (st := st) hI hk hto ((hI.goal goal hgoal).1.fn hk) hg ?_ hpl hd hW⟩) hI' fun ht => by
          rw [List.append_nil]; exact (hI.live ht).env
        revert hpr; cases sig.tainted <;> simp
    · rename_i t hk
      split at h
      · split at h
        · simp [failAt_eq, bind, Except.bind] at h
        · exact typeQed_sound hI hp hgoal hk h
      · exact typeQed_sound hI hp hgoal hk h
  · simp [failAt_eq] at h

end Pledge
