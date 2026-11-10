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
  let ⟨h1, h2, h3⟩ := h sig hs
  ⟨Sig.entriesBelow_mono hnm h1, h2, h3⟩

theorem GlobalsOk.mono {n m : Nat} {gs : List Global} {fn : Option FnCtx} {S : Sigs} {W : World} {act : Act}
    (hnm : n ≤ m) (h : GlobalsOk n gs fn S W act) : GlobalsOk m gs fn S W act := by
  intro x g hg
  have := h x g hg
  match g, this with
  | .fn _ none, _ => trivial
  | .fn _ (some _), ⟨h1, h2, h3, h4, h5⟩ =>
    exact ⟨h1, fun b hb => ⟨TBinder.entriesBelow_mono hnm (h2 b hb).1, (h2 b hb).2⟩,
      fun b hb => ⟨TBinder.entriesBelow_mono hnm (h3 b hb).1, (h3 b hb).2⟩, h4, h5⟩
  | .type .., h' => exact h'
  | .ctor _, h' => exact h'

theorem GoalBelow.mono {n m : Nat} {g : CheckedGoal} (hnm : n ≤ m) (h : GoalBelow n g) : GoalBelow m g := by
  unfold GoalBelow at h ⊢
  split at h
  · exact Term.entriesBelow_mono hnm _ h
  · exact fun b hb => TBinder.entriesBelow_mono hnm (h b hb)

theorem World.Le.extend (W : World) (ρ' : List Value) : W.Le { W with ρ := W.ρ ++ ρ' } :=
  ⟨Prog.Ext.refl _, Sigs.Sub.refl _, List.prefix_append _ _, fun _ _ _ _ _ h h' => by
    simp only at h'; rw [h] at h'; cases h'⟩

theorem TopState.world_extend {st st' : TopState} {ρ : List Value} (ρ' : List Value)
    (hok : SigsOk ρ.length st.sc.sigs) (hs : st'.sc.sigs = st.sc.sigs) (hf : st'.fns = st.fns)
    (hg : st'.globals = st.globals) : st'.world (ρ ++ ρ') = { st.world ρ with ρ := ρ ++ ρ' } := by
  simp only [TopState.world, TopState.prog, hs, hf, hg, World.mk.injEq, and_true, true_and]
  exact List.map_congr_left fun sig hsig => Sig.close_append ρ' (hok sig hsig).1

/-- A top-level item that changes only the scope, the environment and what is proved keeps the invariant, given
the main lemma's invariant for the new scope under an extended valuation. -/
theorem TopInv.step {st st' : TopState} {ρ ρ' : List Value} {C : Ctx} {act : Act} (hI : TopInv st ρ)
    (hI' : Inv C st'.sc st.sc.Γ.length (st.world ρ) (ρ ++ ρ') st'.env act) (hs : st'.sc.sigs = st.sc.sigs)
    (hph : st'.phase = st.phase) (hgl : st'.globals = st.globals) (hf : st'.fns = st.fns)
    (hgr : st'.groups = st.groups) (hgoal : st'.goal = st.goal)
    (hpr : st'.proved = true → ∃ g, st'.goal = some g ∧ ∀ W', (st.world ρ).Le W' → GoalHolds W' g) :
    (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  have hl : ρ.length = st.sc.Γ.length := hI.sat.1
  have hw := TopState.world_extend ρ' (hl ▸ hI.sigsOk) hs hf hgl
  have hle : (st.world ρ).Le (st'.world (ρ ++ ρ')) := by
    rw [hw]; simpa [TopState.world] using World.Le.extend (st.world ρ) ρ'
  have hn : st.sc.Γ.length ≤ st'.sc.Γ.length := by
    have := hI'.sat.1; simp only [List.length_append] at this; omega
  refine ⟨hle, ⟨hph ▸ hI.phase, by rw [hw]; exact hI'.sat, by rw [hw]; exact hI'.names, hI'.inert,
    hs ▸ hI.sigsOk.mono hn, hs ▸ hI.rets, hs ▸ hgl ▸ hI.sigNames, hf ▸ hgl ▸ hI.fnNames, hf ▸ hgr ▸ hI.groups,
    fun W' hW act' hact => ?_, fun g hg => ?_, fun hp => ?_, hs ▸ hI.typeSig⟩⟩
  · rw [hgl, hs]
    exact (hI.globals W' (hle.trans hW) act' (hf ▸ hact)).mono hn
  · obtain ⟨h1, h2⟩ := hI.goal g (hgoal ▸ hg)
    exact ⟨h1, h2.mono hn⟩
  · obtain ⟨g, hg, hh⟩ := hpr hp
    exact ⟨g, hg, fun W' hW => hh W' (hle.trans hW)⟩

theorem checkedStmt_sound {st st' : TopState} {ρ : List Value} {s : Stmt} (hI : TopInv st ρ)
    (hInv : Inv st.ctx st.sc st.sc.Γ.length (st.world ρ) ρ st.env (Act.top st.fns)) (hp : s.plain = true)
    (h : (do
      let o ← checkStmt st.ctx st.sc s
      let env ← keep o.snaps (if o.sc.taintedBy.isSome then pure st.env else st.run o.tree)
      pure { st with sc := o.sc, env := env, snaps := st.snaps ++ o.snaps } : CheckM TopState) = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
  obtain ⟨env, henv, h⟩ := bind_eq_ok.1 h
  cases h
  obtain ⟨hsigs, ρ', env', hev, hI'⟩ := Stmt.sound s hp _ _ _ _ _ _ _ o hInv ho
  rw [keep_ok, hI'.inert.taintedBy] at henv
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at henv
  cases EvalStmt.det (TopState.run_cert henv) hev
  exact ⟨ρ', TopInv.step hI hI' hsigs rfl rfl rfl rfl rfl hI.proved⟩

theorem comptimeLet_sound {st st' : TopState} {ρ : List Value} {p : Pos} {pat : Pattern} {rhs : Expr}
    (hI : TopInv st ρ) (hInv : Inv st.ctx st.sc st.sc.Γ.length (st.world ρ) ρ st.env (Act.top st.fns))
    (hp : rhs.plain = true) (h : comptimeLet st p none pat rhs = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  unfold comptimeLet at h
  simp only [reduceCtorEq, beq_iff_eq, ↓reduceIte] at h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
  rw [keep_ok] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
  obtain ⟨fs, hfs, h⟩ := bind_eq_ok.1 h
  obtain ⟨v', hv', h⟩ := bind_eq_ok.1 h
  obtain ⟨hsigs, hnames, hres, ρ₁, vs, hev, hI₁, hvs, hty, -⟩ :=
    Expr.sound rhs hp _ _ _ _ _ _ _ _ o hInv (by simp) ho
  rw [single_ok hr] at hvs hres
  obtain ⟨v, hv, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs)
  have hrt : r.tainted = false := (hres r (by simp)).1
  rw [hrt] at hv'
  obtain ⟨v'', rfl, hcert⟩ := TopState.eval_cert hv'
  obtain rfl : v = v'' := by simpa using Eval.det hev hcert
  simp only at h
  split at h
  · simp [failAt_eq, bind, Except.bind] at h
  rename_i hhead
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hhead
  obtain ⟨sc, hsc, h⟩ := bind_eq_ok.1 h
  obtain ⟨Γ, ids, ⟨f, hf, hfo⟩, -, rfl⟩ := patBind_spec hsc
  obtain ⟨V, hV⟩ := hty v (by simp)
  obtain ⟨c, ws, sig, Γ', ids', pat', rfl, hf', -, hws, hsat, hlen, hids, -⟩ := forcings_value hI₁ hfs hv hV
  simp only [Value.headName] at hhead
  subst hhead
  rw [hf] at hf'
  cases hf'
  cases hfo
  simp only [reach, hI₁.inert.taintedBy, hrt, Option.orElse, Bool.false_eq_true, ↓reduceIte, Scope.bind_eq,
    Option.isSome_none] at h
  split at h
  · rename_i env henv
    obtain ⟨-, hb⟩ := bindPattern_app.1 henv
    simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
    subst h
    have hl : o.sc.Γ.length = (ρ ++ ρ₁).length := hI₁.sat.1.symm
    have hI₂ := Inv.extend (sc' := { o.sc with Γ := Γ, taintedBy := none }) hI₁ hsat rfl rfl
      ⟨hI₁.inert.holes, rfl, hI₁.inert.names⟩
    have hI₃ := Inv.bind hI₂ (ids := pat.fields) (rs := fieldRes ids)
      (by rw [hids, hl]; exact (evalList_fieldRes rfl)) (TeleSat.hasType hws)
      (fun r hr => by simp only [fieldRes, List.mem_map] at hr; obtain ⟨_, -, rfl⟩ := hr; rfl) hb
    rw [Scope.bind_eq, List.append_assoc] at hI₃
    exact ⟨ρ₁ ++ ws, TopInv.step hI hI₃ hsigs rfl rfl rfl rfl rfl hI.proved⟩
  · simp [failAt_eq, bind, Except.bind] at h

theorem print_sound' {st st' : TopState} {ρ : List Value} {p : Pos} {e : Expr} (hI : TopInv st ρ)
    (hInv : Inv st.ctx st.sc st.sc.Γ.length (st.world ρ) ρ st.env (Act.top st.fns)) (hp : e.plain = true)
    (h : topItem st (.print p e) = .ok st') : ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  simp only [topItem] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
  obtain ⟨v, -, h⟩ := bind_eq_ok.1 h
  cases h
  obtain ⟨hsigs, -, -, ρ₁, -, -, hI₁, -⟩ :=
    Expr.sound e hp _ _ _ _ _ _ _ _ o (hInv.congr_ctx (C' := { st.ctx with place := "the expression of a `print`" })
      rfl rfl rfl rfl) (fun _ h => by cases h) ho
  exact ⟨ρ₁, TopInv.step hI hI₁ hsigs rfl rfl rfl rfl rfl hI.proved⟩

theorem GoalBelow.type {n : Nat} {g : CheckedGoal} {t : Term} (h : GoalBelow n g) (hk : g.kind = .type t) :
    t.entriesBelow n = true := by
  unfold GoalBelow at h; rw [hk] at h; exact h

theorem GoalBelow.fn {n : Nat} {g : CheckedGoal} {ps rs : Telescope} (h : GoalBelow n g) (hk : g.kind = .fn ps rs) :
    ∀ b ∈ ps ++ rs, b.entriesBelow n = true := by
  unfold GoalBelow at h; rw [hk] at h; exact h

theorem typeQed_sound {st st' : TopState} {ρ : List Value} {p : Pos} {e : Expr} {goal : CheckedGoal} {t : Term}
    (hI : TopInv st ρ) (hInv : Inv st.ctx st.sc st.sc.Γ.length (st.world ρ) ρ st.env (Act.top st.fns))
    (hp : e.plain = true) (hgoal : st.goal = some goal) (hk : goal.kind = .type t)
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
  have hgw : goal.given.wants = [⟨none, some t, none, .many⟩] ∧ goal.given.env = [] := by
    simp [CheckedGoal.given, hk]
  obtain ⟨hsigs, -, -, ρ₁, vs, -, hI₁, -, -, hw⟩ :=
    Expr.sound e hp _ _ _ _ _ _ _ _ o hInv (fun g' hg' => by
      cases hg'; exact ⟨⟨[], by rw [hgw.2]; rfl⟩, by rw [hgw.1]; simp⟩) ho
  have hws := hw _ rfl [] (by rw [hgw.2]; rfl)
  rw [hgw.1] at hws
  cases vs with
  | nil => exact hws.elim
  | cons v vs' =>
    obtain ⟨A, hA, hvA⟩ := hws.1.1 t rfl
    have hb := (hI.goal goal hgoal).2.type hk
    have hl : ρ.length = st.sc.Γ.length := hI.sat.1
    refine ⟨ρ₁, TopInv.step hI hI₁ hsigs rfl rfl rfl rfl rfl fun _ => ⟨goal, hgoal, fun W' hW => ?_⟩⟩
    simp only [GoalHolds, hk]
    have hρ : (ρ ++ ρ₁).take st.sc.Γ.length = W'.ρ.take st.sc.Γ.length := by
      rw [hW.take_of_le (by simp [TopState.world, hl])]
      simp [TopState.world, ← hl]
    exact ⟨v, A, by rw [← Term.eval_entriesBelow hρ [] t hb, hA], hvA.mono_sigs hW.sigs⟩

/-- Telescopes with no `difference` agree by value, binder by binder, under a valuation satisfying the scope. -/
theorem difference_agree {S : Sigs} {Γ : Entries} {ρ : List Value} (hΓ : Sat S Γ ρ) :
    ∀ {Δ Δ' : Telescope}, difference Γ Δ Δ' = none → Telescope.Agree ρ ρ Δ Δ'
  | [], [], _ => trivial
  | ⟨xn, xt, xi, xm⟩ :: xs, ⟨yn, yt, yi, ym⟩ :: ys, h => by
    cases xi <;> cases yi <;> simp [difference] at h <;> split at h <;> try cases h
    · rename_i hc
      exact ⟨⟨fun env => hΓ.eval_eq_of_identical hc.2, fun env => rfl⟩, difference_agree hΓ (by simpa using h)⟩
    · rename_i hc
      exact ⟨⟨fun env => hΓ.eval_eq_of_identical hc.2.1, fun env => by simp [hΓ.eval_eq_of_identical hc.2.2]⟩,
        difference_agree hΓ (by simpa using h)⟩
  | [], _ :: _, h | _ :: _, [], h => by simp [difference] at h

theorem Telescope.Agree.append {ρ ρ' : List Value} : ∀ {Δ₁ Δ₁' Δ₂ Δ₂' : Telescope}, Δ₁.length = Δ₁'.length →
    Telescope.Agree ρ ρ' (Δ₁ ++ Δ₂) (Δ₁' ++ Δ₂') → Telescope.Agree ρ ρ' Δ₁ Δ₁' ∧ Telescope.Agree ρ ρ' Δ₂ Δ₂'
  | [], [], _, _, _, h => ⟨trivial, h⟩
  | _ :: _, _ :: _, _, _, hl, h =>
    let ⟨h1, h2⟩ := Telescope.Agree.append (by simpa using hl) h.2
    ⟨⟨h.1, h1⟩, h2⟩
  | [], _ :: _, _, _, hl, _ | _ :: _, [], _, _, hl, _ => by simp at hl

/-- A function whose telescopes have no `difference` from a function goal's proves it in every later world. -/
theorem fnGoal_holds {st : TopState} {ρ : List Value} {ps rs : Telescope} {n m : String} {sig : FnSig}
    {W' : World} (hI : TopInv st ρ) (hb : ∀ b ∈ ps ++ rs, b.entriesBelow st.sc.Γ.length = true)
    (hg : st.globals.find? (·.name == n) = some (.fn m (some sig))) (hpl : sig.params.length = ps.length)
    (hd : difference st.sc.Γ (ps ++ rs) (sig.params ++ sig.returns) = none) (hW : (st.world ρ).Le W') :
    ∀ vs, TeleSat W'.Sc W'.ρ ps [] vs → ∃ ws, TeleSat W'.Sc W'.ρ rs vs ws := by
  have hl : ρ.length = st.sc.Γ.length := hI.sat.1
  have hF := (hI.globals W' hW ⟨st.groups, []⟩ hI.groups).fn hg
  obtain ⟨d, -, -, -, -, -, hcall, hgrp⟩ := hF.defn
  simp only [Option.any_none, Bool.false_eq_true, ↓reduceIte] at hgrp
  have hρ : W'.ρ.take st.sc.Γ.length = ρ.take st.sc.Γ.length := hW.take_of_le (by simp [TopState.world, hl])
  have hsig : ∀ b ∈ sig.params ++ sig.returns, b.entriesBelow st.sc.Γ.length = true := by
    intro b hb'
    rcases List.mem_append.1 hb' with hb' | hb'
    · exact (hF.params b hb').1
    · exact (hF.returns b hb').1
  have hA : Telescope.Agree W'.ρ W'.ρ (ps ++ rs) (sig.params ++ sig.returns) :=
    ((Telescope.agree_of_entriesBelow hρ (List.all_eq_true.2 hb)).trans (difference_agree hI.sat hd)).trans
      (Telescope.agree_of_entriesBelow hρ.symm (List.all_eq_true.2 hsig))
  obtain ⟨hA1, hA2⟩ := hA.append hpl.symm
  intro vs hvs
  obtain ⟨ws, -, hws⟩ := hcall vs ((TeleSat.congr hA1).1 hvs) (Act.lt_of_group (by simpa [calleeAct] using hgrp))
  exact ⟨ws, (TeleSat.congr hA2).2 hws⟩

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

theorem qed_sound' {st st' : TopState} {ρ : List Value} {p : Pos} {e : Expr} (hI : TopInv st ρ)
    (hInv : Inv st.ctx st.sc st.sc.Γ.length (st.world ρ) ρ st.env (Act.top st.fns)) (hp : e.plain = true)
    (h : topItem st (.qed p e) = .ok st') : ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
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
      have hb := (hI.goal goal hgoal).2.fn hk
      have hInv' : Inv st.ctx st.sc st.sc.Γ.length (st.world ρ) (ρ ++ []) st.env (Act.top st.fns) := by
        rw [List.append_nil]; exact hInv
      exact ⟨[], TopInv.step hI hInv' rfl rfl rfl rfl rfl rfl fun _ => ⟨goal, hgoal, fun W' hW => by
        simp only [GoalHolds, hk]; exact fnGoal_holds hI hb hg hpl hd hW⟩⟩
    · rename_i t hk
      split at h
      · split at h
        · simp [failAt_eq, bind, Except.bind] at h
        · exact typeQed_sound hI hInv hp hgoal hk h
      · exact typeQed_sound hI hInv hp hgoal hk h
  · simp [failAt_eq] at h

end Pledge
