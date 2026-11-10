import Pledge.Sound.Term

namespace Pledge

/-- What checking the arguments of a call or application is meant to guarantee: they run to values that satisfy
the parameters, `prevv` being the values of the arguments before them. -/
def ArgsPost (C : Ctx) (sc : Scope) (n0 : Nat) (W : World) (ρ : List Value) (env : Env) (act : Act)
    (params : Telescope) (prevv : List Value) (a : ArgsOut) : Prop :=
  a.sc.sigs = sc.sigs ∧ a.sc.names = sc.names ∧ (∀ r ∈ a.res, r.tainted = false) ∧
  ∃ ρ' vs, evalList W.P act env (a.trees.map Arg.expr) = .ok vs ∧ Inv C a.sc n0 W (ρ ++ ρ') env act ∧
    Term.evalList (ρ ++ ρ') [] (a.res.map (·.term)) = some vs ∧ (∀ v ∈ vs, ∃ V, HasType W.Sc v V) ∧
    TeleSat W.Sc (ρ ++ ρ') params prevv vs

theorem BinderSat.frame {S : Sigs} {ρ env : List Value} {b : TBinder} {v : Value} (ρ' : List Value)
    (h : BinderSat S ρ b env v) : BinderSat S (ρ ++ ρ') b env v :=
  let ⟨A, hA, hv, his⟩ := h
  ⟨A, Term.eval_frame_ρ ρ' hA, hv, fun e he => Term.eval_frame_ρ ρ' (his e he)⟩

theorem one_singleton (v : Value) : one [v] = .ok v := rfl

theorem checkArgs_sound {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr) :
    ∀ {C : Ctx} {sc : Scope} {owner role : String} {params : Telescope} {prev : List Res} {a : ArgsOut}
      {n0 : Nat} {W : World} {ρ : List Value} {env : Env} {act : Act} {prevv : List Value},
      Inv C sc n0 W ρ env act → (∀ p ∈ params, p.mult = .many) → params.length = args.length →
      Term.evalList ρ [] (prev.map (·.term)) = some prevv →
      checkArgs C sc owner role false params prev args = .ok a → ArgsPost C sc n0 W ρ env act params prevv a := by
  induction args with
  | nil =>
    intro C sc owner role params prev a n0 W ρ env act prevv hI _ hl _ h
    cases params with
    | cons => simp at hl
    | nil =>
      simp only [checkArgs, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl, by simp, [], [], by simp [evalList_nil], by simpa using hI, rfl, by simp, .nil⟩
  | cons arg args ihs =>
    intro C sc owner role params prev a n0 W ρ env act prevv hI hm hl hprev h
    obtain ⟨m, e⟩ := arg
    cases params with
    | nil => simp at hl
    | cons p ps =>
      simp only [checkArgs, hI.phase, Nat.not_le_of_lt (by decide : 1 < 2), decide_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
      obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
      obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [keep_ok] at hr hrest
      have hpm := hm p List.mem_cons_self
      have hgok : ∀ g', some (argGiven p prev role owner false) = some g' → g'.Ok ρ := by
        rintro g' ⟨⟩
        refine ⟨⟨prevv, by simpa [argGiven] using hprev⟩, ?_⟩
        simp [argGiven, hpm]
      obtain ⟨hsigs, hnames, hres, ρ₁, vs₁, hev, hI₁, hvs₁, hty₁, hw⟩ :=
        ih (.mk m e) List.mem_cons_self C sc _ n0 W ρ env act o hI hgok ho
      have hr1 := single_ok hr
      rw [hr1] at hvs₁ hres
      obtain ⟨v, hv, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs₁)
      have hb : BinderSat W.Sc (ρ ++ ρ₁) p prevv v := by
        have := hw _ rfl prevv (by simpa [argGiven] using hprev)
        simp only [argGiven, Bool.false_eq_true, ↓reduceIte, WantsSat] at this
        exact this.1.binderSat
      obtain ⟨hsigs₂, hnames₂, hres₂, ρ₂, vs₂, hev₂, hI₂, hvs₂, hty₂, ht₂⟩ :=
        ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hI₁ (fun q hq => hm q (List.mem_cons_of_mem _ hq))
          (by simpa using hl) (by
            rw [List.map_append, List.map_singleton]
            exact Term.evalList_append (Term.evalList_frame_ρ ρ₁ hprev) (Term.evalList_singleton.2 ⟨v, hv, rfl⟩))
          hrest
      refine ⟨hsigs₂.trans hsigs, hnames₂.trans hnames, ?_, ρ₁ ++ ρ₂, v :: vs₂, ?_, by simpa using hI₂, ?_, ?_, ?_⟩
      · intro r' hr'
        rcases List.mem_cons.1 hr' with rfl | hr'
        · exact (hres r' (by simp)).1
        · exact hres₂ r' hr'
      · simp only [List.map_cons, Arg.expr]
        rw [evalList_cons, hev, ok_bind, one_singleton, ok_bind, hev₂]; rfl
      · simp only [List.map_cons]
        rw [← List.append_assoc]
        exact Term.evalList_cons_eq_some.2 ⟨v, vs₂, Term.eval_frame_ρ ρ₂ hv, hvs₂, rfl⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact hty₁ u (by simp)
        · exact hty₂ u hu
      · rw [← List.append_assoc]
        exact TeleSat.cons_iff.2 ⟨v, vs₂, rfl, hb.frame ρ₂, ht₂⟩

theorem TeleSat.hasType {S : Sigs} {ρ : List Value} :
    ∀ {Δ : Telescope} {env vs : List Value}, TeleSat S ρ Δ env vs → ∀ v ∈ vs, ∃ V, HasType S v V
  | [], _, _, h => by rw [TeleSat.nil_iff.1 h]; simp
  | _ :: _, _, _, h => by
    obtain ⟨v, vs', rfl, ⟨A, -, hA, -⟩, ht⟩ := TeleSat.cons_iff.1 h
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ⟨A, hA⟩
    · exact TeleSat.hasType ht u hu

/-- A call whose arguments checked: given that the measure decreases, the body runs to results satisfying the
returns. -/
theorem call_core {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr) {C : Ctx} {sc : Scope}
    {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {env : Env} {act : Act} {o o' : Out} {sig : FnSig}
    {a : ArgsOut} (hI : Inv C sc n0 W ρ env act) (hg : ∀ g', g = some g' → g'.Ok ρ)
    (hfo : FnOk n0 W C.fn act h.name sig) (har : sig.params.length = args.length)
    (ha : checkArgs C sc h.name "parameter" false sig.params [] args = .ok a)
    (hlt : ∀ ρ' vs d, Inv C a.sc n0 W (ρ ++ ρ') env act →
      Term.evalList (ρ ++ ρ') [] (a.res.map (·.term)) = some vs → vs.length = sig.params.length →
      W.P.fns.find h.name = some d → d.subterm = sig.subterm → d.subterm.count true ≤ d.pad →
      (if C.fn.any (·.group.contains h.name) then d.group = act.group ∧ d.pad = act.subs.length
        else d.group < act.group) → Act.lt (calleeAct d vs) act)
    (ho' : applied (opened a.sc sig.returns (a.res.map (·.term)) h.name h.pos
        fun _ => sig.tainted || a.res.any (·.tainted)).1 g h.pos
      (opened a.sc sig.returns (a.res.map (·.term)) h.name h.pos fun _ => sig.tainted || a.res.any (·.tainted)).2
      (.app h a.trees) sc.holes.length a.snaps = .ok o')
    (hf : finish C false g (.app h args) o' = .ok o) : ExprPost C sc g n0 W ρ env act o := by
  obtain ⟨htn, hpar, hret, -, d, hd, -, hds, -, hdc, hspec, hgrp⟩ := hfo
  obtain ⟨hsigs, hnames, hres, ρ', vs, hev, hI', hvs, -, ht⟩ :=
    checkArgs_sound ih hI (fun p hp => (hpar p hp).2) har rfl ha
  have hlt' := hlt ρ' vs d hI' hvs ht.length_eq hd hds hdc hgrp
  have hagree : (ρ ++ ρ').take n0 = W.ρ.take n0 := hI'.agree
  obtain ⟨rs, hcall, hrs⟩ := hspec vs
    ((TeleSat.iff_of_entriesBelow hagree (List.all_eq_true.2 fun b hb => (hpar b hb).1)).1 ht) hlt'
  have hrs' := (TeleSat.iff_of_entriesBelow hagree (List.all_eq_true.2 fun b hb => (hret b hb).1)).2 hrs
  have htaint : (sig.tainted || a.res.any (·.tainted)) = false := by simpa [htn] using hres
  obtain ⟨hsat, hrv, -, hun⟩ := opened_sound (kind := h.name) (pos := h.pos)
    (taint := fun _ => sig.tainted || a.res.any (·.tainted)) hI'.sat hvs hrs'
  have hI'' := Inv.extend hI' hsat rfl rfl
    ⟨hI'.inert.holes, hI'.inert.taintedBy, hI'.inert.names⟩
  have hty := hrs.hasType
  have hframe {t : List Term} {us : List Value} (he : Term.evalList ρ [] t = some us) :=
    Term.evalList_frame_ρ rs (Term.evalList_frame_ρ ρ' he)
  obtain ⟨rfl, hw⟩ := applied_sound hsat (hI'.sigsClose rs) hI'.inert.holes hrv hty
    (fun g' h' => let ⟨envv, he⟩ := (hg g' h').env; ⟨envv, hframe he⟩) ho'
  have hun' := hun fun _ => htaint
  obtain ⟨rfl, -, her⟩ := finish_inert (fun g' h' => (hg g' h').mult) hI'.inert.taintedBy hun' hf
  refine ⟨hsigs, hnames, fun r hr => ⟨hun' r hr, her r hr⟩, ρ' ++ rs, rs, ?_, by simpa using hI'',
    by simpa using hrv, hty, fun g' hg' envv henv => by simpa using (hw g' hg' envv (hframe henv)).2⟩
  rw [evalExpr_call hev hd hlt']
  exact hcall

/-- A call (§8, §9): the arguments satisfy the parameters, the measure decreases, so the body runs to results
satisfying the returns. -/
theorem call_sound {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr) {C : Ctx} {sc : Scope}
    {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {env : Env} {act : Act} {o : Out} {m : String}
    {sig : FnSig} (hI : Inv C sc n0 W ρ env act) (hg : ∀ g', g = some g' → g'.Ok ρ)
    (hglob : C.global h.name = some (.fn m (some sig))) (hc : checkExpr C sc g (.app h args) = .ok o) :
    ExprPost C sc g n0 W ρ env act o := by
  have hwhole : g.any (·.allErased) = false := by
    cases g with
    | none => rfl
    | some g' => simpa using Given.allErased_eq_false (hg g' rfl).mult
  have hC : ({ C with erased := false } : Ctx) = C := by have := hI.erased; cases C; simp_all
  have hfo := hI.globals.fn hglob
  rw [checkExpr] at hc
  simp only [hI.erased, hwhole, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hC, hglob] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  cases hF : C.fn.filter (·.group.contains h.name) with
  | none =>
    simp only [hF] at ho'
    obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
    obtain ⟨plan, hplan, ho'⟩ := bind_eq_ok.1 ho'
    simp only [pure, Except.pure, Except.ok.injEq] at hplan
    subst hplan
    obtain ⟨u, har, ho'⟩ := bind_eq_ok.1 ho'
    obtain ⟨a, ha, ho'⟩ := bind_eq_ok.1 ho'
    rw [keep_ok] at ho'
    refine call_core ih hI hg hfo (arity_ok har) ha ?_ ho' hf
    intro ρ' vs d _ _ _ _ _ _ hgrp
    have hany : C.fn.any (·.group.contains h.name) = false := by
      cases hfn : C.fn with
      | none => rfl
      | some f => simpa [hfn, Option.filter] using hF
    simp only [hany, Bool.false_eq_true, ↓reduceIte] at hgrp
    exact Act.lt_of_group hgrp
  | some fn =>
    simp only [hF] at ho'
    obtain ⟨plan, hplan, ho'⟩ := bind_eq_ok.1 ho'
    obtain ⟨u, har, ho'⟩ := bind_eq_ok.1 ho'
    obtain ⟨a, ha, ho'⟩ := bind_eq_ok.1 ho'
    rw [keep_ok] at ho'
    obtain ⟨⟨subs, k⟩, hm, rfl⟩ : ∃ p, marks h.pos args h.name sig fn = .ok p ∧ plan = some p := by
      cases hmk : marks h.pos args h.name sig fn with
      | error e => simp [hmk, Functor.map, Except.map] at hplan
      | ok p => simp [hmk, Functor.map, Except.map] at hplan; exact ⟨p, rfl, hplan.symm⟩
    obtain ⟨u, hdec, ho'⟩ := bind_eq_ok.1 ho'
    have hCfn : C.fn = some fn := by
      cases hfn : C.fn with
      | none => simp [hfn] at hF
      | some f => simp only [hfn, Option.filter] at hF; split at hF <;> simp_all
    refine call_core ih hI hg hfo (arity_ok har) ha ?_ ho' hf
    intro ρ' vs d hI' hvs hl _ hds hdc hgrp
    have hany : C.fn.any (·.group.contains h.name) = true := by
      simpa [hCfn] using (Option.filter_eq_some_iff.1 hF).2
    simp only [hany, ↓reduceIte] at hgrp
    obtain ⟨ss, hss, hact⟩ := hI'.act fn hCfn
    exact call_lt hI'.sat.rulesHold hm hdec hvs hss hact hds (hfo.subterm.trans hl.symm) hdc hgrp.1 hgrp.2

/-- An application of a type constructor or value constructor builds a value of its type. -/
theorem Given.ok_mult {ρ : List Value} {g : Option Given} (hg : ∀ g', g = some g' → g'.Ok ρ) :
    ∀ g', g = some g' → ∀ w ∈ g'.wants, w.mult = .many := fun g' h => (hg g' h).mult

theorem Given.whole_false {ρ : List Value} {g : Option Given} (hg : ∀ g', g = some g' → g'.Ok ρ) :
    g.any (·.allErased) = false := by
  cases g with
  | none => rfl
  | some g' => simpa using Given.allErased_eq_false (hg g' rfl).mult

theorem Ctx.erased_false {C : Ctx} (h : C.erased = false) : ({ C with erased := false } : Ctx) = C := by
  cases C; simp_all

theorem ctorApp_core {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr) {C : Ctx} {sc : Scope}
    {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {env : Env} {act : Act} {o o' : Out} {k : HeadKind}
    {sig : Sig} {role : String} {a : ArgsOut} {C' : Ctx}
    (hI : Inv C sc n0 W ρ env act) (hg : ∀ g', g = some g' → g'.Ok ρ) (hk : HeadOk sc.sigs W k h.name)
    (hsig : sc.sigs.find ⟨k, h.name⟩ = some sig) (har : sig.params.length = args.length)
    (ha : checkArgs C sc h.name role false sig.params [] args = .ok a)
    (ho' : applied a.sc g h.pos [⟨.app sig.head (a.res.map (·.term)), a.res.any (·.tainted), false⟩]
      (.app h a.trees) sc.holes.length a.snaps = .ok o')
    (hf : finish C' false g (.app h args) o' = .ok o) : ExprPost C sc g n0 W ρ env act o := by
  have hsigm := List.mem_of_find?_eq_some hsig
  obtain ⟨hbelow, hbounds, hmult⟩ := hI.sigsOk sig hsigm
  obtain ⟨hsigs, hnames, hres, ρ', vs, hev, hI', hvs, hty, ht⟩ :=
    checkArgs_sound ih hI hmult har rfl ha
  have hhead := Sigs.find_head hsig
  have hS' : SigsClose a.sc.sigs (ρ ++ ρ') W.Sc := hsigs ▸ hI.sigsClose ρ'
  obtain ⟨V, hV⟩ : ∃ V, sig.ret.eval (ρ ++ ρ') vs = some V := by
    refine Term.eval_isSome _ ?_ (by rw [ht.length_eq]; exact hbounds)
    simp only [Sig.entriesBelow, Bool.and_eq_true] at hbelow
    exact Term.entriesBelow_mono hI'.length _ hbelow.2
  have hvt : HasType W.Sc (.app sig.head vs) V :=
    ((hI.sigsClose ρ').hasType_app_iff (hhead ▸ hsig)).2 ⟨ht, hV⟩
  have hun : (a.res.any (·.tainted)) = false := by simpa using hres
  have hvs1 : Term.evalList (ρ ++ ρ') []
      ([(⟨.app sig.head (a.res.map (·.term)), a.res.any (·.tainted), false⟩ : Res)].map (·.term)) =
        some [.app sig.head vs] := by
    simp [Term.evalList, Term.eval, hvs]
  have hty1 : ∀ u ∈ [Value.app sig.head vs], ∃ V, HasType W.Sc u V := by simp; exact ⟨V, hvt⟩
  obtain ⟨rfl, hw⟩ := applied_sound hI'.sat hS' hI'.inert.holes hvs1 hty1
    (fun g' h' => let ⟨envv, he⟩ := (hg g' h').env; ⟨envv, Term.evalList_frame_ρ ρ' he⟩) ho'
  obtain ⟨rfl, -, her⟩ := finish_inert (Given.ok_mult hg) hI'.inert.taintedBy (by simp [hun]) hf
  refine ⟨hsigs, hnames, fun r hr => ⟨by simp at hr; subst hr; exact hun, her r hr⟩, ρ', [.app sig.head vs], ?_, hI',
    hvs1, hty1, fun g' hg' envv henv => (hw g' hg' envv (Term.evalList_frame_ρ ρ' henv)).2⟩
  rw [evalExpr_ctor hev hk.fns hk.kind, hhead]

theorem ctorApp_sound {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr) {C : Ctx} {sc : Scope}
    {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {env : Env} {act : Act} {o : Out}
    (hI : Inv C sc n0 W ρ env act) (hg : ∀ g', g = some g' → g'.Ok ρ)
    (hglob : (C.global h.name matches some (.type ..)) ∨ (C.global h.name matches some (.ctor _)))
    (hc : checkExpr C sc g (.app h args) = .ok o) : ExprPost C sc g n0 W ρ env act o := by
  rw [checkExpr] at hc
  simp only [hI.erased, Given.whole_false hg, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    Ctx.erased_false hI.erased] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  have hph : ¬ (2 ≤ C.phase) := by rw [hI.phase]; decide
  cases hgl : C.global h.name with
  | none => simp [hgl] at hglob
  | some gl =>
    have hgl' : C.globals.find? (·.name == h.name) = some gl := hgl
    cases gl with
    | fn => simp [hgl] at hglob
    | type T cs d =>
      have hk := (hI.globals.type hgl').1
      simp only [hgl, ↓reduceIte] at ho'
      obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨sig, hsig, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨u₂, har, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨a, ha, ho'⟩ := bind_eq_ok.1 ho'
      simp only [hph, decide_false, Bool.and_false] at ha
      exact ctorApp_core ih hI hg hk (Scope.sig_ok hsig) (arity_ok har) ha ho' hf
    | ctor c =>
      have hk := hI.globals.ctor hgl'
      simp only [hgl] at ho'
      obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨sig, hsig, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨u₂, har, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨a, ha, ho'⟩ := bind_eq_ok.1 ho'
      simp only [hph, decide_false, Bool.and_false] at ha
      exact ctorApp_core ih hI hg hk (Scope.sig_ok hsig) (arity_ok har) ha ho' hf

theorem app_sound {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr) : ExprSound (.app h args) := by
  intro C sc g n0 W ρ env act o hI hg hc
  cases hgl : C.global h.name with
  | none =>
    rw [checkExpr] at hc
    simp [hI.erased, Given.whole_false hg, Ctx.erased_false hI.erased, hgl, notApplied, failAt_eq, error_bind] at hc
  | some gl =>
    cases gl with
    | fn m sig =>
      cases sig with
      | none =>
        rw [checkExpr] at hc
        simp [hI.erased, Given.whole_false hg, Ctx.erased_false hI.erased, hgl, failAt_eq, error_bind] at hc
      | some sig => exact call_sound ih hI hg hgl hc
    | type => exact ctorApp_sound ih hI hg (by simp [hgl]) hc
    | ctor => exact ctorApp_sound ih hI hg (by simp [hgl]) hc

theorem Inv.lookup_untainted {C : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {env : Env} {act : Act}
    (hI : Inv C sc n0 W ρ env act) {n : String} {r : Res} (h : sc.lookup n = some r) : r.tainted = false :=
  hI.inert.names _ (lookup_mem h)

theorem var_sound (x : Id) : ExprSound (.var x) := by
  intro C sc g n0 W ρ env act o hI hg h
  rw [checkExpr] at h
  simp only [hI.erased, Given.whole_false hg, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 h
  cases hx : x.name with
  | none => simp [hx, failAt_eq] at ho'
  | some n =>
    cases hl : sc.lookup n with
    | none => simp [hx, hl, notValue, failAt_eq] at ho'
    | some r =>
      simp only [hx, hl] at ho'
      obtain ⟨v, V, henv, hv, hV⟩ := hI.names n r hl
      have hvs : Term.evalList ρ [] ([({ r with erased := r.erased || sc.erasedEntry r.term } : Res)].map (·.term)) =
          some [v] := by simp [Term.evalList, hv]
      have hty : ∀ u ∈ [v], ∃ V, HasType W.Sc u V := by simp; exact ⟨V, hV⟩
      obtain ⟨rfl, hw⟩ := produced_sound hI.sat (hI.sigs ρ hI.agree) hI.inert.holes hvs hty
        (fun g' h => (hg g' h).env) ho'
      obtain ⟨rfl, -, her⟩ := finish_inert (Given.ok_mult hg) hI.inert.taintedBy
        (by simpa using hI.lookup_untainted hl) hf
      refine ⟨rfl, rfl, fun r' hr' => ⟨?_, her r' hr'⟩, [], [v], ?_, by simpa using hI, by simpa using hvs, hty,
        fun g' hg' envv henv' => by simpa using (hw g' hg' envv henv').2⟩
      · simp only [List.mem_singleton] at hr'; subst hr'; exact (hI.lookup_untainted hl :)
      · rw [evalExpr_var, hx]; simp [henv, pure, Except.pure]

theorem WantSat.frame {S : Sigs} {ρ env : List Value} {w : Want} {v : Value} (ρ' : List Value)
    (h : WantSat S ρ w env v) : WantSat S (ρ ++ ρ') w env v :=
  ⟨fun T hT => let ⟨A, hA, hv⟩ := h.1 T hT; ⟨A, Term.eval_frame_ρ ρ' hA, hv⟩,
    fun e he => Term.eval_frame_ρ ρ' (h.2 e he)⟩

theorem WantsSat.frame {S : Sigs} {ρ : List Value} (ρ' : List Value) :
    ∀ {ws : List Want} {env vs : List Value}, WantsSat S ρ ws env vs → WantsSat S (ρ ++ ρ') ws env vs
  | [], _, [], _ => trivial
  | _ :: _, _, _ :: _, ⟨h1, h2⟩ => ⟨h1.frame ρ', WantsSat.frame ρ' h2⟩
  | [], _, _ :: _, h | _ :: _, _, [], h => h.elim

theorem WantsSat.length_eq {S : Sigs} {ρ : List Value} :
    ∀ {ws : List Want} {env vs : List Value}, WantsSat S ρ ws env vs → vs.length = ws.length
  | [], _, [], _ => rfl
  | _ :: _, _, _ :: _, ⟨_, h2⟩ => by simp [WantsSat.length_eq h2]
  | [], _, _ :: _, h | _ :: _, _, [], h => h.elim

theorem checkElems_sound {es : List Expr} (ih : ∀ e ∈ es, ExprSound e) :
    ∀ {C : Ctx} {sc : Scope} {g : Option Given} {prev : List Res} {o : ElemsOut} {n0 : Nat} {W : World}
      {ρ : List Value} {env : Env} {act : Act} {prevv : List Value},
      Inv C sc n0 W ρ env act → (∀ g', g = some g' → g'.Ok ρ ∧ g'.wants.length = prev.length + es.length) →
      Term.evalList ρ [] (prev.map (·.term)) = some prevv → checkElems C sc g prev es = .ok o →
      o.sc.sigs = sc.sigs ∧ o.sc.names = sc.names ∧ (∀ r ∈ o.res, r.tainted = false) ∧
      ∃ ρ' vs, evalList W.P act env o.trees = .ok vs ∧ Inv C o.sc n0 W (ρ ++ ρ') env act ∧
        Term.evalList (ρ ++ ρ') [] (o.res.map (·.term)) = some vs ∧ (∀ v ∈ vs, ∃ V, HasType W.Sc v V) ∧
        ∀ g', g = some g' → ∀ envv, Term.evalList ρ [] g'.env = some envv →
          WantsSat W.Sc (ρ ++ ρ') (g'.wants.drop prev.length) (envv ++ prevv) vs := by
  induction es with
  | nil =>
    intro C sc g prev o n0 W ρ env act prevv hI hg _ h
    simp only [checkElems, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨rfl, rfl, by simp, [], [], by simp [evalList_nil], by simpa using hI, rfl, by simp, ?_⟩
    intro g' hg' envv _
    have : g'.wants.drop prev.length = [] := by simp [(hg g' hg').2]
    rw [this]; trivial
  | cons e es ihs =>
    intro C sc g prev o n0 W ρ env act prevv hI hg hprev h
    simp only [checkElems] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hr hrest
    have hgok : ∀ g', elemGiven g prev = some g' → g'.Ok ρ := by
      intro g' hg'
      simp only [elemGiven, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hg'
      obtain ⟨g₀, rfl, w, hw, rfl⟩ := hg'
      obtain ⟨⟨envv, henv⟩, hm⟩ := (hg g₀ rfl).1
      exact ⟨⟨envv ++ prevv, Term.evalList_append henv hprev⟩, by simpa using hm w (List.mem_of_getElem? hw)⟩
    obtain ⟨hsigs, hnames, hres, ρ₁, vs₁, hev, hI₁, hvs₁, hty₁, hw₁⟩ := ih e List.mem_cons_self C sc _ n0 W ρ env act
      o₁ hI hgok ho₁
    have hr1 := single_ok hr
    rw [hr1] at hvs₁ hres
    obtain ⟨v, hv, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs₁)
    obtain ⟨hsigs₂, hnames₂, hres₂, ρ₂, vs₂, hev₂, hI₂, hvs₂, hty₂, hw₂⟩ :=
      ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hI₁
        (fun g' hg' => by
          obtain ⟨⟨⟨envv, henv⟩, hm⟩, hl⟩ := hg g' hg'
          exact ⟨⟨⟨envv, Term.evalList_frame_ρ ρ₁ henv⟩, hm⟩, by simp [hl]; omega⟩)
        (by
          rw [List.map_append, List.map_singleton]
          exact Term.evalList_append (Term.evalList_frame_ρ ρ₁ hprev) (Term.evalList_singleton.2 ⟨v, hv, rfl⟩))
        hrest
    refine ⟨hsigs₂.trans hsigs, hnames₂.trans hnames, ?_, ρ₁ ++ ρ₂, v :: vs₂, ?_, by simpa using hI₂, ?_, ?_, ?_⟩
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact (hres r' (by simp)).1
      · exact hres₂ r' hr'
    · rw [evalList_cons, hev, ok_bind, one_singleton, ok_bind, hev₂]; rfl
    · simp only [List.map_cons]
      rw [← List.append_assoc]
      exact Term.evalList_cons_eq_some.2 ⟨v, vs₂, Term.eval_frame_ρ ρ₂ hv, hvs₂, rfl⟩
    · intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · exact hty₁ u (by simp)
      · exact hty₂ u hu
    · intro g' hg' envv henv
      have hl := (hg g' hg').2
      obtain ⟨w, hw⟩ : ∃ w, g'.wants[prev.length]? = some w :=
        ⟨_, List.getElem?_eq_getElem (by simp [hl])⟩
      have hel : elemGiven g prev =
          some ⟨[w], g'.env ++ prev.map (·.term), false, none, g'.label.map (fun l _ => l prev.length)⟩ := by
        simp [elemGiven, hg', hw]
      have h1 := hw₁ _ hel (envv ++ prevv) (Term.evalList_append henv hprev)
      simp only [WantsSat] at h1
      have h2 := hw₂ g' hg' envv (Term.evalList_frame_ρ ρ₁ henv)
      rw [List.drop_eq_getElem_cons (by simp [hl]), ← List.append_assoc]
      refine ⟨?_, ?_⟩
      · have := h1.1.frame ρ₂
        simpa [List.getElem?_eq_some_iff.1 hw |>.2] using this
      · simpa [List.length_append] using h2

theorem tuple_sound (p : Pos) {es : List Expr} (ih : ∀ e ∈ es, ExprSound e) : ExprSound (.tuple p es) := by
  intro C sc g n0 W ρ env act o hI hg hc
  rw [checkExpr] at hc
  simp only [hI.erased, Given.whole_false hg, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    Ctx.erased_false hI.erased] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  have hlen : ∀ g', g = some g' → g'.wants.length = es.length := by
    intro g' hg'
    subst hg'
    simp only at ho'
    by_cases hne : g'.wants.length = es.length
    · exact hne
    · simp [hne, miscount, failAt_eq, error_bind] at ho'
  have ho'' : checkElems C sc g [] es >>= (fun o => pure ⟨o.sc, o.res, .tuple p o.trees, o.snaps⟩) = .ok o' := by
    cases g with
    | none => simpa using ho'
    | some g' =>
      simp only [hlen g' rfl, ne_eq, not_true_eq_false, ↓reduceIte] at ho'
      simpa using ho'
  obtain ⟨oe, hoe, ho''⟩ := bind_eq_ok.1 ho''
  simp only [pure, Except.pure, Except.ok.injEq] at ho''
  subst ho''
  obtain ⟨hsigs, hnames, hres, ρ', vs, hev, hI', hvs, hty, hw⟩ := checkElems_sound ih (prev := []) (prevv := []) hI
    (fun g' hg' => ⟨hg g' hg', by simp [hlen g' hg']⟩) (rfl : Term.evalList ρ [] [] = some []) hoe
  obtain ⟨rfl, -, her⟩ := finish_inert (Given.ok_mult hg) hI'.inert.taintedBy hres hf
  exact ⟨hsigs, hnames, fun r hr => ⟨hres r hr, her r hr⟩, ρ', vs, by rw [evalExpr_tuple]; exact hev, hI', hvs, hty,
    fun g' hg' envv henv => by simpa using hw g' hg' envv henv⟩

theorem checkStmts_sound {ss : List Stmt} (ih : ∀ s ∈ ss, StmtSound s) :
    ∀ {C : Ctx} {sc : Scope} {o : StmtsOut} {n0 : Nat} {W : World} {ρ : List Value} {env : Env} {act : Act},
      Inv C sc n0 W ρ env act → checkStmts C sc ss = .ok o →
      o.sc.sigs = sc.sigs ∧ ∃ ρ' env', Inv C o.sc n0 W (ρ ++ ρ') env' act ∧
        ∀ f, evalBlock W.P act env o.trees f = evalExpr W.P act env' f := by
  induction ss with
  | nil =>
    intro C sc o n0 W ρ env act hI h
    simp only [checkStmts, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, [], env, by simpa using hI, fun f => evalBlock_nil⟩
  | cons s ss ihs =>
    intro C sc o n0 W ρ env act hI h
    simp only [checkStmts] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    obtain ⟨hsigs, ρ₁, env₁, hev, hI₁⟩ := ih s List.mem_cons_self C sc n0 W ρ env act o₁ hI ho₁
    obtain ⟨hsigs₂, ρ₂, env₂, hI₂, hb⟩ := ihs (fun s hs => ih s (List.mem_cons_of_mem _ hs)) hI₁ hrest
    refine ⟨hsigs₂.trans hsigs, ρ₁ ++ ρ₂, env₂, by simpa using hI₂, fun f => ?_⟩
    rw [evalBlock_cons, hev, ok_bind, hb]

theorem Scope.holes_eta {sc : Scope} (h : sc.holes = []) : ({ sc with holes := [] } : Scope) = sc := by
  cases sc; simp_all

/-- The invariant for a scope whose names are put back to those of an earlier scope, with the earlier environment. -/
theorem Inv.restore {C : Ctx} {sc sc' : Scope} {n0 : Nat} {W : World} {ρ ρ' : List Value} {env env' : Env}
    {act : Act} (hI : Inv C sc n0 W ρ env act) (hI' : Inv C sc' n0 W (ρ ++ ρ') env' act) :
    Inv C { sc' with names := sc.names } n0 W (ρ ++ ρ') env act :=
  ⟨hI'.phase, hI'.erased, hI'.sat, hI'.n0_world, hI'.agree, hI'.sigs, hI'.sigsOk, fun n r h => by
    obtain ⟨v, V, h1, h2, h3⟩ := hI.names n r h
    exact ⟨v, V, h1, Term.eval_frame_ρ ρ' h2, h3⟩, hI'.globals, hI'.act,
    ⟨hI'.inert.holes, hI'.inert.taintedBy, hI.inert.names⟩⟩

theorem block_sound {ss : List Stmt} {f : Expr} (ihs : ∀ s ∈ ss, StmtSound s) (ihf : ExprSound f) :
    ExprSound (.block ss f) := by
  intro C sc g n0 W ρ env act o hI hg hc
  rw [checkExpr] at hc
  simp only [hI.erased, Given.whole_false hg, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    Ctx.erased_false hI.erased, Scope.holes_eta hI.inert.holes] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  obtain ⟨s, hs, ho'⟩ := bind_eq_ok.1 ho'
  obtain ⟨of, hof, ho'⟩ := bind_eq_ok.1 ho'
  simp only [pure, Except.pure, Except.ok.injEq] at ho'
  subst ho'
  rw [keep_ok] at hof
  obtain ⟨hsigs, ρ₁, env₁, hI₁, hb⟩ := checkStmts_sound ihs hI hs
  rw [show ({ s.sc with holes := sc.holes } : Scope) = s.sc by
    rw [hI.inert.holes]; exact Scope.holes_eta hI₁.inert.holes]
    at hof
  obtain ⟨hsigs₂, -, hres, ρ₂, vs, hev, hI₂, hvs, hty, hw⟩ := ihf C s.sc g n0 W (ρ ++ ρ₁) env₁ act of hI₁
    (fun g' hg' => let ⟨⟨envv, he⟩, hm⟩ := hg g' hg'; ⟨⟨envv, Term.evalList_frame_ρ ρ₁ he⟩, hm⟩) hof
  have hI₃ := Inv.restore hI (ρ' := ρ₁ ++ ρ₂) (by simpa using hI₂)
  obtain ⟨rfl, -, her⟩ := finish_inert (o := ⟨{ of.sc with names := sc.names }, of.res, .block s.trees of.tree,
    s.snaps ++ of.snaps⟩) (Given.ok_mult hg) hI₂.inert.taintedBy (fun r hr => (hres r hr).1) hf
  refine ⟨by simp [hsigs₂, hsigs], rfl, hres, ρ₁ ++ ρ₂, vs, ?_, hI₃, by simpa using hvs, hty,
    fun g' hg' envv henv => ?_⟩
  · rw [evalExpr_block, hb, hev]
  · simpa using hw g' hg' envv (Term.evalList_frame_ρ ρ₁ henv)

theorem inspect_sound (p : Pos) : StmtSound (.inspect p) := by
  intro C sc n0 W ρ env act o hI h
  simp only [checkStmt, pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, [], env, evalStmt_inspect, by simpa using hI⟩

/-- A `match` (§10): the scrutinee's value is headed by a value constructor that survives forcing, so its branch
exists, runs, and its results satisfy the annotation as it stands before the match. -/
theorem match_sound {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch} (ihs : ExprSound s)
    (ihb : ∀ b ∈ bs, ExprSound b.body) (hm : m = none) (hann : ann.plain = true) :
    ExprSound (.match p m s ann bs) := by
  sorry

theorem take_of_length {n : Nat} {vs : List Value} (h : vs.length = n) : take n vs = .ok vs := by
  simp [take, h, pure, Except.pure]

theorem zip_map_term {bs : List LetBinder} {rs : List Res} (h : bs.length = rs.length) :
    ((bs.zip rs).map fun (b, r) => ({ r with erased := b.mult == some Mult.erased } : Res)).map (·.term) =
      rs.map (·.term) := by
  apply List.ext_getElem (by simp [h])
  intro i h₁ h₂
  simp

theorem let_sound {p : Pos} {bs : List LetBinder} {rhs : Expr} (ih : ExprSound rhs)
    (hp : bs.all (·.mult.isNone) = true) : StmtSound (.let p bs rhs) := by
  intro C sc n0 W ρ env act o hI h
  simp only [checkStmt] at h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨ws, hws, h⟩ := bind_eq_ok.1 h
  obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hwl, hwm⟩ := letWants_spec hp hws
  have hgok : ∀ g', some (letGiven bs ws) = some g' → g'.Ok ρ := by
    rintro g' ⟨⟩
    exact ⟨⟨[], rfl⟩, by simpa [letGiven] using hwm⟩
  obtain ⟨hsigs, -, hres, ρ₁, vs, hev, hI₁, hvs, hty, hw⟩ := ih C sc _ n0 W ρ env act o' hI hgok ho'
  have hvl : vs.length = bs.length := by
    rw [(hw _ rfl [] rfl).length_eq]; simpa [letGiven] using hwl
  have hrl : bs.length = o'.res.length := by
    rw [← hvl, Term.length_evalList hvs, List.length_map]
  have hb : bindIds env (bs.map (·.name)) vs = .ok (pushed (bs.map (·.name)) vs ++ env) :=
    bindIds_of_length (by simp [hvl])
  refine ⟨by rw [Scope.bind_eq]; exact hsigs, ρ₁, _, ?_, Inv.bind hI₁ (by rw [zip_map_term hrl]; exact hvs) hty ?_ hb⟩
  · rw [evalStmt_let, hev, ok_bind, take_of_length hvl, ok_bind, hb]
  · intro r hr
    simp only [List.mem_map] at hr
    obtain ⟨⟨b, r'⟩, hm, rfl⟩ := hr
    exact (hres r' (List.of_mem_zip hm).2).1

/-- A pattern `let` (§10): exactly one value constructor survives forcing, so it heads the right-hand side's
value. -/
theorem patlet_sound {p : Pos} {ct : Bool} {m : Option Mult} {pat : Pattern} {rhs : Expr} (ih : ExprSound rhs)
    (hm : m = none) : StmtSound (.patlet p ct m pat rhs) := by
  sorry


theorem Arg.sizeOf_expr_lt {a : Arg} {args : List Arg} (h : a ∈ args) : sizeOf a.expr < 1 + sizeOf args := by
  have := List.sizeOf_lt_of_mem h
  cases a; simp only [Arg.expr, Arg.mk.sizeOf_spec] at *; omega

theorem Branch.sizeOf_body_lt' {b : Branch} {bs : List Branch} (h : b ∈ bs) : sizeOf b.body < sizeOf bs := by
  have := List.sizeOf_lt_of_mem h
  cases b; simp only [Branch.body, Branch.mk.sizeOf_spec] at *; omega

mutual
/-- The main lemma (SOUNDNESS.md Theorems 5.1 and 6.2, for this checker and evaluator): under the invariant, an
expression that checks runs to values meeting what checking says of them. -/
theorem Expr.sound : (e : Expr) → e.plain = true → ExprSound e
  | .var x, _ => var_sound x
  | .app h args, hp => app_sound fun a ha =>
    Expr.sound a.expr (Arg.plain_expr ▸ Arg.plainList_iff.1 (by simpa [Expr.plain] using hp) a ha)
  | .tuple p es, hp => tuple_sound p fun e he =>
    Expr.sound e (Expr.plainList_iff.1 (by simpa [Expr.plain] using hp) e he)
  | .block ss f, hp => by
    simp only [Expr.plain, Bool.and_eq_true] at hp
    exact block_sound (fun s hs => Stmt.sound s (Stmt.plainList_iff.1 hp.1 s hs)) (Expr.sound f hp.2)
  | .match p m s ann bs, hp => by
    simp only [Expr.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
    exact match_sound (Expr.sound s hp.1.1.2)
      (fun b hb => Expr.sound b.body (Branch.plain_body ▸ Branch.plainList_iff.1 hp.2 b hb)) hp.1.1.1 hp.1.2
  | .sorry .., hp | .removed, hp => by simp [Expr.plain] at hp
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (have := Arg.sizeOf_expr_lt ha; simp only [Expr.app.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem he; simp only [Expr.tuple.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem hs; simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.match.sizeOf_spec]; omega)
    | (have := Branch.sizeOf_body_lt' hb; simp only [Expr.match.sizeOf_spec]; omega)
theorem Stmt.sound : (s : Stmt) → s.plain = true → StmtSound s
  | .let p bs rhs, hp => by
    simp only [Stmt.plain, Bool.and_eq_true] at hp
    exact let_sound (Expr.sound rhs hp.2) hp.1
  | .patlet p ct m pat rhs, hp => by
    simp only [Stmt.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
    exact patlet_sound (Expr.sound rhs hp.2) hp.1
  | .inspect p, _ => inspect_sound p
termination_by s => sizeOf s
decreasing_by all_goals (simp only [Stmt.let.sizeOf_spec, Stmt.patlet.sizeOf_spec]; omega)
end

end Pledge
