import Pledge.Sound.Basic

namespace Pledge

mutual
/-- A checked skeleton term is meant to be untainted and to have a typed value under every valuation satisfying
the scope. -/
theorem checkTerm_sound {C : Ctx} {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} (hT : TermInv sc n0 Sc ρ) :
    ∀ (t : WTerm) {r : Res}, checkTerm C sc t = .ok r →
      r.tainted = false ∧ ∃ v V, r.term.eval ρ [] = some v ∧ HasType Sc v V
  | .var x, r, h => by
    simp only [checkTerm] at h
    split at h
    · rename_i r' hl
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨v, V, hv, hV⟩ := hT.names _ _ hl
      refine ⟨?_, v, V, hv, hV⟩
      simpa [hT.inert.taintedBy] using hT.inert.names _ (lookup_mem hl)
    · simp [notValue, failAt_eq] at h
  | .app hd args, r, h => by
    obtain ⟨k, role, sig, rs, hsig, har, hrs, rfl⟩ : ∃ k role sig rs, sc.sig hd.pos ⟨k, hd.name⟩ = .ok sig ∧
        arity hd.pos hd.name sig.params.length args.length = .ok () ∧
        checkTerms C sc hd.name role sig.params [] args = .ok rs ∧
        r = ⟨.app sig.head (rs.map (·.term)), rs.any (·.tainted) || sc.taintedBy.isSome, false⟩ := by
      unfold checkTerm at h
      split at h
      · simp [failAt_eq, error_bind] at h
      all_goals first
        | (simp [notApplied, failAt_eq, error_bind] at h; done)
        | (obtain ⟨k, -, h⟩ := bind_eq_ok.1 h
           obtain ⟨sig, hsig, h⟩ := bind_eq_ok.1 h
           obtain ⟨u, har, h⟩ := bind_eq_ok.1 h
           obtain ⟨rs, hrs, h⟩ := bind_eq_ok.1 h
           simp only [pure, Except.pure, Except.ok.injEq] at h
           exact ⟨k, _, sig, rs, hsig, har, hrs, h.symm⟩)
    have hfind := Scope.sig_ok hsig
    obtain ⟨hbelow, hbounds, hmult⟩ := hT.sigsOk sig (List.mem_of_find?_eq_some hfind)
    obtain ⟨hun, vs, hvs, ht⟩ := checkTerms_sound hT args (prevv := []) (arity_ok har) rfl hrs
    obtain ⟨V, hV⟩ : ∃ V, sig.ret.eval ρ vs = some V := by
      refine Term.eval_isSome _ ?_ (by rw [ht.length_eq]; exact hbounds)
      simp only [Sig.entriesBelow, Bool.and_eq_true] at hbelow
      exact Term.entriesBelow_mono hT.n0_le _ hbelow.2
    have hhead := Sigs.find_head hfind
    refine ⟨by simpa [hT.inert.taintedBy] using hun, .app sig.head vs, V, by simp [Term.eval, hvs], ?_⟩
    exact (hT.sigs.hasType_app_iff (hhead ▸ hfind)).2 ⟨ht, hV⟩
theorem checkTerms_sound {C : Ctx} {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} (hT : TermInv sc n0 Sc ρ) :
    ∀ (args : List WTerm) {owner role : String} {params : Telescope} {prev rs : List Res} {prevv : List Value},
      params.length = args.length → Term.evalList ρ [] (prev.map (·.term)) = some prevv →
      checkTerms C sc owner role params prev args = .ok rs →
      (∀ r ∈ rs, r.tainted = false) ∧
        ∃ vs, Term.evalList ρ [] (rs.map (·.term)) = some vs ∧ TeleSat Sc ρ params prevv vs
  | [], owner, role, params, prev, rs, prevv, hl, _, h => by
    cases params with
    | cons => simp at hl
    | nil =>
      simp only [checkTerms, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨by simp, [], rfl, .nil⟩
  | a :: as, owner, role, params, prev, rs, prevv, hl, hprev, h => by
    cases params with
    | nil => simp at hl
    | cons p ps =>
      simp only [checkTerms] at h
      obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
      obtain ⟨sc', hsc', h⟩ := bind_eq_ok.1 h
      obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hrt, v, V, hv, hV⟩ := checkTerm_sound hT a hr
      have hw := (against_sound (sc := { sc with holes := [] }) (rs := [r]) hT.sat hT.sigs rfl
        (Term.evalList_singleton.2 ⟨v, hv, rfl⟩) (by simpa using ⟨V, hV⟩) (by simpa using hprev) hsc').2.2
      simp only [WantsSat] at hw
      obtain ⟨hun, vs, hvs, ht⟩ := checkTerms_sound hT as (by simpa using hl)
        (by
          rw [List.map_append, List.map_singleton]
          exact Term.evalList_append hprev (Term.evalList_singleton.2 ⟨v, hv, rfl⟩)) hrest
      refine ⟨?_, v :: vs, Term.evalList_cons_eq_some.2 ⟨v, vs, hv, hvs, rfl⟩,
        TeleSat.cons_iff.2 ⟨v, vs, rfl, WantSat.binderSat (m := p.mult) hw.1, ht⟩⟩
      intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact hrt
      · exact hun r' hr'
end

/-- A checked annotation's type and `is` term have values, and it is untainted. -/
theorem annotate_sound {C : Ctx} {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} {ann : Ann} {ty : Term}
    {is : Option Term} {tainted : Bool} (hT : TermInv sc n0 Sc ρ) (h : annotate C sc ann = .ok (ty, is, tainted)) :
    tainted = false ∧ (∃ A, ty.eval ρ [] = some A) ∧ ∀ e, is = some e → ∃ v, e.eval ρ [] = some v := by
  cases ann with
  | is t =>
    simp only [annotate] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
    obtain ⟨ty', hty, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨hrt, v, V, hv, hV⟩ := checkTerm_sound hT t hr
    exact ⟨hrt, ⟨V, typeOf_sound hT.sat hT.sigs hv hV (Scope.typeOf_ok hty)⟩, fun e he => by cases he; exact ⟨v, hv⟩⟩
  | type t =>
    simp only [annotate] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
    obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨hrt, v, V, hv, hV⟩ := checkTerm_sound hT t hr
    exact ⟨hrt, ⟨v, hv⟩, fun e he => by cases he⟩

theorem abstractChecked_ok {Γ : Entries} {t u : Term} {ids : List Nat} {pos : Pos}
    (h : abstractChecked Γ t ids pos = .ok u) : abstract? Γ t ids = some u := by
  unfold abstractChecked at h
  split at h
  · cases h; assumption
  · simp [internal, failAt_eq] at h

theorem abstracted_ok {Γ : Entries} {name : Option String} {mult : Option Mult} {pos : Pos} {type : Term}
    {is : Option Term} {ids : List Nat} {t : TBinder} (h : abstracted Γ name mult pos type is ids = .ok t) :
    t.name = name ∧ abstract? Γ type ids = some t.type ∧
      (∀ e, is = some e → ∃ e', t.is = some e' ∧ abstract? Γ e ids = some e') ∧ t.mult = mult.getD .many := by
  unfold abstracted at h
  obtain ⟨ty, hty, h⟩ := bind_eq_ok.1 h
  obtain ⟨is', his, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨rfl, abstractChecked_ok hty, fun e he => ?_, rfl⟩
  subst he
  obtain ⟨u, hu, his⟩ := bind_eq_ok.1 his
  simp only [Except.ok.injEq] at his
  subst his
  exact ⟨u, rfl, abstractChecked_ok hu⟩

mutual
/-- A term checked in a scope with no taint is untainted. -/
theorem checkTerm_untainted {C : Ctx} {sc : Scope} (ht : sc.taintedBy = none)
    (hn : ∀ p ∈ sc.names, p.2.tainted = false) : ∀ (t : WTerm) {r : Res}, checkTerm C sc t = .ok r → r.tainted = false
  | .var x, r, h => by
    simp only [checkTerm] at h
    split at h
    · rename_i r' hl
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simpa [ht] using hn _ (lookup_mem hl)
    · simp [notValue, failAt_eq] at h
  | .app hd args, r, h => by
    obtain ⟨k, role, sig, rs, -, -, hrs, rfl⟩ : ∃ k role sig rs, sc.sig hd.pos ⟨k, hd.name⟩ = .ok sig ∧
        arity hd.pos hd.name sig.params.length args.length = .ok () ∧
        checkTerms C sc hd.name role sig.params [] args = .ok rs ∧
        r = ⟨.app sig.head (rs.map (·.term)), rs.any (·.tainted) || sc.taintedBy.isSome, false⟩ := by
      unfold checkTerm at h
      split at h
      · simp [failAt_eq, error_bind] at h
      all_goals first
        | (simp [notApplied, failAt_eq, error_bind] at h; done)
        | (obtain ⟨k, -, h⟩ := bind_eq_ok.1 h
           obtain ⟨sig, hsig, h⟩ := bind_eq_ok.1 h
           obtain ⟨u, har, h⟩ := bind_eq_ok.1 h
           obtain ⟨rs, hrs, h⟩ := bind_eq_ok.1 h
           simp only [pure, Except.pure, Except.ok.injEq] at h
           exact ⟨k, _, sig, rs, hsig, har, hrs, h.symm⟩)
    simpa [ht] using checkTerms_untainted ht hn args hrs
theorem checkTerms_untainted {C : Ctx} {sc : Scope} (ht : sc.taintedBy = none)
    (hn : ∀ p ∈ sc.names, p.2.tainted = false) : ∀ (args : List WTerm) {owner role : String} {params : Telescope}
      {prev rs : List Res}, checkTerms C sc owner role params prev args = .ok rs → ∀ r ∈ rs, r.tainted = false
  | [], owner, role, params, prev, rs, h => by
    simp only [checkTerms, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | a :: as, owner, role, params, prev, rs, h => by
    cases params with
    | nil => simp [checkTerms, internal, failAt_eq] at h
    | cons p ps =>
      simp only [checkTerms] at h
      obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
      obtain ⟨sc', -, h⟩ := bind_eq_ok.1 h
      obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact checkTerm_untainted ht hn a hr
      · exact checkTerms_untainted ht hn as hrest r' hr'
end

theorem annotate_untainted {C : Ctx} {sc : Scope} {ann : Ann} {ty : Term} {is : Option Term} {tainted : Bool}
    (ht : sc.taintedBy = none) (hn : ∀ p ∈ sc.names, p.2.tainted = false)
    (h : annotate C sc ann = .ok (ty, is, tainted)) : tainted = false := by
  cases ann with
  | is t =>
    simp only [annotate] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
    obtain ⟨ty', -, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact checkTerm_untainted ht hn t hr
  | type t =>
    simp only [annotate] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
    obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact checkTerm_untainted ht hn t hr

theorem opening_shape {C : Ctx} {sc : Scope} {name : Id} {ann : Ann} {mult : Option Mult} {kind : String}
    {o : Opening} (h : opening C sc name ann mult kind = .ok o) :
    annotate C sc ann = .ok (o.type, o.is, o.tainted) ∧ o.id = sc.Γ.length ∧ ∃ mk, o.sc = { sc with
      Γ := (openTele sc.Γ [⟨name.name, o.type, o.is, mult.getD .many⟩] [] mk).Γ,
      names := pushed [name] [⟨.entry sc.Γ.length, false, false⟩] ++ sc.names } := by
  unfold opening at h
  obtain ⟨⟨type, is, tainted⟩, ha, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨ha, rfl, _, by rw [Scope.bind_eq]⟩

theorem pushed_untainted : ∀ (ids : List Id) (rs : List Res), (∀ r ∈ rs, r.tainted = false) →
    ∀ p ∈ pushed ids rs, p.2.tainted = false := fun ids rs hr p hp => by
  simp only [pushed, List.mem_reverse, List.mem_filterMap, Option.map_eq_some_iff] at hp
  obtain ⟨⟨i, r⟩, hm, n, -, rfl⟩ := hp
  exact hr r (List.of_mem_zip hm).2

theorem fieldRes_untainted (ids : List Nat) : ∀ r ∈ fieldRes ids, r.tainted = false := by
  simp [fieldRes]

theorem telescope_go_shape {C : Ctx} {kind : String} : ∀ (bs : List Binder) (sc : Scope) (seen : List String)
    (acc : List (Binder × Opening)) {res : Scope × List String × List (Binder × Opening)},
    telescope.go C kind sc seen acc bs = .ok res →
    ∃ new, res.2.2 = acc ++ new ∧ new.map (·.1) = bs ∧ new.map (·.2.id) = List.range' sc.Γ.length bs.length ∧
      res.1.Γ.length = sc.Γ.length + bs.length ∧ sc.Γ <+: res.1.Γ ∧
      res.1 = { sc with
        Γ := res.1.Γ, names := pushed (bs.map (·.name)) (fieldRes (List.range' sc.Γ.length bs.length)) ++ sc.names } ∧
      (sc.taintedBy = none → (∀ p ∈ sc.names, p.2.tainted = false) → ∀ x ∈ new, x.2.tainted = false)
  | [], sc, seen, acc, res, h => by
    simp only [telescope.go, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], by simp, rfl, rfl, by simp, List.prefix_refl _, by simp [pushed, fieldRes], by simp⟩
  | b :: bs, sc, seen, acc, res, h => by
    simp only [telescope.go] at h
    obtain ⟨seen', -, h⟩ := bind_eq_ok.1 h
    obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
    obtain ⟨hann, hid, mk, hsc⟩ := opening_shape ho
    obtain ⟨new, hnew, h1, h2, h3, h4, h5, h6⟩ := telescope_go_shape bs _ _ _ h
    obtain ⟨Δ, hΔ, hΔl, -, -⟩ := openTele_shape sc.Γ [⟨b.name.name, o.type, o.is, b.mult.getD .many⟩] [] mk
    have hoΓ : o.sc.Γ = sc.Γ ++ Δ := by rw [hsc]; exact hΔ
    have hol : o.sc.Γ.length = sc.Γ.length + 1 := by rw [hoΓ, List.length_append, hΔl]; rfl
    refine ⟨(b, o) :: new, by simp [hnew], by simp [h1], ?_, by rw [h3, hol]; simp; omega,
      (hoΓ ▸ List.prefix_append _ _).trans h4, ?_, fun ht hn x hx => ?_⟩
    · simp [h2, hol, hid, List.range'_succ]
    · have hp0 : pushed ([] : List Id) ([] : List Res) = [] := rfl
      rw [h5]
      rw [hsc] at hol ⊢
      simp only at hol ⊢
      rw [hol]
      simp only [List.map_cons, List.length_cons, List.range'_succ, fieldRes, pushed_cons, hp0, List.append_assoc,
        List.nil_append]
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact annotate_untainted ht hn hann
      · refine h6 (by rw [hsc]; exact ht) (fun p hp => ?_) x hx
        rw [hsc] at hp
        rcases List.mem_append.1 hp with hp | hp
        · exact pushed_untainted _ _ (by simp) p hp
        · exact hn p hp

/-- What a checked telescope is, independently of any valuation. -/
theorem telescope_shape {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat} {out : Checked}
    (hp : bs.all Binder.plain = true) (h : telescope C sc bs kind outer = .ok out) :
    out.tele.length = bs.length ∧ out.ids = List.range' sc.Γ.length bs.length ∧
      out.sc.Γ.length = sc.Γ.length + bs.length ∧ sc.Γ <+: out.sc.Γ ∧
      out.sc = Scope.bind { sc with Γ := out.sc.Γ } (bs.map (·.name)) (fieldRes out.ids) ∧
      (∀ b ∈ out.tele, b.mult = .many) ∧
      (sc.taintedBy = none → (∀ p ∈ sc.names, p.2.tainted = false) → out.tainted = false) := by
  unfold telescope at h
  obtain ⟨⟨sc', seen, opens⟩, hgo, h⟩ := bind_eq_ok.1 h
  obtain ⟨tele, htele, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨new, hnew, h1, h2, h3, h4, h5, h6⟩ := telescope_go_shape bs sc [] [] hgo
  simp only [List.nil_append] at hnew
  subst hnew
  obtain ⟨hl, hi⟩ := mapM_ok htele
  have hlen : opens.length = bs.length := by rw [← h1, List.length_map]
  refine ⟨by simp [hl, hlen], h2, h3, h4, by rw [Scope.bind_eq, h2]; exact h5, fun t ht => ?_,
    fun hta hn => by simpa using h6 hta hn⟩
  obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem ht
  have hz : i < (bs.zip opens).length := hl ▸ hi'
  have hb := hi i _ _ (List.getElem?_eq_getElem hz) (List.getElem?_eq_getElem hi')
  have hm : (bs.zip opens)[i].1.mult = none := by
    simpa [Binder.plain] using List.all_eq_true.1 hp _ (List.of_mem_zip (List.getElem_mem hz)).1
  revert hb hm
  generalize (bs.zip opens)[i] = p
  obtain ⟨b, -, o⟩ := p
  intro hb hm
  simp only at hm
  simp [(abstracted_ok hb).2.2.2, hm]

mutual
theorem Term.mapEntries_congr {f g : Nat → Term} :
    ∀ t : Term, (∀ i, t.occurs i = true → f i = g i) → t.mapEntries f = t.mapEntries g
  | .entry i, h => h i (by simp [Term.occurs])
  | .bound _, _ => rfl
  | .app _ as, h => by simp only [Term.mapEntries, Term.mapEntriesList_congr as h]
theorem Term.mapEntriesList_congr {f g : Nat → Term} :
    ∀ as : List Term, (∀ i, Term.occursList i as = true → f i = g i) →
      Term.mapEntriesList f as = Term.mapEntriesList g as
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.mapEntriesList, Term.mapEntries_congr a fun i hi => h i (by simp [Term.occursList, hi]),
      Term.mapEntriesList_congr as fun i hi => h i (by simp [Term.occursList, hi])]
end

mutual
theorem Term.canon_eq_mapEntries (Γ : Entries) :
    ∀ t : Term, t.canon Γ = t.mapEntries fun i => ((Γ[i]?).bind (·.rule)).getD (.entry i)
  | .entry _ => rfl
  | .bound _ => rfl
  | .app _ as => by simp only [Term.canon, Term.mapEntries, Term.canonList_eq_mapEntriesList Γ as]
theorem Term.canonList_eq_mapEntriesList (Γ : Entries) :
    ∀ as : List Term, Term.canonList Γ as = Term.mapEntriesList (fun i => ((Γ[i]?).bind (·.rule)).getD (.entry i)) as
  | [] => rfl
  | a :: as => by
    simp only [Term.canonList, Term.mapEntriesList, Term.canon_eq_mapEntries Γ a, Term.canonList_eq_mapEntriesList Γ as]
end

mutual
theorem Term.lt_of_occurs {n i : Nat} : ∀ t : Term, t.entriesBelow n = true → t.occurs i = true → i < n
  | .entry j, h, ho => by simp only [Term.entriesBelow, Term.occurs, decide_eq_true_eq, beq_iff_eq] at h ho; omega
  | .bound _, _, ho => by simp [Term.occurs] at ho
  | .app _ as, h, ho => Term.lt_of_occursList as h ho
theorem Term.lt_of_occursList {n i : Nat} :
    ∀ as : List Term, Term.entriesBelowList n as = true → Term.occursList i as = true → i < n
  | [], _, ho => by simp [Term.occursList] at ho
  | a :: as, h, ho => by
    simp only [Term.entriesBelowList, Bool.and_eq_true] at h
    simp only [Term.occursList, Bool.or_eq_true] at ho
    exact ho.elim (Term.lt_of_occurs a h.1) (Term.lt_of_occursList as h.2)
end

/-- Abstracting a term over a scope only looks at the entries the term mentions. -/
theorem abstract?_prefix {Γ Γ' : Entries} {t : Term} {ids : List Nat} (hp : Γ <+: Γ')
    (ht : t.entriesBelow Γ.length = true) : abstract? Γ' t ids = abstract? Γ t ids := by
  have hg : ∀ i, t.occurs i = true → Γ'[i]? = Γ[i]? := fun i hi => by
    obtain ⟨l, rfl⟩ := hp
    exact List.getElem?_append_left (Term.lt_of_occurs t ht hi)
  have h1 : t.canon Γ' = t.canon Γ := by
    rw [Term.canon_eq_mapEntries, Term.canon_eq_mapEntries]
    exact Term.mapEntries_congr t fun i hi => by rw [hg i hi]
  have h2 : abstract Γ' t ids = abstract Γ t ids := Term.mapEntries_congr t fun i hi => by simp only [hg i hi]
  simp only [abstract?, h1, h2]

theorem pushed_mem : ∀ {ids : List Id} {rs : List Res} {p : String × Res}, p ∈ pushed ids rs → p.2 ∈ rs := by
  intro ids rs p hp
  simp only [pushed, List.mem_reverse, List.mem_filterMap, Option.map_eq_some_iff] at hp
  obtain ⟨⟨i, r⟩, hm, n, -, rfl⟩ := hp
  exact (List.of_mem_zip hm).2

/-- Opening one binder to a value satisfying it keeps `TermInv`. -/
theorem TermInv.opening {C : Ctx} {sc : Scope} {name : Id} {ann : Ann} {mult : Option Mult} {kind : String}
    {o : Opening} {n0 : Nat} {Sc : Sigs} {ρ : List Value} {v : Value} (hT : TermInv sc n0 Sc ρ)
    (h : opening C sc name ann mult kind = .ok o)
    (hb : BinderSat Sc ρ ⟨name.name, o.type, o.is, mult.getD .many⟩ [] v) : TermInv o.sc n0 Sc (ρ ++ [v]) := by
  obtain ⟨-, -, mk, hsc⟩ := opening_shape h
  obtain ⟨A, hA, hv, his⟩ := hb
  obtain ⟨hs, -⟩ := openTele_sound mk hT.sat (rfl : Term.evalList ρ [] [] = some [])
    (TeleSat.cons_iff.2 ⟨v, [], rfl, ⟨A, hA, hv, his⟩, .nil⟩)
  have hlen := hT.sat.1
  rw [hsc]
  refine ⟨hs, by simp; have := hT.n0_le; omega,
    hT.sigs.frame [v] fun sig hs => Sig.entriesBelow_mono hT.n0_le (hT.sigsOk sig hs).1, hT.sigsOk,
    fun n r hl => ?_, ⟨hT.inert.holes, hT.inert.taintedBy, fun p hp => ?_⟩⟩
  · simp only [Scope.lookup, lookup_append] at hl
    cases hx : (pushed [name] [(⟨.entry sc.Γ.length, false, false⟩ : Res)]).lookup n with
    | some r' =>
      rw [hx, Option.some_or, Option.some.injEq] at hl
      subst hl
      have := pushed_mem (lookup_mem hx)
      simp only [List.mem_singleton] at this
      rw [this]
      exact ⟨v, A, by simp [Term.eval, ← hlen], hv⟩
    | none =>
      rw [hx, Option.none_or] at hl
      obtain ⟨w, W, hw, hW⟩ := hT.names n r hl
      exact ⟨w, W, Term.eval_frame_ρ [v] hw, hW⟩
  · rcases List.mem_append.1 hp with hp | hp
    · exact pushed_untainted _ _ (by simp) p hp
    · exact hT.inert.names p hp

theorem telescope_go_sound {C : Ctx} {kind : String} {n0 : Nat} {Sc : Sigs} : ∀ (bs : List Binder) (sc : Scope)
    (seen : List String) (acc : List (Binder × Opening)) {res : Scope × List String × List (Binder × Opening)}
    (ρc vs : List Value), telescope.go C kind sc seen acc bs = .ok res → TermInv sc n0 Sc ρc →
    vs.length = bs.length →
    (∀ m b o v (Γm : Entries), res.2.2[acc.length + m]? = some (b, o) → vs[m]? = some v →
      Sat Sc Γm (ρc ++ vs.take m) → Γm <+: res.1.Γ → (∃ A, o.type.eval (ρc ++ vs.take m) [] = some A) →
      (∀ e, o.is = some e → ∃ w, e.eval (ρc ++ vs.take m) [] = some w) →
      BinderSat Sc (ρc ++ vs.take m) ⟨b.name.name, o.type, o.is, b.mult.getD .many⟩ [] v) →
    TermInv res.1 n0 Sc (ρc ++ vs)
  | [], sc, seen, acc, res, ρc, vs, h, hT, hl, _ => by
    simp only [telescope.go, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [List.eq_nil_of_length_eq_zero hl, List.append_nil]
    exact hT
  | b :: bs, sc, seen, acc, res, ρc, vs, h, hT, hl, hb => by
    simp only [telescope.go] at h
    obtain ⟨seen', -, h⟩ := bind_eq_ok.1 h
    obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
    obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => simp at hl
      | cons v vs' => exact ⟨v, vs', rfl⟩
    obtain ⟨new, hnew, -, -, -, h4, -, -⟩ := telescope_go_shape bs _ _ _ h
    obtain ⟨hann, -, mk, hsc⟩ := opening_shape ho
    obtain ⟨-, ⟨A, hA⟩, his⟩ := annotate_sound hT hann
    have hpre : sc.Γ <+: o.sc.Γ := by
      obtain ⟨Δ, hΔ, -⟩ := openTele_shape sc.Γ [⟨b.name.name, o.type, o.is, b.mult.getD .many⟩] [] mk
      rw [hsc]; simp only; rw [hΔ]; exact List.prefix_append _ _
    have hb0 := hb 0 b o v sc.Γ (by rw [hnew]; simp) rfl (by simpa using hT.sat) (hpre.trans h4)
      ⟨A, by simpa using hA⟩ (by simpa using his)
    simp only [List.take_zero, List.append_nil] at hb0
    have := telescope_go_sound bs o.sc seen' (acc ++ [(b, o)]) (ρc ++ [v]) vs' h (TermInv.opening hT ho hb0)
      (by simpa using hl) fun m b' o' v' Γm h1 h2 h3 h4 h5 h6 => by
        have := hb (m + 1) b' o' v' Γm (by
          rw [show acc.length + (m + 1) = (acc ++ [(b, o)]).length + m by
            rw [List.length_append, List.length_singleton]; omega]
          exact h1) (by simpa using h2) (by simpa using h3) h4
          (by simpa using h5) (by simpa using h6)
        simpa using this
    simpa using this

/-- Opening a checked telescope to values satisfying it, after the values `outerv` of the entries `outer` it was
abstracted over first, satisfies the scope it was checked in, extended by those values. -/
theorem telescope_sound {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat} {out : Checked}
    {n0 : Nat} {Sc : Sigs} {ρ outerv vs : List Value} (hT : TermInv sc n0 Sc ρ) (hp : bs.all Binder.plain = true)
    (h : telescope C sc bs kind outer = .ok out) (houter : Term.evalList ρ [] (outer.map .entry) = some outerv)
    (hvs : TeleSat Sc ρ out.tele outerv vs) : TermInv out.sc n0 Sc (ρ ++ vs) := by
  unfold telescope at h
  obtain ⟨⟨sc', seen, opens⟩, hgo, h⟩ := bind_eq_ok.1 h
  obtain ⟨tele, htele, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨new, hnew, h1, h2, -, -, -, -⟩ := telescope_go_shape bs sc [] [] hgo
  simp only [List.nil_append] at hnew
  subst hnew
  obtain ⟨hl, hi⟩ := mapM_ok htele
  have hlen : opens.length = bs.length := by rw [← h1, List.length_map]
  have hρ := hT.sat.1
  have hol : outerv.length = outer.length := by simpa using Term.length_evalList houter
  refine telescope_go_sound bs sc [] [] ρ vs hgo hT (by rw [hvs.length_eq, hl]; simp [hlen])
    fun m b o v Γm hbo hv hsat hpre hA his => ?_
  simp only [List.length_nil, Nat.zero_add] at hbo
  have hbm : bs[m]? = some b := by rw [← h1, List.getElem?_map, hbo]; rfl
  obtain ⟨t, ht⟩ : ∃ t, tele[m]? = some t := by
    refine ⟨_, List.getElem?_eq_getElem ?_⟩
    rw [hl, List.length_zip, hlen, Nat.min_self, ← hlen]
    exact (List.getElem?_eq_some_iff.1 hbo).1
  obtain ⟨-, hty, his', -⟩ := abstracted_ok (hi m (b, b, o) t (List.getElem?_zip_eq_some.2 ⟨hbm, hbo⟩) ht)
  obtain ⟨A', hA', hvA, hisv⟩ := (TeleSat.iff_getElem?.1 hvs).2 m t v ht hv
  rw [h2] at hty his'
  have henv : ∀ k i, (outer ++ List.range' sc.Γ.length bs.length)[k]? = some i →
      (outerv ++ vs.take m)[k]? = (ρ ++ vs.take m)[i]? := fun k i hk => by
    by_cases hk' : k < outer.length
    · rw [List.getElem?_append_left hk'] at hk
      rw [List.getElem?_append_left (hol ▸ hk')]
      have := (Term.evalList_eq_some_iff.1 houter).2 k (.entry i) (by simp [hk])
      simp only [Term.eval] at this
      rw [← this]
      have hi : i < ρ.length :=
        (List.getElem?_eq_some_iff.1 (this.trans (List.getElem?_eq_getElem (by rw [hol]; exact hk')))).1
      exact (List.getElem?_append_left hi).symm
    · rw [List.getElem?_append_right (by omega)] at hk
      rw [List.getElem?_append_right (by omega), hol]
      have hlt : k - outer.length < bs.length := by
        have := (List.getElem?_eq_some_iff.1 hk).1; simpa using this
      rw [List.getElem?_range' hlt] at hk
      cases hk
      rw [List.getElem?_append_right (by omega), hρ]
      congr 1; omega
  have key : ∀ u w, abstract? sc'.Γ u (outer ++ List.range' sc.Γ.length bs.length) = some w →
      (∃ a, u.eval (ρ ++ vs.take m) [] = some a) → w.eval (ρ ++ vs.take m) (outerv ++ vs.take m) =
        u.eval (ρ ++ vs.take m) [] := fun u w hw ⟨a, ha⟩ => by
    rw [abstract?_prefix hpre (by rw [← hsat.1]; exact Term.entriesBelow_of_eval u ha)] at hw
    exact abstract?_eval hsat.rulesHold hw henv
  refine ⟨A', ?_, hvA, fun e he => ?_⟩
  · rw [← key _ _ hty hA]; exact Term.eval_frame_ρ _ hA'
  · obtain ⟨e', he', hab⟩ := his' e he
    rw [← key _ _ hab (his e he)]; exact Term.eval_frame_ρ _ (hisv e' he')

/-- What a `match` annotation or `sorry`'s telescope stands for has values for its outer environment and no erased
entry. -/
theorem annotation_sound {C : Ctx} {sc : Scope} {g : Option Given} {ann : Tele} {tele : Telescope} {env : List Term}
    {ρ : List Value} (hp : ann.plain = true) (hg : ∀ g', g = some g' → g'.Ok ρ)
    (h : annotation C sc g ann = .ok (tele, env)) :
    (∃ envv, Term.evalList ρ [] env = some envv) ∧ ∀ b ∈ tele, b.mult = .many := by
  cases ann with
  | binders bs =>
    simp only [annotation] at h
    obtain ⟨out, hout, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨[], rfl⟩, (telescope_shape (by simpa [Tele.plain] using hp) hout).2.2.2.2.2.1⟩
  | hole p =>
    simp only [annotation] at h
    split at h
    · rename_i g'
      split at h
      · obtain ⟨tl, htl, h⟩ := bind_eq_ok.1 h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hl, hi⟩ := mapM_ok htl
        refine ⟨(hg g' rfl).env, fun b hb => ?_⟩
        obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hb
        obtain ⟨w, hw⟩ : ∃ w, g'.wants[i]? = some w := ⟨_, List.getElem?_eq_getElem (hl ▸ hi')⟩
        have := hi i w _ hw (List.getElem?_eq_getElem hi')
        split at this
        · simp only [pure, Except.pure, Except.ok.injEq] at this
          rw [← this]
          exact (hg g' rfl).mult w (List.mem_of_getElem? hw)
        · simp [internal, failAt_eq] at this
      · simp [failAt_eq] at h
    · simp [failAt_eq] at h

theorem letWants_go_length {C : Ctx} : ∀ (bs : List LetBinder) (sc : Scope) (untyped : List String)
    (acc : List (Option Opening)) {res : Scope × List (Option Opening)},
    letWants.go C sc untyped acc bs = .ok res → res.2.length = acc.length + bs.length
  | [], sc, untyped, acc, res, h => by
    simp only [letWants.go, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | b :: bs, sc, untyped, acc, res, h => by
    simp only [letWants.go] at h
    split at h
    · split at h
      · simp [failAt_eq, bind, Except.bind] at h
      · obtain ⟨o, -, h⟩ := bind_eq_ok.1 h
        have := letWants_go_length bs _ _ _ h; simp at this ⊢; omega
    · have := letWants_go_length bs _ _ _ h; simp at this ⊢; omega

/-- What a tuple `let` gives its right-hand side: one entry per binder, none erased. -/
theorem letWants_spec {C : Ctx} {sc : Scope} {bs : List LetBinder} {ws : List Want}
    (hp : bs.all (·.mult.isNone) = true) (h : letWants C sc bs = .ok ws) :
    ws.length = bs.length ∧ ∀ w ∈ ws, w.mult = .many := by
  unfold letWants at h
  obtain ⟨⟨sc', opens⟩, hgo, h⟩ := bind_eq_ok.1 h
  have hol := letWants_go_length bs sc [] [] hgo
  simp only [List.length_nil, Nat.zero_add] at hol
  obtain ⟨hl, hi⟩ := mapM_ok h
  refine ⟨by simp [hl, hol], fun w hw => ?_⟩
  obtain ⟨i, hi', hwi⟩ := List.getElem_of_mem hw
  have hz : i < (bs.zip opens).length := hl ▸ hi'
  have hb := hi i _ w (List.getElem?_eq_getElem hz) (by rw [List.getElem?_eq_getElem hi', hwi])
  have hm : (bs.zip opens)[i].1.mult = none := by
    simpa using List.all_eq_true.1 hp _ (List.of_mem_zip (List.getElem_mem hz)).1
  revert hb hm
  generalize (bs.zip opens)[i] = p
  obtain ⟨b, oo⟩ := p
  intro hb hm
  cases oo with
  | some o =>
    obtain ⟨t, ht, hb⟩ := bind_eq_ok.1 hb
    simp only [pure, Except.pure, Except.ok.injEq] at hb
    subst hb
    simp only at hm
    simp [Want.of, (abstracted_ok ht).2.2.2, hm]
  | none =>
    simp only [pure, Except.pure, Except.ok.injEq] at hb
    subst hb
    simp only at hm
    simp [hm]

end Pledge
