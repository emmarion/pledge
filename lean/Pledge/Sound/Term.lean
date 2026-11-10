import Pledge.Sound.Rel

namespace Pledge

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
  obtain ⟨i, hi⟩ := pushed_mem hp
  exact hr _ (List.mem_of_getElem? hi)

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
    (h : telescope C sc bs kind outer = .ok out) :
    out.tele.length = bs.length ∧ out.ids = List.range' sc.Γ.length bs.length ∧
      out.sc.Γ.length = sc.Γ.length + bs.length ∧ sc.Γ <+: out.sc.Γ ∧
      out.sc = Scope.bind { sc with Γ := out.sc.Γ } (bs.map (·.name)) (fieldRes out.ids) ∧
      (sc.taintedBy = none → (∀ p ∈ sc.names, p.2.tainted = false) → out.tainted = false) := by
  unfold telescope at h
  obtain ⟨⟨sc', seen, opens⟩, hgo, h⟩ := bind_eq_ok.1 h
  obtain ⟨tele, htele, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨new, hnew, h1, h2, h3, h4, h5, h6⟩ := telescope_go_shape bs sc [] [] hgo
  simp only [List.nil_append] at hnew
  subst hnew
  obtain ⟨hl, -⟩ := mapM_ok htele
  have hlen : opens.length = bs.length := by rw [← h1, List.length_map]
  exact ⟨by simp [hl, hlen], h2, h3, h4, by rw [Scope.bind_eq, h2]; exact h5, fun hta hn => by simpa using h6 hta hn⟩

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

theorem WantsSat.lengths {S : Sigs} {ρ : List Value} :
    ∀ {ws : List Want} {env : List Value} {ts : List Bool} {vs : List Value}, WantsSat S ρ ws env ts vs →
      vs.length = ws.length ∧ ts.length = ws.length
  | [], _, [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, _, _ :: _, _ :: _, h => by simp [(WantsSat.lengths h.2).1, (WantsSat.lengths h.2).2]
  | [], _, [], _ :: _, h | [], _, _ :: _, _, h | _ :: _, _, [], _, h | _ :: _, _, _ :: _, [], h => h.elim

theorem WantSat.frame {S : Sigs} {ρ env : List Value} {w : Want} {t : Bool} {v : Value} (ρ' : List Value)
    (h : WantSat S ρ w env t v) : WantSat S (ρ ++ ρ') w env t v :=
  ⟨fun T hT => let ⟨A, hA, h1, h2, h3⟩ := h.1 T hT; ⟨A, Term.eval_frame_ρ ρ' hA, h1, h2, h3⟩,
    fun e he => Term.eval_frame_ρ ρ' (h.2 e he)⟩

theorem WantsSat.frame {S : Sigs} {ρ : List Value} (ρ' : List Value) :
    ∀ {ws : List Want} {env : List Value} {ts : List Bool} {vs : List Value}, WantsSat S ρ ws env ts vs →
      WantsSat S (ρ ++ ρ') ws env ts vs
  | [], _, [], [], _ => trivial
  | _ :: _, _, _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨h1.frame ρ', WantsSat.frame ρ' h2⟩
  | [], _, [], _ :: _, h | [], _, _ :: _, _, h | _ :: _, _, [], _, h | _ :: _, _, _ :: _, [], h => h.elim

/-- Weakening which values must be typed. -/
theorem WantsSat.weaken {S : Sigs} {ρ : List Value} :
    ∀ {ws : List Want} {env : List Value} {ts ts' : List Bool} {vs : List Value}, WantsSat S ρ ws env ts vs →
      ts'.length = ts.length → (∀ (i : Nat), ts'[i]? = some true → ts[i]? = some true) → WantsSat S ρ ws env ts' vs
  | [], _, [], [], [], _, _, _ => trivial
  | _ :: _, _, t :: _, t' :: _, _ :: _, ⟨⟨h1, h2⟩, h3⟩, hl, hi =>
    ⟨⟨fun T hT => let ⟨A, hA, a, b, c⟩ := h1 T hT
        ⟨A, hA, a, b, fun ht => c (by simpa using hi 0 (by simp [ht]))⟩, h2⟩,
      WantsSat.weaken h3 (by simpa using hl) fun i h => by simpa using hi (i + 1) (by simpa using h)⟩
  | [], _, [], _ :: _, _, _, hl, _ => by simp at hl
  | [], _, _ :: _, _, _, h, _, _ => h.elim
  | [], _, [], [], _ :: _, h, _, _ => h.elim
  | _ :: _, _, [], _, _, h, _, _ => h.elim
  | _ :: _, _, _ :: _, [], _, _, hl, _ => by simp at hl
  | _ :: _, _, _ :: _, _ :: _, [], h, _, _ => h.elim

/-- Values meeting a telescope's wants meet it in the sense of `TeleOk`. -/
theorem WantsSat.teleOk {S : Sigs} {ρ : List Value} (typed : Nat → Bool) :
    ∀ {tele : Telescope} {env : List Value} {ts : List Bool} {vs : List Value},
      WantsSat S ρ (tele.map Want.of) env ts vs → (∀ k, typed k = true → ts[k]? = some true) →
      TeleOk S ρ typed tele env vs
  | [], _, [], [], _, _ => trivial
  | b :: tele, env, t :: ts, v :: vs, ⟨⟨h1, h2⟩, h3⟩, hty => by
    obtain ⟨A, hA, a, c, d⟩ := h1 b.type rfl
    exact ⟨⟨A, hA, a, c, fun h => d (by simpa using hty 0 h)⟩, h2,
      WantsSat.teleOk (fun k => typed (k + 1)) h3 fun k h => by simpa using hty (k + 1) h⟩
  | [], _, _ :: _, _, h, _ | [], _, [], _ :: _, h, _ | _ :: _, _, [], _, h, _ | _ :: _, _, _ :: _, [], h, _ => h.elim

/-- Typed values meeting a telescope's wants satisfy it. -/
theorem WantsSat.teleSat {S : Sigs} {ρ : List Value} :
    ∀ {tele : Telescope} {env : List Value} {ts : List Bool} {vs : List Value},
      WantsSat S ρ (tele.map Want.of) env ts vs → (∀ t ∈ ts, t = true) → TeleSat S ρ tele env vs
  | [], _, [], [], _, _ => .nil
  | b :: tele, env, t :: ts, v :: vs, ⟨⟨h1, h2⟩, h3⟩, hty => by
    obtain ⟨A, hA, -, -, d⟩ := h1 b.type rfl
    exact .cons hA (d (hty t List.mem_cons_self)) h2
      (WantsSat.teleSat h3 fun t' h => hty t' (List.mem_cons_of_mem _ h))
  | [], _, _ :: _, _, h, _ | [], _, [], _ :: _, h, _ | _ :: _, _, [], _, h, _ | _ :: _, _, _ :: _, [], h, _ => h.elim

/-- Values satisfying a telescope meet its wants, typed. -/
theorem TeleSat.wantsSat {S : Sigs} {ρ : List Value} (hJ : S.find junkHead = none) :
    ∀ {tele : Telescope} {env vs : List Value}, TeleSat S ρ tele env vs →
      WantsSat S ρ (tele.map Want.of) env (tele.map fun _ => true) vs
  | [], _, _, h => by rw [TeleSat.nil_iff.1 h]; trivial
  | _ :: _, _, _, h => by
    obtain ⟨v, vs', rfl, ⟨A, hA, hv, his⟩, ht⟩ := TeleSat.cons_iff.1 h
    exact ⟨⟨fun T hT => by cases hT; exact ⟨A, hA, hv.noRemoved, hv.wtype hJ, fun _ => hv⟩, his⟩,
      TeleSat.wantsSat hJ ht⟩

theorem WantsCons.frame {S : Sigs} {ρ : List Value} (ρ' : List Value) :
    ∀ {ws : List Want} {env : List Value}, WantsCons S ρ ws env → WantsCons S (ρ ++ ρ') ws env
  | [], _, _ => trivial
  | w :: ws, env, ⟨h1, h2, h3⟩ => by
    refine ⟨fun T hT => ?_, fun e he => ?_, fun v hv => WantsCons.frame ρ' (h3 v ⟨fun T hT => ?_, fun e he => ?_⟩)⟩
    · obtain ⟨A, hA, h⟩ := h1 T hT; exact ⟨A, Term.eval_frame_ρ ρ' hA, h⟩
    · obtain ⟨v, hv, h, h'⟩ := h2 e he
      refine ⟨v, Term.eval_frame_ρ ρ' hv, h, fun T A hT hA => ?_⟩
      obtain ⟨A', hA', -⟩ := h1 T hT
      rw [Term.eval_frame_ρ ρ' hA'] at hA
      obtain rfl := Option.some.inj hA
      exact h' T _ hT hA'
    · obtain ⟨A', hA', -⟩ := h1 T hT
      obtain ⟨A, hA, a, b, c⟩ := hv.1 T hT
      rw [Term.eval_frame_ρ ρ' hA'] at hA
      obtain rfl := Option.some.inj hA
      exact ⟨_, hA', a, b, c⟩
    · obtain ⟨u, hu, -⟩ := h2 e he
      have := hv.2 e he
      rw [Term.eval_frame_ρ ρ' hu] at this
      rw [hu, this]

/-- `WantsCons` does not depend on the wants' multiplicities. -/
theorem WantsCons.congr {S : Sigs} {ρ : List Value} :
    ∀ {ws ws' : List Want} {env : List Value}, ws.length = ws'.length →
      (∀ (i : Nat) (w w' : Want), ws[i]? = some w → ws'[i]? = some w' → w.type = w'.type ∧ w.is = w'.is) →
      WantsCons S ρ ws env → WantsCons S ρ ws' env
  | [], [], _, _, _, _ => trivial
  | w :: ws, w' :: ws', env, hl, hw, ⟨h1, h2, h3⟩ => by
    obtain ⟨ht, hi⟩ := hw 0 w w' rfl rfl
    refine ⟨fun T hT => h1 T (ht ▸ hT), fun e he => ?_, fun v hv => WantsCons.congr (by simpa using hl)
      (fun i a b ha hb => hw (i + 1) a b (by simpa using ha) (by simpa using hb)) (h3 v ?_)⟩
    · obtain ⟨v, hv, a, b⟩ := h2 e (hi ▸ he)
      exact ⟨v, hv, a, fun T A hT hA => b T A (ht ▸ hT) hA⟩
    · exact ⟨fun T hT => hv.1 T (ht ▸ hT), fun e he => hv.2 e (hi ▸ he)⟩
  | [], _ :: _, _, hl, _, _ | _ :: _, [], _, hl, _, _ => by simp at hl

/-- Wants that can be opened are opened to values meeting them, by their heads: `junk` for a want without an `is`
clause (§12). -/
theorem WantsCons.open {S : Sigs} {ρ : List Value} :
    ∀ {ws : List Want} {env : List Value}, WantsCons S ρ ws env →
      ∃ vs, WantsSat S ρ ws env (ws.map fun _ => false) vs
  | [], _, _ => ⟨[], trivial⟩
  | w :: ws, env, ⟨h1, h2, h3⟩ => by
    obtain ⟨v, hv⟩ : ∃ v, WantSat S ρ w env false v := by
      cases hi : w.is with
      | some e =>
        obtain ⟨v, hv, hr, hw⟩ := h2 e hi
        exact ⟨v, ⟨fun T hT => let ⟨A, hA, _⟩ := h1 T hT; ⟨A, hA, hr, hw T A hT hA, by simp⟩,
          fun e' he' => by rw [hi] at he'; cases he'; exact hv⟩⟩
      | none =>
        cases ht : w.type with
        | some T =>
          obtain ⟨A, hA, hr⟩ := h1 T ht
          exact ⟨.junk A, ⟨fun T' hT' => by
            rw [ht] at hT'; cases hT'
            exact ⟨A, hA, by rw [Value.noRemoved_junk]; exact hr, WType.junk S A, by simp⟩,
            fun e he => by rw [hi] at he; cases he⟩⟩
        | none => exact ⟨.junk .TYPE, ⟨fun T hT => (by rw [ht] at hT; cases hT), fun e he => (by rw [hi] at he; cases he)⟩⟩
    obtain ⟨vs, hvs⟩ := WantsCons.open (h3 v hv)
    exact ⟨v :: vs, hv, hvs⟩

/-- What checking a skeleton term or a telescope needs of a scope (§3, §6): ideal values satisfying it, bridged
signatures, and ideal values for every name, typed for the untainted ones. -/
structure TermInv (sc : Scope) (n0 : Nat) (Sc : Sigs) (ρ : List Value) : Prop where
  sat : Sat Sc sc.Γ ρ
  n0_le : n0 ≤ ρ.length
  sigs : SigsClose sc.sigs ρ Sc
  sigsOk : SigsOk n0 sc.sigs
  noJunk : Sc.find junkHead = none
  names : ∀ n r, sc.lookup n = some r → ∃ v, r.term.eval ρ [] = some v ∧ (r.tainted = false → ∃ V, HasType Sc v V)

/-- `TermInv` with `WSat` and no typing: what `telescope_cons` needs, values of tainted results included. -/
structure WTermInv (sc : Scope) (n0 : Nat) (Sc : Sigs) (ρ : List Value) : Prop where
  sat : WSat Sc sc.Γ ρ
  n0_le : n0 ≤ ρ.length
  sigs : SigsClose sc.sigs ρ Sc
  sigsOk : SigsOk n0 sc.sigs
  noJunk : Sc.find junkHead = none
  names : ∀ n r, sc.lookup n = some r → ∃ v, r.term.eval ρ [] = some v

theorem TermInv.weak {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} (h : TermInv sc n0 Sc ρ) :
    WTermInv sc n0 Sc ρ :=
  ⟨h.sat.1, h.n0_le, h.sigs, h.sigsOk, h.noJunk, fun n r hn => let ⟨v, hv, _⟩ := h.names n r hn; ⟨v, hv⟩⟩

theorem Inv.termInv {C : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    (hI : Inv C sc n0 W ρ act) : TermInv sc n0 W.Sc ρ :=
  ⟨hI.sat, hI.length, hI.sigs ρ hI.agree, hI.sigsOk, hI.noJunk, hI.names⟩

mutual
/-- A checked skeleton term has a value when every name has one. -/
theorem checkTerm_eval {C : Ctx} {sc : Scope} {ρ : List Value}
    (hn : ∀ n r, sc.lookup n = some r → ∃ v, r.term.eval ρ [] = some v) :
    ∀ (t : WTerm) {r : Res}, checkTerm C sc t = .ok r → ∃ v, r.term.eval ρ [] = some v
  | .var x, r, h => by
    simp only [checkTerm] at h
    split at h
    · rename_i r' hl
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨v, hv⟩ := hn _ _ hl
      exact ⟨v, hv⟩
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
    obtain ⟨vs, hvs⟩ := checkTerms_eval hn args hrs
    exact ⟨_, Term.eval_app.2 ⟨vs, hvs, rfl⟩⟩
theorem checkTerms_eval {C : Ctx} {sc : Scope} {ρ : List Value}
    (hn : ∀ n r, sc.lookup n = some r → ∃ v, r.term.eval ρ [] = some v) :
    ∀ (args : List WTerm) {owner role : String} {params : Telescope} {prev rs : List Res},
      checkTerms C sc owner role params prev args = .ok rs → ∃ vs, Term.evalList ρ [] (rs.map (·.term)) = some vs
  | [], owner, role, params, prev, rs, h => by
    simp only [checkTerms, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl⟩
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
      obtain ⟨v, hv⟩ := checkTerm_eval hn a hr
      obtain ⟨vs, hvs⟩ := checkTerms_eval hn as hrest
      exact ⟨v :: vs, Term.evalList_cons_eq_some.2 ⟨v, vs, hv, hvs, rfl⟩⟩
end

/-- A checked annotation's type and `is` term have values (§6). -/
theorem annotate_eval {C : Ctx} {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} {ann : Ann} {ty : Term}
    {is : Option Term} {tainted : Bool} (hT : WTermInv sc n0 Sc ρ) (h : annotate C sc ann = .ok (ty, is, tainted)) :
    (∃ A, ty.eval ρ [] = some A) ∧ ∀ e, is = some e → ∃ v, e.eval ρ [] = some v := by
  sorry

/-- Opening a checked telescope to values satisfying it, after the values `outerv` of the entries `outer` it was
abstracted over first, satisfies the scope it was checked in, extended by those values (cf. stage 1's
`telescope_sound`). -/
theorem telescope_sound {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat} {out : Checked}
    {n0 : Nat} {Sc : Sigs} {ρ outerv vs : List Value} (hT : TermInv sc n0 Sc ρ)
    (h : telescope C sc bs kind outer = .ok out) (houter : Term.evalList ρ [] (outer.map .entry) = some outerv)
    (hvs : TeleSat Sc ρ out.tele outerv vs) : TermInv out.sc n0 Sc (ρ ++ vs) := by
  sorry

/-- `telescope_sound` for values that only meet the telescope by their heads, as a tainted call's arguments may. -/
theorem telescope_wsound {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat} {out : Checked}
    {n0 : Nat} {Sc : Sigs} {ρ outerv vs : List Value} (hT : WTermInv sc n0 Sc ρ)
    (h : telescope C sc bs kind outer = .ok out) (houter : Term.evalList ρ [] (outer.map .entry) = some outerv)
    (hvs : WantsSat Sc ρ (out.tele.map Want.of) outerv (out.tele.map fun _ => false) vs) :
    WTermInv out.sc n0 Sc (ρ ++ vs) := by
  sorry

/-- A checked telescope can be opened (`WantsCons`): an `is` binder's type is its term's type (§6), so whatever
values the other binders take, by their types' heads, an `is` binder's value has its type by its head. -/
theorem telescope_cons {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat} {out : Checked}
    {n0 : Nat} {Sc : Sigs} {ρ outerv : List Value} (hT : WTermInv sc n0 Sc ρ)
    (h : telescope C sc bs kind outer = .ok out) (houter : Term.evalList ρ [] (outer.map .entry) = some outerv) :
    WantsCons Sc ρ (out.tele.map Want.of) outerv := by
  sorry

/-- What a tuple `let` whose binders are all annotated gives its right-hand side can be opened. -/
theorem letWants_cons {C : Ctx} {sc : Scope} {bs : List LetBinder} {ws : List Want} {n0 : Nat} {Sc : Sigs}
    {ρ : List Value} (hT : WTermInv sc n0 Sc ρ) (h : letWants C sc bs = .ok ws) (hall : bs.all (·.ann.isSome) = true) :
    WantsCons Sc ρ ws [] := by
  sorry

/-- What a `match` annotation or `sorry`'s telescope stands for: written, it is a telescope checked in the scope,
over no outer entries; `_`, it is the whole telescope given at the position, with its environment (§10, §12). -/
theorem annotation_shape {C : Ctx} {sc : Scope} {g : Option Given} {ann : Tele} {tele : Telescope}
    {env : List Term} (h : annotation C sc g ann = .ok (tele, env)) :
    (∃ bs out, ann = .binders bs ∧ telescope C sc bs "binder" = .ok out ∧ tele = out.tele ∧ env = [] ∧
      tele.length = bs.length) ∨
    (∃ p g', ann = .hole p ∧ g = some g' ∧ g'.whole = true ∧ tele.map Want.of = g'.wants ∧ env = g'.env) := by
  cases ann with
  | binders bs =>
    simp only [annotation] at h
    obtain ⟨out, hout, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inl ⟨bs, out, rfl, hout, rfl, rfl, (telescope_shape hout).1⟩
  | hole p =>
    simp only [annotation] at h
    split at h
    · rename_i g'
      split at h
      · rename_i hw
        obtain ⟨tl, htl, h⟩ := bind_eq_ok.1 h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine .inr ⟨p, g', rfl, rfl, hw, ?_, rfl⟩
        obtain ⟨hl, hi⟩ := mapM_ok htl
        apply List.ext_getElem?
        intro i
        rw [List.getElem?_map]
        cases hw' : g'.wants[i]? with
        | none =>
          have : tl[i]? = none := by rw [List.getElem?_eq_none_iff] at hw' ⊢; omega
          simp [this]
        | some w =>
          obtain ⟨b, hb⟩ : ∃ b, tl[i]? = some b := by
            have : i < tl.length := by rw [hl]; exact (List.getElem?_eq_some_iff.1 hw').1
            exact ⟨_, List.getElem?_eq_getElem this⟩
          have := hi i w b hw' hb
          rw [hb]
          split at this
          · rename_i t ht
            simp only [pure, Except.pure, Except.ok.injEq] at this
            subst this
            simp [Want.of, ← ht]
          · simp [internal, failAt_eq] at this
      · simp [failAt_eq] at h
    · simp [failAt_eq] at h

/-- What a `match` annotation or `sorry`'s telescope stands for has values for its outer environment and can be
opened. -/
theorem annotation_cons {C : Ctx} {sc : Scope} {g : Option Given} {ann : Tele} {tele : Telescope} {env : List Term}
    {n0 : Nat} {Sc : Sigs} {ρ : List Value} (hT : WTermInv sc n0 Sc ρ) (hg : ∀ g', g = some g' → g'.Ok Sc ρ)
    (h : annotation C sc g ann = .ok (tele, env)) :
    ∃ envv, Term.evalList ρ [] env = some envv ∧ WantsCons Sc ρ (tele.map Want.of) envv := by
  rcases annotation_shape h with ⟨bs, out, rfl, hout, rfl, rfl, -⟩ | ⟨p, g', rfl, rfl, hw, hte, rfl⟩
  · exact ⟨[], rfl, telescope_cons (outer := []) hT hout rfl⟩
  · obtain ⟨envv, henv⟩ := (hg g' rfl).env
    exact ⟨envv, henv, hte ▸ (hg g' rfl).cons hw envv henv⟩

theorem annotation_annTake {C : Ctx} {sc : Scope} {g : Option Given} {ann : Tele} {tele : Telescope}
    {env : List Term} {vs vs' : List Value} (h : annotation C sc g ann = .ok (tele, env))
    (ht : take tele.length vs = .ok vs') : ∃ us, annTake ann vs = .ok us ∧ take tele.length us = .ok vs' := by
  rcases annotation_shape h with ⟨bs, out, rfl, -, -, -, hl⟩ | ⟨p, g', rfl, -, -, -, -⟩
  · exact ⟨vs', by rw [annTake, ← hl]; exact ht, take_take ht⟩
  · exact ⟨vs, rfl, ht⟩
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

/-- What a tuple `let` gives its right-hand side: one entry per binder, with the binder's multiplicity. -/
theorem letWants_spec {C : Ctx} {sc : Scope} {bs : List LetBinder} {ws : List Want}
    (h : letWants C sc bs = .ok ws) :
    ws.length = bs.length ∧ ∀ (i : Nat) (w : Want) (b : LetBinder), ws[i]? = some w → bs[i]? = some b →
      w.mult = b.mult.getD .many := by
  unfold letWants at h
  obtain ⟨⟨sc', opens⟩, hgo, h⟩ := bind_eq_ok.1 h
  have hol := letWants_go_length bs sc [] [] hgo
  simp only [List.length_nil, Nat.zero_add] at hol
  obtain ⟨hl, hi⟩ := mapM_ok h
  refine ⟨by simp [hl, hol], fun i w b hw hb => ?_⟩
  obtain ⟨o, ho⟩ : ∃ o, opens[i]? = some o := by
    have : i < opens.length := by rw [hol]; exact (List.getElem?_eq_some_iff.1 hb).1
    exact ⟨_, List.getElem?_eq_getElem this⟩
  have hb' := hi i (b, o) w (List.getElem?_zip_eq_some.2 ⟨hb, ho⟩) hw
  cases o with
  | some o =>
    obtain ⟨t, ht, hb'⟩ := bind_eq_ok.1 hb'
    simp only [pure, Except.pure, Except.ok.injEq] at hb'
    subst hb'
    simp [Want.of, (abstracted_ok ht).2.2.2]
  | none =>
    simp only [pure, Except.pure, Except.ok.injEq] at hb'
    subst hb'
    rfl

end Pledge
