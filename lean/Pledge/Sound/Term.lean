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

/-- What a checked telescope is, independently of any valuation. -/
theorem telescope_shape {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat} {out : Checked}
    (hp : bs.all Binder.plain = true) (h : telescope C sc bs kind outer = .ok out) :
    out.tele.length = bs.length ∧ out.ids = List.range' sc.Γ.length bs.length ∧
      out.sc.Γ.length = sc.Γ.length + bs.length ∧ sc.Γ <+: out.sc.Γ ∧
      out.sc = Scope.bind { sc with Γ := out.sc.Γ } (bs.map (·.name)) (fieldRes out.ids) ∧
      (∀ b ∈ out.tele, b.mult = .many) ∧
      (sc.taintedBy = none → (∀ p ∈ sc.names, p.2.tainted = false) → out.tainted = false) := by
  sorry

/-- Opening a checked telescope to values satisfying it, after the values `outerv` of the entries `outer` it was
abstracted over first, satisfies the scope it was checked in, extended by those values. -/
theorem telescope_sound {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat} {out : Checked}
    {n0 : Nat} {Sc : Sigs} {ρ outerv vs : List Value} (hT : TermInv sc n0 Sc ρ) (hp : bs.all Binder.plain = true)
    (h : telescope C sc bs kind outer = .ok out) (houter : Term.evalList ρ [] (outer.map .entry) = some outerv)
    (hvs : TeleSat Sc ρ out.tele outerv vs) : TermInv out.sc n0 Sc (ρ ++ vs) := by
  sorry

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

/-- What a tuple `let` gives its right-hand side: one entry per binder, none erased. -/
theorem letWants_spec {C : Ctx} {sc : Scope} {bs : List LetBinder} {ws : List Want}
    (hp : bs.all (·.mult.isNone) = true) (h : letWants C sc bs = .ok ws) :
    ws.length = bs.length ∧ ∀ w ∈ ws, w.mult = .many := by
  sorry

end Pledge
