import Pledge.Sound.Solution

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

/-- With `solving` off, a written term is checked by `checkTerm`. -/
theorem term_eq {C : Ctx} {sc : Scope} {t : WTerm} {whole : Bool} (hs : C.solving = false) :
    ∃ C' : Ctx, C'.solving = false ∧ term C sc t whole = checkTerm C' sc whole t :=
  ⟨{ C with erased := C.erased || decide (2 ≤ C.phase) }, hs, by simp [term, hs]⟩

theorem opening_shape {C : Ctx} {sc : Scope} {name : Id} {ann : Ann} {mult : Option Mult} {kind : String}
    {o : Opening} (h : opening C sc name ann mult kind = .ok o) :
    annotate C sc ann = .ok (o.type, o.is, o.tainted) ∧ o.id = sc.Γ.length ∧ ∃ mk, o.sc = { sc with
      Γ := (openTele sc.Γ [⟨name.name, o.type, o.is, mult.getD .many⟩] [] mk).Γ,
      names := pushed [name] [⟨.entry sc.Γ.length, false, false⟩] ++ sc.names } := by
  unfold opening at h
  obtain ⟨⟨type, is, tainted⟩, ha, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨ha, rfl, _, by rw [Scope.openBinder, Scope.bind_eq]⟩

theorem telescope_go_shape {C : Ctx} {kind : String} : ∀ (bs : List Binder) (sc : Scope) (seen : List String)
    (acc : List (Binder × Opening)) {res : Scope × List String × List (Binder × Opening)},
    telescope.go C kind sc seen acc bs = .ok res →
    ∃ new, res.2.2 = acc ++ new ∧ new.map (·.1) = bs ∧ new.map (·.2.id) = List.range' sc.Γ.length bs.length ∧
      res.1.Γ.length = sc.Γ.length + bs.length ∧ sc.Γ <+: res.1.Γ ∧
      res.1 = { sc with
        Γ := res.1.Γ, names := pushed (bs.map (·.name)) (fieldRes (List.range' sc.Γ.length bs.length)) ++ sc.names }
  | [], sc, seen, acc, res, h => by
    simp only [telescope.go, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], by simp, rfl, rfl, by simp, List.prefix_refl _, by simp [pushed, fieldRes]⟩
  | b :: bs, sc, seen, acc, res, h => by
    simp only [telescope.go] at h
    obtain ⟨seen', -, h⟩ := bind_eq_ok.1 h
    obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
    obtain ⟨-, hid, mk, hsc⟩ := opening_shape ho
    obtain ⟨new, hnew, h1, h2, h3, h4, h5⟩ := telescope_go_shape bs _ _ _ h
    obtain ⟨Δ, hΔ, hΔl, -, -⟩ := openTele_shape sc.Γ [⟨b.name.name, o.type, o.is, b.mult.getD .many⟩] [] mk
    have hoΓ : o.sc.Γ = sc.Γ ++ Δ := by rw [hsc]; exact hΔ
    have hol : o.sc.Γ.length = sc.Γ.length + 1 := by rw [hoΓ, List.length_append, hΔl]; rfl
    refine ⟨(b, o) :: new, by simp [hnew], by simp [h1], ?_, by rw [h3, hol]; simp; omega,
      (hoΓ ▸ List.prefix_append _ _).trans h4, ?_⟩
    · simp [h2, hol, hid, List.range'_succ]
    · have hp0 : pushed ([] : List Id) ([] : List Res) = [] := rfl
      rw [h5]
      rw [hsc] at hol ⊢
      simp only at hol ⊢
      rw [hol]
      simp only [List.map_cons, List.length_cons, List.range'_succ, fieldRes, pushed_cons, hp0, List.append_assoc,
        List.nil_append]

/-- What a checked telescope is, independently of any valuation. -/
theorem telescope_shape {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat} {out : Checked}
    (h : telescope C sc bs kind outer = .ok out) :
    out.tele.length = bs.length ∧ out.ids = List.range' sc.Γ.length bs.length ∧
      out.sc.Γ.length = sc.Γ.length + bs.length ∧ sc.Γ <+: out.sc.Γ ∧
      out.sc = Scope.bind { sc with Γ := out.sc.Γ } (bs.map (·.name)) (fieldRes out.ids) := by
  unfold telescope at h
  obtain ⟨⟨sc', seen, opens⟩, hgo, h⟩ := bind_eq_ok.1 h
  obtain ⟨tele, htele, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨new, hnew, h1, h2, h3, h4, h5⟩ := telescope_go_shape bs sc [] [] hgo
  simp only [List.nil_append] at hnew
  subst hnew
  obtain ⟨hl, -⟩ := mapM_ok htele
  have hlen : opens.length = bs.length := by rw [← h1, List.length_map]
  exact ⟨by simp [hl, hlen], h2, h3, h4, by rw [Scope.bind_eq, h2]; exact h5⟩

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
  names : ∀ n r, sc.lookup n = some r → ∃ v, r.term.eval ρ [] = some v ∧ (∃ A, WType Sc v A) ∧
    (r.tainted = false → ∃ V, HasType Sc v V)

/-- `TermInv` with `WSat` and no typing: what `telescope_cons` needs, values of tainted results included. -/
structure WTermInv (sc : Scope) (n0 : Nat) (Sc : Sigs) (ρ : List Value) : Prop where
  sat : WSat Sc sc.Γ ρ
  n0_le : n0 ≤ ρ.length
  sigs : SigsClose sc.sigs ρ Sc
  sigsOk : SigsOk n0 sc.sigs
  noJunk : Sc.find junkHead = none
  names : ∀ n r, sc.lookup n = some r → ∃ v, r.term.eval ρ [] = some v ∧ ∃ A, WType Sc v A

theorem TermInv.weak {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} (h : TermInv sc n0 Sc ρ) :
    WTermInv sc n0 Sc ρ :=
  ⟨h.sat.1, h.n0_le, h.sigs, h.sigsOk, h.noJunk, fun n r hn => let ⟨v, hv, hw, _⟩ := h.names n r hn; ⟨v, hv, hw⟩⟩

theorem Inv.termInv {C : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    (hI : Inv C sc n0 W ρ act) : TermInv sc n0 W.Sc ρ :=
  ⟨hI.sat, hI.length, hI.sigs ρ hI.agree, hI.sigsOk, hI.noJunk, fun n r hn =>
    let ⟨v, hv, h⟩ := hI.names n r hn; ⟨v, hv, h.2.1, h.2.2⟩⟩

theorem checkTerm_app {C : Ctx} {sc : Scope} {whole : Bool} {hd : Name} {args : List WTerm} {r : Res}
    (h : checkTerm C sc whole (.app hd args) = .ok r) :
    ∃ (C' : Ctx) (k : HeadKind) (role : String) (er : Bool) (sig : Sig) (rs : List Res), C'.solving = C.solving ∧
      sc.sig hd.pos ⟨k, hd.name⟩ = .ok sig ∧ sig.params.length = args.length ∧
      checkTerms C' sc hd.name role er sig.params [] args = .ok rs ∧
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
       exact ⟨{ C with inType := C.inType || k == .type }, k, _, _, sig, rs, rfl, hsig, arity_ok har, hrs, h.symm⟩)

theorem checkTerm_var {C : Ctx} {sc : Scope} {whole : Bool} {x : Name} {r : Res}
    (h : checkTerm C sc whole (.var x) = .ok r) : ∃ r', sc.lookup x.name = some r' ∧
      r = { r' with tainted := r'.tainted || sc.taintedBy.isSome } := by
  simp only [checkTerm] at h
  split at h
  · rename_i r' hl
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨r', hl, h.symm⟩
  · simp [notValue, failAt_eq] at h

theorem checkTerm_hole {C : Ctx} {sc : Scope} {whole : Bool} {p : Pos} {r : Res} (hs : C.solving = false)
    (h : checkTerm C sc whole (.hole p) = .ok r) : ∃ ts, sc.solution C ts p .TYPE none C.erased = .ok r := by
  unfold checkTerm at h
  split at h
  · obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
    obtain ⟨-, -, -, ts, r', hr', hres⟩ := Scope.hole_spec hs ho
    rw [hres] at h
    obtain rfl : r' = r := by simpa using single_ok h
    exact ⟨ts, hr'⟩
  · simp [failAt_eq] at h

theorem checkTerms_cons {C : Ctx} {sc : Scope} {owner role : String} {er : Bool} {params : Telescope}
    {prev : List Res} {a : WTerm} {as : List WTerm} {rs : List Res}
    (h : checkTerms C sc owner role er params prev (a :: as) = .ok rs) :
    ∃ p ps r rest, params = p :: ps ∧ rs = r :: rest ∧ checkTerms C sc owner role er ps (prev ++ [r]) as = .ok rest ∧
      ((∃ pos o, holeArg C sc (argGiven p prev role owner er) p prev pos = .ok o ∧ o.res = [r]) ∨
        (checkTerm C sc false a = .ok r ∧
          ∃ sc', against { sc with holes := [] } (argGiven p prev role owner er) a.pos [r] = .ok sc')) := by
  cases params with
  | nil => simp [checkTerms, internal, failAt_eq] at h
  | cons p ps =>
    cases a <;> simp only [checkTerms] at h <;> first
      | (obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
         obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
         obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
         simp only [pure, Except.pure, Except.ok.injEq] at h
         exact ⟨p, ps, r, rest, rfl, h.symm, hrest, .inl ⟨_, o, ho, single_ok hr⟩⟩)
      | (obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
         obtain ⟨sc', hag, h⟩ := bind_eq_ok.1 h
         simp only [pure, Except.pure, ok_bind] at h
         obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
         simp only [pure, Except.pure, Except.ok.injEq] at h
         exact ⟨p, ps, _, rest, rfl, h.symm, hrest, .inr ⟨hr, sc', hag⟩⟩)

namespace TermFill

mutual
theorem eval_noRemoved {ρ env : List Value} (hρ : ∀ v ∈ ρ, v.noRemoved = true)
    (he : ∀ v ∈ env, v.noRemoved = true) : ∀ (t : Term) {v : Value}, t.eval ρ env = some v → v.noRemoved = true
  | .entry _, v, h => by simp only [Term.eval] at h; exact hρ v (List.mem_of_getElem? h)
  | .bound _, v, h => by simp only [Term.eval] at h; exact he v (List.mem_of_getElem? h)
  | .app _ as, v, h => by
    obtain ⟨vs, hvs, rfl⟩ := Term.eval_app.1 h
    simpa [Value.noRemoved] using evalList_noRemoved hρ he as hvs
theorem evalList_noRemoved {ρ env : List Value} (hρ : ∀ v ∈ ρ, v.noRemoved = true)
    (he : ∀ v ∈ env, v.noRemoved = true) :
    ∀ (as : List Term) {vs : List Value}, Term.evalList ρ env as = some vs → Value.noRemovedList vs = true
  | [], vs, h => by cases h; rfl
  | a :: as, vs, h => by
    obtain ⟨v, vs', hv, hvs, rfl⟩ := Term.evalList_cons_eq_some.1 h
    simp [Value.noRemovedList, eval_noRemoved hρ he a hv, evalList_noRemoved hρ he as hvs]
end

mutual
/-- A checked skeleton term has a value with a type by its head. -/
theorem checkTerm_wtype {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} (hT : WTermInv sc n0 Sc ρ) :
    ∀ {C : Ctx} (t : WTerm) {whole : Bool} {r : Res}, C.solving = false → checkTerm C sc whole t = .ok r →
      ∃ v, r.term.eval ρ [] = some v ∧ ∃ A, WType Sc v A
  | C, .hole p, whole, r, hs, h => by
    obtain ⟨ts, hr⟩ := checkTerm_hole hs h
    obtain ⟨v, A, hv, -, -, hw, -⟩ := Scope.solution_sound hT.sat hT.sigs hT.noJunk hT.sigsOk hT.n0_le hr
    exact ⟨v, hv, A, hw⟩
  | C, .var x, whole, r, hs, h => by
    obtain ⟨r', hl, rfl⟩ := checkTerm_var h
    exact hT.names _ r' hl
  | C, .app hd args, whole, r, hs, h => by
    obtain ⟨C', k, role, er, sig, rs, hs', hsig, har, hrs, rfl⟩ := checkTerm_app h
    have hfind := Scope.sig_ok hsig
    obtain ⟨hbelow, hbounds⟩ := hT.sigsOk sig (List.mem_of_find?_eq_some hfind)
    obtain ⟨vs, hvs, hrl⟩ := checkTerms_weval hT args (hs'.trans hs) hrs
    have hl : vs.length = sig.params.length := by
      rw [Term.length_evalList hvs, List.length_map, hrl, har]
    obtain ⟨A, hA⟩ : ∃ A, sig.ret.eval ρ vs = some A := by
      refine Term.eval_isSome _ ?_ (by rw [hl]; exact hbounds)
      simp only [Sig.entriesBelow, Bool.and_eq_true] at hbelow
      exact Term.entriesBelow_mono hT.n0_le _ hbelow.2
    rw [← Sigs.find_head hfind] at hfind
    obtain ⟨sig', hc, -⟩ := hT.sigs.find hfind
    have hne : sig.head ≠ junkHead := fun e => by rw [e, hT.noJunk] at hc; cases hc
    refine ⟨_, Term.eval_app.2 ⟨vs, hvs, rfl⟩, A, ?_⟩
    simp only [WType, hne, ↓reduceIte]
    exact ⟨sig', hc, by rw [hT.sigs.ret_eval hfind hc]; exact hA⟩
theorem checkTerms_weval {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} (hT : WTermInv sc n0 Sc ρ) :
    ∀ {C : Ctx} (args : List WTerm) {owner role : String} {er : Bool} {params : Telescope} {prev rs : List Res},
      C.solving = false → checkTerms C sc owner role er params prev args = .ok rs →
      ∃ vs, Term.evalList ρ [] (rs.map (·.term)) = some vs ∧ rs.length = args.length
  | C, [], owner, role, er, params, prev, rs, _, h => by
    simp only [checkTerms, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | C, a :: as, owner, role, er, params, prev, rs, hs, h => by
    obtain ⟨p, ps, r, rest, rfl, rfl, hrest, hr⟩ := checkTerms_cons h
    obtain ⟨v, hv⟩ : ∃ v, r.term.eval ρ [] = some v := by
      rcases hr with ⟨pos, o, ho, hres⟩ | ⟨hr, -⟩
      · obtain ⟨-, -, -, -, ts, r', hr', hres'⟩ := holeArg_spec hs ho
        rw [hres] at hres'
        obtain rfl : r = r' := by simpa using hres'
        obtain ⟨v, -, hv, -⟩ := Scope.solution_sound hT.sat hT.sigs hT.noJunk hT.sigsOk hT.n0_le hr'
        exact ⟨v, hv⟩
      · obtain ⟨v, hv, -⟩ := checkTerm_wtype hT a hs hr
        exact ⟨v, hv⟩
    obtain ⟨vs, hvs, hl⟩ := checkTerms_weval hT as hs hrest
    exact ⟨v :: vs, Term.evalList_cons_eq_some.2 ⟨v, vs, hv, hvs, rfl⟩, by simp [hl]⟩
end

theorem annotate_spec {C : Ctx} {sc : Scope} {ann : Ann} {ty : Term} {is : Option Term} {tainted : Bool}
    (hs : C.solving = false) (h : annotate C sc ann = .ok (ty, is, tainted)) :
    ∃ (C' : Ctx) (r : Res), C'.solving = false ∧ checkTerm C' sc (ann matches .type _) ann.term = .ok r ∧
      tainted = r.tainted ∧ match ann with
        | .is _ => is = some r.term ∧ sc.typeOf ann.term.pos r.term = .ok ty
        | .type _ => is = none ∧ ty = r.term ∧ isType sc ann.term.pos r.term = .ok () := by
  cases ann with
  | is t =>
    obtain ⟨C', hs', heq⟩ := term_eq (sc := sc) (t := t) (whole := false) hs
    simp only [annotate, heq] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
    obtain ⟨ty', hty, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨C', r, hs', hr, rfl, rfl, hty⟩
  | type t =>
    obtain ⟨C', hs', heq⟩ := term_eq (sc := sc) (t := t) (whole := true) hs
    simp only [annotate, heq] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
    obtain ⟨u, hu, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨C', r, hs', hr, rfl, rfl, rfl, hu⟩

/-- A checked annotation's type has a value, and its `is` term a value with that type by its head. -/
theorem annotate_weval {C : Ctx} {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} {ann : Ann} {ty : Term}
    {is : Option Term} {tainted : Bool} (hT : WTermInv sc n0 Sc ρ) (hs : C.solving = false)
    (h : annotate C sc ann = .ok (ty, is, tainted)) :
    ∃ A, ty.eval ρ [] = some A ∧ ∀ e, is = some e → ∃ v, e.eval ρ [] = some v ∧ WType Sc v A := by
  obtain ⟨C', r, hs', hr, -, h⟩ := annotate_spec hs h
  obtain ⟨v, hv, A, hA⟩ := checkTerm_wtype hT _ hs' hr
  cases ann with
  | is t =>
    obtain ⟨rfl, hty⟩ := h
    exact ⟨A, typeOf_eval hT.sat hT.sigs hT.noJunk hv hA (Scope.typeOf_ok hty),
      fun e he => by cases he; exact ⟨v, hv, hA⟩⟩
  | type t =>
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨v, hv, fun e he => by cases he⟩

end TermFill

/-- A checked annotation's type and `is` term have values (§6). -/
theorem annotate_eval {C : Ctx} {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} {ann : Ann} {ty : Term}
    {is : Option Term} {tainted : Bool} (hT : WTermInv sc n0 Sc ρ) (hs : C.solving = false)
    (h : annotate C sc ann = .ok (ty, is, tainted)) :
    (∃ A, ty.eval ρ [] = some A) ∧ ∀ e, is = some e → ∃ v, e.eval ρ [] = some v :=
  let ⟨A, hA, his⟩ := TermFill.annotate_weval hT hs h
  ⟨⟨A, hA⟩, fun e he => let ⟨v, hv, _⟩ := his e he; ⟨v, hv⟩⟩

mutual
/-- A checked skeleton term's value meets `ResOk`: an untainted one has a type. -/
theorem checkTerm_resOk {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} (hT : TermInv sc n0 Sc ρ) :
    ∀ {C : Ctx} (t : WTerm) {whole : Bool} {r : Res}, C.solving = false → checkTerm C sc whole t = .ok r →
      ∃ v, r.term.eval ρ [] = some v ∧ ResOk Sc r v
  | C, .hole p, whole, r, hs, h => by
    obtain ⟨ts, hr⟩ := checkTerm_hole hs h
    obtain ⟨v, A, hv, -, hnr, hw, hty, -⟩ := Scope.solution_sound hT.sat.1 hT.sigs hT.noJunk hT.sigsOk hT.n0_le hr
    exact ⟨v, hv, hnr, ⟨A, hw⟩, fun ht => ⟨A, hty hT.sat ht⟩⟩
  | C, .var x, whole, r, hs, h => by
    obtain ⟨r', hl, rfl⟩ := checkTerm_var h
    obtain ⟨v, hv, hw, hty⟩ := hT.names _ r' hl
    exact ⟨v, hv, TermFill.eval_noRemoved hT.sat.noRemoved (by simp) _ hv, hw, fun ht => hty (by simp_all)⟩
  | C, .app hd args, whole, r, hs, h => by
    obtain ⟨v, hv, hw⟩ := TermFill.checkTerm_wtype hT.weak _ hs h
    refine ⟨v, hv, TermFill.eval_noRemoved hT.sat.noRemoved (by simp) _ hv, hw, fun ht => ?_⟩
    obtain ⟨C', k, role, er, sig, rs, hs', hsig, har, hrs, rfl⟩ := checkTerm_app h
    have hfind := Scope.sig_ok hsig
    obtain ⟨vs, hvs, -, hws⟩ := checkTerms_resOk hT args (prevv := []) (hs'.trans hs) hrs rfl har
    obtain ⟨vs', hvs', rfl⟩ := Term.eval_app.1 hv
    rw [hvs] at hvs'
    cases hvs'
    obtain ⟨A, hA⟩ := hw
    have hne : sig.head ≠ junkHead := fun e => by
      rw [← Sigs.find_head hfind, e] at hfind
      obtain ⟨_, hc, -⟩ := hT.sigs.find hfind
      rw [hT.noJunk] at hc; cases hc
    simp only [WType, hne, ↓reduceIte] at hA
    obtain ⟨sig', hc, hret⟩ := hA
    rw [← Sigs.find_head hfind] at hfind
    refine ⟨A, .app hc ((hT.sigs.teleSat_iff hfind hc).2 (WantsSat.teleSat hws fun b hb => ?_)) hret⟩
    simp only [Bool.or_eq_false_iff, List.any_eq_false] at ht
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hb
    simpa using ht.1 r hr
theorem checkTerms_resOk {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} (hT : TermInv sc n0 Sc ρ) :
    ∀ {C : Ctx} (args : List WTerm) {owner role : String} {er : Bool} {params : Telescope} {prev rs : List Res}
      {prevv : List Value}, C.solving = false → checkTerms C sc owner role er params prev args = .ok rs →
      Term.evalList ρ [] (prev.map (·.term)) = some prevv →
      params.length = args.length → ∃ vs, Term.evalList ρ [] (rs.map (·.term)) = some vs ∧ ResOks Sc rs vs ∧
        WantsSat Sc ρ (params.map Want.of) prevv (rs.map (!·.tainted)) vs
  | C, [], owner, role, er, params, prev, rs, prevv, _, h, _, hl => by
    simp only [checkTerms, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [List.length_eq_zero_iff.1 hl]
    exact ⟨[], rfl, trivial, trivial⟩
  | C, a :: as, owner, role, er, params, prev, rs, prevv, hs, h, hprev, hl => by
    obtain ⟨p, ps, r, rest, rfl, rfl, hrest, hr⟩ := checkTerms_cons h
    obtain ⟨v, hv, hok, hw⟩ : ∃ v, r.term.eval ρ [] = some v ∧ ResOk Sc r v ∧
        WantSat Sc ρ (Want.of p) prevv (!r.tainted) v := by
      rcases hr with ⟨pos, o, ho, hres⟩ | ⟨hr, sc', hag⟩
      · obtain ⟨r', v, A, hres', hv, hA, hnr, hw, hty, his⟩ := holeArg_value hs hT.sat.1 hT.sigs hT.noJunk hT.sigsOk
          hT.n0_le hprev ho
        rw [hres] at hres'
        obtain rfl : r = r' := by simpa using hres'
        refine ⟨v, hv, ⟨hnr, ⟨A, hw⟩, fun ht => ⟨A, hty hT.sat ht⟩⟩, fun T hT' => ?_, his⟩
        cases hT'
        exact ⟨A, hA, hnr, hw, fun ht => hty hT.sat (by simpa using ht)⟩
      · obtain ⟨v, hv, hok⟩ := checkTerm_resOk hT a hs hr
        obtain ⟨-, -, hw⟩ := against_sound (sc := { sc with holes := [] }) (rs := [r]) (vs := [v]) hT.sat.1 hT.sigs
          hT.noJunk rfl (Term.evalList_singleton.2 ⟨v, hv, rfl⟩) ⟨hok, trivial⟩ (by simpa [argGiven] using hprev) hag
        exact ⟨v, hv, hok, hw.1⟩
    obtain ⟨vs, hvs, hoks, hws⟩ := checkTerms_resOk hT as hs hrest
      (by simpa using Term.evalList_append hprev (Term.evalList_singleton.2 ⟨v, hv, rfl⟩)) (by simpa using hl)
    exact ⟨v :: vs, Term.evalList_cons_eq_some.2 ⟨v, vs, hv, hvs, rfl⟩, ⟨hok, hoks⟩, hw, hws⟩
end

/-- A checked type annotation, if untainted, has a value of type `Type()` (§3). -/
theorem annotate_type_typed {C : Ctx} {sc : Scope} {n0 : Nat} {Sc : Sigs} {ρ : List Value} {t : WTerm} {ty : Term}
    {is : Option Term} {tainted : Bool} (hT : TermInv sc n0 Sc ρ) (hs : C.solving = false)
    (h : annotate C sc (.type t) = .ok (ty, is, tainted))
    (ht : tainted = false) : ∃ V, ty.eval ρ [] = some V ∧ HasType Sc V Value.TYPE := by
  obtain ⟨C', r, hs', hr, rfl, -, rfl, hu⟩ := TermFill.annotate_spec hs h
  obtain ⟨V, hV, -, -, hty⟩ := checkTerm_resOk hT t hs' hr
  obtain ⟨A, hA⟩ := hty ht
  simp only [isType, bind, Except.bind, Ann.term] at hu
  cases hT' : sc.typeOf t.pos r.term with
  | error => simp [hT'] at hu
  | ok T =>
    simp only [hT'] at hu
    split at hu
    · rename_i hid
      have hTA := typeOf_sound hT.sat.1 hT.sigs hT.noJunk hV hA (Scope.typeOf_ok hT')
      rw [hT.sat.eval_eq_of_identical (by simpa using hid)] at hTA
      cases hTA
      exact ⟨V, hV, hA⟩
    · simp [failAt_eq] at hu

namespace TermFill

/-- What opening a binder to the value `v` needs under `ρ`: `v` has the type by its head, and has it if `typed`,
and is the `is` term's value. -/
def OpenOk (S : Sigs) (ρ : List Value) (o : Opening) (typed : Bool) (v : Value) : Prop :=
  (∃ A, o.type.eval ρ [] = some A ∧ v.noRemoved = true ∧ WType S v A ∧ (typed = true → HasType S v A)) ∧
    ∀ e, o.is = some e → e.eval ρ [] = some v

theorem wsat_push {S : Sigs} {Γ : Entries} {ρ : List Value} {en : Entry} {v A : Value} (hΓ : WSat S Γ ρ)
    (hA : en.type.eval (ρ ++ [v]) [] = some A) (hr : v.noRemoved = true) (hw : WType S v A)
    (hru : ∀ r, en.rule = some r → r.eval (ρ ++ [v]) [] = some v) : WSat S (Γ ++ [en]) (ρ ++ [v]) := by
  refine ⟨by simp [hΓ.1], fun i en' hen => ?_⟩
  by_cases hi : i < Γ.length
  · rw [List.getElem?_append_left hi] at hen
    obtain ⟨w, B, hw', hB, h1, h2, h3⟩ := hΓ.2 i en' hen
    exact ⟨w, B, getElem?_append_of_some hw', Term.eval_frame_ρ _ hB, h1, h2,
      fun r h => Term.eval_frame_ρ _ (h3 r h)⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hen
    have h0 : i - Γ.length = 0 := by
      have := (List.getElem?_eq_some_iff.1 hen).1; simp at this; omega
    rw [h0] at hen
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hen
    subst hen
    refine ⟨v, A, ?_, hA, hr, hw, hru⟩
    rw [List.getElem?_append_right (by rw [hΓ.1]; omega), hΓ.1, h0]
    rfl

theorem opening_entry {C : Ctx} {sc : Scope} {name : Id} {ann : Ann} {mult : Option Mult} {kind : String}
    {o : Opening} (h : opening C sc name ann mult kind = .ok o) :
    annotate C sc ann = .ok (o.type, o.is, o.tainted) ∧ o.id = sc.Γ.length ∧ ∃ en : Entry, o.sc.Γ = sc.Γ ++ [en] ∧
      en.type = o.type.subst [] ∧ en.rule = o.is.map (fun e => (e.subst []).canon sc.Γ) ∧ o.sc.sigs = sc.sigs ∧
      o.sc.names = pushed [name] [⟨.entry sc.Γ.length, false, false⟩] ++ sc.names := by
  obtain ⟨ha, hid, mk, hsc⟩ := opening_shape h
  rw [hsc]
  simp only [openTele, openTele.go]
  refine ⟨ha, hid, _, rfl, ?_⟩
  simp

/-- Opening a binder to a value meeting it pushes an entry that value meets. -/
theorem opening_facts {C : Ctx} {sc : Scope} {name : Id} {ann : Ann} {mult : Option Mult} {kind : String}
    {o : Opening} {n0 : Nat} {Sc : Sigs} {ρ : List Value} {v : Value} {t : Bool} (hT : WTermInv sc n0 Sc ρ)
    (h : opening C sc name ann mult kind = .ok o) (hv : OpenOk Sc ρ o t v) :
    ∃ en A, o.sc.Γ = sc.Γ ++ [en] ∧ en.type.eval (ρ ++ [v]) [] = some A ∧ v.noRemoved = true ∧ WType Sc v A ∧
      (t = true → HasType Sc v A) ∧ (∀ r, en.rule = some r → r.eval (ρ ++ [v]) [] = some v) ∧
      o.sc.sigs = sc.sigs ∧ o.sc.names = pushed [name] [⟨.entry sc.Γ.length, false, false⟩] ++ sc.names := by
  obtain ⟨-, -, en, hΓ, hty, hrule, hsigs, hnames⟩ := opening_entry h
  obtain ⟨⟨A, hA, hr, hw, hV⟩, his⟩ := hv
  refine ⟨en, A, hΓ, ?_, hr, hw, hV, fun r hr' => ?_, hsigs, hnames⟩
  · rw [hty, Term.eval_subst (rfl : Term.evalList (ρ ++ [v]) [] [] = some [])]; exact Term.eval_frame_ρ _ hA
  · rw [hrule] at hr'
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hr'
    exact Term.eval_frame_ρ [v] (by rw [hT.sat.eval_canon, Term.eval_subst rfl]; exact his e he)

theorem lookup_push {name : Id} {r0 r : Res} {l : List (String × Res)} {n : String}
    (h : (pushed [name] [r0] ++ l).lookup n = some r) : r = r0 ∨ l.lookup n = some r := by
  rw [lookup_append] at h
  cases hx : (pushed [name] [r0]).lookup n with
  | some r' =>
    rw [hx, Option.some_or, Option.some.injEq] at h
    subst h
    obtain ⟨i, hi⟩ := pushed_mem (lookup_mem hx)
    cases i <;> simp_all
  | none => rw [hx, Option.none_or] at h; exact .inr h

theorem wopen {C : Ctx} {sc : Scope} {name : Id} {ann : Ann} {mult : Option Mult} {kind : String}
    {o : Opening} {n0 : Nat} {Sc : Sigs} {ρ : List Value} {v : Value} {t : Bool} (hT : WTermInv sc n0 Sc ρ)
    (h : opening C sc name ann mult kind = .ok o) (hv : OpenOk Sc ρ o t v) : WTermInv o.sc n0 Sc (ρ ++ [v]) := by
  obtain ⟨en, A, hΓ, hA, hr, hw, -, hru, hsigs, hnames⟩ := opening_facts hT h hv
  have hlen := hT.sat.1
  refine ⟨by rw [hΓ]; exact wsat_push hT.sat hA hr hw hru, by simp; have := hT.n0_le; omega, ?_, ?_, hT.noJunk,
    fun n r hl => ?_⟩
  · rw [hsigs]; exact hT.sigs.frame [v] fun sig hs => Sig.entriesBelow_mono hT.n0_le (hT.sigsOk sig hs).1
  · rw [hsigs]; exact hT.sigsOk
  · rw [Scope.lookup, hnames] at hl
    rcases lookup_push hl with rfl | hl
    · exact ⟨v, by simp [Term.eval, ← hlen], A, hw⟩
    · obtain ⟨w, hw', B, hB⟩ := hT.names n r hl
      exact ⟨w, Term.eval_frame_ρ [v] hw', B, hB⟩

theorem topen {C : Ctx} {sc : Scope} {name : Id} {ann : Ann} {mult : Option Mult} {kind : String}
    {o : Opening} {n0 : Nat} {Sc : Sigs} {ρ : List Value} {v : Value} (hT : TermInv sc n0 Sc ρ)
    (h : opening C sc name ann mult kind = .ok o) (hv : OpenOk Sc ρ o true v) : TermInv o.sc n0 Sc (ρ ++ [v]) := by
  have hW := wopen hT.weak h hv
  obtain ⟨en, A, hΓ, hA, hr, hw, hV, hru, -, hnames⟩ := opening_facts hT.weak h hv
  have hlen := hT.sat.1.1
  refine ⟨by rw [hΓ]; exact hT.sat.push ⟨A, hA, hr, hw, fun _ => hV rfl, hru⟩, hW.n0_le, hW.sigs, hW.sigsOk,
    hW.noJunk, fun n r hl => ?_⟩
  rw [Scope.lookup, hnames] at hl
  rcases lookup_push hl with rfl | hl
  · exact ⟨v, by simp [Term.eval, ← hlen], ⟨A, hw⟩, fun _ => ⟨A, hV rfl⟩⟩
  · obtain ⟨w, hw', hB, hV'⟩ := hT.names n r hl
    exact ⟨w, Term.eval_frame_ρ [v] hw', hB, hV'⟩

/-- The scopes a sequence of `opening`s passes through, from a scope to `fin`. -/
inductive Chain (C : Ctx) (kind : String) (fin : Scope) : Scope → List Opening → Prop
  | nil : Chain C kind fin fin []
  | cons {sc : Scope} {name : Id} {ann : Ann} {mult : Option Mult} {o : Opening} {os : List Opening} :
      opening C sc name ann mult kind = .ok o → Chain C kind fin o.sc os →
        Chain C kind fin sc (o :: os)

theorem chain_shape {C : Ctx} {kind : String} {fin : Scope} {sc : Scope} {os : List Opening}
    (hc : Chain C kind fin sc os) : sc.Γ <+: fin.Γ ∧ fin.Γ.length = sc.Γ.length + os.length ∧
      os.map (·.id) = List.range' sc.Γ.length os.length := by
  induction hc with
  | nil => exact ⟨List.prefix_refl _, by simp, rfl⟩
  | cons ho _ ih =>
    obtain ⟨-, hid, en, hΓ, -⟩ := opening_entry ho
    rw [hΓ] at ih
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨(List.prefix_append _ _).trans h1, by rw [h2]; simp; omega, ?_⟩
    simp [List.range'_succ, hid, h3]

/-- `R`, position by position, on two lists of the same length. -/
def Pairs {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Pairs R as bs
  | _, _ => False

theorem pairs_of_getElem {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β}, l.length = l'.length →
    (∀ (i : Nat) a b, l[i]? = some a → l'[i]? = some b → R a b) → Pairs R l l'
  | [], [], _, _ => trivial
  | a :: l, b :: l', hl, h => ⟨h 0 a b rfl rfl, pairs_of_getElem (by simpa using hl)
      fun i a b ha hb => h (i + 1) a b (by simpa using ha) (by simpa using hb)⟩
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-- The want `w` is the binder opened as `o`, abstracted over `ids` in `Γ`. -/
def WantAbs (Γ : Entries) (ids : List Nat) (o : Opening) (w : Want) : Prop :=
  ∃ T, w.type = some T ∧ abstract? Γ o.type ids = some T ∧
    (∀ e', w.is = some e' → ∃ e, o.is = some e ∧ abstract? Γ e ids = some e') ∧
    ∀ e, o.is = some e → ∃ e', w.is = some e' ∧ abstract? Γ e ids = some e'

theorem abstracted_abs {Γ : Entries} {name : Option String} {mult : Option Mult} {pos : Pos} {ids : List Nat}
    {o : Opening} {t : TBinder} (h : abstracted Γ name mult pos o.type o.is ids = .ok t) :
    WantAbs Γ ids o (Want.of t) := by
  obtain ⟨-, hty, his, -⟩ := abstracted_ok h
  refine ⟨t.type, rfl, hty, fun e' he' => ?_, his⟩
  cases hi : o.is with
  | some e =>
    obtain ⟨e'', h1, h2⟩ := his e hi
    simp only [Want.of, h1, Option.some.injEq] at he'
    subst he'
    exact ⟨e, rfl, h2⟩
  | none =>
    rw [hi] at h
    unfold abstracted at h
    obtain ⟨ty, -, h⟩ := bind_eq_ok.1 h
    obtain ⟨is', hmis, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp [Option.mapM, pure, Except.pure] at hmis
    subst hmis
    simp [Want.of] at he'

mutual
theorem mapEntries_entriesBelow {n : Nat} {f : Nat → Term} :
    ∀ t : Term, (∀ i, t.occurs i = true → (f i).entriesBelow n = true) → (t.mapEntries f).entriesBelow n = true
  | .entry i, h => h i (by simp [Term.occurs])
  | .bound _, _ => rfl
  | .app _ as, h => mapEntriesList_entriesBelow as h
theorem mapEntriesList_entriesBelow {n : Nat} {f : Nat → Term} :
    ∀ as : List Term, (∀ i, Term.occursList i as = true → (f i).entriesBelow n = true) →
      Term.entriesBelowList n (Term.mapEntriesList f as) = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.mapEntriesList, Term.entriesBelowList, Bool.and_eq_true]
    exact ⟨mapEntries_entriesBelow a fun i hi => h i (by simp [Term.occursList, hi]),
      mapEntriesList_entriesBelow as fun i hi => h i (by simp [Term.occursList, hi])⟩
end

/-- An abstracted term mentions only entries below `n` when every entry of the original term below `n` is
abstracted or below `n`, with rules below `n`. -/
theorem abstract_entriesBelow {Γ : Entries} {t w : Term} {ids : List Nat} {n : Nat}
    (h : abstract? Γ t ids = some w) (ht : ∀ i, t.occurs i = true → i ∉ ids → i < n)
    (hr : ∀ i en r, i < n → Γ[i]? = some en → en.rule = some r → r.entriesBelow n = true) :
    w.entriesBelow n = true := by
  simp only [abstract?] at h
  split at h
  · cases h
    refine mapEntries_entriesBelow t fun i hi => ?_
    cases hk : ids.idxOf? i with
    | some k => simp [hk, Term.entriesBelow]
    | none =>
      have hin := ht i hi (List.idxOf?_eq_none_iff.1 hk)
      simp only [hk, Option.map_none, Option.getD_none]
      cases hen : Γ[i]? with
      | none => simp [Term.entriesBelow, hin]
      | some en =>
        cases hru : en.rule with
        | none => simp [hru, Term.entriesBelow, hin]
        | some r =>
          simp only [Option.bind_some, hru, Option.elim_some]
          refine mapEntries_entriesBelow r fun j hj => ?_
          cases hk' : ids.idxOf? j with
          | some k => simp [Term.entriesBelow]
          | none =>
            simp only [Option.map_none, Option.getD_none, Term.entriesBelow, decide_eq_true_eq]
            exact Term.lt_of_occurs r (hr i en r hin hen hru) hj
  · cases h

/-- A term checked in a later scope `Γm`, abstracted over the telescope's entries in the final scope `Γ'`, takes
under `ρ` and the binders' values the value the term has under `ρ` extended by them. -/
theorem abs_eval {Sc : Sigs} {Γ0 Γm Γ' : Entries} {ρ prev outerv : List Value} {outer : List Nat} {N : Nat}
    {u w : Term} {x : Value} (h0 : WSat Sc Γ0 ρ) (hp0 : Γ0 <+: Γ') (hl : Γ'.length = Γ0.length + N)
    (houter : Term.evalList ρ [] (outer.map .entry) = some outerv) (hm : WSat Sc Γm (ρ ++ prev)) (hpm : Γm <+: Γ')
    (hab : abstract? Γ' u (outer ++ List.range' Γ0.length N) = some w) (hu : u.eval (ρ ++ prev) [] = some x) :
    w.eval ρ (outerv ++ prev) = some x := by
  have hρ := h0.1
  have hol : outerv.length = outer.length := by simpa using Term.length_evalList houter
  have henv : ∀ k i : Nat, (outer ++ List.range' Γ0.length N)[k]? = some i →
      (outerv ++ prev)[k]? = (ρ ++ prev)[i]? := by
    intro k i hk
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
      have hlt : k - outer.length < N := by have := (List.getElem?_eq_some_iff.1 hk).1; simpa using this
      rw [List.getElem?_range' hlt] at hk
      cases hk
      rw [List.getElem?_append_right (by omega), hρ]
      congr 1; omega
  have hum : u.entriesBelow Γm.length = true := by rw [← hm.1]; exact Term.entriesBelow_of_eval u hu
  have hw1 : w.eval (ρ ++ prev) (outerv ++ prev) = some x := by
    have hab' := hab
    rw [abstract?_prefix hpm hum] at hab'
    rw [abstract?_eval hm.rulesHold hab' henv]; exact hu
  have hwb : w.entriesBelow ρ.length = true := by
    refine abstract_entriesBelow hab (fun i hi hni => ?_) (fun i en r hi hen hr => ?_)
    · have h1 := Term.lt_of_occurs u hum hi
      have h2 := hpm.length_le
      refine Decidable.byContradiction fun hn =>
        hni (List.mem_append_right _ (List.mem_range'.2 ⟨i - Γ0.length, ?_, ?_⟩))
      all_goals omega
    · obtain ⟨l, rfl⟩ := hp0
      rw [List.getElem?_append_left (by omega)] at hen
      obtain ⟨v, -, hv, -, -, -, hrv⟩ := h0.2 i en hen
      exact Term.entriesBelow_of_eval r (hrv r hr)
  rw [Term.eval_entriesBelow (show ρ.take ρ.length = (ρ ++ prev).take ρ.length by simp) _ w hwb]
  exact hw1

/-- One binder of a checked telescope, as a want: it can be opened, and a value meeting it meets the binder. -/
theorem want_open {C : Ctx} {kind : String} {sc0 scm fin : Scope} {name : Id} {ann : Ann} {mult : Option Mult}
    {o : Opening} {w : Want} {n0 N : Nat} {Sc : Sigs} {ρ prev outerv : List Value} {outer : List Nat}
    (h0 : WSat Sc sc0.Γ ρ) (hp0 : sc0.Γ <+: fin.Γ) (hl : fin.Γ.length = sc0.Γ.length + N)
    (houter : Term.evalList ρ [] (outer.map .entry) = some outerv) (hT : WTermInv scm n0 Sc (ρ ++ prev))
    (hpm : scm.Γ <+: fin.Γ) (hs : C.solving = false) (h : opening C scm name ann mult kind = .ok o)
    (hw : WantAbs fin.Γ (outer ++ List.range' sc0.Γ.length N) o w) :
    ((∀ T, w.type = some T → ∃ A, T.eval ρ (outerv ++ prev) = some A ∧ A.noRemoved = true) ∧
      (∀ e, w.is = some e → ∃ v, e.eval ρ (outerv ++ prev) = some v ∧ v.noRemoved = true ∧
        ∀ T A, w.type = some T → T.eval ρ (outerv ++ prev) = some A → WType Sc v A)) ∧
    ∀ t v, WantSat Sc ρ w (outerv ++ prev) t v → OpenOk Sc (ρ ++ prev) o t v := by
  obtain ⟨A, hA, his⟩ := annotate_weval hT hs (opening_entry h).1
  obtain ⟨T, hT', hab, hisb, hisf⟩ := hw
  have key := fun {u w : Term} {x : Value} => @abs_eval Sc _ _ _ ρ prev outerv outer N u w x h0 hp0 hl houter hT.sat hpm
  have hTA := key hab hA
  have hnr := hT.sat.noRemoved
  refine ⟨⟨fun T' hT'' => ?_, fun e' he' => ?_⟩, fun t v hv => ?_⟩
  · rw [hT'] at hT''; cases hT''
    exact ⟨A, hTA, eval_noRemoved hnr (by simp) _ hA⟩
  · obtain ⟨e, he, habe⟩ := hisb e' he'
    obtain ⟨x, hx, hxA⟩ := his e he
    refine ⟨x, key habe hx, eval_noRemoved hnr (by simp) _ hx, fun T' A' hT'' hA' => ?_⟩
    rw [hT'] at hT''; cases hT''; rw [hTA] at hA'; cases hA'; exact hxA
  · obtain ⟨B, hB, hr, hwB, hty⟩ := hv.1 T hT'
    rw [hTA] at hB; cases hB
    refine ⟨⟨A, hA, hr, hwB, hty⟩, fun e he => ?_⟩
    obtain ⟨e', he', habe⟩ := hisf e he
    obtain ⟨x, hx, -⟩ := his e he
    have := hv.2 e' he'
    rw [key habe hx] at this; cases this; exact hx

/-- The binders of a chain of openings, as wants, can be opened (`WantsCons`). -/
theorem chain_cons {C : Ctx} {kind : String} {sc0 fin : Scope} {n0 N : Nat} {Sc : Sigs} {ρ outerv : List Value}
    {outer : List Nat} (h0 : WSat Sc sc0.Γ ρ) (hp0 : sc0.Γ <+: fin.Γ) (hl : fin.Γ.length = sc0.Γ.length + N)
    (houter : Term.evalList ρ [] (outer.map .entry) = some outerv) (hs : C.solving = false) {scm : Scope}
    {os : List Opening} (hc : Chain C kind fin scm os) :
    ∀ {ws : List Want} {prev : List Value}, WTermInv scm n0 Sc (ρ ++ prev) →
      Pairs (WantAbs fin.Γ (outer ++ List.range' sc0.Γ.length N)) os ws → WantsCons Sc ρ ws (outerv ++ prev) := by
  induction hc with
  | nil =>
    intro ws prev _ hp
    cases ws with
    | nil => trivial
    | cons => exact (hp : False).elim
  | cons ho hc ih =>
    intro ws prev hT hp
    cases ws with
    | nil => exact (hp : False).elim
    | cons w ws =>
      obtain ⟨hw, hws⟩ := hp
      obtain ⟨hhead, htr⟩ := want_open h0 hp0 hl houter hT (chain_shape (.cons ho hc)).1 hs ho hw
      refine ⟨hhead.1, hhead.2, fun v hv => ?_⟩
      have := ih (prev := prev ++ [v]) (by simpa using wopen hT ho (htr false v hv)) hws
      simpa using this

/-- Values meeting the binders of a chain of openings as wants extend an invariant `P` along the chain. -/
theorem chain_sat {C : Ctx} {kind : String} {sc0 fin : Scope} {n0 N : Nat} {Sc : Sigs} {ρ outerv : List Value}
    {outer : List Nat} (P : Scope → List Value → Prop) (hPW : ∀ s ρ', P s ρ' → WTermInv s n0 Sc ρ')
    (Q : Bool → Prop) (step : ∀ {s : Scope} {name : Id} {ann : Ann} {mult : Option Mult} {o : Opening}
      {ρ' : List Value} {v : Value} {t : Bool}, opening C s name ann mult kind = .ok o → P s ρ' → Q t →
      OpenOk Sc ρ' o t v → P o.sc (ρ' ++ [v]))
    (h0 : WSat Sc sc0.Γ ρ) (hp0 : sc0.Γ <+: fin.Γ) (hl : fin.Γ.length = sc0.Γ.length + N)
    (houter : Term.evalList ρ [] (outer.map .entry) = some outerv) (hsolv : C.solving = false) {scm : Scope}
    {os : List Opening} (hc : Chain C kind fin scm os) : ∀ {ws : List Want} {prev vs : List Value} {ts : List Bool},
      P scm (ρ ++ prev) → Pairs (WantAbs fin.Γ (outer ++ List.range' sc0.Γ.length N)) os ws → (∀ t ∈ ts, Q t) →
      WantsSat Sc ρ ws (outerv ++ prev) ts vs → P fin (ρ ++ prev ++ vs) := by
  induction hc with
  | nil =>
    intro ws prev vs ts hP hp _ hs
    cases ws with
    | cons => exact (hp : False).elim
    | nil =>
      cases ts with
      | cons => exact (hs : False).elim
      | nil =>
        cases vs with
        | cons => exact (hs : False).elim
        | nil => simpa using hP
  | cons ho hc ih =>
    intro ws prev vs ts hP hp hQ hs
    cases ws with
    | nil => exact (hp : False).elim
    | cons w ws =>
      cases ts with
      | nil => exact (hs : False).elim
      | cons t ts =>
        cases vs with
        | nil => exact (hs : False).elim
        | cons v vs =>
          obtain ⟨hw, hws⟩ := hp
          obtain ⟨hv, hvs⟩ := hs
          obtain ⟨-, htr⟩ := want_open h0 hp0 hl houter (hPW _ _ hP) (chain_shape (.cons ho hc)).1 hsolv ho hw
          have hP' := step ho hP (hQ t List.mem_cons_self) (htr t v hv)
          have := ih (prev := prev ++ [v]) (vs := vs) (by simpa using hP') hws
            (fun t' h => hQ t' (List.mem_cons_of_mem _ h)) (by simpa using hvs)
          simpa using this

theorem telescope_go_chain {C : Ctx} {kind : String} : ∀ (bs : List Binder) (sc : Scope) (seen : List String)
    (acc : List (Binder × Opening)) {res : Scope × List String × List (Binder × Opening)},
    telescope.go C kind sc seen acc bs = .ok res →
    ∃ new, res.2.2 = acc ++ new ∧ new.map (·.1) = bs ∧ Chain C kind res.1 sc (new.map (·.2))
  | [], sc, seen, acc, res, h => by
    simp only [telescope.go, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], by simp, rfl, .nil⟩
  | b :: bs, sc, seen, acc, res, h => by
    simp only [telescope.go] at h
    obtain ⟨seen', -, h⟩ := bind_eq_ok.1 h
    obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
    obtain ⟨new, h1, h2, h3⟩ := telescope_go_chain bs _ _ _ h
    exact ⟨(b, o) :: new, by simp [h1], by simp [h2], .cons ho h3⟩

/-- A checked telescope is a chain of openings, whose binders, as wants, are the openings abstracted. -/
theorem telescope_chain {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat}
    {out : Checked} (h : telescope C sc bs kind outer = .ok out) :
    ∃ os, Chain C kind out.sc sc os ∧
      Pairs (WantAbs out.sc.Γ (outer ++ List.range' sc.Γ.length bs.length)) os (out.tele.map Want.of) := by
  have hsh := telescope_shape h
  unfold telescope at h
  obtain ⟨⟨sc', seen, opens⟩, hgo, h⟩ := bind_eq_ok.1 h
  obtain ⟨tele, htele, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨new, hnew, h1, hc⟩ := telescope_go_chain bs sc [] [] hgo
  simp only [List.nil_append] at hnew
  subst hnew
  obtain ⟨hl, hi⟩ := mapM_ok htele
  have hlen : opens.length = bs.length := by rw [← h1, List.length_map]
  refine ⟨_, hc, pairs_of_getElem (by simp [hl, hlen]) fun i o w ho hw => ?_⟩
  rw [← hsh.2.1]
  rw [List.getElem?_map, Option.map_eq_some_iff] at ho hw
  obtain ⟨⟨b', o'⟩, hbo, rfl⟩ := ho
  obtain ⟨t, ht, rfl⟩ := hw
  have hbm : bs[i]? = some b' := by rw [← h1, List.getElem?_map, hbo]; rfl
  exact abstracted_abs (hi i (b', b', o') t (List.getElem?_zip_eq_some.2 ⟨hbm, hbo⟩) ht)

end TermFill

/-- Opening a checked telescope to values satisfying it, after the values `outerv` of the entries `outer` it was
abstracted over first, satisfies the scope it was checked in, extended by those values. -/
theorem telescope_sound {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat} {out : Checked}
    {n0 : Nat} {Sc : Sigs} {ρ outerv vs : List Value} (hT : TermInv sc n0 Sc ρ)
    (hs : C.solving = false) (h : telescope C sc bs kind outer = .ok out)
    (houter : Term.evalList ρ [] (outer.map .entry) = some outerv)
    (hvs : TeleSat Sc ρ out.tele outerv vs) : TermInv out.sc n0 Sc (ρ ++ vs) := by
  obtain ⟨os, hc, hp⟩ := TermFill.telescope_chain h
  obtain ⟨-, -, hl, hp0, -⟩ := telescope_shape h
  have := TermFill.chain_sat (n0 := n0) (TermInv · n0 Sc ·) (fun _ _ h => h.weak) (· = true)
    (fun ho hP ht hv => by subst ht; exact TermFill.topen hP ho hv) hT.sat.1 hp0 hl houter hs hc (prev := [])
    (ts := out.tele.map fun _ => true) (by simpa using hT) hp (by simp) (by simpa using TeleSat.wantsSat hT.noJunk hvs)
  simpa using this

/-- `telescope_sound` for values that only meet the telescope by their heads, as a tainted call's arguments may. -/
theorem telescope_wsound {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat} {out : Checked}
    {n0 : Nat} {Sc : Sigs} {ρ outerv vs : List Value} (hT : WTermInv sc n0 Sc ρ)
    (hs : C.solving = false) (h : telescope C sc bs kind outer = .ok out)
    (houter : Term.evalList ρ [] (outer.map .entry) = some outerv)
    (hvs : WantsSat Sc ρ (out.tele.map Want.of) outerv (out.tele.map fun _ => false) vs) :
    WTermInv out.sc n0 Sc (ρ ++ vs) := by
  obtain ⟨os, hc, hp⟩ := TermFill.telescope_chain h
  obtain ⟨-, -, hl, hp0, -⟩ := telescope_shape h
  have := TermFill.chain_sat (n0 := n0) (WTermInv · n0 Sc ·) (fun _ _ h => h) (fun _ => True)
    (fun ho hP _ hv => TermFill.wopen hP ho hv) hT.sat hp0 hl houter hs hc (prev := [])
    (by simpa using hT) hp (by simp) (by simpa using hvs)
  simpa using this

/-- A checked telescope can be opened (`WantsCons`): an `is` binder's type is its term's type (§6), so whatever
values the other binders take, by their types' heads, an `is` binder's value has its type by its head. -/
theorem telescope_cons {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat} {out : Checked}
    {n0 : Nat} {Sc : Sigs} {ρ outerv : List Value} (hT : WTermInv sc n0 Sc ρ)
    (hs : C.solving = false) (h : telescope C sc bs kind outer = .ok out)
    (houter : Term.evalList ρ [] (outer.map .entry) = some outerv) :
    WantsCons Sc ρ (out.tele.map Want.of) outerv := by
  obtain ⟨os, hc, hp⟩ := TermFill.telescope_chain h
  obtain ⟨-, -, hl, hp0, -⟩ := telescope_shape h
  simpa using TermFill.chain_cons hT.sat hp0 hl houter hs hc (prev := []) (by simpa using hT) hp

namespace TermFill

theorem letWants_go_chain {C : Ctx} : ∀ (bs : List LetBinder) (sc : Scope) (untyped : List String)
    (acc : List (Option Opening)) {res : Scope × List (Option Opening)},
    letWants.go C false sc untyped acc bs = .ok res → bs.all (·.ann.isSome) = true →
    bs.any (·.ann.any (·.term.holed)) = false →
    ∃ new, res.2 = acc ++ new.map some ∧ new.length = bs.length ∧ Chain C "binder" res.1 sc new
  | [], sc, untyped, acc, res, h, _, _ => by
    simp only [letWants.go, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], by simp, rfl, .nil⟩
  | b :: bs, sc, untyped, acc, res, h, hall, hf => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    simp only [List.any_cons, Bool.or_eq_false_iff] at hf
    simp only [letWants.go] at h
    split at h
    · rename_i ann hann
      obtain ⟨-, -, h⟩ := bind_eq_ok.1 h
      obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
      obtain ⟨new, h1, h2, h3⟩ := letWants_go_chain bs _ _ _ h hall.2 hf.2
      have hfa : ann.term.holed = false := by simpa [hann] using hf.1
      exact ⟨o :: new, by simp [h1], by simp [h2], .cons (by simpa using ho) h3⟩
    · rename_i hn
      simp [hn] at hall

theorem letWants_eq {C : Ctx} {sc sc' : Scope} {bs : List LetBinder} {ws : List Want}
    (h : letWants C sc bs = .ok (ws, sc')) (hf : bs.any (·.ann.any (·.term.holed)) = false) :
    sc' = sc ∧ ∃ sc'' opens, letWants.go C false sc [] [] bs = .ok (sc'', opens) ∧
      (bs.zip opens).mapM (letWant sc''.Γ (opens.map fun o => (o.map (·.id)).getD sc''.Γ.length)) = .ok ws := by
  unfold letWants at h
  rw [hf] at h
  obtain ⟨⟨sc'', opens⟩, hgo, h⟩ := bind_eq_ok.1 h
  obtain ⟨ws', hws, h⟩ := bind_eq_ok.1 h
  simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, sc'', opens, hgo, hws⟩

/-- A tuple `let` whose binders are all annotated gives its right-hand side a chain of openings, abstracted. -/
theorem letWants_chain {C : Ctx} {sc sc' : Scope} {bs : List LetBinder} {ws : List Want}
    (h : letWants C sc bs = .ok (ws, sc')) (hall : bs.all (·.ann.isSome) = true)
    (hf : bs.any (·.ann.any (·.term.holed)) = false) :
    ∃ fin os, Chain C "binder" fin sc os ∧ Pairs (WantAbs fin.Γ (List.range' sc.Γ.length os.length)) os ws := by
  obtain ⟨-, sc', opens, hgo, h⟩ := letWants_eq h hf
  obtain ⟨new, hnew, hlen, hc⟩ := letWants_go_chain bs sc [] [] hgo hall hf
  simp only [List.nil_append] at hnew
  subst hnew
  obtain ⟨hl, hi⟩ := mapM_ok h
  have hids := (chain_shape hc).2.2
  refine ⟨sc', new, hc, pairs_of_getElem (by simp [hl, hlen]) fun i o w ho hw => ?_⟩
  obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 ho).1)⟩
  have := hi i (b, some o) w (List.getElem?_zip_eq_some.2 ⟨hb, by simp [ho]⟩) hw
  simp only [letWant] at this
  obtain ⟨t, ht, this⟩ := bind_eq_ok.1 this
  simp only [pure, Except.pure, Except.ok.injEq] at this
  subst this
  have hids' : (new.map some).map (fun o => (o.map (·.id)).getD sc'.Γ.length) = new.map (·.id) := by simp
  rw [hids', hids] at ht
  exact abstracted_abs ht

end TermFill

/-- What a tuple `let` whose binders are all annotated gives its right-hand side can be opened. -/
theorem letWants_cons {C : Ctx} {sc sc' : Scope} {bs : List LetBinder} {ws : List Want} {n0 : Nat} {Sc : Sigs}
    {ρ : List Value} (hT : WTermInv sc n0 Sc ρ) (hs : C.solving = false) (h : letWants C sc bs = .ok (ws, sc'))
    (hall : bs.all (·.ann.isSome) = true) (hf : bs.any (·.ann.any (·.term.holed)) = false) :
    WantsCons Sc ρ ws [] := by
  obtain ⟨fin, os, hc, hp⟩ := TermFill.letWants_chain h hall hf
  obtain ⟨hp0, hl, -⟩ := TermFill.chain_shape hc
  simpa using TermFill.chain_cons (outer := []) (outerv := []) hT.sat hp0 hl rfl hs hc (prev := [])
    (by simpa using hT) hp

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
    (hs : C.solving = false) (h : annotation C sc g ann = .ok (tele, env)) :
    ∃ envv, Term.evalList ρ [] env = some envv ∧ WantsCons Sc ρ (tele.map Want.of) envv := by
  rcases annotation_shape h with ⟨bs, out, rfl, hout, rfl, rfl, -⟩ | ⟨p, g', rfl, rfl, hw, hte, rfl⟩
  · exact ⟨[], rfl, telescope_cons (outer := []) hT hs hout rfl⟩
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
    letWants.go C false sc untyped acc bs = .ok res → res.2.length = acc.length + bs.length
  | [], sc, untyped, acc, res, h => by
    simp only [letWants.go, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | b :: bs, sc, untyped, acc, res, h => by
    simp only [letWants.go] at h
    split at h
    · obtain ⟨-, -, h⟩ := bind_eq_ok.1 h
      obtain ⟨o, -, h⟩ := bind_eq_ok.1 h
      have := letWants_go_length bs _ _ _ h; simp at this ⊢; omega
    · have := letWants_go_length bs _ _ _ h; simp at this ⊢; omega

/-- What a tuple `let` gives its right-hand side: one entry per binder, with the binder's multiplicity, and the
scope it is checked in. -/
theorem letWants_spec {C : Ctx} {sc sc' : Scope} {bs : List LetBinder} {ws : List Want}
    (h : letWants C sc bs = .ok (ws, sc')) (hf : bs.any (·.ann.any (·.term.holed)) = false) :
    sc' = sc ∧ ws.length = bs.length ∧ ∀ (i : Nat) (w : Want) (b : LetBinder), ws[i]? = some w → bs[i]? = some b →
      w.mult = b.mult.getD .many := by
  obtain ⟨hsc, sc'', opens, hgo, h⟩ := TermFill.letWants_eq h hf
  have hol := letWants_go_length bs sc [] [] hgo
  simp only [List.length_nil, Nat.zero_add] at hol
  obtain ⟨hl, hi⟩ := mapM_ok h
  refine ⟨hsc, by simp [hl, hol], fun i w b hw hb => ?_⟩
  obtain ⟨o, ho⟩ : ∃ o, opens[i]? = some o := by
    have : i < opens.length := by rw [hol]; exact (List.getElem?_eq_some_iff.1 hb).1
    exact ⟨_, List.getElem?_eq_getElem this⟩
  have hb' := hi i (b, o) w (List.getElem?_zip_eq_some.2 ⟨hb, ho⟩) hw
  cases o with
  | some o =>
    simp only [letWant] at hb'
    obtain ⟨t, ht, hb'⟩ := bind_eq_ok.1 hb'
    simp only [pure, Except.pure, Except.ok.injEq] at hb'
    subst hb'
    simp [Want.of, (abstracted_ok ht).2.2.2]
  | none =>
    simp only [letWant, pure, Except.pure, Except.ok.injEq] at hb'
    subst hb'
    rfl

end Pledge
