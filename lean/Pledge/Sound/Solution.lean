import Pledge.Sound.Rel

namespace Pledge

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


/-- No entry among `xs` is tainted. -/
abbrev Untainted (Γ : Entries) (xs : List Nat) : Prop := ∀ x ∈ xs, (Γ[x]?).any (·.tainted) = false

mutual
/-- A term `coreType` checks has a value with its type by its head under a valuation satisfying the scope by heads,
and has that type when `typed`: when the valuation satisfies the scope and every entry the term mentions is
untainted. -/
theorem coreType_sound {S Sc : Sigs} {Γ : Entries} {ρ : List Value} {n0 : Nat} (hΓ : WSat Sc Γ ρ)
    (hS : SigsClose S ρ Sc) (hJ : Sc.find junkHead = none) (hok : SigsOk n0 S) (hn : n0 ≤ ρ.length) (typed : Bool) :
    ∀ (t : Term) {T : Term}, coreType S Γ t = some T → (typed = true → Sat Sc Γ ρ ∧ Untainted Γ t.entries) →
      ∃ v A, t.eval ρ [] = some v ∧ T.eval ρ [] = some A ∧ v.noRemoved = true ∧ WType Sc v A ∧
        (typed = true → HasType Sc v A)
  | .entry i, T, h, ht => by
    simp only [coreType, Option.map_eq_some_iff] at h
    obtain ⟨en, hen, rfl⟩ := h
    obtain ⟨v, A, hv, hA, hr, hw, -⟩ := hΓ.2 i en hen
    refine ⟨v, A, hv, hA, hr, hw, fun hty => ?_⟩
    obtain ⟨hsat, hu⟩ := ht hty
    exact hsat.2 i en v A hen hv hA (by simpa [hen] using hu i (by simp [Term.entries]))
  | .bound _, T, h, _ => by simp [coreType] at h
  | .app hd as, T, h, ht => by
    simp only [coreType, Option.bind_eq_some_iff] at h
    obtain ⟨sig, hsig, h⟩ := h
    split at h
    · rename_i hargs
      cases h
      obtain ⟨vs, hvs, hl, hnr, hws⟩ := coreArgs_sound hΓ hS hJ hok hn typed sig.params [] as hargs rfl
        fun hty => ⟨(ht hty).1, by simpa [Term.entries] using (ht hty).2⟩
      obtain ⟨hbelow, hbounds⟩ := hok sig (List.mem_of_find?_eq_some hsig)
      obtain ⟨A, hA⟩ : ∃ A, sig.ret.eval ρ vs = some A := by
        refine Term.eval_isSome _ ?_ (by rw [hl]; exact hbounds)
        simp only [Sig.entriesBelow, Bool.and_eq_true] at hbelow
        exact Term.entriesBelow_mono hn _ hbelow.2
      obtain ⟨sig', hc, -⟩ := hS.find hsig
      have hne : hd ≠ junkHead := fun e => by rw [e, hJ] at hc; cases hc
      refine ⟨.app hd vs, A, Term.eval_app.2 ⟨vs, hvs, rfl⟩, by rw [Term.eval_subst hvs]; exact hA,
        by simpa [Value.noRemoved] using hnr, ?_, fun hty => ?_⟩
      · simp only [WType, hne, ↓reduceIte]
        exact ⟨sig', hc, by rw [hS.ret_eval hsig hc]; exact hA⟩
      · exact (hS.hasType_app_iff hsig).2 ⟨WantsSat.teleSat hws (by simp [hty]), hA⟩
    · cases h
theorem coreArgs_sound {S Sc : Sigs} {Γ : Entries} {ρ : List Value} {n0 : Nat} (hΓ : WSat Sc Γ ρ)
    (hS : SigsClose S ρ Sc) (hJ : Sc.find junkHead = none) (hok : SigsOk n0 S) (hn : n0 ≤ ρ.length) (typed : Bool) :
    ∀ (params : Telescope) (prev as : List Term) {prevv : List Value}, coreArgs S Γ params prev as = true →
      Term.evalList ρ [] prev = some prevv → (typed = true → Sat Sc Γ ρ ∧ Untainted Γ (Term.entriesList as)) →
      ∃ vs, Term.evalList ρ [] as = some vs ∧ vs.length = params.length ∧ Value.noRemovedList vs = true ∧
        WantsSat Sc ρ (params.map Want.of) prevv (params.map fun _ => typed) vs
  | [], _, [], _, _, _, _ => ⟨[], rfl, rfl, rfl, trivial⟩
  | p :: ps, prev, a :: as, prevv, h, hprev, ht => by
    simp only [coreArgs, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases hT' : coreType S Γ a with
    | none => simp [hT'] at h1
    | some T' =>
      simp only [hT', Option.any_some] at h1
      have hsub : ∀ hty : typed = true, Untainted Γ a.entries ∧ Untainted Γ (Term.entriesList as) := fun hty =>
        ⟨fun x hx => (ht hty).2 x (by simp [Term.entriesList, hx]),
          fun x hx => (ht hty).2 x (by simp [Term.entriesList, hx])⟩
      obtain ⟨v, A, hv, hA, hnr, hw, hty⟩ := coreType_sound hΓ hS hJ hok hn typed a hT'
        fun hty => ⟨(ht hty).1, (hsub hty).1⟩
      obtain ⟨vs, hvs, hl, hnrs, hws⟩ := coreArgs_sound hΓ hS hJ hok hn typed ps (prev ++ [a]) as h3
        (Term.evalList_append hprev (Term.evalList_singleton.2 ⟨v, hv, rfl⟩)) fun hty => ⟨(ht hty).1, (hsub hty).2⟩
      refine ⟨v :: vs, Term.evalList_cons_eq_some.2 ⟨v, vs, hv, hvs, rfl⟩, by simp [hl],
        by simp [Value.noRemovedList, hnr, hnrs], ⟨fun T hT => ?_, fun e he => ?_⟩, hws⟩
      · cases hT
        exact ⟨A, by rw [← Term.eval_subst hprev, hΓ.eval_eq_of_identical h1, hA], hnr, hw, hty⟩
      · have he' : p.is = some e := he
        have hi : identical Γ (e.subst prev) a = true := by simpa [he'] using h2
        rw [← Term.eval_subst hprev, hΓ.eval_eq_of_identical hi, hv]
  | [], _, _ :: _, _, h, _, _ => by simp [coreArgs] at h
  | _ :: _, _, [], _, h, _, _ => by simp [coreArgs] at h
end

/-- The term `Scope.solution` takes for a `_` (§16): a term of the scope (`coreType`) with the wanted type, meeting the
`is` term, tainted as §12 says. -/
theorem Scope.solution_spec {C : Ctx} {sc : Scope} {ts : List Term} {pos : Pos} {type : Term} {is : Option Term}
    {erased : Bool} {r : Res} (h : sc.solution C ts pos type is erased = .ok r) :
    (∃ has, coreType sc.sigs sc.Γ r.term = some has ∧ identical sc.Γ type has = true) ∧
      (∀ e, is = some e → identical sc.Γ e r.term = true) ∧
      r.tainted = (sc.taintedBy.isSome || r.term.entries.any fun x => (sc.Γ[x]?).any (·.tainted)) ∧
      r.erased = erased := by
  unfold Scope.solution at h
  simp only at h
  split at h
  · rename_i t ht
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hw := List.find?_some ht
    split at hw
    · simp at hw
    · rename_i has hc
      refine ⟨⟨has, hc, ?_⟩, fun e he => ?_, rfl, rfl⟩
      · cases hn : identical sc.Γ type has
        · simp [hn] at hw
        · rfl
      · cases hn : identical sc.Γ e t
        · have : is.any (!identical sc.Γ · t) = true := by simp [he, hn]
          simp only [this] at hw
          split at hw <;> simp at hw
        · rfl
  · simp [failAt_eq] at h

/-- With `solving` off, a `_` takes a term of the table, changing nothing in the scope, and its tree is removed. -/
theorem Scope.hole_spec {C : Ctx} {sc : Scope} {pos : Pos} {type : Term} {is : Option Term} {erased : Bool} {o : Out}
    (hs : C.solving = false) (h : sc.hole C pos type is erased = .ok o) :
    o.sc = sc ∧ o.tree = .removed ∧ o.snaps = [] ∧
      ∃ ts r, sc.solution C ts pos type is erased = .ok r ∧ o.res = [r] := by
  unfold Scope.hole at h
  split at h
  · obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, _, r, hr, rfl⟩
  · rename_i hsv; rw [hs] at hsv; cases hsv
  · simp [internal, failAt_eq] at h

/-- A `_` argument (§16): erased, inside a type, or of type `Type()`, and a `_` as `Scope.hole` takes it. -/
theorem holeArg_spec {C : Ctx} {sc : Scope} {g : Given} {p : TBinder} {prev : List Res} {pos : Pos} {o : Out}
    (hs : C.solving = false) (h : holeArg C sc g p prev pos = .ok o) :
    (C.erased || g.erasedAt 0 || C.inType || identical sc.Γ (p.type.subst (prev.map (·.term))) .TYPE) = true ∧
      o.sc = sc ∧ o.tree = .removed ∧ o.snaps = [] ∧ ∃ ts r, sc.solution C ts pos (p.type.subst (prev.map (·.term)))
        (p.is.map (·.subst (prev.map (·.term)))) (C.erased || g.erasedAt 0) = .ok r ∧ o.res = [r] := by
  unfold holeArg at h
  simp only at h
  split at h
  · rename_i hc
    exact ⟨by simpa [Bool.or_assoc] using hc, Scope.hole_spec hs h⟩
  · simp [failAt_eq, bind, Except.bind] at h

/-- The value of the term a `_` takes: it has the wanted type, by its head, and when the `_` is untainted and the
valuation satisfies the scope, has it; and it is the `is` term's value. -/
theorem Scope.solution_sound {C : Ctx} {sc : Scope} {ts : List Term} {pos : Pos} {type : Term} {is : Option Term}
    {erased : Bool} {r : Res} {Sc : Sigs} {ρ : List Value} {n0 : Nat} (hΓ : WSat Sc sc.Γ ρ)
    (hS : SigsClose sc.sigs ρ Sc) (hJ : Sc.find junkHead = none) (hok : SigsOk n0 sc.sigs) (hn : n0 ≤ ρ.length)
    (h : sc.solution C ts pos type is erased = .ok r) :
    ∃ v A, r.term.eval ρ [] = some v ∧ type.eval ρ [] = some A ∧ v.noRemoved = true ∧ WType Sc v A ∧
      (Sat Sc sc.Γ ρ → r.tainted = false → HasType Sc v A) ∧ ∀ e, is = some e → e.eval ρ [] = some v := by
  obtain ⟨⟨has, hc, hid⟩, his, ht, -⟩ := Scope.solution_spec h
  obtain ⟨v, A, hv, hA, hnr, hw, -⟩ := coreType_sound hΓ hS hJ hok hn false r.term hc (by simp)
  refine ⟨v, A, hv, by rw [hΓ.eval_eq_of_identical hid, hA], hnr, hw, fun hsat hrt => ?_,
    fun e he => by rw [hΓ.eval_eq_of_identical (his e he), hv]⟩
  rw [hrt, eq_comm, Bool.or_eq_false_iff, List.any_eq_false] at ht
  obtain ⟨v', A', hv', hA', -, -, hty⟩ := coreType_sound hΓ hS hJ hok hn true r.term hc
    fun _ => ⟨hsat, fun x hx => by simpa using ht.2 x hx⟩
  rw [hv] at hv'; cases hv'
  rw [hA] at hA'; cases hA'
  exact hty rfl

/-- The value of a `_` argument (§16): it meets its parameter, the earlier arguments taking the values `prevv`, by
its head, and, when the `_` is untainted and the valuation satisfies the scope, with its type. -/
theorem holeArg_value {C : Ctx} {sc : Scope} {g : Given} {p : TBinder} {prev : List Res} {pos : Pos} {o : Out}
    {Sc : Sigs} {ρ prevv : List Value} {n0 : Nat} (hs : C.solving = false) (hΓ : WSat Sc sc.Γ ρ)
    (hS : SigsClose sc.sigs ρ Sc) (hJ : Sc.find junkHead = none) (hok : SigsOk n0 sc.sigs) (hn : n0 ≤ ρ.length)
    (hprev : Term.evalList ρ [] (prev.map (·.term)) = some prevv) (h : holeArg C sc g p prev pos = .ok o) :
    ∃ r v A, o.res = [r] ∧ r.term.eval ρ [] = some v ∧ p.type.eval ρ prevv = some A ∧ v.noRemoved = true ∧
      WType Sc v A ∧ (Sat Sc sc.Γ ρ → r.tainted = false → HasType Sc v A) ∧
      ∀ e, p.is = some e → e.eval ρ prevv = some v := by
  obtain ⟨-, -, -, -, ts, r, hr, hres⟩ := holeArg_spec hs h
  obtain ⟨v, A, hv, hA, hnr, hw, hty, his⟩ := Scope.solution_sound hΓ hS hJ hok hn hr
  refine ⟨r, v, A, hres, hv, by rw [← Term.eval_subst hprev]; exact hA, hnr, hw, hty, fun e he => ?_⟩
  rw [← Term.eval_subst hprev]
  exact his _ (by simp [he])

/-- A value of type `Type()` is headed by a type constructor, so `removed` stands for it at run time. -/
theorem removed_rel_type {S : Sigs} {phase : Nat} {v : Value} (hT : TypeHeads S) (h : HasType S v Value.TYPE) :
    Rel S phase .removed v := by
  obtain ⟨hd, ws, sig, rfl, hs, -, hr⟩ := h.inv
  exact .type (hT hd sig ws hs hr)

end Pledge
