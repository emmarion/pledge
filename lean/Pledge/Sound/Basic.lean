import Pledge.Sound.Defs

namespace Pledge

theorem Prog.Ext.refl (P : Prog) : P.Ext P := ⟨fun _ _ h => h, fun _ _ h hk => ⟨h, hk⟩⟩

theorem Prog.Ext.trans {P₁ P₂ P₃ : Prog} (h₁ : P₁.Ext P₂) (h₂ : P₂.Ext P₃) : P₁.Ext P₃ :=
  ⟨fun n d h => h₂.fns n d (h₁.fns n d h), fun n k h hk =>
    let ⟨h', hk'⟩ := h₁.kind n k h hk
    h₂.kind n k h' hk'⟩

theorem Sigs.Sub.trans {S₁ S₂ S₃ : Sigs} (h₁ : S₁.Sub S₂) (h₂ : S₂.Sub S₃) : S₁.Sub S₃ :=
  fun h sig hs => h₂ h sig (h₁ h sig hs)

theorem World.Le.refl (W : World) : W.Le W :=
  ⟨Prog.Ext.refl _, Sigs.Sub.refl _, List.prefix_refl _, fun _ _ _ _ _ h h' => (by rw [h] at h'; cases h'), id, id⟩

theorem World.Le.trans {W₁ W₂ W₃ : World} (h₁ : W₁.Le W₂) (h₂ : W₂.Le W₃) : W₁.Le W₃ := by
  refine ⟨h₁.prog.trans h₂.prog, h₁.sigs.trans h₂.sigs, h₁.val.trans h₂.val, ?_, fun h => h₂.noJunk (h₁.noJunk h),
    fun h => h₂.typeHeads (h₁.typeHeads h)⟩
  intro h sig' ws hd us hn hs hr
  cases hm : W₂.Sc.find h with
  | none =>
    obtain ⟨hk, hd'⟩ := h₂.fresh h sig' ws hd us hm hs hr
    refine ⟨hk, hd'.imp_right fun hd' => ?_⟩
    cases h₃ : W₁.Sc.find hd with
    | none => rfl
    | some s => rw [h₁.sigs _ _ h₃] at hd'; cases hd'
  | some s =>
    obtain rfl := Option.some.inj ((h₂.sigs _ _ hm).symm.trans hs)
    exact h₁.fresh h s ws hd us hn hm hr

theorem World.Le.take {W W' : World} (h : W.Le W') : W'.ρ.take W.ρ.length = W.ρ := by
  obtain ⟨t, ht⟩ := h.val
  rw [← ht]; simp

theorem World.Le.take_of_le {W W' : World} (h : W.Le W') {n : Nat} (hn : n ≤ W.ρ.length) :
    W'.ρ.take n = W.ρ.take n := by
  obtain ⟨t, ht⟩ := h.val
  rw [← ht, List.take_append_of_le_length hn]

mutual
/-- A term that has a value mentions only entries the valuation gives values to. -/
theorem Term.entriesBelow_of_eval {ρ env : List Value} :
    ∀ (t : Term) {v : Value}, t.eval ρ env = some v → t.entriesBelow ρ.length = true
  | .entry i, _, h => by
    simp only [Term.eval] at h
    simpa [Term.entriesBelow] using (List.getElem?_eq_some_iff.1 h).1
  | .bound _, _, _ => rfl
  | .app _ as, _, h => by
    obtain ⟨vs, hvs, -⟩ := Term.eval_app.1 h
    exact Term.entriesBelowList_of_evalList as hvs
theorem Term.entriesBelowList_of_evalList {ρ env : List Value} :
    ∀ (as : List Term) {vs : List Value}, Term.evalList ρ env as = some vs → Term.entriesBelowList ρ.length as = true
  | [], _, _ => rfl
  | a :: as, _, h => by
    obtain ⟨v, vs, hv, hvs, -⟩ := Term.evalList_cons_eq_some.1 h
    simp only [Term.entriesBelowList, Term.entriesBelow_of_eval a hv, Term.entriesBelowList_of_evalList as hvs,
      Bool.and_self]
end

mutual
/-- A term whose entries and bound variables are in range has a value. -/
theorem Term.eval_isSome {ρ env : List Value} :
    ∀ t : Term, t.entriesBelow ρ.length = true → t.boundsBelow env.length = true → ∃ v, t.eval ρ env = some v
  | .entry i, h, _ => by
    simp only [Term.entriesBelow, decide_eq_true_eq] at h
    exact ⟨_, List.getElem?_eq_getElem h⟩
  | .bound i, _, h => by
    simp only [Term.boundsBelow, decide_eq_true_eq] at h
    exact ⟨_, List.getElem?_eq_getElem h⟩
  | .app hd as, h, h' => by
    obtain ⟨vs, hvs⟩ := Term.evalList_isSome as h h'
    exact ⟨_, Term.eval_app.2 ⟨vs, hvs, rfl⟩⟩
theorem Term.evalList_isSome {ρ env : List Value} :
    ∀ as : List Term, Term.entriesBelowList ρ.length as = true → Term.boundsBelowList env.length as = true →
      ∃ vs, Term.evalList ρ env as = some vs
  | [], _, _ => ⟨[], rfl⟩
  | a :: as, h, h' => by
    simp only [Term.entriesBelowList, Term.boundsBelowList, Bool.and_eq_true] at h h'
    obtain ⟨v, hv⟩ := Term.eval_isSome a h.1 h'.1
    obtain ⟨vs, hvs⟩ := Term.evalList_isSome as h.2 h'.2
    exact ⟨v :: vs, Term.evalList_cons_eq_some.2 ⟨v, vs, hv, hvs, rfl⟩⟩
end

mutual
theorem Term.entriesBelow_mono {n m : Nat} (hnm : n ≤ m) :
    ∀ t : Term, t.entriesBelow n = true → t.entriesBelow m = true
  | .entry i, h => by simp only [Term.entriesBelow, decide_eq_true_eq] at h ⊢; omega
  | .bound _, _ => rfl
  | .app _ as, h => Term.entriesBelowList_mono hnm as h
theorem Term.entriesBelowList_mono {n m : Nat} (hnm : n ≤ m) :
    ∀ as : List Term, Term.entriesBelowList n as = true → Term.entriesBelowList m as = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.entriesBelowList, Bool.and_eq_true] at h ⊢
    exact ⟨Term.entriesBelow_mono hnm a h.1, Term.entriesBelowList_mono hnm as h.2⟩
end

theorem TBinder.entriesBelow_mono {n m : Nat} (hnm : n ≤ m) {b : TBinder} (h : b.entriesBelow n = true) :
    b.entriesBelow m = true := by
  simp only [TBinder.entriesBelow, Bool.and_eq_true, Option.all_eq_true] at h ⊢
  exact ⟨Term.entriesBelow_mono hnm _ h.1, fun e he => Term.entriesBelow_mono hnm e (h.2 e he)⟩

theorem Sig.entriesBelow_mono {n m : Nat} (hnm : n ≤ m) {sig : Sig} (h : sig.entriesBelow n = true) :
    sig.entriesBelow m = true := by
  simp only [Sig.entriesBelow, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨fun b hb => TBinder.entriesBelow_mono hnm (h.1 b hb), Term.entriesBelow_mono hnm _ h.2⟩

theorem GoalBelow.mono {n m : Nat} {g : CheckedGoal} (hnm : n ≤ m) (h : GoalBelow n g) : GoalBelow m g := by
  unfold GoalBelow at h ⊢
  split at h
  · exact Term.entriesBelow_mono hnm _ h
  · exact fun b hb => TBinder.entriesBelow_mono hnm (h b hb)

/-- The goal facts of the top level's invariant carry over to a later state in a later world that keeps the goal. -/
theorem TopInv.goal_le {st st' : TopState} {ρ ρ' : List Value} (hI : TopInv st ρ)
    (hle : (st.world ρ).Le (st'.world ρ')) (hg : st'.goal = st.goal) (hn : st.sc.Γ.length ≤ st'.sc.Γ.length)
    (ht : st'.sc.taintedBy = none → st.sc.taintedBy = none) : ∀ g, st'.goal = some g →
      GoalBelow st'.sc.Γ.length g ∧ (st'.sc.taintedBy = none → (∀ t, g.kind = .type t → t.closed = true) ∧
        ∀ W', (st'.world ρ').Le W' → GoalTyped W' g) := fun g hg' =>
  let ⟨h1, h2⟩ := hI.goal g (hg ▸ hg')
  ⟨h1.mono hn, fun ht' => let ⟨c, w⟩ := h2 (ht ht'); ⟨c, fun W' hW => w W' (hle.trans hW)⟩⟩

theorem Term.evalList_map_append {ρ ρ' : List Value} {ts : List Term} {vs : List Value}
    (h : Term.evalList ρ [] ts = some vs) : Term.evalList (ρ ++ ρ') [] ts = some vs :=
  Term.evalList_frame_ρ ρ' h

theorem Term.evalList_append_iff {ρ env : List Value} {as bs : List Term} {us : List Value} :
    Term.evalList ρ env (as ++ bs) = some us ↔
      ∃ vs ws, Term.evalList ρ env as = some vs ∧ Term.evalList ρ env bs = some ws ∧ us = vs ++ ws := by
  constructor
  · intro h
    induction as generalizing us with
    | nil => exact ⟨[], us, rfl, h, rfl⟩
    | cons a as ih =>
      obtain ⟨v, us', hv, hus, rfl⟩ := Term.evalList_cons_eq_some.1 h
      obtain ⟨vs, ws, hvs, hws, rfl⟩ := ih hus
      exact ⟨v :: vs, ws, Term.evalList_cons_eq_some.2 ⟨v, vs, hv, hvs, rfl⟩, hws, rfl⟩
  · rintro ⟨vs, ws, hvs, hws, rfl⟩
    exact Term.evalList_append hvs hws

theorem Term.evalList_singleton {ρ env : List Value} {a : Term} {us : List Value} :
    Term.evalList ρ env [a] = some us ↔ ∃ v, a.eval ρ env = some v ∧ us = [v] := by
  rw [Term.evalList_cons_eq_some]
  constructor
  · rintro ⟨v, vs, hv, hvs, rfl⟩
    cases hvs; exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, [], hv, rfl, rfl⟩

mutual
theorem Value.isSub_of_mem {v : Value} : ∀ {as : List Value}, v ∈ as → Value.isSubList v as = true
  | _ :: _, .head _ => by simp [Value.isSubList]
  | _ :: _, .tail _ h => by simp [Value.isSubList, Value.isSub_of_mem h]
theorem Value.isSubList_of_mem_sub {v a : Value} : ∀ {as : List Value}, a ∈ as → v.isSub a = true →
    Value.isSubList v as = true
  | _ :: _, .head _, h => by simp [Value.isSubList, h]
  | _ :: _, .tail _ hm, h => by simp [Value.isSubList, Value.isSubList_of_mem_sub hm h]
end

/-- The checker's strict subtree relation is the evaluator's. -/
theorem Value.StrictSub.lt {v w : Value} (h : v.StrictSub w) : v.lt w := by
  induction h with
  | arg hm => exact Value.isSub_of_mem hm
  | deep hm _ ih => exact Value.isSubList_of_mem_sub hm ih

theorem failAt_eq {α : Type} {pos : Pos} {m : Unit → String} :
    (failAt pos m : CheckM α) = .error { pos, msg := m } := rfl

theorem evalFail_eq {α : Type} {pos : Pos} {m : Unit → String} :
    (evalFail pos m : CheckM α) = .error { pos, msg := m, evaluated := true } := rfl

theorem solveHoles_nil {sc : Scope} (h : sc.holes = []) (l r : Term) (pos : Pos) :
    solveHoles sc l r pos = .ok sc := by
  unfold solveHoles; rw [h]; rfl

theorem ResOks.getElem {S : Sigs} : ∀ {rs : List Res} {vs : List Value}, ResOks S rs vs →
    ∀ (i : Nat) (r : Res) (v : Value), rs[i]? = some r → vs[i]? = some v → ResOk S r v
  | _ :: _, _ :: _, h, 0, _, _, hr, hv => by cases hr; cases hv; exact h.1
  | _ :: _, _ :: _, h, i + 1, r, v, hr, hv => ResOks.getElem h.2 i r v (by simpa using hr) (by simpa using hv)
  | [], [], _, _, _, _, hr, _ => by simp at hr

theorem ResOks.of_getElem {S : Sigs} : ∀ {rs : List Res} {vs : List Value}, rs.length = vs.length →
    (∀ (i : Nat) (r : Res) (v : Value), rs[i]? = some r → vs[i]? = some v → ResOk S r v) → ResOks S rs vs
  | [], [], _, _ => trivial
  | r :: rs, v :: vs, hl, h => ⟨h 0 r v rfl rfl, ResOks.of_getElem (by simpa using hl) fun i r' v' h1 h2 =>
      h (i + 1) r' v' (by simpa using h1) (by simpa using h2)⟩
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

theorem against_go_sound {Sc : Sigs} {sc : Scope} {g : Given} {pos : Pos} {ρ envv : List Value}
    (hΓ : WSat Sc sc.Γ ρ) (hS : SigsClose sc.sigs ρ Sc) (hJ : Sc.find junkHead = none) (hh : sc.holes = [])
    (henv : Term.evalList ρ [] g.env = some envv) :
    ∀ (ws : List Want) (rs : List Res) (prev : List Term) (prevv vs : List Value) (sc' : Scope),
      Term.evalList ρ [] prev = some prevv → Term.evalList ρ [] (rs.map (·.term)) = some vs →
      ResOks Sc rs vs → ws.length = rs.length →
      against.go g pos sc prev ws rs = .ok sc' →
        sc' = sc ∧ WantsSat Sc ρ ws (envv ++ prevv) (rs.map (!·.tainted)) vs
  | [], [], prev, prevv, vs, sc', _, hvs, _, _, h => by
    cases hvs; simp [against.go, pure, Except.pure] at h; exact ⟨h.symm, trivial⟩
  | w :: ws, r :: rs, prev, prevv, vs, sc', hprev, hvs, hok, hl, h => by
    obtain ⟨v, vs', hv, hvs', rfl⟩ := Term.evalList_cons_eq_some.1 hvs
    have hE : Term.evalList ρ [] (g.env ++ prev) = some (envv ++ prevv) := Term.evalList_append henv hprev
    have ih := fun (h' : against.go g pos sc (prev ++ [r.term]) ws rs = .ok sc') =>
      against_go_sound hΓ hS hJ hh henv ws rs (prev ++ [r.term]) (prevv ++ [v]) vs' sc'
      (Term.evalList_append hprev (Term.evalList_singleton.2 ⟨v, hv, rfl⟩)) hvs' hok.2 (by simpa using hl) h'
    obtain ⟨hnr, ⟨A, hA⟩, hty⟩ := hok.1
    rw [against.go] at h
    simp only [Scope.typeOf, solveHoles_nil hh] at h
    cases hT : typeOf sc.sigs sc.Γ r.term with
    | none => simp [hT, internal, failAt, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    | some has =>
      have hhas := typeOf_eval hΓ hS hJ hv hA hT
      have hwT : ∀ T, w.type = some T → identical sc.Γ (T.subst (g.env ++ prev)) has = true →
          ∃ A', T.eval ρ (envv ++ prevv) = some A' ∧ v.noRemoved = true ∧ WType Sc v A' ∧
            ((!r.tainted) = true → HasType Sc v A') := fun T _ hi =>
        ⟨A, by rw [← Term.eval_subst hE, hΓ.eval_eq_of_identical hi, hhas], hnr, hA, fun ht => by
          obtain ⟨V, hV⟩ := hty (by simpa using ht)
          rwa [(hV.wtype hJ).unique hA] at hV⟩
      have hwI : ∀ e, w.is = some e → identical sc.Γ (e.subst (g.env ++ prev)) r.term = true →
          e.eval ρ (envv ++ prevv) = some v := fun e _ hi => by
        rw [← Term.eval_subst hE, hΓ.eval_eq_of_identical hi, hv]
      have fin : against.go g pos sc (prev ++ [r.term]) ws rs = .ok sc' →
          (∀ T, w.type = some T → identical sc.Γ (T.subst (g.env ++ prev)) has = true) →
          (∀ e, w.is = some e → identical sc.Γ (e.subst (g.env ++ prev)) r.term = true) →
          sc' = sc ∧ WantsSat Sc ρ (w :: ws) (envv ++ prevv) ((r :: rs).map (!·.tainted)) (v :: vs') :=
        fun hgo h1 h2 => by
          obtain ⟨h3, h4⟩ := ih hgo
          exact ⟨h3, ⟨fun T hT' => hwT T hT' (h1 T hT'), fun e he => hwI e he (h2 e he)⟩, by simpa using h4⟩
      cases hwt : w.type <;> cases hwi : w.is <;>
        simp only [hT, hwt, hwi, Option.map_some, Option.map_none, pure, Except.pure, bind, Except.bind,
          solveHoles_nil hh, failAt_eq] at h
      · exact fin h (by simp [hwt]) (by simp [hwi])
      · split at h
        · rename_i hi; exact fin h (by simp [hwt]) (fun e he => by rw [hwi] at he; cases he; exact hi)
        · cases h
      · split at h
        · rename_i hi; exact fin h (fun e he => by rw [hwt] at he; cases he; exact hi) (by simp [hwi])
        · cases h
      · split at h
        · split at h
          · rename_i hi hi'
            exact fin h (fun e he => by rw [hwt] at he; cases he; exact hi)
              (fun e he => by rw [hwi] at he; cases he; exact hi')
          · cases h
        · cases h
  | [], _ :: _, _, _, _, _, _, _, _, hl, _ | _ :: _, [], _, _, _, _, _, _, _, hl, _ => by simp at hl

/-- Checking results against what a position is given (§8): the results' ideal values meet it, those of untainted
results with their types. -/
theorem against_sound {Sc : Sigs} {sc sc' : Scope} {g : Given} {pos : Pos} {rs : List Res}
    {ρ envv vs : List Value} (hΓ : WSat Sc sc.Γ ρ) (hS : SigsClose sc.sigs ρ Sc) (hJ : Sc.find junkHead = none)
    (hh : sc.holes = []) (hvs : Term.evalList ρ [] (rs.map (·.term)) = some vs) (hok : ResOks Sc rs vs)
    (henv : Term.evalList ρ [] g.env = some envv) (h : against sc g pos rs = .ok sc') :
    sc' = sc ∧ rs.length = g.wants.length ∧ WantsSat Sc ρ g.wants envv (rs.map (!·.tainted)) vs := by
  simp only [against] at h
  by_cases hl : rs.length = g.wants.length
  · simp only [hl, ne_eq, not_true_eq_false, ↓reduceIte] at h
    obtain ⟨h1, h2⟩ := against_go_sound hΓ hS hJ hh henv g.wants rs [] [] vs sc' rfl hvs hok hl.symm h
    exact ⟨h1, hl, by simpa using h2⟩
  · simp [hl, miscount, failAt_eq, bind, Except.bind] at h

theorem produced_sound {Sc : Sigs} {sc : Scope} {g : Option Given} {pos : Pos} {rs : List Res} {tree : Expr}
    {o : Out} {ρ vs : List Value} (hΓ : WSat Sc sc.Γ ρ) (hS : SigsClose sc.sigs ρ Sc) (hJ : Sc.find junkHead = none)
    (hh : sc.holes = []) (hvs : Term.evalList ρ [] (rs.map (·.term)) = some vs) (hok : ResOks Sc rs vs)
    (hg : ∀ g', g = some g' → ∃ envv, Term.evalList ρ [] g'.env = some envv)
    (h : produced sc g pos rs tree = .ok o) :
    o = ⟨sc, rs, tree, []⟩ ∧ ∀ g', g = some g' → ∀ envv, Term.evalList ρ [] g'.env = some envv →
      rs.length = g'.wants.length ∧ WantsSat Sc ρ g'.wants envv (rs.map (!·.tainted)) vs := by
  cases g with
  | none =>
    simp only [produced, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
    exact ⟨h.symm, by simp⟩
  | some g =>
    simp only [produced] at h
    obtain ⟨sc', hsc, h⟩ := bind_eq_ok.1 h
    cases h
    obtain ⟨envv, henv⟩ := hg g rfl
    obtain ⟨rfl, -⟩ := against_sound hΓ hS hJ hh hvs hok henv hsc
    refine ⟨rfl, fun g' hg envv henv => ?_⟩
    cases hg
    exact (against_sound hΓ hS hJ hh hvs hok henv hsc).2

theorem keep_ok {α : Type} {snaps : List Snapshot} {x : CheckM α} {a : α} : keep snaps x = .ok a ↔ x = .ok a := by
  cases x <;> simp [keep]

theorem ensure_ok {ok : Bool} {pos : Pos} {what : String} {u : Unit} (h : ensure ok pos what = .ok u) :
    ok = true := by
  cases ok
  · simp [ensure, internal, failAt_eq] at h
  · rfl

theorem close_nil {o : Out} (hh : o.sc.holes = []) (since : Nat) : close o since = .ok o := by
  unfold close; rw [hh, List.drop_nil]; rfl

theorem produced_eq {sc : Scope} {g : Option Given} {pos : Pos} {rs : List Res} {tree : Expr} {o : Out}
    (hh : sc.holes = []) (h : produced sc g pos rs tree = .ok o) : o = ⟨sc, rs, tree, []⟩ := by
  cases g with
  | none => simp only [produced, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h; exact h.symm
  | some g =>
    simp only [produced] at h
    obtain ⟨sc', hsc, h⟩ := bind_eq_ok.1 h
    cases h
    simp only [against] at hsc
    split at hsc
    · simp [miscount, failAt_eq, bind, Except.bind] at hsc
    · have : ∀ (ws : List Want) (rs : List Res) (prev : List Term) (sc'' : Scope),
          against.go g pos sc prev ws rs = .ok sc'' → sc'' = sc := by
        intro ws
        induction ws with
        | nil => intro rs prev sc'' h; cases rs <;> simp [against.go, pure, Except.pure] at h <;> exact h.symm
        | cons w ws ih =>
          intro rs prev sc'' h
          cases rs with
          | nil => simp [against.go, pure, Except.pure] at h; exact h.symm
          | cons r rs =>
            rw [against.go] at h
            simp only [Scope.typeOf, solveHoles_nil hh] at h
            cases hT : typeOf sc.sigs sc.Γ r.term with
            | none => simp [hT, internal, failAt, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
            | some has =>
              cases hwt : w.type <;> cases hwi : w.is <;>
                simp only [hT, hwt, hwi, Option.map_some, Option.map_none, pure, Except.pure, bind, Except.bind,
                  solveHoles_nil hh, failAt_eq] at h
              all_goals first
                | exact ih _ _ _ h
                | (split at h <;> first | exact ih _ _ _ h | cases h)
                | (split at h
                   · split at h
                     · exact ih _ _ _ h
                     · cases h
                   · cases h)
      rw [this _ _ _ _ hsc]

theorem applied_eq {sc : Scope} {g : Option Given} {pos : Pos} {rs : List Res} {tree : Expr}
    {since : Option Nat} {snaps : List Snapshot} {o : Out} (hh : sc.holes = [])
    (h : applied sc g pos rs tree since snaps = .ok o) :
    o = ⟨sc, rs, tree, snaps⟩ ∧ produced sc g pos rs tree = .ok ⟨sc, rs, tree, []⟩ := by
  simp only [applied, keep_ok] at h
  obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
  obtain rfl := produced_eq hh ho'
  have hc : close ⟨sc, rs, tree, []⟩ = fun n => .ok ⟨sc, rs, tree, []⟩ := funext (close_nil hh)
  cases since <;> simp only [hc, ok_bind, pure, Except.pure, Except.ok.injEq] at h <;> exact ⟨h.symm, ho'⟩

theorem close_ok {o o' : Out} {since : Nat} (h : close o since = .ok o') : o' = o := by
  unfold close at h
  split at h
  · cases h; rfl
  · obtain ⟨sc, -, h⟩ := bind_eq_ok.1 h
    obtain ⟨vs, -, h⟩ := bind_eq_ok.1 h
    cases h

/-- `closed` with no `_` being solved, around a check that leaves none, is the check. -/
theorem closed_eq {sc : Scope} {check : Scope → CheckM Out} (hh : sc.holes = [])
    (hc : ∀ o, check sc = .ok o → o.sc.holes = []) : closed sc check = check sc := by
  have hs : ({ sc with holes := [] } : Scope) = sc := by cases sc; cases hh; rfl
  unfold closed
  rw [hs]
  cases h : check sc with
  | error e => rfl
  | ok o =>
    have ho := hc o h
    simp only [ok_bind, close_nil ho]
    show Except.ok { o with sc := { o.sc with holes := sc.holes } } = .ok o
    rw [hh, ← ho]

/-- What `finish` does (§12, §16): an expression produces a value; in a tainted scope every result is tainted; outside
a wholly erased position, an erased result is in an erased position; and the tree is removed when the position is
wholly erased or every result is tainted. -/
theorem finish_spec {C : Ctx} {whole : Bool} {g : Option Given} {e : Expr} {o o' : Out}
    (h : finish C whole g e o = .ok o') :
    o.res ≠ [] ∧ o'.sc = o.sc ∧ o'.snaps = o.snaps ∧
      o'.res = (if o.sc.taintedBy.isSome then o.res.map ({ · with tainted := true }) else o.res) ∧
      o'.tree = (if whole || o'.res.all (·.tainted) then .removed else o.tree) ∧
      (whole = false → ∀ (i : Nat) (r : Res), o'.res[i]? = some r → r.erased = true → g.any (·.erasedAt i) = true) := by
  simp only [finish] at h
  obtain ⟨u, hu, h⟩ := bind_eq_ok.1 h
  have hne : o.res ≠ [] := by simpa using ensure_ok hu
  generalize hres : (if o.sc.taintedBy.isSome then o.res.map ({ · with tainted := true }) else o.res) = res at h
  cases whole
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.false_or] at h
    split at h
    · simp [failAt_eq, bind, Except.bind] at h
    · rename_i hx
      simp only [pure, Except.pure, Except.ok.injEq, ok_bind] at h
      subst h
      refine ⟨hne, rfl, rfl, rfl, by simp, fun _ i r hr he => ?_⟩
      have hi : i < res.length := (List.getElem?_eq_some_iff.1 hr).1
      cases hfi : List.find? (fun i => Option.any (fun x => x.erased) res[i]? && !Option.any (fun x => x.erasedAt i) g)
        (List.range res.length) with
      | some j => exact absurd hfi (hx j)
      | none =>
        have := List.find?_eq_none.1 hfi i (List.mem_range.2 hi)
        simpa [hr, he] using this
  · simp only [↓reduceIte, Bool.true_or, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hne, rfl, rfl, rfl, by simp, by simp⟩

theorem single_ok {pos : Pos} {rs : List Res} {r : Res} (h : single pos rs = .ok r) : rs = [r] := by
  unfold single at h
  split at h
  · cases h; rfl
  · simp [miscount, failAt_eq] at h

theorem opened_fst (sc : Scope) (tele : Telescope) (env : List Term) (kind : String) (pos : Pos)
    (taint : Nat → Bool) :
    (opened sc tele env kind pos taint).1 = { sc with Γ := (opened sc tele env kind pos taint).1.Γ } :=
  rfl

theorem openTele.go_prefix_getElem (mk : TBinder → Nat → Entry → Entry) (tele : Telescope) (i : Nat)
    (Γ : Entries) (ids : List Nat) (env : List Term) (k : Nat) (hk : k < Γ.length) :
    (openTele.go mk i tele ⟨Γ, ids, env⟩).Γ[k]? = Γ[k]? := by
  obtain ⟨Δ, h, -⟩ := openTele.go_shape mk tele i Γ ids env
  rw [h, List.getElem?_append_left hk]

theorem openTele.go_getElem (mk : TBinder → Nat → Entry → Entry) :
    ∀ (tele : Telescope) (i : Nat) (Γ : Entries) (ids : List Nat) (env : List Term) (k : Nat) (b : TBinder),
      tele[k]? = some b → ∃ type rule, (openTele.go mk i tele ⟨Γ, ids, env⟩).Γ[Γ.length + k]? =
        some { mk b (i + k) { type, rule, erased := b.mult == .erased } with type, rule }
  | [], _, _, _, _, _, _, hb => by simp at hb
  | b :: bs, i, Γ, ids, env, 0, b', hb => by
    cases hb
    simp only [openTele.go]
    refine ⟨b.type.subst env, b.is.map fun e => (e.subst env).canon Γ, ?_⟩
    rw [Nat.add_zero, openTele.go_prefix_getElem mk bs _ _ _ _ _ (by simp)]
    simp
  | b :: bs, i, Γ, ids, env, k + 1, b', hb => by
    simp only [openTele.go]
    obtain ⟨type, rule, h⟩ := openTele.go_getElem mk bs (i + 1) _ (ids ++ [Γ.length]) (env ++ [.entry Γ.length]) k b'
      (by simpa using hb)
    refine ⟨type, rule, ?_⟩
    rw [show Γ.length + (k + 1) = (Γ ++ [_]).length + k by simp; omega, show i + (k + 1) = i + 1 + k by omega]
    exact h

/-- What `opened` returns, independently of any valuation: the fresh entries of the telescope, as results, tainted
and erased as `taint` and the binders' multiplicities say. -/
theorem opened_shape (sc : Scope) (tele : Telescope) (env : List Term) (kind : String) (pos : Pos)
    (taint : Nat → Bool) :
    sc.Γ <+: (opened sc tele env kind pos taint).1.Γ ∧
      (opened sc tele env kind pos taint).1.Γ.length = sc.Γ.length + tele.length ∧
      (opened sc tele env kind pos taint).2.length = tele.length ∧
      ∀ (i : Nat) (b : TBinder), tele[i]? = some b →
        (opened sc tele env kind pos taint).2[i]? = some ⟨.entry (sc.Γ.length + i), taint i, b.mult == .erased⟩ ∧
        ∃ en, (opened sc tele env kind pos taint).1.Γ[sc.Γ.length + i]? = some en ∧ en.tainted = taint i ∧
          en.erased = (b.mult == .erased) := by
  let mk : TBinder → Nat → Entry → Entry := fun b i en =>
    { en with origin := s!"{kind}.{b.name.getD (toString (i + 1))}@{pos}", tainted := taint i }
  have hop : opened sc tele env kind pos taint = ({ sc with Γ := (openTele sc.Γ tele env mk).Γ },
      (openTele sc.Γ tele env mk).ids.mapIdx fun i id =>
        ⟨.entry id, taint i, (((openTele sc.Γ tele env mk).Γ[id]?).map (·.erased)).getD false⟩) := rfl
  rw [hop]
  obtain ⟨Δ, hΔ, hΔl, hids, -⟩ := openTele_shape sc.Γ tele env mk
  have hent : ∀ (i : Nat) (b : TBinder), tele[i]? = some b → ∃ en,
      (openTele sc.Γ tele env mk).Γ[sc.Γ.length + i]? = some en ∧ en.tainted = taint i ∧
        en.erased = (b.mult == .erased) := fun i b hb => by
    obtain ⟨type, rule, h⟩ := openTele.go_getElem mk tele 0 sc.Γ [] env i b hb
    exact ⟨_, h, by simp [mk], by simp [mk]⟩
  refine ⟨by rw [hΔ]; exact List.prefix_append _ _, by rw [hΔ, List.length_append, hΔl], by simp [hids],
    fun i b hb => ⟨?_, hent i b hb⟩⟩
  have hi : i < tele.length := (List.getElem?_eq_some_iff.1 hb).1
  obtain ⟨en, hen, -, her⟩ := hent i b hb
  simp [hids, List.getElem?_range' hi, hen, her]

/-- Opening a telescope to entries whose values meet it, the untainted ones typed: the scope stays satisfied, and
the results are the new entries, taking those values. -/
theorem opened_sound {Sc : Sigs} {sc : Scope} {tele : Telescope} {env : List Term} {kind : String} {pos : Pos}
    {taint : Nat → Bool} {ρ envv vs : List Value} (hΓ : Sat Sc sc.Γ ρ)
    (henv : Term.evalList ρ [] env = some envv) (ht : TeleOk Sc ρ (fun k => !taint k) tele envv vs) :
    Sat Sc (opened sc tele env kind pos taint).1.Γ (ρ ++ vs) ∧
      Term.evalList (ρ ++ vs) [] ((opened sc tele env kind pos taint).2.map (·.term)) = some vs := by
  let mk : TBinder → Nat → Entry → Entry := fun b i en =>
    { en with origin := s!"{kind}.{b.name.getD (toString (i + 1))}@{pos}", tainted := taint i }
  have hop : opened sc tele env kind pos taint = ({ sc with Γ := (openTele sc.Γ tele env mk).Γ },
      (openTele sc.Γ tele env mk).ids.mapIdx fun i id =>
        ⟨.entry id, taint i, (((openTele sc.Γ tele env mk).Γ[id]?).map (·.erased)).getD false⟩) := rfl
  rw [hop]
  obtain ⟨hs, he⟩ := openTele_sound mk taint (fun _ _ _ _ => rfl) hΓ henv ht
  obtain ⟨Δ, hΔ, hΔl, hids, henv'⟩ := openTele_shape sc.Γ tele env mk
  have hmap : (((openTele sc.Γ tele env mk).ids.mapIdx fun i id =>
        (⟨.entry id, taint i, (((openTele sc.Γ tele env mk).Γ[id]?).map (·.erased)).getD false⟩ : Res)).map
          (·.term)) = (openTele sc.Γ tele env mk).ids.map .entry :=
    List.ext_getElem (by simp) fun i h₁ h₂ => by simp [List.getElem_mapIdx]
  refine ⟨hs, ?_⟩
  rw [hmap]
  rw [henv'] at he
  obtain ⟨a, b, ha, hb, hab⟩ := Term.evalList_append_iff.1 he
  have : a = envv := by
    have h₁ := Term.evalList_frame_ρ vs henv
    rw [ha] at h₁; exact Option.some.inj h₁
  subst this
  obtain rfl := List.append_cancel_left hab
  exact hb

/-- The names `bind` and `bindIds` push, newest first. -/
def pushed {α : Type} (ids : List Id) (xs : List α) : List (String × α) :=
  ((ids.zip xs).filterMap fun (i, x) => i.name.map (·, x)).reverse

theorem pushed_cons {α : Type} (x : Id) (ids : List Id) (a : α) (xs : List α) :
    pushed (x :: ids) (a :: xs) = pushed ids xs ++ (x.name.map (·, a)).toList := by
  cases h : x.name <;> simp [pushed, h]

theorem Scope.bind_eq : ∀ (sc : Scope) (ids : List Id) (rs : List Res),
    sc.bind ids rs = { sc with names := pushed ids rs ++ sc.names }
  | sc, x :: xs, r :: rs => by
    rw [Scope.bind, Scope.bind_eq _ xs rs, pushed_cons]
    cases x.name <;> simp
  | sc, [], _ => by simp [Scope.bind, pushed]
  | sc, _ :: _, [] => by simp [Scope.bind, pushed]

theorem bindIds_ok {env : Env} {ids : List Id} {vs : List Value} {env' : Env} (h : bindIds env ids vs = .ok env') :
    ids.length = vs.length ∧ env' = pushed ids vs ++ env := by
  unfold bindIds at h
  split at h
  · cases h; exact ⟨‹_›, rfl⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem bindIds_of_length {env : Env} {ids : List Id} {vs : List Value} (h : ids.length = vs.length) :
    bindIds env ids vs = .ok (pushed ids vs ++ env) := by
  simp [bindIds, h, pushed, pure, Except.pure]

theorem bindPattern_app {env : Env} {pat : Pattern} {h : Head} {ws : List Value} {env' : Env} :
    bindPattern env none pat (.app h ws) = .ok env' ↔
      h.name = pat.ctor.name ∧ bindIds env pat.fields ws = .ok env' := by
  simp only [bindPattern, destruct]
  by_cases hn : h.name = pat.ctor.name
  · simp [hn, pure, Except.pure, bind, Except.bind]
  · simp [hn, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem lookup_append {α : Type} (l l' : List (String × α)) (n : String) :
    (l ++ l').lookup n = (l.lookup n).or (l'.lookup n) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨k, a⟩ := p
    simp only [List.cons_append, List.lookup]
    split <;> simp_all

/-- Looking a name up after pushing names for two lists of the same length finds entries at the same position, or
falls through to what was there before in both. -/
theorem lookup_pushed₂ {α β : Type} (R : α → β → Prop) : ∀ (ids : List Id) (xs : List α) (ys : List β)
    (l : List (String × α)) (l' : List (String × β)), ids.length = xs.length → xs.length = ys.length →
    (∀ (i : Nat) (x : α) (y : β), xs[i]? = some x → ys[i]? = some y → R x y) →
    ∀ n x, (pushed ids xs ++ l).lookup n = some x →
      (∃ y, (pushed ids ys ++ l').lookup n = some y ∧ R x y) ∨
        (l.lookup n = some x ∧ (pushed ids ys ++ l').lookup n = l'.lookup n)
  | [], xs, ys, l, l', _, _, _, n, x, h => .inr ⟨by simpa [pushed] using h, by simp [pushed]⟩
  | i :: ids, a :: xs, b :: ys, l, l', h1, h2, hR, n, x, h => by
    rw [pushed_cons, List.append_assoc] at h
    rw [pushed_cons, List.append_assoc]
    rcases lookup_pushed₂ R ids xs ys _ _ (by simpa using h1) (by simpa using h2)
      (fun k x y hx hy => hR (k + 1) x y (by simpa using hx) (by simpa using hy)) n x h with h' | ⟨h', h''⟩
    · exact .inl h'
    · rw [h'']
      rw [lookup_append] at h'
      cases hn : i.name with
      | none =>
        simp only [hn, Option.map_none, Option.toList_none, List.lookup, Option.none_or, List.nil_append] at h' ⊢
        exact .inr ⟨h', by simp⟩
      | some m =>
        by_cases hnm : n = m
        · subst hnm
          simp only [hn, Option.map_some, Option.toList_some, List.lookup, beq_self_eq_true, Option.some_or,
            List.singleton_append] at h' ⊢
          cases h'
          exact .inl ⟨b, rfl, hR 0 _ _ rfl rfl⟩
        · have hb : (n == m) = false := by simpa using hnm
          simp only [hn, Option.map_some, Option.toList_some, List.lookup, hb, Option.none_or,
            List.singleton_append] at h' ⊢
          exact .inr ⟨h', by simp⟩
  | _ :: _, [], _, _, _, h1, _, _, _, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, _, h2, _, _, _, _ => by simp at h2

theorem pushed_mem : ∀ {α : Type} {ids : List Id} {rs : List α} {p : String × α}, p ∈ pushed ids rs →
    ∃ i : Nat, rs[i]? = some p.2 := by
  intro α ids rs p hp
  simp only [pushed, List.mem_reverse, List.mem_filterMap, Option.map_eq_some_iff] at hp
  obtain ⟨⟨i, r⟩, hm, n, -, rfl⟩ := hp
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem (List.of_mem_zip hm).2
  exact ⟨k, by rw [List.getElem?_eq_getElem hk, he]⟩

theorem lookup_mem {α : Type} {n : String} {r : α} : ∀ {l : List (String × α)}, l.lookup n = some r → (n, r) ∈ l
  | [], h => by simp at h
  | (k, b) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk; cases h; simp at hk; subst hk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem Inv.length {C : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    (hI : Inv C sc n0 W ρ act) : n0 ≤ ρ.length := by
  have := congrArg List.length hI.agree
  simp only [List.length_take] at this
  have := hI.n0_world
  omega

theorem Inv.sigsClose {C : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    (hI : Inv C sc n0 W ρ act) (ρ' : List Value) : SigsClose sc.sigs (ρ ++ ρ') W.Sc :=
  hI.sigs _ (by rw [List.take_append_of_le_length hI.length]; exact hI.agree)

/-- The invariant carries over to an untainted scope with more entries, the same names and signatures, satisfied by
an extension of the valuation. -/
theorem Inv.extend {C : Ctx} {sc sc' : Scope} {n0 : Nat} {W : World} {ρ ρ' : List Value} {act : Act}
    (hI : Inv C sc n0 W ρ act) (hsat : Sat W.Sc sc'.Γ (ρ ++ ρ')) (hsigs : sc'.sigs = sc.sigs)
    (hnames : sc'.names = sc.names) (hh : sc'.holes = []) (ht : sc'.taintedBy = none) :
    Inv C sc' n0 W (ρ ++ ρ') act := by
  have hl := hI.length
  refine ⟨hh, ht, hsat, hI.n0_world, by rw [List.take_append_of_le_length hl]; exact hI.agree,
    hsigs ▸ hI.sigs, hsigs ▸ hI.sigsOk, hI.noJunk, fun n r h => ?_, hsigs ▸ hI.globals, fun f hf => ?_, hI.solving,
    hI.typeHeads⟩
  · have h' : sc.lookup n = some r := by simpa [Scope.lookup, hnames] using h
    obtain ⟨v, h1, h2⟩ := hI.names n r h'
    exact ⟨v, Term.eval_frame_ρ ρ' h1, h2⟩
  · obtain ⟨ss, h1, h2⟩ := hI.act f hf
    exact ⟨ss, Term.evalList_frame_ρ ρ' h1, h2⟩

/-- The invariant carries over to a scope with names pushed for results with ideal values, typed where the result
is untainted. -/
theorem Inv.bind {C : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    {ids : List Id} {rs : List Res} {vs : List Value} (hI : Inv C sc n0 W ρ act)
    (hvs : Term.evalList ρ [] (rs.map (·.term)) = some vs)
    (hty : ∀ (i : Nat) (r : Res) (v : Value), rs[i]? = some r → vs[i]? = some v → ResOk W.Sc r v) :
    Inv C (sc.bind ids rs) n0 W ρ act := by
  rw [Scope.bind_eq]
  refine ⟨hI.holes, hI.untainted, hI.sat, hI.n0_world, hI.agree, hI.sigs, hI.sigsOk, hI.noJunk, ?_, hI.globals,
    hI.act, hI.solving, hI.typeHeads⟩
  intro n r h
  simp only [Scope.lookup, lookup_append] at h
  cases hp : (pushed ids rs).lookup n with
  | none => rw [hp, Option.none_or] at h; exact hI.names n r h
  | some r' =>
    rw [hp, Option.some_or, Option.some.injEq] at h
    subst h
    obtain ⟨i, hi⟩ := pushed_mem (lookup_mem hp)
    have hx := (Term.evalList_eq_some_iff.1 hvs).2 i r'.term (by simp [hi])
    obtain ⟨v, hv⟩ : ∃ v, vs[i]? = some v := by
      have hl := Term.length_evalList hvs
      have : i < vs.length := by rw [hl, List.length_map]; exact (List.getElem?_eq_some_iff.1 hi).1
      exact ⟨_, List.getElem?_eq_getElem this⟩
    exact ⟨v, by rw [hx, hv], hty i r' v hi hv⟩

/-- The run-time environment stays related after pushing the names of results with run-time values related to
their ideal values. -/
theorem EnvRel.bind {S : Sigs} {phase : Nat} {sc : Scope} {ρ : List Value} {env : Env} {ids : List Id}
    {rs : List Res} {us : List Value} (h : EnvRel S phase sc ρ env) (hl : ids.length = rs.length)
    (hlu : rs.length = us.length)
    (hR : ∀ (i : Nat) (r : Res) (a : Value), rs[i]? = some r → us[i]? = some a → r.tainted = false →
      ∃ v, r.term.eval ρ [] = some v ∧ MultRel S phase (sc.multOf r) a v) :
    EnvRel S phase (sc.bind ids rs) ρ (pushed ids us ++ env) := by
  intro n r hn ht
  rw [Scope.bind_eq] at hn
  have hmult : (sc.bind ids rs).multOf r = sc.multOf r := by rw [Scope.bind_eq]; rfl
  simp only [Scope.lookup] at hn
  rcases lookup_pushed₂ (fun r a => r.tainted = false → ∃ v, r.term.eval ρ [] = some v ∧
      MultRel S phase (sc.multOf r) a v) ids rs us sc.names env hl hlu (fun i r a hr ha => hR i r a hr ha) n r hn with
    ⟨a, ha, hra⟩ | ⟨h1, h2⟩
  · obtain ⟨v, hv, hm⟩ := hra ht
    exact ⟨a, v, ha, hv, by rw [hmult]; exact hm⟩
  · obtain ⟨a, v, ha, hv, hm⟩ := h n r h1 ht
    exact ⟨a, v, by rw [h2]; exact ha, hv, by rw [hmult]; exact hm⟩

theorem forM_ok {α ε : Type} {f : α → Except ε Unit} : ∀ {l : List α}, l.forM f = .ok () → ∀ x ∈ l, f x = .ok ()
  | [], _, _, hx => by cases hx
  | a :: l, h, x, hx => by
    rw [List.forM] at h
    obtain ⟨u, hu, h⟩ := bind_eq_ok.1 h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hu
    · exact forM_ok h x hx

theorem marks_spec {pos : Pos} {args : List Arg} {name : String} {sig : FnSig} {fn : FnCtx} {subs : List Nat}
    {k : Nat} (h : marks pos args name sig fn = .ok (subs, k)) :
    subs = (List.range sig.subterm.length).filter (sig.subterm.getD · false) ∧ k < subs.length ∧
      k < fn.subterms.length := by
  unfold marks at h
  simp only at h
  split at h
  · rename_i k' hk
    simp only [pure, Except.pure, bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · simp [failAt_eq] at h
      · rename_i hlt
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_, by omega⟩
        obtain ⟨i, -, hi⟩ := Option.bind_eq_some_iff.1 hk
        exact (List.idxOf?_eq_some_iff.1 hi).1
  · simp [failAt_eq, bind, Except.bind] at h

theorem decrease_spec {sc : Scope} {pos : Pos} {args : List Arg} {rs : List Res} {fn : FnCtx} {subs : List Nat}
    {k : Nat} (h : decrease sc pos args rs fn subs k = .ok ()) :
    ∀ j ≤ k, ∃ p r own, subs[j]? = some p ∧ rs[p]? = some r ∧ fn.subterms[j]? = some own ∧
      (if j = k then isStrictSubterm sc.Γ r.term own else identical sc.Γ r.term own) = true := by
  intro j hj
  have := forM_ok h j (List.mem_range.2 (by omega))
  cases hp : subs[j]? with
  | none => simp [hp, internal, failAt_eq] at this
  | some p =>
    cases hr : rs[p]? with
    | none => simp [hp, hr, internal, failAt_eq] at this
    | some r =>
      cases ho : fn.subterms[j]? with
      | none => simp [hp, hr, ho, internal, failAt_eq] at this
      | some own =>
        refine ⟨p, r, own, rfl, hr, rfl, ?_⟩
        simp only [hp, hr, ho] at this
        cases hc : (if j = k then isStrictSubterm sc.Γ r.term own else identical sc.Γ r.term own)
        · simp [hc, failAt_eq] at this
        · rfl

theorem filterMap_flags : ∀ (flags : List Bool) (vs : List Value), flags.length = vs.length →
    (flags.zip vs).filterMap (fun (b, v) => if b then some (some v) else none) =
      ((List.range flags.length).filter (flags.getD · false)).map (fun i => vs[i]?)
  | [], [], _ => rfl
  | b :: fl, v :: vl, h => by
    have ih := filterMap_flags fl vl (by simpa using h)
    have e : ((fun i => (b :: fl).getD i false) ∘ Nat.succ) = fun i => fl.getD i false := by
      funext i; simp
    rw [List.zip_cons_cons, List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map, e]
    cases b <;> simp [ih, Function.comp_def]

theorem filterMap_flags_length : ∀ (flags : List Bool) (vs : List Value),
    ((flags.zip vs).filterMap (fun (b, v) => if b then some (some v) else none)).length ≤ flags.count true
  | [], _ => by simp
  | _ :: _, [] => by simp
  | b :: fl, v :: vl => by
    have := filterMap_flags_length fl vl
    cases b <;> simp <;> omega

theorem calleeAct_subs (d : FnDef) (vs : List Value) (hl : d.subterm.length = vs.length)
    (hc : d.subterm.count true ≤ d.pad) :
    (calleeAct d vs).subs = ((List.range d.subterm.length).filter (d.subterm.getD · false)).map (fun i => vs[i]?) ++
      List.replicate (d.pad - ((List.range d.subterm.length).filter (d.subterm.getD · false)).length) none ∧
    (calleeAct d vs).subs.length = d.pad ∧ (calleeAct d vs).group = d.group := by
  have h1 := filterMap_flags d.subterm vs hl
  have h2 := filterMap_flags_length d.subterm vs
  rw [h1, List.length_map] at h2
  refine ⟨?_, ?_, rfl⟩
  · simp only [calleeAct]; rw [h1, List.length_map]
  · simp only [calleeAct]; rw [h1, List.length_append, List.length_map, List.length_replicate]; omega

/-- A call within the group whose marks and decrease checked has a measure below the caller's activation. -/
theorem call_lt {sc : Scope} {pos : Pos} {args : List Arg} {name : String} {sig : FnSig} {fn : FnCtx}
    {rs : List Res} {subs : List Nat} {k : Nat} {d : FnDef} {act : Act} {ρ vs ss : List Value}
    (hΓ : RulesHold sc.Γ ρ) (hm : marks pos args name sig fn = .ok (subs, k))
    (hd : decrease sc pos args rs fn subs k = .ok ()) (hrs : Term.evalList ρ [] (rs.map (·.term)) = some vs)
    (hss : Term.evalList ρ [] fn.subterms = some ss)
    (hact : act.subs = ss.map some ++ List.replicate (act.subs.length - ss.length) none)
    (hsub : d.subterm = sig.subterm) (hlen : sig.subterm.length = vs.length) (hcount : d.subterm.count true ≤ d.pad)
    (hg : d.group = act.group) (hpad : d.pad = act.subs.length) : Act.lt (calleeAct d vs) act := by
  obtain ⟨hsubs, hk, hkf⟩ := marks_spec hm
  have hdec := decrease_spec hd
  obtain ⟨hcs, hcl, hcg⟩ := calleeAct_subs d vs (hsub ▸ hlen) hcount
  rw [hsub, ← hsubs] at hcs
  have hssl : ss.length = fn.subterms.length := Term.length_evalList hss
  have hvs : ∀ j ≤ k, ∃ p x y, subs[j]? = some p ∧ vs[p]? = some x ∧ ss[j]? = some y ∧
      (if j = k then x.StrictSub y else x = y) := by
    intro j hj
    obtain ⟨p, r, own, hp, hr, ho, hc⟩ := hdec j hj
    have hx := (Term.evalList_eq_some_iff.1 hrs).2
    obtain ⟨x, hxv⟩ : ∃ x, vs[p]? = some x := by
      have : p < vs.length := by
        rw [Term.length_evalList hrs, List.length_map]; exact (List.getElem?_eq_some_iff.1 hr).1
      exact ⟨_, List.getElem?_eq_getElem this⟩
    obtain ⟨y, hyv⟩ : ∃ y, ss[j]? = some y := by
      have : j < ss.length := by rw [hssl]; exact (List.getElem?_eq_some_iff.1 ho).1
      exact ⟨_, List.getElem?_eq_getElem this⟩
    have hrx : r.term.eval ρ [] = some x := by
      rw [hx p r.term (by simp [hr])]; exact hxv
    have hoy : own.eval ρ [] = some y := by
      rw [(Term.evalList_eq_some_iff.1 hss).2 j own ho]; exact hyv
    refine ⟨p, x, y, hp, hxv, hyv, ?_⟩
    split
    · rename_i hjk
      simp only [hjk, ↓reduceIte] at hc
      exact isStrictSubterm_sound hΓ hc hrx hoy
    · rename_i hjk
      simp only [hjk, ↓reduceIte] at hc
      exact Option.some.inj (hrx.symm.trans ((identical.eval_eq hΓ hc).trans hoy))
  have hca : ∀ j, j < subs.length → (calleeAct d vs).subs[j]? = some (subs[j]?.bind fun i => vs[i]?) := by
    intro j hj
    rw [hcs, List.getElem?_append_left (by simpa using hj)]
    simp [List.getElem?_eq_getElem hj]
  have hac : ∀ j, j < ss.length → act.subs[j]? = some (ss[j]?) := by
    intro j hj
    rw [hact, List.getElem?_append_left (by simpa using hj)]
    simp [List.getElem?_eq_getElem hj]
  obtain ⟨p, x, y, hp, hx, hy, hxy⟩ := hvs k (Nat.le_refl k)
  simp only [↓reduceIte] at hxy
  refine Act.lt_of_subs (k := k) (x := x) (y := y) (hcg.trans hg) (hcl.trans hpad) ?_ ?_ ?_ hxy.lt
  · apply List.ext_getElem?
    intro j
    simp only [List.getElem?_take]
    split
    · rename_i hj
      obtain ⟨p', x', y', hp', hx', hy', hxy'⟩ := hvs j (by omega)
      simp only [show j ≠ k by omega, ↓reduceIte] at hxy'
      rw [hca j (by omega), hac j (by omega), hp', Option.bind_some, hx', hy', hxy']
    · rfl
  · rw [hca k hk, hp, Option.bind_some, hx]
  · rw [hac k (by omega), hy]


theorem mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' → l'.length = l.length ∧ ∀ (i : Nat) a b, l[i]? = some a →
      l'[i]? = some b → f a = .ok b
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, by simp⟩
  | a :: l, l', h => by
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_eq_ok.1 h
    obtain ⟨bs, hbs, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hl, hi⟩ := mapM_ok hbs
    refine ⟨by simp [hl], fun i a' b' ha hb' => ?_⟩
    cases i with
    | zero => simp at ha hb'; subst ha hb'; exact hb
    | succ i => exact hi i a' b' (by simpa using ha) (by simpa using hb')

theorem Scope.sig_ok {sc : Scope} {pos : Pos} {h : Head} {sig : Sig} (hs : sc.sig pos h = .ok sig) :
    sc.sigs.find h = some sig := by
  unfold Scope.sig at hs
  split at hs
  · cases hs; assumption
  · simp [internal, failAt_eq] at hs

theorem Scope.typeOf_ok {sc : Scope} {pos : Pos} {t ty : Term} (h : sc.typeOf pos t = .ok ty) :
    Pledge.typeOf sc.sigs sc.Γ t = some ty := by
  unfold Scope.typeOf at h
  split at h
  · cases h; assumption
  · simp [internal, failAt_eq] at h

/-- The value constructors `dataCtors` lists are those of the data type that heads the scrutinee's type. -/
theorem dataCtors_spec {C : Ctx} {sc : Scope} {t : Term} {pos : Pos} {ctors : List (String × Sig)}
    (h : dataCtors C sc t pos = .ok ctors) :
    ∃ ty hd args T cs, typeOf sc.sigs sc.Γ t = some ty ∧ ty.canon sc.Γ = .app hd args ∧
      C.global hd.name = some (.type T (some cs) true) ∧ ctors.map (·.1) = cs ∧
      ∀ c sig, (c, sig) ∈ ctors → sc.sigs.find ⟨.ctor, c⟩ = some sig := by
  unfold dataCtors at h
  obtain ⟨ty, hty, h⟩ := bind_eq_ok.1 h
  simp only at h
  split at h
  · rename_i hd args hcanon
    split at h
    · rename_i T cs hg
      obtain ⟨hl, hi⟩ := mapM_ok h
      refine ⟨ty, hd, args, T, cs, Scope.typeOf_ok hty, hcanon, hg, ?_, fun c sig hm => ?_⟩
      · apply List.ext_getElem?
        intro i
        rw [List.getElem?_map]
        cases hc : cs[i]? with
        | none =>
          have : ctors[i]? = none := by
            rw [List.getElem?_eq_none_iff] at hc ⊢; omega
          simp [this]
        | some c =>
          obtain ⟨p, hp⟩ : ∃ p, ctors[i]? = some p := by
            have : i < ctors.length := by rw [hl]; exact (List.getElem?_eq_some_iff.1 hc).1
            exact ⟨_, List.getElem?_eq_getElem this⟩
          have := hi i c p hc hp
          obtain ⟨s, hs, hpe⟩ := bind_eq_ok.1 this
          simp only [pure, Except.pure, Except.ok.injEq] at hpe
          simp [hp, ← hpe]
      · obtain ⟨i, hi', hm⟩ := List.getElem_of_mem hm
        obtain ⟨c', hc'⟩ : ∃ c', cs[i]? = some c' := by
          have : i < cs.length := by rw [← hl]; exact hi'
          exact ⟨_, List.getElem?_eq_getElem this⟩
        have := hi i c' _ hc' (by rw [List.getElem?_eq_getElem hi', hm])
        obtain ⟨s, hs, hpe⟩ := bind_eq_ok.1 this
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hpe
        obtain ⟨rfl, rfl⟩ := hpe
        exact Scope.sig_ok hs
    all_goals simp [failAt_eq] at h
  · simp [failAt_eq] at h


theorem foldlM_ok {α β ε : Type} {f : β → α → Except ε β} :
    ∀ {l : List α} {init r : β}, l.foldlM f init = .ok r → ∀ x ∈ l, ∃ s r', f s x = .ok r'
  | [], _, _, _, x, hx => by cases hx
  | a :: l, init, r, h, x, hx => by
    simp only [List.foldlM_cons] at h
    obtain ⟨s, hs, h⟩ := bind_eq_ok.1 h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨init, s, hs⟩
    · exact foldlM_ok h x hx

/-- What `forcings` returns: one forcing per value constructor of the scrutinee's data type, none stuck, and the
patterns name value constructors of it with their numbers of fields. -/
theorem forcings_spec {C : Ctx} {sc : Scope} {t : Term} {sp at_ : Pos} {pats : List Pattern} {erased : Bool}
    {fs : List Forcing} (h : forcings C sc t sp pats at_ erased = .ok fs) :
    ∃ ctors, dataCtors C sc t sp = .ok ctors ∧
      (∀ p ∈ pats, ∃ sig, (p.ctor.name, sig) ∈ ctors ∧ p.fields.length = sig.params.length) ∧
      fs.length = ctors.length ∧ ∀ (i : Nat) f, fs[i]? = some f → ∃ sig mk, ctors[i]? = some (f.name, sig) ∧
        f.forced = force sc.sigs sc.Γ t sig mk ∧
        (∀ b k en, (mk b k en).tainted = en.tainted ∧ (mk b k en).erased = (en.erased || erased)) ∧
        (∀ msg, f.forced ≠ .stuck msg) ∧
        f.pat = pats.find? (·.ctor.name == f.name) := by
  unfold forcings at h
  obtain ⟨ctors, hc, h⟩ := bind_eq_ok.1 h
  obtain ⟨seen, hseen, h⟩ := bind_eq_ok.1 h
  obtain ⟨hl, hi⟩ := mapM_ok h
  refine ⟨ctors, hc, fun p hp => ?_, hl, fun i f hf => ?_⟩
  · obtain ⟨s, r', hs⟩ := foldlM_ok hseen p hp
    simp only at hs
    split at hs
    · rename_i n0 sig hfind
      split at hs
      · simp [failAt_eq, bind, Except.bind] at hs
      split at hs
      · simp [failAt_eq, bind, Except.bind] at hs
      rename_i hne
      refine ⟨sig, ?_, by simpa using hne⟩
      have := List.find?_some hfind
      have hm := List.mem_of_find?_eq_some hfind
      simp only [beq_iff_eq] at this
      rw [this] at hm
      exact hm
    · simp [failAt_eq] at hs
  · obtain ⟨⟨n, sig⟩, hp⟩ : ∃ p, ctors[i]? = some p := by
      have : i < ctors.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hf).1
      exact ⟨_, List.getElem?_eq_getElem this⟩
    have := hi i _ f hp hf
    simp only at this
    split at this
    · simp [internal, failAt_eq] at this
    · rename_i hns
      simp only [pure, Except.pure, Except.ok.injEq] at this
      subst this
      exact ⟨sig, _, hp, rfl, fun b k en => ⟨rfl, rfl⟩, fun msg hm => hns msg hm, rfl⟩


theorem GlobalsOk.fn {n0 phase : Nat} {gs : List Global} {fn : Option FnCtx} {S : Sigs} {W : World} {act : Act}
    {n m : String} {sig : FnSig} (h : GlobalsOk n0 phase gs fn S W act)
    (hg : gs.find? (·.name == n) = some (.fn m (some sig))) :
    FnOk n0 phase W fn act n sig := h n _ hg

theorem GlobalsOk.type {n0 phase : Nat} {gs : List Global} {fn : Option FnCtx} {S : Sigs} {W : World} {act : Act}
    {n T : String} {cs : Option (List String)} {done : Bool} (h : GlobalsOk n0 phase gs fn S W act)
    (hg : gs.find? (·.name == n) = some (.type T cs done)) :
    HeadOk S W .type n ∧ ∀ cs', cs = some cs' → done = true →
      n ≠ "Type" ∧ (∃ s, W.Sc.find ⟨.type, n⟩ = some s) ∧ Complete W n cs' ∧
      ∀ c ∈ cs', gs.find? (·.name == c) = some (.ctor c) := h n _ hg

theorem GlobalsOk.ctor {n0 phase : Nat} {gs : List Global} {fn : Option FnCtx} {S : Sigs} {W : World} {act : Act}
    {n m : String} (h : GlobalsOk n0 phase gs fn S W act) (hg : gs.find? (·.name == n) = some (.ctor m)) :
    HeadOk S W .ctor n := h n _ hg

theorem Ctx.global_name {C : Ctx} {n : String} {g : Global} (h : C.global n = some g) : g.name = n := by
  simpa using List.find?_some h

/-- At a `match` or pattern `let` whose scrutinee has a typed value (an untainted one, §12), that value is an
application of a value constructor of the scrutinee's data type, whose forcing survived; the scope it gave is
satisfied by the valuation extended by the value's arguments, and the fields' entries are untainted, erased when
the field or the match is (§16). -/
theorem forcings_value {C : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    {t : Term} {sp at_ : Pos} {pats : List Pattern} {erased : Bool} {fs : List Forcing} {v V : Value}
    (hI : Inv C sc n0 W ρ act) (h : forcings C sc t sp pats at_ erased = .ok fs)
    (ht : t.eval ρ [] = some v) (hv : HasType W.Sc v V) :
    ∃ c ws sig Γ' ids pat, v = .app ⟨.ctor, c⟩ ws ∧ fs.find? (·.name == c) = some ⟨c, .ok Γ' ids, pat⟩ ∧
      sc.sigs.find ⟨.ctor, c⟩ = some sig ∧ TeleSat W.Sc ρ sig.params [] ws ∧ Sat W.Sc Γ' (ρ ++ ws) ∧
      sc.Γ.eraseRules <+: Γ'.eraseRules ∧ Γ'.length = sc.Γ.length + ws.length ∧
      ids = List.range' sc.Γ.length ws.length ∧ pat = pats.find? (·.ctor.name == c) ∧
      ∀ (k : Nat) (b : TBinder), sig.params[k]? = some b → ∃ en, Γ'[sc.Γ.length + k]? = some en ∧
        en.tainted = false ∧ en.erased = (b.mult == .erased || erased) := by
  obtain ⟨ctors, hc, -, hl, hfs⟩ := forcings_spec h
  obtain ⟨ty, hd, args, T, cs, hty, hcanon, hg, hcs, hsigs⟩ := dataCtors_spec hc
  have hS := hI.sigs ρ hI.agree
  have hV := typeOf_sound hI.sat.1 hS hI.noJunk ht hv hty
  rw [← hI.sat.eval_canon, hcanon] at hV
  obtain ⟨us, -, rfl⟩ := Term.eval_app.1 hV
  obtain ⟨-, -, hcomp, -⟩ := (hI.globals.type hg).2 cs rfl rfl
  obtain ⟨h', ws, sig', rfl, hfind, -, hret⟩ := hv.inv
  obtain ⟨hk, hmem⟩ := hcomp h' sig' ws hd us hfind hret rfl
  obtain ⟨k, c⟩ := h'
  simp only at hk hmem
  subst hk
  rw [← hcs] at hmem
  obtain ⟨⟨c', sig⟩, hmem', hcc⟩ := List.mem_map.1 hmem
  simp only at hcc
  subst c'
  have hsig := hsigs _ _ hmem'
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hmem'
  obtain ⟨f, hf⟩ : ∃ f, fs[i]? = some f := ⟨fs[i]'(hl ▸ hi), by simp⟩
  obtain ⟨sig₁, mk₁, hc₁, -, -, -, -⟩ := hfs i f hf
  rw [List.getElem?_eq_getElem hi, hci] at hc₁
  have hfc : f.name = c := (congrArg Prod.fst (Option.some.inj hc₁)).symm
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, fs.find? (·.name == c) = some f₀ :=
    Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨f, List.mem_of_getElem? hf, by simp [hfc]⟩)
  have hn₀ : f₀.name = c := by simpa using List.find?_some hf₀
  obtain ⟨j, hj, hj'⟩ := List.getElem_of_mem (List.mem_of_find?_eq_some hf₀)
  obtain ⟨sig₀, mk₀, hc₀, hforce, hmk₀, hstuck, hpat⟩ := hfs j f₀ (by rw [List.getElem?_eq_getElem hj, hj'])
  have hsig₀ := hsigs _ _ (List.mem_of_getElem? hc₀)
  rw [hn₀, hsig] at hsig₀
  obtain rfl := Option.some.inj hsig₀
  have hhead : sig.head = ⟨.ctor, c⟩ := Sigs.find_head hsig
  have hgood := force_good mk₀ (fun b k en hen => (hmk₀ b k en).1.trans hen) hI.sat hS (hI.sigsClose ws) hI.noJunk
    (scrut := t) (ctor := sig) (by rw [hhead]; exact ht) (by rw [hhead]; exact hsig) (by rw [hhead]; exact hv)
  obtain ⟨n₀, forced, pat⟩ := f₀
  simp only at hn₀ hforce hstuck hpat
  subst hn₀
  rw [← hforce] at hgood
  cases forced with
  | ok Γ' ids =>
    obtain ⟨hsat, hero, hpre, hlen, hids, -⟩ := hgood
    refine ⟨n₀, ws, sig, Γ', ids, pat, rfl, hf₀, hsig, ((hS.hasType_app_iff hsig).1 hv).1, hsat, hpre, hlen, hids,
      hpat, fun k b hb => ?_⟩
    obtain ⟨type, rule, hk⟩ := openTele.go_getElem mk₀ sig.params 0 sc.Γ [] [] k b hb
    have h1 := congrArg (·[sc.Γ.length + k]?) hero
    simp only [Entries.eraseRules, List.getElem?_map] at h1
    change Option.map _ Γ'[sc.Γ.length + k]? = Option.map _ (openTele.go mk₀ 0 sig.params ⟨sc.Γ, [], []⟩).Γ[sc.Γ.length + k]? at h1
    rw [hk] at h1
    cases hen : Γ'[sc.Γ.length + k]? with
    | none => rw [hen] at h1; cases h1
    | some en =>
      rw [hen] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      have ht' := congrArg Entry.tainted h1
      have he' := congrArg Entry.erased h1
      simp only at ht' he'
      exact ⟨en, rfl, by rw [ht', (hmk₀ _ _ _).1], by rw [he', (hmk₀ _ _ _).2]⟩
  | refuted => exact hgood.elim
  | stuck msg => exact (hstuck msg rfl).elim

theorem survivor_spec {sc : Scope} {fs : List Forcing} {n : String} {pos : Pos} {cons : String} {Γ : Entries}
    {ids : List Nat} (h : survivor sc fs n pos cons = .ok (Γ, ids)) :
    ∃ f, fs.find? (·.name == n) = some f ∧ f.forced = .ok Γ ids := by
  unfold survivor at h
  split at h
  · rename_i n' Γ' ids' pat hf
    cases h
    exact ⟨_, hf, rfl⟩
  all_goals simp [failAt_eq, internal] at h

/-- What a pattern `let` checks: its value constructor survives forcing, and, unless `comptime`, no other does. -/
theorem patBind_spec {sc sc' : Scope} {r : Res} {rhsPos : Pos} {comptime : Bool} {pat : Pattern}
    {fs : List Forcing} (h : patBind sc r rhsPos comptime pat fs = .ok sc') :
    ∃ Γ ids, (∃ f, fs.find? (·.name == pat.ctor.name) = some f ∧ f.forced = .ok Γ ids) ∧
      (comptime = false → ∀ f ∈ fs, f.name ≠ pat.ctor.name → ∀ Γ' ids', f.forced ≠ .ok Γ' ids') ∧
      sc' = Scope.bind { sc with Γ, taintedBy := reach sc r rhsPos } pat.fields (fieldRes ids) := by
  unfold patBind at h
  obtain ⟨⟨Γ, ids⟩, hs, h⟩ := bind_eq_ok.1 h
  refine ⟨Γ, ids, survivor_spec hs, fun hc f hf hne Γ' ids' hfo => ?_, ?_⟩
  · subst hc
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · simp [failAt_eq, bind, Except.bind] at h
    · rename_i hnone
      have : (fs.find? fun f : Forcing => f.name != pat.ctor.name && f.forced matches .ok ..).isSome :=
        List.find?_isSome.2 ⟨f, hf, by simp [hne, hfo]⟩
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 this
      exact hnone o ho
  · cases comptime
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · simp [failAt_eq, bind, Except.bind] at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h.symm
    · simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      exact h.symm

theorem HeadOk.mono {S : Sigs} {W W' : World} {k : HeadKind} {n : String} (hW : W.Le W') (h : HeadOk S W k n) :
    HeadOk S W' k n :=
  let ⟨h1, h2⟩ := hW.prog.kind n k h.fns h.kind
  ⟨h1, h2, h.sig⟩

/-- Later worlds add no value constructor to a data type of `W`. -/
theorem Complete.mono {W W' : World} {T : String} {cs : List String} (hW : W.Le W') (hT : T ≠ "Type")
    (hs : ∃ s, W.Sc.find ⟨.type, T⟩ = some s) (h : Complete W T cs) : Complete W' T cs := by
  intro h' sig' ws hd us hf hr hn
  cases hm : W.Sc.find h' with
  | some s =>
    obtain rfl := Option.some.inj ((hW.sigs _ _ hm).symm.trans hf)
    exact h h' s ws hd us hm hr hn
  | none =>
    obtain ⟨hk, hd'⟩ := hW.fresh h' sig' ws hd us hm hf hr
    obtain ⟨k, n⟩ := hd
    simp only at hk hn
    subst hk hn
    rcases hd' with hd' | hd'
    · exact absurd (congrArg Head.name hd') hT
    · obtain ⟨s, hs⟩ := hs
      rw [hs] at hd'; cases hd'

theorem FnSpec.callSpec {W : World} {phase : Nat} {d : FnDef} {sig : FnSig} (h : FnSpec W phase d sig) (act : Act) :
    CallSpec W phase d sig act := fun vs hvs _ => h vs hvs

/-- The invariant depends on the context only through its phase, globals, enclosing function and `solving`. -/
theorem Inv.congr_ctx {C C' : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    (hI : Inv C sc n0 W ρ act) (hph : C'.phase = C.phase) (hgl : C'.globals = C.globals) (hfn : C'.fn = C.fn)
    (hsv : C'.solving = C.solving := by rfl) : Inv C' sc n0 W ρ act :=
  ⟨hI.holes, hI.untainted, hI.sat, hI.n0_world, hI.agree, hI.sigs, hI.sigsOk, hI.noJunk, hI.names,
    hph ▸ hgl ▸ hfn ▸ hI.globals, hfn ▸ hI.act, hsv ▸ hI.solving, hI.typeHeads⟩

theorem arity_ok {pos : Pos} {name : String} {params args : Nat} {u : Unit} (h : arity pos name params args = .ok u) :
    params = args := by
  unfold arity at h
  split at h
  · simp [failAt_eq] at h
  · omega

theorem WantSat.binderSat {S : Sigs} {ρ env : List Value} {b : TBinder} {m : Mult} {v : Value}
    (h : WantSat S ρ { Want.of b with mult := m } env true v) : BinderSat S ρ b env v := by
  obtain ⟨A, hA, -, -, hv⟩ := h.1 b.type rfl
  exact ⟨A, hA, hv rfl, h.2⟩

/-- Signatures returning applications, `Type` only for type constructors, closed, return `Type()` only for type
constructors. -/
theorem typeHeads_close {S : Sigs} {ρ : List Value}
    (h : ∀ sig ∈ S, ∃ hd args, sig.ret = .app hd args ∧ (hd = Head.Type → sig.head.kind = .type)) :
    TypeHeads (S.map (Sig.close ρ)) := by
  intro hh sig vs hf hr
  simp only [Sigs.find_map_close, Option.map_eq_some_iff] at hf
  obtain ⟨s, hs, rfl⟩ := hf
  obtain ⟨hd, args, hret, hk⟩ := h s (List.mem_of_find?_eq_some hs)
  simp only [Sig.close, hret, Term.close, Term.eval_app] at hr
  obtain ⟨ws, -, he⟩ := hr
  simp only [Value.TYPE, Value.app.injEq] at he
  rw [← Sigs.find_head hs]
  exact hk he.1.symm

/-- The closed signatures of a top-level state return `Type()` only for type constructors. -/
theorem TopInv.worldTypeHeads {st : TopState} {ρ : List Value} (hI : TopInv st ρ) : TypeHeads (st.world ρ).Sc :=
  typeHeads_close fun sig hs =>
    let ⟨hd, args, hret, _⟩ := hI.rets sig hs
    ⟨hd, args, hret, fun e => hI.typeHeads sig hs ⟨args, e ▸ hret⟩⟩

end Pledge
