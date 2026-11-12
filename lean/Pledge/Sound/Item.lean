import Pledge.Sound.Stmt
import Pledge.Sound.Fn
import Pledge.Sound.Data

namespace Pledge

theorem TopInv.init (phase : Nat) (table : Table) : TopInv (TopState.init phase table) [] := by
  have hTy : Sigs.find [⟨Head.Type, [], Term.TYPE⟩] Head.Type = some ⟨Head.Type, [], Term.TYPE⟩ := by
    simp [Sigs.find]
  refine ⟨rfl, by simp, rfl, ?_, by simp [TopState.init, Sigs.find, junkHead, Head.Type], ?_, ?_,
    by simp [TopState.init], by simp [TopState.init], ⟨_, hTy⟩, by simp [TopState.init],
    by simp [TopState.init], fun _ => ⟨⟨⟨rfl, fun i en h => by simp [TopState.init] at h⟩,
      fun i en v A h => by simp [TopState.init] at h⟩, fun n r h => by simp [TopState.init, Scope.lookup] at h,
      fun n r h => by simp [TopState.init, Scope.lookup] at h, ?_⟩, rfl, fun sig hs _ => ?_⟩
  · intro sig hs
    simp only [TopState.init, List.mem_singleton] at hs
    subst hs
    simp [Sig.entriesBelow, Term.TYPE, Term.entriesBelow, Term.entriesBelowList, Term.boundsBelow,
      Term.boundsBelowList]
  · intro sig hs
    simp only [TopState.init, List.mem_singleton] at hs
    subst hs
    exact ⟨Head.Type, [], rfl, rfl, _, hTy⟩
  · intro h sig hs
    have hm := List.mem_of_find?_eq_some hs
    simp only [TopState.init, List.mem_singleton] at hm
    subst hm
    have := Sigs.find_head hs
    subst this
    simp [kindOf, TopState.init, Head.Type, Global.name]
  · intro W' hW act _ n g hg
    simp only [TopState.init, List.find?_cons, List.find?_nil] at hg
    split at hg
    · rename_i hn
      cases hg
      simp only [Global.name, beq_iff_eq] at hn
      subst hn
      exact ⟨HeadOk.mono hW ⟨by simp [TopState.world, TopState.prog, Fns.find, TopState.init],
        by simp [TopState.world, TopState.prog, kindOf, TopState.init, Global.name], _, hTy⟩, by simp⟩
    · cases hg
  · simp only [TopState.init, List.mem_singleton] at hs
    subst hs
    rfl

/-- A group of `data` declarations adds closed signatures that keep the top level's invariant. -/
theorem dataGroup_sound {st st' : TopState} {ρ : List Value} {ds : List Data} (hI : TopInv st ρ)
    (h : dataGroup st ds = .ok st') : (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ := by
  obtain ⟨_, hg⟩ := dataGroup_group h
  exact ⟨hg.le hI hg.junk, hg.topInv hI hg.junk⟩

theorem fnGroup_sound {st st' : TopState} {ρ : List Value} {fs : List Fn} (hI : TopInv st ρ)
    (h : fnGroup st fs = .ok st') :
    (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ :=
  FnGroup.fnGroup_ok hI h

theorem TopState.world_snaps (st : TopState) (snaps : List Snapshot) (ρ : List Value) :
    ({ st with snaps } : TopState).world ρ = st.world ρ := rfl

theorem TopInv.snaps {st : TopState} {ρ : List Value} (hI : TopInv st ρ) (snaps : List Snapshot) :
    TopInv { st with snaps } ρ := by
  cases hI with
  | mk a b c d e f g h i j k l m n o =>
    exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, fun ht => let L := m ht; ⟨L.sat, L.names, L.env, L.globals⟩, n, o⟩

theorem topItem_sound {st st' : TopState} {ρ : List Value} {hw : st.Runs} {t : Top} (hI : TopInv st ρ)
    (h : topItem st hw t = .ok st') : ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  cases t with
  | data d =>
    obtain ⟨h1, h2⟩ := dataGroup_sound hI h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | mutualData _ ds =>
    obtain ⟨h1, h2⟩ := dataGroup_sound hI h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | fn f =>
    obtain ⟨h1, h2⟩ := fnGroup_sound (fs := [f]) hI h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | mutualFn _ fs =>
    obtain ⟨h1, h2⟩ := fnGroup_sound hI h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | stmt s =>
    cases s with
    | patlet p ct m pat rhs =>
      cases ct
      · exact topStmt_sound (hw := hw) hI h
      · exact comptimeLet_sound (hw := hw) hI h
    | «let» => exact topStmt_sound (hw := hw) hI h
    | inspect => exact topStmt_sound (hw := hw) hI h
  | print p e => exact print_sound (hw := hw) hI h
  | goal p g =>
    obtain ⟨h1, h2⟩ := goalItem_sound hI h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | qed p e => exact qed_sound (hw := hw) hI h

namespace DataTop

theorem qedFnGoal_keeps {st st' : TopState} {ps rs : Telescope} {e : Expr} (h : qedFnGoal st ps rs e = .ok st') :
    st'.phase = st.phase ∧ st'.solving = st.solving := by
  obtain ⟨_, _, _, -, -, -, -, rfl⟩ := qedFnGoal_spec h
  exact ⟨rfl, rfl⟩

theorem topItem_keeps {st st' : TopState} {hw : st.Runs} {t : Top} (h : topItem st hw t = .ok st') :
    st'.phase = st.phase ∧ st'.solving = st.solving := by
  unfold topItem at h
  split at h
  · obtain ⟨_, hgr⟩ := dataGroup_group h
    rw [hgr.eq]; exact ⟨rfl, rfl⟩
  · obtain ⟨_, hgr⟩ := dataGroup_group h
    rw [hgr.eq]; exact ⟨rfl, rfl⟩
  · exact (fnGroup_keeps h).1
  · exact (fnGroup_keeps h).1
  · unfold comptimeLet at h
    unwind_ok h
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h]; exact ⟨rfl, rfl⟩)
  · unfold topStmt at h
    unwind_ok h
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h]; exact ⟨rfl, rfl⟩)
  · unwind_ok h
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h]; exact ⟨rfl, rfl⟩)
  · obtain ⟨-, goal, rfl, -⟩ := goal_spec (hw := hw) (by unfold topItem; exact h)
    exact ⟨rfl, rfl⟩
  · unwind_ok h
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h])
    all_goals dsimp only
    all_goals first
      | exact qedFnGoal_keeps (by assumption)
      | (simp only [pure, Except.pure, Except.ok.injEq] at *; subst_vars; exact ⟨rfl, rfl⟩)

end DataTop

/-- At a state with the top level's invariant: an expression checked there as `print`, a `comptime` pattern `let` and
`qed` against a type goal check theirs, with an untainted result, has an evaluation to one run-time value related to
a typed ideal value under the invariant's valuation, which `TopState.eval` returns. -/
theorem TopInv.eval_ok {st : TopState} {ρ : List Value} (hI : TopInv st ρ) {pl : String} {g : Option Given}
    {e : Expr} {o : Out} {r : Res}
    (hg : g = none ∨ ∃ goal t, st.goal = some goal ∧ goal.kind = .type t ∧ g = some goal.given)
    (h : closed st.sc (checkExpr { st.ctx with place := pl } · g e) = .ok o) (hr : single e.pos o.res = .ok r)
    (hrt : r.tainted = false) :
    ∃ a v V, Sat (st.world ρ).Sc st.sc.Γ ρ ∧ Eval st.prog st.env o.tree [a] ∧ Rel (st.world ρ).Sc st.phase a v ∧
      HasType (st.world ρ).Sc v V ∧ ∀ hw, st.eval o.tree r.tainted hw = some a := by
  rw [closed_eq hI.holes fun o h => (Expr.shape e _ _ _ o hI.solving hI.holes h).2.2.1] at h
  have hres := single_ok hr
  have ho : o.sc.taintedBy = none := by
    cases hs : o.sc.taintedBy with
    | none => rfl
    | some _ =>
      have := ((checkExpr_removed h).2.1 (by simp [hs])).2 r (by simp [hres])
      rw [hrt] at this; cases this
  have ht := TopStmt.none_of (Expr.shape e _ st.sc g o hI.solving hI.holes h).2.2.2.2 ho
  have hL := hI.live ht
  have hgok : ∀ g', g = some g' → g'.Ok (st.world ρ).Sc ρ := by
    rintro g' rfl
    obtain ⟨goal, t, hgoal, hk, hg⟩ := hg.resolve_left (by simp)
    cases hg
    exact TopStmt.given_ok hI ht hgoal hk
  obtain ⟨_, vs, -, hvs, hok, -, hrun⟩ := (Expr.sound e _ _ g _ _ ρ _ o (hI.inv ht rfl rfl rfl) hgok h).1 ho
  rw [hres] at hvs hok
  obtain ⟨v, -, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs)
  obtain ⟨V, hV⟩ := (hok 0 r v rfl rfl).2.2 hrt
  obtain ⟨us, hev, us', htk, hrel⟩ := hrun rfl _ hL.env
  rw [hres] at htk hrel
  obtain ⟨a, ho₁, rfl⟩ := one_of_take htk
  obtain rfl := one_eq_ok ho₁
  have hmult : ({ st.ctx with place := pl } : Ctx).posMult g 0 = .many := by
    rcases hg with rfl | ⟨goal, t, -, hk, rfl⟩
    · simp [Ctx.posMult, TopState.ctx]
    · simp [Ctx.posMult, TopState.ctx, TopStmt.given_eq hk, Given.erasedAt]
  have hR := hrel 0 r a v (by simp) rfl rfl hrt
  rw [hmult] at hR
  refine ⟨a, v, V, hL.sat, hev, hR, hV, fun hw => ?_⟩
  obtain ⟨w, hw', hcert⟩ := TopState.eval_spec (h := hw) (by simp [hI.solving, hrt])
  cases Eval.det hcert hev
  exact hw'

/-- What the top level evaluates outside the solving pass has an evaluation (§11): by `Expr.sound` and `Stmt.sound`,
in the scope the invariant says is untainted whenever a result or the scope after a statement is. -/
theorem TopInv.runs {st : TopState} {ρ : List Value} (hI : TopInv st ρ) : st.Runs := by
  refine ⟨fun _ pl e o r ho hr hrt => ?_, fun _ s o ho hto => ?_⟩
  · obtain ⟨a, -, -, -, ha, -⟩ := hI.eval_ok (.inl rfl) ho hr hrt
    exact ⟨a, ha⟩
  · obtain ⟨-, -, -, htnt⟩ := Stmt.shape s st.ctx st.sc o hI.solving hI.holes ho
    obtain ⟨_, -, hrun⟩ := Stmt.sound s _ _ _ _ _ _ _ (hI.inv (TopStmt.none_of htnt hto) rfl rfl rfl) ho hto
    obtain ⟨env, hev, -⟩ := hrun rfl rfl _ (hI.live (TopStmt.none_of htnt hto)).env
    exact ⟨env, hev⟩

/-- A state the top level reaches: while solving `_` (§20), any; otherwise one meeting the invariant. -/
def TopOk (st : TopState) : Prop := st.solving = true ∨ ∃ ρ, TopInv st ρ

theorem TopOk.runs {st : TopState} (h : TopOk st) : st.Runs := by
  rcases h with hs | ⟨_, hI⟩
  · exact ⟨fun h => by simp [hs] at h, fun h => by simp [hs] at h⟩
  · exact hI.runs

theorem TopOk.next {st st' : TopState} {hw : st.Runs} {t : Top} (h : TopOk st) (ht : topItem st hw t = .ok st') :
    TopOk st' := by
  rcases h with hs | ⟨_, hI⟩
  · exact .inl ((DataTop.topItem_keeps ht).2.trans hs)
  · obtain ⟨_, -, hI'⟩ := topItem_sound hI ht
    exact .inr ⟨_, hI'⟩

theorem TopOk.snaps {st : TopState} (h : TopOk st) (snaps : List Snapshot) : TopOk { st with snaps } := by
  rcases h with hs | ⟨_, hI⟩
  · exact .inl hs
  · exact .inr ⟨_, hI.snaps snaps⟩

theorem TopOk.init (phase : Nat) (table : Table) (solving : Bool) : TopOk (.init phase table solving) := by
  cases solving
  · exact .inr ⟨[], TopInv.init phase table⟩
  · exact .inl rfl

end Pledge
