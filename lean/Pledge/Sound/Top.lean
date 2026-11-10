import Pledge.Sound.Stmt
import Pledge.Sound.Fn
import Pledge.Sound.Data

namespace Pledge

theorem TopInv.init (phase : Nat) : TopInv (TopState.init phase) [] := by
  have hTy : Sigs.find [⟨Head.Type, [], Term.TYPE⟩] Head.Type = some ⟨Head.Type, [], Term.TYPE⟩ := by
    simp [Sigs.find]
  refine ⟨rfl, by simp, rfl, ?_, by simp [TopState.init, Sigs.find, junkHead, Head.Type], ?_, ?_,
    by simp [TopState.init], by simp [TopState.init], ⟨_, hTy⟩, by simp [TopState.init],
    by simp [TopState.init], fun _ => ⟨⟨⟨rfl, fun i en h => by simp [TopState.init] at h⟩,
      fun i en v A h => by simp [TopState.init] at h⟩, fun n r h => by simp [TopState.init, Scope.lookup] at h,
      fun n r h => by simp [TopState.init, Scope.lookup] at h, ?_⟩⟩
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

/-- A group of `data` declarations adds closed signatures that keep the top level's invariant. -/
theorem dataGroup_sound {st st' : TopState} {ρ : List Value} {ds : List Data} (hI : TopInv st ρ)
    (h : dataGroup st ds = .ok st') : (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ := by
  obtain ⟨_, hg⟩ := dataGroup_group h
  exact ⟨hg.le hI hg.junk, hg.topInv hI hg.junk⟩

theorem fnGroup_sound {st st' : TopState} {ρ : List Value} {fs : List Fn} (hI : TopInv st ρ)
    (hp : fs.all Fn.holeFree = true) (h : fnGroup st fs = .ok st') :
    (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ :=
  FnGroup.fnGroup_ok hI hp h

theorem TopState.world_snaps (st : TopState) (snaps : List Snapshot) (ρ : List Value) :
    ({ st with snaps } : TopState).world ρ = st.world ρ := rfl

theorem TopInv.snaps {st : TopState} {ρ : List Value} (hI : TopInv st ρ) (snaps : List Snapshot) :
    TopInv { st with snaps } ρ := by
  cases hI with
  | mk a b c d e f g h i j k l m =>
    exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, fun ht => let L := m ht; ⟨L.sat, L.names, L.env, L.globals⟩⟩

theorem topItem_sound {st st' : TopState} {ρ : List Value} {t : Top} (hI : TopInv st ρ) (hp : t.holeFree = true)
    (h : topItem st t = .ok st') : ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  cases t with
  | data d =>
    obtain ⟨h1, h2⟩ := dataGroup_sound hI h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | mutualData _ ds =>
    obtain ⟨h1, h2⟩ := dataGroup_sound hI h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | fn f =>
    obtain ⟨h1, h2⟩ := fnGroup_sound (fs := [f]) hI (by simpa [Top.holeFree] using hp) h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | mutualFn _ fs =>
    obtain ⟨h1, h2⟩ := fnGroup_sound hI (by simpa [Top.holeFree] using hp) h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | stmt s =>
    cases s with
    | patlet p ct m pat rhs =>
      cases ct
      · exact topStmt_sound hI hp (fun _ _ _ _ h => by cases h) h
      · exact comptimeLet_sound hI hp h
    | «let» => exact topStmt_sound hI hp (fun _ _ _ _ h => by cases h) h
    | inspect => exact topStmt_sound hI hp (fun _ _ _ _ h => by cases h) h
  | print p e => exact print_sound hI hp h
  | goal p g =>
    obtain ⟨h1, h2⟩ := goalItem_sound hI hp h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | qed p e => exact qed_sound hI hp h

theorem topItems_sound {ρ : List Value} : ∀ {st : TopState} {prog : Program}, TopInv st ρ →
    Program.holeFree prog = true →
    ∃ ρ', (st.world ρ).Le ((topItems st prog).1.world (ρ ++ ρ')) ∧ TopInv (topItems st prog).1 (ρ ++ ρ')
  | st, [], hI, _ => ⟨[], by simpa [topItems] using World.Le.refl _, by simpa [topItems] using hI⟩
  | st, t :: ts, hI, hp => by
    simp only [Program.holeFree, List.all_cons, Bool.and_eq_true] at hp
    simp only [topItems]
    split
    · rename_i st' h
      obtain ⟨ρ₁, hle, hI'⟩ := topItem_sound hI hp.1 h
      obtain ⟨ρ₂, hle', hI''⟩ := topItems_sound (ρ := ρ ++ ρ₁) (prog := ts) hI' hp.2
      exact ⟨ρ₁ ++ ρ₂, by simpa using hle.trans hle', by simpa using hI''⟩
    · exact ⟨[], by simpa [TopState.world_snaps] using World.Le.refl _, by simpa using hI.snaps _⟩

namespace DataTop

theorem qedFnGoal_phase {st st' : TopState} {ps rs : Telescope} {e : Expr} (h : qedFnGoal st ps rs e = .ok st') :
    st'.phase = st.phase := by
  obtain ⟨_, _, _, -, -, -, -, rfl⟩ := qedFnGoal_spec h
  rfl

theorem topItem_phase {st st' : TopState} {t : Top} (h : topItem st t = .ok st') : st'.phase = st.phase := by
  unfold topItem at h
  split at h
  · obtain ⟨_, hgr⟩ := dataGroup_group h
    rw [hgr.eq]
  · obtain ⟨_, hgr⟩ := dataGroup_group h
    rw [hgr.eq]
  · exact (fnGroup_keeps h).1
  · exact (fnGroup_keeps h).1
  · unfold comptimeLet at h
    unwind_ok h
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h])
  · unwind_ok h
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h])
  · unwind_ok h
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h])
  · obtain ⟨-, goal, rfl, -⟩ := goal_spec (by unfold topItem; exact h)
    rfl
  · unwind_ok h
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h])
    all_goals dsimp only
    all_goals first
      | exact qedFnGoal_phase (by assumption)
      | (simp only [pure, Except.pure, Except.ok.injEq] at *; subst_vars; rfl)

theorem topItems_phase : ∀ (st : TopState) (prog : Program), (topItems st prog).1.phase = st.phase
  | st, [] => rfl
  | st, t :: ts => by
    simp only [topItems]
    split
    · rename_i st' h
      rw [topItems_phase st' ts, topItem_phase h]
    · rfl

end DataTop

/-- Checking keeps the phase. -/
theorem topItems_phase (phase : Nat) (prog : Program) : (topItems (.init phase) prog).1.phase = phase :=
  DataTop.topItems_phase _ prog

/-- The goal `g` was proved at a `qed` of `prog`: checking stopped at no error up to that `qed`, which proved `g`, and
the top-level scope after it was untainted, had every entry `g` mentions, and was satisfied by the first values of
`ρ`, with the signatures of that scope closed by them. -/
def ProvedAt (phase : Nat) (prog : Program) (g : CheckedGoal) (ρ : List Value) : Prop :=
  ∃ pre p e post, prog = pre ++ .qed p e :: post ∧ (topItems (.init phase) (pre ++ [.qed p e])).2 = none ∧
    let st := (topItems (.init phase) (pre ++ [.qed p e])).1
    st.proved = true ∧ st.sc.taintedBy = none ∧ st.goal = some g ∧ GoalBelow st.sc.Γ.length g ∧
      st.sc.Γ.length ≤ ρ.length ∧
      Sat (st.sc.sigs.map (Sig.close (ρ.take st.sc.Γ.length))) st.sc.Γ (ρ.take st.sc.Γ.length)

/-- The final state's invariant, for a valuation whose first values satisfy the scope at the `qed` if the goal is
proved. -/
theorem topItems_final (phase : Nat) (prog : Program) (hp : Program.holeFree prog = true) :
    ∃ ρ, TopInv (topItems (.init phase) prog).1 ρ ∧ ((topItems (.init phase) prog).2 = none →
      (topItems (.init phase) prog).1.proved = true → ∀ g, (topItems (.init phase) prog).1.goal = some g →
        ProvedAt phase prog g ρ) := by
  by_cases hc : (topItems (.init phase) prog).2 = none ∧ (topItems (.init phase) prog).1.proved = true
  · obtain ⟨pre, p, e, post, rfl, hn, hpr, ht⟩ := (topItems_proved hc.1 hc.2).resolve_left (by simp [TopState.init])
    simp only [Program.holeFree, List.all_append, List.all_cons, Bool.and_eq_true] at hp
    obtain ⟨ρ₀, -, hI₀⟩ := topItems_sound (ρ := []) (prog := pre ++ [.qed p e]) (TopInv.init phase)
      (by simp [Program.holeFree, hp.1, hp.2.1])
    simp only [List.nil_append] at hI₀
    have he := topItems_append post hn
    simp only [List.append_assoc, List.singleton_append] at he
    obtain ⟨ρ₂, hle, hI⟩ := topItems_sound (prog := post) hI₀ hp.2.2
    rw [← he] at hle hI
    refine ⟨ρ₀ ++ ρ₂, hI, fun hn' _ g hg => ⟨pre, p, e, post, rfl, hn, hpr, ht, ?_⟩⟩
    obtain ⟨g₀, hg₀, -⟩ := hI₀.proved hpr
    have hgF := topItems_goal (l := post) (by rw [← he]; exact hn') hg₀
    rw [← he, hg] at hgF
    cases hgF
    have hl := hI₀.len
    refine ⟨hg₀, (hI₀.goal _ hg₀).1, by simp; omega, ?_⟩
    have := hle.take
    simp only [TopState.world] at this
    rw [← hl, this]
    exact (hI₀.live ht).sat
  · obtain ⟨ρ, -, hI⟩ := topItems_sound (ρ := []) (prog := prog) (TopInv.init phase) hp
    exact ⟨ρ, by simpa using hI, fun hn hpr => absurd ⟨hn, hpr⟩ hc⟩

/-- Soundness of the checker and evaluator, for hole-free programs (no `_`, §16; `sorry` and
multiplicities allowed), under any phase: there is an ideal valuation `W.ρ` of the final top-level entries, the
program's signatures closed by it typing values, with `W.P` the evaluator's view of the program; it satisfies the
final scope if that scope is untainted (`tainted` is false); and if the goal is reported proved,
the first values of `W.ρ` satisfy the scope at the `qed` that proved it (`ProvedAt`), and the goal holds
(`GoalHolds`): a type goal's type has a value of type `Type()` that some value has as its type, and the function a
`qed` names computes, from run-time arguments related to ideal ones satisfying a function goal's parameters,
run-time results related to ideal ones satisfying its returns. -/
theorem runProgram_sound (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String))
    (hp : Program.holeFree prog = true) :
    ∃ W : World, W.P = (topItems (.init phase) prog).1.prog ∧
      W.Sc = (runProgram phase prog has err).sigs.map (Sig.close W.ρ) ∧
      W.P.fns = (runProgram phase prog has err).fns ∧ W.ρ.length = (runProgram phase prog has err).entries.length ∧
      ((runProgram phase prog has err).tainted = false → Sat W.Sc (runProgram phase prog has err).entries W.ρ) ∧
      ((runProgram phase prog has err).goalProved = some true → ∃ g, (runProgram phase prog has err).goal = some g ∧
        ProvedAt phase prog g W.ρ ∧ GoalHolds W phase g (runProgram phase prog has err).qedFn) := by
  obtain ⟨ρ, hI, hat⟩ := topItems_final phase prog hp
  refine ⟨(topItems (.init phase) prog).1.world ρ, rfl, rfl, rfl, hI.len,
    fun ht => (hI.live (by simpa [runProgram] using ht)).sat, fun hg => ?_⟩
  simp only [runProgram] at hg ⊢
  split at hg
  · simp only [Option.some.injEq, Bool.and_eq_true] at hg
    have hn : (topItems (.init phase) prog).2 = none := by
      cases hf : (topItems (.init phase) prog).2 with
      | none => rfl
      | some _ => simp [hf] at hg
    obtain ⟨g, hg', hW⟩ := hI.proved hg.2
    exact ⟨g, hg', hat hn hg.2 g hg', by simpa [topItems_phase] using hW _ (World.Le.refl _)⟩
  · cases hg

/-- A proved type goal has a value: there is a valuation `ρ` of the final top-level entries, satisfying the final
scope if that scope is untainted, whose first values satisfy the scope at the `qed` that proved the goal
(`ProvedAt`), under which the goal's type `t` evaluates to a value `V` of type `Type()`, and some value has type `V`,
by the program's signatures closed by `ρ`. -/
theorem type_goal_inhabited (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String))
    (hp : Program.holeFree prog = true) {g : CheckedGoal} {t : Term}
    (hproved : (runProgram phase prog has err).goalProved = some true)
    (hg : (runProgram phase prog has err).goal = some g) (ht : g.kind = .type t) :
    ∃ ρ, ρ.length = (runProgram phase prog has err).entries.length ∧
      ((runProgram phase prog has err).tainted = false →
        Sat ((runProgram phase prog has err).sigs.map (Sig.close ρ)) (runProgram phase prog has err).entries ρ) ∧
      ProvedAt phase prog g ρ ∧
      ∃ v V, t.eval ρ [] = some V ∧ HasType ((runProgram phase prog has err).sigs.map (Sig.close ρ)) v V ∧
        HasType ((runProgram phase prog has err).sigs.map (Sig.close ρ)) V Value.TYPE := by
  obtain ⟨W, -, hSc, -, hl, hsat, hgoal⟩ := runProgram_sound phase prog has err hp
  obtain ⟨g', hg', hat, hh⟩ := hgoal hproved
  rw [hg] at hg'
  cases hg'
  simp only [GoalHolds, ht] at hh
  rw [hSc] at hh hsat
  exact ⟨W.ρ, hl, hsat, hat, hh⟩

/-- A proved function goal holds: there is a valuation `ρ` of the final top-level entries, satisfying the final scope
if that scope is untainted, whose first values satisfy the scope at the `qed` that proved the goal (`ProvedAt`),
under which the function `n` the `qed` names, `d` to the evaluator, takes every list of values satisfying the
goal's parameters `ps` to values satisfying its returns `rs`: running `d` on any run-time values related to them by
the parameters' multiplicities returns run-time results related to them by the returns' multiplicities. -/
theorem fn_goal_holds (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String))
    (hp : Program.holeFree prog = true) {g : CheckedGoal} {ps rs : Telescope}
    (hproved : (runProgram phase prog has err).goalProved = some true)
    (hg : (runProgram phase prog has err).goal = some g) (hk : g.kind = .fn ps rs) :
    ∃ ρ n d, ρ.length = (runProgram phase prog has err).entries.length ∧
      ((runProgram phase prog has err).tainted = false →
        Sat ((runProgram phase prog has err).sigs.map (Sig.close ρ)) (runProgram phase prog has err).entries ρ) ∧
      ProvedAt phase prog g ρ ∧
      (runProgram phase prog has err).qedFn = some n ∧ (runProgram phase prog has err).fns.find n = some d ∧
      ∀ vs, TeleSat ((runProgram phase prog has err).sigs.map (Sig.close ρ)) ρ ps [] vs →
        ∃ ws, TeleSat ((runProgram phase prog has err).sigs.map (Sig.close ρ)) ρ rs vs ws ∧
          ∀ as, MultsRel ((runProgram phase prog has err).sigs.map (Sig.close ρ)) phase (ps.map (·.mult)) as vs →
            ∃ ws', CallRel (topItems (.init phase) prog).1.prog d as ws' ∧
              MultsRel ((runProgram phase prog has err).sigs.map (Sig.close ρ)) phase (rs.map (·.mult)) ws' ws := by
  obtain ⟨W, hP, hSc, hF, hl, hsat, hgoal⟩ := runProgram_sound phase prog has err hp
  obtain ⟨g', hg', hat, hh⟩ := hgoal hproved
  rw [hg] at hg'
  cases hg'
  simp only [GoalHolds, hk] at hh
  obtain ⟨n, d, hn, hd, hh⟩ := hh
  rw [hSc] at hh hsat
  rw [hP] at hh
  exact ⟨W.ρ, n, d, hl, hsat, hat, hn, by rw [← hF]; exact hd, hh⟩

/-- `runProgram_sound` for source text whose parsed program is hole-free. -/
theorem run_sound (source : String) (phase : Nat) (hp : Program.holeFree (parse source phase).1 = true) :
    ∃ W : World, W.P = (topItems (.init phase) (parse source phase).1).1.prog ∧
      W.Sc = (run source phase).sigs.map (Sig.close W.ρ) ∧ W.P.fns = (run source phase).fns ∧
      W.ρ.length = (run source phase).entries.length ∧
      ((run source phase).tainted = false → Sat W.Sc (run source phase).entries W.ρ) ∧
      ((run source phase).goalProved = some true → ∃ g, (run source phase).goal = some g ∧
        ProvedAt phase (parse source phase).1 g W.ρ ∧ GoalHolds W phase g (run source phase).qedFn) :=
  runProgram_sound phase _ (hasKeyword source phase) (parse source phase).2 hp

/-- The "no `False`" corollary, with `sorry` allowed: a program that declares a data type with no value
constructors and sets as its goal an application of it is never reported to prove that goal. -/
theorem no_empty_goal (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String))
    (hp : Program.holeFree prog = true) (d : Data)
    (hd : Top.data d ∈ prog ∨ ∃ p ds, Top.mutualData p ds ∈ prog ∧ d ∈ ds)
    (hc : d.ctors = []) (p : Pos) (hn : Name) (args : List WTerm) (hg : Top.goal p (.type (.app hn args)) ∈ prog)
    (hname : hn.name = d.name.name) : (runProgram phase prog has err).goalProved ≠ some true := by
  intro hgp
  obtain ⟨hnone, hpr⟩ : (topItems (.init phase) prog).2 = none ∧ (topItems (.init phase) prog).1.proved = true := by
    simp only [runProgram] at hgp
    split at hgp
    · simp only [Option.some.injEq, Bool.and_eq_true] at hgp
      refine ⟨?_, hgp.2⟩
      cases hf : (topItems (TopState.init phase) prog).2 with
      | none => rfl
      | some _ => simp [hf] at hgp
    · cases hgp
  have hsplitp : ∀ {pre post : List Top} {t : Top}, prog = pre ++ t :: post →
      Program.holeFree pre = true ∧ t.holeFree = true ∧ Program.holeFree post = true := fun he => by
    rw [he] at hp
    simpa [Program.holeFree] using hp
  obtain ⟨t, ds, ht, hdds, htop⟩ : ∃ t ds, t ∈ prog ∧ d ∈ ds ∧ ∀ s, topItem s t = dataGroup s ds := by
    rcases hd with hd | ⟨p', ds, hd, hdds⟩
    · exact ⟨_, [d], hd, List.mem_singleton_self _, fun _ => rfl⟩
    · exact ⟨_, ds, hd, hdds, fun _ => rfl⟩
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem ht
  obtain ⟨s', -, hs', hpost⟩ := topItems_split (hsplit ▸ hnone)
  obtain ⟨hp1, -, hp3⟩ := hsplitp hsplit
  obtain ⟨ρ₁, -, hI₁⟩ := topItems_sound (ρ := []) (prog := pre) (TopInv.init phase) hp1
  rw [htop] at hs'
  obtain ⟨new, hgr⟩ := dataGroup_group hs'
  have hI' := (dataGroup_sound hI₁ hs').2
  obtain ⟨ρ₂, hle, hIF⟩ := topItems_sound (prog := post) hI' hp3
  rw [hpost, ← hsplit] at hle hIF
  obtain ⟨g, hgF, hgoal⟩ := hIF.proved hpr
  have hT := List.mem_map_of_mem (f := (·.name.name)) hdds
  have hSc : ∃ s, ((s'.world ([] ++ ρ₁)).Sc).find ⟨.type, d.name.name⟩ = some s := by
    obtain ⟨s0, hs0, hh⟩ := hgr.types _ hT
    obtain ⟨s, hs⟩ := Sigs.find_of_mem (List.mem_append_right _ hs0) hh
    rw [hgr.world_Sc, Sigs.find_map_close, hs]
    exact ⟨_, rfl⟩
  have hcomp := Complete.mono hle (hgr.ne_Type hI₁ (List.mem_append_left _ hT)) hSc (hgr.complete hI₁ hT)
  rw [ownedBy_empty (List.nodup_append.1 hgr.nodup).1 hdds hc] at hcomp
  obtain ⟨preg, postg, hsplitg⟩ := List.append_of_mem hg
  obtain ⟨sg, -, hsg, hpostg⟩ := topItems_split (hsplitg ▸ hnone)
  obtain ⟨-, hpg, -⟩ := hsplitp hsplitg
  obtain ⟨-, goal, rfl, ty, is, tn, hann, -, rfl⟩ := goal_spec hsg
  have hgF' := topItems_goal (hpostg ▸ hsplitg ▸ hnone) rfl
  rw [hpostg, ← hsplitg, hgF] at hgF'
  cases hgF'
  obtain ⟨r, hr, rfl⟩ := annotate_type (by simpa [Top.holeFree] using hpg) hann
  obtain ⟨k, ts, hrt⟩ := checkTerm_app_head hr
  obtain ⟨v, V, hV, hv, -⟩ := hgoal _ (World.Le.refl _)
  simp only [hrt, Term.eval_app] at hV
  obtain ⟨us, -, rfl⟩ := hV
  obtain rfl : k = .type := hIF.hasType_kind hv
  obtain ⟨h', ws, sig, -, hf, hret⟩ := hv.inv_type
  exact List.not_mem_nil (hcomp h' sig ws _ us hf hret hname).2

/-- `no_empty_goal` for source text whose parsed program is hole-free. -/
theorem run_no_empty_goal (source : String) (phase : Nat) (hp : Program.holeFree (parse source phase).1 = true)
    (d : Data) (hd : Top.data d ∈ (parse source phase).1 ∨ ∃ p ds, Top.mutualData p ds ∈ (parse source phase).1 ∧ d ∈ ds)
    (hc : d.ctors = []) (p : Pos) (hn : Name) (args : List WTerm)
    (hg : Top.goal p (.type (.app hn args)) ∈ (parse source phase).1) (hname : hn.name = d.name.name) :
    (run source phase).goalProved ≠ some true :=
  no_empty_goal phase _ _ _ hp d hd hc p hn args hg hname

namespace DataTop

mutual
theorem Term.eval_noRemoved {ρ env : List Value} (hρ : ∀ v ∈ ρ, v.noRemoved = true)
    (henv : ∀ v ∈ env, v.noRemoved = true) : ∀ (t : Term) {v : Value}, t.eval ρ env = some v → v.noRemoved = true
  | .entry i, _, h => hρ _ (List.mem_of_getElem? h)
  | .bound i, _, h => henv _ (List.mem_of_getElem? h)
  | .app _ as, _, h => by
    obtain ⟨vs, hvs, rfl⟩ := Term.eval_app.1 h
    exact Term.evalList_noRemoved hρ henv as hvs
theorem Term.evalList_noRemoved {ρ env : List Value} (hρ : ∀ v ∈ ρ, v.noRemoved = true)
    (henv : ∀ v ∈ env, v.noRemoved = true) :
    ∀ (as : List Term) {vs : List Value}, Term.evalList ρ env as = some vs → Value.noRemovedList vs = true
  | [], _, h => by cases h; rfl
  | a :: as, _, h => by
    obtain ⟨v, vs, hv, hvs, rfl⟩ := Term.evalList_cons_eq_some.1 h
    simp only [Value.noRemovedList, Term.eval_noRemoved hρ henv a hv, Term.evalList_noRemoved hρ henv as hvs,
      Bool.and_self]
end

/-- Wants without `is` clauses whose types have values whatever their bound variables are can be opened. -/
theorem wantsCons_closed {S : Sigs} {ρ : List Value} :
    ∀ (ws : List Want) (env : List Value), (∀ w ∈ ws, w.is = none ∧
      ∀ t, w.type = some t → ∃ A, (∀ env, t.eval ρ env = some A) ∧ A.noRemoved = true) → WantsCons S ρ ws env
  | [], _, _ => trivial
  | w :: ws, env, h => by
    refine ⟨fun T hT => ?_, fun e he => ?_, fun v _ => wantsCons_closed ws _ fun w' hw' =>
      h w' (List.mem_cons_of_mem _ hw')⟩
    · obtain ⟨A, hA, hn⟩ := (h w List.mem_cons_self).2 T hT
      exact ⟨A, hA env, hn⟩
    · rw [(h w List.mem_cons_self).1] at he; cases he

end DataTop

/-- Evaluation at a state `st` the checker reaches on a hole-free program, while its scope is untainted
(§12): an expression checked there at the top level with an untainted result, given closed types of multiplicity
`many`, as `print`, `qed` against a type goal and a `comptime` pattern `let` check theirs, has an evaluation (`Eval`)
to one run-time value related (`Rel`) to a typed ideal value, under an ideal valuation `ρ` satisfying the scope; any
value `TopState.eval` returns for it is that one. `TopState.eval` runs the `partial` evaluator, so this does not
establish that it returns a value rather than an error, or that it returns at all. -/
theorem reached_eval_ok (phase : Nat) {pre : Program} (hp : Program.holeFree pre = true) {st : TopState}
    (hst : st = (topItems (.init phase) pre).1) (ht : st.sc.taintedBy = none) {C : Ctx} {g : Option Given} {e : Expr}
    {o : Out} {r : Res} (hph : C.phase = phase) (her : C.erased = false) (hgl : C.globals = st.globals)
    (hfn : C.fn = none) (hg : ∀ g', g = some g' → g'.env = [] ∧ ∀ w ∈ g'.wants, w.mult = .many ∧ w.is = none ∧
      ∀ t, w.type = some t → t.entriesBelow st.sc.Γ.length = true ∧ t.closed = true)
    (he : e.holeFree = true) (h : checkExpr C st.sc g e = .ok o) (hr : single e.pos o.res = .ok r)
    (hrt : r.tainted = false) :
    ∃ ρ a v V, Sat (st.world ρ).Sc st.sc.Γ ρ ∧ Eval st.prog st.env o.tree [a] ∧ Rel (st.world ρ).Sc phase a v ∧
      HasType (st.world ρ).Sc v V ∧ ∀ pos w, st.eval pos o.tree r.tainted = .ok (some w) → w = a := by
  subst hst
  obtain ⟨ρ, -, hI⟩ := topItems_sound (ρ := []) (prog := pre) (TopInv.init phase) hp
  simp only [List.nil_append] at hI
  have hph' : C.phase = (topItems (.init phase) pre).1.phase := by rw [topItems_phase]; exact hph
  have hL := hI.live ht
  have hInv := hI.inv ht hph' hgl hfn
  have hgok : ∀ g', g = some g' → g'.Ok (TopState.world (topItems (.init phase) pre).1 ρ).Sc ρ := by
    intro g' hg'
    obtain ⟨henv, hw⟩ := hg g' hg'
    refine ⟨⟨[], by rw [henv]; rfl⟩, fun _ envv _ => DataTop.wantsCons_closed _ _ fun w hw' => ⟨(hw w hw').2.1,
      fun t ht' => ?_⟩⟩
    obtain ⟨hb, hc⟩ := (hw w hw').2.2 t ht'
    obtain ⟨A, hA⟩ := Term.eval_isSome (ρ := ρ) (env := []) t (by rw [hI.len]; exact hb) hc
    exact ⟨A, fun env => by rw [Term.eval_closed env hc, hA],
      DataTop.Term.eval_noRemoved hI.noRemoved (by simp) t hA⟩
  have hres := single_ok hr
  have ho : o.sc.taintedBy = none := by
    cases hs : o.sc.taintedBy with
    | none => rfl
    | some _ =>
      have := ((checkExpr_removed h).2.1 (by simp [hs])).2 r (by simp [hres])
      rw [hrt] at this; cases this
  obtain ⟨ρ', vs, -, hvs, hok, -, hrun⟩ := (Expr.sound e he C _ g _ _ ρ _ o hInv hgok h).1 ho
  rw [hres] at hvs hok
  obtain ⟨v, -, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs)
  obtain ⟨V, hV⟩ := (hok 0 r v rfl rfl).2.2 hrt
  obtain ⟨us, hev, us', htk, hrel⟩ := hrun _ (hph' ▸ hL.env)
  rw [hres] at htk hrel
  obtain ⟨a, -, rfl⟩ := one_of_take htk
  have hmult : C.posMult g 0 = .many := by
    cases g with
    | none => simp [Ctx.posMult, her]
    | some g' =>
      cases hw : g'.wants[0]? with
      | none => simp [Ctx.posMult, her, Given.erasedAt, hw]
      | some w => simp [Ctx.posMult, her, Given.erasedAt, hw, ((hg g' rfl).2 w (List.mem_of_getElem? hw)).1]
  have hR : Rel (TopState.world (topItems (.init phase) pre).1 ρ).Sc phase a v := by
    have := hrel 0 r a v (by simp) rfl rfl hrt
    rw [hmult, hph] at this
    exact this
  have hus : us = [a] := by
    rcases (take_ok htk).2 with h' | ⟨rfl, h'⟩
    · exact h'.symm
    · cases h'; rfl
  subst hus
  refine ⟨ρ, a, v, V, hL.sat, hev, hR, hV, fun pos w hw => ?_⟩
  rw [hrt] at hw
  obtain ⟨w', hw', hcert⟩ := TopState.eval_cert hw
  obtain rfl := Option.some.inj hw'
  simpa using (Eval.det hev hcert).symm

/-- At a state `st` the checker reaches on a hole-free program, while its scope is untainted, a
statement checked there at the top level that leaves the scope untainted has a run (`EvalStmt`). -/
theorem reached_run_ok (phase : Nat) {pre : Program} (hp : Program.holeFree pre = true) {st : TopState}
    (hst : st = (topItems (.init phase) pre).1) (ht : st.sc.taintedBy = none) {C : Ctx} {s : Stmt} {o : StmtOut}
    (hph : C.phase = phase) (her : C.erased = false) (hgl : C.globals = st.globals) (hfn : C.fn = none)
    (hs : s.holeFree = true) (h : checkStmt C st.sc s = .ok o) (ht' : o.sc.taintedBy = none) :
    ∃ env, EvalStmt st.prog st.env o.tree env := by
  subst hst
  obtain ⟨ρ, -, hI⟩ := topItems_sound (ρ := []) (prog := pre) (TopInv.init phase) hp
  simp only [List.nil_append] at hI
  have hph' : C.phase = (topItems (.init phase) pre).1.phase := by rw [topItems_phase]; exact hph
  obtain ⟨ρ', -, hrun⟩ := Stmt.sound s hs C _ _ _ ρ _ o (hI.inv ht hph' hgl hfn) h ht'
  obtain ⟨env, hev, -⟩ := hrun her _ (hph' ▸ (hI.live ht).env)
  exact ⟨env, hev⟩

/-- `data Unit() : Type() { tt() : Unit(); } goal Unit(); qed tt();`, which the checker accepts with its goal
proved, so the goal clause of `runProgram_sound` is not vacuous. The evaluator is `partial`, which kernel reduction
does not unfold, so this is checked by `#guard`, not a theorem. -/
def unitProgram : Program :=
  [.data ⟨⟨"Unit", 0⟩, [], [⟨⟨"tt", 0⟩, [], .app ⟨"Unit", 0⟩ []⟩]⟩,
   .goal 0 (.type (.app ⟨"Unit", 0⟩ [])),
   .qed 0 (.app ⟨"tt", 0⟩ [])]

#guard (runProgram 1 unitProgram (fun _ => true)).goalProved == some true

#guard Program.holeFree unitProgram

def natSource : String :=
  "data Nat() : Type() { Zero() : Nat(); Succ(pred : Nat()) : Nat(); }
  data Plus(m : Nat(), n : Nat(), r : Nat()) : Type() {
    PlusZero(n : Nat()) : Plus(Zero(), n, n);
    PlusSucc(m : Nat(), n : Nat(), r : Nat(), p : Plus(m, n, r)) : Plus(Succ(m), n, Succ(r));
  }
  fn plusZero(subterm n : Nat()) -> (p : Plus(n, Zero(), n)) {
    match n : (p : Plus(n, Zero(), n)) {
      Zero() => PlusZero(Zero());
      Succ(m) => PlusSucc(m, Zero(), m, plusZero(subterm m));
    }
  }
  print plusZero(Succ(Zero()));
  "

def fnGoalSource : String := natSource ++ "goal fn (n : Nat()) -> (p : Plus(n, Zero(), n)); qed plusZero;"

def typeGoalSource : String := natSource ++
  "goal Plus(Succ(Succ(Zero())), Zero(), Succ(Succ(Zero()))); qed plusZero(Succ(Succ(Zero())));"

def emptyGoalSource : String := "data False() : Type() {} goal False(); qed sorry(_);"

/-- A program with `sorry` whose goal is proved without it: an untainted function, and a top-level entry of an empty
type that a declaration's signature mentions (the case `Value.junk` is for). -/
def sorrySource : String :=
  "data Empty() : Type() {}
  data Nat() : Type() { Zero() : Nat(); Succ(p : Nat()) : Nat(); }
  let e = sorry(e : Empty());
  data Box(x : Empty()) : Type() { MkBox() : Box(e); }
  fn f(b : Box(e)) -> (r : Nat()) { Zero() }
  goal Nat();
  qed f(MkBox());"

#guard Program.holeFree (parse fnGoalSource 1).1 && (run fnGoalSource 1).goalProved == some true

#guard Program.holeFree (parse typeGoalSource 1).1 && (run typeGoalSource 1).goalProved == some true &&
  (run typeGoalSource 1).prints.map (·.2) == ["PlusSucc(Zero(), Zero(), Zero(), PlusZero(Zero()))"]

#guard Program.holeFree (parse emptyGoalSource 1).1 && (run emptyGoalSource 1).error.isNone &&
  (run emptyGoalSource 1).goalProved == some false

#guard Program.holeFree (parse sorrySource 1).1 && (run sorrySource 1).goalProved == some true

/-- A phase 2 program with `sorry` and erased fields whose goal is proved. -/
def erasedSource : String :=
  "data Nat() : Type() { Zero() : Nat(); Succ(p : Nat()) : Nat(); }
  data Le(m : Nat(), n : Nat()) : Type() {
    LeZero(erased n : Nat()) : Le(Zero(), n);
    LeSucc(erased m : Nat(), erased n : Nat(), p : Le(m, n)) : Le(Succ(m), Succ(n));
  }
  let s = sorry(s : Nat());
  goal Le(Succ(Zero()), Succ(Succ(Zero())));
  qed LeSucc(Zero(), Succ(Zero()), LeZero(Succ(Zero())));"

/-- A goal tainted through its type, and a goal after a pattern `let` on `sorry`: neither is proved. -/
def taintedGoalSource : String :=
  "data Unit() : Type() { tt() : Unit(); }
  let e = sorry(e : Unit());
  data Box(x : Unit()) : Type() { MkBox(x : Unit()) : Box(x); }
  goal Box(e);
  qed MkBox(e);"

def taintedScopeSource : String :=
  "data Unit() : Type() { tt() : Unit(); }
  let tt() = sorry(u : Unit());
  goal Unit();
  qed tt();"

#guard Program.holeFree (parse erasedSource 2).1 && (run erasedSource 2).error.isNone &&
  (run erasedSource 2).goalProved == some true

#guard [taintedGoalSource, taintedScopeSource].all fun s => [1, 2].all fun ph =>
  Program.holeFree (parse s ph).1 && (run s ph).error.isNone && (run s ph).qed == "checks" &&
    (run s ph).goalProved == some false

#guard Program.holeFree (parse emptyGoalSource 2).1 && (run emptyGoalSource 2).error.isNone &&
  (run emptyGoalSource 2).goalProved == some false

end Pledge
