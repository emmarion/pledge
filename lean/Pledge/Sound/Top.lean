import Pledge.Run

namespace Pledge

theorem topItems_ok : ∀ {st : TopState} (h : TopOk st) (prog : Program), TopOk (topItems st h prog).1
  | _, h, [] => h
  | st, h, t :: ts => by
    rcases hc : certify (topItem st h.runs t) with e | ⟨st', hs⟩ <;> simp only [topItems, hc]
    · exact h.snaps _
    · exact topItems_ok _ ts

theorem topItems_sound {ρ : List Value} : ∀ {st : TopState} {h : TopOk st} {prog : Program}, TopInv st ρ →
    ∃ ρ', (st.world ρ).Le ((topItems st h prog).1.world (ρ ++ ρ')) ∧ TopInv (topItems st h prog).1 (ρ ++ ρ')
  | st, _, [], hI => ⟨[], by simpa [topItems] using World.Le.refl _, by simpa [topItems] using hI⟩
  | st, h, t :: ts, hI => by
    rcases hc : certify (topItem st h.runs t) with e | ⟨st', hs⟩ <;> simp only [topItems, hc]
    · exact ⟨[], by simpa [TopState.world_snaps] using World.Le.refl _, by simpa using hI.snaps _⟩
    · obtain ⟨ρ₁, hle, hI'⟩ := topItem_sound hI hs
      obtain ⟨ρ₂, hle', hI''⟩ := topItems_sound (ρ := ρ ++ ρ₁) (h := h.next hs) (prog := ts) hI'
      exact ⟨ρ₁ ++ ρ₂, by simpa using hle.trans hle', by simpa using hI''⟩

/-- Checking items that stop at no error, then more items, is checking them all. -/
theorem topItems_append : ∀ {st : TopState} {h : TopOk st} {pre : List Top} (post : List Top),
    (topItems st h pre).2 = none → topItems st h (pre ++ post) = topItems (topItems st h pre).1 (topItems_ok h pre) post
  | st, h, [], post, _ => rfl
  | st, h, t :: pre, post, hn => by
    rcases hc : certify (topItem st h.runs t) with e | ⟨st', hs⟩ <;> simp only [List.cons_append, topItems, hc] at hn ⊢
    · simp at hn
    · exact topItems_append post hn

/-- When checking a program stops at no error with the goal proved, from a state where it was not, some `qed` proved
it, and checking stopped at no error up to it, in a scope it left untainted. -/
theorem topItems_proved : ∀ {st : TopState} {h : TopOk st} {prog : Program}, (topItems st h prog).2 = none →
    (topItems st h prog).1.proved = true → st.proved = true ∨ ∃ pre p e post, prog = pre ++ .qed p e :: post ∧
      (topItems st h (pre ++ [.qed p e])).2 = none ∧ (topItems st h (pre ++ [.qed p e])).1.proved = true ∧
      (topItems st h (pre ++ [.qed p e])).1.sc.taintedBy = none
  | st, h, [], _, hp => .inl (by simpa [topItems] using hp)
  | st, h, t :: ts, hn, hp => by
    rcases hc : certify (topItem st h.runs t) with e | ⟨st', hs⟩ <;> simp only [topItems, hc] at hn hp
    · simp at hn
    · rcases topItems_proved hn hp with hp' | ⟨pre, p, e, post, rfl, h1, h2, h3⟩
      · rcases topItem_proved hs hp' with hp'' | ⟨⟨p, e, rfl⟩, ht⟩
        · exact .inl hp''
        · exact .inr ⟨[], p, e, ts, rfl, by simp [topItems, hc], by simpa [topItems, hc] using hp',
            by simpa [topItems, hc] using ht⟩
      · exact .inr ⟨t :: pre, p, e, post, rfl, by simpa [topItems, hc] using h1, by simpa [topItems, hc] using h2,
          by simpa [topItems, hc] using h3⟩

/-- When checking a program stops at no error, each item was checked, from the state the items before it left. -/
theorem topItems_split : ∀ {st : TopState} {h : TopOk st} {pre post : List Top} {t : Top},
    (topItems st h (pre ++ t :: post)).2 = none → ∃ s' hs, (topItems st h pre).2 = none ∧
      topItem (topItems st h pre).1 (topItems_ok h pre).runs t = .ok s' ∧
      topItems s' hs post = topItems st h (pre ++ t :: post)
  | st, h, [], post, t, hn => by
    rcases hc : certify (topItem st h.runs t) with e | ⟨s', hs⟩ <;> simp only [List.nil_append, topItems, hc] at hn ⊢
    · simp at hn
    · exact ⟨s', h.next hs, trivial, hs, rfl⟩
  | st, h, a :: pre, post, t, hn => by
    rcases hc : certify (topItem st h.runs a) with e | ⟨s1, hs1⟩ <;>
      simp only [List.cons_append, topItems, hc] at hn ⊢
    · simp at hn
    · exact topItems_split hn

theorem topItems_goal : ∀ {st : TopState} {h : TopOk st} {l : List Top} {g : CheckedGoal},
    (topItems st h l).2 = none → st.goal = some g → (topItems st h l).1.goal = some g
  | st, h, [], g, _, hg => by simpa [topItems] using hg
  | st, h, t :: l, g, hn, hg => by
    rcases hc : certify (topItem st h.runs t) with e | ⟨s', hs⟩ <;> simp only [topItems, hc] at hn ⊢
    · simp at hn
    · exact topItems_goal hn (topItem_goal hs hg)

theorem topItems_keeps : ∀ (st : TopState) (h : TopOk st) (prog : Program), (topItems st h prog).1.phase = st.phase
  | st, h, [] => rfl
  | st, h, t :: ts => by
    rcases hc : certify (topItem st h.runs t) with e | ⟨s', hs⟩ <;> simp only [topItems, hc]
    · rw [topItems_keeps s' _ ts, (DataTop.topItem_keeps hs).1]

/-- Checking keeps the phase. -/
theorem topItems_phase (phase : Nat) (table : Table) (prog : Program) : (checkItems phase table prog).1.phase = phase :=
  topItems_keeps _ _ prog

/-- The goal `g` was proved at a `qed` of `prog`: checking stopped at no error up to that `qed`, which proved `g`, and
the top-level scope after it was untainted, had every entry `g` mentions, and was satisfied by the first values of
`ρ`, with the signatures of that scope closed by them. -/
def ProvedAt (phase : Nat) (table : Table) (prog : Program) (g : CheckedGoal) (ρ : List Value) : Prop :=
  ∃ pre p e post, prog = pre ++ .qed p e :: post ∧ (checkItems phase table (pre ++ [.qed p e])).2 = none ∧
    let st := (checkItems phase table (pre ++ [.qed p e])).1
    st.proved = true ∧ st.sc.taintedBy = none ∧ st.goal = some g ∧ GoalBelow st.sc.Γ.length g ∧
      st.sc.Γ.length ≤ ρ.length ∧
      Sat (st.sc.sigs.map (Sig.close (ρ.take st.sc.Γ.length))) st.sc.Γ (ρ.take st.sc.Γ.length)

/-- The final state's invariant, for a valuation whose first values satisfy the scope at the `qed` if the goal is
proved. -/
theorem topItems_final (phase : Nat) (table : Table) (prog : Program) :
    ∃ ρ, TopInv (checkItems phase table prog).1 ρ ∧ ((checkItems phase table prog).2 = none →
      (checkItems phase table prog).1.proved = true →
        ∀ g, (checkItems phase table prog).1.goal = some g →
        ProvedAt phase table prog g ρ) := by
  by_cases hc : (checkItems phase table prog).2 = none ∧ (checkItems phase table prog).1.proved = true
  · obtain ⟨pre, p, e, post, rfl, hn, hpr, ht⟩ := (topItems_proved hc.1 hc.2).resolve_left (by simp [TopState.init])
    obtain ⟨ρ₀, -, hI₀⟩ := topItems_sound (h := .init _ _ false) (ρ := []) (prog := pre ++ [.qed p e])
      (TopInv.init phase table)
    simp only [List.nil_append] at hI₀
    have he := topItems_append post hn
    simp only [List.append_assoc, List.singleton_append] at he
    obtain ⟨ρ₂, hle, hI⟩ := topItems_sound (prog := post) hI₀
    rw [← he] at hle hI
    refine ⟨ρ₀ ++ ρ₂, hI, fun hn' _ g hg => ⟨pre, p, e, post, rfl, hn, hpr, ht, ?_⟩⟩
    obtain ⟨g₀, hg₀, -⟩ := hI₀.proved hpr
    have hgF := topItems_goal (l := post) (by rw [← he]; exact hn') hg₀
    rw [← he, hg] at hgF
    cases hgF
    have hl := hI₀.len
    simp only [checkItems] at hl ⊢
    refine ⟨hg₀, (hI₀.goal _ hg₀).1, by simp; omega, ?_⟩
    have := hle.take
    simp only [TopState.world] at this
    rw [← hl, this]
    exact (hI₀.live ht).sat
  · obtain ⟨ρ, -, hI⟩ := topItems_sound (h := .init _ _ false) (ρ := []) (prog := prog) (TopInv.init phase table)
    exact ⟨ρ, by simpa using hI, fun hn hpr => absurd ⟨hn, hpr⟩ hc⟩

theorem runProgramWith_sound (phase : Nat) (table : Table) (prog : Program) (has : String → Bool)
    (err : Option (Pos × String)) :
    ∃ W : World, W.P = (checkItems phase table prog).1.prog ∧
      W.Sc = (runProgramWith phase table prog has err).sigs.map (Sig.close W.ρ) ∧
      W.P.fns = (runProgramWith phase table prog has err).fns ∧
      W.ρ.length = (runProgramWith phase table prog has err).entries.length ∧
      ((runProgramWith phase table prog has err).tainted = false →
        Sat W.Sc (runProgramWith phase table prog has err).entries W.ρ) ∧
      ((runProgramWith phase table prog has err).goalProved = some true → ∃ g,
        (runProgramWith phase table prog has err).goal = some g ∧ ProvedAt phase table prog g W.ρ ∧
        GoalHolds W phase g (runProgramWith phase table prog has err).qedFn) := by
  obtain ⟨ρ, hI, hat⟩ := topItems_final phase table prog
  refine ⟨(checkItems phase table prog).1.world ρ, rfl, rfl, rfl, hI.len,
    fun ht => (hI.live (by simpa [runProgramWith, outcome] using ht)).sat, fun hg => ?_⟩
  simp only [runProgramWith, outcome] at hg ⊢
  split at hg
  · simp only [Option.some.injEq, Bool.and_eq_true, Option.isNone_iff_eq_none] at hg
    obtain ⟨g, hg', hW⟩ := hI.proved hg.2
    exact ⟨g, hg', hat hg.1.1 hg.2 g hg', by simpa [topItems_phase] using hW _ (World.Le.refl _)⟩
  · cases hg

/-- An outcome's fields other than its error do not depend on how the error is reported. -/
theorem outcome_text (has : String → Bool) (st : TopState) (failed : Option Stop) (err : Option (Pos × String))
    (text : Stop → Pos × String) :
    outcome has st failed err text = { outcome has st failed err with error := (failed.map text).orElse fun _ => err } :=
  rfl

/-- `runProgram` reports what checking with the table solving finds reports (`runProgramWith`), except for the text
and position of an error: it reports an error exactly when that does, the same one when it was found by evaluating,
and every other field is that of `runProgramWith`, none taken from solving. -/
theorem runProgram_eq (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String)) :
    ∃ error : Option (Pos × String),
      error.isSome = (runProgramWith phase (solution phase prog) prog has err).error.isSome ∧
      (∀ e t n, (checkItems phase (solution phase prog) prog).2 = some (e, t, n) → e.evaluated = true →
        error = some (e.pos, e.msg ())) ∧
      runProgram phase prog has err = { runProgramWith phase (solution phase prog) prog has err with error } := by
  refine ⟨(runProgram phase prog has err).error, ?_, fun e t n hf he => ?_, outcome_text _ _ _ _ _⟩
  · simp only [runProgram, runProgramWith, solution, outcome]
    cases (checkItems phase (solveFrom phase prog []).1 prog).2 <;> simp
  · simp only [runProgram, outcome]
    simp only [solution] at hf
    rw [hf]
    simp [he]

/-- Soundness of the checker and evaluator, for every program (`_`, `sorry` and multiplicities included), under any
phase: there is an ideal valuation `W.ρ` of the final top-level entries, the
program's signatures closed by it typing values, with `W.P` the evaluator's view of the program; it satisfies the
final scope if that scope is untainted (`tainted` is false); and if the goal is reported proved,
the first values of `W.ρ` satisfy the scope at the `qed` that proved it (`ProvedAt`), and the goal holds
(`GoalHolds`): a type goal's type has a value of type `Type()` that some value has as its type, and the function a
`qed` names computes, from run-time arguments related to ideal ones satisfying a function goal's parameters,
run-time results related to ideal ones satisfying its returns. -/
theorem runProgram_sound (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String)) :
    ∃ W : World, W.P = (checkItems phase (solution phase prog) prog).1.prog ∧
      W.Sc = (runProgram phase prog has err).sigs.map (Sig.close W.ρ) ∧
      W.P.fns = (runProgram phase prog has err).fns ∧ W.ρ.length = (runProgram phase prog has err).entries.length ∧
      ((runProgram phase prog has err).tainted = false → Sat W.Sc (runProgram phase prog has err).entries W.ρ) ∧
      ((runProgram phase prog has err).goalProved = some true → ∃ g, (runProgram phase prog has err).goal = some g ∧
        ProvedAt phase (solution phase prog) prog g W.ρ ∧
        GoalHolds W phase g (runProgram phase prog has err).qedFn) := by
  obtain ⟨_, -, -, h⟩ := runProgram_eq phase prog has err
  rw [h]
  exact runProgramWith_sound phase _ prog has err

theorem runProgram_proved {phase : Nat} {prog : Program} {has : String → Bool} {err : Option (Pos × String)}
    (h : (runProgram phase prog has err).goalProved = some true) :
    (checkItems phase (solution phase prog) prog).2 = none ∧
      (checkItems phase (solution phase prog) prog).1.proved = true := by
  obtain ⟨_, -, -, he⟩ := runProgram_eq phase prog has err
  rw [he] at h
  simp only [runProgramWith, outcome] at h
  split at h
  · simp only [Option.some.injEq, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    exact ⟨h.1.1, h.2⟩
  · cases h

/-- A proved type goal has a value: there is a valuation `ρ` of the final top-level entries, satisfying the final
scope if that scope is untainted, whose first values satisfy the scope at the `qed` that proved the goal
(`ProvedAt`), under which the goal's type `t` evaluates to a value `V` of type `Type()`, and some value has type `V`,
by the program's signatures closed by `ρ`. -/
theorem type_goal_inhabited (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String))
    {g : CheckedGoal} {t : Term}
    (hproved : (runProgram phase prog has err).goalProved = some true)
    (hg : (runProgram phase prog has err).goal = some g) (ht : g.kind = .type t) :
    ∃ ρ, ρ.length = (runProgram phase prog has err).entries.length ∧
      ((runProgram phase prog has err).tainted = false →
        Sat ((runProgram phase prog has err).sigs.map (Sig.close ρ)) (runProgram phase prog has err).entries ρ) ∧
      ProvedAt phase (solution phase prog) prog g ρ ∧
      ∃ v V, t.eval ρ [] = some V ∧ HasType ((runProgram phase prog has err).sigs.map (Sig.close ρ)) v V ∧
        HasType ((runProgram phase prog has err).sigs.map (Sig.close ρ)) V Value.TYPE := by
  obtain ⟨W, -, hSc, -, hl, hsat, hgoal⟩ := runProgram_sound phase prog has err
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
    {g : CheckedGoal} {ps rs : Telescope}
    (hproved : (runProgram phase prog has err).goalProved = some true)
    (hg : (runProgram phase prog has err).goal = some g) (hk : g.kind = .fn ps rs) :
    ∃ ρ n d, ρ.length = (runProgram phase prog has err).entries.length ∧
      ((runProgram phase prog has err).tainted = false →
        Sat ((runProgram phase prog has err).sigs.map (Sig.close ρ)) (runProgram phase prog has err).entries ρ) ∧
      ProvedAt phase (solution phase prog) prog g ρ ∧
      (runProgram phase prog has err).qedFn = some n ∧ (runProgram phase prog has err).fns.find n = some d ∧
      ∀ vs, TeleSat ((runProgram phase prog has err).sigs.map (Sig.close ρ)) ρ ps [] vs →
        ∃ ws, TeleSat ((runProgram phase prog has err).sigs.map (Sig.close ρ)) ρ rs vs ws ∧
          ∀ as, MultsRel ((runProgram phase prog has err).sigs.map (Sig.close ρ)) phase (ps.map (·.mult)) as vs →
            ∃ ws', CallRel (checkItems phase (solution phase prog) prog).1.prog d as ws' ∧
              MultsRel ((runProgram phase prog has err).sigs.map (Sig.close ρ)) phase (rs.map (·.mult)) ws' ws := by
  obtain ⟨W, hP, hSc, hF, hl, hsat, hgoal⟩ := runProgram_sound phase prog has err
  obtain ⟨g', hg', hat, hh⟩ := hgoal hproved
  rw [hg] at hg'
  cases hg'
  simp only [GoalHolds, hk] at hh
  obtain ⟨n, d, hn, hd, hh⟩ := hh
  rw [hSc] at hh hsat
  rw [hP] at hh
  exact ⟨W.ρ, n, d, hl, hsat, hat, hn, by rw [← hF]; exact hd, hh⟩

/-- `runProgram_sound` for source text. -/
theorem run_sound (source : String) (phase : Nat) :
    ∃ W : World,
      W.P = (checkItems phase (solution phase (parse source phase).1) (parse source phase).1).1.prog ∧
      W.Sc = (run source phase).sigs.map (Sig.close W.ρ) ∧ W.P.fns = (run source phase).fns ∧
      W.ρ.length = (run source phase).entries.length ∧
      ((run source phase).tainted = false → Sat W.Sc (run source phase).entries W.ρ) ∧
      ((run source phase).goalProved = some true → ∃ g, (run source phase).goal = some g ∧
        ProvedAt phase (solution phase (parse source phase).1) (parse source phase).1 g W.ρ ∧
        GoalHolds W phase g (run source phase).qedFn) :=
  runProgram_sound phase _ (hasKeyword source phase) (parse source phase).2

/-- The "no `False`" corollary, with `sorry` allowed: a program that declares a data type with no value
constructors and sets as its goal an application of it is never reported to prove that goal. -/
theorem no_empty_goal (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String)) (d : Data)
    (hd : Top.data d ∈ prog ∨ ∃ p ds, Top.mutualData p ds ∈ prog ∧ d ∈ ds)
    (hc : d.ctors = []) (p : Pos) (hn : Name) (args : List WTerm) (hg : Top.goal p (.type (.app hn args)) ∈ prog)
    (hname : hn.name = d.name.name) : (runProgram phase prog has err).goalProved ≠ some true := by
  intro hgp
  obtain ⟨hnone, hpr⟩ := runProgram_proved hgp
  obtain ⟨t, ds, ht, hdds, htop⟩ : ∃ t ds, t ∈ prog ∧ d ∈ ds ∧ ∀ s hw, topItem s hw t = dataGroup s ds := by
    rcases hd with hd | ⟨p', ds, hd, hdds⟩
    · exact ⟨_, [d], hd, List.mem_singleton_self _, fun _ _ => rfl⟩
    · exact ⟨_, ds, hd, hdds, fun _ _ => rfl⟩
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem ht
  obtain ⟨s', hs, -, hs', hpost⟩ := topItems_split (hsplit ▸ hnone)
  obtain ⟨ρ₁, -, hI₁⟩ := topItems_sound (h := .init _ _ false) (ρ := []) (prog := pre) (TopInv.init phase _)
  rw [htop] at hs'
  obtain ⟨new, hgr⟩ := dataGroup_group hs'
  have hI' := (dataGroup_sound hI₁ hs').2
  obtain ⟨ρ₂, hle, hIF⟩ := topItems_sound (h := hs) (prog := post) hI'
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
  obtain ⟨sg, hsg', -, hsg, hpostg⟩ := topItems_split (hsplitg ▸ hnone)
  obtain ⟨-, goal, rfl, ty, is, tn, hann, -, rfl⟩ := goal_spec hsg
  have hgF' := topItems_goal (h := hsg') (l := postg) (by rw [hpostg, ← hsplitg]; exact hnone) rfl
  rw [hpostg, ← hsplitg, hgF] at hgF'
  cases hgF'
  obtain ⟨C₁, r, hr, rfl⟩ := annotate_type (by
    obtain ⟨_, -, hIg⟩ := topItems_sound (h := .init _ _ false) (ρ := []) (prog := preg) (TopInv.init phase _)
    exact hIg.solving) hann
  obtain ⟨k, ts, hrt⟩ := checkTerm_app_head hr
  obtain ⟨v, V, hV, hv, -⟩ := hgoal _ (World.Le.refl _)
  simp only [hrt, Term.eval_app] at hV
  obtain ⟨us, -, rfl⟩ := hV
  obtain rfl : k = .type := hIF.hasType_kind hv
  obtain ⟨h', ws, sig, -, hf, hret⟩ := hv.inv_type
  exact List.not_mem_nil (hcomp h' sig ws _ us hf hret hname).2

/-- `no_empty_goal` for source text. -/
theorem run_no_empty_goal (source : String) (phase : Nat) (d : Data)
    (hd : Top.data d ∈ (parse source phase).1 ∨ ∃ p ds, Top.mutualData p ds ∈ (parse source phase).1 ∧ d ∈ ds)
    (hc : d.ctors = []) (p : Pos) (hn : Name) (args : List WTerm)
    (hg : Top.goal p (.type (.app hn args)) ∈ (parse source phase).1) (hname : hn.name = d.name.name) :
    (run source phase).goalProved ≠ some true :=
  no_empty_goal phase _ _ _ d hd hc p hn args hg hname


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

/-- Evaluation at a state `st` that checking a program reaches, given any table for its `_` (§20): an expression
checked there as `print`, a `comptime` pattern `let` and `qed` against a type goal check theirs, with an untainted
result, has an evaluation (`Eval`) to one run-time value related (`Rel`) to a typed ideal value, under an ideal
valuation `ρ` satisfying the scope; the top level's evaluation (`TopState.eval`) returns that value. -/
theorem reached_eval_ok (phase : Nat) (table : Table) (pre : Program) {st : TopState}
    (hst : st = (checkItems phase table pre).1) {pl : String} {g : Option Given} {e : Expr} {o : Out} {r : Res}
    (hg : g = none ∨ ∃ goal t, st.goal = some goal ∧ goal.kind = .type t ∧ g = some goal.given)
    (h : closed st.sc (checkExpr { st.ctx with place := pl } · g e) = .ok o) (hr : single e.pos o.res = .ok r)
    (hrt : r.tainted = false) :
    ∃ ρ a v V, Sat (st.world ρ).Sc st.sc.Γ ρ ∧ Eval st.prog st.env o.tree [a] ∧ Rel (st.world ρ).Sc phase a v ∧
      HasType (st.world ρ).Sc v V ∧ ∀ hw, st.eval o.tree r.tainted hw = some a := by
  obtain ⟨ρ, -, hI⟩ := topItems_sound (h := .init _ _ false) (ρ := []) (prog := pre) (TopInv.init phase table)
  have hph := topItems_phase phase table pre
  subst hst
  obtain ⟨a, v, V, h1, h2, h3, h4, h5⟩ := TopInv.eval_ok (List.nil_append ρ ▸ hI) hg h hr hrt
  rw [hph] at h3
  exact ⟨ρ, a, v, V, h1, h2, h3, h4, h5⟩

/-- At a state `st` that checking a program reaches, given any table for its `_` (§20), a statement checked there as
the top level checks one that leaves the scope untainted has a run (`EvalStmt`), the one `TopState.run` gives. -/
theorem reached_run_ok (phase : Nat) (table : Table) (pre : Program) {st : TopState}
    (hst : st = (checkItems phase table pre).1) {s : Stmt} {o : StmtOut} (h : checkStmt st.ctx st.sc s = .ok o)
    (ht : o.sc.taintedBy = none) : ∃ env, EvalStmt st.prog st.env o.tree env ∧ ∀ hw, st.run o.tree hw = env := by
  obtain ⟨ρ, -, hI⟩ := topItems_sound (h := .init _ _ false) (ρ := []) (prog := pre) (TopInv.init phase table)
  subst hst
  have hs := hI.solving
  obtain ⟨env, hev⟩ := hI.runs.stmt hs s o h ht
  exact ⟨env, hev, fun _ => EvalStmt.det (TopState.run_cert hs) hev⟩

/-- `data Unit() : Type() { tt() : Unit(); } goal Unit(); qed tt();`, which the checker accepts with its goal
proved, so the goal clause of `runProgram_sound` is not vacuous. Checking it runs definitions by well-founded
recursion, which `decide` does not get through within its default limits, so this is checked by `#guard`, not a
theorem. -/
def unitProgram : Program :=
  [.data ⟨⟨"Unit", 0⟩, [], [⟨⟨"tt", 0⟩, [], .app ⟨"Unit", 0⟩ []⟩]⟩,
   .goal 0 (.type (.app ⟨"Unit", 0⟩ [])),
   .qed 0 (.app ⟨"tt", 0⟩ [])]

#guard (runProgram 1 unitProgram (fun _ => true)).goalProved == some true

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

#guard (run fnGoalSource 1).goalProved == some true

#guard (run typeGoalSource 1).goalProved == some true &&
  (run typeGoalSource 1).prints.map (·.2) == ["PlusSucc(Zero(), Zero(), Zero(), PlusZero(Zero()))"]

#guard (run emptyGoalSource 1).error.isNone &&
  (run emptyGoalSource 1).goalProved == some false

#guard (run sorrySource 1).goalProved == some true

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

#guard (run erasedSource 2).error.isNone &&
  (run erasedSource 2).goalProved == some true

#guard [taintedGoalSource, taintedScopeSource].all fun s => [1, 2].all fun ph =>
  (run s ph).error.isNone && (run s ph).qed == "checks" &&
    (run s ph).goalProved == some false

#guard (run emptyGoalSource 2).error.isNone &&
  (run emptyGoalSource 2).goalProved == some false

end Pledge
