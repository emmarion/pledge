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
    · rw [topItems_keeps s' _ ts, DataTop.topItem_keeps hs]

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

/-- After an error, checking more items changes nothing but the error's count of the items after it. -/
theorem topItems_stop : ∀ {st : TopState} {h : TopOk st} {pre : List Top} (post : List Top),
    (topItems st h pre).2 ≠ none →
      (topItems st h (pre ++ post)).1 = (topItems st h pre).1 ∧ (topItems st h (pre ++ post)).2 ≠ none
  | st, h, [], post, hn => by simp [topItems] at hn
  | st, h, t :: pre, post, hn => by
    rcases hc : certify (topItem st h.runs t) with e | ⟨st', hs⟩ <;>
      simp only [List.cons_append, topItems, hc] at hn ⊢
    · simp
    · exact topItems_stop post hn

theorem ProvedAt.extend {phase : Nat} {table : Table} {prog : Program} {g : CheckedGoal} {ρ : List Value}
    (post : List Top) (ρ' : List Value) (h : ProvedAt phase table prog g ρ) :
    ProvedAt phase table (prog ++ post) g (ρ ++ ρ') := by
  obtain ⟨pre, p, e, rest, rfl, hn, hp, ht, hg, hb, hl, hs⟩ := h
  exact ⟨pre, p, e, rest ++ post, by simp, hn, hp, ht, hg, hb, by simp; omega,
    by rw [List.take_append_of_le_length hl]; exact hs⟩

/-- Each entry `(p, s)` of `prints`, the `i`-th, is shown by the `i`-th item of `prog` that is a `print`,
`print e` at `p`, checked after the items before it, which stop at no error: `PrintJust`, read in the world `W`. -/
def PrintsShown (W : World) (phase : Nat) (table : Table) (prog : Program) (prints : List (Pos × String)) : Prop :=
  ∀ i p s, prints[i]? = some (p, s) → ∃ pre e post, prog = pre ++ .print p e :: post ∧
    pre.countP (· matches .print ..) = i ∧ (checkItems phase table pre).2 = none ∧
    PrintJust W (checkItems phase table pre).1 e s

theorem PrintsShown.extend {W W' : World} {phase : Nat} {table : Table} {prog : Program}
    {prints : List (Pos × String)} (hW : W.Le W') (post : List Top) (h : PrintsShown W phase table prog prints) :
    PrintsShown W' phase table (prog ++ post) prints := fun i p s hi => by
  obtain ⟨pre, e, rest, rfl, hc, hn, hj⟩ := h i p s hi
  exact ⟨pre, e, rest ++ post, by simp, hc, hn, hj.mono hW⟩

/-- The invariant of checking a program, item by item: a valuation meeting the top level's invariant at the final
state, whose first values satisfy the scope at the `qed` if the goal is proved (`ProvedAt`), and under which every
print listed is justified (`PrintsShown`); with no error, there is one print per `print`. -/
theorem checkItems_inv (phase : Nat) (table : Table) (prog : Program) :
    ∃ ρ, TopInv (checkItems phase table prog).1 ρ ∧
      ((checkItems phase table prog).2 = none → (checkItems phase table prog).1.proved = true →
        ∀ g, (checkItems phase table prog).1.goal = some g → ProvedAt phase table prog g ρ) ∧
      PrintsShown ((checkItems phase table prog).1.world ρ) phase table prog (checkItems phase table prog).1.prints ∧
      ((checkItems phase table prog).2 = none →
        (checkItems phase table prog).1.prints.length = prog.countP (· matches .print ..)) := by
  obtain ⟨l, rfl⟩ : ∃ l, prog = l.reverse := ⟨prog.reverse, by simp⟩
  induction l with
  | nil =>
    exact ⟨[], TopInv.init phase table, fun _ hp => by simp [checkItems, topItems, TopState.init] at hp,
      fun i p s hi => by simp [checkItems, topItems, TopState.init] at hi, fun _ => by simp [topItems, TopState.init]⟩
  | cons t l ih =>
    rw [List.reverse_cons]
    generalize l.reverse = pre at ih ⊢
    obtain ⟨ρ, hI, hP, hS, hL⟩ := ih
    by_cases hn : (checkItems phase table pre).2 = none
    · have he := topItems_append (h := .init phase table) [t] hn
      rcases hc : certify (topItem (checkItems phase table pre).1 (topItems_ok _ pre).runs t) with e | ⟨st', hs⟩
      · have hf : checkItems phase table (pre ++ [t]) = ({ (checkItems phase table pre).1 with
            snaps := (checkItems phase table pre).1.snaps ++ e.snaps }, some (e, t, 0)) := by
          simp only [checkItems] at he ⊢; rw [he]; simp [topItems, hc]
        rw [hf]
        exact ⟨ρ, hI.snaps _, by simp, by simpa [TopState.world_snaps] using hS.extend (World.Le.refl _) [t],
          by simp⟩
      · have hf : checkItems phase table (pre ++ [t]) = (st', none) := by
          simp only [checkItems] at he ⊢; rw [he]; simp [topItems, hc]
        rw [hf]
        obtain ⟨ρ', hle, hI', hpr⟩ := topItem_step hI hs
        refine ⟨ρ ++ ρ', hI', fun _ hp g hg => ?_, ?_, fun _ => ?_⟩
        · rcases topItem_proved hs hp with hp0 | ⟨⟨p, e, rfl⟩, ht⟩
          · obtain ⟨g0, hg0, -⟩ := hI.proved hp0
            rw [topItem_goal hs hg0] at hg
            obtain rfl := Option.some.inj hg
            exact (hP hn hp0 _ hg0).extend [t] ρ'
          · refine ⟨pre, p, e, [], rfl, by rw [hf], ?_⟩
            rw [hf]
            exact ⟨hp, ht, hg, (hI'.goal g hg).1, by simp [hI'.len], by
              rw [← hI'.len, List.take_length]; exact (hI'.live ht).sat⟩
        · rcases hpr with ⟨p, e, s, rfl, hps, hj⟩ | ⟨-, hps⟩
          · intro i q x hi
            rw [hps] at hi
            rcases Nat.lt_or_ge i (checkItems phase table pre).1.prints.length with hlt | hge
            · rw [List.getElem?_append_left hlt] at hi
              exact hS.extend hle [_] i q x hi
            · rw [List.getElem?_append_right hge] at hi
              obtain ⟨h0, hx⟩ : i - (checkItems phase table pre).1.prints.length = 0 ∧ (p, s) = (q, x) := by
                cases h' : i - (checkItems phase table pre).1.prints.length <;> simp_all
              cases hx
              exact ⟨pre, e, [], rfl, by rw [← hL hn]; omega, hn, hj⟩
          · rw [hps]; exact hS.extend hle [t]
        · rcases hpr with ⟨p, e, s, rfl, hps, -⟩ | ⟨ht, hps⟩
          · simp [hps, hL hn]
          · rw [hps, hL hn, List.countP_append]
            cases t <;> simp_all
    · obtain ⟨h1, h2⟩ := topItems_stop (h := .init phase table) [t] hn
      simp only [checkItems] at h1 h2 hI hS ⊢
      rw [h1]
      exact ⟨ρ, hI, fun h => absurd h h2, hS.extend (World.Le.refl _) [t], fun h => absurd h h2⟩

/-- What the theorems say of an outcome `out` of checking `prog` under `phase` with the table `table`, in the world
`W`: `W.P` is the evaluator's view of the program at the final state, `W.ρ` an ideal valuation of the final entries,
and `W.Sc` the program's signatures closed by it; `W.ρ` satisfies the final scope if that is untainted; if the goal is
reported proved, it was proved at a `qed` (`ProvedAt`) and holds (`GoalHolds`); every print listed is what its
`print` shows (`PrintsShown`); and with no error, every `print` is listed. -/
structure OutcomeSound (W : World) (phase : Nat) (table : Table) (prog : Program) (out : Outcome) : Prop where
  P : W.P = (checkItems phase table prog).1.prog
  Sc : W.Sc = out.sigs.map (Sig.close W.ρ)
  fns : W.P.fns = out.fns
  len : W.ρ.length = out.entries.length
  sat : out.tainted = false → Sat W.Sc out.entries W.ρ
  goal : out.goalProved = some true → ∃ g, out.goal = some g ∧ ProvedAt phase table prog g W.ρ ∧
    GoalHolds W phase g out.qedFn
  prints : PrintsShown W phase table prog out.prints
  allPrints : out.error = none → out.prints.length = prog.countP (· matches .print ..)

/-- Soundness of `runProgramWith`, with any table for the program's `_` (§20). -/
theorem runProgramWith_sound (phase : Nat) (table : Table) (prog : Program) (has : String → Bool)
    (err : Option (Pos × String)) : ∃ W, OutcomeSound W phase table prog (runProgramWith phase table prog has err) := by
  obtain ⟨ρ, hI, hat, hS, hL⟩ := checkItems_inv phase table prog
  refine ⟨(checkItems phase table prog).1.world ρ, ⟨rfl, rfl, rfl, hI.len,
    fun ht => (hI.live (by simpa [runProgramWith, outcome] using ht)).sat, fun hg => ?_, hS, fun he => hL (by
    revert he; simp only [runProgramWith, outcome]; cases (checkItems phase table prog).2 <;> simp)⟩⟩
  · simp only [runProgramWith, outcome] at hg ⊢
    split at hg
    · simp only [Option.some.injEq, Bool.and_eq_true, Option.isNone_iff_eq_none] at hg
      obtain ⟨g, hg', hW⟩ := hI.proved hg.2
      exact ⟨g, hg', hat hg.1.1 hg.2 g hg', by simpa [topItems_phase] using hW _ (World.Le.refl _)⟩
    · cases hg

theorem OutcomeSound.error {W : World} {phase : Nat} {table : Table} {prog : Program} {out : Outcome}
    {error : Option (Pos × String)} (h : OutcomeSound W phase table prog out) (he : error.isSome = out.error.isSome) :
    OutcomeSound W phase table prog { out with error } :=
  ⟨h.P, h.Sc, h.fns, h.len, h.sat, h.goal, h.prints, fun hn => h.allPrints (by
    cases hx : out.error <;> simp_all)⟩

/-- `report` keeps the item a stop is at and the number of items after it, and gives the checking pass's error, or one
the solver meets, not internal, solving that item from the same state, when the checking pass's was not found by
evaluating. -/
theorem report_spec (st : TopState) (s : Stop) : (report st s).2 = s.2 ∧ ((report st s).1 = s.1 ∨
    s.1.evaluated = false ∧ (report st s).1.internal = false ∧
      Solve.item st s.2.1 = .error (.failed (report st s).1)) := by
  obtain ⟨e, t, n⟩ := s
  unfold report
  by_cases hev : e.evaluated = true
  · simp [hev]
  · cases hs : Solve.item st t with
    | ok _ => simp [hev, hs]
    | error x =>
      cases x with
      | solved _ => simp [hev, hs]
      | failed e' => by_cases hi : e'.internal = true <;> simp [hev, hs, hi]

/-- `runProgram` reports what checking with the table solving ends with reports (`runProgramWith`), but for the error:
when checking stops at an error not found by evaluating, at an item `t`, the error reported may instead be one that
the solver meets solving `t` from the state checking reached before it, which is not internal. -/
theorem runProgram_eq (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String)) :
    ∃ error, runProgram phase prog has err = { runProgramWith phase (solution phase prog) prog has err with error } ∧
      (error = (runProgramWith phase (solution phase prog) prog has err).error ∨
        ∃ e t n e', (checkItems phase (solution phase prog) prog).2 = some (e, t, n) ∧ e.evaluated = false ∧
          e'.internal = false ∧ Solve.item (checkItems phase (solution phase prog) prog).1 t = .error (.failed e') ∧
          error = some (e'.pos, e'.msg ())) := by
  unfold runProgram runProgramWith
  rcases hc : checkItems phase (solution phase prog) prog with ⟨st, _ | s⟩
  · exact ⟨_, rfl, .inl rfl⟩
  · obtain ⟨hs, hr⟩ := report_spec st s
    obtain ⟨e, t, n⟩ := s
    generalize hrep : report st (e, t, n) = r at hs hr
    obtain ⟨e', t', n'⟩ := r
    simp only [Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨some (e'.pos, e'.msg ()), by simp [outcome, hrep], ?_⟩
    rcases hr with rfl | ⟨hev, hi, hs⟩
    · exact .inl (by simp [outcome])
    · exact .inr ⟨e, t', n', e', rfl, hev, hi, hs, rfl⟩

theorem runProgram_isSome (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String)) :
    ∃ error : Option (Pos × String),
      error.isSome = (runProgramWith phase (solution phase prog) prog has err).error.isSome ∧
      runProgram phase prog has err = { runProgramWith phase (solution phase prog) prog has err with error } := by
  obtain ⟨error, he, hc⟩ := runProgram_eq phase prog has err
  refine ⟨error, ?_, he⟩
  rcases hc with rfl | ⟨e, t, n, e', hf, -, -, -, rfl⟩
  · rfl
  · simp [runProgramWith, outcome, hf]

/-- Soundness of the checker and evaluator, for every program (`_`, `sorry` and multiplicities included), under any
phase (`OutcomeSound`): there is an ideal valuation `W.ρ` of the final top-level entries, the
program's signatures closed by it typing values, with `W.P` the evaluator's view of the program; it satisfies the
final scope if that scope is untainted (`tainted` is false); if the goal is reported proved,
the first values of `W.ρ` satisfy the scope at the `qed` that proved it (`ProvedAt`), and the goal holds
(`GoalHolds`): a type goal's type has a value of type `Type()` that some value has as its type, and the function a
`qed` names computes, from run-time arguments related to ideal ones satisfying a function goal's parameters,
run-time results related to ideal ones satisfying its returns; and each print is `sorry` for a tainted result, or
else shows the run-time value its `print`'s checked tree evaluates to, related to the ideal value of its result. -/
theorem runProgram_sound (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String)) :
    ∃ W, OutcomeSound W phase (solution phase prog) prog (runProgram phase prog has err) := by
  obtain ⟨_, he, h⟩ := runProgram_isSome phase prog has err
  obtain ⟨W, hW⟩ := runProgramWith_sound phase (solution phase prog) prog has err
  exact ⟨W, h ▸ hW.error he⟩

theorem runProgram_proved {phase : Nat} {prog : Program} {has : String → Bool} {err : Option (Pos × String)}
    (h : (runProgram phase prog has err).goalProved = some true) :
    (checkItems phase (solution phase prog) prog).2 = none ∧
      (checkItems phase (solution phase prog) prog).1.proved = true := by
  obtain ⟨_, -, he⟩ := runProgram_isSome phase prog has err
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
  obtain ⟨W, -, hSc, -, hl, hsat, hgoal, -⟩ := runProgram_sound phase prog has err
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
  obtain ⟨W, hP, hSc, hF, hl, hsat, hgoal, -⟩ := runProgram_sound phase prog has err
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
    ∃ W, OutcomeSound W phase (solution phase (parse source phase).1) (parse source phase).1 (run source phase) :=
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
  obtain ⟨ρ₁, -, hI₁⟩ := topItems_sound (h := .init _ _) (ρ := []) (prog := pre) (TopInv.init phase _)
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
  obtain ⟨C₁, r, hr, rfl⟩ := annotate_type hann
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

/-- A top-level statement other than a `comptime` pattern `let`, at the state checking any items `pre` with any table
for their `_` (§20) reaches, that passes: its scope is the checked statement's, and its run (`EvalStmt`) gives the
new values of the top-level names, unless it leaves the scope tainted (§12), when it runs nothing. -/
theorem reached_stmt (phase : Nat) (table : Table) {pre : Program} {s : Stmt}
    (hs : ∀ p m pat rhs, s ≠ .patlet p true m pat rhs) {hw : _}
    {st' : TopState} (h : topItem (checkItems phase table pre).1 hw (.stmt s) = .ok st') :
    ∃ o, checkStmt (checkItems phase table pre).1.ctx (checkItems phase table pre).1.sc s = .ok o ∧ st'.sc = o.sc ∧
      (o.sc.taintedBy = none →
        EvalStmt (checkItems phase table pre).1.prog (checkItems phase table pre).1.env o.tree st'.env) ∧
      (o.sc.taintedBy.isSome → st'.env = (checkItems phase table pre).1.env) := by
  obtain ⟨ρ, hI, -⟩ := checkItems_inv phase table pre
  have ht : topItem (checkItems phase table pre).1 hw (.stmt s) = topStmt _ hw s := by
    cases s with
    | patlet p ct m pat rhs => cases ct; rfl; exact absurd rfl (hs p m pat rhs)
    | _ => rfl
  rw [ht] at h
  unfold topStmt at h
  obtain ⟨⟨o, ho⟩, -, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨o, ho, rfl, fun hto => ?_, fun hto => by simp [hto]⟩
  simp only [hto, Option.isSome_none, Bool.false_eq_true, ↓reduceDIte]
  exact TopState.run_cert

/-- A `qed` against a type goal `t`, at the state checking any items `pre` with any table reaches, that passes:
it checks its expression given the goal, and if the scope after it is untainted, the expression has one result, and
when that is untainted, its checked tree has an evaluation (`Eval`) to a run-time value related (`Rel`) to an ideal
value of type `t`, under an ideal valuation `ρ` satisfying the scope; `TopState.eval` would return that value. -/
theorem reached_qed (phase : Nat) (table : Table) {pre : Program} {p : Pos} {e : Expr} {goal : CheckedGoal} {t : Term}
    (hgoal : (checkItems phase table pre).1.goal = some goal)
    (hk : goal.kind = .type t) {hw : _} {st' : TopState}
    (h : topItem (checkItems phase table pre).1 hw (.qed p e) = .ok st') :
    let st := (checkItems phase table pre).1
    ∃ o, checkExpr st.ctx st.sc (some goal.given) e = .ok o ∧ st'.sc = o.sc ∧
      (o.sc.taintedBy = none → ∃ r, o.res = [r] ∧ (r.tainted = false → ∃ ρ a v V,
        Sat (st.world ρ).Sc st.sc.Γ ρ ∧ Eval st.prog st.env o.tree [a] ∧ Rel (st.world ρ).Sc phase a v ∧
        HasType (st.world ρ).Sc v V ∧ t.eval ρ [] = some V ∧ ∀ hw, st.eval o.tree r.tainted hw = some a)) := by
  intro st
  obtain ⟨ρ, hI, -⟩ := checkItems_inv phase table pre
  have hph := topItems_phase phase table pre
  have hq : ∃ o, checkExpr st.ctx st.sc (some goal.given) e = .ok o ∧ st'.sc = o.sc := by
    simp only [topItem] at h
    split at h
    · simp [failAt_eq, bind, Except.bind] at h
    split at h
    · rename_i goal' hgoal'
      rw [hgoal] at hgoal'
      cases hgoal'
      split at h
      · rename_i hk'; rw [hk] at hk'; cases hk'
      · have hq : ∀ x, (do
            let o ← checkExpr st.ctx st.sc (some goal.given) e
            let st ← pure { st with sc := o.sc, proved := !o.res.any fun x => x.tainted, snaps := st.snaps ++ o.snaps }
            pure { st with qedChecks := true, proved := st.proved && st.sc.taintedBy.isNone && !goal.tainted } :
            CheckM TopState) = .ok x → ∃ o, checkExpr st.ctx st.sc (some goal.given) e = .ok o ∧
              x.sc = o.sc := fun x hx => by
          obtain ⟨o, ho, hx⟩ := bind_eq_ok.1 hx
          cases hx
          exact ⟨o, ho, rfl⟩
        split at h
        · split at h
          · simp [failAt_eq, bind, Except.bind] at h
          · exact hq _ h
        · exact hq _ h
    · simp [failAt_eq] at h
  obtain ⟨o, ho₀, hsc⟩ := hq
  refine ⟨o, ho₀, hsc, fun hto => ?_⟩
  have ho := ho₀
  have ht := TopStmt.none_of (Expr.shape e _ st.sc _ o ho).2.2.2 hto
  obtain ⟨_, vs, -, -, -, hws, -⟩ := (Expr.sound e _ _ _ _ _ _ _ _ (hI.inv ht rfl rfl rfl)
    (fun g' hg' => by cases hg'; exact TopStmt.given_ok hI ht hgoal hk) ho).1 hto
  have hws := hws _ rfl [] (by rw [TopStmt.given_eq hk]; rfl)
  rw [TopStmt.given_eq hk] at hws
  obtain ⟨r, hr⟩ : ∃ r, o.res = [r] := by
    generalize o.res = rs at hws
    rcases rs with _ | ⟨r, _ | ⟨r', rs⟩⟩ <;> rcases vs with _ | ⟨v, _ | ⟨v', vs⟩⟩
    all_goals first | exact hws.elim | exact hws.2.elim | exact ⟨r, rfl⟩
  refine ⟨r, hr, fun hrt => ?_⟩
  obtain ⟨ρ₁, a, v, V, -, hsat, -, hev, hR, hV, -, hW, heval⟩ :=
    hI.eval_ok (pl := st.ctx.place) (.inr ⟨goal, t, hgoal, hk, rfl⟩) ho₀ (by rw [hr]; rfl) hrt
  have hW := hW _ rfl [] (by rw [TopStmt.given_eq hk]; rfl)
  rw [TopStmt.given_eq hk] at hW
  obtain ⟨A, hA, -, -, hvA⟩ := hW.1.1 t rfl
  obtain rfl := hV.unique (hvA rfl)
  rw [hph] at hR
  refine ⟨ρ, a, v, V, hsat, hev, hR, hV, ?_, heval⟩
  rw [Term.eval_entriesBelow (ρ' := ρ ++ ρ₁) (n := ρ.length) (by simp) [] t
    (by rw [hI.len]; exact (hI.goal goal hgoal).1.type hk)]
  exact hA

theorem bind_eq_error {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {e : ε} :
    (x >>= f) = .error e ↔ x = .error e ∨ ∃ a, x = .ok a ∧ f a = .error e := by
  cases x <;> simp [bind, Except.bind]

theorem keep_eq_error {α : Type} {snaps : List Snapshot} {x : CheckM α} {e : CheckError} (h : keep snaps x = .error e) :
    ∃ e0 : CheckError, x = .error e0 ∧ e = { e0 with snaps := snaps ++ e0.snaps } := by
  cases x with
  | ok => cases h
  | error e0 => exact ⟨e0, rfl, (Except.error.inj h).symm⟩

/-- A `comptime` pattern `let C(...) = rhs;`, at the state checking any items `pre` with any table reaches, whose
right-hand side checks with one untainted result: its checked tree has an evaluation (`Eval`) to a run-time value
`a` related (`Rel`) to a typed ideal value, under an ideal valuation `ρ` satisfying the scope, which `TopState.eval`
returns; if the item passes, `a` is headed by `C` and, unless the scope after it is tainted (§12), the new values of
the top-level names are `a`'s fields (`bindPattern`); and if `a` is not headed by `C`, once forcing `C` succeeds, the
item fails with the error that shows `a` (§11). -/
theorem reached_comptime (phase : Nat) (table : Table) {pre : Program} {p : Pos} {m : Option Mult} {pat : Pattern}
    {rhs : Expr} {o : Out} {r : Res}
    (h : checkExpr (checkItems phase table pre).1.ctx (checkItems phase table pre).1.sc none rhs = .ok o)
    (hr : single rhs.pos o.res = .ok r) (hrt : r.tainted = false) :
    let st := (checkItems phase table pre).1
    ∃ ρ a v V, Sat (st.world ρ).Sc st.sc.Γ ρ ∧ Eval st.prog st.env o.tree [a] ∧ Rel (st.world ρ).Sc phase a v ∧
      HasType (st.world ρ).Sc v V ∧ (∀ hw, st.eval o.tree r.tainted hw = some a) ∧
      (∀ hw st', topItem st hw (.stmt (.patlet p true m pat rhs)) = .ok st' →
        a.headName = pat.ctor.name ∧ (st'.sc.taintedBy = none → bindPattern st.env m pat a = .ok st'.env)) ∧
      (∀ hw fs, m ≠ some .erased → freshAll st.ctx st.sc pat.fields = .ok () →
        forcings st.ctx o.sc r.term rhs.pos [pat] p false = .ok fs → a.headName ≠ pat.ctor.name →
        ∃ err, topItem st hw (.stmt (.patlet p true m pat rhs)) = .error err ∧ err.evaluated = true ∧
          err.pos = rhs.pos ∧
          err.msg () =
            s!"this evaluates to {code (showValue a)}, which is not headed by {code pat.ctor.name} (§11)") := by
  intro st
  obtain ⟨ρ, hI, -⟩ := checkItems_inv phase table pre
  have hph := topItems_phase phase table pre
  obtain ⟨ρ₁, a, v, V, -, hsat, -, hev, hR, hV, -, -, heval⟩ := hI.eval_ok (pl := st.ctx.place) (.inl rfl) h hr hrt
  rw [hph] at hR
  have hpass : ∀ hw st', topItem st hw (.stmt (.patlet p true m pat rhs)) = .ok st' →
      a.headName = pat.ctor.name ∧ (st'.sc.taintedBy = none → bindPattern st.env m pat a = .ok st'.env) := by
    intro hw st' h'
    simp only [topItem] at h'
    unfold comptimeLet at h'
    simp only at h'
    split at h'
    · simp [failAt_eq, bind, Except.bind] at h'
    obtain ⟨-, -, h'⟩ := bind_eq_ok.1 h'
    obtain ⟨⟨o', ho'⟩, -, h'⟩ := bind_eq_ok.1 h'
    obtain rfl : o = o' := Except.ok.inj (h.symm.trans ho')
    dsimp only at h'
    rw [keep_ok] at h'
    obtain ⟨⟨r', hr'⟩, -, h'⟩ := bind_eq_ok.1 h'
    obtain rfl : r = r' := Except.ok.inj (hr.symm.trans hr')
    obtain ⟨fs, -, h'⟩ := bind_eq_ok.1 h'
    generalize hv' : TopState.eval st o.tree r.tainted _ = v' at h'
    rw [heval] at hv'
    subst hv'
    simp only at h'
    split at h'
    · simp [evalFail_eq, bind, Except.bind] at h'
    rename_i hhead
    refine ⟨by simpa using hhead, fun ht => ?_⟩
    obtain ⟨sc, -, h'⟩ := bind_eq_ok.1 h'
    split at h'
    · simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h'
      subst h'
      simp_all
    · split at h'
      · rename_i env henv
        simp only [pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h'
        subst h'
        exact henv
      · simp [evalFail_eq, bind, Except.bind] at h'
  refine ⟨ρ, a, v, V, hsat, hev, hR, hV, heval, hpass, fun hw fs hm hfr hfs hhead => ?_⟩
  cases hres : topItem st hw (.stmt (.patlet p true m pat rhs)) with
  | ok st' => exact absurd (hpass hw st' hres).1 hhead
  | error err =>
    refine ⟨err, rfl, ?_⟩
    simp only [topItem] at hres
    unfold comptimeLet at hres
    simp only at hres
    split at hres
    · simp_all
    rw [bind_eq_error] at hres
    rcases hres with hres | ⟨_, -, hres⟩
    · rw [hfr] at hres; cases hres
    rw [bind_eq_error] at hres
    rcases hres with hres | ⟨⟨o', ho'⟩, -, hres⟩
    · rw [h] at hres; simp [certify] at hres
    obtain rfl : o = o' := Except.ok.inj (h.symm.trans ho')
    dsimp only at hres
    obtain ⟨e0, hk, rfl⟩ := keep_eq_error hres
    rw [bind_eq_error] at hk
    rcases hk with hk | ⟨⟨r', hr'⟩, -, hk⟩
    · rw [hr] at hk; simp [certify] at hk
    obtain rfl : r = r' := Except.ok.inj (hr.symm.trans hr')
    rw [bind_eq_error] at hk
    rcases hk with hk | ⟨fs', hfs', hk⟩
    · rw [hfs] at hk; cases hk
    generalize hv' : TopState.eval st o.tree r.tainted _ = v' at hk
    rw [heval] at hv'
    subst hv'
    simp only [show (a.headName != pat.ctor.name) = true by simpa using hhead, ↓reduceIte, evalFail_eq,
      bind, Except.bind, Except.error.injEq] at hk
    subst hk
    exact ⟨rfl, rfl, rfl⟩

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
