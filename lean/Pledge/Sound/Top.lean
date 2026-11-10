import Pledge.Sound.Stmt
import Pledge.Sound.Fn
import Pledge.Sound.Data

namespace Pledge

theorem TopInv.init (phase : Nat) : TopInv (TopState.init phase) [] := by
  sorry

/-- A group of `data` declarations, none named `sorry`, adds closed signatures that keep the top level's
invariant. -/
theorem dataGroup_sound {st st' : TopState} {ρ : List Value} {ds : List Data} (hI : TopInv st ρ)
    (hp : ds.all Data.holeFree = true) (h : dataGroup st ds = .ok st') :
    (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ := by
  obtain ⟨_, hg⟩ := dataGroup_group h
  refine ⟨hg.le hI, hg.topInv hI fun n hn hj => ?_⟩
  rcases List.mem_append.1 hn with hn | hn
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hn
    have := List.all_eq_true.1 hp d hd
    simp [Data.holeFree, hj] at this
  · obtain ⟨⟨T, c⟩, hc, rfl⟩ := List.mem_map.1 hn
    simp only [groupCtors, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨d, hd, k, hk, he⟩ := hc
    cases he
    have := List.all_eq_true.1 hp d hd
    simp only [Data.holeFree, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at this
    exact this.2 k hk hj

theorem fnGroup_sound {st st' : TopState} {ρ : List Value} {fs : List Fn} (hI : TopInv st ρ)
    (hp : fs.all (·.body.holeFree) = true) (h : fnGroup st fs = .ok st') :
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
    obtain ⟨h1, h2⟩ := dataGroup_sound hI (by simpa [Top.holeFree] using hp) h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | mutualData _ ds =>
    obtain ⟨h1, h2⟩ := dataGroup_sound hI (by simpa [Top.holeFree] using hp) h
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
    obtain ⟨h1, h2⟩ := goalItem_sound hI h
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

/-- Checking keeps the phase. -/
theorem topItems_phase (phase : Nat) (prog : Program) : (topItems (.init phase) prog).1.phase = phase := by
  sorry

/-- Soundness of the checker and evaluator, for programs with `sorry` and multiplicities but no `_` argument
(§12, §16), under any phase: there is an ideal valuation `W.ρ` of the final top-level entries, the program's
signatures closed by it typing values, with `W.P` the evaluator's view of the program; it satisfies the final
scope if that scope is untainted; and if the goal is reported proved, it holds there (`GoalHolds`): a type goal's
type has a value, and the function a `qed` names computes, from run-time arguments related to ideal ones
satisfying a function goal's parameters, run-time results related to ideal ones satisfying its returns. -/
theorem runProgram_sound (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String))
    (hp : Program.holeFree prog = true) :
    ∃ W : World, W.P = (topItems (.init phase) prog).1.prog ∧
      W.Sc = (runProgram phase prog has err).sigs.map (Sig.close W.ρ) ∧
      W.P.fns = (runProgram phase prog has err).fns ∧ W.ρ.length = (runProgram phase prog has err).entries.length ∧
      ((topItems (.init phase) prog).1.sc.taintedBy = none → Sat W.Sc (runProgram phase prog has err).entries W.ρ) ∧
      ((runProgram phase prog has err).goalProved = some true → ∃ g, (runProgram phase prog has err).goal = some g ∧
        GoalHolds W phase g (runProgram phase prog has err).qedFn) := by
  obtain ⟨ρ, -, hI⟩ := topItems_sound (ρ := []) (prog := prog) (TopInv.init phase) hp
  simp only [List.nil_append] at hI
  refine ⟨(topItems (.init phase) prog).1.world ρ, rfl, rfl, rfl, hI.len, fun ht => (hI.live ht).sat, fun hg => ?_⟩
  simp only [runProgram] at hg ⊢
  split at hg
  · simp only [Option.some.injEq, Bool.and_eq_true] at hg
    obtain ⟨g, hg', hW⟩ := hI.proved hg.2
    exact ⟨g, hg', by simpa [topItems_phase] using hW _ (World.Le.refl _)⟩
  · cases hg

/-- A proved type goal has a value: under an ideal valuation `ρ` of the final top-level entries, the goal's type
`t` evaluates to a type `V`, and some value has type `V` by the program's signatures closed by `ρ`. -/
theorem type_goal_inhabited (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String))
    (hp : Program.holeFree prog = true) {g : CheckedGoal} {t : Term}
    (hproved : (runProgram phase prog has err).goalProved = some true)
    (hg : (runProgram phase prog has err).goal = some g) (ht : g.kind = .type t) :
    ∃ ρ, ρ.length = (runProgram phase prog has err).entries.length ∧
      ∃ v V, t.eval ρ [] = some V ∧ HasType ((runProgram phase prog has err).sigs.map (Sig.close ρ)) v V := by
  obtain ⟨W, -, hSc, -, hl, -, hgoal⟩ := runProgram_sound phase prog has err hp
  obtain ⟨g', hg', hh⟩ := hgoal hproved
  rw [hg] at hg'
  cases hg'
  simp only [GoalHolds, ht] at hh
  rw [hSc] at hh
  exact ⟨W.ρ, hl, hh⟩

/-- A proved function goal holds: under an ideal valuation `ρ` of the final top-level entries, the function `n` the
`qed` names, `d` to the evaluator, takes every list of values satisfying the goal's parameters `ps` to values
satisfying its returns `rs`: running `d` on those values, or on any run-time values related to them by the
parameters' multiplicities, returns run-time results related to them by the returns' multiplicities. -/
theorem fn_goal_holds (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String))
    (hp : Program.holeFree prog = true) {g : CheckedGoal} {ps rs : Telescope}
    (hproved : (runProgram phase prog has err).goalProved = some true)
    (hg : (runProgram phase prog has err).goal = some g) (hk : g.kind = .fn ps rs) :
    ∃ ρ n d, ρ.length = (runProgram phase prog has err).entries.length ∧
      (runProgram phase prog has err).qedFn = some n ∧ (runProgram phase prog has err).fns.find n = some d ∧
      ∀ vs, TeleSat ((runProgram phase prog has err).sigs.map (Sig.close ρ)) ρ ps [] vs →
        ∃ ws, TeleSat ((runProgram phase prog has err).sigs.map (Sig.close ρ)) ρ rs vs ws ∧
          ∀ as, MultsRel ((runProgram phase prog has err).sigs.map (Sig.close ρ)) phase (ps.map (·.mult)) as vs →
            ∃ ws', CallRel (topItems (.init phase) prog).1.prog d as ws' ∧
              MultsRel ((runProgram phase prog has err).sigs.map (Sig.close ρ)) phase (rs.map (·.mult)) ws' ws := by
  obtain ⟨W, hP, hSc, hF, hl, -, hgoal⟩ := runProgram_sound phase prog has err hp
  obtain ⟨g', hg', hh⟩ := hgoal hproved
  rw [hg] at hg'
  cases hg'
  simp only [GoalHolds, hk] at hh
  obtain ⟨n, d, hn, hd, hh⟩ := hh
  rw [hSc] at hh
  rw [hP] at hh
  exact ⟨W.ρ, n, d, hl, hn, by rw [← hF]; exact hd, hh⟩

/-- `runProgram_sound` for source text whose parsed program has no `_` argument. -/
theorem run_sound (source : String) (phase : Nat) (hp : Program.holeFree (parse source phase).1 = true) :
    ∃ W : World, W.Sc = (run source phase).sigs.map (Sig.close W.ρ) ∧ W.P.fns = (run source phase).fns ∧
      ((run source phase).goalProved = some true →
        ∃ g, (run source phase).goal = some g ∧ GoalHolds W phase g (run source phase).qedFn) := by
  obtain ⟨W, -, h1, h2, -, -, h3⟩ := runProgram_sound phase _ (hasKeyword source phase) (parse source phase).2 hp
  exact ⟨W, h1, h2, h3⟩

/-- The "no `False`" corollary, with `sorry` allowed: a program that declares a data type with no value
constructors and sets as its goal an application of it is never reported to prove that goal. -/
theorem no_empty_goal (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String))
    (hp : Program.holeFree prog = true) (d : Data)
    (hd : Top.data d ∈ prog ∨ ∃ p ds, Top.mutualData p ds ∈ prog ∧ d ∈ ds)
    (hc : d.ctors = []) (p : Pos) (hn : Name) (args : List WTerm) (hg : Top.goal p (.type (.app hn args)) ∈ prog)
    (hname : hn.name = d.name.name) : (runProgram phase prog has err).goalProved ≠ some true := by
  sorry

/-- `no_empty_goal` for source text whose parsed program has no `_` argument. -/
theorem run_no_empty_goal (source : String) (phase : Nat) (hp : Program.holeFree (parse source phase).1 = true)
    (d : Data) (hd : Top.data d ∈ (parse source phase).1 ∨ ∃ p ds, Top.mutualData p ds ∈ (parse source phase).1 ∧ d ∈ ds)
    (hc : d.ctors = []) (p : Pos) (hn : Name) (args : List WTerm)
    (hg : Top.goal p (.type (.app hn args)) ∈ (parse source phase).1) (hname : hn.name = d.name.name) :
    (run source phase).goalProved ≠ some true :=
  no_empty_goal phase _ _ _ hp d hd hc p hn args hg hname

/-- Evaluation at a state `st` the checker reaches on a program without `_` arguments, while its scope is untainted
(§12): an expression checked there at the top level with an untainted result, as `print`, `qed` against a type goal
and a `comptime` pattern `let` check theirs, has an evaluation (`Eval`) to one run-time value related (`Rel`) to a
typed ideal value; any value `TopState.eval` returns for it is that one. `TopState.eval` runs the `partial`
evaluator, so this does not establish that it returns a value rather than an error, or that it returns at all. -/
theorem reached_eval_ok (phase : Nat) {pre : Program} (hp : Program.holeFree pre = true) {st : TopState}
    (hst : st = (topItems (.init phase) pre).1) (ht : st.sc.taintedBy = none) {C : Ctx} {g : Option Given} {e : Expr}
    {o : Out} {r : Res} (hph : C.phase = phase) (her : C.erased = false) (hgl : C.globals = st.globals)
    (hfn : C.fn = none) (hg : ∀ g', g = some g' → g'.env = [] ∧ ∀ w ∈ g'.wants, w.mult = .many ∧ w.is = none ∧
      ∀ t, w.type = some t → t.entriesBelow st.sc.Γ.length = true)
    (he : e.holeFree = true) (h : checkExpr C st.sc g e = .ok o) (hr : single e.pos o.res = .ok r)
    (hrt : r.tainted = false) :
    ∃ ρ a v V, Eval st.prog st.env o.tree [a] ∧ Rel (st.world ρ).Sc phase a v ∧ HasType (st.world ρ).Sc v V := by
  sorry

/-- At a state `st` the checker reaches on a program without `_` arguments, while its scope is untainted, a
statement checked there at the top level that leaves the scope untainted has a run (`EvalStmt`). -/
theorem reached_run_ok (phase : Nat) {pre : Program} (hp : Program.holeFree pre = true) {st : TopState}
    (hst : st = (topItems (.init phase) pre).1) (ht : st.sc.taintedBy = none) {C : Ctx} {s : Stmt} {o : StmtOut}
    (hph : C.phase = phase) (her : C.erased = false) (hgl : C.globals = st.globals) (hfn : C.fn = none)
    (hs : s.holeFree = true) (h : checkStmt C st.sc s = .ok o) (ht' : o.sc.taintedBy = none) :
    ∃ env, EvalStmt st.prog st.env o.tree env := by
  sorry

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

end Pledge
