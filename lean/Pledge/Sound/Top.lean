import Pledge.Sound.Stmt

namespace Pledge

theorem Act.top_group {F : Fns} {d : FnDef} (h : d ∈ F) : d.group < (Act.top F).group := by
  simp only [Act.top]
  induction F with
  | nil => cases h
  | cons e F ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem TopInv.sigsClose {st : TopState} {ρ : List Value} (hI : TopInv st ρ) :
    SigsClose st.sc.sigs ρ (st.world ρ).Sc :=
  SigsClose.close hI.sat.noRemoved

/-- Top-level code is checked under the main lemma's invariant, in the world of the state. -/
theorem TopInv.inv {st : TopState} {ρ : List Value} {C : Ctx} (hI : TopInv st ρ) (hph : C.phase = 1)
    (her : C.erased = false) (hgl : C.globals = st.globals) (hfn : C.fn = none) :
    Inv C st.sc st.sc.Γ.length (st.world ρ) ρ st.env (Act.top st.fns) := by
  have hl : ρ.length = st.sc.Γ.length := hI.sat.1
  refine ⟨hph, her, hI.sat, by simp [TopState.world, hl], rfl, fun ρ' hρ' => ?_, hI.sigsOk, hI.names, ?_,
    fun f hf => by simp [hfn] at hf, hI.inert⟩
  · refine hI.sigsClose.of_entriesBelow (n := st.sc.Γ.length) ?_ fun sig hs => (hI.sigsOk sig hs).1
    simpa [TopState.world] using hρ'.symm
  · rw [hgl, hfn]
    exact hI.globals _ (World.Le.refl _) _ fun d hd => Act.top_group hd

theorem TopInv.init : TopInv (TopState.init 1) [] := by
  have hTy : Sigs.find [⟨Head.Type, [], Term.TYPE⟩] Head.Type = some ⟨Head.Type, [], Term.TYPE⟩ := by
    simp [Sigs.find]
  refine ⟨rfl, ⟨rfl, fun i en h => by simp [TopState.init] at h⟩,
    fun n r h => by simp [TopState.init, Scope.lookup] at h,
    ⟨rfl, rfl, by simp [TopState.init]⟩, ?_, ?_, ?_, by simp [TopState.init], by simp [TopState.init], ?_,
    by simp [TopState.init], by simp [TopState.init]⟩
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
      exact ⟨HeadOk.mono hW ⟨by simp [TopState.world, Fns.find, TopState.init],
        by simp [TopState.world, kindOf, TopState.init, Global.name], _, hTy⟩, by simp⟩
    · cases hg

/-- A group of `data` declarations adds closed signatures that keep the top level's invariant. -/
theorem dataGroup_sound {st st' : TopState} {ρ : List Value} {ds : List Data} (hI : TopInv st ρ)
    (hp : ds.all Data.plain = true) (h : dataGroup st ds = .ok st') : (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ := by
  sorry

/-- A group of functions keeps the top level's invariant: in every later world, each of its functions meets its
specification (`FnSpec`), by well-founded induction on the measure of its activations (`Act.lt_wf`), applying the
main lemma `Expr.sound` to its body. -/
theorem fnGroup_sound {st st' : TopState} {ρ : List Value} {fs : List Fn} (hI : TopInv st ρ)
    (hp : fs.all Fn.plain = true) (h : fnGroup st fs = .ok st') : (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ := by
  sorry

/-- A top-level statement, `comptime` pattern `let` included (§11), keeps the invariant for the valuation extended
by the values of its new entries. -/
theorem topStmt_sound {st st' : TopState} {ρ : List Value} {s : Stmt} (hI : TopInv st ρ) (hp : s.plain = true)
    (h : topItem st (.stmt s) = .ok st') : ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  have hInv := hI.inv (C := st.ctx) hI.phase rfl rfl rfl
  cases s with
  | patlet p ct m pat rhs =>
    cases ct
    · exact checkedStmt_sound hI hInv hp h
    · simp only [Stmt.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
      obtain ⟨rfl, hp⟩ := hp
      exact comptimeLet_sound hI hInv hp h
  | _ => exact checkedStmt_sound hI hInv hp h

theorem print_sound {st st' : TopState} {ρ : List Value} {p : Pos} {e : Expr} (hI : TopInv st ρ)
    (hp : e.plain = true) (h : topItem st (.print p e) = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  exact print_sound' hI (hI.inv hI.phase rfl rfl rfl) hp h

theorem goal_sound {st st' : TopState} {ρ : List Value} {p : Pos} {g : Goal} (hI : TopInv st ρ)
    (hp : g.plain = true) (h : topItem st (.goal p g) = .ok st') : (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ := by
  sorry

/-- A `qed` that checks proves the goal in every later world: for `qed e;`, `e`'s value has the goal's type; for
`qed f;`, `f`'s telescopes agree with the goal's (`difference … = none`) and `f` meets its specification. -/
theorem qed_sound {st st' : TopState} {ρ : List Value} {p : Pos} {e : Expr} (hI : TopInv st ρ)
    (hp : e.plain = true) (h : topItem st (.qed p e) = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  exact qed_sound' hI (hI.inv hI.phase rfl rfl rfl) hp h

theorem TopState.world_snaps (st : TopState) (snaps : List Snapshot) (ρ : List Value) :
    ({ st with snaps } : TopState).world ρ = st.world ρ := rfl

theorem TopInv.snaps {st : TopState} {ρ : List Value} (hI : TopInv st ρ) (snaps : List Snapshot) :
    TopInv { st with snaps } ρ := by
  cases hI; constructor <;> assumption

theorem topItem_sound {st st' : TopState} {ρ : List Value} {t : Top} (hI : TopInv st ρ) (hp : t.plain = true)
    (h : topItem st t = .ok st') : ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  cases t with
  | data d =>
    obtain ⟨h1, h2⟩ := dataGroup_sound hI (by simpa [Top.plain] using hp) h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | mutualData _ ds =>
    obtain ⟨h1, h2⟩ := dataGroup_sound hI (by simpa [Top.plain] using hp) h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | fn f =>
    obtain ⟨h1, h2⟩ := fnGroup_sound hI (by simpa [Top.plain] using hp) h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | mutualFn _ fs =>
    obtain ⟨h1, h2⟩ := fnGroup_sound hI (by simpa [Top.plain] using hp) h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | stmt s => exact topStmt_sound hI hp h
  | print p e => exact print_sound hI hp h
  | goal p g =>
    obtain ⟨h1, h2⟩ := goal_sound hI hp h
    exact ⟨[], by simpa using h1, by simpa using h2⟩
  | qed p e => exact qed_sound hI hp h

theorem topItems_sound {ρ : List Value} : ∀ {st : TopState} {prog : Program}, TopInv st ρ → Program.plain prog = true →
    ∃ ρ', (st.world ρ).Le ((topItems st prog).1.world (ρ ++ ρ')) ∧ TopInv (topItems st prog).1 (ρ ++ ρ')
  | st, [], hI, _ => ⟨[], by simpa [topItems] using World.Le.refl _, by simpa [topItems] using hI⟩
  | st, t :: ts, hI, hp => by
    simp only [Program.plain, List.all_cons, Bool.and_eq_true] at hp
    simp only [topItems]
    split
    · rename_i st' h
      obtain ⟨ρ₁, hle, hI'⟩ := topItem_sound hI hp.1 h
      obtain ⟨ρ₂, hle', hI''⟩ := topItems_sound (ρ := ρ ++ ρ₁) (prog := ts) hI' hp.2
      exact ⟨ρ₁ ++ ρ₂, by simpa using hle.trans hle', by simpa using hI''⟩
    · exact ⟨[], by simpa [TopState.world_snaps] using World.Le.refl _, by simpa using hI.snaps _⟩

/-- Stage 1 soundness of the checker and evaluator, for phase 1 programs without `sorry` or written
multiplicities: there is a world (closed signatures, the evaluator's program and values of the top-level entries)
in which the final top-level scope is satisfied, and, if the goal is reported proved, the goal holds in it: a type
goal's type has a value, and a function goal's parameters, whenever satisfied, have returns satisfying its return
telescope. This is meant to say that the checker accepts no proof of an uninhabited type. -/
theorem runProgram_sound (prog : Program) (has : String → Bool) (err : Option (Pos × String))
    (hp : Program.plain prog = true) :
    ∃ W : World, Sat W.Sc (runProgram 1 prog has err).entries W.ρ ∧
      SigsClose (runProgram 1 prog has err).sigs W.ρ W.Sc ∧ W.P.fns = (runProgram 1 prog has err).fns ∧
      ((runProgram 1 prog has err).goalProved = some true →
        ∃ g, (runProgram 1 prog has err).goal = some g ∧ GoalHolds W g) := by
  obtain ⟨ρ, -, hI⟩ := topItems_sound (ρ := []) (prog := prog) TopInv.init hp
  simp only [List.nil_append] at hI
  refine ⟨(topItems (.init 1) prog).1.world ρ, hI.sat, hI.sigsClose, rfl, fun hg => ?_⟩
  simp only [runProgram] at hg ⊢
  split at hg
  · simp only [Option.some.injEq, Bool.and_eq_true] at hg
    obtain ⟨g, hg', hW⟩ := hI.proved hg.2
    exact ⟨g, hg', hW _ (World.Le.refl _)⟩
  · cases hg

/-- The "no `False`" corollary: a program that declares a data type with no value constructors and sets as its goal
an application of it is never reported to prove that goal. -/
theorem no_empty_goal (prog : Program) (has : String → Bool) (err : Option (Pos × String))
    (hp : Program.plain prog = true) (d : Data) (hd : Top.data d ∈ prog ∨ ∃ p ds, Top.mutualData p ds ∈ prog ∧ d ∈ ds)
    (hc : d.ctors = []) (p : Pos) (hn : Name) (args : List WTerm) (hg : Top.goal p (.type (.app hn args)) ∈ prog)
    (hname : hn.name = d.name.name) : (runProgram 1 prog has err).goalProved ≠ some true := by
  sorry

/-- No top-level evaluation the checker performs fails: the evaluator runs every checked tree to a value. -/
theorem TopState.eval_ok {st : TopState} {ρ : List Value} {C : Ctx} {g : Option Given} {e : Expr} {o : Out}
    {pos : Pos} (hI : TopInv st ρ) (hph : C.phase = 1) (her : C.erased = false) (hgl : C.globals = st.globals)
    (hfn : C.fn = none) (hg : ∀ g', g = some g' → g'.Ok ρ) (hp : e.plain = true) (h : checkExpr C st.sc g e = .ok o)
    {r : Res} (hr : single e.pos o.res = .ok r) : ∃ v, st.eval pos o.tree r.tainted = .ok (some v) := by
  obtain ⟨-, -, hres, ρ', vs, hev, -, hvs, -, -⟩ :=
    Expr.sound e hp C st.sc g _ _ ρ st.env _ o (hI.inv hph her hgl hfn) hg h
  rw [single_ok hr] at hvs hres
  obtain ⟨v, -, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs)
  refine ⟨v, ?_⟩
  simp only [TopState.eval, (hres r (by simp)).1, Bool.false_eq_true, ↓reduceIte]
  have : evalExpr ⟨st.fns, kindOf st.globals⟩ (Act.top st.fns) st.env o.tree = .ok [v] := hev
  rw [this]; rfl

theorem TopState.run_ok {st : TopState} {ρ : List Value} {C : Ctx} {s : Stmt} {o : StmtOut} (hI : TopInv st ρ)
    (hph : C.phase = 1) (her : C.erased = false) (hgl : C.globals = st.globals) (hfn : C.fn = none)
    (hp : s.plain = true) (h : checkStmt C st.sc s = .ok o) : ∃ env, st.run o.tree = .ok env := by
  obtain ⟨-, ρ', env', hev, -⟩ := Stmt.sound s hp C st.sc _ _ ρ st.env _ o (hI.inv hph her hgl hfn) h
  refine ⟨env', ?_⟩
  have : evalStmt ⟨st.fns, kindOf st.globals⟩ (Act.top st.fns) st.env o.tree = .ok env' := hev
  simp only [TopState.run, this]; rfl

/-- `data Unit() : Type() { tt() : Unit(); } goal Unit(); qed tt();`, which the checker accepts with its goal
proved, so the goal clause of `runProgram_sound` is not vacuous. Kernel reduction does not seem to get through the
evaluator's well-founded recursion (`decide +kernel` gets stuck), so this is checked by `#guard`, not a theorem. -/
def unitProgram : Program :=
  [.data ⟨⟨"Unit", 0⟩, [], [⟨⟨"tt", 0⟩, [], .app ⟨"Unit", 0⟩ []⟩]⟩,
   .goal 0 (.type (.app ⟨"Unit", 0⟩ [])),
   .qed 0 (.app ⟨"tt", 0⟩ [])]

#guard (runProgram 1 unitProgram (fun _ => true)).goalProved == some true

#guard Program.plain unitProgram

end Pledge
