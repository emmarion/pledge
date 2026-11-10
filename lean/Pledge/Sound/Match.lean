import Pledge.Sound.Term

namespace Pledge

theorem against_go_eq {sc : Scope} {g : Given} {pos : Pos} (hh : sc.holes = []) :
    ∀ (ws : List Want) (rs : List Res) (prev : List Term) (sc' : Scope),
      against.go g pos sc prev ws rs = .ok sc' → sc' = sc
  | w :: ws, r :: rs, prev, sc', h => by
    rw [against.go] at h
    simp only [Scope.typeOf, solveHoles_nil hh] at h
    cases hT : typeOf sc.sigs sc.Γ r.term with
    | none => simp [hT, internal, failAt, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    | some has =>
      cases hwt : w.type <;> cases hwi : w.is <;>
        simp only [hT, hwt, hwi, Option.map_some, Option.map_none, pure, Except.pure, bind, Except.bind,
          solveHoles_nil hh, failAt_eq] at h
      all_goals (repeat (split at h)) <;> first | exact against_go_eq hh ws rs _ sc' h | simp at h
  | [], _, _, sc', h | _ :: _, [], _, sc', h => by
    simp only [against.go, pure, Except.pure, Except.ok.injEq] at h; exact h.symm

theorem produced_eq {sc : Scope} {g : Option Given} {pos : Pos} {rs : List Res} {tree : Expr} {o : Out}
    (hh : sc.holes = []) (h : produced sc g pos rs tree = .ok o) : o = ⟨sc, rs, tree, []⟩ := by
  cases g with
  | none =>
    simp only [produced, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
    exact h.symm
  | some g =>
    simp only [produced] at h
    obtain ⟨sc', hsc, h⟩ := bind_eq_ok.1 h
    cases h
    simp only [against] at hsc
    by_cases hl : rs.length = g.wants.length
    · simp only [hl, ne_eq, not_true_eq_false, ↓reduceIte] at hsc
      rw [against_go_eq hh _ _ _ _ hsc]
    · simp [hl, miscount, failAt_eq, bind, Except.bind] at hsc

theorem finish_eq {C : Ctx} {whole : Bool} {g : Option Given} {e : Expr} {o o' : Out}
    (h : finish C whole g e o = .ok o') : o'.sc = o.sc ∧ (o.sc.taintedBy = none → o'.res = o.res) := by
  simp only [finish] at h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  have fin : ∀ x : Out, (pure x : CheckM Out) = .ok o' → x.sc = o.sc → (o.sc.taintedBy = none → x.res = o.res) →
      o'.sc = o.sc ∧ (o.sc.taintedBy = none → o'.res = o.res) := fun x h h1 h2 => by
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨h1, h2⟩
  cases whole <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  · split at h
    · simp [failAt_eq, bind, Except.bind] at h
    · exact fin _ h rfl (fun ht => by simp [ht])
  · exact fin _ h rfl (fun ht => by simp [ht])

theorem applied_eq {sc : Scope} {g : Option Given} {pos : Pos} {rs : List Res} {tree : Expr} {since : Nat}
    {snaps : List Snapshot} {o : Out} (hh : sc.holes = []) (h : applied sc g pos rs tree since snaps = .ok o) :
    o = ⟨sc, rs, tree, snaps⟩ := by
  simp only [applied, keep_ok] at h
  obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
  obtain rfl := produced_eq hh ho'
  simp only [settle_nil hh, ok_bind, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

theorem opened_untainted {sc : Scope} {tele : Telescope} {env : List Term} {kind : String} {pos : Pos}
    {taint : Nat → Bool} (hT : ∀ i, taint i = false) :
    ∀ r ∈ (opened sc tele env kind pos taint).2, r.tainted = false := by
  intro r hr
  simp only [opened, List.mem_mapIdx] at hr
  obtain ⟨i, -, rfl⟩ := hr
  exact hT i

/-- Every function the globals resolve to has an untainted signature. -/
def FnsClean (gs : List Global) : Prop :=
  ∀ n m sig, gs.find? (·.name == n) = some (.fn m (some sig)) → sig.tainted = false

/-- Checking an expression of plain syntax in an inert scope is meant to give untainted results and an inert scope. -/
def ExprClean (e : Expr) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (g : Option Given) (o : Out), C.phase = 1 → FnsClean C.globals → sc.Inert →
    checkExpr C sc g e = .ok o → o.sc.Inert ∧ ∀ r ∈ o.res, r.tainted = false

def StmtClean (s : Stmt) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (o : StmtOut), C.phase = 1 → FnsClean C.globals → sc.Inert →
    checkStmt C sc s = .ok o → o.sc.Inert

theorem finish_clean {C : Ctx} {whole : Bool} {g : Option Given} {e : Expr} {o o' : Out}
    (h : finish C whole g e o = .ok o') (hin : o.sc.Inert) (hr : ∀ r ∈ o.res, r.tainted = false) :
    o'.sc.Inert ∧ ∀ r ∈ o'.res, r.tainted = false := by
  obtain ⟨h1, h2⟩ := finish_eq h
  rw [h1, h2 hin.taintedBy]
  exact ⟨hin, hr⟩

theorem Scope.Inert.lookup {sc : Scope} (hin : sc.Inert) {n : String} {r : Res} (h : sc.lookup n = some r) :
    r.tainted = false :=
  hin.names _ (lookup_mem h)

theorem notValue_ne {α : Type} {C : Ctx} {sc : Scope} {n : Name} {a : α} : notValue C sc n ≠ .ok a := by
  simp [notValue, failAt_eq]

theorem var_clean (x : Id) : ExprClean (.var x) := by
  intro C sc g o hph hfc hin h
  rw [checkExpr] at h
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 h
  clear h
  cases hx : x.name with
  | none => simp [hx, failAt_eq] at ho'
  | some n =>
    cases hl : sc.lookup n with
    | none => simp only [hx, hl] at ho'; exact absurd ho' notValue_ne
    | some r =>
      simp only [hx, hl] at ho'
      obtain rfl := produced_eq hin.holes ho'
      exact finish_clean hf hin (by simpa using hin.lookup hl)

theorem checkArgs_clean {args : List Arg} (ih : ∀ a ∈ args, ExprClean a.expr) :
    ∀ {C : Ctx} {sc : Scope} {owner role : String} {erased : Bool} {params : Telescope} {prev : List Res}
      {a : ArgsOut}, C.phase = 1 → FnsClean C.globals → sc.Inert →
      checkArgs C sc owner role erased params prev args = .ok a → a.sc.Inert ∧ ∀ r ∈ a.res, r.tainted = false := by
  induction args with
  | nil =>
    intro C sc owner role erased params prev a _ _ hin h
    simp only [checkArgs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hin, by simp⟩
  | cons arg args ihs =>
    intro C sc owner role erased params prev a hph hfc hin h
    obtain ⟨m, e⟩ := arg
    cases params with
    | nil => simp [checkArgs, internal, failAt_eq] at h
    | cons p ps =>
      simp only [checkArgs, hph, Nat.not_le_of_lt (by decide : 1 < 2), decide_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
      obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
      obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [keep_ok] at hr hrest
      obtain ⟨hin₁, hr₁⟩ := ih (.mk m e) List.mem_cons_self C sc _ o hph hfc hin ho
      obtain ⟨hin₂, hr₂⟩ := ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hph hfc hin₁ hrest
      refine ⟨hin₂, fun r' hr' => ?_⟩
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact hr₁ _ (by rw [single_ok hr]; simp)
      · exact hr₂ r' hr'

theorem any_untainted {rs : List Res} (h : ∀ r ∈ rs, r.tainted = false) : rs.any (·.tainted) = false := by
  simp only [List.any_eq_false]
  intro r hr
  simp [h r hr]

theorem app_clean {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprClean a.expr) : ExprClean (.app h args) := by
  intro C sc g o hph hfc hin hc
  rw [checkExpr] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  clear hc
  suffices key : o'.sc.Inert ∧ ∀ r ∈ o'.res, r.tainted = false from finish_clean hf key.1 key.2
  simp only [Ctx.global] at ho'
  cases hgl : C.globals.find? (·.name == h.name) with
  | none => simp [hgl, notApplied, failAt_eq] at ho'
  | some gl =>
    cases gl with
    | fn m sig =>
      cases sig with
      | none => simp [hgl, failAt_eq] at ho'
      | some sig =>
        simp only [hgl] at ho'
        have hst := hfc _ _ _ hgl
        split at ho'
        · obtain ⟨plan, -, ho'⟩ := bind_eq_ok.1 ho'
          obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
          obtain ⟨a, ha, ho'⟩ := bind_eq_ok.1 ho'
          rw [keep_ok] at ho'
          obtain ⟨hin', hra⟩ := checkArgs_clean ih (by exact hph) (by exact hfc) hin ha
          split at ho'
          · obtain ⟨u2, -, ho'⟩ := bind_eq_ok.1 ho'
            obtain rfl := applied_eq (by exact hin'.holes) ho'
            exact ⟨⟨hin'.holes, hin'.taintedBy, hin'.names⟩, opened_untainted fun _ => by simp [hst, any_untainted hra]⟩
          · obtain rfl := applied_eq (by exact hin'.holes) ho'
            exact ⟨⟨hin'.holes, hin'.taintedBy, hin'.names⟩, opened_untainted fun _ => by simp [hst, any_untainted hra]⟩
        · obtain ⟨u0, -, ho'⟩ := bind_eq_ok.1 ho'
          obtain ⟨plan, -, ho'⟩ := bind_eq_ok.1 ho'
          obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
          obtain ⟨a, ha, ho'⟩ := bind_eq_ok.1 ho'
          rw [keep_ok] at ho'
          obtain ⟨hin', hra⟩ := checkArgs_clean ih (by exact hph) (by exact hfc) hin ha
          split at ho'
          · obtain ⟨u2, -, ho'⟩ := bind_eq_ok.1 ho'
            obtain rfl := applied_eq (by exact hin'.holes) ho'
            exact ⟨⟨hin'.holes, hin'.taintedBy, hin'.names⟩, opened_untainted fun _ => by simp [hst, any_untainted hra]⟩
          · obtain rfl := applied_eq (by exact hin'.holes) ho'
            exact ⟨⟨hin'.holes, hin'.taintedBy, hin'.names⟩, opened_untainted fun _ => by simp [hst, any_untainted hra]⟩
    | type _ _ _ | ctor _ =>
      simp only [hgl] at ho'
      obtain ⟨u0, -, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨sig, -, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨a, ha, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨hin', hra⟩ := checkArgs_clean ih (by exact hph) (by exact hfc) hin ha
      obtain rfl := applied_eq hin'.holes ho'
      exact ⟨hin', by simp [any_untainted hra]⟩

theorem Scope.Inert.bind {sc : Scope} {ids : List Id} {rs : List Res} (hin : sc.Inert)
    (hr : ∀ r ∈ rs, r.tainted = false) : (sc.bind ids rs).Inert := by
  rw [Scope.bind_eq]
  refine ⟨hin.holes, hin.taintedBy, fun q hq => ?_⟩
  rcases List.mem_append.1 hq with hq | hq
  · simp only [pushed, List.mem_reverse, List.mem_filterMap, Option.map_eq_some_iff] at hq
    obtain ⟨⟨i, r'⟩, hm, n, -, rfl⟩ := hq
    exact hr r' (List.of_mem_zip hm).2
  · exact hin.names q hq

theorem reach_none {sc : Scope} {r : Res} {pos : Pos} (h : sc.taintedBy = none) (hr : r.tainted = false) :
    reach sc r pos = none := by
  simp [reach, h, hr]

/-- The scope a branch is checked in is inert when the scope before the match is and the scrutinee is untainted. -/
theorem branchScope_inert {inner : Scope} {r : Res} {sp : Pos} {Γ : Entries} {ids : List Nat} {fields : List Id}
    (hin : inner.Inert) (hr : r.tainted = false) :
    (Scope.bind { inner with Γ, taintedBy := reach inner r sp, holes := [] } fields (fieldRes ids)).Inert :=
  Scope.Inert.bind ⟨rfl, reach_none hin.taintedBy hr, hin.names⟩ (fieldRes_untainted ids)

theorem checkBranches_spec {C : Ctx} {inner : Scope} {r : Res} {sp : Pos} {fs : List Forcing} {g : Given} :
    ∀ {bs : List Branch} {bo : BranchesOut}, checkBranches C inner r sp fs g bs = .ok bo →
      bo.outs.length = bs.length ∧ bo.trees = (bs.zip bo.outs).map (fun p => .mk p.1.pat p.2.tree) ∧
      ∀ b o, (b, o) ∈ bs.zip bo.outs → ∃ Γ ids, survivor inner fs b.pat.ctor.name b.pat.ctor.pos "" = .ok (Γ, ids) ∧
        checkExpr C (Scope.bind { inner with Γ, taintedBy := reach inner r sp, holes := [] } b.pat.fields
          (fieldRes ids)) (some g) b.body = .ok o
  | [], bo, h => by
    simp only [checkBranches, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | .mk pat body :: bs, bo, h => by
    simp only [checkBranches] at h
    obtain ⟨⟨Γ, ids⟩, hs, h⟩ := bind_eq_ok.1 h
    obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    obtain ⟨h1, h2, h3⟩ := checkBranches_spec hrest
    refine ⟨by simp [h1], by simp [h2]; rfl, fun b o' hm => ?_⟩
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hm
    · exact ⟨Γ, ids, hs, ho⟩
    · exact h3 b o' hm

theorem mem_zip_right {α β : Type} {l : List α} {l' : List β} (hl : l'.length ≤ l.length) {y : β} (hy : y ∈ l') :
    ∃ x, (x, y) ∈ l.zip l' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  exact ⟨l[i]'(by omega), by rw [← List.getElem_zip (h := by simp; omega)]; exact List.getElem_mem _⟩

theorem mem_zip_left {α β : Type} {l : List α} {l' : List β} (hl : l.length ≤ l'.length) {x : α} (hx : x ∈ l) :
    ∃ y, (x, y) ∈ l.zip l' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact ⟨l'[i]'(by omega), by rw [← List.getElem_zip (h := by simp; omega)]; exact List.getElem_mem _⟩

theorem checkBranches_clean {bs : List Branch} (ih : ∀ b ∈ bs, ExprClean b.body) {C : Ctx} {inner : Scope} {r : Res}
    {sp : Pos} {fs : List Forcing} {g : Given} {bo : BranchesOut} (hph : C.phase = 1) (hfc : FnsClean C.globals)
    (hin : inner.Inert) (hr : r.tainted = false) (h : checkBranches C inner r sp fs g bs = .ok bo) :
    ∀ o ∈ bo.outs, ∀ r ∈ o.res, r.tainted = false := by
  obtain ⟨hl, -, hbr⟩ := checkBranches_spec h
  intro o ho
  obtain ⟨b, hm⟩ := mem_zip_right (l := bs) (by omega) ho
  obtain ⟨Γ, ids, -, hc⟩ := hbr b o hm
  exact (ih b (List.of_mem_zip hm).1 C _ _ o hph hfc (branchScope_inert hin hr) hc).2

theorem checkElems_clean {es : List Expr} (ih : ∀ e ∈ es, ExprClean e) :
    ∀ {C : Ctx} {sc : Scope} {g : Option Given} {prev : List Res} {o : ElemsOut}, C.phase = 1 →
      FnsClean C.globals → sc.Inert → checkElems C sc g prev es = .ok o →
      o.sc.Inert ∧ ∀ r ∈ o.res, r.tainted = false := by
  induction es with
  | nil =>
    intro C sc g prev o _ _ hin h
    simp only [checkElems, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hin, by simp⟩
  | cons e es ihs =>
    intro C sc g prev o hph hfc hin h
    simp only [checkElems] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hr hrest
    obtain ⟨hin₁, hr₁⟩ := ih e List.mem_cons_self C sc _ o₁ hph hfc hin ho₁
    obtain ⟨hin₂, hr₂⟩ := ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hph hfc hin₁ hrest
    refine ⟨hin₂, fun r' hr' => ?_⟩
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact hr₁ _ (by rw [single_ok hr]; simp)
    · exact hr₂ r' hr'

theorem tuple_clean (p : Pos) {es : List Expr} (ih : ∀ e ∈ es, ExprClean e) : ExprClean (.tuple p es) := by
  intro C sc g o hph hfc hin hc
  rw [checkExpr] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  simp only at ho'
  repeat (split at ho')
  all_goals first
    | (simp [miscount, failAt_eq, bind, Except.bind] at ho'; done)
    | (obtain ⟨oe, hoe, ho'⟩ := bind_eq_ok.1 ho'
       simp only [pure, Except.pure, Except.ok.injEq] at ho'
       subst ho'
       obtain ⟨hin', hr⟩ := checkElems_clean ih (by exact hph) (by exact hfc) hin hoe
       exact finish_clean hf hin' hr)

theorem checkStmts_clean {ss : List Stmt} (ih : ∀ s ∈ ss, StmtClean s) :
    ∀ {C : Ctx} {sc : Scope} {o : StmtsOut}, C.phase = 1 → FnsClean C.globals → sc.Inert →
      checkStmts C sc ss = .ok o → o.sc.Inert := by
  induction ss with
  | nil =>
    intro C sc o _ _ hin h
    simp only [checkStmts, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hin
  | cons s ss ihs =>
    intro C sc o hph hfc hin h
    simp only [checkStmts] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    exact ihs (o := rest) (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hph hfc
      (ih s List.mem_cons_self C sc o₁ hph hfc hin ho₁) hrest

theorem block_clean {ss : List Stmt} {f : Expr} (ihs : ∀ s ∈ ss, StmtClean s) (ihf : ExprClean f) :
    ExprClean (.block ss f) := by
  intro C sc g o hph hfc hin hc
  rw [checkExpr] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  obtain ⟨s, hs, ho'⟩ := bind_eq_ok.1 ho'
  obtain ⟨of, hof, ho'⟩ := bind_eq_ok.1 ho'
  simp only [pure, Except.pure, Except.ok.injEq] at ho'
  subst ho'
  rw [keep_ok] at hof
  have hs' := checkStmts_clean ihs (by exact hph) (by exact hfc) (by exact ⟨rfl, hin.taintedBy, hin.names⟩) hs
  obtain ⟨hin', hr⟩ := ihf _ _ _ _ (by exact hph) (by exact hfc) (by exact ⟨hin.holes, hs'.taintedBy, hs'.names⟩) hof
  exact finish_clean hf ⟨hin'.holes, hin'.taintedBy, hin.names⟩ hr

theorem inspect_clean (p : Pos) : StmtClean (.inspect p) := by
  intro C sc o _ _ hin h
  simp only [checkStmt, pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact hin

theorem let_clean {p : Pos} {bs : List LetBinder} {rhs : Expr} (ih : ExprClean rhs) : StmtClean (.let p bs rhs) := by
  intro C sc o hph hfc hin h
  simp only [checkStmt] at h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨ws, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hin', hr⟩ := ih C sc _ o' hph hfc hin ho'
  refine Scope.Inert.bind hin' fun r hr' => ?_
  simp only [List.mem_map] at hr'
  obtain ⟨⟨b, r'⟩, hm, rfl⟩ := hr'
  exact hr r' (List.of_mem_zip hm).2

theorem patlet_clean {p : Pos} {ct : Bool} {m : Option Mult} {pat : Pattern} {rhs : Expr} (ih : ExprClean rhs)
    (hm : m = none) : StmtClean (.patlet p ct m pat rhs) := by
  intro C sc o hph hfc hin h
  subst hm
  simp only [checkStmt, show ((none : Option Mult) == some Mult.erased) = false from rfl, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨u', -, h⟩ := bind_eq_ok.1 h
  obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
  rw [keep_ok] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
  obtain ⟨fs, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨sc', hsc', h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hin', hres⟩ := ih _ sc none o' (by exact hph) (by exact hfc) hin ho'
  obtain ⟨Γ, ids, -, -, rfl⟩ := patBind_spec hsc'
  exact Scope.Inert.bind ⟨hin'.holes, reach_none hin'.taintedBy (hres r (by rw [single_ok hr]; simp)), hin'.names⟩
    (fieldRes_untainted ids)

/-- A match result is untainted when the scrutinee and every branch's results are. -/
theorem matchTaint_false {r : Res} {outs : List Out} (hr : r.tainted = false)
    (h : ∀ o ∈ outs, ∀ r ∈ o.res, r.tainted = false) (i : Nat) :
    (r.tainted || outs.any fun o : Out => ((o.res[i]?).map (Res.tainted ·)).getD false) = false := by
  simp only [hr, Bool.false_or, List.any_eq_false]
  intro o ho
  cases hi : o.res[i]? with
  | none => simp
  | some r' => simpa using h o ho r' (List.mem_of_getElem? hi)

theorem match_clean {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch} (ihs : ExprClean s)
    (ihb : ∀ b ∈ bs, ExprClean b.body) (hm : m = none) : ExprClean (.match p m s ann bs) := by
  intro C sc g o hph hfc hin hc
  subst hm
  rw [checkExpr] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  clear hc
  obtain ⟨so, hso, ho₁⟩ := bind_eq_ok.1 ho'
  clear ho'
  rw [keep_ok] at ho₁
  obtain ⟨r, hr, ho₂⟩ := bind_eq_ok.1 ho₁
  obtain ⟨⟨tele, tenv⟩, -, ho₃⟩ := bind_eq_ok.1 ho₂
  obtain ⟨fs, -, ho₄⟩ := bind_eq_ok.1 ho₃
  obtain ⟨u1, -, ho₅⟩ := bind_eq_ok.1 ho₄
  clear ho₁ ho₂ ho₃ ho₄
  obtain ⟨hin₁, hr₁⟩ := ihs _ sc none so (by exact hph) (by exact hfc) hin hso
  have hrt : r.tainted = false := hr₁ r (by rw [single_ok hr]; simp)
  simp only [show ((none : Option Mult) == some Mult.erased) = false from rfl, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte] at ho₅
  split at ho₅
  case isFalse => simp [failAt_eq, bind, Except.bind] at ho₅
  split at ho₅
  all_goals
    obtain ⟨u4, -, ho₆⟩ := bind_eq_ok.1 ho₅
    obtain ⟨bo, hbo, ho₇⟩ := bind_eq_ok.1 ho₆
    obtain ⟨o'', ho'', ho₈⟩ := bind_eq_ok.1 ho₇
    simp only [pure, Except.pure, Except.ok.injEq] at ho₈
    subst ho₈
    rw [keep_ok] at ho''
    obtain rfl := produced_eq (by exact hin₁.holes) ho''
    exact finish_clean hf ⟨hin₁.holes, hin₁.taintedBy, hin₁.names⟩ (opened_untainted
      (matchTaint_false hrt (checkBranches_clean ihb (by exact hph) (by exact hfc) hin₁ hrt hbo)))

mutual
/-- Plain syntax checked in an inert scope gives untainted results and leaves the scope inert. -/
theorem Expr.clean : (e : Expr) → e.plain = true → ExprClean e
  | .var x, _ => var_clean x
  | .app h args, hp => app_clean fun a ha =>
    Expr.clean a.expr (Arg.plain_expr ▸ Arg.plainList_iff.1 (by simpa [Expr.plain] using hp) a ha)
  | .tuple p es, hp => tuple_clean p fun e he =>
    Expr.clean e (Expr.plainList_iff.1 (by simpa [Expr.plain] using hp) e he)
  | .block ss f, hp => by
    simp only [Expr.plain, Bool.and_eq_true] at hp
    exact block_clean (fun s hs => Stmt.clean s (Stmt.plainList_iff.1 hp.1 s hs)) (Expr.clean f hp.2)
  | .match p m s ann bs, hp => by
    simp only [Expr.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
    exact match_clean (Expr.clean s hp.1.1.2)
      (fun b hb => Expr.clean b.body (Branch.plain_body ▸ Branch.plainList_iff.1 hp.2 b hb)) hp.1.1.1
  | .sorry .., hp | .removed, hp => by simp [Expr.plain] at hp
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (have := List.sizeOf_lt_of_mem (List.mem_map_of_mem (f := Arg.expr) ha); have := sizeOf_map_expr args
       simp only [Expr.app.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem he; simp only [Expr.tuple.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem hs; simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.match.sizeOf_spec]; omega)
    | (have := sizeOf_body_lt hb; simp only [Expr.match.sizeOf_spec]; omega)
theorem Stmt.clean : (s : Stmt) → s.plain = true → StmtClean s
  | .let p bs rhs, hp => by
    simp only [Stmt.plain, Bool.and_eq_true] at hp
    exact let_clean (Expr.clean rhs hp.2)
  | .patlet p ct m pat rhs, hp => by
    simp only [Stmt.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
    exact patlet_clean (Expr.clean rhs hp.2) hp.1
  | .inspect p, _ => inspect_clean p
termination_by s => sizeOf s
decreasing_by all_goals (simp only [Stmt.let.sizeOf_spec, Stmt.patlet.sizeOf_spec]; omega)
end


theorem TeleSat.of_wantsSat {S : Sigs} {ρ : List Value} :
    ∀ {tele : Telescope} {ws : List Want} {env vs : List Value}, ws.length = tele.length →
      (∀ (i : Nat) (w : Want) (b : TBinder), ws[i]? = some w → tele[i]? = some b →
        w.type = some b.type ∧ w.is = b.is) →
      WantsSat S ρ ws env vs → TeleSat S ρ tele env vs
  | [], [], _, [], _, _, _ => .nil
  | b :: _, w :: _, _, _ :: _, hl, hwb, ⟨h1, h2⟩ => by
    obtain ⟨ht, hi⟩ := hwb 0 w b rfl rfl
    obtain ⟨A, hA, hv⟩ := h1.1 b.type ht
    exact .cons hA hv (fun e he => h1.2 e (hi ▸ he))
      (TeleSat.of_wantsSat (by simpa using hl) (fun i w' b' h1 h2 => hwb (i + 1) w' b' h1 h2) h2)
  | [], _ :: _, _, _, hl, _, _ | _ :: _, [], _, _, hl, _, _ => by simp at hl
  | [], [], _, _ :: _, _, _, h | _ :: _, _ :: _, _, [], _, _, h => h.elim

theorem TeleSat.typed {S : Sigs} {ρ : List Value} :
    ∀ {Δ : Telescope} {env vs : List Value}, TeleSat S ρ Δ env vs → ∀ v ∈ vs, ∃ V, HasType S v V
  | [], _, _, h => by rw [TeleSat.nil_iff.1 h]; simp
  | _ :: _, _, _, h => by
    obtain ⟨v, vs, rfl, ⟨A, -, hv, -⟩, ht⟩ := TeleSat.cons_iff.1 h
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ⟨A, hv⟩
    · exact TeleSat.typed ht u hu

theorem evalList_range' {ρ ws : List Value} :
    Term.evalList (ρ ++ ws) [] ((List.range' ρ.length ws.length).map .entry) = some ws := by
  refine Term.evalList_eq_some_iff.2 ⟨by simp, fun i a ha => ?_⟩
  simp only [List.getElem?_map, Option.map_eq_some_iff] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  have hi : i < ws.length := by have := (List.getElem?_eq_some_iff.1 hj).1; simpa using this
  rw [List.getElem?_range' hi] at hj
  cases hj
  simp [Term.eval, List.getElem?_append_right]

/-- The fields a forcing opens, as results, take the values of the value constructor's arguments. -/
theorem evalList_fieldRes {ρ ws : List Value} {ids : List Nat} (hids : ids = List.range' ρ.length ws.length) :
    Term.evalList (ρ ++ ws) [] ((fieldRes ids).map (·.term)) = some ws := by
  subst hids
  simpa [fieldRes, Function.comp_def] using evalList_range' (ρ := ρ) (ws := ws)

theorem pickBranch_of_find {h : Head} {ws : List Value} {bs : List Branch} {b : Branch}
    (hf : bs.find? (·.pat.ctor.name == h.name) = some b) : pickBranch none (.app h ws) bs = .ok b := by
  simp [pickBranch, hf, pure, Except.pure]

theorem annotation_annTake {C : Ctx} {sc : Scope} {g : Option Given} {ann : Tele} {tele : Telescope}
    {env : List Term} {vs : List Value} (hp : ann.plain = true) (h : annotation C sc g ann = .ok (tele, env))
    (hl : vs.length = tele.length) : annTake ann vs = .ok vs := by
  cases ann with
  | binders bs =>
    simp only [annotation] at h
    obtain ⟨out, hout, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := (telescope_shape (by simpa [Tele.plain] using hp) hout).1
    simp [annTake, take, hl, this, pure, Except.pure]
  | hole => rfl

/-- The fields of a pattern for a value constructor whose arguments satisfy its fields are as many as the
arguments. -/
theorem forcings_fields {C : Ctx} {sc : Scope} {t : Term} {sp at_ : Pos} {pats : List Pattern} {erased : Bool}
    {fs : List Forcing} {pat : Pattern} {sig : Sig} {S : Sigs} {ρ ws : List Value}
    (h : forcings C sc t sp pats at_ erased = .ok fs) (hp : pat ∈ pats)
    (hsig : sc.sigs.find ⟨.ctor, pat.ctor.name⟩ = some sig) (hws : TeleSat S ρ sig.params [] ws) :
    pat.fields.length = ws.length := by
  obtain ⟨ctors, hct, hpats, -⟩ := forcings_spec h
  obtain ⟨-, -, -, -, -, -, -, -, -, hsigs⟩ := dataCtors_spec hct
  obtain ⟨sig', hm, hl⟩ := hpats pat hp
  have := hsigs _ _ hm
  rw [hsig] at this
  cases this
  rw [hl, hws.length_eq]

/-- The scrutinee of a `match` or pattern `let` runs to one typed value, its result's. -/
theorem scrut_sound {s : Expr} (ih : ExprSound s) {C C' : Ctx} {sc : Scope} {n0 : Nat} {W : World}
    {ρ : List Value} {env : Env} {act : Act} {so : Out} {pos : Pos} {r : Res} (hI : Inv C sc n0 W ρ env act)
    (hph : C'.phase = C.phase) (her : C'.erased = C.erased) (hgl : C'.globals = C.globals) (hfn : C'.fn = C.fn)
    (h : checkExpr C' sc none s = .ok so) (hr : single pos so.res = .ok r) :
    so.sc.sigs = sc.sigs ∧ so.sc.names = sc.names ∧ r.tainted = false ∧ ∃ ρ₁ v V,
      evalExpr W.P act env so.tree = .ok [v] ∧ Inv C so.sc n0 W (ρ ++ ρ₁) env act ∧
      r.term.eval (ρ ++ ρ₁) [] = some v ∧ HasType W.Sc v V := by
  obtain ⟨hsigs, hnames, hres, ρ₁, vs, hev, hI₁, hvs, hty, -⟩ :=
    ih C' sc none n0 W ρ env act so (hI.congr_ctx hph her hgl hfn) (by simp) h
  rw [single_ok hr] at hvs hres
  obtain ⟨v, hv, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs)
  obtain ⟨V, hV⟩ := hty v (by simp)
  exact ⟨hsigs, hnames, (hres r (by simp)).1, ρ₁, v, V, hev, hI₁.congr_ctx hph.symm her.symm hgl.symm hfn.symm,
    hv, hV⟩

/-- The invariant for the scope a forcing gave, with a pattern's names bound to its fields. -/
theorem Inv.pattern {C : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {env : Env} {act : Act}
    {Γ' : Entries} {ids : List Nat} {fields : List Id} {ρ' ws : List Value} {Δ : Telescope} {tb : Option Pos}
    {hs : List Hole} (hI : Inv C sc n0 W ρ env act) (hsat : Sat W.Sc Γ' (ρ ++ ws))
    (hids : ids = List.range' sc.Γ.length ws.length) (hws : TeleSat W.Sc ρ' Δ [] ws)
    (hfl : fields.length = ws.length) (htb : tb = none) (hhs : hs = []) :
    Inv C (Scope.bind { sc with Γ := Γ', taintedBy := tb, holes := hs } fields (fieldRes ids)) n0 W (ρ ++ ws)
      (pushed fields ws ++ env) act := by
  subst htb hhs
  exact (hI.extend (sc' := { sc with Γ := Γ', taintedBy := none, holes := [] }) hsat rfl rfl
    ⟨rfl, rfl, hI.inert.names⟩).bind
    (evalList_fieldRes (by rw [hids, hI.sat.1])) hws.typed (fieldRes_untainted ids) (bindIds_of_length hfl)

end Pledge
