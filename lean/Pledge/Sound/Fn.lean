import Pledge.Sound.Expr

namespace Pledge

namespace FnGroup

/-- Every function a name resolves to has an untainted signature. -/
def GlobalsClean (gs : List Global) : Prop :=
  ∀ n m sig, gs.find? (·.name == n) = some (.fn m (some sig)) → sig.tainted = false

/-- Checking an expression in an inert scope, with untainted functions, gives untainted results and an inert
scope, whatever the valuation. -/
def ExprClean (e : Expr) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (g : Option Given) (o : Out), C.phase = 1 → GlobalsClean C.globals → sc.Inert →
    checkExpr C sc g e = .ok o → o.sc.Inert ∧ ∀ r ∈ o.res, r.tainted = false

def StmtClean (s : Stmt) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (o : StmtOut), C.phase = 1 → GlobalsClean C.globals → sc.Inert →
    checkStmt C sc s = .ok o → o.sc.Inert

theorem against_go_same {g : Given} {pos : Pos} :
    ∀ (ws : List Want) (rs : List Res) (sc sc' : Scope) (prev : List Term), sc.holes = [] →
      against.go g pos sc prev ws rs = .ok sc' → sc' = sc
  | [], _, sc, sc', prev, _, h => by cases h; rfl
  | _ :: _, [], sc, sc', prev, _, h => by cases h; rfl
  | w :: ws, r :: rs, sc, sc', prev, hh, h => by
    rw [against.go] at h
    obtain ⟨has, -, h⟩ := bind_eq_ok.1 h
    cases hwt : w.type <;> cases hwi : w.is <;>
      simp only [hwt, hwi, Option.map_some, Option.map_none, pure, Except.pure, bind, Except.bind,
        solveHoles_nil hh, failAt_eq] at h
    all_goals first
      | exact against_go_same ws rs sc sc' _ hh h
      | (split at h
         · first
           | exact against_go_same ws rs sc sc' _ hh h
           | (split at h
              · exact against_go_same ws rs sc sc' _ hh h
              · cases h)
         · cases h)

theorem produced_same {sc : Scope} {g : Option Given} {pos : Pos} {rs : List Res} {tree : Expr} {o : Out}
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
    · rw [against_go_same _ _ _ _ _ hh hsc]

theorem applied_same {sc : Scope} {g : Option Given} {pos : Pos} {rs : List Res} {tree : Expr} {since : Nat}
    {snaps : List Snapshot} {o : Out} (hh : sc.holes = []) (h : applied sc g pos rs tree since snaps = .ok o) :
    o = ⟨sc, rs, tree, snaps⟩ := by
  simp only [applied, keep_ok] at h
  obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
  obtain rfl := produced_same hh ho'
  simp only [settle_nil hh, ok_bind] at h
  simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

theorem finish_same {C : Ctx} {w : Bool} {g : Option Given} {e : Expr} {o o' : Out}
    (h : finish C w g e o = .ok o') (ht : o.sc.taintedBy = none) : o'.sc = o.sc ∧ o'.res = o.res := by
  simp only [finish] at h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

theorem inert_bind {sc : Scope} (h : sc.Inert) {ids : List Id} {rs : List Res}
    (hr : ∀ r ∈ rs, r.tainted = false) : (sc.bind ids rs).Inert := by
  rw [Scope.bind_eq]
  refine ⟨h.holes, h.taintedBy, fun p hp => ?_⟩
  rcases List.mem_append.1 hp with hp | hp
  · simp only [pushed, List.mem_reverse, List.mem_filterMap, Option.map_eq_some_iff] at hp
    obtain ⟨⟨i, r⟩, hm, n, -, rfl⟩ := hp
    exact hr r (List.of_mem_zip hm).2
  · exact h.names p hp

theorem fieldRes_untainted (ids : List Nat) : ∀ r ∈ fieldRes ids, r.tainted = false := by
  simp [fieldRes]

theorem var_clean (x : Id) : ExprClean (.var x) := by
  intro C sc g o hph hgl hin hc
  rw [checkExpr] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  cases hx : x.name with
  | none => simp [hx, failAt_eq] at ho'
  | some n =>
    cases hl : sc.lookup n with
    | none => simp [hx, hl, notValue, failAt_eq] at ho'
    | some r =>
      simp only [hx, hl] at ho'
      obtain rfl := produced_same hin.holes ho'
      obtain ⟨h1, h2⟩ := finish_same hf hin.taintedBy
      refine ⟨h1 ▸ hin, ?_⟩
      rw [h2]
      simpa using hin.names _ (lookup_mem hl)

theorem opened_untainted (sc : Scope) (tele : Telescope) (env : List Term) (kind : String) (pos : Pos)
    {taint : Nat → Bool} (hT : ∀ i, taint i = false) :
    ∀ r ∈ (opened sc tele env kind pos taint).2, r.tainted = false := by
  intro r hr
  simp only [opened, List.mem_mapIdx] at hr
  obtain ⟨i, -, rfl⟩ := hr
  exact hT i

theorem inert_withΓ {sc : Scope} (h : sc.Inert) (Γ : Entries) : ({ sc with Γ } : Scope).Inert :=
  ⟨h.holes, h.taintedBy, h.names⟩

theorem checkElems_clean {es : List Expr} (ih : ∀ e ∈ es, ExprClean e) :
    ∀ {C : Ctx} {sc : Scope} {g : Option Given} {prev : List Res} {o : ElemsOut}, C.phase = 1 →
      GlobalsClean C.globals → sc.Inert → checkElems C sc g prev es = .ok o →
      o.sc.Inert ∧ ∀ r ∈ o.res, r.tainted = false := by
  induction es with
  | nil =>
    intro C sc g prev o _ _ hin h
    simp only [checkElems, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨hin, by simp⟩
  | cons e es ihs =>
    intro C sc g prev o hph hgl hin h
    simp only [checkElems] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hr hrest
    obtain ⟨hin₁, hres₁⟩ := ih e List.mem_cons_self C sc _ o₁ hph hgl hin ho₁
    obtain ⟨hin₂, hres₂⟩ := ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hph hgl hin₁ hrest
    refine ⟨hin₂, fun r' hr' => ?_⟩
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact hres₁ r' (by rw [single_ok hr]; simp)
    · exact hres₂ r' hr'

theorem checkArgs_clean {args : List Arg} (ih : ∀ a ∈ args, ExprClean a.expr) :
    ∀ {C : Ctx} {sc : Scope} {owner role : String} {erased : Bool} {params : Telescope} {prev : List Res}
      {a : ArgsOut}, C.phase = 1 → GlobalsClean C.globals → sc.Inert →
      checkArgs C sc owner role erased params prev args = .ok a → a.sc.Inert ∧ ∀ r ∈ a.res, r.tainted = false := by
  induction args with
  | nil =>
    intro C sc owner role erased params prev a _ _ hin h
    simp only [checkArgs, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨hin, by simp⟩
  | cons arg args ihs =>
    intro C sc owner role erased params prev a hph hgl hin h
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
      obtain ⟨hin₁, hres₁⟩ := ih (.mk m e) List.mem_cons_self C sc _ o hph hgl hin ho
      obtain ⟨hin₂, hres₂⟩ := ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hph hgl hin₁ hrest
      refine ⟨hin₂, fun r' hr' => ?_⟩
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact hres₁ r' (by rw [single_ok hr]; simp)
      · exact hres₂ r' hr'

theorem tuple_clean (p : Pos) {es : List Expr} (ih : ∀ e ∈ es, ExprClean e) : ExprClean (.tuple p es) := by
  intro C sc g o hph hgl hin hc
  rw [checkExpr] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  simp only at ho'
  split at ho'
  all_goals (try split at ho')
  all_goals (try (simp [miscount, failAt_eq, bind, Except.bind] at ho'; done))
  all_goals
    obtain ⟨oe, hoe, ho'⟩ := bind_eq_ok.1 ho'
    simp only [pure, Except.pure, Except.ok.injEq] at ho'
    subst ho'
    obtain ⟨hin', hres⟩ := checkElems_clean ih (by exact hph) (by exact hgl) hin hoe
    obtain ⟨h1, h2⟩ := finish_same hf hin'.taintedBy
    exact ⟨by rw [h1]; exact hin', by rw [h2]; exact hres⟩

theorem checkStmts_clean {ss : List Stmt} (ih : ∀ s ∈ ss, StmtClean s) :
    ∀ {C : Ctx} {sc : Scope} {o : StmtsOut}, C.phase = 1 → GlobalsClean C.globals → sc.Inert →
      checkStmts C sc ss = .ok o → o.sc.Inert := by
  induction ss with
  | nil =>
    intro C sc o _ _ hin h
    simp only [checkStmts, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hin
  | cons s ss ihs =>
    intro C sc o hph hgl hin h
    simp only [checkStmts] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    exact ihs (o := rest) (fun s hs => ih s (List.mem_cons_of_mem _ hs)) hph hgl
      (ih s List.mem_cons_self C sc o₁ hph hgl hin ho₁) hrest

theorem block_clean {ss : List Stmt} {f : Expr} (ihs : ∀ s ∈ ss, StmtClean s) (ihf : ExprClean f) :
    ExprClean (.block ss f) := by
  intro C sc g o hph hgl hin hc
  rw [checkExpr] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  obtain ⟨s, hs, ho'⟩ := bind_eq_ok.1 ho'
  obtain ⟨of, hof, ho'⟩ := bind_eq_ok.1 ho'
  simp only [pure, Except.pure, Except.ok.injEq] at ho'
  subst ho'
  rw [keep_ok] at hof
  have hs' := checkStmts_clean ihs (by exact hph) (by exact hgl) (by exact ⟨rfl, hin.taintedBy, hin.names⟩) hs
  obtain ⟨hin₂, hres⟩ := ihf _ _ _ of (by exact hph) (by exact hgl) (by exact ⟨hin.holes, hs'.taintedBy, hs'.names⟩) hof
  have hin₃ : ({ of.sc with names := sc.names } : Scope).Inert := ⟨hin₂.holes, hin₂.taintedBy, hin.names⟩
  obtain ⟨h1, h2⟩ := finish_same hf hin₃.taintedBy
  exact ⟨by rw [h1]; exact hin₃, by rw [h2]; exact hres⟩

theorem let_clean {p : Pos} {bs : List LetBinder} {rhs : Expr} (ih : ExprClean rhs) : StmtClean (.let p bs rhs) := by
  intro C sc o hph hgl hin h
  simp only [checkStmt] at h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨ws, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hin', hres⟩ := ih C sc _ o' hph hgl hin ho'
  refine inert_bind hin' fun r hr => ?_
  simp only [List.mem_map] at hr
  obtain ⟨⟨b, r'⟩, hm, rfl⟩ := hr
  exact hres r' (List.of_mem_zip hm).2

theorem reach_none {sc : Scope} {r : Res} {pos : Pos} (h : sc.taintedBy = none) (hr : r.tainted = false) :
    reach sc r pos = none := by
  simp [reach, h, hr]

theorem patlet_clean {p : Pos} {ct : Bool} {m : Option Mult} {pat : Pattern} {rhs : Expr} (ih : ExprClean rhs) :
    StmtClean (.patlet p ct m pat rhs) := by
  intro C sc o hph hgl hin h
  simp only [checkStmt] at h
  split at h
  · first | cases h | simp [failAt_eq, bind, Except.bind] at h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
  rw [keep_ok] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
  obtain ⟨fs, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨sc', hsc', h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hin', hres⟩ := ih _ sc none o' (by exact hph) (by exact hgl) hin ho'
  obtain ⟨Γ, ids, -, -, rfl⟩ := patBind_spec hsc'
  exact inert_bind
    (by exact ⟨hin'.holes, reach_none hin'.taintedBy (hres r (by rw [single_ok hr]; simp)), hin'.names⟩)
    (fieldRes_untainted ids)

theorem inspect_clean (p : Pos) : StmtClean (.inspect p) := by
  intro C sc o _ _ hin h
  simp only [checkStmt, pure, Except.pure, Except.ok.injEq] at h
  subst h; exact hin

theorem applied_opened_clean {sc : Scope} (hin : sc.Inert) {tele : Telescope} {env : List Term} {name : String}
    {pos pos' : Pos} {taint : Nat → Bool} (hT : ∀ i, taint i = false) {g : Option Given} {tree : Expr} {since : Nat}
    {snaps : List Snapshot} {o : Out}
    (h : applied (opened sc tele env name pos taint).1 g pos' (opened sc tele env name pos taint).2 tree since snaps =
      .ok o) : o.sc.Inert ∧ ∀ r ∈ o.res, r.tainted = false := by
  obtain rfl := applied_same (by rw [opened_fst]; exact hin.holes) h
  exact ⟨by rw [opened_fst]; exact inert_withΓ hin _, opened_untainted _ _ _ _ _ hT⟩

theorem app_clean {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprClean a.expr) : ExprClean (.app h args) := by
  intro C sc g o hph hgl hin hc
  rw [checkExpr] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  simp only [Ctx.global] at ho'
  suffices o'.sc.Inert ∧ ∀ r ∈ o'.res, r.tainted = false by
    obtain ⟨h1, h2⟩ := finish_same hf this.1.taintedBy
    exact ⟨by rw [h1]; exact this.1, by rw [h2]; exact this.2⟩
  cases hg : C.globals.find? (·.name == h.name) with
  | none => simp [hg, notApplied, failAt_eq] at ho'
  | some gl =>
    cases gl with
    | fn m sig =>
      cases sig with
      | none => simp [hg, failAt_eq] at ho'
      | some sig =>
        simp only [hg] at ho'
        have hst : sig.tainted = false := hgl _ _ _ hg
        have fin : ∀ a : ArgsOut, a.sc.Inert → (∀ r ∈ a.res, r.tainted = false) →
            (sig.tainted || a.res.any fun x => x.tainted) = false := fun a _ hres => by
          simp only [hst, Bool.false_or, List.any_eq_false]
          exact fun r hr => by simp [hres r hr]
        split at ho'
        · obtain ⟨plan, -, ho'⟩ := bind_eq_ok.1 ho'
          obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
          obtain ⟨a, ha, ho'⟩ := bind_eq_ok.1 ho'
          rw [keep_ok] at ho'
          obtain ⟨hin', hres⟩ := checkArgs_clean ih (by exact hph) (by exact hgl) hin ha
          split at ho'
          · obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
            exact applied_opened_clean hin' (fun _ => fin a hin' hres) ho'
          · exact applied_opened_clean hin' (fun _ => fin a hin' hres) ho'
        · obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
          obtain ⟨plan, -, ho'⟩ := bind_eq_ok.1 ho'
          obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
          obtain ⟨a, ha, ho'⟩ := bind_eq_ok.1 ho'
          rw [keep_ok] at ho'
          obtain ⟨hin', hres⟩ := checkArgs_clean ih (by exact hph) (by exact hgl) hin ha
          split at ho'
          · obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
            exact applied_opened_clean hin' (fun _ => fin a hin' hres) ho'
          · exact applied_opened_clean hin' (fun _ => fin a hin' hres) ho'
    | type T cs d =>
      simp only [hg, ↓reduceIte] at ho'
      obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨sig, -, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨u₂, -, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨a, ha, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨hin', hres⟩ := checkArgs_clean ih (by exact hph) (by exact hgl) hin ha
      obtain rfl := applied_same hin'.holes ho'
      exact ⟨hin', by simpa using hres⟩
    | ctor c =>
      simp only [hg] at ho'
      obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨sig, -, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨u₂, -, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨a, ha, ho'⟩ := bind_eq_ok.1 ho'
      obtain ⟨hin', hres⟩ := checkArgs_clean ih (by exact hph) (by exact hgl) hin ha
      obtain rfl := applied_same hin'.holes ho'
      exact ⟨hin', by simpa using hres⟩

theorem checkBranches_clean {bs : List Branch} (ih : ∀ b ∈ bs, ExprClean b.body) :
    ∀ {C : Ctx} {inner : Scope} {r : Res} {sp : Pos} {fs : List Forcing} {g : Given} {bo : BranchesOut},
      C.phase = 1 → GlobalsClean C.globals → inner.Inert → r.tainted = false →
      checkBranches C inner r sp fs g bs = .ok bo → ∀ o ∈ bo.outs, ∀ x ∈ o.res, x.tainted = false := by
  induction bs with
  | nil =>
    intro C inner r sp fs g bo _ _ _ _ h
    simp only [checkBranches, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | cons b bs ihs =>
    intro C inner r sp fs g bo hph hgl hin hr h
    obtain ⟨pat, body⟩ := b
    simp only [checkBranches] at h
    obtain ⟨⟨Γ, ids⟩, -, h⟩ := bind_eq_ok.1 h
    obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    have hin₀ : ({ inner with Γ := Γ, taintedBy := reach inner r sp, holes := [] } : Scope).Inert :=
      ⟨rfl, reach_none hin.taintedBy hr, hin.names⟩
    have hin₁ := inert_bind hin₀ (ids := pat.fields) (fieldRes_untainted ids)
    have h₁ := (ih (.mk pat body) List.mem_cons_self C _ _ o hph hgl hin₁ ho).2
    have h₂ := ihs (fun b hb => ih b (List.mem_cons_of_mem _ hb)) hph hgl hin hr hrest
    intro o' ho'
    rcases List.mem_cons.1 ho' with rfl | ho'
    · exact h₁
    · exact h₂ o' ho'

theorem match_clean {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch} (ihs : ExprClean s)
    (ihb : ∀ b ∈ bs, ExprClean b.body) : ExprClean (.match p m s ann bs) := by
  intro C sc g o hph hgl hin hc
  rw [checkExpr] at hc
  obtain ⟨o', ho', hf⟩ := bind_eq_ok.1 hc
  simp only at ho'
  suffices o'.sc.Inert ∧ ∀ r ∈ o'.res, r.tainted = false by
    obtain ⟨h1, h2⟩ := finish_same hf this.1.taintedBy
    exact ⟨by rw [h1]; exact this.1, by rw [h2]; exact this.2⟩
  obtain ⟨so, hso, ho'⟩ := bind_eq_ok.1 ho'
  rw [keep_ok] at ho'
  obtain ⟨r, hr, ho'⟩ := bind_eq_ok.1 ho'
  obtain ⟨hin₁, hres₁⟩ := ihs _ sc none so (by exact hph) (by exact hgl) hin hso
  have hrt : r.tainted = false := hres₁ r (by rw [single_ok hr]; simp)
  obtain ⟨tx, -, ho'⟩ := bind_eq_ok.1 ho'
  obtain ⟨fs, -, ho'⟩ := bind_eq_ok.1 ho'
  obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
  split at ho'
  all_goals try (cases ho'; done)
  split at ho'
  all_goals (try (split at ho'; all_goals try (cases ho'; done)))
  all_goals
    obtain ⟨u, -, ho'⟩ := bind_eq_ok.1 ho'
    obtain ⟨bo, hbo, ho'⟩ := bind_eq_ok.1 ho'
    obtain ⟨o₂, ho₂, ho'⟩ := bind_eq_ok.1 ho'
    simp only [pure, Except.pure, Except.ok.injEq] at ho'
    subst ho'
    rw [keep_ok] at ho₂
    have hbr := checkBranches_clean ihb (by exact hph) (by exact hgl) hin₁ hrt hbo
    obtain rfl := produced_same (by rw [opened_fst]; exact hin₁.holes) ho₂
    refine ⟨by rw [opened_fst]; exact inert_withΓ hin₁ _, opened_untainted _ _ _ _ _ fun i => ?_⟩
    simp only [hrt, Bool.false_or, List.any_eq_false]
    intro o ho
    cases hx : o.res[i]?
    · simp
    · simp [hbr o ho _ (List.mem_of_getElem? hx)]

mutual
/-- In phase 1 without `sorry`, checking produces no taint. -/
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
      (fun b hb => Expr.clean b.body (Branch.plain_body ▸ Branch.plainList_iff.1 hp.2 b hb))
  | .sorry .., hp | .removed, hp => by simp [Expr.plain] at hp
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (have := Arg.sizeOf_expr_lt ha; simp only [Expr.app.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem he; simp only [Expr.tuple.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem hs; simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.match.sizeOf_spec]; omega)
    | (have := Branch.sizeOf_body_lt' hb; simp only [Expr.match.sizeOf_spec]; omega)
theorem Stmt.clean : (s : Stmt) → s.plain = true → StmtClean s
  | .let p bs rhs, hp => by
    simp only [Stmt.plain, Bool.and_eq_true] at hp
    exact let_clean (Expr.clean rhs hp.2)
  | .patlet p ct m pat rhs, hp => by
    simp only [Stmt.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
    exact patlet_clean (Expr.clean rhs hp.2)
  | .inspect p, _ => inspect_clean p
termination_by s => sizeOf s
decreasing_by all_goals (simp only [Stmt.let.sizeOf_spec, Stmt.patlet.sizeOf_spec]; omega)
end

theorem fresh_global {C : Ctx} {sc : Scope} {seen : List String} {n : String} {pos : Pos} {x : List String}
    (h : fresh C sc seen (some n) pos = .ok x) : C.global n = none := by
  simp only [fresh] at h
  split at h
  · simp [failAt_eq] at h
  · split at h
    · simp [failAt_eq] at h
    · rename_i hc
      cases hg : C.global n
      · rfl
      · simp [hg] at hc

theorem fold0_spec : ∀ (fs : List Fn) (s s' : TopState),
    List.foldlM (fun st f => do
      let _ ← fresh (st.ctx true) st.sc [] (some f.name.name) f.name.pos
      pure { st with globals := st.globals ++ [Global.fn f.name.name none] }) s fs = .ok s' →
    s' = { s with globals := s.globals ++ fs.map fun f => .fn f.name.name none } ∧ (fs.map (·.name.name)).Nodup ∧
      ∀ f ∈ fs, s.globals.find? (·.name == f.name.name) = none
  | [], s, s', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | f :: fs, s, s', h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨s1, hs1, h⟩ := bind_eq_ok.1 h
    obtain ⟨x, hx, hs1⟩ := bind_eq_ok.1 hs1
    simp only [pure, Except.pure, Except.ok.injEq] at hs1
    subst hs1
    have hfr : s.globals.find? (·.name == f.name.name) = none := fresh_global hx
    obtain ⟨rfl, hnd, hfr'⟩ := fold0_spec fs _ s' h
    have hfr'' : ∀ f' ∈ fs, s.globals.find? (·.name == f'.name.name) = none ∧ f.name.name ≠ f'.name.name := by
      intro f' hf'
      have := hfr' f' hf'
      rw [List.find?_append, Option.or_eq_none_iff] at this
      refine ⟨this.1, fun he => ?_⟩
      simp [Global.name, he] at this
    refine ⟨by simp, ?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
      exact ⟨fun f' hf' he => (hfr'' f' hf').2 he.symm, hnd⟩
    · intro f' hf'
      rcases List.mem_cons.1 hf' with rfl | hf'
      · exact hfr
      · exact (hfr'' f' hf').1

/-- What `fnHead` checked of a function's head: its telescopes, in the top-level scope `sc`, mention only top-level
entries, and the head records them. -/
structure HeadSpec (sc : Scope) (names : List String) (h : FnHead) : Prop where
  name : h.fn.name = h.f.name.name
  group : h.fn.group = names
  tele : ∃ (C : Ctx) (ps rs : Checked), telescope C sc (h.f.header.params.map (·.binder)) "param" = .ok ps ∧
    telescope C ps.sc h.f.header.returns "binder" ps.ids = .ok rs ∧
    (ps.tele ++ rs.tele).all (·.entriesBelow sc.Γ.length) = true ∧
    h.sig = ⟨ps.tele, rs.tele, h.f.header.params.map (·.subterm), false⟩ ∧ h.sc = ps.sc ∧ h.env = ps.ids.map .entry ∧
    h.fn.subterms = ((ps.ids.zip (h.f.header.params.map (·.subterm))).filter (·.2)).map fun (i, _) => Term.entry i

theorem fnHead_spec {names : List String} {st st' : TopState} {f : Fn} {h : FnHead}
    (hh : fnHead names st f = .ok (st', h)) :
    h.f = f ∧ HeadSpec st.sc names h ∧
      st' = { st with
        globals := st.globals.map fun g => if g.name == h.fn.name then .fn g.name (some h.sig) else g } := by
  simp only [fnHead] at hh
  obtain ⟨⟨ps, rs⟩, hhd, hh⟩ := bind_eq_ok.1 hh
  obtain ⟨u, htl, hh⟩ := bind_eq_ok.1 hh
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hh
  obtain ⟨rfl, rfl⟩ := hh
  simp only [header] at hhd
  obtain ⟨ps', hps, hhd⟩ := bind_eq_ok.1 hhd
  obtain ⟨rs', hrs, hhd⟩ := bind_eq_ok.1 hhd
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hhd
  obtain ⟨rfl, rfl⟩ := hhd
  exact ⟨rfl, ⟨rfl, rfl, _, ps', rs', hps, hrs, ensure_ok htl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- The globals after the signatures of `hs` are recorded one after the other, as `fnHead` does. -/
def updSigs : List FnHead → List Global → List Global
  | [], gs => gs
  | h :: hs, gs => updSigs hs (gs.map fun g => if g.name == h.fn.name then .fn g.name (some h.sig) else g)

theorem fold1_spec (names : List String) : ∀ (fs : List Fn) (s : TopState) (acc : List FnHead) (s' : TopState)
    (hs : List FnHead), List.foldlM (fun x f => do
        let __x ← fnHead names x.fst f
        pure (__x.fst, x.snd ++ [__x.snd])) (s, acc) fs = .ok (s', hs) →
      ∃ hs', hs = acc ++ hs' ∧ hs'.map (·.f) = fs ∧ (∀ h ∈ hs', HeadSpec s.sc names h) ∧
        s' = { s with globals := updSigs hs' s.globals }
  | [], s, acc, s', hs, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, rfl, by simp, rfl⟩
  | f :: fs, s, acc, s', hs, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨x, hx, h⟩ := bind_eq_ok.1 h
    obtain ⟨y, hy, hx⟩ := bind_eq_ok.1 hx
    simp only [pure, Except.pure, Except.ok.injEq] at hx
    subst hx
    obtain ⟨hf, hspec, hst⟩ := fnHead_spec (st' := y.1) (h := y.2) hy
    obtain ⟨hs', rfl, hmap, hall, rfl⟩ := fold1_spec names fs _ _ s' hs h
    rw [hst] at hall ⊢
    refine ⟨y.2 :: hs', by simp, by simp [hf, hmap], ?_, rfl⟩
    intro h' hh'
    rcases List.mem_cons.1 hh' with rfl | hh'
    · exact hspec
    · exact hall h' hh'

/-- A global after the signatures of `hs` are recorded: the last of them with its name, if any. -/
def lastSig (hs : List FnHead) (g : Global) : Global :=
  match hs.reverse.find? (·.fn.name == g.name) with
  | some h => .fn g.name (some h.sig)
  | none => g

theorem lastSig_cons (h : FnHead) (hs : List FnHead) (g : Global) :
    lastSig (h :: hs) g = lastSig hs (if g.name == h.fn.name then .fn g.name (some h.sig) else g) := by
  have hn : (if g.name == h.fn.name then Global.fn g.name (some h.sig) else g).name = g.name := by
    split <;> rfl
  unfold lastSig
  rw [hn, List.reverse_cons, List.find?_append]
  cases hf : hs.reverse.find? (·.fn.name == g.name) with
  | some h' => rfl
  | none =>
    simp only [Option.none_or, List.find?_cons, List.find?_nil]
    by_cases e : h.fn.name = g.name
    · simp [e]
    · have e' : (g.name == h.fn.name) = false := by simpa using Ne.symm e
      have e'' : (h.fn.name == g.name) = false := by simpa using e
      simp [e', e'']

theorem updSigs_eq : ∀ (hs : List FnHead) (gs : List Global), updSigs hs gs = gs.map (lastSig hs)
  | [], gs => by
    simp only [updSigs]
    induction gs with
    | nil => rfl
    | cons g gs ih => exact congrArg (g :: ·) ih
  | h :: hs, gs => by
    rw [updSigs, updSigs_eq hs, List.map_map]
    exact List.map_congr_left fun g _ => (lastSig_cons h hs g).symm

theorem find?_name_map {gs : List Global} {f : Global → Global} (hf : ∀ g, (f g).name = g.name) (n : String) :
    (gs.map f).find? (·.name == n) = (gs.find? (·.name == n)).map f := by
  rw [List.find?_map]
  have : ((fun g : Global => g.name == n) ∘ f) = fun g => g.name == n := funext fun g => by simp [hf]
  rw [this]

theorem find?_unique {α : Type} {k : α → String} : ∀ {l : List α}, (l.map k).Nodup → ∀ {x}, x ∈ l →
    l.find? (fun y => k y == k x) = some x
  | y :: l, hnd, x, hx => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · have : (k y == k x) = false := by
        simpa using fun he => hnd.1 x hx he.symm
      rw [this]
      exact find?_unique hnd.2 hx

/-- What `setSigs` does to one global. -/
def setSig (heads : List FnHead) (taint : List Bool) : Global → Global
  | .fn n s => match (heads.zip taint).find? (·.1.fn.name == n) with
    | some (h, t) => .fn n (some { h.sig with tainted := t })
    | none => .fn n s
  | g => g

theorem setSigs_eq (gs : List Global) (heads : List FnHead) (taint : List Bool) :
    setSigs gs heads taint = gs.map (setSig heads taint) := by
  simp only [setSigs]
  congr 1

theorem setSig_name (heads : List FnHead) (taint : List Bool) (g : Global) : (setSig heads taint g).name = g.name := by
  cases g <;> simp only [setSig] <;> try rfl
  split <;> rfl

theorem lastSig_name (hs : List FnHead) (g : Global) : (lastSig hs g).name = g.name := by
  unfold lastSig; split <;> rfl

theorem zip_false {α : Type} : ∀ l : List α, l.zip (l.map fun _ => false) = l.map (·, false)
  | [] => rfl
  | a :: l => by simp [zip_false l]

theorem FnSig.with_untainted {s : FnSig} (h : s.tainted = false) : { s with tainted := false } = s := by
  cases s; simp_all

/-- After a group's heads are checked and its bodies leave no function tainted, a name resolves as among the
earlier globals followed by the group's functions with their signatures. -/
theorem group_find {gs : List Global} {heads : List FnHead} (hnd : (heads.map (·.fn.name)).Nodup)
    (hfr : ∀ h ∈ heads, gs.find? (·.name == h.fn.name) = none) (ht : ∀ h ∈ heads, h.sig.tainted = false)
    (n : String) :
    (setSigs (updSigs heads (gs ++ heads.map fun h => Global.fn h.fn.name none)) heads
        (heads.map fun _ => false)).find? (·.name == n) =
      (gs ++ heads.map fun h => Global.fn h.fn.name (some h.sig)).find? (·.name == n) := by
  rw [updSigs_eq, setSigs_eq, find?_name_map (setSig_name _ _), find?_name_map (lastSig_name _), List.find?_append,
    List.find?_append]
  have hz : ∀ m, (heads.zip (heads.map fun _ => false)).find? (·.1.fn.name == m) =
      (heads.find? (·.fn.name == m)).map (·, false) := fun m => by
    rw [zip_false, List.find?_map]; rfl
  cases hg : gs.find? (·.name == n) with
  | some g =>
    have hgn : g.name = n := by simpa using List.find?_some hg
    have hno : ∀ m, m = n → heads.find? (·.fn.name == m) = none := fun m hm => by
      subst hm
      refine List.find?_eq_none.2 fun h hh he => ?_
      have := hfr h hh
      rw [show h.fn.name = m by simpa using he, hg] at this
      cases this
    have hl : lastSig heads g = g := by
      unfold lastSig
      rw [show heads.reverse.find? (·.fn.name == g.name) = none from
        List.find?_eq_none.2 fun h hh he => by
          have := hno _ hgn
          rw [List.find?_eq_none] at this
          exact this h (List.mem_reverse.1 hh) he]
    simp only [Option.map_some, Option.some_or, hl]
    cases g with
    | fn m s =>
      simp only [setSig, hz, hno m hgn, Option.map_none]
    | _ => rfl
  | none =>
    simp only [Option.none_or, List.find?_map, Function.comp_def, Global.name]
    cases hh : heads.find? (·.fn.name == n) with
    | none => rfl
    | some h =>
      have hm := List.mem_of_find?_eq_some hh
      have hn : h.fn.name = n := by simpa using List.find?_some hh
      subst hn
      have hr : heads.reverse.find? (·.fn.name == h.fn.name) = some h :=
        find?_unique (k := fun h : FnHead => h.fn.name)
          (by rw [List.map_reverse]; exact List.pairwise_reverse.2 (hnd.imp Ne.symm)) (List.mem_reverse.2 hm)
      simp only [Option.map_some, lastSig, Global.name, hr, setSig, hz, hh, FnSig.with_untainted (ht h hm)]

theorem GlobalsOk.congr_find {n0 : Nat} {gs gs' : List Global} {fn : Option FnCtx} {S : Sigs} {W : World} {act : Act}
    (hf : ∀ n, gs.find? (·.name == n) = gs'.find? (·.name == n)) (h : GlobalsOk n0 gs fn S W act) :
    GlobalsOk n0 gs' fn S W act := by
  intro n g hg
  rw [← hf] at hg
  simpa only [hf] using h n g hg

theorem kindOf_congr {gs gs' : List Global} (hf : ∀ n, gs.find? (·.name == n) = gs'.find? (·.name == n))
    (n : String) : kindOf gs n = kindOf gs' n := by
  unfold kindOf; rw [hf]

theorem GlobalsClean.congr_find {gs gs' : List Global} (hf : ∀ n, gs.find? (·.name == n) = gs'.find? (·.name == n))
    (h : GlobalsClean gs) : GlobalsClean gs' := fun n m sig hg => h n m sig (by rw [hf]; exact hg)

theorem FnOk.of_none {n0 : Nat} {W : World} {fn : Option FnCtx} {act : Act} {n : String} {sig : FnSig}
    (h : FnOk n0 W none act n sig) (hn : ∀ f, fn = some f → f.group.contains n = false) : FnOk n0 W fn act n sig := by
  obtain ⟨d, h1, h2, h3, h4, h5, h6, h7⟩ := h.defn
  have hc : fn.any (·.group.contains n) = false := by
    cases fn with
    | none => rfl
    | some f => simpa using hn f rfl
  have h7' : d.group < act.group := by simpa using h7
  refine ⟨h.tainted, h.params, h.returns, h.subterm, d, h1, h2, h3, h4, h5, h6, ?_⟩
  rw [hc]
  simpa using h7'

/-- The globals of a group's bodies and of the top level after it: the earlier ones, then the group's functions. -/
theorem GlobalsOk.group {n0 : Nat} {gs : List Global} {fn : Option FnCtx} {S : Sigs} {W : World} {act : Act}
    {heads : List FnHead} (hbase : GlobalsOk n0 gs none S W act)
    (hout : ∀ f, fn = some f → ∀ n g, gs.find? (·.name == n) = some g → f.group.contains n = false)
    (hnew : ∀ h ∈ heads, FnOk n0 W fn act h.fn.name h.sig) :
    GlobalsOk n0 (gs ++ heads.map fun h => .fn h.fn.name (some h.sig)) fn S W act := by
  intro n g hg
  rw [List.find?_append] at hg
  cases hgs : gs.find? (·.name == n) with
  | some g0 =>
    rw [hgs, Option.some_or, Option.some.injEq] at hg
    subst hg
    have := hbase n _ hgs
    cases g0 with
    | fn m sig =>
      cases sig with
      | none => trivial
      | some sig => exact FnOk.of_none this fun f hf => hout f hf n _ hgs
    | type T cs d =>
      refine ⟨this.1, fun cs' hcs hd => ?_⟩
      obtain ⟨a, b, c, e⟩ := this.2 cs' hcs hd
      exact ⟨a, b, c, fun c hc => by rw [List.find?_append, e c hc]; rfl⟩
    | ctor c => exact this
  | none =>
    rw [hgs, Option.none_or, List.find?_map, Option.map_eq_some_iff] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    have hn : h.fn.name = n := by simpa [Global.name] using List.find?_some hh
    subst hn
    exact hnew h (List.mem_of_find?_eq_some hh)

theorem count_filter_zip : ∀ (ids : List Nat) (flags : List Bool), ids.length = flags.length →
    ((ids.zip flags).filter (·.2)).length = flags.count true
  | [], [], _ => rfl
  | i :: ids, b :: flags, h => by
    have := count_filter_zip ids flags (by simpa using h)
    cases b <;> simp [this]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- What a function's head gives, whatever the valuation. -/
theorem HeadSpec.facts {sc : Scope} {names : List String} {h : FnHead} (hs : HeadSpec sc names h)
    (hp : h.f.plain = true) (hin : sc.Inert) :
    h.sig.tainted = false ∧ (∀ b ∈ h.sig.params, b.entriesBelow sc.Γ.length = true ∧ b.mult = .many) ∧
      (∀ b ∈ h.sig.returns, b.entriesBelow sc.Γ.length = true ∧ b.mult = .many) ∧
      h.sig.subterm.length = h.sig.params.length ∧ h.sig.params.length = h.f.header.params.length ∧
      h.fn.subterms.length = h.sig.subterm.count true ∧ h.sc.Inert ∧ h.sc.sigs = sc.sigs := by
  obtain ⟨C, ps, rs, hps, hrs, hbelow, hsig, hsc, -, hsub⟩ := hs.tele
  simp only [Fn.plain, Header.plain, Bool.and_eq_true] at hp
  have hpp : (h.f.header.params.map (·.binder)).all Binder.plain = true := by
    simpa [List.all_map] using hp.1.1
  obtain ⟨hpl, hpids, -, -, hpsc, hpm, -⟩ := telescope_shape hpp hps
  obtain ⟨-, -, -, -, -, hrm, -⟩ := telescope_shape hp.1.2 hrs
  simp only [List.all_append, Bool.and_eq_true, List.all_eq_true] at hbelow
  rw [hsig]
  refine ⟨rfl, fun b hb => ⟨hbelow.1 b hb, hpm b hb⟩, fun b hb => ⟨hbelow.2 b hb, hrm b hb⟩, by simpa using hpl.symm,
    by simpa using hpl, ?_, ?_, ?_⟩
  · rw [hsub, List.length_map, count_filter_zip _ _ (by simp [hpids])]
  · rw [hsc, hpsc]
    exact inert_bind (inert_withΓ hin _) (fieldRes_untainted _)
  · rw [hsc, hpsc, Scope.bind_eq]

theorem checkAll_spec {α : Type} {f : α → CheckM Out} : ∀ {l : List α} {outs : List Out}, checkAll f l = .ok outs →
    outs.length = l.length ∧ ∀ p ∈ l.zip outs, f p.1 = .ok p.2
  | [], outs, h => by
    simp only [checkAll, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | a :: l, outs, h => by
    simp only [checkAll] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
    obtain ⟨os, hos, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hos
    obtain ⟨hl, hall⟩ := checkAll_spec hos
    refine ⟨by simp [hl], fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ho
    · exact hall p hp

theorem grows_false : ∀ (ts ns : List Bool), (∀ n ∈ ns, n = false) → grows ts ns = false
  | t :: ts, n :: ns, h => by
    simp only [grows, h n List.mem_cons_self, Bool.and_false, Bool.false_or]
    exact grows_false ts ns fun m hm => h m (List.mem_cons_of_mem _ hm)
  | [], _, _ | _ :: _, [], _ => rfl

/-- The taint fixed point is reached at once when the first round taints nothing. -/
theorem fixTaint_clean {step : List Bool → CheckM (List Out)} {t : List Bool} {r : List Bool × List Out}
    (h : fixTaint step t = .ok r)
    (hc : ∀ bodies, step t = .ok bodies → ∀ o ∈ bodies, ∀ x ∈ o.res, x.tainted = false) :
    r.1 = t ∧ step t = .ok r.2 := by
  rw [fixTaint] at h
  obtain ⟨bodies, hb, h⟩ := bind_eq_ok.1 h
  have hg : grows t (bodies.map fun o => o.res.any (·.tainted)) = false := by
    refine grows_false _ _ fun n hn => ?_
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hn
    simpa using fun x hx => hc bodies hb o ho x hx
  simp only [hg, Bool.false_eq_true, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, hb⟩

theorem evalList_range' : ∀ (pre vs : List Value),
    Term.evalList (pre ++ vs) [] ((List.range' pre.length vs.length).map .entry) = some vs
  | _, [] => rfl
  | pre, v :: vs => by
    have := evalList_range' (pre ++ [v]) vs
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at this
    simp only [List.length_cons, List.range'_succ, List.map_cons]
    refine Term.evalList_cons_eq_some.2 ⟨v, vs, ?_, this, rfl⟩
    simp [Term.eval]

theorem subterms_eval : ∀ (pre : List Value) (flags : List Bool) (vs : List Value), flags.length = vs.length →
    Term.evalList (pre ++ vs) [] ((((List.range' pre.length flags.length).zip flags).filter (·.2)).map
      fun (i, _) => Term.entry i) = some ((flags.zip vs).filterMap fun (b, v) => if b then some v else none)
  | _, [], [], _ => rfl
  | pre, b :: flags, v :: vs, hl => by
    have := subterms_eval (pre ++ [v]) flags vs (by simpa using hl)
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at this
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.filter_cons, List.filterMap_cons]
    cases b
    · simpa using this
    · simp only [↓reduceIte, List.map_cons]
      refine Term.evalList_cons_eq_some.2 ⟨v, _, by simp [Term.eval], this, rfl⟩
  | _, [], _ :: _, hl | _, _ :: _, [], hl => by simp at hl

theorem filterMap_some : ∀ (flags : List Bool) (vs : List Value),
    (flags.zip vs).filterMap (fun (b, v) => if b then some (some v) else none) =
      ((flags.zip vs).filterMap fun (b, v) => if b then some v else none).map some
  | [], _ | _ :: _, [] => rfl
  | b :: flags, v :: vs => by cases b <;> simp [filterMap_some flags vs]

theorem wantsSat_teleSat {S : Sigs} {ρ : List Value} :
    ∀ {tele : Telescope} {env vs : List Value}, WantsSat S ρ (tele.map Want.of) env vs → TeleSat S ρ tele env vs
  | [], _, [], _ => .nil
  | b :: _, _, v :: vs, ⟨h1, h2⟩ =>
    TeleSat.cons_iff.2 ⟨v, vs, rfl, WantSat.binderSat (m := b.mult) h1, wantsSat_teleSat h2⟩
  | [], _, _ :: _, h | _ :: _, _, [], h => h.elim

theorem teleSat_typed {S : Sigs} {ρ : List Value} :
    ∀ {Δ : Telescope} {env vs : List Value}, TeleSat S ρ Δ env vs → ∀ v ∈ vs, ∃ V, HasType S v V
  | [], _, _, h => by rw [TeleSat.nil_iff.1 h]; simp
  | _ :: _, _, _, h => by
    obtain ⟨v, vs', rfl, ⟨A, -, hA, -⟩, ht⟩ := TeleSat.cons_iff.1 h
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ⟨A, hA⟩
    · exact teleSat_typed ht u hu

theorem exists_zip {α β : Type} {l : List α} {l' : List β} (hl : l'.length = l.length) {a : α} (ha : a ∈ l) :
    ∃ b, (a, b) ∈ l.zip l' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  exact ⟨l'[i]'(hl ▸ hi), List.mem_iff_getElem.2 ⟨i, by simp [hl, hi], by simp⟩⟩

theorem le_foldr_max {n : Nat} : ∀ {l : List Nat}, n ∈ l → n ≤ l.foldr max 0
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => by have := le_foldr_max h; simp only [List.foldr_cons]; omega

/-- The function a group's head and checked body make. -/
def mkDef (st : TopState) (pad : Nat) (p : FnHead × Out) : FnDef :=
  { name := p.1.fn.name, params := p.1.f.header.params.map (·.binder.name), subterm := p.1.sig.subterm,
    returns := p.1.sig.returns.length, body := p.2.tree, globals := st.env, group := st.groups, pad := pad }

/-- The globals of a group's bodies: the earlier ones, then the group's functions with their signatures. -/
def groupGlobals (st : TopState) (heads : List FnHead) : List Global :=
  st.globals ++ heads.map fun h => .fn h.fn.name (some h.sig)

/-- What checking a group of functions establishes, before its functions are known to meet their
specifications. -/
structure GroupOk (st : TopState) (ρ : List Value) (heads : List FnHead) (bodies : List Out) (pad : Nat) : Prop where
  inv : TopInv st ρ
  len : bodies.length = heads.length
  spec : ∀ h ∈ heads, HeadSpec st.sc (heads.map (·.fn.name)) h ∧ h.f.plain = true
  nodup : (heads.map (·.fn.name)).Nodup
  fresh : ∀ h ∈ heads, st.globals.find? (·.name == h.fn.name) = none
  pad : ∀ h ∈ heads, h.fn.subterms.length ≤ pad
  body : ∀ p ∈ heads.zip bodies, ∃ C : Ctx, C.phase = 1 ∧ C.erased = false ∧ C.fn = some p.1.fn ∧
    (∀ n, C.globals.find? (·.name == n) = (groupGlobals st heads).find? (·.name == n)) ∧
    checkExpr C p.1.sc (some (returnsGiven p.1)) p.1.f.body = .ok p.2

/-- One activation of a group's function (SOUNDNESS.md Lemma 6.1 and Theorem 6.2): given that every function of the
group meets its specification from this activation, the body runs, by the main lemma, to results satisfying the
returns. -/
theorem GroupOk.step {st : TopState} {ρ : List Value} {heads : List FnHead} {bodies : List Out} {pad : Nat}
    (G : GroupOk st ρ heads bodies pad) {W : World} (hW : (st.world ρ).Le W)
    (hfind : ∀ p ∈ heads.zip bodies, W.P.fns.find p.1.fn.name = some (mkDef st pad p))
    {p : FnHead × Out} (hp : p ∈ heads.zip bodies) {vs : List Value} (hvs : TeleSat W.Sc W.ρ p.1.sig.params [] vs)
    (ih : ∀ q ∈ heads.zip bodies, CallSpec W (mkDef st pad q) q.1.sig (calleeAct (mkDef st pad p) vs)) :
    ∃ rs, callBody W.P (mkDef st pad p) vs = .ok rs ∧ TeleSat W.Sc W.ρ p.1.sig.returns vs rs := by
  obtain ⟨h, o⟩ := p
  have hmem : h ∈ heads := (List.of_mem_zip hp).1
  obtain ⟨hs, hpl⟩ := G.spec h hmem
  obtain ⟨-, hpar, hret, hsubl, hparl, hsubc, hin, hsigs⟩ := hs.facts hpl G.inv.inert
  obtain ⟨C0, ps, rs, hps, -, -, hsig, hsc, henv, hsub⟩ := hs.tele
  obtain ⟨C, hph, her, hfn, hgl, hc⟩ := G.body _ hp
  simp only at hc hfn hvs ih ⊢
  have hρl : ρ.length = st.sc.Γ.length := G.inv.sat.1
  have hρt : ρ.take st.sc.Γ.length = ρ := by rw [← hρl]; exact List.take_length
  have hpre : W.ρ.take st.sc.Γ.length = ρ := by rw [← hρl]; exact hW.take
  have hpb : h.sig.params.all (·.entriesBelow st.sc.Γ.length) = true := List.all_eq_true.2 fun b hb => (hpar b hb).1
  have hrb : h.sig.returns.all (·.entriesBelow st.sc.Γ.length) = true := List.all_eq_true.2 fun b hb => (hret b hb).1
  have hvs₀ : TeleSat W.Sc ρ ps.tele [] vs := by
    have := (TeleSat.iff_of_entriesBelow (ρ' := ρ) (by rw [hpre, hρt]) hpb).1 hvs
    rw [hsig] at this
    exact this
  have hSC : SigsClose st.sc.sigs ρ W.Sc := (SigsClose.close G.inv.sat.noRemoved).mono hW.sigs
  simp only [Fn.plain, Header.plain, Bool.and_eq_true] at hpl
  have hpp : (h.f.header.params.map (·.binder)).all Binder.plain = true := by simpa [List.all_map] using hpl.1.1
  have hT : TermInv st.sc st.sc.Γ.length W.Sc ρ :=
    ⟨G.inv.sat.mono_sigs hW.sigs, Nat.le_of_eq hρl.symm, hSC, G.inv.sigsOk, fun n r hl => by
      obtain ⟨v, V, -, hv, hV⟩ := G.inv.names n r hl
      exact ⟨v, V, hv, hV.mono_sigs hW.sigs⟩, G.inv.inert⟩
  have hT' := telescope_sound (outerv := []) hT hpp hps rfl hvs₀
  obtain ⟨hpl', hids, -, -, hpsc, -, -⟩ := telescope_shape hpp hps
  have hvl : vs.length = h.f.header.params.length := by simpa [hpl'] using hvs₀.length_eq
  have hids' : ps.ids = List.range' ρ.length vs.length := by rw [hids, hρl, hvl, List.length_map]
  have hevids : Term.evalList (ρ ++ vs) [] (ps.ids.map .entry) = some vs := by rw [hids']; exact evalList_range' ρ vs
  have hpn : (h.f.header.params.map (·.binder)).map (·.name) = (mkDef st pad (h, o)).params := by
    simp [mkDef]
  have hbind : bindIds (mkDef st pad (h, o)).globals (mkDef st pad (h, o)).params vs =
      .ok (pushed (mkDef st pad (h, o)).params vs ++ st.env) := bindIds_of_length (by simp [mkDef, hvl])
  have hdl : (mkDef st pad (h, o)).subterm.length = vs.length := by simp only [mkDef]; rw [hsubl, hparl, hvl]
  have hdc : (mkDef st pad (h, o)).subterm.count true ≤ (mkDef st pad (h, o)).pad := by
    simp only [mkDef]; rw [← hsubc]; exact G.pad h hmem
  obtain ⟨-, hcl, -⟩ := calleeAct_subs _ vs hdl hdc
  have hI : Inv C h.sc st.sc.Γ.length W (ρ ++ vs) (pushed (mkDef st pad (h, o)).params vs ++ st.env)
      (calleeAct (mkDef st pad (h, o)) vs) := by
    refine ⟨hph, her, hsc ▸ hT'.sat, by rw [← hρl]; exact hW.val.length_le, by rw [hpre, ← hρl]; simp, ?_,
      hsigs ▸ G.inv.sigsOk, ?_, ?_, ?_, hin⟩
    · intro ρ'' hρ''
      rw [hsigs]
      exact hSC.of_entriesBelow (by rw [hρ'', hpre, hρt]) fun sig hs => (G.inv.sigsOk sig hs).1
    · intro n r hl
      rw [hsc, hpsc] at hl
      simp only [Scope.lookup, Scope.bind_eq] at hl
      rw [← hpn]
      refine names_pushed _ (fieldRes ps.ids) vs st.sc.names st.env (fun n r hl => ?_) ?_ (teleSat_typed hvs₀) n r hl
      · obtain ⟨v, V, h1, h2, h3⟩ := G.inv.names n r hl
        exact ⟨v, V, h1, Term.eval_frame_ρ vs h2, h3.mono_sigs hW.sigs⟩
      · simp only [fieldRes, List.map_map]; exact hevids
    · refine GlobalsOk.congr_find (fun n => (hgl n).symm) ?_
      rw [hsigs, hfn]
      refine GlobalsOk.group (G.inv.globals W hW _ fun d hd => G.inv.groups d hd) ?_ fun h' hh' => ?_
      · intro f hf n g hg
        cases hf
        rw [hs.group]
        refine Bool.eq_false_iff.2 fun hcn => ?_
        obtain ⟨h', hh', rfl⟩ := List.mem_map.1 (by simpa using hcn)
        rw [G.fresh h' hh'] at hg
        cases hg
      · obtain ⟨hs', hpl''⟩ := G.spec h' hh'
        obtain ⟨htnt', hpar', hret', hsubl', hparl', hsubc', -, -⟩ := hs'.facts hpl'' G.inv.inert
        obtain ⟨o', ho'⟩ := exists_zip G.len hh'
        refine ⟨htnt', hpar', hret', hsubl', mkDef st pad (h', o'), hfind _ ho', by simp [mkDef, hparl'], rfl, rfl,
          by simp only [mkDef]; rw [← hsubc']; exact G.pad h' hh', ih _ ho', ?_⟩
        have : (some h.fn).any (·.group.contains h'.fn.name) = true := by
          simp [hs.group]; exact ⟨h', hh', rfl⟩
        rw [this]
        exact ⟨rfl, hcl.symm⟩
    · rw [hfn]
      rintro f ⟨⟩
      have hfl : (h.f.header.params.map (·.subterm)).length = vs.length := by simp [hvl]
      have hids'' : ps.ids = List.range' ρ.length (h.f.header.params.map (·.subterm)).length := by rw [hids', hfl]
      rw [hsub, hids'']
      refine ⟨_, subterms_eval ρ _ vs hfl, ?_⟩
      have hst : (mkDef st pad (h, o)).subterm = h.f.header.params.map (·.subterm) := by simp [mkDef, hsig]
      simp only [calleeAct, hst, filterMap_some, List.length_append, List.length_map, List.length_replicate]
      congr 2
      omega
  have hg : ∀ g', some (returnsGiven h) = some g' → g'.Ok (ρ ++ vs) := by
    rintro g' ⟨⟩
    refine ⟨⟨vs, by simp only [returnsGiven]; rw [henv]; exact hevids⟩, fun w hw => ?_⟩
    simp only [returnsGiven, List.mem_map] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    exact (hret b hb).2
  obtain ⟨-, -, -, ρ', vr, hev, -, -, -, hw⟩ := Expr.sound h.f.body hpl.2 C h.sc _ _ W (ρ ++ vs) _ _ o hI hg hc
  have hw' := hw _ rfl vs (by simp only [returnsGiven]; rw [henv]; exact hevids)
  have ht : TeleSat W.Sc (ρ ++ vs ++ ρ') h.sig.returns vs vr := wantsSat_teleSat hw'
  refine ⟨vr, ?_, (TeleSat.iff_of_entriesBelow ?_ hrb).1 ht⟩
  · simp only [callBody]
    rw [hbind, ok_bind]
    have hev' : evalExpr W.P (calleeAct (mkDef st pad (h, o)) vs) (pushed (mkDef st pad (h, o)).params vs ++ st.env)
        (mkDef st pad (h, o)).body = .ok vr := hev
    rw [hev', ok_bind]
    exact take_of_length (by simpa [mkDef] using ht.length_eq)
  · rw [hpre, List.append_assoc, List.take_append_of_le_length (Nat.le_of_eq hρl.symm), hρt]

/-- Every function of a checked group meets its specification in every later world (SOUNDNESS.md part 6), by
well-founded induction on the measure of its activations. -/
theorem GroupOk.fnSpec {st : TopState} {ρ : List Value} {heads : List FnHead} {bodies : List Out} {pad : Nat}
    (G : GroupOk st ρ heads bodies pad) {W : World} (hW : (st.world ρ).Le W)
    (hfind : ∀ p ∈ heads.zip bodies, W.P.fns.find p.1.fn.name = some (mkDef st pad p)) :
    ∀ p ∈ heads.zip bodies, FnSpec W (mkDef st pad p) p.1.sig := by
  suffices H : ∀ a p, p ∈ heads.zip bodies → ∀ vs, TeleSat W.Sc W.ρ p.1.sig.params [] vs →
      calleeAct (mkDef st pad p) vs = a →
      ∃ rs, callBody W.P (mkDef st pad p) vs = .ok rs ∧ TeleSat W.Sc W.ρ p.1.sig.returns vs rs from
    fun p hp vs hvs => H _ p hp vs hvs rfl
  intro a
  induction a using WellFounded.induction Act.lt_wf with
  | _ a ih =>
  intro p hp vs hvs ha
  subst ha
  exact G.step hW hfind hp hvs fun q hq vs' hvs' hlt => ih _ hlt q hq vs' hvs' rfl

theorem kindOf_some {gs : List Global} {n : String} {k : HeadKind} (h : kindOf gs n = some k) :
    ∃ g, gs.find? (·.name == n) = some g := by
  unfold kindOf at h
  split at h <;> first | (cases h; done) | exact ⟨_, ‹_›⟩

theorem kindOf_group (st : TopState) (heads : List FnHead) (n : String) :
    kindOf (groupGlobals st heads) n = kindOf st.globals n := by
  unfold kindOf groupGlobals
  rw [List.find?_append]
  cases hg : st.globals.find? (·.name == n) with
  | some g => rfl
  | none =>
    rw [Option.none_or, List.find?_map]
    cases (heads.find? ((·.name == n) ∘ fun h => Global.fn h.fn.name (some h.sig))) <;> rfl

theorem fns_find_group {st : TopState} {ρ : List Value} {heads : List FnHead} {bodies : List Out} {pad : Nat}
    (G : GroupOk st ρ heads bodies pad) {p : FnHead × Out} (hp : p ∈ heads.zip bodies) :
    Fns.find (st.fns ++ (heads.zip bodies).map (mkDef st pad)) p.1.fn.name = some (mkDef st pad p) := by
  have hm := (List.of_mem_zip hp).1
  simp only [Fns.find, List.find?_append]
  have hst : st.fns.find? (·.name == p.1.fn.name) = none := List.find?_eq_none.2 fun d hd he => by
    obtain ⟨sig, hs⟩ := G.inv.fnNames d hd
    rw [show d.name = p.1.fn.name by simpa using he, G.fresh _ hm] at hs
    cases hs
  rw [hst, Option.none_or, List.find?_map]
  have hz : (heads.zip bodies).map (fun q => q.1.fn.name) = heads.map (·.fn.name) := by
    have hz0 := List.map_fst_zip (l₁ := heads) (l₂ := bodies) (Nat.le_of_eq G.len.symm)
    calc (heads.zip bodies).map (fun q => q.1.fn.name) = ((heads.zip bodies).map Prod.fst).map (·.fn.name) := by
          rw [List.map_map]; rfl
      _ = _ := by rw [hz0]
  have := find?_unique (k := fun q : FnHead × Out => q.1.fn.name) (by rw [hz]; exact G.nodup) hp
  rw [show ((fun d : FnDef => d.name == p.1.fn.name) ∘ mkDef st pad) = fun q => q.1.fn.name == p.1.fn.name from rfl,
    this]
  rfl

/-- The state after a checked group of functions extends the world and keeps the top level's invariant. -/
theorem GroupOk.post {st : TopState} {ρ : List Value} {heads : List FnHead} {bodies : List Out} {pad : Nat}
    (G : GroupOk st ρ heads bodies pad) {st' : TopState} (hph : st'.phase = st.phase) (hsc : st'.sc = st.sc)
    (henv : st'.env = st.env) (hgoal : st'.goal = st.goal) (hproved : st'.proved = st.proved)
    (hfns : st'.fns = st.fns ++ (heads.zip bodies).map (mkDef st pad)) (hgroups : st'.groups = st.groups + 1)
    (hglob : ∀ n, st'.globals.find? (·.name == n) = (groupGlobals st heads).find? (·.name == n)) :
    (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ := by
  have hI := G.inv
  have hkind : ∀ n, kindOf st'.globals n = kindOf st.globals n := fun n => by
    rw [kindOf_congr hglob, kindOf_group]
  have hSc : (st'.world ρ).Sc = (st.world ρ).Sc := by simp [TopState.world, hsc]
  have hdef : ∀ d ∈ (heads.zip bodies).map (mkDef st pad), ∃ p ∈ heads.zip bodies, d = mkDef st pad p := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hd
    exact ⟨p, hp, rfl⟩
  have hle : (st.world ρ).Le (st'.world ρ) := by
    refine ⟨⟨fun n d hd => ?_, fun n k hd hk => ⟨?_, by simp only [TopState.world, hkind]; exact hk⟩⟩,
      by rw [hSc]; exact Sigs.Sub.refl _, List.prefix_refl _, fun h' sig' ws hd us hn hs => ?_⟩
    · simp only [TopState.world, hfns, Fns.find, List.find?_append] at hd ⊢
      rw [hd]; rfl
    · simp only [TopState.world, hfns, Fns.find, List.find?_append] at hd ⊢
      rw [hd, Option.none_or]
      refine List.find?_eq_none.2 fun d hdm he => ?_
      obtain ⟨p, hp, rfl⟩ := hdef d hdm
      obtain ⟨g, hg⟩ := kindOf_some hk
      rw [show n = p.1.fn.name from (by simpa [mkDef] using he : p.1.fn.name = n).symm,
        G.fresh _ (List.of_mem_zip hp).1] at hg
      cases hg
    · rw [hSc] at hs; rw [hs] at hn; cases hn
  refine ⟨hle, ?_⟩
  have hfind : ∀ W, (st'.world ρ).Le W → ∀ p ∈ heads.zip bodies, W.P.fns.find p.1.fn.name = some (mkDef st pad p) :=
    fun W hW p hp => hW.prog.fns _ _ (by simp only [TopState.world, hfns]; exact fns_find_group G hp)
  refine ⟨hph ▸ hI.phase, by rw [hSc, hsc]; exact hI.sat, by rw [hSc, hsc, henv]; exact hI.names, hsc ▸ hI.inert,
    hsc ▸ hI.sigsOk, hsc ▸ hI.rets, fun h sig hs => by rw [hkind]; exact hI.sigNames h sig (hsc ▸ hs), ?_, ?_, ?_,
    by rw [hgoal, hsc]; exact hI.goal, fun hp => ?_, hsc ▸ hI.typeSig⟩
  · intro d hd
    rw [hglob, groupGlobals, List.find?_append]
    rw [hfns] at hd
    rcases List.mem_append.1 hd with hd | hd
    · obtain ⟨sig, hs⟩ := hI.fnNames d hd
      exact ⟨sig, by rw [hs]; rfl⟩
    · obtain ⟨p, hp, rfl⟩ := hdef d hd
      have hm := (List.of_mem_zip hp).1
      refine ⟨some p.1.sig, ?_⟩
      rw [show (mkDef st pad p).name = p.1.fn.name from rfl, G.fresh _ hm, Option.none_or, List.find?_map]
      have := find?_unique (k := fun h : FnHead => h.fn.name) G.nodup hm
      rw [show ((fun g : Global => g.name == p.1.fn.name) ∘ fun h : FnHead => Global.fn h.fn.name
        (some h.sig)) = fun h => h.fn.name == p.1.fn.name from rfl, this]
      rfl
  · intro d hd
    rw [hfns] at hd
    rw [hgroups]
    rcases List.mem_append.1 hd with hd | hd
    · have := hI.groups d hd; omega
    · obtain ⟨p, hp, rfl⟩ := hdef d hd
      simp [mkDef]
  · intro W' hW' act hact
    rw [hsc]
    refine GlobalsOk.congr_find (fun n => (hglob n).symm) ?_
    refine GlobalsOk.group (hI.globals W' (hle.trans hW') act fun d hd => hact d (by rw [hfns]; simp [hd]))
      (fun f hf => by cases hf) fun h' hh' => ?_
    obtain ⟨hs', hpl'⟩ := G.spec h' hh'
    obtain ⟨htnt', hpar', hret', hsubl', hparl', hsubc', -, -⟩ := hs'.facts hpl' G.inv.inert
    obtain ⟨o', ho'⟩ := exists_zip G.len hh'
    refine ⟨htnt', hpar', hret', hsubl', mkDef st pad (h', o'), hfind W' hW' _ ho', by simp [mkDef, hparl'], rfl, rfl,
      by simp only [mkDef]; rw [← hsubc']; exact G.pad h' hh',
      (G.fnSpec (hle.trans hW') (hfind W' hW') _ ho').callSpec act, ?_⟩
    exact hact _ (by rw [hfns]; exact List.mem_append_right _ (List.mem_map_of_mem ho'))
  · obtain ⟨g, hg, hW⟩ := hI.proved (hproved ▸ hp)
    exact ⟨g, hgoal ▸ hg, fun W' hW' => hW W' (hle.trans hW')⟩

/-- A group of functions keeps the top level's invariant (SOUNDNESS.md part 6, with the main lemma for 5.1). -/
theorem fnGroup_ok {st st' : TopState} {ρ : List Value} {fs : List Fn} (hI : TopInv st ρ)
    (hp : fs.all Fn.plain = true) (h : fnGroup st fs = .ok st') : (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ := by
  simp only [fnGroup] at h
  obtain ⟨st0, h0, h⟩ := bind_eq_ok.1 h
  obtain ⟨⟨st1, heads⟩, h1, h⟩ := bind_eq_ok.1 h
  obtain ⟨⟨taint, bodies⟩, h2, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨rfl, hnd, hfr⟩ := fold0_spec fs st st0 h0
  obtain ⟨heads', hh, hmap, hspec, rfl⟩ := fold1_spec _ fs _ [] st1 heads h1
  simp only [List.nil_append] at hh
  subst hh
  have hname : ∀ h ∈ heads, h.fn.name = h.f.name.name := fun h hh => (hspec h hh).name
  have hnames : fs.map (·.name.name) = heads.map (·.fn.name) := by
    rw [← hmap, List.map_map]; exact List.map_congr_left fun h hh => (hname h hh).symm
  have hmemf : ∀ h ∈ heads, h.f ∈ fs := fun h hh => hmap ▸ List.mem_map_of_mem hh
  have hpl : ∀ h ∈ heads, h.f.plain = true := fun h hh => List.all_eq_true.1 hp _ (hmemf h hh)
  have hfr' : ∀ h ∈ heads, st.globals.find? (·.name == h.fn.name) = none := fun h hh => by
    rw [hname h hh]; exact hfr _ (hmemf h hh)
  have hnd' : (heads.map (·.fn.name)).Nodup := hnames ▸ hnd
  have hspec' : ∀ h ∈ heads, HeadSpec st.sc (heads.map (·.fn.name)) h ∧ h.f.plain = true := fun h hh => by
    have := hspec h hh
    rw [hnames] at this
    exact ⟨this, hpl h hh⟩
  have hfacts := fun h hh => ((hspec' h hh).1.facts (hpl h hh) hI.inert)
  have hnews : fs.map (fun f => Global.fn f.name.name none) = heads.map fun h => Global.fn h.fn.name none := by
    rw [← hmap, List.map_map]; exact List.map_congr_left fun h hh => by simp [hname h hh]
  have hgg : ∀ n, (setSigs (updSigs heads (st.globals ++ fs.map fun f => Global.fn f.name.name none)) heads
      (heads.map fun _ => false)).find? (·.name == n) = (groupGlobals st heads).find? (·.name == n) := by
    rw [hnews]; exact group_find hnd' hfr' fun h hh => (hfacts h hh).1
  have hclean : GlobalsClean (groupGlobals st heads) := by
    intro n m sig hg
    simp only [groupGlobals, List.find?_append] at hg
    cases hgs : st.globals.find? (·.name == n) with
    | some g =>
      rw [hgs, Option.some_or] at hg
      cases hg
      exact (hI.globals _ (World.Le.refl _) ⟨st.groups, []⟩ (fun d hd => hI.groups d hd) n _ hgs).tainted
    | none =>
      rw [hgs, Option.none_or, List.find?_map, Option.map_eq_some_iff] at hg
      obtain ⟨h, hh, he⟩ := hg
      cases he
      exact (hfacts h (List.mem_of_find?_eq_some hh)).1
  obtain ⟨htaint, hstep⟩ := fixTaint_clean h2 fun bodies hb o ho x hx => by
    obtain ⟨hl, hall⟩ := checkAll_spec hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    have hi' : i < heads.length := hl ▸ hi
    have hpz : (heads[i], bodies[i]) ∈ heads.zip bodies := List.mem_iff_getElem.2 ⟨i, by simp [hl, hi'], by simp⟩
    have hm : heads[i] ∈ heads := List.getElem_mem _
    have hbp : heads[i].f.body.plain = true := by
      have := hpl _ hm
      simp only [Fn.plain, Bool.and_eq_true] at this
      exact this.2
    exact (Expr.clean _ hbp _ _ _ _ hI.phase (GlobalsClean.congr_find (fun n => (hgg n).symm) hclean)
      (hfacts _ hm).2.2.2.2.2.2.1 (hall _ hpz)).2 x hx
  simp only at htaint
  subst htaint
  obtain ⟨hlen, hall⟩ := checkAll_spec hstep
  have G : GroupOk st ρ heads bodies ((heads.map fun h => h.fn.subterms.length).foldr max 0) :=
    ⟨hI, hlen, hspec', hnd', hfr', fun h hh => le_foldr_max (List.mem_map_of_mem hh),
      fun p hp => ⟨_, hI.phase, rfl, rfl, hgg, hall p hp⟩⟩
  exact G.post rfl rfl rfl rfl rfl rfl rfl hgg

end FnGroup

end Pledge
