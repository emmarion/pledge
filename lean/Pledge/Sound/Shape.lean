import Pledge.Sound.Term

namespace Pledge

/-- `checkExpr` ends with `finish` (§12, §16). -/
theorem checkExpr_finish {C : Ctx} {sc : Scope} {g : Option Given} {e : Expr} {o : Out}
    (h : checkExpr C sc g e = .ok o) :
    ∃ o₀, finish { C with erased := C.erased || g.any (·.allErased) } (C.erased || g.any (·.allErased))
      (if C.erased then g.map (·.erase) else g) e o₀ = .ok o := by
  unfold checkExpr at h
  obtain ⟨o₀, -, h⟩ := bind_eq_ok.1 h
  exact ⟨o₀, h⟩

/-- After an expression, in a tainted scope, every result is tainted and the tree is removed (§12); in a wholly
erased position the tree is removed (§16); and the expression produces a value. -/
theorem checkExpr_removed {C : Ctx} {sc : Scope} {g : Option Given} {e : Expr} {o : Out}
    (h : checkExpr C sc g e = .ok o) :
    o.res ≠ [] ∧ (o.sc.taintedBy.isSome → o.tree = .removed ∧ ∀ r ∈ o.res, r.tainted = true) ∧
      ((C.erased || g.any (·.allErased)) = true → o.tree = .removed) ∧
      ((∀ r ∈ o.res, r.tainted = true) → o.tree = .removed) := by
  obtain ⟨o₀, hf⟩ := checkExpr_finish h
  obtain ⟨hne, hsc, -, hres, htree, -⟩ := finish_spec hf
  have hall : (∀ r ∈ o.res, r.tainted = true) → o.tree = .removed := fun ha => by
    rw [htree]; simp [List.all_eq_true.2 fun r hr => ha r hr]
  refine ⟨by rw [hres]; split <;> simpa using hne, fun ht => ?_, fun hw => by rw [htree, hw]; rfl, hall⟩
  have hres' : ∀ r ∈ o.res, r.tainted = true := by
    rw [hsc] at ht
    rw [hres, if_pos ht]
    simp
  exact ⟨hall hres', hres'⟩

/-- What checking an expression keeps, whatever the scope's taint: signatures and names, no `_` (§16) to solve,
entries only added or given rules, and taint (§12). -/
def ExprShape (e : Expr) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (g : Option Given) (o : Out), sc.holes = [] → checkExpr C sc g e = .ok o →
    o.sc.sigs = sc.sigs ∧ o.sc.names = sc.names ∧ o.sc.holes = [] ∧ sc.Γ.eraseRules <+: o.sc.Γ.eraseRules ∧
    (sc.taintedBy.isSome → o.sc.taintedBy.isSome)

/-- What checking a statement keeps, whatever the scope's taint. -/
def StmtShape (s : Stmt) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (o : StmtOut), sc.holes = [] → checkStmt C sc s = .ok o →
    o.sc.sigs = sc.sigs ∧ o.sc.holes = [] ∧ sc.Γ.eraseRules <+: o.sc.Γ.eraseRules ∧
    (sc.taintedBy.isSome → o.sc.taintedBy.isSome)

theorem var_shape (x : Id) : ExprShape (.var x) := by
  intro C sc g o hh h
  unfold checkExpr at h
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 h
  obtain ⟨-, hsc, -⟩ := finish_spec hf
  simp only at h₀
  split at h₀
  · simp [failAt_eq] at h₀
  · split at h₀
    · obtain rfl := produced_eq hh h₀
      rw [hsc]
      exact ⟨rfl, rfl, hh, List.prefix_refl _, id⟩
    · simp [notValue, failAt_eq] at h₀

namespace ShapeFill

/-- What `ExprShape` says of the scope after an expression. -/
def Grows (sc sc' : Scope) : Prop :=
  sc'.sigs = sc.sigs ∧ sc'.names = sc.names ∧ sc'.holes = [] ∧ sc.Γ.eraseRules <+: sc'.Γ.eraseRules ∧
    (sc.taintedBy.isSome → sc'.taintedBy.isSome)

theorem Grows.refl {sc : Scope} (hh : sc.holes = []) : Grows sc sc := ⟨rfl, rfl, hh, List.prefix_refl _, id⟩

theorem Grows.trans {a b c : Scope} (h₁ : Grows a b) (h₂ : Grows b c) : Grows a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1, h₁.2.2.2.1.trans h₂.2.2.2.1, h₂.2.2.2.2 ∘ h₁.2.2.2.2⟩

theorem Grows.opened {sc : Scope} (hh : sc.holes = []) (tele : Telescope) (env : List Term) (kind : String)
    (pos : Pos) (taint : Nat → Bool) : Grows sc (opened sc tele env kind pos taint).1 := by
  obtain ⟨⟨t, ht⟩, -⟩ := opened_shape sc tele env kind pos taint
  exact ⟨rfl, rfl, hh, ⟨Entries.eraseRules t, by rw [← ht]; simp [Entries.eraseRules]⟩, id⟩

theorem isHole_false {e : Expr} (h : e.holeFree = true) : isHole e = false := by
  unfold isHole; split
  · simp [Expr.holeFree] at h
  · rfl

theorem args_grows {args : List Arg} (ih : ∀ a ∈ args, ExprShape a.expr)
    (hp : ∀ a ∈ args, a.expr.holeFree = true) :
    ∀ {C : Ctx} {sc : Scope} {owner role : String} {erased : Bool} {params : Telescope} {prev : List Res}
      {a : ArgsOut}, sc.holes = [] → checkArgs C sc owner role erased params prev args = .ok a → Grows sc a.sc := by
  induction args with
  | nil =>
    intro C sc owner role erased params prev a hh h
    simp only [checkArgs, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact Grows.refl hh
  | cons arg args ihs =>
    intro C sc owner role erased params prev a hh h
    obtain ⟨m, e⟩ := arg
    cases params with
    | nil => simp [checkArgs, internal, failAt_eq] at h
    | cons p ps =>
      have he : isHole e = false := isHole_false (hp _ List.mem_cons_self)
      simp only [checkArgs, he, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
      obtain ⟨r, -, h⟩ := bind_eq_ok.1 h
      obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [keep_ok] at hrest
      have h₁ : Grows sc o.sc := ih (.mk m e) List.mem_cons_self C sc _ o hh ho
      exact h₁.trans (ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha))
        (fun a ha => hp a (List.mem_cons_of_mem _ ha)) (a := rest) h₁.2.2.1 hrest)

theorem elems_grows {es : List Expr} (ih : ∀ e ∈ es, ExprShape e) :
    ∀ {C : Ctx} {sc : Scope} {g : Option Given} {prev : List Res} {o : ElemsOut}, sc.holes = [] →
      checkElems C sc g prev es = .ok o → Grows sc o.sc := by
  induction es with
  | nil =>
    intro C sc g prev o hh h
    simp only [checkElems, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact Grows.refl hh
  | cons e es ihs =>
    intro C sc g prev o hh h
    simp only [checkElems] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨r, -, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    have h₁ : Grows sc o₁.sc := ih e List.mem_cons_self C sc _ o₁ hh ho₁
    exact h₁.trans (ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha)) (o := rest) h₁.2.2.1 hrest)

/-- What `StmtShape` says, for a list of statements. -/
theorem stmts_grows {ss : List Stmt} (ih : ∀ s ∈ ss, StmtShape s) :
    ∀ {C : Ctx} {sc : Scope} {o : StmtsOut}, sc.holes = [] → checkStmts C sc ss = .ok o →
      o.sc.sigs = sc.sigs ∧ o.sc.holes = [] ∧ sc.Γ.eraseRules <+: o.sc.Γ.eraseRules ∧
        (sc.taintedBy.isSome → o.sc.taintedBy.isSome) := by
  induction ss with
  | nil =>
    intro C sc o hh h
    simp only [checkStmts, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, hh, List.prefix_refl _, id⟩
  | cons s ss ihs =>
    intro C sc o hh h
    simp only [checkStmts] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    obtain ⟨a₁, a₂, a₃, a₄⟩ := ih s List.mem_cons_self C sc o₁ hh ho₁
    obtain ⟨b₁, b₂, b₃, b₄⟩ := ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha)) a₂ hrest
    exact ⟨b₁.trans a₁, b₂, a₃.trans b₃, b₄ ∘ a₄⟩

theorem applied_opened {sc : Scope} (hh : sc.holes = []) {tele : Telescope} {env : List Term} {name : String}
    {pos pos' : Pos} {taint : Nat → Bool} {g : Option Given} {tree : Expr} {since : Nat} {snaps : List Snapshot}
    {o : Out} (h : applied (opened sc tele env name pos taint).1 g pos' (opened sc tele env name pos taint).2 tree
      since snaps = .ok o) : Grows sc o.sc := by
  obtain ⟨rfl, -⟩ := applied_eq (by exact hh) h
  exact Grows.opened hh ..

end ShapeFill

theorem app_shape {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprShape a.expr)
    (hh : ∀ a ∈ args, a.expr.holeFree = true) : ExprShape (.app h args) := by
  intro C sc g o hsh hc
  unfold checkExpr at hc
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 hc
  obtain ⟨-, hsc, -⟩ := finish_spec hf
  show ShapeFill.Grows sc o.sc
  rw [hsc]
  simp only [Ctx.global] at h₀
  cases hg : C.globals.find? (·.name == h.name) with
  | none => simp [hg, notApplied, failAt_eq] at h₀
  | some gl =>
    cases gl with
    | fn m sig =>
      cases sig with
      | none => simp [hg, failAt_eq] at h₀
      | some sig =>
        simp only [hg] at h₀
        split at h₀
        all_goals
          repeat obtain ⟨_, _, h₀⟩ := bind_eq_ok.1 h₀
          rw [keep_ok] at h₀
          have hg := ShapeFill.args_grows ih hh hsh (by assumption)
          split at h₀ <;> (try obtain ⟨_, -, h₀⟩ := bind_eq_ok.1 h₀) <;>
            exact hg.trans (ShapeFill.applied_opened hg.2.2.1 h₀)
    | type T cs d | ctor c =>
      simp only [hg, ↓reduceIte] at h₀
      obtain ⟨u, -, h₀⟩ := bind_eq_ok.1 h₀
      obtain ⟨sig, -, h₀⟩ := bind_eq_ok.1 h₀
      obtain ⟨u₂, -, h₀⟩ := bind_eq_ok.1 h₀
      obtain ⟨a, ha, h₀⟩ := bind_eq_ok.1 h₀
      have hg := ShapeFill.args_grows ih hh hsh ha
      obtain ⟨rfl, -⟩ := applied_eq hg.2.2.1 h₀
      exact hg

theorem tuple_shape (p : Pos) {es : List Expr} (ih : ∀ e ∈ es, ExprShape e) : ExprShape (.tuple p es) := by
  intro C sc g o hsh hc
  unfold checkExpr at hc
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 hc
  obtain ⟨-, hsc, -⟩ := finish_spec hf
  show ShapeFill.Grows sc o.sc
  rw [hsc]
  simp only at h₀
  split at h₀
  all_goals (try split at h₀)
  all_goals (try (simp [miscount, failAt_eq, bind, Except.bind] at h₀; done))
  all_goals
    obtain ⟨oe, hoe, h₀⟩ := bind_eq_ok.1 h₀
    simp only [pure, Except.pure, Except.ok.injEq] at h₀
    subst h₀
    exact ShapeFill.elems_grows ih hsh hoe

theorem block_shape {ss : List Stmt} {f : Expr} (ihs : ∀ s ∈ ss, StmtShape s) (ihf : ExprShape f) :
    ExprShape (.block ss f) := by
  intro C sc g o hsh hc
  unfold checkExpr at hc
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 hc
  obtain ⟨-, hsc, -⟩ := finish_spec hf
  show ShapeFill.Grows sc o.sc
  rw [hsc]
  simp only at h₀
  obtain ⟨s, hs, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨of, hof, h₀⟩ := bind_eq_ok.1 h₀
  simp only [pure, Except.pure, Except.ok.injEq] at h₀
  subst h₀
  rw [keep_ok] at hof
  obtain ⟨a₁, -, a₃, a₄⟩ := ShapeFill.stmts_grows ihs (sc := { sc with holes := [] }) rfl hs
  obtain ⟨b₁, -, b₃, b₄, b₅⟩ := ihf _ { s.sc with holes := sc.holes } _ of hsh hof
  exact ⟨b₁.trans a₁, rfl, b₃, a₃.trans b₄, b₅ ∘ a₄⟩

theorem match_shape {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch} (ihs : ExprShape s) :
    ExprShape (.match p m s ann bs) := by
  intro C sc g o hsh hc
  unfold checkExpr at hc
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 hc
  obtain ⟨-, hsc, -⟩ := finish_spec hf
  show ShapeFill.Grows sc o.sc
  rw [hsc]
  simp only at h₀
  obtain ⟨so, hso, h₀⟩ := bind_eq_ok.1 h₀
  rw [keep_ok] at h₀
  have h₁ : ShapeFill.Grows sc so.sc := ihs _ sc none so hsh hso
  obtain ⟨r, -, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨⟨tele, tenv⟩, -, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨fs, -, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨u1, -, h₀⟩ := bind_eq_ok.1 h₀
  split at h₀
  case isFalse => simp [failAt_eq, bind, Except.bind] at h₀
  split at h₀
  all_goals (try split at h₀)
  all_goals (try (simp [failAt_eq, bind, Except.bind] at h₀; done))
  all_goals
    obtain ⟨u4, -, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨bo, -, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨o', ho', h₀⟩ := bind_eq_ok.1 h₀
    simp only [pure, Except.pure, Except.ok.injEq] at h₀
    subst h₀
    rw [keep_ok] at ho'
    obtain rfl := produced_eq (by exact h₁.2.2.1) ho'
    exact h₁.trans (ShapeFill.Grows.opened h₁.2.2.1 ..)

theorem Entries.eraseRules_prefix {Γ Γ' : Entries} (h : Γ <+: Γ') : Γ.eraseRules <+: Γ'.eraseRules := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨Entries.eraseRules t, by simp [Entries.eraseRules]⟩

theorem sorry_shape (p : Pos) (t : Tele) : ExprShape (.sorry p t) := by
  intro C sc g o hh h
  unfold checkExpr at h
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 h
  obtain ⟨-, hsc, -⟩ := finish_spec hf
  simp only at h₀
  obtain ⟨⟨tele, env⟩, -, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨hpre, -⟩ := opened_shape sc tele env "sorry" p fun _ => true
  have hh' : (opened sc tele env "sorry" p fun _ => true).1.holes = [] := hh
  obtain rfl := produced_eq hh' h₀
  rw [hsc]
  exact ⟨rfl, rfl, hh, Entries.eraseRules_prefix hpre, id⟩

theorem removed_shape : ExprShape .removed := by
  intro C sc g o _ h
  simp [checkExpr, internal, failAt_eq, bind, Except.bind] at h

theorem let_shape {p : Pos} {bs : List LetBinder} {rhs : Expr} (ih : ExprShape rhs) : StmtShape (.let p bs rhs) := by
  intro C sc o hsh h
  simp only [checkStmt] at h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨ws, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨a₁, -, a₃, a₄, a₅⟩ := ih C sc _ o' hsh ho'
  rw [Scope.bind_eq]
  exact ⟨a₁, a₃, a₄, a₅⟩

theorem patlet_shape {p : Pos} {ct : Bool} {m : Option Mult} {pat : Pattern} {rhs : Expr} (ih : ExprShape rhs) :
    StmtShape (.patlet p ct m pat rhs) := by
  intro C sc o hsh h
  simp only [checkStmt] at h
  split at h
  · simp [failAt_eq, bind, Except.bind] at h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
  rw [keep_ok] at h
  obtain ⟨r, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨fs, hfs, h⟩ := bind_eq_ok.1 h
  obtain ⟨sc', hsc', h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨a₁, -, a₃, a₄, a₅⟩ := ih _ sc none o' hsh ho'
  obtain ⟨Γ, ids, ⟨f, hf, hfo⟩, -, rfl⟩ := patBind_spec hsc'
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (List.mem_of_find?_eq_some hf)
  obtain ⟨_, -, -, -, hfs'⟩ := forcings_spec hfs
  obtain ⟨sig, mk, -, hforce, -⟩ := hfs' i f hi
  rw [hforce] at hfo
  obtain ⟨-, hpre, -⟩ := force_eraseRules hfo
  rw [Scope.bind_eq]
  refine ⟨a₁, a₃, a₄.trans hpre, fun ht => ?_⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (a₅ ht)
  simp [reach, hx]

theorem inspect_shape (p : Pos) : StmtShape (.inspect p) := by
  intro C sc o _ h
  simp only [checkStmt, pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, ‹_›, List.prefix_refl _, id⟩

theorem Arg.sizeOf_expr_lt {a : Arg} {args : List Arg} (h : a ∈ args) : sizeOf a.expr < 1 + sizeOf args := by
  have := List.sizeOf_lt_of_mem h
  cases a; simp only [Arg.expr, Arg.mk.sizeOf_spec] at *; omega

theorem Branch.sizeOf_body_lt' {b : Branch} {bs : List Branch} (h : b ∈ bs) : sizeOf b.body < sizeOf bs := by
  have := List.sizeOf_lt_of_mem h
  cases b; simp only [Branch.body, Branch.mk.sizeOf_spec] at *; omega

mutual
/-- `ExprShape` for every expression without `_` (§16). -/
theorem Expr.shape : (e : Expr) → e.holeFree = true → ExprShape e
  | .var x, _ => var_shape x
  | .app h args, hp => by
    simp only [Expr.holeFree] at hp
    have hargs := Arg.holeFreeList_iff.1 hp
    exact app_shape (fun a ha => Expr.shape a.expr (by rw [← Arg.holeFree_expr]; exact hargs a ha))
      (fun a ha => by rw [← Arg.holeFree_expr]; exact hargs a ha)
  | .tuple p es, hp => by
    simp only [Expr.holeFree] at hp
    exact tuple_shape p fun e he => Expr.shape e (Expr.holeFreeList_iff.1 hp e he)
  | .block ss f, hp => by
    simp only [Expr.holeFree, Bool.and_eq_true] at hp
    exact block_shape (fun s hs => Stmt.shape s (Stmt.holeFreeList_iff.1 hp.1 s hs)) (Expr.shape f hp.2)
  | .match p m s ann bs, hp => by
    simp only [Expr.holeFree, Bool.and_eq_true] at hp
    exact match_shape (Expr.shape s hp.1)
  | .sorry p t, _ => sorry_shape p t
  | .removed, _ => removed_shape
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (have := Arg.sizeOf_expr_lt ‹_›; simp only [Expr.app.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem ‹_›; simp only [Expr.tuple.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem ‹_›; simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.match.sizeOf_spec]; omega)
theorem Stmt.shape : (s : Stmt) → s.holeFree = true → StmtShape s
  | .let p bs rhs, hp => let_shape (Expr.shape rhs hp)
  | .patlet p ct m pat rhs, hp => patlet_shape (Expr.shape rhs hp)
  | .inspect p, _ => inspect_shape p
termination_by s => sizeOf s
decreasing_by all_goals (simp only [Stmt.let.sizeOf_spec, Stmt.patlet.sizeOf_spec]; omega)
end

end Pledge
