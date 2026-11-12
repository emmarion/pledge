import Pledge.Sound.Term

namespace Pledge

/-- `checkExpr` ends with `finish` (§12, §16). -/
theorem checkExpr_finish {C : Ctx} {sc : Scope} {g : Option Given} {e : Expr} {o : Out}
    (h : checkExpr C sc g e = .ok o) :
    ∃ o₀, finish (C.enter (C.erased || g.any (·.allErased)))
      (C.erased || g.any (·.allErased))
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
    simp [hres, ht]
  exact ⟨hall hres', hres'⟩

/-- What checking an expression keeps, whatever the scope's taint: signatures and names, entries only added or given
rules, and taint (§12). -/
def ExprShape (e : Expr) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (g : Option Given) (o : Out), checkExpr C sc g e = .ok o →
    o.sc.sigs = sc.sigs ∧ o.sc.names = sc.names ∧ sc.Γ.eraseRules <+: o.sc.Γ.eraseRules ∧
    (sc.taintedBy.isSome → o.sc.taintedBy.isSome)

/-- What checking a statement keeps, whatever the scope's taint. -/
def StmtShape (s : Stmt) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (o : StmtOut), checkStmt C sc s = .ok o →
    o.sc.sigs = sc.sigs ∧ sc.Γ.eraseRules <+: o.sc.Γ.eraseRules ∧ (sc.taintedBy.isSome → o.sc.taintedBy.isSome)

theorem var_shape (x : Id) : ExprShape (.var x) := by
  intro C sc g o h
  unfold checkExpr at h
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 h
  obtain ⟨-, hsc, -⟩ := finish_spec hf
  simp only at h₀
  split at h₀
  · simp [failAt_eq] at h₀
  · split at h₀
    · obtain rfl := produced_eq h₀
      rw [hsc]
      exact ⟨rfl, rfl, List.prefix_refl _, id⟩
    · simp [notValue, failAt_eq] at h₀

/-- One argument of a call or application (§8): a `_` (§16), or an expression checked against its parameter. -/
theorem checkArgs_cons {C : Ctx} {sc : Scope} {owner role : String} {er : Bool} {p : TBinder} {ps : Telescope}
    {prev : List Res} {m : Option Mark} {e : Expr} {as : List Arg} {out : ArgsOut}
    (h : checkArgs C sc owner role er (p :: ps) prev (.mk m e :: as) = .ok out) :
    ∃ o r rest, (if isHole e then holeArg C sc (argGiven p prev role owner er) p prev e.pos
        else checkExpr C sc (some (argGiven p prev role owner er)) e) = .ok o ∧ o.res = [r] ∧
      checkArgs C o.sc owner role er ps (prev ++ [r]) as = .ok rest ∧
      out = ⟨rest.sc, r :: rest.res, .mk m o.tree :: rest.trees, o.snaps ++ rest.snaps⟩ := by
  rw [checkArgs] at h
  split at h <;>
  · rename_i hc
    obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
    obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    rw [keep_ok] at hr hrest
    exact ⟨o, r, rest, by simpa [hc] using ho, single_ok hr, hrest, h.symm⟩

namespace ShapeFill

/-- What `ExprShape` says of the scope after an expression. -/
def Grows (sc sc' : Scope) : Prop :=
  sc'.sigs = sc.sigs ∧ sc'.names = sc.names ∧ sc.Γ.eraseRules <+: sc'.Γ.eraseRules ∧
    (sc.taintedBy.isSome → sc'.taintedBy.isSome)

theorem Grows.refl (sc : Scope) : Grows sc sc := ⟨rfl, rfl, List.prefix_refl _, id⟩

theorem Grows.trans {a b c : Scope} (h₁ : Grows a b) (h₂ : Grows b c) : Grows a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₁.2.2.1.trans h₂.2.2.1, h₂.2.2.2 ∘ h₁.2.2.2⟩

theorem Grows.opened (sc : Scope) (tele : Telescope) (env : List Term) (kind : String)
    (pos : Pos) (taint : Nat → Bool) : Grows sc (opened sc tele env kind pos taint).1 := by
  obtain ⟨⟨t, ht⟩, -⟩ := opened_shape sc tele env kind pos taint
  exact ⟨rfl, rfl, ⟨Entries.eraseRules t, by rw [← ht]; simp [Entries.eraseRules]⟩, id⟩

theorem args_grows {args : List Arg} (ih : ∀ a ∈ args, ExprShape a.expr) :
    ∀ {C : Ctx} {sc : Scope} {owner role : String} {erased : Bool} {params : Telescope} {prev : List Res}
      {a : ArgsOut}, checkArgs C sc owner role erased params prev args = .ok a → Grows sc a.sc := by
  induction args with
  | nil =>
    intro C sc owner role erased params prev a h
    simp only [checkArgs, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact Grows.refl _
  | cons arg args ihs =>
    intro C sc owner role erased params prev a h
    obtain ⟨m, e⟩ := arg
    cases params with
    | nil => simp [checkArgs, internal, failAt_eq] at h
    | cons p ps =>
      obtain ⟨o, r, rest, ho, -, hrest, rfl⟩ := checkArgs_cons h
      have h₁ : Grows sc o.sc := by
        split at ho
        · rw [(holeArg_spec ho).2.1]; exact Grows.refl _
        · exact ih (.mk m e) List.mem_cons_self C sc _ o ho
      exact h₁.trans (ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha)) (a := rest) hrest)

theorem elems_grows {es : List Expr} (ih : ∀ e ∈ es, ExprShape e) :
    ∀ {C : Ctx} {sc : Scope} {g : Option Given} {prev : List Res} {o : ElemsOut},
      checkElems C sc g prev es = .ok o → Grows sc o.sc := by
  induction es with
  | nil =>
    intro C sc g prev o h
    simp only [checkElems, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact Grows.refl _
  | cons e es ihs =>
    intro C sc g prev o h
    simp only [checkElems] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨r, -, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    have h₁ : Grows sc o₁.sc := ih e List.mem_cons_self C sc _ o₁ ho₁
    exact h₁.trans (ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha)) (o := rest) hrest)

/-- What `StmtShape` says, for a list of statements. -/
theorem stmts_grows {ss : List Stmt} (ih : ∀ s ∈ ss, StmtShape s) :
    ∀ {C : Ctx} {sc : Scope} {o : StmtsOut}, checkStmts C sc ss = .ok o →
      o.sc.sigs = sc.sigs ∧ sc.Γ.eraseRules <+: o.sc.Γ.eraseRules ∧ (sc.taintedBy.isSome → o.sc.taintedBy.isSome) := by
  induction ss with
  | nil =>
    intro C sc o h
    simp only [checkStmts, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, List.prefix_refl _, id⟩
  | cons s ss ihs =>
    intro C sc o h
    simp only [checkStmts] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    obtain ⟨a₁, a₃, a₄⟩ := ih s List.mem_cons_self C sc o₁ ho₁
    obtain ⟨b₁, b₃, b₄⟩ := ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha)) hrest
    exact ⟨b₁.trans a₁, a₃.trans b₃, b₄ ∘ a₄⟩

theorem applied_opened {sc : Scope} {tele : Telescope} {env : List Term} {name : String}
    {pos pos' : Pos} {taint : Nat → Bool} {g : Option Given} {tree : Expr} {snaps : List Snapshot}
    {o : Out} (h : applied (opened sc tele env name pos taint).1 g pos' (opened sc tele env name pos taint).2 tree
      snaps = .ok o) : Grows sc o.sc := by
  obtain ⟨rfl, -⟩ := applied_eq h
  exact Grows.opened ..

end ShapeFill

theorem app_shape {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprShape a.expr) : ExprShape (.app h args) := by
  intro C sc g o hc
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
          have hg := ShapeFill.args_grows ih (by assumption)
          split at h₀ <;> (try obtain ⟨_, -, h₀⟩ := bind_eq_ok.1 h₀) <;>
            exact hg.trans (ShapeFill.applied_opened h₀)
    | type T cs d | ctor c =>
      simp only [hg, ↓reduceIte] at h₀
      obtain ⟨u, -, h₀⟩ := bind_eq_ok.1 h₀
      obtain ⟨sig, -, h₀⟩ := bind_eq_ok.1 h₀
      obtain ⟨u₂, -, h₀⟩ := bind_eq_ok.1 h₀
      obtain ⟨a, ha, h₀⟩ := bind_eq_ok.1 h₀
      have hg := ShapeFill.args_grows ih ha
      obtain ⟨rfl, -⟩ := applied_eq h₀
      exact hg

theorem tuple_shape (p : Pos) {es : List Expr} (ih : ∀ e ∈ es, ExprShape e) : ExprShape (.tuple p es) := by
  intro C sc g o hc
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
    exact ShapeFill.elems_grows ih hoe

theorem block_shape {ss : List Stmt} {f : Expr} (ihs : ∀ s ∈ ss, StmtShape s) (ihf : ExprShape f) :
    ExprShape (.block ss f) := by
  intro C sc g o hc
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
  obtain ⟨a₁, a₃, a₄⟩ := ShapeFill.stmts_grows ihs hs
  obtain ⟨b₁, -, b₄, b₅⟩ := ihf _ s.sc _ of hof
  exact ⟨b₁.trans a₁, rfl, a₃.trans b₄, b₅ ∘ a₄⟩

theorem match_shape {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch} (ihs : ExprShape s) :
    ExprShape (.match p m s ann bs) := by
  intro C sc g o hc
  unfold checkExpr at hc
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 hc
  obtain ⟨-, hsc, -⟩ := finish_spec hf
  show ShapeFill.Grows sc o.sc
  rw [hsc]
  simp only at h₀
  obtain ⟨so, hso, h₀⟩ := bind_eq_ok.1 h₀
  rw [keep_ok] at h₀
  have h₁ : ShapeFill.Grows sc so.sc := ihs _ sc none so hso
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
    obtain rfl := produced_eq ho'
    exact h₁.trans (ShapeFill.Grows.opened ..)

theorem Entries.eraseRules_prefix {Γ Γ' : Entries} (h : Γ <+: Γ') : Γ.eraseRules <+: Γ'.eraseRules := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨Entries.eraseRules t, by simp [Entries.eraseRules]⟩

theorem sorry_shape (p : Pos) (t : Tele) : ExprShape (.sorry p t) := by
  intro C sc g o h
  unfold checkExpr at h
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 h
  obtain ⟨-, hsc, -⟩ := finish_spec hf
  simp only at h₀
  obtain ⟨⟨tele, env⟩, -, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨hpre, -⟩ := opened_shape sc tele env "sorry" p fun _ => true
  obtain rfl := produced_eq h₀
  rw [hsc]
  exact ⟨rfl, rfl, Entries.eraseRules_prefix hpre, id⟩

theorem removed_shape : ExprShape .removed := by
  intro C sc g o h
  simp [checkExpr, internal, failAt_eq, bind, Except.bind] at h

/-- A tuple `let` (§8): its right-hand side is checked against its binders, as `letWants` gives them when they have
no `_` (§20), and otherwise right-hand side first, given only their multiplicities; its binders name the results. -/
theorem let_steps {C : Ctx} {sc : Scope} {p : Pos} {bs : List LetBinder} {rhs : Expr} {o : StmtOut}
    (h : checkStmt C sc (.let p bs rhs) = .ok o) :
    ∃ o' ws, checkExpr C sc (some (letGiven bs ws)) rhs = .ok o' ∧ ws.length = bs.length ∧
      (∀ (i : Nat) (w : Want) (b : LetBinder), ws[i]? = some w → bs[i]? = some b → w.mult = b.mult.getD .many) ∧
      ((holedLet bs = false ∧ letWants C sc bs = .ok ws) ∨ holedLet bs = true) ∧
      o = ⟨o'.sc.bind (bs.map LetBinder.name) ((bs.zip o'.res).map fun (x : LetBinder × Res) =>
        ({ x.2 with erased := x.1.mult == some Mult.erased } : Res)), .let p bs o'.tree, o'.snaps⟩ := by
  simp only [checkStmt] at h
  obtain ⟨u, -, h'⟩ := bind_eq_ok.1 h
  clear h
  have h := h'
  clear h'
  by_cases hr : holedLet bs = true
  · simp only [hr, ↓reduceIte] at h
    obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
    obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq, ok_bind] at h
    refine ⟨o', _, ho', by simp, fun i w b hw hb => ?_, .inr hr, h.symm⟩
    simp only [List.getElem?_map, hb, Option.map_some, Option.some.injEq] at hw
    subst hw; rfl
  · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
    have hf : holedLet bs = false := by simpa using hr
    obtain ⟨ws, hws, h₁⟩ := bind_eq_ok.1 h
    clear h
    obtain ⟨hwl, hwm⟩ := letWants_spec hws
    obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h₁
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨o', ws, ho', hwl, hwm, .inl ⟨hf, hws⟩, h.symm⟩

theorem let_shape {p : Pos} {bs : List LetBinder} {rhs : Expr} (ih : ExprShape rhs) : StmtShape (.let p bs rhs) := by
  intro C sc o h
  obtain ⟨o', ws, ho', -, -, -, rfl⟩ := let_steps h
  obtain ⟨a₁, -, a₄, a₅⟩ := ih C sc _ o' ho'
  rw [Scope.bind_eq]
  exact ⟨a₁, a₄, a₅⟩

theorem patlet_shape {p : Pos} {ct : Bool} {m : Option Mult} {pat : Pattern} {rhs : Expr} (ih : ExprShape rhs) :
    StmtShape (.patlet p ct m pat rhs) := by
  intro C sc o h
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
  obtain ⟨a₁, -, a₄, a₅⟩ := ih _ sc none o' ho'
  obtain ⟨Γ, ids, ⟨f, hf, hfo⟩, -, rfl⟩ := patBind_spec hsc'
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 (List.mem_of_find?_eq_some hf)
  obtain ⟨_, -, -, -, hfs'⟩ := forcings_spec hfs
  obtain ⟨sig, mk, -, hforce, -⟩ := hfs' i f hi
  rw [hforce] at hfo
  obtain ⟨-, hpre, -⟩ := force_eraseRules hfo
  rw [Scope.bind_eq]
  refine ⟨a₁, a₄.trans hpre, fun ht => ?_⟩
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (a₅ ht)
  simp [reach, hx]

theorem inspect_shape (p : Pos) : StmtShape (.inspect p) := by
  intro C sc o h
  simp only [checkStmt, pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, List.prefix_refl _, id⟩

theorem Arg.sizeOf_expr_lt {a : Arg} {args : List Arg} (h : a ∈ args) : sizeOf a.expr < 1 + sizeOf args := by
  have := List.sizeOf_lt_of_mem h
  cases a; simp only [Arg.expr, Arg.mk.sizeOf_spec] at *; omega

theorem Branch.sizeOf_body_lt' {b : Branch} {bs : List Branch} (h : b ∈ bs) : sizeOf b.body < sizeOf bs := by
  have := List.sizeOf_lt_of_mem h
  cases b; simp only [Branch.body, Branch.mk.sizeOf_spec] at *; omega

mutual
/-- `ExprShape` for every expression. -/
theorem Expr.shape : (e : Expr) → ExprShape e
  | .var x => var_shape x
  | .app h args => app_shape fun a _ => Expr.shape a.expr
  | .tuple p es => tuple_shape p fun e _ => Expr.shape e
  | .block ss f => block_shape (fun s _ => Stmt.shape s) (Expr.shape f)
  | .match p m s ann bs => match_shape (Expr.shape s)
  | .sorry p t => sorry_shape p t
  | .removed => removed_shape
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (have := Arg.sizeOf_expr_lt ‹_›; simp only [Expr.app.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem ‹_›; simp only [Expr.tuple.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem ‹_›; simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.match.sizeOf_spec]; omega)
theorem Stmt.shape : (s : Stmt) → StmtShape s
  | .let p bs rhs => let_shape (Expr.shape rhs)
  | .patlet p ct m pat rhs => patlet_shape (Expr.shape rhs)
  | .inspect p => inspect_shape p
termination_by s => sizeOf s
decreasing_by all_goals (simp only [Stmt.let.sizeOf_spec, Stmt.patlet.sizeOf_spec]; omega)
end

end Pledge
