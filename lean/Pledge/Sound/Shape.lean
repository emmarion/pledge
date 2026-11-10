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
  sorry

theorem app_shape {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprShape a.expr)
    (hh : ∀ a ∈ args, a.expr.holeFree = true) : ExprShape (.app h args) := by
  sorry

theorem tuple_shape (p : Pos) {es : List Expr} (ih : ∀ e ∈ es, ExprShape e) : ExprShape (.tuple p es) := by
  sorry

theorem block_shape {ss : List Stmt} {f : Expr} (ihs : ∀ s ∈ ss, StmtShape s) (ihf : ExprShape f) :
    ExprShape (.block ss f) := by
  sorry

theorem match_shape {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch} (ihs : ExprShape s) :
    ExprShape (.match p m s ann bs) := by
  sorry

theorem sorry_shape (p : Pos) (t : Tele) : ExprShape (.sorry p t) := by
  sorry

theorem removed_shape : ExprShape .removed := by
  intro C sc g o _ h
  simp [checkExpr, internal, failAt_eq, bind, Except.bind] at h

theorem let_shape {p : Pos} {bs : List LetBinder} {rhs : Expr} (ih : ExprShape rhs) : StmtShape (.let p bs rhs) := by
  sorry

theorem patlet_shape {p : Pos} {ct : Bool} {m : Option Mult} {pat : Pattern} {rhs : Expr} (ih : ExprShape rhs) :
    StmtShape (.patlet p ct m pat rhs) := by
  sorry

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
