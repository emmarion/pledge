import Pledge.Sound.Match
import Pledge.Sound.Call
import Pledge.Sound.Simple
import Pledge.Sound.Erased

namespace Pledge

/-! The main lemma (SOUNDNESS.md Theorems 5.1 and 6.2, with taint and erasure), one lemma per construct. Each
case lemma is about an untainted scope (`Inv`); `Expr.sound` and `Stmt.sound` assemble them. -/

/-- A variable (§2): its name's ideal value, and the evaluator's value for an untainted name. -/
theorem var_sound (x : Id) : ExprSound (.var x) := by
  intro C sc g n0 W ρ act o hI hg h
  refine ⟨?_, fun _ ha => by simp [Expr.absurd] at ha⟩
  unfold checkExpr at h
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 h
  simp only at h₀
  split at h₀
  · simp [failAt_eq] at h₀
  · split at h₀
    · exact Simple.var_post hI hg ‹_› ‹_› h₀ hf
    · simp [notValue, failAt_eq] at h₀

/-- A call (§8, §9, §12): its arguments' ideal values satisfy the parameters; for an untainted function and
untainted arguments, the measure decreases and the callee's specification gives typed ideal results, and the call
runs on the arguments' run-time values; otherwise every result is tainted, opened to `junk` or its `is` clause's
value (`FnOk.cons`), and the tree is removed. -/
theorem call_sound {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr)
    (ihs : ∀ a ∈ args, ExprShape a.expr) (hh : ∀ a ∈ args, a.expr.holeFree = true) {C : Ctx} {sc : Scope}
    {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {act : Act} {o : Out} {m : String} {sig : FnSig}
    (hI : Inv C sc n0 W ρ act) (hg : ∀ g', g = some g' → g'.Ok W.Sc ρ)
    (hgl : C.global h.name = some (.fn m (some sig))) (h : checkExpr C sc g (.app h args) = .ok o) :
    ExprPost C sc g n0 W ρ act o := by
  exact Call.sound ih ihs hh hI hg hgl h

/-- An application of a type constructor or value constructor (§8): its arguments' ideal values satisfy the
telescope, the untainted application is typed, and it runs to the head applied to the arguments' run-time values,
an erased argument (§16) only approximating. -/
theorem ctorApp_sound {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr)
    (ihs : ∀ a ∈ args, ExprShape a.expr) (hh : ∀ a ∈ args, a.expr.holeFree = true) {C : Ctx} {sc : Scope}
    {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {act : Act} {o : Out}
    (hI : Inv C sc n0 W ρ act) (hg : ∀ g', g = some g' → g'.Ok W.Sc ρ)
    (hgl : (C.global h.name).any (fun gl => gl matches .type .. || gl matches .ctor _) = true)
    (h : checkExpr C sc g (.app h args) = .ok o) : ExprPost C sc g n0 W ρ act o := by
  unfold checkExpr at h
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 h
  simp only [Ctx.global] at hgl h₀
  split at h₀
  · rename_i hT; simp [hT] at hgl
  · rename_i T cs d hT
    simp only [hT] at h₀
    obtain ⟨u, -, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨sig, hsig, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨u₂, har, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨a, ha, h₀⟩ := bind_eq_ok.1 h₀
    exact Simple.ctorApp_post ih ihs hh hI hg (hI.globals.type hT).1 rfl (Scope.sig_ok hsig) (arity_ok har) ha h₀ hf
  · rename_i c hT
    simp only [hT] at h₀
    obtain ⟨u, -, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨sig, hsig, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨u₂, har, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨a, ha, h₀⟩ := bind_eq_ok.1 h₀
    exact Simple.ctorApp_post ih ihs hh hI hg (hI.globals.ctor hT) rfl (Scope.sig_ok hsig) (arity_ok har) ha h₀ hf
  · simp [notApplied, failAt_eq] at h₀

theorem app_sound {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr)
    (ihs : ∀ a ∈ args, ExprShape a.expr) (hh : ∀ a ∈ args, a.expr.holeFree = true) : ExprSound (.app h args) := by
  intro C sc g n0 W ρ act o hI hg hc
  refine ⟨?_, fun _ ha => by simp [Expr.absurd] at ha⟩
  cases hgl : C.global h.name with
  | none =>
    obtain ⟨o₀, h₀, -⟩ := bind_eq_ok.1 (show checkExpr C sc g (.app h args) = .ok o from hc)
    simp only [Ctx.global] at hgl h₀
    simp [hgl, notApplied, failAt_eq] at h₀
  | some gl =>
    cases gl with
    | fn n s =>
      cases s with
      | none =>
        obtain ⟨o₀, h₀, -⟩ := bind_eq_ok.1 (show checkExpr C sc g (.app h args) = .ok o from hc)
        simp only [Ctx.global] at hgl h₀
        simp [hgl, failAt_eq, bind, Except.bind] at h₀
      | some sig => exact call_sound ih ihs hh hI hg hgl hc
    | type => exact ctorApp_sound ih ihs hh hI hg (by simp [hgl]) hc
    | ctor => exact ctorApp_sound ih ihs hh hI hg (by simp [hgl]) hc

/-- A tuple (§8): its elements' results, in order. -/
theorem tuple_sound (p : Pos) {es : List Expr} (ih : ∀ e ∈ es, ExprSound e) (ihs : ∀ e ∈ es, ExprShape e) :
    ExprSound (.tuple p es) := by
  intro C sc g n0 W ρ act o hI hg h
  refine ⟨?_, fun _ ha => by simp [Expr.absurd] at ha⟩
  unfold checkExpr at h
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 h
  simp only at h₀
  split at h₀
  · rename_i g' hg'
    split at h₀
    · simp [miscount, failAt_eq, bind, Except.bind] at h₀
    · rename_i hne
      obtain ⟨oe, hoe, h₀⟩ := bind_eq_ok.1 h₀
      simp only [pure, Except.pure, Except.ok.injEq] at h₀
      subst h₀
      exact Simple.tuple_post ih ihs hI hg
        (fun g'' h'' => by simp only [Simple.given] at h''; rw [hg'] at h''; cases h''; simpa using hne) hoe hf
  · rename_i hg'
    obtain ⟨oe, hoe, h₀⟩ := bind_eq_ok.1 h₀
    simp only [pure, Except.pure, Except.ok.injEq] at h₀
    subst h₀
    exact Simple.tuple_post ih ihs hI hg (fun g'' h'' => (hg' g'' h'').elim) hoe hf

/-- A block (§8): its statements run in order, then its final expression, whose results are the block's; a block
whose statements taint the scope (§12) is removed; an absurd block's final expression is absurd. -/
theorem block_sound {ss : List Stmt} {f : Expr} (ihs : ∀ s ∈ ss, StmtSound s) (ihss : ∀ s ∈ ss, StmtShape s)
    (ihf : ExprSound f) (ihfs : ExprShape f) : ExprSound (.block ss f) := by
  intro C sc g n0 W ρ act o hI hg h
  unfold checkExpr at h
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 h
  obtain ⟨s, hs, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨of, hof, h₀⟩ := bind_eq_ok.1 h₀
  simp only [pure, Except.pure, Except.ok.injEq] at h₀
  subst h₀
  rw [keep_ok] at hof
  exact Simple.block_post ihs ihss ihf ihfs hI hg hs hof hf

/-- A `match` that is not erased (§10, §11): the untainted scrutinee's ideal value is headed by a value constructor
whose forcing survived, so the match has a branch for it, whose results are the match's; at run time the
scrutinee's tag picks that branch. With no branch, it is absurd: its results are tainted, or it is not reached. -/
theorem matchMany_sound {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch}
    (hm : m ≠ some .erased) (ihs : ExprSound s) (ihss : ExprShape s) (ihb : ∀ b ∈ bs, ExprSound b.body)
    (ihbs : ∀ b ∈ bs, ExprShape b.body) : ExprSound (.match p m s ann bs) :=
  MatchMany.sound hm ihs ihss ihb ihbs

/-- An erased `match` (§16): the scrutinee is not run; when a result is untainted and the match is not wholly
erased, an annotation entry is `many`, so at most one branch is not absurd, and the branch for the value
constructor heading the scrutinee's ideal value is not absurd (its results would be tainted, `ExprSound`'s second
part), so the evaluator's only branch is the right one, its fields bound to `removed`. -/
theorem matchErased_sound {p : Pos} {s : Expr} {ann : Tele} {bs : List Branch}
    (ihs : ExprSound s) (ihss : ExprShape s) (ihb : ∀ b ∈ bs, ExprSound b.body) (ihbs : ∀ b ∈ bs, ExprShape b.body) :
    ExprSound (.match p (some .erased) s ann bs) :=
  Erased.match ihs ihss ihb

theorem match_sound {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch}
    (ihs : ExprSound s) (ihss : ExprShape s) (ihb : ∀ b ∈ bs, ExprSound b.body) (ihbs : ∀ b ∈ bs, ExprShape b.body) :
    ExprSound (.match p m s ann bs) := by
  by_cases hm : m = some .erased
  · subst hm; exact matchErased_sound ihs ihss ihb ihbs
  · exact matchMany_sound hm ihs ihss ihb ihbs

/-- `sorry` (§12): every result is tainted, opened to `junk` or its `is` clause's value (`annotation_cons`), and the
tree is removed. -/
theorem sorry_sound (p : Pos) (t : Tele) : ExprSound (.sorry p t) := by
  intro C sc g n0 W ρ act o hI hg h
  refine ⟨?_, fun _ ha => by simp [Expr.absurd] at ha⟩
  unfold checkExpr at h
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 h
  obtain ⟨⟨tele, env⟩, ha, h₀⟩ := bind_eq_ok.1 h₀
  exact Simple.sorry_post hI hg ha h₀ hf

theorem removed_sound : ExprSound .removed := by
  intro C sc g n0 W ρ act o _ _ h
  simp [checkExpr, internal, failAt_eq, bind, Except.bind] at h

/-- A tuple `let` (§8): its binders name the right-hand side's results. -/
theorem let_sound {p : Pos} {bs : List LetBinder} {rhs : Expr} (ih : ExprSound rhs) (ihs : ExprShape rhs) :
    StmtSound (.let p bs rhs) := by
  intro C sc n0 W ρ act o hI h
  simp only [checkStmt] at h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨ws, hws, h⟩ := bind_eq_ok.1 h
  obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact Simple.let_post ih ihs hI hws ho'

/-- A pattern `let` that is not erased (§10): as a `match` with one branch, the rest of the body; a tainted
scrutinee taints the scope after it (§12). -/
theorem patletMany_sound {p : Pos} {ct : Bool} {m : Option Mult} {pat : Pattern} {rhs : Expr}
    (hm : m ≠ some .erased) (ih : ExprSound rhs) (ihs : ExprShape rhs) : StmtSound (.patlet p ct m pat rhs) :=
  MatchMany.patletSound hm ih ihs

/-- An erased pattern `let` (§16): the right-hand side is not run, and the fields are bound to `removed`. -/
theorem patletErased_sound {p : Pos} {ct : Bool} {pat : Pattern} {rhs : Expr} (ih : ExprSound rhs)
    (ihs : ExprShape rhs) : StmtSound (.patlet p ct (some .erased) pat rhs) :=
  Erased.patlet ih ihs

theorem patlet_sound {p : Pos} {ct : Bool} {m : Option Mult} {pat : Pattern} {rhs : Expr} (ih : ExprSound rhs)
    (ihs : ExprShape rhs) : StmtSound (.patlet p ct m pat rhs) := by
  by_cases hm : m = some .erased
  · subst hm; exact patletErased_sound ih ihs
  · exact patletMany_sound hm ih ihs

theorem inspect_sound (p : Pos) : StmtSound (.inspect p) := by
  intro C sc n0 W ρ act o hI h _
  simp only [checkStmt, pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨[], by simpa using hI, fun _ env hE => ⟨env, .inspect, by simpa using hE⟩⟩

mutual
/-- The main lemma for every expression without `_` (§16). -/
theorem Expr.sound : (e : Expr) → e.holeFree = true → ExprSound e
  | .var x, _ => var_sound x
  | .app h args, hp => by
    simp only [Expr.holeFree] at hp
    have hargs := Arg.holeFreeList_iff.1 hp
    have hh : ∀ a ∈ args, a.expr.holeFree = true := fun a ha => by rw [← Arg.holeFree_expr]; exact hargs a ha
    exact app_sound (fun a ha => Expr.sound a.expr (hh a ha)) (fun a ha => Expr.shape a.expr (hh a ha)) hh
  | .tuple p es, hp => by
    simp only [Expr.holeFree] at hp
    exact tuple_sound p (fun e he => Expr.sound e (Expr.holeFreeList_iff.1 hp e he))
      (fun e he => Expr.shape e (Expr.holeFreeList_iff.1 hp e he))
  | .block ss f, hp => by
    simp only [Expr.holeFree, Bool.and_eq_true] at hp
    exact block_sound (fun s hs => Stmt.sound s (Stmt.holeFreeList_iff.1 hp.1 s hs))
      (fun s hs => Stmt.shape s (Stmt.holeFreeList_iff.1 hp.1 s hs)) (Expr.sound f hp.2) (Expr.shape f hp.2)
  | .match p m s ann bs, hp => by
    simp only [Expr.holeFree, Bool.and_eq_true] at hp
    have hb : ∀ b ∈ bs, b.body.holeFree = true := fun b hb => by
      rw [← Branch.holeFree_body]; exact Branch.holeFreeList_iff.1 hp.2 b hb
    exact match_sound (Expr.sound s hp.1) (Expr.shape s hp.1) (fun b h' => Expr.sound b.body (hb b h'))
      (fun b h' => Expr.shape b.body (hb b h'))
  | .sorry p t, _ => sorry_sound p t
  | .removed, _ => removed_sound
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (have := Arg.sizeOf_expr_lt ‹_›; simp only [Expr.app.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem ‹_›; simp only [Expr.tuple.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem ‹_›; simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.match.sizeOf_spec]; omega)
    | (have := Branch.sizeOf_body_lt' ‹_›; simp only [Expr.match.sizeOf_spec]; omega)
theorem Stmt.sound : (s : Stmt) → s.holeFree = true → StmtSound s
  | .let p bs rhs, hp => let_sound (Expr.sound rhs hp) (Expr.shape rhs hp)
  | .patlet p ct m pat rhs, hp => patlet_sound (Expr.sound rhs hp) (Expr.shape rhs hp)
  | .inspect p, _ => inspect_sound p
termination_by s => sizeOf s
decreasing_by all_goals (simp only [Stmt.let.sizeOf_spec, Stmt.patlet.sizeOf_spec]; omega)
end

end Pledge
