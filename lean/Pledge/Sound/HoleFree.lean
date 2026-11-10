import Pledge.Check.Top

namespace Pledge

/-- No `_` (§16) in a written binder's annotation. -/
def Binder.holeFree (b : Binder) : Bool := !b.ann.term.holed

def Tele.holeFree : Tele → Bool
  | .binders bs => bs.all Binder.holeFree
  | .hole _ => true

def Header.holeFree (h : Header) : Bool := h.params.all (·.binder.holeFree) && h.returns.all Binder.holeFree

def Data.holeFree (d : Data) : Bool :=
  d.params.all Binder.holeFree && d.ctors.all fun k => k.fields.all Binder.holeFree && !k.ret.holed

def LetBinder.holeFree (b : LetBinder) : Bool := !b.ann.any (·.term.holed)

mutual
  /-- No `_` in place of an expression or in a written term (§16): the syntax the soundness theorems are meant to
  cover, `sorry`, `_` in place of a telescope, and multiplicities included. -/
  def Expr.holeFree : Expr → Bool
    | .var x => x.name.isSome
    | .app _ args => Arg.holeFreeList args
    | .tuple _ es => Expr.holeFreeList es
    | .block ss f => Stmt.holeFreeList ss && f.holeFree
    | .match _ _ s ann bs => s.holeFree && ann.holeFree && Branch.holeFreeList bs
    | .sorry _ t => t.holeFree
    | .removed => true
  def Expr.holeFreeList : List Expr → Bool
    | [] => true
    | e :: es => e.holeFree && Expr.holeFreeList es
  def Arg.holeFree : Arg → Bool
    | .mk _ e => e.holeFree
  def Arg.holeFreeList : List Arg → Bool
    | [] => true
    | a :: as => a.holeFree && Arg.holeFreeList as
  def Stmt.holeFree : Stmt → Bool
    | .let _ bs rhs => bs.all LetBinder.holeFree && rhs.holeFree
    | .patlet _ _ _ _ rhs => rhs.holeFree
    | .inspect _ => true
  def Stmt.holeFreeList : List Stmt → Bool
    | [] => true
    | s :: ss => s.holeFree && Stmt.holeFreeList ss
  def Branch.holeFree : Branch → Bool
    | .mk _ body => body.holeFree
  def Branch.holeFreeList : List Branch → Bool
    | [] => true
    | b :: bs => b.holeFree && Branch.holeFreeList bs
end

def Fn.holeFree (f : Fn) : Bool := f.header.holeFree && f.body.holeFree

def Top.holeFree : Top → Bool
  | .data d => d.holeFree
  | .mutualData _ ds => ds.all Data.holeFree
  | .goal _ (.type t) => !t.holed
  | .goal _ (.fn h) => h.holeFree
  | .fn f => f.holeFree
  | .mutualFn _ fs => fs.all Fn.holeFree
  | .stmt s => s.holeFree
  | .print _ e | .qed _ e => e.holeFree

/-- The programs the soundness theorems cover: no `_` (§16) in place of an expression or in a written term,
`sorry`, `_` in place of a telescope, and multiplicities allowed. -/
def Program.holeFree (prog : Program) : Bool := prog.all Top.holeFree

theorem Expr.holeFreeList_iff : ∀ {es : List Expr}, Expr.holeFreeList es = true ↔ ∀ e ∈ es, e.holeFree = true
  | [] => by simp [Expr.holeFreeList]
  | e :: es => by simp [Expr.holeFreeList, Expr.holeFreeList_iff (es := es)]

theorem Arg.holeFreeList_iff : ∀ {as : List Arg}, Arg.holeFreeList as = true ↔ ∀ a ∈ as, a.holeFree = true
  | [] => by simp [Arg.holeFreeList]
  | a :: as => by simp [Arg.holeFreeList, Arg.holeFreeList_iff (as := as)]

theorem Stmt.holeFreeList_iff : ∀ {ss : List Stmt}, Stmt.holeFreeList ss = true ↔ ∀ s ∈ ss, s.holeFree = true
  | [] => by simp [Stmt.holeFreeList]
  | s :: ss => by simp [Stmt.holeFreeList, Stmt.holeFreeList_iff (ss := ss)]

theorem Branch.holeFreeList_iff : ∀ {bs : List Branch}, Branch.holeFreeList bs = true ↔ ∀ b ∈ bs, b.holeFree = true
  | [] => by simp [Branch.holeFreeList]
  | b :: bs => by simp [Branch.holeFreeList, Branch.holeFreeList_iff (bs := bs)]

theorem LetBinder.holeFree_any {bs : List LetBinder} (h : bs.all LetBinder.holeFree = true) :
    bs.any (·.ann.any (·.term.holed)) = false := by
  simpa [LetBinder.holeFree, List.all_eq_true, List.any_eq_false] using h

theorem Binder.holeFree_all {bs : List Binder} (h : bs.all Binder.holeFree = true) :
    ∀ b ∈ bs, b.ann.term.holed = false := by
  simpa [Binder.holeFree, List.all_eq_true] using h

theorem Fn.holeFree_header {f : Fn} (h : f.holeFree = true) : f.header.holeFree = true := by
  simp only [Fn.holeFree, Bool.and_eq_true] at h; exact h.1

theorem Fn.holeFree_body {f : Fn} (h : f.holeFree = true) : f.body.holeFree = true := by
  simp only [Fn.holeFree, Bool.and_eq_true] at h; exact h.2

theorem Header.holeFree_params {hd : Header} (h : hd.holeFree = true) :
    ∀ b ∈ hd.params.map (·.binder), b.ann.term.holed = false := by
  simp only [Header.holeFree, Bool.and_eq_true] at h
  simpa [Binder.holeFree, List.all_eq_true] using h.1

theorem Header.holeFree_returns {hd : Header} (h : hd.holeFree = true) :
    ∀ b ∈ hd.returns, b.ann.term.holed = false := by
  simp only [Header.holeFree, Bool.and_eq_true] at h
  exact Binder.holeFree_all h.2

theorem Tele.holeFree_binders {t : Tele} (h : t.holeFree = true) :
    ∀ bs, t = .binders bs → ∀ b ∈ bs, b.ann.term.holed = false := by
  rintro bs rfl
  exact Binder.holeFree_all h

theorem Arg.holeFree_expr {a : Arg} : a.holeFree = a.expr.holeFree := by cases a; rfl

theorem Branch.holeFree_body {b : Branch} : b.holeFree = b.body.holeFree := by cases b; rfl

end Pledge
