import Pledge.Check.Top

namespace Pledge

mutual
  /-- No `_` in place of an expression (§16): the syntax the soundness theorems are meant to cover, `sorry` and
  multiplicities included. -/
  def Expr.holeFree : Expr → Bool
    | .var x => x.name.isSome
    | .app _ args => Arg.holeFreeList args
    | .tuple _ es => Expr.holeFreeList es
    | .block ss f => Stmt.holeFreeList ss && f.holeFree
    | .match _ _ s _ bs => s.holeFree && Branch.holeFreeList bs
    | .sorry .. | .removed => true
  def Expr.holeFreeList : List Expr → Bool
    | [] => true
    | e :: es => e.holeFree && Expr.holeFreeList es
  def Arg.holeFree : Arg → Bool
    | .mk _ e => e.holeFree
  def Arg.holeFreeList : List Arg → Bool
    | [] => true
    | a :: as => a.holeFree && Arg.holeFreeList as
  def Stmt.holeFree : Stmt → Bool
    | .let _ _ rhs | .patlet _ _ _ _ rhs => rhs.holeFree
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

/-- No type constructor or value constructor is named as `junkHead` is, which a parsed program meets since
`sorry` is a keyword. -/
def Data.holeFree (d : Data) : Bool := d.name.name != junkHead.name && d.ctors.all (·.name.name != junkHead.name)

def Top.holeFree : Top → Bool
  | .data d => d.holeFree
  | .fn f => f.body.holeFree
  | .mutualData _ ds => ds.all Data.holeFree
  | .mutualFn _ fs => fs.all (·.body.holeFree)
  | .stmt s => s.holeFree
  | .print _ e | .qed _ e => e.holeFree
  | .goal .. => true

/-- The programs the soundness theorems cover: no `_` argument (§16) anywhere, `sorry` and multiplicities
allowed, and no declaration named `sorry`. -/
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

theorem Arg.holeFree_expr {a : Arg} : a.holeFree = a.expr.holeFree := by cases a; rfl

theorem Branch.holeFree_body {b : Branch} : b.holeFree = b.body.holeFree := by cases b; rfl

end Pledge
