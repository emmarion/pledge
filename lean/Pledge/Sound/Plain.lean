import Pledge.Check.Top

namespace Pledge

def Binder.plain (b : Binder) : Bool := b.mult.isNone

def Tele.plain : Tele → Bool
  | .binders bs => bs.all Binder.plain
  | .hole _ => true

mutual
  /-- No `sorry`, no `removed` and no written multiplicity: the syntax the stage 1 soundness theorems are
  meant to cover. -/
  def Expr.plain : Expr → Bool
    | .var _ => true
    | .app _ args => Arg.plainList args
    | .tuple _ es => Expr.plainList es
    | .block ss f => Stmt.plainList ss && f.plain
    | .match _ m s ann bs => m.isNone && s.plain && ann.plain && Branch.plainList bs
    | .sorry .. | .removed => false
  def Expr.plainList : List Expr → Bool
    | [] => true
    | e :: es => e.plain && Expr.plainList es
  def Arg.plain : Arg → Bool
    | .mk _ e => e.plain
  def Arg.plainList : List Arg → Bool
    | [] => true
    | a :: as => a.plain && Arg.plainList as
  def Stmt.plain : Stmt → Bool
    | .let _ bs rhs => bs.all (·.mult.isNone) && rhs.plain
    | .patlet _ _ m _ rhs => m.isNone && rhs.plain
    | .inspect _ => true
  def Stmt.plainList : List Stmt → Bool
    | [] => true
    | s :: ss => s.plain && Stmt.plainList ss
  def Branch.plain : Branch → Bool
    | .mk _ body => body.plain
  def Branch.plainList : List Branch → Bool
    | [] => true
    | b :: bs => b.plain && Branch.plainList bs
end

def Header.plain (h : Header) : Bool := h.params.all (·.binder.plain) && h.returns.all Binder.plain

def Ctor.plain (k : Ctor) : Bool := k.fields.all Binder.plain

def Data.plain (d : Data) : Bool := d.params.all Binder.plain && d.ctors.all Ctor.plain

def Fn.plain (f : Fn) : Bool := f.header.plain && f.body.plain

def Goal.plain : Goal → Bool
  | .type _ => true
  | .fn h => h.plain

def Top.plain : Top → Bool
  | .data d => d.plain
  | .fn f => f.plain
  | .mutualData _ ds => ds.all Data.plain
  | .mutualFn _ fs => fs.all Fn.plain
  | .stmt s => s.plain
  | .print _ e => e.plain
  | .goal _ g => g.plain
  | .qed _ e => e.plain

def Program.plain (prog : Program) : Bool := prog.all Top.plain

theorem Expr.plainList_iff : ∀ {es : List Expr}, Expr.plainList es = true ↔ ∀ e ∈ es, e.plain = true
  | [] => by simp [Expr.plainList]
  | e :: es => by simp [Expr.plainList, Expr.plainList_iff (es := es)]

theorem Arg.plainList_iff : ∀ {as : List Arg}, Arg.plainList as = true ↔ ∀ a ∈ as, a.plain = true
  | [] => by simp [Arg.plainList]
  | a :: as => by simp [Arg.plainList, Arg.plainList_iff (as := as)]

theorem Stmt.plainList_iff : ∀ {ss : List Stmt}, Stmt.plainList ss = true ↔ ∀ s ∈ ss, s.plain = true
  | [] => by simp [Stmt.plainList]
  | s :: ss => by simp [Stmt.plainList, Stmt.plainList_iff (ss := ss)]

theorem Branch.plainList_iff : ∀ {bs : List Branch}, Branch.plainList bs = true ↔ ∀ b ∈ bs, b.plain = true
  | [] => by simp [Branch.plainList]
  | b :: bs => by simp [Branch.plainList, Branch.plainList_iff (bs := bs)]

theorem Arg.plain_expr {a : Arg} : a.plain = a.expr.plain := by cases a; rfl

theorem Branch.plain_body {b : Branch} : b.plain = b.body.plain := by cases b; rfl

end Pledge
