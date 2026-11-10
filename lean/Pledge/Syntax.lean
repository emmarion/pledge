namespace Pledge

/-- An offset into the source text. -/
abbrev Pos := Nat

structure Name where
  name : String
  pos : Pos := 0
  deriving Repr, Inhabited

/-- A binder's name; `none` is `_`. -/
structure Id where
  name : Option String
  pos : Pos := 0
  deriving Repr, Inhabited

/-- A skeleton term as written (DESIGN.md §3, §19 `term`); `hole` is `_` (§16). -/
inductive WTerm where
  | var (name : Name)
  | app (head : Name) (args : List WTerm)
  | hole (pos : Pos)
  deriving Repr, Inhabited

inductive Mult where
  | many | erased
  deriving Repr, DecidableEq, Inhabited

inductive Ann where
  | type (term : WTerm)
  | is (term : WTerm)
  deriving Repr, Inhabited

structure Binder where
  name : Id
  ann : Ann
  mult : Option Mult := none
  deriving Repr, Inhabited

structure Param where
  subterm : Bool
  binder : Binder
  deriving Repr, Inhabited

structure LetBinder where
  name : Id
  ann : Option Ann
  mult : Option Mult := none
  deriving Repr, Inhabited

structure Pattern where
  ctor : Name
  fields : List Id
  deriving Repr, Inhabited

inductive Mark where
  | subterm | same
  deriving Repr, DecidableEq, Inhabited

/-- A written telescope, or `_` standing for the telescope given at its position (§10). -/
inductive Tele where
  | binders (bs : List Binder)
  | hole (pos : Pos)
  deriving Repr, Inhabited

mutual
  /-- Expressions (§19 `expr`). `removed` is what taint and erasure leave behind (§12, §14);
  the parser never produces it. -/
  inductive Expr where
    | var (name : Id)
    | app (head : Name) (args : List Arg)
    | tuple (pos : Pos) (elems : List Expr)
    | block (stmts : List Stmt) (final : Expr)
    | «match» (pos : Pos) (mult : Option Mult) (scrut : Expr) (ann : Tele) (branches : List Branch)
    | «sorry» (pos : Pos) (tele : Tele)
    | removed
  inductive Arg where
    | mk (mark : Option Mark) (expr : Expr)
  inductive Stmt where
    | «let» (pos : Pos) (binders : List LetBinder) (rhs : Expr)
    | patlet (pos : Pos) (comptime : Bool) (mult : Option Mult) (pat : Pattern) (rhs : Expr)
    | inspect (pos : Pos)
  inductive Branch where
    | mk (pat : Pattern) (body : Expr)
end

instance : Inhabited Expr := ⟨.removed⟩

structure Ctor where
  name : Name
  fields : List Binder
  ret : WTerm
  deriving Inhabited

structure Data where
  name : Name
  params : List Binder
  ctors : List Ctor
  deriving Inhabited

structure Header where
  params : List Param
  returns : List Binder
  deriving Inhabited

structure Fn where
  name : Name
  header : Header
  body : Expr
  deriving Inhabited

inductive Goal where
  | type (term : WTerm)
  | fn (header : Header)

inductive Top where
  | data (d : Data)
  | fn (f : Fn)
  | mutualData (pos : Pos) (ds : List Data)
  | mutualFn (pos : Pos) (fs : List Fn)
  | stmt (s : Stmt)
  | print (pos : Pos) (e : Expr)
  | goal (pos : Pos) (g : Goal)
  | qed (pos : Pos) (e : Expr)

abbrev Program := List Top

end Pledge
