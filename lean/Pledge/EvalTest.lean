import Pledge.Eval

namespace Pledge.EvalTest

def v (x : String) : Expr := .var ⟨some x, 0⟩
def ap (h : String) (args : List Expr) : Expr := .app ⟨h, 0⟩ (args.map (.mk none))
def br (c : String) (fields : List String) (body : Expr) : Branch :=
  .mk ⟨⟨c, 0⟩, fields.map (⟨some ·, 0⟩)⟩ body
def natAnn : Tele := .binders [{ name := ⟨some "r", 0⟩, ann := .type (.app ⟨"Nat", 0⟩ []) }]
def matchNat (s : Expr) (bs : List Branch) : Expr := .match 0 none s natAnn bs

def nat : Nat → Expr
  | 0 => ap "Zero" []
  | n + 1 => ap "Succ" [nat n]

def natV : Nat → Value
  | 0 => .app ⟨.ctor, "Zero"⟩ []
  | n + 1 => .app ⟨.ctor, "Succ"⟩ [natV n]

def fn (name : String) (params : List String) (subterm : List Bool) (body : Expr) (group : Nat) : FnDef :=
  { name, params := params.map (⟨some ·, 0⟩), subterm, returns := 1, body, globals := [], group,
    pad := subterm.count true }

def plus : FnDef := fn "plus" ["m", "n"] [true, false] (matchNat (v "m")
  [br "Zero" [] (v "n"), br "Succ" ["p"] (ap "Succ" [ap "plus" [v "p", v "n"]])]) 0

def loop : FnDef := fn "loop" ["m"] [true] (ap "loop" [v "m"]) 1

def ack : FnDef := fn "ack" ["m", "n"] [true, true] (matchNat (v "m")
  [br "Zero" [] (ap "Succ" [v "n"]),
   br "Succ" ["m1"] (matchNat (v "n")
     [br "Zero" [] (ap "ack" [v "m1", nat 1]),
      br "Succ" ["n1"] (ap "ack" [v "m1", ap "ack" [v "m", v "n1"]])])]) 2

def P : Prog := ⟨[plus, loop, ack], fun n => if n = "Nat" then some .type else if n = "Zero" ∨ n = "Succ" then
  some .ctor else none⟩

def run (e : Expr) : Except String (List Value) := evalExpr P (Act.top P.fns) [] e

def isOk (r : Except String (List Value)) (vs : List Value) : Bool := match r with
  | .ok ws => ws == vs
  | .error _ => false

#guard isOk (run (ap "plus" [nat 2, nat 3])) [natV 5]
#guard isOk (run (ap "plus" [nat 0, nat 0])) [natV 0]
#guard isOk (run (ap "ack" [nat 2, nat 2])) [natV 7]
#guard showValue (natV 2) = "Succ(Succ(Zero()))"
#guard match run (ap "loop" [nat 1]) with
  | .error e => e = "the call to loop does not decrease"
  | .ok _ => false
#guard isOk (run (matchNat (nat 1) [br "Zero" [] (nat 3), br "Succ" ["k"] (ap "Succ" [ap "Succ" [v "k"]])]))
  [natV 2]
#guard isOk (run (.tuple 0 [nat 1, .removed])) [natV 1, .removed]
#guard match run (ap "Foo" []) with
  | .error _ => true
  | .ok _ => false

end Pledge.EvalTest
