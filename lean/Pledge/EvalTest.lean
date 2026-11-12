import Pledge.Run

namespace Pledge.EvalTest

def natSource : String :=
  "data Nat() : Type() { Zero() : Nat(); Succ(pred : Nat()) : Nat(); }
  data Option(A : Type()) : Type() { None(A : Type()) : Option(A); Some(A : Type(), x : A) : Option(A); }
  fn plus(subterm m : Nat(), n : Nat()) -> (r : Nat()) {
    match m : (r : Nat()) { Zero() => n; Succ(p) => Succ(plus(subterm p, n)); }
  }
  fn ack(subterm m : Nat(), subterm n : Nat()) -> (r : Nat()) {
    match m : (r : Nat()) {
      Zero() => Succ(n);
      Succ(m1) => match n : (r : Nat()) {
        Zero() => ack(subterm m1, Succ(Zero()));
        Succ(n1) => ack(subterm m1, ack(same m, subterm n1));
      };
    }
  }
  fn pred(n : Nat()) -> (r : Option(Nat())) { match n : (r : Option(Nat())) { Zero() => None(Nat()); Succ(p) =>
    Some(Nat(), p); } }
  "

def nat : Nat → String
  | 0 => "Zero()"
  | n + 1 => s!"Succ({nat n})"

def prints (body : String) : List String := (run (natSource ++ body) 1).prints.map (·.2)

#guard prints s!"print plus({nat 2}, {nat 3});" == [nat 5]
#guard prints s!"print plus({nat 0}, {nat 0});" == [nat 0]
#guard prints s!"print ack({nat 2}, {nat 2});" == [nat 7]
#guard prints s!"let k = plus({nat 1}, {nat 1}); print Succ(k); print pred(k);" == [nat 3, s!"Some(_, {nat 1})"]
#guard prints s!"comptime let Some(_, p) = pred({nat 2}); print p;" == [nat 1]
#guard (run (natSource ++ s!"comptime let Some(_, p) = pred({nat 0});") 1).error.map (·.2) ==
  some "this evaluates to `None(_)`, which is not headed by `Some` (§11)"
#guard prints "print sorry(n : Nat());" == ["sorry"]

end Pledge.EvalTest
