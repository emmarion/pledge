import Pledge.Check.Top

namespace Pledge.SolveTest

def prelude : String :=
  "data Nat() : Type() { Zero() : Nat(); Succ(pred : Nat()) : Nat(); }
  data Eq(A : Type(), a : A, b : A) : Type() { Refl(A : Type(), a : A) : Eq(A, a, a); }
  data EqE(A : Type(), a : A, b : A) : Type() { ReflE(erased A : Type(), erased a : A) : EqE(A, a, a); }
  data Vec(A : Type(), n : Nat()) : Type() {
    VNil(A : Type()) : Vec(A, Zero());
    VCons(A : Type(), n : Nat(), head : A, rest : Vec(A, n)) : Vec(A, Succ(n));
  }
  data IsS(n : Nat()) : Type() { MkIsS(erased m : Nat()) : IsS(Succ(m)); }
  data Pt(A : Type(), a : A) : Type() { MkPt(A : Type(), a : A) : Pt(A, a); }
  data Box(A : Type()) : Type() { MkBox(A : Type(), x : A) : Box(A); }
  data Any() : Type() { MkAny(erased n : Nat()) : Any(); }
  fn mkn() -> (r : Nat()) { Zero() }
  "

def accepts (body : String) : Bool := (run (prelude ++ body) 2).error.isNone

def rejects (body : String) : Bool := (run (prelude ++ body) 2).error.any (!·.2.startsWith "internal")

def inspected (body : String) : String := " ".intercalate ((run (prelude ++ body) 2).inspects.map (·.2))

def has (s frag : String) : Bool := (s.splitOn frag).length > 1

#guard accepts "let (A : Type(), x : A, p : Eq(A, x, _)) = (Nat(), Zero(), Refl(Nat(), Zero()));"
#guard accepts "let (n : Nat(), v : Vec(Nat(), n), e : Eq(Vec(Nat(), n), v, _)) =
  (Zero(), VNil(Nat()), Refl(Vec(Nat(), Zero()), VNil(Nat())));"
#guard accepts "let (A : Type(), b : Pt(A, _)) = (Nat(), MkPt(Nat(), Zero()));"
#guard accepts "let (A : Type(), x : A, p : EqE(EqE(A, x, x), _, _)) = (Nat(), Zero(), ReflE(_, ReflE(_, _)));"
#guard accepts "let (n : Nat(), e is Refl(Nat(), _)) = (Zero(), Refl(Nat(), Zero()));"
#guard accepts "fn f(s : IsS(Succ(Zero()))) -> (r : Nat()) {
    let (v : Vec(Nat(), _), m : Nat()) = (VNil(Nat()), { let MkIsS(a) = s; Zero() });
    m
  }"

#guard accepts "fn f(erased n : Nat(), q : IsS(n), k : Nat()) -> (r : Nat()) { k }
  fn g(k : Nat(), z : IsS(k)) -> (r : Nat()) { f(_, z, { let MkIsS(a) = z; k }) }"
#guard accepts "fn f(erased n : Nat(), m : Nat(), e : EqE(Nat(), n, m)) -> (r : Nat()) { m }
  fn g(k : Nat(), z : IsS(k)) -> (r : Nat()) { f(_, { let MkIsS(a) = z; k }, ReflE(_, _)) }"
#guard accepts "fn g(k : Nat(), z : IsS(k)) -> (e : EqE(Nat(), k, k), r : Nat()) {
    (ReflE(_, _), { let MkIsS(a) = z; Zero() })
  }"
#guard accepts "fn h(k : Nat()) -> (r : Nat(), e : EqE(Nat(), r, k)) { (k, ReflE(Nat(), k)) }
  fn g(erased n : Nat(), m : Nat(), e : EqE(Nat(), n, m)) -> (r : Nat()) { m }
  fn t(k : Nat()) -> (r : Nat()) { g(_, { let (r, e) = h(k); let ReflE(_, _) = e; r }, ReflE(_, _)) }
  print t(Zero());"

#guard rejects "fn g(erased n : Nat(), m : Nat(), e : EqE(Nat(), n, m)) -> (r : Nat()) { m }
  print g(_, mkn(), ReflE(_, _));"
#guard rejects "fn g() -> (a : Any(), p : EqE(Any(), a, a), m : Nat()) {
    (MkAny(_), { let k = mkn(); ReflE(_, MkAny(k)) }, Zero())
  }"
#guard rejects "let (A : Type(), x : A, p : EqE(EqE(A, _, _), _, _)) = (Nat(), Zero(), ReflE(_, ReflE(_, _)));"
#guard rejects "fn f(erased n : Nat(), e : EqE(Nat(), Succ(n), n)) -> (r : Nat()) { Zero() }
  fn g(m : Nat(), e : EqE(Nat(), m, Succ(m))) -> (r : Nat()) { f(_, e) }"
#guard rejects "let p : Eq(Nat(), Zero(), Zero()) = Refl(_, _);"
#guard rejects "let (A : Type(), x : A, p : Eq(A, x, _)) = sorry(_);"

def taint : String :=
  "let s = sorry(p : Nat());
  fn use(erased n : Nat(), e : EqE(Nat(), n, Zero())) -> (r : Nat()) { Zero() }
  fn g(k : Nat(), e : EqE(Nat(), k, s), e2 : EqE(Nat(), k, Zero())) -> (r : Nat()) {
    let ReflE(_, _) = e;
    let r1 = use(_, e2);
    let r2 = use(k, e2);
    let r3 = use(s, e2);
    inspect;
    r1
  }"

#guard has (inspected taint) "r1 : Nat()" && has (inspected taint) "r2 : Nat()" &&
  has (inspected taint) "r3 (tainted) : Nat()"

#guard (run (prelude ++ "let s = sorry(p is Zero());
  fn use(erased n : Nat(), e : EqE(Nat(), n, Zero())) -> (r : Nat()) { Zero() }
  fn g(e : EqE(Nat(), s, Zero())) -> (r : Nat()) { use(_, e) }
  goal fn (e : EqE(Nat(), Zero(), Zero())) -> (r : Nat());
  qed g;") 2).goalProved == some true

#guard accepts "fn f(erased A : Type(), x : A) -> (b : Box(A)) { MkBox(_, x) }"

def boxSource : String := prelude ++ "let v : Vec(Nat(), _) = VNil(Nat());"
def boxProg : Program := (parse boxSource 2).1
def hole : Pos := ((boxProg.flatMap Top.holes).head?).getD 0
def zero : Term := .app ⟨.ctor, "Zero"⟩ []
def one : Term := .app ⟨.ctor, "Succ"⟩ [zero]

#guard solution 2 boxProg == [(hole, [zero])]
#guard (runProgramWith 2 [(hole, [zero])] boxProg (fun _ => false)).error.isNone
#guard (runProgramWith 2 [(hole, [.app ⟨.ctor, "Succ"⟩ [.TYPE], zero])] boxProg (fun _ => false)).error.isNone
#guard (runProgramWith 2 [(hole, [one])] boxProg (fun _ => false)).error.isSome
#guard (runProgramWith 2 [(hole, [.app ⟨.ctor, "Succ"⟩ [.TYPE]])] boxProg (fun _ => false)).error.isSome
#guard (runProgramWith 2 [(hole, [.entry 0])] boxProg (fun _ => false)).error.isSome
#guard (runProgramWith 2 [] boxProg (fun _ => false)).error.isSome

def erasedΓ : Entries := [{ type := .TYPE, erased := true }, { type := .app ⟨.type, "Nat"⟩ [], erased := true }]
#guard !(Term.entry 0).erasedUse [] erasedΓ 2 && (Term.entry 1).erasedUse [] erasedΓ 2
#guard !(Term.app ⟨.type, "Vec"⟩ [.entry 0, .entry 1]).erasedUse [] erasedΓ 2

end Pledge.SolveTest
