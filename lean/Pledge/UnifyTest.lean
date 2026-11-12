import Pledge.Unify

namespace Pledge.UnifyTest

def T (n : String) (as : List Term := []) : Term := .app ⟨.type, n⟩ as
def C (n : String) (as : List Term := []) : Term := .app ⟨.ctor, n⟩ as
def b (type : Term) (is : Option Term := none) : TBinder := ⟨none, type, is, .many⟩
def x (i : Nat) : Term := .entry i
def v (i : Nat) : Term := .bound i
def sig (n : String) (params : Telescope) (ret : Term) : Sig := ⟨⟨.ctor, n⟩, params, ret⟩
def tsig (n : String) (params : Telescope) : Sig := ⟨⟨.type, n⟩, params, .TYPE⟩

def Nat' := T "Nat"
def Zero := C "Zero"
def Succ (t : Term) := C "Succ" [t]
def Vec (a n : Term) := T "Vec" [a, n]

def sZero := sig "Zero" [] Nat'
def sSucc := sig "Succ" [b Nat'] Nat'
def sVNil := sig "VNil" [b .TYPE] (Vec (v 0) Zero)
def sVCons := sig "VCons" [b .TYPE, b Nat', b (v 0), b (Vec (v 0) (v 1))] (Vec (v 0) (Succ (v 1)))
def sRefl := sig "Refl" [b .TYPE, b (v 0)] (T "Eq" [v 0, v 1, v 1])

def S : Sigs := [tsig "Type" [], tsig "Nat" [], tsig "Vec" [b .TYPE, b Nat'], tsig "Eq" [b .TYPE, b (v 0), b (v 0)],
  sZero, sSucc, sVNil, sVCons, sRefl]
def en (type : Term) (rule : Option Term := none) : Entry := { type, rule }
def mk : TBinder → Nat → Entry → Entry := fun _ _ e => e

def heads : Forced → Bool
  | .refuted ⟨_, _, .heads .., _⟩ => true
  | _ => false

def mSucc : Entries := [en Nat', en Nat' (Succ (x 0))]
#guard heads (force S mSucc (x 1) sZero mk)
#guard heads (force S mSucc (Succ (x 0)) sZero mk)
#guard match force S mSucc (x 1) sSucc mk with
  | .ok Γ [f] => identical Γ (x f) (x 0)
  | _ => false

def vec : Entries := [en .TYPE, en Nat', en (Vec (x 0) (Succ (x 1)))]
#guard match force S vec (x 2) sVCons mk with
  | .ok Γ [3, 4, 5, 6] => identical Γ (x 2) (C "VCons" [x 0, x 1, x 5, x 6])
      && identical Γ (Γ[6]?.map (·.type) |>.getD .TYPE) (Vec (x 0) (x 1))
  | _ => false
#guard heads (force S vec (x 2) sVNil mk)
#guard match force S vec (x 2) sVNil mk with
  | .refuted f => (f.render ⟨.ctor, "VNil"⟩).getLast? == some "refuted: Succ and Zero are different heads"
  | _ => false

def eqn : Entries := [en Nat', en (T "Eq" [Nat', x 0, Succ (x 0)])]
#guard match force S eqn (x 1) sRefl mk with
  | .refuted ⟨_, _, .occurs 0 e, _⟩ => e == Succ (x 0)
  | _ => false

#guard match force S [en Nat'] (x 0) sSucc mk with
  | .ok Γ [m1] => isStrictSubterm Γ (x m1) (x 0) && !isStrictSubterm Γ (x 0) (x m1)
      && !isStrictSubterm Γ (x m1) (x m1) && isStrictSubterm Γ (x m1) (Succ (Succ (x m1)))
  | _ => false

#guard match force S [en Nat', en Nat', en (T "Eq" [Nat', x 0, x 1])] (x 2) sRefl mk with
  | .ok Γ [_, a] => Γ[0]?.bind (·.rule) == none && Γ[a]?.bind (·.rule) == some (x 0)
      && Γ[1]?.bind (·.rule) == some (x 0)
  | _ => false

#guard match unify S [en Nat', en Nat'] (Succ (x 1)) (Succ Zero) (· == 1) with
  | .ok (Γ, none) => identical Γ (x 1) Zero
  | _ => false
#guard match unify S [en Nat', en Nat'] (Succ (x 0)) (x 1) (· == 0) with
  | .ok (_, some (a, b)) => a == Succ (x 0) && b == x 1
  | _ => false
#guard match unify S [en Nat', en Nat'] (Succ (x 0)) (x 0) (· == 0) with
  | .ok (_, some (a, b)) => a == x 0 && b == Succ (x 0)
  | _ => false

def opened := openTele [] [b Nat', b Nat' (Succ (v 0)), b (T "IsZero" [v 1])] [] mk
#guard opened.ids == [0, 1, 2] && opened.Γ[1]?.bind (·.rule) == some (Succ (x 0))
#guard abstract opened.Γ (opened.Γ[2]?.map (·.type) |>.getD .TYPE) opened.ids == T "IsZero" [v 1]
#guard abstract [en Nat', en Nat' (Succ (x 0))] (T "IsZero" [x 1]) [0] == T "IsZero" [Succ (v 0)]

#guard difference [] [b Nat', b (v 0)] [b Nat', b (v 0)] == none
#guard difference [] [b Nat', b (v 0)] [b Nat', b Nat'] == some 1
#guard difference [] [b Nat'] [b Nat', b Nat'] == some 1

end Pledge.UnifyTest
