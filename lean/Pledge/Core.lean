import Pledge.Syntax

namespace Pledge

inductive HeadKind where
  | type | ctor
  deriving Repr, DecidableEq, Inhabited

/-- What an application applies: a type constructor or a value constructor. -/
structure Head where
  kind : HeadKind
  name : String
  deriving Repr, DecidableEq, Inhabited

/-- A skeleton term (§3): entries of the scope and bound variables of an unopened telescope
at the leaves, applications of type constructors and value constructors above them. -/
inductive Term where
  | entry (id : Nat)
  | bound (index : Nat)
  | app (head : Head) (args : List Term)
  deriving Repr, Inhabited

mutual
  def Term.decEq : (a b : Term) → Decidable (a = b)
    | .entry i, .entry j => if h : i = j then isTrue (h ▸ rfl) else isFalse (fun e => h (Term.entry.inj e))
    | .bound i, .bound j => if h : i = j then isTrue (h ▸ rfl) else isFalse (fun e => h (Term.bound.inj e))
    | .app h as, .app k bs =>
      if hk : h = k then
        match Term.decEqList as bs with
        | isTrue e => isTrue (hk ▸ e ▸ rfl)
        | isFalse ne => isFalse (fun e => ne (Term.app.inj e).2)
      else isFalse (fun e => hk (Term.app.inj e).1)
    | .entry _, .bound _ | .entry _, .app _ _ | .bound _, .entry _ | .bound _, .app _ _
    | .app _ _, .entry _ | .app _ _, .bound _ => isFalse (fun e => nomatch e)
  def Term.decEqList : (as bs : List Term) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
      match Term.decEq a b, Term.decEqList as bs with
      | isTrue e, isTrue es => isTrue (e ▸ es ▸ rfl)
      | isFalse ne, _ => isFalse (fun e => ne (List.cons.inj e).1)
      | _, isFalse ne => isFalse (fun e => ne (List.cons.inj e).2)
    | [], _ :: _ | _ :: _, [] => isFalse (fun e => nomatch e)
end

instance : DecidableEq Term := Term.decEq

/-- A value (§11): a tree of applications. `removed` stands for what taint or erasure
removed before evaluation (§12, §16); no typing rule gives it a type. -/
inductive Value where
  | app (head : Head) (args : List Value)
  | removed
  deriving Repr, Inhabited

mutual
  def Value.decEq : (a b : Value) → Decidable (a = b)
    | .removed, .removed => isTrue rfl
    | .app h as, .app k bs =>
      if hk : h = k then
        match Value.decEqList as bs with
        | isTrue e => isTrue (hk ▸ e ▸ rfl)
        | isFalse ne => isFalse (fun e => ne (Value.app.inj e).2)
      else isFalse (fun e => hk (Value.app.inj e).1)
    | .removed, .app _ _ | .app _ _, .removed => isFalse (fun e => nomatch e)
  def Value.decEqList : (as bs : List Value) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
      match Value.decEq a b, Value.decEqList as bs with
      | isTrue e, isTrue es => isTrue (e ▸ es ▸ rfl)
      | isFalse ne, _ => isFalse (fun e => ne (List.cons.inj e).1)
      | _, isFalse ne => isFalse (fun e => ne (List.cons.inj e).2)
    | [], _ :: _ | _ :: _, [] => isFalse (fun e => nomatch e)
end

instance : DecidableEq Value := Value.decEq

def Head.Type : Head := ⟨.type, "Type"⟩
def Term.TYPE : Term := .app .Type []
def Value.TYPE : Value := .app .Type []

/-- A checked binder. Bound variables in `type` and `is` are indexed by position in the
whole environment the telescope is opened or instantiated under: an outer prefix, such as
the parameters for a return telescope, then the telescope's own earlier binders. -/
structure TBinder where
  name : Option String
  type : Term
  is : Option Term
  mult : Mult := .many
  deriving Repr, DecidableEq, Inhabited

abbrev Telescope := List TBinder

/-- The signature of a type constructor or value constructor: its telescope and what an
application of it has as its type, over the telescope's bound variables. -/
structure Sig where
  head : Head
  params : Telescope
  ret : Term
  deriving Repr, Inhabited

abbrev Sigs := List Sig

def Sigs.find (S : Sigs) (h : Head) : Option Sig := List.find? (fun s => s.head == h) S

/-- An entry of the scope (§7): its type and, possibly, its `is` rule. An entry's id is
its index in the scope's list of entries. -/
structure Entry where
  type : Term
  rule : Option Term := none
  origin : String := ""
  erased : Bool := false
  tainted : Bool := false
  deriving Repr, Inhabited

abbrev Entries := List Entry

mutual
  /-- Instantiates bound variables by `env`. -/
  def Term.subst (env : List Term) : Term → Term
    | .entry i => .entry i
    | .bound i => (env[i]?).getD (.bound i)
    | .app h as => .app h (Term.substList env as)
  def Term.substList (env : List Term) : List Term → List Term
    | [] => []
    | a :: as => a.subst env :: Term.substList env as
end

mutual
  /-- Replaces the entry `x` by `e`. -/
  def Term.replace (x : Nat) (e : Term) : Term → Term
    | .entry i => if i = x then e else .entry i
    | .bound i => .bound i
    | .app h as => .app h (Term.replaceList x e as)
  def Term.replaceList (x : Nat) (e : Term) : List Term → List Term
    | [] => []
    | a :: as => Term.replace x e a :: Term.replaceList x e as
end

mutual
  /-- Canonicalization (§7) in one pass: each entry with a rule is replaced by its rule's
  term. `addRule` keeps the rules' terms free of entries that have rules, which is what is
  meant to make one pass reach the fixed point. -/
  def Term.canon (Γ : Entries) : Term → Term
    | .entry i => ((Γ[i]?).bind (·.rule)).getD (.entry i)
    | .bound i => .bound i
    | .app h as => .app h (Term.canonList Γ as)
  def Term.canonList (Γ : Entries) : List Term → List Term
    | [] => []
    | a :: as => a.canon Γ :: Term.canonList Γ as
end

mutual
  def Term.occurs (x : Nat) : Term → Bool
    | .entry i => i == x
    | .bound _ => false
    | .app _ as => Term.occursList x as
  def Term.occursList (x : Nat) : List Term → Bool
    | [] => false
    | a :: as => a.occurs x || Term.occursList x as
end

/-- Canonical identity, the comparison type checking makes (§3). -/
def identical (Γ : Entries) (a b : Term) : Bool := a.canon Γ == b.canon Γ

/-- The type of a closed term: an entry's recorded type, or an application's signature's
return instantiated by the arguments. -/
def typeOf (S : Sigs) (Γ : Entries) : Term → Option Term
  | .entry i => (Γ[i]?).map (·.type)
  | .bound _ => none
  | .app h as => (S.find h).map (·.ret.subst as)

/-- Gives the entry `x` the rule that it is `e`, and rewrites the other rules by it. It is
meant to be called with `e` canonical and not mentioning `x`. -/
def addRule (Γ : Entries) (x : Nat) (e : Term) : Entries :=
  Γ.mapIdx fun i en =>
    if i = x then { en with rule := some e } else { en with rule := en.rule.map (Term.replace x e) }

mutual
  /-- The value of a term under a valuation `ρ` of the entries and values `env` for the
  bound variables; `none` when a leaf has no value. -/
  def Term.eval (ρ env : List Value) : Term → Option Value
    | .entry i => ρ[i]?
    | .bound i => env[i]?
    | .app h as => (Term.evalList ρ env as).map (.app h)
  def Term.evalList (ρ env : List Value) : List Term → Option (List Value)
    | [] => some []
    | a :: as => do
      let v ← a.eval ρ env
      let vs ← Term.evalList ρ env as
      pure (v :: vs)
end

mutual
  /-- `HasType S v V`: the value `v` has the type `V`, itself a value (SOUNDNESS.md part 2).
  Every premise is about a strict subtree of `v`. `S` is meant to hold closed signatures:
  the program's signatures with the values of the top-level entries they mention substituted
  for those entries (`SigsClose`), so that typing a value depends on no valuation. -/
  inductive HasType (S : Sigs) : Value → Value → Prop where
    | app {h : Head} {sig : Sig} {vs : List Value} {V : Value} :
        S.find h = some sig → TeleSat S [] sig.params [] vs → sig.ret.eval [] vs = some V →
        HasType S (.app h vs) V
  /-- `TeleSat S ρ Δ env vs`: the values `vs` satisfy the telescope `Δ`, types and `is`
  clauses alike, when `ρ` gives values to the entries `Δ` mentions and `env` holds the values
  of the bound variables before `Δ`'s own. -/
  inductive TeleSat (S : Sigs) : List Value → Telescope → List Value → List Value → Prop where
    | nil {ρ env : List Value} : TeleSat S ρ [] env []
    | cons {ρ : List Value} {b : TBinder} {Δ : Telescope} {env : List Value} {v A : Value} {vs : List Value} :
        b.type.eval ρ env = some A → HasType S v A →
        (∀ e, b.is = some e → e.eval ρ env = some v) →
        TeleSat S ρ Δ (env ++ [v]) vs →
        TeleSat S ρ (b :: Δ) env (v :: vs)
end

mutual
  /-- Every entry's id is below `n`. -/
  def Term.entriesBelow (n : Nat) : Term → Bool
    | .entry i => decide (i < n)
    | .bound _ => true
    | .app _ as => Term.entriesBelowList n as
  def Term.entriesBelowList (n : Nat) : List Term → Bool
    | [] => true
    | a :: as => a.entriesBelow n && Term.entriesBelowList n as
end

def TBinder.entriesBelow (n : Nat) (b : TBinder) : Bool := b.type.entriesBelow n && b.is.all (·.entriesBelow n)

def Sig.entriesBelow (n : Nat) (sig : Sig) : Bool := sig.params.all (·.entriesBelow n) && sig.ret.entriesBelow n

mutual
  /-- A value as a term. `removed`, which no term evaluates to without entries or bound
  variables, becomes `.bound 0`, so `Term.close` is meant for valuations with no `removed`. -/
  def Value.toTerm : Value → Term
    | .app h vs => .app h (Value.toTermList vs)
    | .removed => .bound 0
  def Value.toTermList : List Value → List Term
    | [] => []
    | v :: vs => v.toTerm :: Value.toTermList vs
end

mutual
  /-- No subtree is `removed`. -/
  def Value.noRemoved : Value → Bool
    | .app _ vs => Value.noRemovedList vs
    | .removed => false
  def Value.noRemovedList : List Value → Bool
    | [] => true
    | v :: vs => v.noRemoved && Value.noRemovedList vs
end

/-- The head of `Value.junk`. No signature is meant to have it: `sorry` is a keyword, so no
declaration is named so. -/
def junkHead : Head := ⟨.ctor, "sorry"⟩

/-- The value a soundness proof may give a tainted result that need have none (§12), such as a result
of `sorry`: it carries the type `A` the result is meant to have, and no typing rule gives it a type. -/
def Value.junk (A : Value) : Value := .app junkHead [A]

/-- `WType S v A`: `v` has the type `A` by its head alone, without its arguments being typed: an
application's type is its signature's return, and `junk A`'s is `A`. -/
def WType (S : Sigs) : Value → Value → Prop
  | .app h vs, A => if h = junkHead then vs = [A] else ∃ sig, S.find h = some sig ∧ sig.ret.eval [] vs = some A
  | .removed, _ => False

/-- `WSat S Γ ρ`: the valuation `ρ` gives every entry of `Γ` a value without `removed` that has the
entry's type by its head (`WType`) and agrees with the entry's rule. -/
def WSat (S : Sigs) (Γ : Entries) (ρ : List Value) : Prop :=
  ρ.length = Γ.length ∧
  ∀ (i : Nat) (en : Entry), Γ[i]? = some en →
    ∃ v A, ρ[i]? = some v ∧ en.type.eval ρ [] = some A ∧ v.noRemoved = true ∧ WType S v A ∧
    ∀ r : Term, en.rule = some r → r.eval ρ [] = some v

/-- `Sat S Γ ρ` (SOUNDNESS.md part 3, with taint): `WSat`, and every entry not marked tainted has a
value of its type. A tainted entry's value may be `Value.junk`, so that what relies on `sorry` is
meant to need no value. `S` is meant to hold closed signatures, as for `HasType`. -/
def Sat (S : Sigs) (Γ : Entries) (ρ : List Value) : Prop :=
  WSat S Γ ρ ∧ ∀ (i : Nat) (en : Entry) (v A : Value), Γ[i]? = some en → ρ[i]? = some v →
    en.type.eval ρ [] = some A → en.tainted = false → HasType S v A

/-- The run-time value `a` approximates the ideal value `i`: `a` is `removed` where erasure or taint
removed it (§12, §16), and otherwise applies `i`'s head to arguments approximating `i`'s. -/
inductive Approx : Value → Value → Prop
  | removed {i : Value} : Approx .removed i
  | app {h : Head} {as is : List Value} : as.length = is.length →
      (∀ (k : Nat) (a i : Value), as[k]? = some a → is[k]? = some i → Approx a i) → Approx (.app h as) (.app h is)

/-- Whether argument `k` of an application of `h` is erased (§16): every argument of a type
constructor from phase 2 on, and a parameter or field declared `erased`. -/
def Sigs.erasedArg (S : Sigs) (phase : Nat) (h : Head) (k : Nat) : Bool :=
  (h.kind == .type && 2 ≤ phase) || ((S.find h).bind (·.params[k]?)).any (·.mult == .erased)

/-- `Rel S phase a i`: the run-time value `a` of a result in a position that is not erased has the
ideal value `i`'s head, and so on in every argument that is not erased; an erased argument only
approximates (`Approx`). -/
inductive Rel (S : Sigs) (phase : Nat) : Value → Value → Prop
  | app {h : Head} {as is : List Value} : as.length = is.length →
      (∀ (k : Nat) (a i : Value), as[k]? = some a → is[k]? = some i → S.erasedArg phase h k = true → Approx a i) →
      (∀ (k : Nat) (a i : Value), as[k]? = some a → is[k]? = some i → S.erasedArg phase h k = false →
        Rel S phase a i) →
      Rel S phase (.app h as) (.app h is)

/-- The relation between a run-time and an ideal value at a position of multiplicity `m`. -/
def MultRel (S : Sigs) (phase : Nat) : Mult → Value → Value → Prop
  | .erased, a, i => Approx a i
  | .many, a, i => Rel S phase a i

/-- `MultRel`, position by position, for the multiplicities `ms`. -/
def MultsRel (S : Sigs) (phase : Nat) (ms : List Mult) (as is : List Value) : Prop :=
  as.length = ms.length ∧ is.length = ms.length ∧
  ∀ (k : Nat) (m : Mult) (a i : Value), ms[k]? = some m → as[k]? = some a → is[k]? = some i → MultRel S phase m a i

mutual
  /-- Replaces each entry `i` that `ρ` gives a value by that value as a term. -/
  def Term.close (ρ : List Value) : Term → Term
    | .entry i => ((ρ[i]?).map Value.toTerm).getD (.entry i)
    | .bound i => .bound i
    | .app h as => .app h (Term.closeList ρ as)
  def Term.closeList (ρ : List Value) : List Term → List Term
    | [] => []
    | a :: as => a.close ρ :: Term.closeList ρ as
end

def TBinder.close (ρ : List Value) (b : TBinder) : TBinder :=
  { b with type := b.type.close ρ, is := b.is.map (Term.close ρ) }

def Sig.close (ρ : List Value) (sig : Sig) : Sig :=
  { sig with params := sig.params.map (TBinder.close ρ), ret := sig.ret.close ρ }

/-- The binders `b` under `ρ` and `b'` under `ρ'` have the same type and the same `is` clause,
by value, whatever the values of the bound variables, and the same multiplicity. -/
structure TBinder.Agree (ρ ρ' : List Value) (b b' : TBinder) : Prop where
  type : ∀ env, b.type.eval ρ env = b'.type.eval ρ' env
  is : ∀ env, b.is.map (Term.eval ρ env) = b'.is.map (Term.eval ρ' env)
  mult : b.mult = b'.mult

/-- `TBinder.Agree`, binder by binder. -/
def Telescope.Agree (ρ ρ' : List Value) : Telescope → Telescope → Prop
  | [], [] => True
  | b :: Δ, b' :: Δ' => TBinder.Agree ρ ρ' b b' ∧ Telescope.Agree ρ ρ' Δ Δ'
  | _, _ => False

structure Sig.Agree (ρ ρ' : List Value) (sig sig' : Sig) : Prop where
  params : Telescope.Agree ρ ρ' sig.params sig'.params
  ret : ∀ env, sig.ret.eval ρ env = sig'.ret.eval ρ' env

/-- `Sc` closes the signatures `S` under the valuation `ρ` of the entries they mention: every head
with a signature in `S` has one in `Sc`, which, evaluated with no entries, agrees with the original
evaluated under `ρ`. `Sc` may have more signatures, such as those declared later. -/
def SigsClose (S : Sigs) (ρ : List Value) (Sc : Sigs) : Prop :=
  ∀ h sig, S.find h = some sig → ∃ sig', Sc.find h = some sig' ∧ Sig.Agree ρ [] sig sig'

/-- The evaluator's environment: the values of the names in scope, newest first. -/
abbrev Env := List (String × Value)

/-- A function as the evaluator sees it: the body the checker left after removing what
taint and erasure remove (§14), and the top-level environment in force where the function
was declared. `subterm` says, per parameter, whether it is marked `subterm`; with `group`, the
function's group, and `pad`, the group's largest number of `subterm` parameters, it is read only by
the totality proof's measure (`calleeAct`), not by evaluation. -/
structure FnDef where
  name : String
  params : List Id
  subterm : List Bool
  returns : Nat
  body : Expr
  globals : Env
  group : Nat
  pad : Nat
  deriving Inhabited

abbrev Fns := List FnDef

def Fns.find (F : Fns) (name : String) : Option FnDef := List.find? (fun d => d.name == name) F

end Pledge
