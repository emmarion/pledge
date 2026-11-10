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
  /-- `HasType S ρ v V`: the value `v` has the type `V`, itself a value (SOUNDNESS.md
  part 2). Every premise is about a strict subtree of `v`. The valuation `ρ` gives values
  to the top-level entries the signatures mention. -/
  inductive HasType (S : Sigs) (ρ : List Value) : Value → Value → Prop where
    | app {h : Head} {sig : Sig} {vs : List Value} {V : Value} :
        S.find h = some sig → TeleSat S ρ sig.params [] vs → sig.ret.eval ρ vs = some V →
        HasType S ρ (.app h vs) V
  /-- `TeleSat S ρ Δ env vs`: the values `vs` satisfy the telescope `Δ`, types and `is`
  clauses alike, when `env` holds the values of the bound variables before `Δ`'s own. -/
  inductive TeleSat (S : Sigs) (ρ : List Value) : Telescope → List Value → List Value → Prop where
    | nil {env : List Value} : TeleSat S ρ [] env []
    | cons {b : TBinder} {Δ : Telescope} {env : List Value} {v A : Value} {vs : List Value} :
        b.type.eval ρ env = some A → HasType S ρ v A →
        (∀ e, b.is = some e → e.eval ρ env = some v) →
        TeleSat S ρ Δ (env ++ [v]) vs →
        TeleSat S ρ (b :: Δ) env (v :: vs)
end

/-- `Sat S Γ ρ`: the valuation `ρ` gives every entry of `Γ` a value of the entry's type
that agrees with the entry's rule (SOUNDNESS.md part 3). -/
def Sat (S : Sigs) (Γ : Entries) (ρ : List Value) : Prop :=
  ρ.length = Γ.length ∧
  ∀ (i : Nat) (en : Entry), Γ[i]? = some en →
    ∃ v A, ρ[i]? = some v ∧ en.type.eval ρ [] = some A ∧ HasType S ρ v A ∧
    ∀ r : Term, en.rule = some r → r.eval ρ [] = some v

/-- The evaluator's environment: the values of the names in scope, newest first. -/
abbrev Env := List (String × Value)

/-- An activation's measure (SOUNDNESS.md part 6): the group of the running function and
the values of its `subterm` parameters, padded with `none` to the group's largest number of
`subterm` parameters. Top-level code runs with a group above every function's. -/
structure Act where
  group : Nat
  subs : List (Option Value)
  deriving Repr, DecidableEq, Inhabited

/-- A function as the evaluator sees it: the body the checker left after removing what
taint and erasure remove (§14), and the top-level environment in force where the function
was declared. `subterm` says, per parameter, whether it is marked `subterm`. -/
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
