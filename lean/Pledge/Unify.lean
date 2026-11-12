import Pledge.Core

namespace Pledge

mutual
  /-- Replaces each entry `i` by `f i`. -/
  def Term.mapEntries (f : Nat → Term) : Term → Term
    | .entry i => f i
    | .bound i => .bound i
    | .app h as => .app h (Term.mapEntriesList f as)
  def Term.mapEntriesList (f : Nat → Term) : List Term → List Term
    | [] => []
    | a :: as => a.mapEntries f :: Term.mapEntriesList f as
end

mutual
  def Term.size : Term → Nat
    | .app _ as => Term.sizeList as + 1
    | _ => 1
  def Term.sizeList : List Term → Nat
    | [] => 0
    | a :: as => a.size + Term.sizeList as
end

theorem Term.size_pos (t : Term) : 0 < t.size := by
  cases t <;> simp [Term.size]

/-- Replaces the entry `ids[k]` by `.bound k`, and an entry with a rule that is not among `ids` by its rule's term,
abstracted the same way; it is meant to agree with `abstract` in terms.ts while rules' terms mention no entry
with a rule. -/
def abstract (Γ : Entries) (t : Term) (ids : List Nat) : Term :=
  let leaf (i : Nat) (other : Term) : Term := ((ids.idxOf? i).map .bound).getD other
  t.mapEntries fun i => leaf i (((Γ[i]?).bind (·.rule)).elim (.entry i) (·.mapEntries fun j => leaf j (.entry j)))

mutual
  /-- Every bound variable's index is below `n`. -/
  def Term.boundsBelow (n : Nat) : Term → Bool
    | .entry _ => true
    | .bound i => decide (i < n)
    | .app _ as => Term.boundsBelowList n as
  def Term.boundsBelowList (n : Nat) : List Term → Bool
    | [] => true
    | a :: as => a.boundsBelow n && Term.boundsBelowList n as
end

/-- No bound variable occurs. -/
def Term.closed (t : Term) : Bool := t.boundsBelow 0

/-- `abstract`, when the term and the rules it expands are closed. -/
def abstract? (Γ : Entries) (t : Term) (ids : List Nat) : Option Term :=
  if (t.canon Γ).closed then some (abstract Γ t ids) else none

structure Opened where
  Γ : Entries
  ids : List Nat
  env : List Term

/-- Opens a telescope to fresh entries appended to `Γ` (§3), its bound variables standing for `env` and then for the
earlier fresh entries. A fresh entry's `is` rule is stored canonical; `mk` sets everything but the type and rule. -/
def openTele (Γ : Entries) (tele : Telescope) (env : List Term) (mk : TBinder → Nat → Entry → Entry) : Opened :=
  go 0 tele ⟨Γ, [], env⟩
where
  go (i : Nat) : Telescope → Opened → Opened
    | [], o => o
    | b :: bs, ⟨Γ, ids, env⟩ =>
      let type := b.type.subst env
      let rule := b.is.map fun e => (e.subst env).canon Γ
      let en := { mk b i { type, rule, erased := b.mult == .erased } with type, rule }
      go (i + 1) bs ⟨Γ ++ [en], ids ++ [Γ.length], env ++ [.entry Γ.length]⟩

mutual
  def Term.strictSub (s : Term) : Term → Bool
    | .app _ as => Term.strictSubList s as
    | _ => false
  def Term.strictSubList (s : Term) : List Term → Bool
    | [] => false
    | a :: as => a == s || Term.strictSub s a || Term.strictSubList s as
end

/-- `s` is a strict subterm of `t` (§9): canonicalized, `s` is identical to an argument of `t` or strictly below
one. -/
def isStrictSubterm (Γ : Entries) (s t : Term) : Bool := Term.strictSub (s.canon Γ) (t.canon Γ)

/-- The first position at which two telescopes differ (§12), compared as open terms: multiplicity, type and `is`
clause; `none` when they agree. -/
def difference (Γ : Entries) : Telescope → Telescope → Option Nat
  | [], [] => none
  | x :: xs, y :: ys =>
    let agree : Option Term → Option Term → Bool
      | some a, some b => identical Γ a b
      | none, none => true
      | _, _ => false
    if x.mult = y.mult ∧ identical Γ x.type y.type ∧ agree x.is y.is then (difference Γ xs ys).map (· + 1)
    else some 0
  | _, _ => some 0

/-- Why an equation was posed; `parent` is the position in the log of the equation it came from. -/
inductive Why where
  | scrutinee
  | scrutineeType
  | given
  | types (parent : Nat)
  | arg (head : Head) (index : Nat) (parent : Nat)
  deriving Repr, Inhabited

structure Eqn where
  lhs : Term
  rhs : Term
  why : Why
  deriving Repr, Inhabited

/-- An equation as processed, and the rule it gave, if any. -/
structure Step where
  eqn : Eqn
  gave : Option (Nat × Term)
  deriving Repr, Inhabited

inductive Clash where
  | heads (a b : Head)
  | occurs (x : Nat) (e : Term)
  | rigid (a b : Term)
  deriving Repr, Inhabited

/-- A failed equation, with the scope at the failure and the log of the equations processed, the failing one
last. -/
structure Failure where
  Γ : Entries
  eqn : Eqn
  clash : Clash
  log : List Step
  deriving Repr, Inhabited

/-- `stuck` is meant to be unreachable: it reports an internal error, never a refutation. -/
inductive Solved where
  | ok (Γ : Entries) (log : List Step)
  | failed (f : Failure)
  | stuck (msg : String)
  deriving Repr, Inhabited

def free (Γ : Entries) : Nat := Γ.countP (·.rule.isNone)

def eqsSize : List Eqn → Nat
  | [] => 0
  | q :: qs => q.lhs.size + q.rhs.size + eqsSize qs

theorem eqsSize_append (as bs : List Eqn) : eqsSize (as ++ bs) = eqsSize as + eqsSize bs := by
  induction as with
  | nil => simp [eqsSize]
  | cons q qs ih => simp [eqsSize, ih]; omega

def argEqns (h : Head) (parent : Nat) (i : Nat) : List Term → List Term → List Eqn
  | a :: as, b :: bs => ⟨a, b, .arg h i parent⟩ :: argEqns h parent (i + 1) as bs
  | _, _ => []

theorem eqsSize_argEqns (h : Head) (p : Nat) :
    ∀ i as bs, eqsSize (argEqns h p i as bs) ≤ Term.sizeList as + Term.sizeList bs
  | i, a :: as, b :: bs => by
    have := eqsSize_argEqns h p (i + 1) as bs; simp only [argEqns, eqsSize, Term.sizeList]; omega
  | _, [], _ | _, _ :: _, [] => by simp [argEqns, eqsSize]

theorem free_mapIdx_le : ∀ (Γ : Entries) (f : Nat → Entry → Entry),
    (∀ i en, (f i en).rule.isNone → en.rule.isNone) → free (Γ.mapIdx f) ≤ free Γ
  | [], _, _ => by simp [free]
  | a :: Γ, f, hf => by
    have := free_mapIdx_le Γ (fun i => f (i + 1)) (fun i => hf (i + 1))
    have := hf 0 a
    simp only [free, List.mapIdx_cons, List.countP_cons] at *
    split <;> split <;> simp_all <;> omega

theorem free_mapIdx_lt : ∀ (Γ : Entries) (f : Nat → Entry → Entry) (x : Nat) (en : Entry),
    (∀ i en, (f i en).rule.isNone → en.rule.isNone) → Γ[x]? = some en → en.rule = none →
    (f x en).rule.isSome → free (Γ.mapIdx f) < free Γ
  | [], _, _, _, _, hx, _, _ => by simp at hx
  | a :: Γ, f, 0, en, hf, hx, hn, hs => by
    have := free_mapIdx_le Γ (fun i => f (i + 1)) (fun i => hf (i + 1))
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx
    simp only [free, List.mapIdx_cons, List.countP_cons] at *
    cases h : (f 0 a).rule <;> simp_all <;> omega
  | a :: Γ, f, x + 1, en, hf, hx, hn, hs => by
    have := free_mapIdx_lt Γ (fun i => f (i + 1)) x en (fun i => hf (i + 1)) (by simpa using hx) hn hs
    have := hf 0 a
    simp only [free, List.mapIdx_cons, List.countP_cons] at *
    split <;> split <;> simp_all <;> omega

/-- Which side of an equation takes a rule: an entry that `may` take one, the newer of two. -/
def pick (may : Nat → Bool) (l r : Term) : Option (Nat × Term) :=
  let cand : Term → Option Nat
    | .entry i => if may i then some i else none
    | _ => none
  match cand l, cand r with
  | some i, some j => if j < i then some (i, r) else some (j, l)
  | some i, none => some (i, r)
  | none, some j => some (j, l)
  | none, none => none

/-- Solves pending equations, first in first out (§7), every pending equation being kept canonical: the initial
ones are given canonical, and adding a rule `x is e` replaces `x` by `e` in them. Only entries that `may` take a
rule take one. -/
def solve (S : Sigs) (may : Nat → Bool) (Γ : Entries) (log : List Step) (eqs : List Eqn) : Solved :=
  match eqs with
  | [] => .ok Γ log
  | q :: rest =>
    let done (gave : Option (Nat × Term)) := log ++ [⟨q, gave⟩]
    let fail (c : Clash) : Solved := .failed ⟨Γ, q, c, done none⟩
    if q.lhs = q.rhs then
      have : eqsSize rest < eqsSize (q :: rest) := by have := q.lhs.size_pos; simp only [eqsSize]; omega
      solve S may Γ (done none) rest
    else match hl : q.lhs, hr : q.rhs with
    | .app h as, .app k bs =>
      if h = k ∧ as.length = bs.length then
        have : eqsSize (rest ++ argEqns h log.length 0 as bs) < eqsSize (q :: rest) := by
          have := eqsSize_argEqns h log.length 0 as bs
          simp only [eqsSize_append, eqsSize, hl, hr, Term.size]; omega
        solve S may Γ (done none) (rest ++ argEqns h log.length 0 as bs)
      else fail (.heads h k)
    | l, r =>
      match pick may l r with
      | none => fail (.rigid l r)
      | some (x, e) =>
        if e.occurs x then fail (.occurs x e)
        else match hx : Γ[x]? with
        | some en =>
          if hn : en.rule = none then
            match typeOf S Γ e with
            | some te =>
              let Γ' := addRule Γ x e
              have : free Γ' < free Γ := free_mapIdx_lt Γ _ x en
                (fun i en => by split <;> cases h : en.rule <;> simp_all) hx hn (by simp)
              solve S may Γ' (done (some (x, e)))
                (rest.map (fun q => { q with lhs := Term.replace x e q.lhs, rhs := Term.replace x e q.rhs })
                  ++ [⟨en.type.canon Γ', te.canon Γ', .types log.length⟩])
            | none => .stuck "internal: a term has no type"
          else .stuck "internal: a pending equation is not canonical"
        | none => .stuck "internal: an entry is not in scope"
termination_by (free Γ, eqsSize eqs)
decreasing_by
  all_goals first | exact Prod.Lex.right _ ‹_› | exact Prod.Lex.left _ _ ‹_›

/-- The outcome of forcing a value constructor (§7). `stuck` is an internal error: it must make checking fail,
never refute the value constructor. -/
inductive Forced where
  | ok (Γ : Entries) (fields : List Nat)
  | refuted (why : Failure)
  | stuck (msg : String)
  deriving Repr, Inhabited

/-- Forces `ctor` on `scrut` (§7): opens its fields as fresh entries and equates `scrut` with `ctor` applied to
them and `scrut`'s type with that application's type, every entry being allowed a rule. -/
def force (S : Sigs) (Γ : Entries) (scrut : Term) (ctor : Sig) (mk : TBinder → Nat → Entry → Entry) : Forced :=
  let o := openTele Γ ctor.params [] mk
  let eqn (l r : Term) (why : Why) : Eqn := ⟨l.canon o.Γ, r.canon o.Γ, why⟩
  match typeOf S o.Γ scrut with
  | none => .stuck "internal: the scrutinee has no type"
  | some ty =>
    match solve S (fun _ => true) o.Γ []
      [eqn scrut (.app ctor.head o.env) .scrutinee, eqn ty (ctor.ret.subst o.env) .scrutineeType] with
    | .ok Γ' _ => .ok Γ' o.ids
    | .failed ⟨_, _, .rigid .., _⟩ => .stuck "internal: forcing met an equation no entry can take a rule from"
    | .failed f => .refuted f
    | .stuck msg => .stuck msg

mutual
  def Term.render (Γ : Entries) : Term → String
    | .entry i => match Γ[i]? with
      | some en => if en.origin.isEmpty then s!"#{i}" else en.origin
      | none => s!"#{i}"
    | .bound i => s!"^{i}"
    | .app h as => h.name ++ "(" ++ ", ".intercalate (Term.renderList Γ as) ++ ")"
  def Term.renderList (Γ : Entries) : List Term → List String
    | [] => []
    | a :: as => a.render Γ :: Term.renderList Γ as
end

/-- The lines explaining a refutation of `ctor`: each equation processed, then the failure. -/
def Failure.render (f : Failure) (ctor : Head) : List String :=
  let t (u : Term) := u.render f.Γ
  let why : Why → String
    | .scrutinee => s!"forcing {ctor.name} on the scrutinee"
    | .scrutineeType => s!"the scrutinee's type and {ctor.name}'s"
    | .given => "the equation to solve"
    | .types p => s!"the types of the two sides of {p + 1}"
    | .arg h i p => s!"argument {i + 1} of {h.name} in {p + 1}"
  let line (k : Nat) (s : Step) :=
    s!"{k + 1}. {t s.eqn.lhs} = {t s.eqn.rhs}   ({why s.eqn.why})" ++
      (s.gave.elim "" fun (x, e) => s!", so {t (.entry x)} is {t e}")
  f.log.mapIdx line ++ [match f.clash with
    | .heads a b => s!"refuted: {a.name} and {b.name} are different heads"
    | .occurs x e => s!"refuted: {t (.entry x)} occurs strictly inside {t e}"
    | .rigid a b => s!"refuted: {t a} and {t b} cannot be equated"]

end Pledge
