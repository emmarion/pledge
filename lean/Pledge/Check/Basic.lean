import Pledge.Unify
import Pledge.Eval

namespace Pledge

def code (s : String) : String := "`" ++ s ++ "`"

def plural (n : Nat) (what : String) : String := s!"{n} {what}{if n = 1 then "" else "s"}"

def are (n : Nat) (what : String) : String := s!"{plural n what} {if n = 1 then "is" else "are"}"

def labelled (role : String) (name : Option String) (i : Nat) (owner : Option String := none) : String :=
  s!"{role} {(name.map code).getD (toString (i + 1))}" ++ owner.elim "" (s!" of {code ·}")

def Stmt.pos : Stmt → Pos
  | .let p .. | .patlet p .. | .inspect p => p

def Expr.pos : Expr → Pos
  | .var x => x.pos
  | .app h _ => h.pos
  | .tuple p _ | .match p .. | .sorry p _ => p
  | .block (s :: _) _ => s.pos
  | .block [] f => f.pos
  | .removed => 0

/-- A match with no branches, possibly the final expression of a block (§16). -/
def Expr.absurd : Expr → Bool
  | .match _ _ _ _ [] => true
  | .block _ f => f.absurd
  | _ => false

def WTerm.pos : WTerm → Pos
  | .var n | .app n _ => n.pos
  | .hole p => p

mutual
  /-- Whether `_` (§16) is written anywhere in the term. -/
  def WTerm.holed : WTerm → Bool
    | .var _ => false
    | .app _ as => WTerm.holedList as
    | .hole _ => true
  def WTerm.holedList : List WTerm → Bool
    | [] => false
    | a :: as => a.holed || WTerm.holedList as
end

def Arg.mark : Arg → Option Mark
  | .mk m _ => m

mutual
  def Term.entries : Term → List Nat
    | .entry i => [i]
    | .bound _ => []
    | .app _ as => Term.entriesList as
  def Term.entriesList : List Term → List Nat
    | [] => []
    | a :: as => a.entries ++ Term.entriesList as
end

/-- A result of an expression (§8, §12, §16): its term, and whether it is tainted or erased. -/
structure Res where
  term : Term
  tainted : Bool := false
  erased : Bool := false
  deriving Inhabited

/-- A `_` still being solved (§16): its entry, where it is written, and its parameter's `is` term; a `late` one, in
a tuple `let` binder's annotation, may be solved to what the right-hand side produces. -/
structure Hole where
  id : Nat
  pos : Pos
  is : Option Term
  late : Bool := false

/-- What the checker knows at a position (§7): signatures, entries with their rules, the names in scope (newest
first, each bound to a result whose `erased` says whether the name was bound erased), the scrutinee position whose
taint reached this scope, if any (§12), and the `_` still being solved since the nearest boundary (§16). -/
structure Scope where
  sigs : Sigs
  Γ : Entries
  names : List (String × Res) := []
  taintedBy : Option Pos := none
  holes : List Hole := []

def Scope.lookup (sc : Scope) (n : String) : Option Res := List.lookup n sc.names

def Scope.bind (sc : Scope) : List Id → List Res → Scope
  | x :: xs, r :: rs => ({ sc with names := (x.name.map fun n => [(n, r)]).getD [] ++ sc.names }).bind xs rs
  | _, _ => sc

def Scope.nameOf (sc : Scope) (i : Nat) : Option String :=
  (sc.names.reverse.find? (·.2.term == .entry i)).map (·.1)

def Scope.erasedEntry (sc : Scope) : Term → Bool
  | .entry i => (sc.Γ[i]?).any (·.erased)
  | _ => false

/-- Entries labelled for display: by name where they have one, otherwise by their origin. -/
def Scope.labels (sc : Scope) (Γ : Entries) : Entries :=
  Γ.mapIdx fun i en => { en with origin := (sc.nameOf i).getD (if en.origin.isEmpty then "" else "?" ++ en.origin) }

mutual
  /-- A term as text, entries by their origin and bound variables by the names in `bound`. -/
  def Term.show (Γ : Entries) (bound : List String) : Term → String
    | .entry i => ((Γ[i]?).map (·.origin)).filter (!·.isEmpty) |>.getD s!"#{i}"
    | .bound i => bound.getD i s!"_{i + 1}"
    | .app h as => h.name ++ "(" ++ ", ".intercalate (Term.showList Γ bound as) ++ ")"
  def Term.showList (Γ : Entries) (bound : List String) : List Term → List String
    | [] => []
    | a :: as => a.show Γ bound :: Term.showList Γ bound as
end

/-- A term canonicalized and shown with entries by name, or by their origin. -/
def Scope.text (sc : Scope) (t : Term) (bound : List String := []) : String :=
  (t.canon sc.Γ).show (sc.labels sc.Γ) bound

def Scope.disp (sc : Scope) (t : Term) (bound : List String := []) : String := code (sc.text t bound)

/-- Appends the fresh entry of a `_` (§16), its origin starting `_@`, and records it as a hole. -/
def Scope.addHole (sc : Scope) (type : Term) (is : Option Term) (pos : Pos) (erased : Bool) : Scope × Nat :=
  let en : Entry := { type, origin := s!"_@{pos}", erased }
  ({ sc with Γ := sc.Γ ++ [en], holes := sc.holes ++ [{ id := sc.Γ.length, pos, is }] }, sc.Γ.length)

def Entry.isHole (en : Entry) : Bool := en.origin.startsWith "_@"

def markTainted (Γ : Entries) (rs : List Res) : Entries :=
  Γ.mapIdx fun i en => if rs.any (·.term == .entry i) then { en with tainted := true } else en

structure FnSig where
  params : Telescope
  returns : Telescope
  subterm : List Bool
  tainted : Bool := false

/-- A declared name other than a value: a function (its signature once its telescopes are checked), a type
constructor (its value constructors, `none` for `Type`, and whether its group is declared) or a value
constructor. -/
inductive Global where
  | fn (name : String) (sig : Option FnSig)
  | type (name : String) (ctors : Option (List String)) (done : Bool)
  | ctor (name : String)

def Global.name : Global → String
  | .fn n _ | .type n .. | .ctor n => n

def Global.describe : Global → String
  | .fn .. => "a function"
  | .type .. => "a type constructor"
  | .ctor _ => "a value constructor"

def kindOf (gs : List Global) (n : String) : Option HeadKind :=
  match gs.find? (·.name == n) with
  | some (.type ..) => some .type
  | some (.ctor _) => some .ctor
  | _ => none

/-- The enclosing function (§9): its group and the terms of its `subterm` parameters. -/
structure FnCtx where
  name : String
  group : List String
  subterms : List Term
  subtermNames : List String

/-- What an expression is checked under: the phase, the globals declared so far, the enclosing function,
whether the position is erased (§16), inside a declaration the numbers of entries and names at its start (§13),
how messages name a position given nothing, and whether the position is inside a type constructor's argument, at
any depth, where `_` may stand for anything since nothing there is evaluated (§16). -/
structure Ctx where
  phase : Nat := 1
  globals : List Global
  fn : Option FnCtx := none
  erased : Bool := false
  decl : Option (Nat × Nat) := none
  place : String := "this position"
  inType : Bool := false

def Ctx.global (C : Ctx) (n : String) : Option Global := C.globals.find? (·.name == n)

/-- The context an expression is checked in: erased when `whole` is (§16). -/
abbrev Ctx.enter (C : Ctx) (whole : Bool) : Ctx :=
  { C with erased := whole }

/-- An entry of what a position is given (§8); `type` is `none` for a tuple `let` binder with neither a type nor
an `is` clause. -/
structure Want where
  name : Option String
  type : Option Term
  is : Option Term := none
  mult : Mult := .many

def Want.of (b : TBinder) : Want := ⟨b.name, some b.type, b.is, b.mult⟩

/-- What a position is given (§8): bound variables of `wants` index `env`, then the earlier results. `whole` says
whether `_` may stand for it (§10). -/
structure Given where
  wants : List Want
  env : List Term := []
  whole : Bool := false
  params : Option Nat := none
  label : Option (Nat → String) := none

def Given.erase (g : Given) : Given := { g with wants := g.wants.map ({ · with mult := .erased }) }

def Given.erasedAt (g : Given) (i : Nat) : Bool := (g.wants[i]?).any (·.mult == .erased)

/-- Every entry is erased, and there is one (§16). -/
def Given.allErased (g : Given) : Bool := g.wants.any (·.mult == .erased) && g.wants.all (·.mult == .erased)

/-- The type and `is` terms of each entry, instantiated by the results before it. -/
def Given.terms (g : Given) (rs : List Res) : List Term :=
  (List.range g.wants.length).flatMap fun i =>
    let env := g.env ++ (rs.take i).map (·.term)
    ((g.wants[i]?).map fun w => (w.type.toList ++ w.is.toList).map (·.subst env)).getD []

structure Snapshot where
  pos : Pos
  sc : Scope
  given : Option Given
  fn : Option FnCtx
  decl : Option (Nat × Nat)

/-- A checking error: where it is, its message, built only when it is reported, and the `inspect;` snapshots
met before it in the statement where it occurs. -/
structure CheckError where
  pos : Pos
  msg : Unit → String
  snaps : List Snapshot := []

abbrev CheckM := Except CheckError

def failAt (pos : Pos) (msg : Unit → String) : CheckM α := throw { pos, msg }

/-- An error that is meant to be unreachable; the program is rejected. -/
def internal (pos : Pos) (what : String) : CheckM α :=
  failAt pos fun _ => s!"internal: {what}; the checker rejects the program"

/-- Rejects the program unless `ok`: a check meant never to fail, which the soundness proof relies on. -/
def ensure (ok : Bool) (pos : Pos) (what : String) : CheckM Unit :=
  unless ok do internal pos what

/-- Keeps the snapshots met so far on an error. -/
def keep (snaps : List Snapshot) : CheckM α → CheckM α
  | .ok a => .ok a
  | .error e => .error { e with snaps := snaps ++ e.snaps }

def miscount (pos : Pos) (want : Nat) (got : String) : CheckM α :=
  failAt pos fun _ => s!"{are want "value"} expected here, and this {got} (§8)"

def Scope.typeOf (sc : Scope) (pos : Pos) (t : Term) : CheckM Term :=
  match Pledge.typeOf sc.sigs sc.Γ t with
  | some ty => pure ty
  | none => internal pos "a term has no type"

def Scope.sig (sc : Scope) (pos : Pos) (h : Head) : CheckM Sig :=
  match sc.sigs.find h with
  | some s => pure s
  | none => internal pos s!"{h.name} has no signature"

/-- What checking an expression produces: the scope after it, its results, the tree to evaluate (§14) and the
`inspect;` snapshots met. -/
structure Out where
  sc : Scope
  res : List Res
  tree : Expr
  snaps : List Snapshot := []

def single (pos : Pos) : List Res → CheckM Res
  | [r] => pure r
  | rs => miscount pos 1 s!"produces {rs.length}"

/-- After an expression is checked (§12, §16): taint from a tainted scope, the rule that an erased result is
only in an erased position, and removal of an expression that is wholly erased or whose results are all tainted. -/
def finish (C : Ctx) (whole : Bool) (g : Option Given) (e : Expr) (o : Out) : CheckM Out := do
  ensure (!o.res.isEmpty) e.pos "an expression produces no value"
  let res := if o.sc.taintedBy.isSome then o.res.map ({ · with tainted := true }) else o.res
  unless whole do
    if let some i := (List.range res.length).find? fun i => (res[i]?).any (·.erased) && !g.any (·.erasedAt i) then
      failAt e.pos fun _ =>
        let what := match e with
          | .var ⟨some n, _⟩ => code n
          | _ => if res.length = 1 then "this value" else s!"value {i + 1} of this"
        let place : String := match g.map Given.label with
          | some (some l) => l i
          | some none => "this position"
          | none => C.place
        s!"{what} is erased, and {place} is not; an erased value " ++
        "is allowed only in an erased position: a type, an argument for an erased parameter or field, " ++
        "or the result for an erased return or binder (§16)"
  pure { o with res, tree := if whole || res.all (·.tainted) then .removed else o.tree }

/-- Solves the `_` being solved (§16) from an equation, only their entries taking rules; nothing when there are none. -/
def solveHoles (sc : Scope) (lhs rhs : Term) (pos : Pos) : CheckM Scope :=
  match sc.holes with
  | [] => pure sc
  | holes =>
    match unify sc.sigs sc.Γ lhs rhs (fun i => holes.any (·.id == i)) with
    | .error msg => internal pos msg
    | .ok (Γ, stuck) =>
      let now := { sc with Γ }
      match stuck.bind fun (a, b) => (holes.find? fun h => a.occurs h.id || b.occurs h.id).map (a, b, ·) with
      | some (a, b, h) => failAt h.pos fun _ =>
        s!"this `_` cannot be inferred: it would need {now.disp a} and {now.disp b} to be equal, " ++
        "and this checker solves a `_` only by giving a rule to its own entry"
      | none => pure now

/-- Checks results against what the position is given (§8): each entry is instantiated to its result's term. -/
def against (sc : Scope) (g : Given) (pos : Pos) (rs : List Res) : CheckM Scope := do
  if rs.length ≠ g.wants.length then miscount pos g.wants.length s!"produces {rs.length}"
  go sc [] g.wants rs
where
  go (sc : Scope) (prev : List Term) : List Want → List Res → CheckM Scope
    | w :: ws, r :: rs => do
      let i := prev.length
      let env := g.env ++ prev
      let what (_ : Unit) := (g.label.map (· i)).getD <| match w.name with
        | some x => code x
        | none => if g.wants.length = 1 then "the value expected here" else s!"value {i + 1}"
      let has ← sc.typeOf pos r.term
      let ty := w.type.map (·.subst env)
      let is := w.is.map (·.subst env)
      let sc ← match ty with
        | some ty => solveHoles sc ty has pos
        | none => pure sc
      let sc ← match is with
        | some e => solveHoles sc e r.term pos
        | none => pure sc
      if let some ty := ty then
        unless identical sc.Γ ty has do
          failAt pos fun _ => s!"{what ()} must have type {sc.disp ty}, and this has type {sc.disp has}"
      if let some e := is then
        unless identical sc.Γ e r.term do
          failAt pos fun _ => s!"{what ()} must be {sc.disp e}, and this is {sc.disp r.term}"
      go sc (prev ++ [r.term]) ws rs
    | _, _ => pure sc

def produced (sc : Scope) (g : Option Given) (pos : Pos) (rs : List Res) (tree : Expr) : CheckM Out := do
  let sc ← match g with
    | some g => against sc g pos rs
    | none => pure sc
  pure ⟨sc, rs, tree, []⟩

/-- Checks a `_` at its boundary (§16): its solution mentions no unsolved `_` and only entries before it, has its
type and meets its parameter's `is` term; gives whether the solution is tainted (§12). -/
def settle (sc : Scope) (h : Hole) : CheckM Bool := do
  let value := (Term.entry h.id).canon sc.Γ
  if value.entries.any fun x => (sc.Γ[x]?).any Entry.isHole then failAt h.pos fun _ =>
    "this `_` cannot be inferred: a `_` is solved only by unification, from the arguments around it " ++
    "and what its position is given, before the call, statement, scrutinee, body or binder it is in ends, " ++
    "and these do not determine it (§16)"
  if !h.late && value.entries.any (· > h.id) then failAt h.pos fun _ =>
    s!"this `_` would be {sc.disp value}, which mentions what is produced only after it, " ++
    "such as a result of the call it is an argument of, and a `_` is solved only to what exists before it"
  let some en := sc.Γ[h.id]? | internal h.pos "a `_` has no entry"
  let has ← sc.typeOf h.pos value
  unless identical sc.Γ en.type has do failAt h.pos fun _ =>
    s!"this `_` would be {sc.disp value}, of type {sc.disp has}, and it must have type {sc.disp en.type}"
  if let some e := h.is then
    unless identical sc.Γ e value do failAt h.pos fun _ =>
      s!"this `_` must be {sc.disp e}, and it would be {sc.disp value}"
  pure (value.entries.any fun x => (sc.Γ[x]?).any (·.tainted))

/-- A boundary (§16): every `_` created since `since` is settled; a result whose term mentions a `_` solved to
something tainted, or every result when `all`, becomes tainted (§12), and the tree is removed when every result
is. Nothing happens when there is no such `_`. -/
def close (o : Out) (since : Nat) (all : Bool) : CheckM Out :=
  match o.sc.holes.drop since with
  | [] => pure o
  | mine => do
    let done := mine.zip (← mine.mapM (settle o.sc))
    let sc := { o.sc with holes := o.sc.holes.take since }
    let bad := (done.filter (·.2)).map (·.1.id)
    if bad.isEmpty then pure { o with sc } else
    let res := o.res.map fun r => if all || r.term.entries.any bad.contains then { r with tainted := true } else r
    pure ⟨{ sc with Γ := markTainted sc.Γ (res.filter (·.tainted)) }, res,
      if res.all (·.tainted) then .removed else o.tree, o.snaps⟩

/-- Checks with no `_` being solved, then closes the boundary (§16), the enclosing `_` being solved again after. -/
def closed (sc : Scope) (check : Scope → CheckM Out) : CheckM Out := do
  let o ← check { sc with holes := [] }
  let o ← keep o.snaps (close o 0 false)
  pure { o with sc := { o.sc with holes := sc.holes } }

/-- Results of an application (§8), checked against what the position is given; a call is a boundary (§16), whose
`_` are those created since `since`. -/
def applied (sc : Scope) (g : Option Given) (pos : Pos) (rs : List Res) (tree : Expr) (since : Option Nat)
    (snaps : List Snapshot) : CheckM Out := keep snaps do
  let o ← produced sc g pos rs tree
  let o ← match since with
    | some n => close o n true
    | none => pure o
  pure { o with snaps }

/-- Opens a telescope to fresh entries, each a result (§3). -/
def opened (sc : Scope) (tele : Telescope) (env : List Term) (kind : String) (pos : Pos) (tainted : Nat → Bool) :
    Scope × List Res :=
  let o := openTele sc.Γ tele env fun b i en =>
    { en with origin := s!"{kind}.{b.name.getD (toString (i + 1))}@{pos}", tainted := tainted i }
  ({ sc with Γ := o.Γ }, o.ids.mapIdx fun i id => ⟨.entry id, tainted i, ((o.Γ[id]?).map (·.erased)).getD false⟩)

def notValue (C : Ctx) (sc : Scope) (n : Name) : CheckM α :=
  let nullary (h : Head) : String :=
    if ((sc.sigs.find h).map fun s : Sig => s.params.isEmpty).getD false then "" else "..."
  failAt n.pos fun _ => match C.global n.name with
    | none => s!"{code n.name} is not in scope"
    | some g =>
      let args := match g with
        | .type .. => nullary ⟨.type, n.name⟩
        | .ctor _ => nullary ⟨.ctor, n.name⟩
        | _ => "..."
      s!"{code n.name} is {g.describe}, which is not a value: " ++ match g with
        | .fn .. => "functions are not first class (§4)"
        | _ => s!"it is applied, as in {code s!"{n.name}({args})"}"

/-- The no-shadowing rule (§2) for a name introduced among `seen`. -/
def fresh (C : Ctx) (sc : Scope) (seen : List String) (name : Option String) (pos : Pos) :
    CheckM (List String) :=
  match name with
  | none => pure seen
  | some n =>
    if seen.contains n then failAt pos fun _ => s!"{code n} is introduced twice here (§2)"
    else if (sc.lookup n).isSome || (C.global n).isSome then
      failAt pos fun _ => s!"{code n} is already in scope here, and no name is allowed to be shadowed (§2)"
    else pure (n :: seen)

def freshAll (C : Ctx) (sc : Scope) (ids : List Id) : CheckM Unit :=
  discard <| ids.foldlM (fun seen x => fresh C sc seen x.name x.pos) []

/-- `abstract?`, rejecting the program when the term is not closed. -/
def abstractChecked (Γ : Entries) (t : Term) (ids : List Nat) (pos : Pos) : CheckM Term :=
  match abstract? Γ t ids with
  | some u => pure u
  | none => internal pos "a term to abstract is not closed"

def arity (pos : Pos) (name : String) (params args : Nat) : CheckM Unit :=
  if args ≠ params then
    failAt pos fun _ => s!"{code name} takes {plural params "argument"}, and {are args "argument"} given"
  else pure ()

/-- The error for applying a name that is not a function, type constructor or value constructor. -/
def notApplied (sc : Scope) (h : Name) : CheckM α := failAt h.pos fun _ => if (sc.lookup h.name).isSome
  then s!"{code h.name} is a value, and only functions, type constructors and value constructors are applied (§4)"
  else s!"{code h.name} is not in scope"

mutual
  /-- A skeleton term (§3) without `_`. -/
  def checkTerm (C : Ctx) (sc : Scope) : WTerm → CheckM Res
    | .hole p => failAt p fun _ => "`_` stands only for a whole argument or inside a type (§16)"
    | .var x => match sc.lookup x.name with
      | some r => pure { r with tainted := r.tainted || sc.taintedBy.isSome }
      | none => notValue C sc x
    | .app h args => do
      let kind ← match C.global h.name with
        | some (.fn ..) => failAt h.pos fun _ =>
          s!"{code h.name} is a function, and a type contains no function call (§3)"
        | some (.type ..) => pure HeadKind.type
        | some (.ctor _) => pure .ctor
        | none => notApplied sc h
      let sig ← sc.sig h.pos ⟨kind, h.name⟩
      arity h.pos h.name sig.params.length args.length
      let rs ← checkTerms C sc h.name (if kind = .type then "parameter" else "field") sig.params [] args
      pure ⟨.app sig.head (rs.map (·.term)), rs.any (·.tainted) || sc.taintedBy.isSome, false⟩
  def checkTerms (C : Ctx) (sc : Scope) (owner role : String) (params : Telescope) (prev : List Res) :
      List WTerm → CheckM (List Res)
    | [] => pure []
    | a :: as => match params with
      | p :: ps => do
        let r ← checkTerm C sc a
        let i := prev.length
        let label := some fun _ => labelled role p.name i owner
        let _ ← against { sc with holes := [] } { wants := [Want.of p], env := prev.map (·.term), label } a.pos [r]
        return r :: (← checkTerms C sc owner role ps (prev ++ [r]) as)
      | [] => internal a.pos "an argument has no parameter"
end

def Ann.term : Ann → WTerm
  | .type t | .is t => t

/-- What an argument is given (§8); a type constructor's argument is erased from phase 2 on (§16). -/
def argGiven (p : TBinder) (prev : List Res) (role owner : String) (erased : Bool) : Given :=
  let i := prev.length
  { wants := [{ Want.of p with mult := if erased then .erased else p.mult }], env := prev.map (·.term),
    label := some fun _ => labelled role p.name i owner }

/-- A `_` argument (§16): a fresh entry typed by its parameter, solved by unification, erased where the argument
is; it is never evaluated, so its tree is `removed`. -/
def holeArg (C : Ctx) (sc : Scope) (g : Given) (p : TBinder) (prev : List Res) (pos : Pos) : CheckM Out := do
  let env := prev.map (·.term)
  let type := p.type.subst env
  let erased := C.erased || g.erasedAt 0
  unless erased || C.inType || identical sc.Γ type .TYPE do failAt pos fun _ =>
    "`_` stands for an argument that is erased or has type `Type()`, or for part of a type (§16), " ++
    s!"and {(g.label.map (· 0)).getD "this argument"} is none of these"
  let is := p.is.map (·.subst env)
  let (sc, id) := sc.addHole type is pos erased
  let sc ← match is with
    | some e => solveHoles sc (.entry id) e pos
    | none => pure sc
  pure ⟨sc, [⟨.entry id, false, erased⟩], .removed, []⟩

mutual
  /-- A skeleton term with `_` (§3, §16), checked as an expression in a position that is not evaluated: its `_`
  become holes of the scope, and inside a type constructor's argument may stand for anything. -/
  def checkSkel (C : Ctx) (sc : Scope) (g : Option Given) : WTerm → CheckM Out
    | .hole p => failAt p fun _ => "`_` stands only for a whole argument or inside a type (§16)"
    | .var x => match sc.lookup x.name with
      | some r => produced sc g x.pos [{ r with tainted := r.tainted || sc.taintedBy.isSome }] .removed
      | none => notValue C sc x
    | .app h args => do
      let kind ← match C.global h.name with
        | some (.fn ..) => failAt h.pos fun _ =>
          s!"{code h.name} is a function, and a type contains no function call (§3)"
        | some (.type ..) => pure HeadKind.type
        | some (.ctor _) => pure .ctor
        | none => notApplied sc h
      let sig ← sc.sig h.pos ⟨kind, h.name⟩
      arity h.pos h.name sig.params.length args.length
      let role := if kind = .type then "parameter" else "field"
      let (sc', rs) ← checkSkels { C with inType := C.inType || kind == .type } sc h.name role
        (kind = .type && C.phase ≥ 2) sig.params [] args
      produced sc' g h.pos [⟨.app sig.head (rs.map (·.term)), rs.any (·.tainted) || sc.taintedBy.isSome, false⟩]
        .removed
  def checkSkels (C : Ctx) (sc : Scope) (owner role : String) (erased : Bool) (params : Telescope) (prev : List Res) :
      List WTerm → CheckM (Scope × List Res)
    | [] => pure (sc, [])
    | a :: as => match params with
      | p :: ps => do
        let g := argGiven p prev role owner erased
        let o ← match a with
          | .hole pos => holeArg C sc g p prev pos
          | a => checkSkel C sc (some g) a
        let r ← single a.pos o.res
        let (sc, rs) ← checkSkels C o.sc owner role erased ps (prev ++ [r]) as
        pure (sc, r :: rs)
      | [] => internal a.pos "an argument has no parameter"
end

/-- A written term with `_` (§16), in a position that is erased from phase 2 on (§3); a whole `_` stands for a
type when `whole`. Its `_` stay holes of the scope. -/
def written (C : Ctx) (sc : Scope) (whole : Bool) (t : WTerm) : CheckM Out :=
  let C := { C with erased := C.erased || C.phase ≥ 2 }
  match t, whole with
  | .hole p, true =>
    let (sc, id) := sc.addHole .TYPE none p C.erased
    pure ⟨sc, [⟨.entry id, false, C.erased⟩], .removed, []⟩
  | t, _ => checkSkel C sc none t

/-- A written term (§3), a whole `_` standing for a type when `whole`; its `_` (§16) are solved by the term alone,
and its term mentions only entries of `sc`. -/
def term (C : Ctx) (sc : Scope) (t : WTerm) (whole : Bool) : CheckM Res :=
  if t.holed then do
    let o ← written C { sc with holes := [] } whole t >>= (close · 0 false)
    let r ← single t.pos o.res
    pure { r with term := r.term.mapEntries fun i =>
      if i < sc.Γ.length then .entry i else ((o.sc.Γ[i]?).bind (·.rule)).getD (.entry i) }
  else checkTerm C sc t

def isType (sc : Scope) (pos : Pos) (t : Term) : CheckM Unit := do
  let ty ← sc.typeOf pos t
  unless identical sc.Γ ty .TYPE do
    failAt pos fun _ => s!"{sc.disp t} is not a type: its type is {sc.disp ty}, not `Type()` (§3)"

/-- A checked annotation (§6): the type, the `is` term if any, and taint. -/
def annotate (C : Ctx) (sc : Scope) : Ann → CheckM (Term × Option Term × Bool)
  | .is t => do
    let r ← term C sc t false
    pure (← sc.typeOf t.pos r.term, some r.term, r.tainted)
  | .type t => do
    let r ← term C sc t true
    isType sc t.pos r.term
    pure (r.term, none, r.tainted)

/-- An annotation of a tuple `let` binder, checked with its `_` (§16) left as holes of the scope. -/
def annotateOpen (C : Ctx) (sc : Scope) (ann : Ann) : CheckM (Scope × Term × Option Term) := do
  let o ← written C sc (ann matches .type _) ann.term
  let r ← single ann.term.pos o.res
  match ann with
  | .is t => pure (o.sc, ← o.sc.typeOf t.pos r.term, some r.term)
  | .type t => do isType o.sc t.pos r.term; pure (o.sc, r.term, none)

/-- A binder opened as written (§3): its entry, named, and its type and `is` term as checked. -/
structure Opening where
  sc : Scope
  id : Nat
  type : Term
  is : Option Term
  tainted : Bool

def Scope.openBinder (sc : Scope) (name : Id) (type : Term) (is : Option Term) (mult : Option Mult) (kind : String)
    (tainted : Bool) : Opening :=
  let o := openTele sc.Γ [⟨name.name, type, is, mult.getD .many⟩] [] fun _ _ en =>
    { en with origin := s!"{kind}@{name.pos}" }
  let id := sc.Γ.length
  ⟨Scope.bind { sc with Γ := o.Γ } [name] [⟨.entry id, false, false⟩], id, type, is, tainted⟩

def opening (C : Ctx) (sc : Scope) (name : Id) (ann : Ann) (mult : Option Mult) (kind : String) :
    CheckM Opening := do
  let (type, is, tainted) ← annotate C sc ann
  pure (sc.openBinder name type is mult kind tainted)

def abstracted (Γ : Entries) (name : Option String) (mult : Option Mult) (pos : Pos) (type : Term)
    (is : Option Term) (ids : List Nat) : CheckM TBinder := do
  pure ⟨name, ← abstractChecked Γ type ids pos, ← is.mapM (abstractChecked Γ · ids pos), mult.getD .many⟩

/-- A checked telescope: the scope with its binders opened and named, their entries, the telescope over its own
bound variables after `outer`'s, and whether any annotation is tainted. -/
structure Checked where
  sc : Scope
  ids : List Nat
  tele : Telescope
  tainted : Bool

def telescope (C : Ctx) (sc : Scope) (bs : List Binder) (kind : String) (outer : List Nat := []) :
    CheckM Checked := do
  let (sc', seen, opens) ← go sc [] [] bs
  let _ := seen
  let ids := opens.map (·.2.id)
  let tele ← (bs.zip opens).mapM fun (b, _, o) =>
    abstracted sc'.Γ b.name.name b.mult b.name.pos o.type o.is (outer ++ ids)
  pure ⟨sc', ids, tele, opens.any (·.2.tainted)⟩
where
  go (sc : Scope) (seen : List String) (acc : List (Binder × Opening)) :
      List Binder → CheckM (Scope × List String × List (Binder × Opening))
    | [] => pure (sc, seen, acc)
    | b :: bs => do
      let seen ← fresh C sc seen b.name.name b.name.pos
      let o ← opening C sc b.name b.ann b.mult kind
      go o.sc seen (acc ++ [(b, o)]) bs

def header (C : Ctx) (sc : Scope) (h : Header) : CheckM (Checked × Checked) := do
  let ps ← telescope C sc (h.params.map (·.binder)) "param"
  pure (ps, ← telescope C ps.sc h.returns "binder" ps.ids)

/-- The telescope a `match` annotation or `sorry` stands for, and its outer environment (§10, §12); `_` takes
the given telescope with its multiplicities (§16). -/
def annotation (C : Ctx) (sc : Scope) (g : Option Given) : Tele → CheckM (Telescope × List Term)
  | .binders bs => do pure ((← telescope C sc bs "binder").tele, [])
  | .hole p => match g with
    | some g =>
      if g.whole then do
        let tele ← g.wants.mapM fun w => match w.type with
          | some t => pure ⟨w.name, t, w.is, w.mult⟩
          | none => internal p "an undetermined entry in a whole telescope"
        pure (tele, g.env)
      else failAt p fun _ => "`_` stands for the whole telescope given at its position, and none is given here (§10)"
    | none => failAt p fun _ => "`_` stands for the whole telescope given at its position, and none is given here (§10)"

mutual
  def WTerm.unknown (untyped : List String) : WTerm → Option WTerm
    | .var n => if untyped.contains n.name then some (.var n) else none
    | .app h as => if untyped.contains h.name then some (.app h as) else WTerm.unknownList untyped as
    | .hole _ => none
  def WTerm.unknownList (untyped : List String) : List WTerm → Option WTerm
    | [] => none
    | a :: as => (a.unknown untyped).orElse fun _ => WTerm.unknownList untyped as
end

def letWant (Γ : Entries) (ids : List Nat) : LetBinder × Option Opening → CheckM Want
  | (b, some o) => do
    let t ← abstracted Γ b.name.name b.mult b.name.pos o.type o.is ids
    pure (Want.of t)
  | (b, none) => pure ⟨b.name.name, none, none, b.mult.getD .many⟩

/-- What a tuple `let` gives its right-hand side (§8): its binders as a telescope, an unannotated binder taking
any result, and the scope the right-hand side is checked in. When an annotation has `_` (§16), every annotation
is checked with its `_` left as holes, which are `late`, and that scope keeps the binders' entries and the holes,
without the binders' names. -/
def letWants (C : Ctx) (sc : Scope) (bs : List LetBinder) : CheckM (List Want × Scope) := do
  let holed := bs.any (·.ann.any (·.term.holed))
  let (sc', opens) ← go holed sc [] [] bs
  let ws ← (bs.zip opens).mapM (letWant sc'.Γ (opens.map fun o => (o.map (·.id)).getD sc'.Γ.length))
  let late := sc.holes ++ (sc'.holes.drop sc.holes.length).map fun h => { h with late := true }
  pure (ws, if holed then { sc' with names := sc.names, holes := late } else sc)
where
  go (holed : Bool) (sc : Scope) (untyped : List String) (acc : List (Option Opening)) :
      List LetBinder → CheckM (Scope × List (Option Opening))
    | [] => pure (sc, acc)
    | b :: bs => match b.ann with
      | some ann => do
        if let some u := ann.term.unknown untyped then
          failAt u.pos fun _ => s!"{code (match u with | .var n | .app n _ => n.name | .hole _ => "_")} has no " ++
            "type here: give it one before referring to it"
        let o ← if holed then do
            let (sc, type, is) ← annotateOpen C sc ann
            pure (sc.openBinder b.name type is b.mult "binder" false)
          else opening C sc b.name ann b.mult "binder"
        go holed o.sc untyped (acc ++ [some o]) bs
      | none => go holed sc ((b.name.name.map ([·])).getD [] ++ untyped) (acc ++ [none]) bs

def unmarked (args : List Arg) (why : Unit → String) : CheckM Unit :=
  match args.find? (·.mark.isSome) with
  | some a => failAt a.expr.pos fun _ => s!"only a call within its group has marks (§9), and {why ()}"
  | none => pure ()

/-- Checks the §9 marks of a call within the group; gives the positions of the callee's `subterm` parameters
and the `k` of the one marked `subterm`. -/
def marks (pos : Pos) (args : List Arg) (name : String) (sig : FnSig) (fn : FnCtx) : CheckM (List Nat × Nat) := do
  let subs := (List.range sig.subterm.length).filter (sig.subterm.getD · false)
  let at? := args.findIdx? (·.mark == some .subterm)
  let within := s!"this call is within {code name}'s group, so it must mark one argument `subterm`"
  let k ← match at?.bind subs.idxOf? with
    | some k => pure k
    | none =>
      let p := (at?.bind fun i => (args[i]?).map (·.expr.pos)).getD pos
      failAt p fun _ =>
        if subs.isEmpty then s!"{within}, and {code name} has no `subterm` parameter to mark an argument for (§9)"
        else match at? with
          | none => s!"{within}: the argument for one of {code name}'s `subterm` parameters (§9)"
          | some i => s!"{labelled "parameter" ((sig.params[i]?).bind (·.name)) i name} is not a `subterm` " ++
              "parameter, so its argument is not marked `subterm` (§9)"
  let _ ← args.mapIdxM fun i a => do
    let want := if at? = some i then some Mark.subterm else if (subs.take k).contains i then some .same else none
    if a.mark ≠ want then failAt a.expr.pos fun _ => match want with
      | some _ => s!"this argument is for a `subterm` parameter of {code name} before the one marked `subterm`, " ++
          "so it is marked `same` (§9)"
      | none => s!"this argument is not marked: only the arguments for {code name}'s `subterm` parameters " ++
          "up to the one marked `subterm` are (§9)"
  if fn.subterms.length ≤ k then
    failAt pos fun _ => s!"this marks {code name}'s `subterm` parameter {k + 1} `subterm`, and {code fn.name} has " ++
      s!"only {plural fn.subterms.length "`subterm` parameter"} (§9)"
  pure (subs, k)

/-- The decrease of §9 at a call within the group. -/
def decrease (sc : Scope) (pos : Pos) (args : List Arg) (rs : List Res) (fn : FnCtx) (subs : List Nat) (k : Nat) :
    CheckM Unit :=
  (List.range (k + 1)).forM fun j => do
    let some p := subs[j]? | internal pos "a `subterm` parameter is missing"
    let some r := rs[p]? | internal pos "an argument is missing"
    let some own := fn.subterms[j]? | internal pos "a `subterm` parameter of the caller is missing"
    let strict := j = k
    let ok := if strict then isStrictSubterm sc.Γ r.term own else identical sc.Γ r.term own
    unless ok do
      failAt ((args[p]?.map (·.expr.pos)).getD pos) fun _ =>
        s!"{sc.disp r.term} is not {if strict then "a strict subterm of" else "canonically identical to"} " ++
        s!"{code ((fn.subtermNames[j]?).getD "_")}, {code fn.name}'s `subterm` parameter {j + 1}, " ++
        s!"which is {sc.disp own} here (§9)"

structure Forcing where
  name : String
  forced : Forced
  pat : Option Pattern

/-- The value constructors of the scrutinee's data type (§10), with their signatures. -/
def dataCtors (C : Ctx) (sc : Scope) (t : Term) (pos : Pos) : CheckM (List (String × Sig)) := do
  let ty := (← sc.typeOf pos t).canon sc.Γ
  let notData (_ : Unit) := s!"the scrutinee's type {sc.disp ty} is not a data type (§10)"
  match ty with
  | .app h _ => match C.global h.name with
    | some (.type _ (some cs) true) => cs.mapM fun c => do pure (c, ← sc.sig pos ⟨.ctor, c⟩)
    | some (.type _ none _) => failAt pos fun _ =>
      "this has type `Type()`, and a value of type `Type()` cannot be the scrutinee of a `match` or pattern `let` (§4)"
    | some (.type n _ false) => failAt pos fun _ => s!"{code n} is still being declared here"
    | _ => failAt pos notData
  | _ => failAt pos notData

/-- Forces every value constructor of the scrutinee's data type (§7, §10), after checking the patterns; under an
erased match or pattern `let`, every field's entry is erased (§16). -/
def forcings (C : Ctx) (sc : Scope) (t : Term) (scrutPos : Pos) (pats : List Pattern) (at_ : Pos) (erased : Bool) :
    CheckM (List Forcing) := do
  let ctors ← dataCtors C sc t scrutPos
  let _ ← pats.foldlM (init := ([] : List String)) fun seen p => do
    let n := p.ctor.name
    let some (_, sig) := ctors.find? (·.1 == n) | failAt p.ctor.pos fun _ =>
      s!"{code n} is not a value constructor of the scrutinee's type {sc.disp ((typeOf sc.sigs sc.Γ t).getD t)}"
    if seen.contains n then failAt p.ctor.pos fun _ => s!"{code n} already has a branch (§10)"
    if p.fields.length ≠ sig.params.length then failAt p.ctor.pos fun _ =>
      s!"{code n} has {plural sig.params.length "field"}, and this pattern names {p.fields.length}"
    pure (n :: seen)
  ctors.mapM fun (n, sig) => do
    let pat := pats.find? (·.ctor.name == n)
    let forced := force sc.sigs sc.Γ t sig fun b i en =>
      let pos := ((pat.bind (·.fields[i]?)).map (·.pos)).getD at_
      { en with origin := s!"{n}.{b.name.getD (toString (i + 1))}@{pos}", erased := en.erased || erased }
    match forced with
    | .stuck msg => internal scrutPos msg
    | _ => pure ⟨n, forced, pat⟩

/-- The scope and fields of a value constructor that survives forcing; a refuted one is an error (§10). -/
def survivor (sc : Scope) (fs : List Forcing) (n : String) (pos : Pos) (consequence : String) :
    CheckM (Entries × List Nat) :=
  match fs.find? (·.name == n) with
  | some ⟨_, .ok Γ ids, _⟩ => pure (Γ, ids)
  | some ⟨_, .refuted f, _⟩ => failAt pos fun _ =>
    "\n".intercalate (s!"{code n} is refuted here, so {consequence} (§10)" ::
      ({ f with Γ := sc.labels f.Γ }).render ⟨.ctor, n⟩)
  | some ⟨_, .stuck msg, _⟩ => internal pos msg
  | none => internal pos s!"{n} was not forced"

def fieldRes (ids : List Nat) : List Res := ids.map fun id => ⟨.entry id, false, false⟩

def reach (sc : Scope) (r : Res) (pos : Pos) : Option Pos :=
  sc.taintedBy.orElse fun _ => if r.tainted then some pos else none

/-- The scope after a pattern `let` (§10, §11), its value constructor's forcing having survived. -/
def patBind (sc : Scope) (r : Res) (rhsPos : Pos) (comptime : Bool) (pat : Pattern) (fs : List Forcing) :
    CheckM Scope := do
  let (Γ, ids) ← survivor sc fs pat.ctor.name pat.ctor.pos "this pattern `let` cannot match"
  unless comptime do
    if let some other := fs.find? fun f => f.name != pat.ctor.name && f.forced matches .ok .. then
      failAt pat.ctor.pos fun _ => s!"{code other.name} is not refuted here, " ++
        "and exactly one value constructor must survive forcing at a pattern `let` (§10)"
  pure (Scope.bind { sc with Γ, taintedBy := reach sc r rhsPos } pat.fields (fieldRes ids))

end Pledge
