import Pledge.Unify
import Pledge.Eval

namespace Pledge

/-- A checking error: where it is, and its message, built only when it is reported. -/
structure CheckError where
  pos : Pos
  msg : Unit → String

abbrev CheckM := Except CheckError

def failAt (pos : Pos) (msg : Unit → String) : CheckM α := throw ⟨pos, msg⟩

/-- An error that is meant to be unreachable; the program is rejected. -/
def internal (pos : Pos) (what : String) : CheckM α :=
  failAt pos fun _ => s!"internal: {what}; the checker rejects the program"

def code (s : String) : String := "`" ++ s ++ "`"

def plural (n : Nat) (what : String) : String := s!"{n} {what}{if n = 1 then "" else "s"}"

def are (n : Nat) (what : String) : String := s!"{plural n what} {if n = 1 then "is" else "are"}"

def labelled (role : String) (name : Option String) (i : Nat) (owner : Option String := none) : String :=
  s!"{role} {(name.map code).getD (toString (i + 1))}" ++ owner.elim "" (s!" of {code ·}")

def miscount (pos : Pos) (want : Nat) (got : String) : CheckM α :=
  failAt pos fun _ => s!"{are want "value"} expected here, and this {got} (§8)"

def Stmt.pos : Stmt → Pos
  | .let p .. | .patlet p .. | .inspect p => p

def Expr.pos : Expr → Pos
  | .var x => x.pos
  | .app h _ => h.pos
  | .tuple p _ | .match p .. | .sorry p _ => p
  | .block (s :: _) _ => s.pos
  | .block [] f => f.pos
  | .removed => 0

def WTerm.pos : WTerm → Pos
  | .var n | .app n _ => n.pos

def Arg.mark : Arg → Option Mark
  | .mk m _ => m

/-- A result of an expression (§8, §12): its term, and whether it is tainted or erased. -/
structure Res where
  term : Term
  tainted : Bool := false
  erased : Bool := false
  deriving Inhabited

/-- What the checker knows at a position (§7): signatures, entries with their rules, the names in scope (newest
first, each bound to a result), and the scrutinee position whose taint reached this scope, if any (§12). -/
structure Scope where
  sigs : Sigs
  Γ : Entries
  names : List (String × Res) := []
  taintedBy : Option Pos := none

def Scope.lookup (sc : Scope) (n : String) : Option Res := List.lookup n sc.names

def Scope.bind (sc : Scope) : List Id → List Res → Scope
  | x :: xs, r :: rs => ({ sc with names := (x.name.map fun n => [(n, r)]).getD [] ++ sc.names }).bind xs rs
  | _, _ => sc

def Scope.nameOf (sc : Scope) (i : Nat) : Option String :=
  (sc.names.reverse.find? (·.2.term == .entry i)).map (·.1)

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

def Scope.typeOf (sc : Scope) (pos : Pos) (t : Term) : CheckM Term :=
  match Pledge.typeOf sc.sigs sc.Γ t with
  | some ty => pure ty
  | none => internal pos "a term has no type"

def Scope.sig (sc : Scope) (pos : Pos) (h : Head) : CheckM Sig :=
  match sc.sigs.find h with
  | some s => pure s
  | none => internal pos s!"{h.name} has no signature"

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

/-- What an expression is checked under: the globals declared so far, the enclosing function, and, inside a
declaration, the numbers of entries and names at its start (§13). -/
structure Ctx where
  globals : List Global
  fn : Option FnCtx := none
  decl : Option (Nat × Nat) := none

def Ctx.global (C : Ctx) (n : String) : Option Global := C.globals.find? (·.name == n)

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

structure Snapshot where
  pos : Pos
  sc : Scope
  given : Option Given
  fn : Option FnCtx
  decl : Option (Nat × Nat)

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

/-- Taint from a tainted scope, and removal of an expression whose results are all tainted (§12). -/
def wrap (o : Out) : Out :=
  let res := if o.sc.taintedBy.isSome then o.res.map ({ · with tainted := true }) else o.res
  { o with res, tree := if res.all (·.tainted) then .removed else o.tree }

/-- Checks results against what the position is given (§8): each entry is instantiated to its result's term. -/
def against (sc : Scope) (g : Given) (pos : Pos) (rs : List Res) : CheckM Unit := do
  if rs.length ≠ g.wants.length then miscount pos g.wants.length s!"produces {rs.length}"
  go [] g.wants rs
where
  go (prev : List Term) : List Want → List Res → CheckM Unit
    | w :: ws, r :: rs => do
      let i := prev.length
      let env := g.env ++ prev
      let what (_ : Unit) := (g.label.map (· i)).getD <| match w.name with
        | some x => code x
        | none => if g.wants.length = 1 then "the value expected here" else s!"value {i + 1}"
      if let some ty := w.type then
        let ty := ty.subst env
        let has ← sc.typeOf pos r.term
        unless identical sc.Γ ty has do
          failAt pos fun _ => s!"{what ()} must have type {sc.disp ty}, and this has type {sc.disp has}"
      if let some e := w.is then
        let e := e.subst env
        unless identical sc.Γ e r.term do
          failAt pos fun _ => s!"{what ()} must be {sc.disp e}, and this is {sc.disp r.term}"
      go (prev ++ [r.term]) ws rs
    | _, _ => pure ()

def produced (sc : Scope) (g : Option Given) (pos : Pos) (rs : List Res) (tree : Expr) : CheckM Out := do
  if let some g := g then against sc g pos rs
  pure ⟨sc, rs, tree, []⟩

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
  def checkTerm (C : Ctx) (sc : Scope) : WTerm → CheckM Res
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
        against sc { wants := [Want.of p], env := prev.map (·.term), label } a.pos [r]
        return r :: (← checkTerms C sc owner role ps (prev ++ [r]) as)
      | [] => internal a.pos "an argument has no parameter"
end

def isType (sc : Scope) (pos : Pos) (t : Term) : CheckM Unit := do
  let ty ← sc.typeOf pos t
  unless identical sc.Γ ty .TYPE do
    failAt pos fun _ => s!"{sc.disp t} is not a type: its type is {sc.disp ty}, not `Type()` (§3)"

/-- A checked annotation (§6): the type, the `is` term if any, and taint. -/
def annotate (C : Ctx) (sc : Scope) : Ann → CheckM (Term × Option Term × Bool)
  | .is t => do
    let r ← checkTerm C sc t
    pure (← sc.typeOf t.pos r.term, some r.term, r.tainted)
  | .type t => do
    let r ← checkTerm C sc t
    isType sc t.pos r.term
    pure (r.term, none, r.tainted)

/-- A binder opened as written (§3): its entry, named, and its type and `is` term as checked. -/
structure Opening where
  sc : Scope
  id : Nat
  type : Term
  is : Option Term
  tainted : Bool

def opening (C : Ctx) (sc : Scope) (name : Id) (ann : Ann) (mult : Option Mult) (kind : String) :
    CheckM Opening := do
  let (type, is, tainted) ← annotate C sc ann
  let o := openTele sc.Γ [⟨name.name, type, is, mult.getD .many⟩] [] fun _ _ en =>
    { en with origin := s!"{kind}@{name.pos}" }
  let id := sc.Γ.length
  pure ⟨Scope.bind { sc with Γ := o.Γ } [name] [⟨.entry id, false, mult == some Mult.erased⟩], id, type, is, tainted⟩

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

/-- The telescope a `match` annotation or `sorry` stands for, and its outer environment (§10, §12). -/
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
  def WTerm.unknownList (untyped : List String) : List WTerm → Option WTerm
    | [] => none
    | a :: as => (a.unknown untyped).orElse fun _ => WTerm.unknownList untyped as
end

def Ann.term : Ann → WTerm
  | .type t | .is t => t

/-- What a tuple `let` gives its right-hand side (§8): its binders as a telescope, an unannotated binder taking
any result. -/
def letWants (C : Ctx) (sc : Scope) (bs : List LetBinder) : CheckM (List Want) := do
  let (sc', opens) ← go sc [] [] bs
  let ids := opens.map fun o => (o.map (·.id)).getD sc'.Γ.length
  (bs.zip opens).mapM fun
    | (b, some o) => do
      let t ← abstracted sc'.Γ b.name.name b.mult b.name.pos o.type o.is ids
      pure (Want.of t)
    | (b, none) => pure ⟨b.name.name, none, none, b.mult.getD .many⟩
where
  go (sc : Scope) (untyped : List String) (acc : List (Option Opening)) :
      List LetBinder → CheckM (Scope × List (Option Opening))
    | [] => pure (sc, acc)
    | b :: bs => match b.ann with
      | some ann => do
        if let some u := ann.term.unknown untyped then
          failAt u.pos fun _ => s!"{code (match u with | .var n | .app n _ => n.name)} has no type here: " ++
            "give it one before referring to it"
        let o ← opening C sc b.name ann b.mult "binder"
        go o.sc untyped (acc ++ [some o]) bs
      | none => go sc ((b.name.name.map ([·])).getD [] ++ untyped) (acc ++ [none]) bs

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

/-- Forces every value constructor of the scrutinee's data type (§7, §10), after checking the patterns. -/
def forcings (C : Ctx) (sc : Scope) (t : Term) (scrutPos : Pos) (pats : List Pattern) (at_ : Pos) :
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
      { en with origin := s!"{n}.{b.name.getD (toString (i + 1))}@{pos}" }
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

def fieldRes (Γ : Entries) (ids : List Nat) : List Res :=
  ids.map fun id => ⟨.entry id, false, ((Γ[id]?).map (·.erased)).getD false⟩

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
  pure (Scope.bind { sc with Γ, taintedBy := reach sc r rhsPos } pat.fields (fieldRes Γ ids))

end Pledge
