import Pledge.Check.Top

namespace Pledge

mutual
  def Expr.holes : Expr → List Pos
    | .var ⟨none, p⟩ => [p]
    | .var _ | .removed => []
    | .app _ args => Arg.holesList args
    | .tuple _ es => Expr.holesList es
    | .block ss f => Stmt.holesList ss ++ f.holes
    | .match _ _ s ann bs => s.holes ++ Tele.holesOf ann ++ Branch.holesList bs
    | .sorry _ t => Tele.holesOf t
  def Expr.holesList : List Expr → List Pos
    | [] => []
    | e :: es => e.holes ++ Expr.holesList es
  def Arg.holesList : List Arg → List Pos
    | [] => []
    | .mk _ e :: as => e.holes ++ Arg.holesList as
  def Stmt.holesList : List Stmt → List Pos
    | [] => []
    | .let _ bs rhs :: ss => bs.flatMap (·.ann.elim [] (·.term.holes)) ++ rhs.holes ++ Stmt.holesList ss
    | .patlet _ _ _ _ rhs :: ss => rhs.holes ++ Stmt.holesList ss
    | .inspect _ :: ss => Stmt.holesList ss
  def Branch.holesList : List Branch → List Pos
    | [] => []
    | .mk _ body :: bs => body.holes ++ Branch.holesList bs
  def Tele.holesOf : Tele → List Pos
    | .binders bs => bs.flatMap (·.ann.term.holes)
    | .hole _ => []
end

def Header.holes (h : Header) : List Pos :=
  (h.params.map (·.binder) ++ h.returns).flatMap (·.ann.term.holes)

def Data.holes (d : Data) : List Pos :=
  d.params.flatMap (·.ann.term.holes) ++ d.ctors.flatMap fun k => k.fields.flatMap (·.ann.term.holes) ++ k.ret.holes

/-- The positions of the `_` of an item that stand for an argument or a term (§20). -/
def Top.holes : Top → List Pos
  | .data d => d.holes
  | .mutualData _ ds => ds.flatMap Data.holes
  | .fn f => f.header.holes ++ f.body.holes
  | .mutualFn _ fs => fs.flatMap fun f => f.header.holes ++ f.body.holes
  | .stmt s => Stmt.holesList [s]
  | .print _ e | .qed _ e => e.holes
  | .goal _ (.type t) => t.holes
  | .goal _ (.fn h) => h.holes

/-- The number of `_` of the program the table has no terms for. -/
def unsolved (prog : Program) (table : Table) : Nat :=
  ((prog.flatMap Top.holes).filter fun p => (table.lookup p).isNone).length

namespace Solve

/-- A `_` being solved (§20): its entry, where it is written, and its parameter's `is` term; a `late` one, in a tuple
`let` binder's annotation, may be solved to what the right-hand side produces, and a placeholder (`binder`) stands
for the result a tuple `let` binder names. -/
structure Hole where
  id : Nat
  pos : Pos
  is : Option Term
  late : Bool := false
  first : Option Term := none
  binder : Option Nat := none

/-- A scope while solving: its entries include one per `_` being solved, and `holes` lists those created since the
nearest boundary (§20). -/
structure Sc extends Scope where
  holes : List Hole := []

instance : Coe Sc Scope := ⟨Sc.toScope⟩

/-- Where solving an item stops: at a boundary, with the terms found for its `_`, or at an error. -/
inductive Stop where
  | solved (table : Table)
  | failed (e : CheckError)

abbrev SolveM := Except Stop

instance : MonadLift CheckM SolveM := ⟨Except.mapError .failed⟩

/-- An entry the checking pass also has: not that of a `_` or of a placeholder. -/
def real (en : Entry) : Bool := !en.origin.startsWith "_@" && !en.origin.startsWith "let@"

def Sc.addHole (sc : Sc) (type : Term) (is : Option Term) (pos : Pos) (erased : Bool) : Sc × Nat :=
  ({ sc with Γ := sc.Γ ++ [{ type, origin := s!"_@{pos}", erased }],
             holes := sc.holes ++ [{ id := sc.Γ.length, pos, is }] }, sc.Γ.length)

/-- Solves `lhs = rhs` for `_` (§16), only `hole` entries taking rules. Returns the scope with
the rules found and, on a failure, the two terms that could not be equated. -/
def unify (S : Sigs) (Γ : Entries) (lhs rhs : Term) (hole : Nat → Bool) :
    Except String (Entries × Option (Term × Term)) :=
  match solve S hole Γ [] [⟨lhs.canon Γ, rhs.canon Γ, .given⟩] with
  | .ok Γ' _ => .ok (Γ', none)
  | .failed ⟨Γ', _, .rigid a b, _⟩ => .ok (Γ', some (a, b))
  | .failed ⟨Γ', _, .occurs x e, _⟩ => .ok (Γ', some (.entry x, e))
  | .failed ⟨Γ', q, .heads .., _⟩ => .ok (Γ', some (q.lhs, q.rhs))
  | .stuck msg => .error msg

/-- Solves the `_` being solved from an equation, only their entries taking rules; nothing when there are none. -/
def solveHoles (sc : Sc) (lhs rhs : Term) (pos : Pos) : CheckM Sc :=
  match sc.holes with
  | [] => pure sc
  | holes =>
    match unify sc.sigs sc.Γ lhs rhs (fun i => holes.any (·.id == i)) with
    | .error msg => internal pos msg
    | .ok (Γ, stuck) =>
      let first (h : Hole) := { h with first := h.first.orElse fun _ => (Γ[h.id]?).bind (·.rule) }
      let now : Sc := { sc with Γ, holes := holes.map first }
      match stuck.bind fun (a, b) => (holes.find? fun h => a.occurs h.id || b.occurs h.id).map (a, b, ·) with
      | some (a, b, h) => failAt h.pos fun _ =>
        s!"this `_` cannot be inferred: it would need {now.disp a} and {now.disp b} to be equal, " ++
        "and this checker solves a `_` only by giving rules to entries of `_`"
      | none => pure now

/-- `against`, solving the `_` being solved from each entry's equations before checking it. -/
def Sc.against (sc : Sc) (g : Given) (pos : Pos) (rs : List Res) : CheckM Sc := do
  if rs.length ≠ g.wants.length then miscount pos g.wants.length s!"produces {rs.length}"
  go sc [] g.wants rs
where
  go (sc : Sc) (prev : List Term) : List Want → List Res → CheckM Sc
    | w :: ws, r :: rs => do
      let env := g.env ++ prev
      let has ← sc.typeOf pos r.term
      let sc ← match w.type with
        | some ty => solveHoles sc (ty.subst env) has pos
        | none => pure sc
      let sc ← match w.is with
        | some e => solveHoles sc (e.subst env) r.term pos
        | none => pure sc
      g.meets sc pos prev.length w env r has
      go sc (prev ++ [r.term]) ws rs
    | _, _ => pure sc

def Sc.produced (sc : Sc) (g : Option Given) (pos : Pos) (rs : List Res) : CheckM (Sc × List Res) := do
  match g with
  | some g => pure (← sc.against g pos rs, rs)
  | none => pure (sc, rs)

mutual
  def untaintedAs (Γ : Entries) (ok : Nat → Bool) (c : Term) : Term :=
    let same (x : Nat) := ok x && (Γ[x]?).any (!·.tainted) && (Term.entry x).canon Γ == c
    match (List.range Γ.length).find? same, c with
    | some x, _ => .entry x
    | none, .app h as => .app h (untaintedAsList Γ ok as)
    | none, c => c
  def untaintedAsList (Γ : Entries) (ok : Nat → Bool) : List Term → List Term
    | [] => []
    | a :: as => untaintedAs Γ ok a :: untaintedAsList Γ ok as
end

/-- The terms offered for a `_`: one built from untainted entries wherever canonicalization allows (§20), the term
unification first gave it, and its canonical form. -/
def candidates (Γ : Entries) (ok : Nat → Bool) (first : Option Term) (canonical : Term) : List Term :=
  (untaintedAs Γ ok canonical :: first.toList ++ [canonical]).eraseDups

/-- Checks a `_` at its boundary: its term mentions no unsolved `_` and only entries before it, has its type and meets
its parameter's `is` term; gives the terms to try, numbering only the real entries. -/
def settle (sc : Scope) (h : Hole) : CheckM (Pos × List Term) := do
  let some en := sc.Γ[h.id]? | internal h.pos "a `_` has no entry"
  let isReal (x : Nat) := (sc.Γ[x]?).any real
  let canonical := (Term.entry h.id).canon sc.Γ
  let first := h.first.map (·.mapEntries fun x => if isReal x then .entry x else (Term.entry x).canon sc.Γ)
  let wrong (value : Term) : Option (Unit → String) :=
    if !value.entries.all isReal then some cannotInfer
    else if !h.late && value.entries.any (· > h.id) then some fun _ =>
      s!"this `_` would be {sc.disp value}, which mentions what is produced only after it, " ++
      "such as a result of the call it is an argument of, and a `_` is solved only to what exists before it"
    else match typeOf sc.sigs sc.Γ value with
      | none => some fun _ => s!"this `_` would be {sc.disp value}, which has no type"
      | some has =>
        if !identical sc.Γ en.type has then some fun _ =>
          s!"this `_` would be {sc.disp value}, of type {sc.disp has}, and it must have type {sc.disp en.type}"
        else if h.is.any (!identical sc.Γ · value) then some fun _ =>
          s!"this `_` must be {sc.disp ((h.is.map (·.canon sc.Γ)).getD value)}, and it would be {sc.disp value}"
        else none
  let renumber (t : Term) := t.mapEntries fun x => .entry ((sc.Γ.take x).countP real)
  let ok (x : Nat) := isReal x && (h.late || x < h.id)
  match (candidates sc.Γ ok first canonical).filter fun t => (wrong t).isNone with
  | [] => failAt h.pos ((wrong canonical).getD fun _ => "")
  | ts => pure (h.pos, ts.map renumber)

/-- Equates each placeholder with the result its binder names. -/
def identify (sc : Sc) (rs : List Res) (holes : List Hole) : CheckM Sc :=
  holes.foldlM (init := sc) fun sc h => match h.binder.bind (rs[·]?) with
    | some r => solveHoles sc (.entry h.id) r.term h.pos
    | none => pure sc

/-- A boundary (§20): when a `_` was created since `since`, solving stops with its terms. -/
def close (o : Sc × List Res) (since : Nat) : SolveM Unit :=
  match o.1.holes.drop since with
  | [] => pure ()
  | mine => do
    let sc ← identify o.1 o.2 mine
    throw (.solved (← ((mine.filter (·.binder.isNone)).mapM (settle sc) : CheckM _)))

/-- Checks with no `_` being solved, then closes the boundary, the enclosing `_` being solved again after. -/
def closed (sc : Sc) (check : Sc → SolveM (Sc × List Res)) : SolveM (Sc × List Res) := do
  let o ← check { sc with holes := [] }
  close o 0
  pure ({ o.1 with holes := sc.holes }, o.2)

/-- The table's terms number only real entries (`settle`), so each number is read as the real entry it counts. -/
def fromTable (sc : Scope) (ts : List Term) : List Term :=
  let reals := (List.range sc.Γ.length).filter fun i => (sc.Γ[i]?).any real
  ts.map (·.mapEntries fun k => .entry (reals.getD k (sc.Γ.length + k)))

/-- A `_`: the table's term, or a fresh entry to solve. -/
def Sc.hole (C : Ctx) (sc : Sc) (pos : Pos) (type : Term) (is : Option Term) (erased : Bool) :
    CheckM (Sc × List Res) :=
  match C.table.lookup pos with
  | some ts => do pure (sc, [← sc.solution C (fromTable sc ts) pos type is erased])
  | none => do
    let (sc, id) := sc.addHole type is pos erased
    let sc ← match is with
      | some e => solveHoles sc (.entry id) e pos
      | none => pure sc
    pure (sc, [⟨.entry id, false, erased⟩])

def holeArg (C : Ctx) (sc : Sc) (g : Given) (p : TBinder) (prev : List Res) (pos : Pos) : CheckM (Sc × List Res) := do
  let (type, is, erased) ← holeType C sc g p prev pos
  sc.hole C pos type is erased

mutual
  /-- A skeleton term with `_`, checked as an expression in a position that is not evaluated. -/
  def skel (C : Ctx) (sc : Sc) (g : Option Given) : WTerm → CheckM (Sc × List Res)
    | .hole p => failAt p fun _ => "`_` stands only for a whole argument or inside a type (§16)"
    | .var x => match sc.lookup x.name with
      | some r => sc.produced g x.pos [{ r with tainted := r.tainted || sc.taintedBy.isSome }]
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
      let (sc', rs) ← skels { C with inType := C.inType || kind == .type } sc h.name role
        (kind = .type && C.phase ≥ 2) sig.params [] args
      sc'.produced g h.pos [⟨.app sig.head (rs.map (·.term)), rs.any (·.tainted) || sc.taintedBy.isSome, false⟩]
  def skels (C : Ctx) (sc : Sc) (owner role : String) (erased : Bool) (params : Telescope) (prev : List Res) :
      List WTerm → CheckM (Sc × List Res)
    | [] => pure (sc, [])
    | a :: as => match params with
      | p :: ps => do
        let g := argGiven p prev role owner erased
        let (sc, rs) ← match a with
          | .hole pos => holeArg C sc g p prev pos
          | a => skel C sc (some g) a
        let r ← single a.pos rs
        let (sc, rs) ← skels C sc owner role erased ps (prev ++ [r]) as
        pure (sc, r :: rs)
      | [] => internal a.pos "an argument has no parameter"
end

/-- A written term with `_`, in a position that is erased from phase 2 on; its `_` stay being solved. -/
def written (C : Ctx) (sc : Sc) (whole : Bool) (t : WTerm) : CheckM (Sc × List Res) :=
  let C := { C with erased := C.erased || C.phase ≥ 2 }
  match t, whole with
  | .hole p, true => sc.hole C p .TYPE none C.erased
  | t, _ => skel C sc none t

/-- A written term with `_` is a boundary of its own (§20). -/
def term (C : Ctx) (sc : Scope) (t : WTerm) (whole : Bool) : SolveM Res :=
  if t.holed then do
    let o ← written C { toScope := sc } whole t
    close o 0
    single t.pos o.2
  else Pledge.term C sc t whole

def annotate (C : Ctx) (sc : Scope) : Ann → SolveM (Term × Option Term × Bool)
  | .is t => do
    let r ← term C sc t false
    pure (← sc.typeOf t.pos r.term, some r.term, r.tainted)
  | .type t => do
    let r ← term C sc t true
    isType sc t.pos r.term
    pure (r.term, none, r.tainted)

def opening (C : Ctx) (sc : Scope) (name : Id) (ann : Ann) (mult : Option Mult) (kind : String) : SolveM Opening := do
  let (type, is, tainted) ← annotate C sc ann
  pure (sc.openBinder name type is mult kind tainted)

def telescope (C : Ctx) (sc : Scope) (bs : List Binder) (kind : String) (outer : List Nat := []) :
    SolveM Checked := do
  let (sc', opens) ← go sc [] [] bs
  let ids := opens.map (·.2.id)
  let tele ← (bs.zip opens).mapM fun (b, _, o) =>
    abstracted sc'.Γ b.name.name b.mult b.name.pos o.type o.is (outer ++ ids)
  pure ⟨sc', ids, tele, opens.any (·.2.tainted)⟩
where
  go (sc : Scope) (seen : List String) (acc : List (Binder × Opening)) :
      List Binder → SolveM (Scope × List (Binder × Opening))
    | [] => pure (sc, acc)
    | b :: bs => do
      let seen ← fresh C sc seen b.name.name b.name.pos
      let o ← opening C sc b.name b.ann b.mult kind
      go o.sc seen (acc ++ [(b, o)]) bs

def header (C : Ctx) (sc : Scope) (h : Header) : SolveM (Checked × Checked) := do
  let ps ← telescope C sc (h.params.map (·.binder)) "param"
  pure (ps, ← telescope C ps.sc h.returns "binder" ps.ids)

def annotation (C : Ctx) (sc : Scope) (g : Option Given) : Tele → SolveM (Telescope × List Term)
  | .binders bs => do pure ((← telescope C sc bs "binder").tele, [])
  | t => Pledge.annotation C sc g t

/-- An annotation of a tuple `let` binder, its `_` left being solved. -/
def annotateOpen (C : Ctx) (sc : Sc) (ann : Ann) : CheckM (Sc × Term × Option Term) := do
  let (sc, rs) ← written C sc (ann matches .type _) ann.term
  let r ← single ann.term.pos rs
  match ann with
  | .is t => pure (sc, ← sc.typeOf t.pos r.term, some r.term)
  | .type t => do isType sc t.pos r.term; pure (sc, r.term, none)

/-- What a tuple `let` gives its right-hand side while solving. When an annotation has `_`, every annotation is
checked with its `_` left being solved, `late`, and the scope the right-hand side is checked in keeps the binders'
entries, placeholders, and the `_`, without the binders' names; a binder's type or `is` term is abstracted only over
the binders before it, so a `_` may take a later binder's placeholder. -/
def letWants (C : Ctx) (sc : Sc) (bs : List LetBinder) : SolveM (List Want × Sc) := do
  let holed := holedLet bs
  let (sc', opens) ← go holed sc [] [] bs
  let ids := opens.map fun o => (o.map (·.id)).getD sc'.Γ.length
  let ws ← (if holed then (bs.zip opens).zipIdx.mapM fun (p, i) => letWant sc'.Γ (ids.take i) p
    else (bs.zip opens).mapM (letWant sc'.Γ ids) : CheckM _)
  let placeholders := (opens.zipIdx.zip bs).filterMap fun ((o, i), b) =>
    o.map fun o => ({ id := o.id, pos := b.name.pos, is := none, binder := some i } : Hole)
  let late := sc.holes ++ (sc'.holes.drop sc.holes.length).map ({ · with late := true }) ++ placeholders
  pure (ws, if holed then { sc' with names := sc.names, holes := late } else sc)
where
  go (holed : Bool) (sc : Sc) (untyped : List String) (acc : List (Option Opening)) :
      List LetBinder → SolveM (Sc × List (Option Opening))
    | [] => pure (sc, acc)
    | b :: bs => match b.ann with
      | some ann => do
        typedBefore untyped ann
        let (sc, o) ← if holed then do
            let (sc, type, is) ← annotateOpen { C with table := [] } sc ann
            pure (sc, sc.openBinder b.name type is b.mult "let" false)
          else do pure (sc, ← opening C sc b.name ann b.mult "binder")
        go holed { sc with toScope := o.sc } untyped (acc ++ [some o]) bs
      | none => go holed sc ((b.name.name.map ([·])).getD [] ++ untyped) (acc ++ [none]) bs

def letBinders (C : Ctx) (sc : Scope) (pos : Pos) (bs : List LetBinder) (rs : List Res) : SolveM Unit :=
  go sc [] 0 (bs.zip rs)
where
  go (sc : Scope) (untyped : List String) (i : Nat) : List (LetBinder × Res) → SolveM Unit
    | [] => pure ()
    | (b, r) :: rest => do
      let r := { r with erased := b.mult == some .erased }
      let untyped ← match b.ann with
        | some ann => do
          typedBefore untyped ann
          let (type, is, _) ← annotate C sc ann
          let want : Want := ⟨b.name.name, some type, is, b.mult.getD .many⟩
          against sc { wants := [want], label := some fun _ => labelled "binder" b.name.name i } pos [r]
          pure untyped
        | none => pure ((b.name.name.map ([·])).getD [] ++ untyped)
      go (sc.bind [b.name] [r]) untyped (i + 1) rest

def finished (C : Ctx) (whole : Bool) (g : Option Given) (e : Expr) (o : Sc × List Res) : CheckM (Sc × List Res) := do
  pure (o.1, (← finish C whole g e ⟨o.1, o.2, .removed, []⟩).res)

mutual
  /-- `checkExpr` while solving: the `_` of a call are solved at its end, and the scrutinee, a branch body and a
  pattern `let`'s right-hand side are boundaries (§20). -/
  def expr (C : Ctx) (sc : Sc) (g : Option Given) (e : Expr) : SolveM (Sc × List Res) :=
    let whole := C.erased || g.any (·.allErased)
    let g := if C.erased then g.map (·.erase) else g
    let C := C.enter whole
    (match e with
    | .var x => match x.name with
      | none => failAt x.pos fun _ => "`_` stands only for a whole argument or inside a type (§16)"
      | some n => match sc.lookup n with
        | some r => sc.produced g x.pos
          [{ r with erased := sc.sigs.restricted sc.Γ C.phase (r.erased || sc.erasedEntry r.term) r.term }]
        | none => notValue C sc ⟨n, x.pos⟩
    | .app h args => match C.global h.name with
      | some (.fn _ sig) => do
        let some sig := sig | failAt h.pos fun _ =>
          s!"{code h.name}'s parameters and returns are still being checked here"
        let fn := C.fn.filter (·.group.contains h.name)
        let plan ← match fn with
          | some fn => some <$> (marks h.pos args h.name sig fn : CheckM _)
          | none => do
            unmarked args fun _ => match C.fn with
              | some f => s!"{code h.name} is not in {code f.name}'s group"
              | none => "top-level code calls any function unmarked"
            pure none
        arity h.pos h.name sig.params.length args.length
        let (sc', rs) ← exprArgs C sc h.name "parameter" false sig.params [] args
        if let (some fn, some (subs, k)) := (fn, plan) then decrease sc' h.pos args rs fn subs k
        let tainted := sig.tainted || rs.any (·.tainted)
        let (sc'', rs') := opened sc' sig.returns (rs.map (·.term)) h.name h.pos fun _ => tainted
        let o ← ({ sc' with toScope := sc'' } : Sc).produced g h.pos rs'
        close o sc.holes.length
        pure o
      | some (.type ..) | some (.ctor _) => do
        let kind := if (C.global h.name) matches some (.type ..) then HeadKind.type else .ctor
        unmarked args fun _ => s!"{code h.name} is not a function"
        let sig ← sc.sig h.pos ⟨kind, h.name⟩
        arity h.pos h.name sig.params.length args.length
        let role := if kind = .type then "parameter" else "field"
        let (sc', rs) ← exprArgs { C with inType := C.inType || kind == .type } sc h.name role
          (kind = .type && C.phase ≥ 2) sig.params [] args
        sc'.produced g h.pos [⟨.app sig.head (rs.map (·.term)), rs.any (·.tainted), false⟩]
      | _ => notApplied sc h
    | .tuple p es => do
      if let some g := g then
        if g.wants.length ≠ es.length then miscount p g.wants.length s!"tuple has {plural es.length "element"}"
      exprElems C sc g [] es
    | .block ss f => do
      let s ← stmts C { sc with holes := [] } ss
      let (sc', rs) ← expr C { s with holes := sc.holes } g f
      pure ({ sc' with names := sc.names }, rs)
    | .match p m s ann bs => do
      let erased := m == some .erased
      let place := if erased then C.place else "the scrutinee of a `many` match"
      let (inner, srs) ← closed sc (expr { C with erased := C.erased || erased, place } · none s)
      let r ← single s.pos srs
      let (tele, env) ← annotation C inner g ann
      let fs ← forcings C inner r.term s.pos (bs.map Branch.pat) p erased
      bs.forM fun b => do
        let _ ← survivor inner fs b.pat.ctor.name b.pat.ctor.pos "the match has no branch for it"
        freshAll C inner b.pat.fields
      let missing := (fs.filter fun f => f.pat.isNone && f.forced matches .ok ..).map (·.name)
      unless missing.isEmpty do
        failAt p fun _ => s!"no branch for {", ".intercalate (missing.map code)}, " ++
          s!"which {if missing.length = 1 then "is" else "are"} not refuted here (§10)"
      let live := bs.filter fun b => !(erased && b.body.absurd)
      if let some second := live[1]? then
        if erased && tele.any (·.mult == .many) then failAt second.pat.ctor.pos fun _ =>
          "an erased match with a `many` annotation entry has at most one branch that is not absurd, " ++
          "a branch being absurd when its body is a match with no branches, possibly the final expression of a " ++
          "block, since evaluation has no value to choose a branch by (§16)"
      let wants := tele.mapIdx fun i b => { Want.of b with mult := if g.any (·.erasedAt i) then .erased else b.mult }
      let label := match ann with
        | .binders _ => some fun i => labelled "annotation entry" ((tele[i]?).bind (·.name)) i
        | .hole _ => g.bind (·.label)
      ensure (tele.all (·.entriesBelow inner.Γ.length) && env.all (·.entriesBelow inner.Γ.length)) p
        "an annotation mentions an entry created after the scrutinee"
      let outs ← branches C inner r s.pos fs { wants, env, whole := true, label } bs
      let taint (i : Nat) := r.tainted || outs.any fun o => ((o.2[i]?).map (·.tainted)).getD false
      let (sc', rs) := opened inner tele env "match" p taint
      ({ inner with toScope := sc' } : Sc).produced g p rs
    | .sorry p t => do
      let (tele, env) ← annotation C sc g t
      let (sc', rs) := opened sc tele env "sorry" p fun _ => true
      ({ sc with toScope := sc' } : Sc).produced g p rs
    | .removed => internal 0 "a removed expression was checked") >>= fun o => finished C whole g e o
  def exprArgs (C : Ctx) (sc : Sc) (owner role : String) (erased : Bool) (params : Telescope) (prev : List Res) :
      List Arg → SolveM (Sc × List Res)
    | [] => pure (sc, [])
    | .mk _ e :: as => match params with
      | p :: ps => do
        let g := argGiven p prev role owner erased
        let (sc, rs) ← if isHole e then (holeArg C sc g p prev e.pos : SolveM _) else expr C sc (some g) e
        let r ← single e.pos rs
        let (sc, rs) ← exprArgs C sc owner role erased ps (prev ++ [r]) as
        pure (sc, r :: rs)
      | [] => internal e.pos "an argument has no parameter"
  def exprElems (C : Ctx) (sc : Sc) (g : Option Given) (prev : List Res) : List Expr → SolveM (Sc × List Res)
    | [] => pure (sc, [])
    | e :: es => do
      let (sc, rs) ← expr C sc (elemGiven g prev) e
      let r ← single e.pos rs
      let (sc, rs) ← exprElems C sc g (prev ++ [r]) es
      pure (sc, r :: rs)
  def branches (C : Ctx) (inner : Sc) (r : Res) (scrutPos : Pos) (fs : List Forcing) (g : Given) :
      List Branch → SolveM (List (Sc × List Res))
    | [] => pure []
    | .mk pat body :: bs => do
      let (Γ, ids) ← survivor inner fs pat.ctor.name pat.ctor.pos ""
      let sc := Scope.bind { inner.toScope with Γ, taintedBy := reach inner r scrutPos } pat.fields (fieldRes ids)
      let o ← closed { toScope := sc } (expr C · (some g) body)
      pure (o :: (← branches C inner r scrutPos fs g bs))
  def stmts (C : Ctx) (sc : Sc) : List Stmt → SolveM Sc
    | [] => pure sc
    | s :: ss => do stmts C (← stmt C sc s) ss
  def stmt (C : Ctx) (sc : Sc) : Stmt → SolveM Sc
    | .inspect _ => pure sc
    | .let _ bs rhs => do
      freshAll C sc (bs.map (·.name))
      let missing := bs.any (·.ann.any fun a => a.term.holes.any (C.table.lookup · |>.isNone))
      let (sc', rs) ← if holedLet bs && !missing then do
          let o ← expr C sc (some (anyGiven bs)) rhs
          close o 0
          letBinders C o.1 rhs.pos bs o.2
          pure o
        else do
          let (ws, sc') ← letWants C sc bs
          let o ← expr C sc' (some (letGiven bs ws)) rhs
          close o 0
          pure o
      let rs := (bs.zip rs).map fun (b, r) => { r with erased := b.mult == some .erased }
      pure { sc' with toScope := sc'.bind (bs.map (·.name)) rs }
    | .patlet p ct m pat rhs => do
      let erased := m == some .erased
      if ct && erased then failAt p fun _ =>
        "a `comptime` pattern `let` evaluates its right-hand side (§11), so it cannot be erased (§16)"
      ensure (!ct) p "a `comptime` pattern `let` below the top level"
      freshAll C sc pat.fields
      let place := if erased then C.place else "the right-hand side of a `many` pattern `let`"
      let (sc', rs) ← closed sc (expr { C with erased := C.erased || erased, place } · none rhs)
      let r ← single rhs.pos rs
      let fs ← forcings C sc' r.term rhs.pos [pat] p erased
      let sc'' ← patBind sc' r rhs.pos ct pat fs
      pure { sc' with toScope := sc'' }
end

/-- An expression checked at the top level, a boundary of its own (§20). -/
def topExpr (C : Ctx) (sc : Scope) (g : Option Given) (e : Expr) : SolveM (Sc × List Res) :=
  closed { toScope := sc } (expr C · g e)

def declType (st : TopState) (d : Data) : SolveM TopState := do
  let C := st.ctx true
  let _ ← fresh C st.sc [] d.name.name d.name.pos
  ensure (d.name.name != junkHead.name) d.name.pos "a type constructor is named `sorry`"
  let ps ← telescope C st.sc d.params "binder"
  topLevel st d.name.pos ps.tele
  pure (addSig st ⟨⟨.type, d.name.name⟩, ps.tele, .TYPE⟩ (.type d.name.name (some []) false))

def declCtor (owner : String) (st : TopState) (k : Ctor) : SolveM TopState := do
  let C := st.ctx true
  let _ ← fresh C st.sc [] k.name.name k.name.pos
  ensure (k.name.name != junkHead.name) k.name.pos "a value constructor is named `sorry`"
  let fs ← telescope C st.sc k.fields "binder"
  unless (match k.ret with | .app h _ => h.name == owner | _ => false) do
    failAt k.ret.pos fun _ =>
      s!"{code k.name.name} returns {code owner} applied to one argument per parameter of {code owner} (§5)"
  let r ← term C fs.sc k.ret false
  let ret ← abstractChecked fs.sc.Γ r.term fs.ids k.ret.pos
  topLevel st k.name.pos fs.tele
  ensure (ret.entriesBelow st.sc.Γ.length && ret.boundsBelow fs.tele.length &&
      match ret with | .app h _ => h == ⟨.type, owner⟩ | _ => false) k.ret.pos
    "a value constructor's return mentions an entry below the top level or a missing field, or does not apply its type"
  let st := addSig st ⟨⟨.ctor, k.name.name⟩, fs.tele, ret⟩ (.ctor k.name.name)
  pure { st with globals := st.globals.map fun
    | .type n (some cs) d => .type n (some (if n == owner then cs ++ [k.name.name] else cs)) d
    | g => g }

def dataGroup (st : TopState) (ds : List Data) : SolveM Unit := do
  let st ← ds.foldlM declType st
  discard <| ds.foldlM (fun st d => d.ctors.foldlM (declCtor d.name.name) st) st

def fnHead (names : List String) (st : TopState) (f : Fn) : SolveM (TopState × FnHead) := do
  let flags := f.header.params.map (·.subterm)
  let subtermNames := (f.header.params.filter (·.subterm)).map fun p => p.binder.name.name.getD "_"
  let fn : FnCtx := ⟨f.name.name, names, [], subtermNames⟩
  let (ps, rs) ← header { st.ctx true with fn := some fn } st.sc f.header
  topLevel st f.name.pos (ps.tele ++ rs.tele)
  let subterms := ((ps.ids.zip flags).filter (·.2)).map fun (i, _) => Term.entry i
  let sig : FnSig := ⟨ps.tele, rs.tele, flags, false⟩
  let st := { st with globals := st.globals.map fun g => if g.name == f.name.name then .fn g.name (some sig) else g }
  pure (st, ⟨f, { fn with subterms }, sig, ps.sc, ps.ids.map .entry⟩)

/-- A group of functions, its bodies checked with every function untainted: taint (§12) decides no `_`. -/
def fnGroup (st : TopState) (fs : List Fn) : SolveM Unit := do
  let names := fs.map (·.name.name)
  let st0 ← fs.foldlM (fun st f => do
    let _ ← fresh (st.ctx true) st.sc [] f.name.name f.name.pos
    pure { st with globals := st.globals ++ [.fn f.name.name none] }) st
  let (st1, heads) ← fs.foldlM (fun (st, hs) f => do
    let (st, h) ← fnHead names st f
    pure (st, hs ++ [h])) (st0, [])
  let C := { st.ctx true with globals := setSigs st1.globals heads (heads.map fun _ => false) }
  heads.forM fun h => discard <| topExpr { C with fn := some h.fn } h.sc (some (returnsGiven h)) h.f.body

/-- Solves an item (§20) from the top-level state before it, as `topItem` checks it, evaluating nothing. -/
def item (st : TopState) : Top → SolveM Unit
  | .data d => dataGroup st [d]
  | .mutualData _ ds => dataGroup st ds
  | .fn f => fnGroup st [f]
  | .mutualFn _ fs => fnGroup st fs
  | .stmt (.patlet p true m pat rhs) => do
    if m == some .erased then failAt p fun _ =>
      "a `comptime` pattern `let` evaluates its right-hand side (§11), so it cannot be erased (§16)"
    freshAll st.ctx st.sc pat.fields
    let (sc, rs) ← topExpr st.ctx st.sc none rhs
    let r ← single rhs.pos rs
    let fs ← forcings st.ctx sc r.term rhs.pos [pat] p false
    discard <| patBind sc r rhs.pos true pat fs
  | .stmt s => discard <| stmt st.ctx { toScope := st.sc } s
  | .print _ e => do discard <| single e.pos (← topExpr { st.ctx with place := printPlace } st.sc none e).2
  | .goal p g => do
    if st.goal.isSome then failAt p fun _ => "a program has at most one `goal` (§12)"
    match g with
    | .fn h => do
      let (ps, rs) ← header (st.ctx true) st.sc h
      topLevel st p (ps.tele ++ rs.tele)
    | .type t => do
      let (ty, _, _) ← annotate st.ctx st.sc (.type t)
      ensure (ty.entriesBelow st.sc.Γ.length) t.pos "a goal mentions an entry below the top level"
  | .qed p e => do
    if st.qedChecks then failAt p fun _ => "a program has at most one `qed` (§12)"
    let some goal := st.goal | failAt p fun _ =>
      "`qed` comes after `goal`, and no `goal` is set before this `qed` (§12)"
    match goal.kind with
    | .fn ps rs => discard <| (qedFnGoal st ps rs e : CheckM _)
    | .type _ => do
      if let .var ⟨some n, _⟩ := e then
        if let some (.fn ..) := st.ctx.global n then failAt e.pos fun _ =>
          s!"{code n} is a function, and naming a function proves only a function goal, " ++
          "`goal fn (...) -> (...);`; this goal is a type"
      discard <| topExpr st.ctx st.sc (some goal.given) e

end Solve

end Pledge
