import Pledge.Check.Basic

namespace Pledge

structure ArgsOut where
  sc : Scope
  res : List Res
  trees : List Arg
  snaps : List Snapshot

structure ElemsOut where
  sc : Scope
  res : List Res
  trees : List Expr
  snaps : List Snapshot

structure BranchesOut where
  outs : List Out
  trees : List Branch
  snaps : List Snapshot

structure StmtOut where
  sc : Scope
  tree : Stmt
  snaps : List Snapshot

structure StmtsOut where
  sc : Scope
  trees : List Stmt
  snaps : List Snapshot

/-- What an argument is given (§8); a type constructor's argument is erased from phase 2 on (§16). -/
def argGiven (p : TBinder) (prev : List Res) (role owner : String) (erased : Bool) : Given :=
  let i := prev.length
  { wants := [{ Want.of p with mult := if erased then .erased else p.mult }], env := prev.map (·.term),
    label := some fun _ => labelled role p.name i owner }

def elemGiven (g : Option Given) (prev : List Res) : Option Given :=
  g.bind fun g => (g.wants[prev.length]?).map fun w =>
    { wants := [w], env := g.env ++ prev.map (·.term), label := g.label.map fun l _ => l prev.length }

def letGiven (bs : List LetBinder) (wants : List Want) : Given :=
  { wants, whole := bs.all (·.ann.isSome), label := some fun i => labelled "binder" ((bs[i]?).bind (·.name.name)) i }

/-- A `_` argument (§16): a fresh erased entry typed by its parameter, solved later. -/
def holeArg (sc : Scope) (g : Given) (p : TBinder) (prev : List Res) (pos : Pos) : CheckM Out := do
  unless g.erasedAt 0 do failAt pos fun _ =>
    s!"`_` stands for an erased argument (§16), and {(g.label.map (· 0)).getD "this argument"} is not erased"
  let env := prev.map (·.term)
  let is := p.is.map (·.subst env)
  let (sc, id) := sc.addHole (p.type.subst env) is pos
  let sc ← match is with
    | some e => solveHoles sc (.entry id) e pos
    | none => pure sc
  pure ⟨sc, [⟨.entry id, false, true⟩], .removed, []⟩

def isHole : Expr → Bool
  | .var ⟨none, _⟩ => true
  | _ => false

mutual
  /-- Checks an expression against what its position is given, if anything (§8); in an erased position, or
  where every entry given is erased, the expression is wholly erased (§16). -/
  def checkExpr (C : Ctx) (sc : Scope) (g : Option Given) (e : Expr) : CheckM Out :=
    let whole := C.erased || g.any (·.allErased)
    let g := if C.erased then g.map (·.erase) else g
    let C := { C with erased := whole }
    (match e with
    | .var x => match x.name with
      | none => failAt x.pos fun _ => "`_` stands only for a whole argument, for an erased parameter or field (§16)"
      | some n => match sc.lookup n with
        | some r => produced sc g x.pos [{ r with erased := r.erased || sc.erasedEntry r.term }] (.var x)
        | none => notValue C sc ⟨n, x.pos⟩
    | .app h args => match C.global h.name with
      | some (.fn _ sig) => do
        let some sig := sig | failAt h.pos fun _ =>
          s!"{code h.name}'s parameters and returns are still being checked here"
        let fn := C.fn.filter (·.group.contains h.name)
        let plan ← match fn with
          | some fn => some <$> marks h.pos args h.name sig fn
          | none => do
            unmarked args fun _ => match C.fn with
              | some f => s!"{code h.name} is not in {code f.name}'s group"
              | none => "top-level code calls any function unmarked"
            pure none
        arity h.pos h.name sig.params.length args.length
        let a ← checkArgs C sc h.name "parameter" false sig.params [] args
        keep a.snaps do
          if let (some fn, some (subs, k)) := (fn, plan) then decrease a.sc h.pos args a.res fn subs k
          let tainted := sig.tainted || a.res.any (·.tainted)
          let (sc', rs) := opened a.sc sig.returns (a.res.map (·.term)) h.name h.pos fun _ => tainted
          applied sc' g h.pos rs (.app h a.trees) sc.holes.length a.snaps
      | some (.type ..) | some (.ctor _) => do
        let kind := if (C.global h.name) matches some (.type ..) then HeadKind.type else .ctor
        unmarked args fun _ => s!"{code h.name} is not a function"
        let sig ← sc.sig h.pos ⟨kind, h.name⟩
        arity h.pos h.name sig.params.length args.length
        let role := if kind = .type then "parameter" else "field"
        let a ← checkArgs C sc h.name role (kind = .type && C.phase ≥ 2) sig.params [] args
        applied a.sc g h.pos [⟨.app sig.head (a.res.map (·.term)), a.res.any (·.tainted), false⟩] (.app h a.trees)
          sc.holes.length a.snaps
      | _ => notApplied sc h
    | .tuple p es => do
      if let some g := g then
        if g.wants.length ≠ es.length then miscount p g.wants.length s!"tuple has {plural es.length "element"}"
      let o ← checkElems C sc g [] es
      pure ⟨o.sc, o.res, .tuple p o.trees, o.snaps⟩
    | .block ss f => do
      let s ← checkStmts C { sc with holes := [] } ss
      let o ← keep s.snaps (checkExpr C { s.sc with holes := sc.holes } g f)
      pure ⟨{ o.sc with names := sc.names }, o.res, .block s.trees o.tree, s.snaps ++ o.snaps⟩
    | .match p m s ann bs => do
      let erased := m == some .erased
      let place := if erased then C.place else "the scrutinee of a `many` match"
      let so ← checkExpr { C with erased := C.erased || erased, place } sc none s
      keep so.snaps do
        let r ← single s.pos so.res
        let inner := so.sc
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
        let bo ← checkBranches C inner r s.pos fs { wants, env, whole := true, label } bs
        let taint (i : Nat) := r.tainted || bo.outs.any fun o => ((o.res[i]?).map (·.tainted)).getD false
        let (sc', rs) := opened inner tele env "match" p taint
        let trees := (bs.zip bo.trees).filterMap fun (b, t) => if erased && b.body.absurd then none else some t
        let o ← keep bo.snaps (produced sc' g p rs (.match p m so.tree ann trees))
        pure { o with snaps := so.snaps ++ bo.snaps }
    | .sorry p t => do
      let (tele, env) ← annotation C sc g t
      let (sc', rs) := opened sc tele env "sorry" p fun _ => true
      produced sc' g p rs (.sorry p t)
    | .removed => internal 0 "a removed expression was checked") >>= finish C whole g e
  /-- The arguments of a call or application, each checked against its parameter or field (§8); a `_` argument
  is accepted only from phase 2 on (§16). -/
  def checkArgs (C : Ctx) (sc : Scope) (owner role : String) (erased : Bool) (params : Telescope) (prev : List Res) :
      List Arg → CheckM ArgsOut
    | [] => pure ⟨sc, [], [], []⟩
    | .mk m e :: as => match params with
      | p :: ps => do
        let g := argGiven p prev role owner erased
        let o ← if C.phase ≥ 2 && isHole e then holeArg sc g p prev e.pos else checkExpr C sc (some g) e
        let r ← keep o.snaps (single e.pos o.res)
        let rest ← keep o.snaps (checkArgs C o.sc owner role erased ps (prev ++ [r]) as)
        pure ⟨rest.sc, r :: rest.res, .mk m o.tree :: rest.trees, o.snaps ++ rest.snaps⟩
      | [] => internal e.pos "an argument has no parameter"
  def checkElems (C : Ctx) (sc : Scope) (g : Option Given) (prev : List Res) : List Expr → CheckM ElemsOut
    | [] => pure ⟨sc, [], [], []⟩
    | e :: es => do
      let o ← checkExpr C sc (elemGiven g prev) e
      let r ← keep o.snaps (single e.pos o.res)
      let rest ← keep o.snaps (checkElems C o.sc g (prev ++ [r]) es)
      pure ⟨rest.sc, r :: rest.res, o.tree :: rest.trees, o.snaps ++ rest.snaps⟩
  /-- Each branch body, in the scope forcing its value constructor gave, against the annotation (§10). -/
  def checkBranches (C : Ctx) (inner : Scope) (r : Res) (scrutPos : Pos) (fs : List Forcing) (g : Given) :
      List Branch → CheckM BranchesOut
    | [] => pure ⟨[], [], []⟩
    | .mk pat body :: bs => do
      let (Γ, ids) ← survivor inner fs pat.ctor.name pat.ctor.pos ""
      let sc := Scope.bind { inner with Γ, taintedBy := reach inner r scrutPos, holes := [] } pat.fields (fieldRes ids)
      let o ← checkExpr C sc (some g) body
      let rest ← keep o.snaps (checkBranches C inner r scrutPos fs g bs)
      pure ⟨o :: rest.outs, .mk pat o.tree :: rest.trees, o.snaps ++ rest.snaps⟩
  def checkStmts (C : Ctx) (sc : Scope) : List Stmt → CheckM StmtsOut
    | [] => pure ⟨sc, [], []⟩
    | s :: ss => do
      let o ← checkStmt C sc s
      let rest ← keep o.snaps (checkStmts C o.sc ss)
      pure ⟨rest.sc, o.tree :: rest.trees, o.snaps ++ rest.snaps⟩
  /-- A statement (§8, §10); a pattern `let`'s facts stay in the scope after it. -/
  def checkStmt (C : Ctx) (sc : Scope) : Stmt → CheckM StmtOut
    | .inspect p => pure ⟨sc, .inspect p, [⟨p, sc, none, C.fn, C.decl⟩]⟩
    | .let p bs rhs => do
      freshAll C sc (bs.map (·.name))
      let o ← checkExpr C sc (some (letGiven bs (← letWants C sc bs))) rhs
      let rs := (bs.zip o.res).map fun (b, r) => { r with erased := b.mult == some .erased }
      pure ⟨o.sc.bind (bs.map (·.name)) rs, .let p bs o.tree, o.snaps⟩
    | .patlet p ct m pat rhs => do
      let erased := m == some .erased
      if ct && erased then failAt p fun _ =>
        "a `comptime` pattern `let` evaluates its right-hand side (§11), so it cannot be erased (§16)"
      freshAll C sc pat.fields
      let place := if erased then C.place else "the right-hand side of a `many` pattern `let`"
      let o ← checkExpr { C with erased := C.erased || erased, place } sc none rhs
      keep o.snaps do
        let r ← single rhs.pos o.res
        let fs ← forcings C o.sc r.term rhs.pos [pat] p erased
        pure ⟨← patBind o.sc r rhs.pos ct pat fs, .patlet p ct m pat o.tree, o.snaps⟩
end

end Pledge
