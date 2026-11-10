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

def argGiven (p : TBinder) (prev : List Res) (role owner : String) : Given :=
  let i := prev.length
  { wants := [Want.of p], env := prev.map (·.term), label := some fun _ => labelled role p.name i owner }

def elemGiven (g : Option Given) (prev : List Res) : Option Given :=
  g.bind fun g => (g.wants[prev.length]?).map fun w =>
    { wants := [w], env := g.env ++ prev.map (·.term), label := g.label.map fun l _ => l prev.length }

def letGiven (bs : List LetBinder) (wants : List Want) : Given :=
  { wants, whole := bs.all (·.ann.isSome), label := some fun i => labelled "binder" ((bs[i]?).bind (·.name.name)) i }

mutual
  /-- Checks an expression against what its position is given, if anything (§8). -/
  def checkExpr (C : Ctx) (sc : Scope) (g : Option Given) : Expr → CheckM Out
    | .var x => wrap <$> match x.name with
      | none => failAt x.pos fun _ => "`_` stands only for a whole argument, for an erased parameter or field (§16)"
      | some n => match sc.lookup n with
        | some r => produced sc g x.pos [r] (.var x)
        | none => notValue C sc ⟨n, x.pos⟩
    | .app h args => wrap <$> match C.global h.name with
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
        let a ← checkArgs C sc h.name "parameter" sig.params [] args
        if let (some fn, some (subs, k)) := (fn, plan) then decrease a.sc h.pos args a.res fn subs k
        let tainted := sig.tainted || a.res.any (·.tainted)
        let (sc', rs) := opened a.sc sig.returns (a.res.map (·.term)) h.name h.pos fun _ => tainted
        let o ← produced sc' g h.pos rs (.app h a.trees)
        pure { o with snaps := a.snaps }
      | some (.type ..) | some (.ctor _) => do
        let kind := if (C.global h.name) matches some (.type ..) then HeadKind.type else .ctor
        unmarked args fun _ => s!"{code h.name} is not a function"
        let sig ← sc.sig h.pos ⟨kind, h.name⟩
        arity h.pos h.name sig.params.length args.length
        let a ← checkArgs C sc h.name (if kind = .type then "parameter" else "field") sig.params [] args
        let o ← produced a.sc g h.pos [⟨.app sig.head (a.res.map (·.term)), a.res.any (·.tainted), false⟩]
          (.app h a.trees)
        pure { o with snaps := a.snaps }
      | _ => notApplied sc h
    | .tuple p es => wrap <$> do
      if let some g := g then
        if g.wants.length ≠ es.length then miscount p g.wants.length s!"tuple has {plural es.length "element"}"
      let o ← checkElems C sc g [] es
      pure ⟨o.sc, o.res, .tuple p o.trees, o.snaps⟩
    | .block ss f => wrap <$> do
      let s ← checkStmts C sc ss
      let o ← checkExpr C s.sc g f
      pure ⟨{ o.sc with names := sc.names }, o.res, .block s.trees o.tree, s.snaps ++ o.snaps⟩
    | .match p m s ann bs => wrap <$> do
      let so ← checkExpr C sc none s
      let r ← single s.pos so.res
      let inner := so.sc
      let (tele, env) ← annotation C inner g ann
      let fs ← forcings C inner r.term s.pos (bs.map Branch.pat) p
      bs.forM fun b => do
        let _ ← survivor inner fs b.pat.ctor.name b.pat.ctor.pos "the match has no branch for it"
        freshAll C inner b.pat.fields
      let missing := (fs.filter fun f => f.pat.isNone && f.forced matches .ok ..).map (·.name)
      unless missing.isEmpty do
        failAt p fun _ => s!"no branch for {", ".intercalate (missing.map code)}, " ++
          s!"which {if missing.length = 1 then "is" else "are"} not refuted here (§10)"
      let label := match ann with
        | .binders _ => some fun i => labelled "annotation entry" ((tele[i]?).bind (·.name)) i
        | .hole _ => g.bind (·.label)
      let bo ← checkBranches C inner r s.pos fs { wants := tele.map Want.of, env, whole := true, label } bs
      let taint (i : Nat) := r.tainted || bo.outs.any fun o => ((o.res[i]?).map (·.tainted)).getD false
      let (sc', rs) := opened inner tele env "match" p taint
      let o ← produced sc' g p rs (.match p m so.tree ann bo.trees)
      pure { o with snaps := so.snaps ++ bo.snaps }
    | .sorry p t => wrap <$> do
      let (tele, env) ← annotation C sc g t
      let (sc', rs) := opened sc tele env "sorry" p fun _ => true
      produced sc' g p rs (.sorry p t)
    | .removed => internal 0 "a removed expression was checked"
  /-- The arguments of a call or application, each checked against its parameter or field (§8). -/
  def checkArgs (C : Ctx) (sc : Scope) (owner role : String) (params : Telescope) (prev : List Res) :
      List Arg → CheckM ArgsOut
    | [] => pure ⟨sc, [], [], []⟩
    | .mk m e :: as => match params with
      | p :: ps => do
        let o ← checkExpr C sc (some (argGiven p prev role owner)) e
        let r ← single e.pos o.res
        let rest ← checkArgs C o.sc owner role ps (prev ++ [r]) as
        pure ⟨rest.sc, r :: rest.res, .mk m o.tree :: rest.trees, o.snaps ++ rest.snaps⟩
      | [] => internal e.pos "an argument has no parameter"
  def checkElems (C : Ctx) (sc : Scope) (g : Option Given) (prev : List Res) : List Expr → CheckM ElemsOut
    | [] => pure ⟨sc, [], [], []⟩
    | e :: es => do
      let o ← checkExpr C sc (elemGiven g prev) e
      let r ← single e.pos o.res
      let rest ← checkElems C o.sc g (prev ++ [r]) es
      pure ⟨rest.sc, r :: rest.res, o.tree :: rest.trees, o.snaps ++ rest.snaps⟩
  /-- Each branch body, in the scope forcing its value constructor gave, against the annotation (§10). -/
  def checkBranches (C : Ctx) (inner : Scope) (r : Res) (scrutPos : Pos) (fs : List Forcing) (g : Given) :
      List Branch → CheckM BranchesOut
    | [] => pure ⟨[], [], []⟩
    | .mk pat body :: bs => do
      let (Γ, ids) ← survivor inner fs pat.ctor.name pat.ctor.pos ""
      let sc := Scope.bind { inner with Γ, taintedBy := reach inner r scrutPos } pat.fields (fieldRes Γ ids)
      let o ← checkExpr C sc (some g) body
      let rest ← checkBranches C inner r scrutPos fs g bs
      pure ⟨o :: rest.outs, .mk pat o.tree :: rest.trees, o.snaps ++ rest.snaps⟩
  def checkStmts (C : Ctx) (sc : Scope) : List Stmt → CheckM StmtsOut
    | [] => pure ⟨sc, [], []⟩
    | s :: ss => do
      let o ← checkStmt C sc s
      let rest ← checkStmts C o.sc ss
      pure ⟨rest.sc, o.tree :: rest.trees, o.snaps ++ rest.snaps⟩
  /-- A statement (§8, §10); a pattern `let`'s facts stay in the scope after it. -/
  def checkStmt (C : Ctx) (sc : Scope) : Stmt → CheckM StmtOut
    | .inspect p => pure ⟨sc, .inspect p, [⟨p, sc, none, C.fn, C.decl⟩]⟩
    | .let p bs rhs => do
      freshAll C sc (bs.map (·.name))
      let o ← checkExpr C sc (some (letGiven bs (← letWants C sc bs))) rhs
      let rs := (bs.zip o.res).map fun (b, r) => { r with erased := r.erased || b.mult == some .erased }
      pure ⟨o.sc.bind (bs.map (·.name)) rs, .let p bs o.tree, o.snaps⟩
    | .patlet p ct m pat rhs => do
      freshAll C sc pat.fields
      let o ← checkExpr C sc none rhs
      let r ← single rhs.pos o.res
      let fs ← forcings C o.sc r.term rhs.pos [pat] p
      pure ⟨← patBind o.sc r rhs.pos ct pat fs, .patlet p ct m pat o.tree, o.snaps⟩
end

end Pledge
