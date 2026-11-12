import Pledge.Check.Expr
import Pledge.Parser

namespace Pledge

inductive GoalKind where
  | type (t : Term)
  | fn (params returns : Telescope)

/-- The program's goal (§12). -/
structure CheckedGoal where
  kind : GoalKind
  tainted : Bool
  pos : Pos

def CheckedGoal.given (g : CheckedGoal) : Given := match g.kind with
  | .type t => { wants := [⟨none, some t, none, .many⟩], whole := true, label := some fun _ => "the goal's proof" }
  | .fn ps rs => { wants := (ps ++ rs).map Want.of, whole := true, params := some ps.length }

/-- The state of the top level: the phase, the scope, the globals, the functions and the values of the
top-level names (§11), the number of function groups, the goal and what the `qed` did, and the output so far. -/
structure TopState where
  phase : Nat := 1
  sc : Scope
  globals : List Global
  fns : Fns := []
  env : Env := []
  groups : Nat := 0
  goal : Option CheckedGoal := none
  qedChecks : Bool := false
  proved : Bool := false
  qedFn : Option String := none
  prints : List (Pos × String) := []
  snaps : List Snapshot := []
  table : Table := []
  solving : Bool := false

def TopState.init (phase : Nat) (table : Table := []) (solving : Bool := false) : TopState :=
  { phase, sc := { sigs := [⟨.Type, [], .TYPE⟩], Γ := [] }, globals := [.type "Type" none true], table, solving }

def TopState.ctx (st : TopState) (inDecl : Bool := false) : Ctx :=
  { phase := st.phase, globals := st.globals,
    decl := if inDecl then some (st.sc.Γ.length, st.sc.names.length) else none, table := st.table,
    solving := st.solving }

/-- The evaluator's view of the program at the top level. -/
def TopState.prog (st : TopState) : Prog := ⟨st.fns, kindOf st.globals⟩

/-- What evaluating at the top level needs, outside the solving pass (§20): each tree it evaluates has an
evaluation. -/
structure TopState.Runs (st : TopState) : Prop where
  expr : st.solving = false → ∀ pl e o r, closed st.sc (checkExpr { st.ctx with place := pl } · none e) = .ok o →
    single e.pos o.res = .ok r → r.tainted = false → ∃ v, Eval st.prog st.env o.tree [v]
  stmt : st.solving = false → ∀ s o, checkStmt st.ctx st.sc s = .ok o → o.sc.taintedBy = none →
    ∃ env, EvalStmt st.prog st.env o.tree env

/-- Evaluates a checked tree that has an evaluation to one value (§11); nothing while solving `_` (§20) or for a
tainted result (§12). -/
def TopState.eval (st : TopState) (tree : Expr) (tainted : Bool)
    (h : st.solving = false → tainted = false → ∃ v, Eval st.prog st.env tree [v]) : Option Value :=
  if hs : st.solving || tainted then none
  else (evalExpr st.prog st.env tree ((h (by simp_all) (by simp_all)).elim fun _ hv => ⟨_, hv⟩)).1.head?

/-- Runs a checked statement that has a run (§11); nothing while solving `_` (§20). -/
def TopState.run (st : TopState) (s : Stmt) (h : st.solving = false → ∃ env, EvalStmt st.prog st.env s env) : Env :=
  if hs : st.solving then st.env else (evalStmt st.prog st.env s (h (by simpa using hs))).1

/-- `TopState.eval` returns the value `Eval` relates the tree to, unless solving or tainted. -/
theorem TopState.eval_spec {st : TopState} {tree : Expr} {tainted : Bool}
    {h : st.solving = false → tainted = false → ∃ v, Eval st.prog st.env tree [v]} :
    (st.solving || tainted) = false → ∃ v, st.eval tree tainted h = some v ∧ Eval st.prog st.env tree [v] := by
  intro hs
  obtain ⟨v, hv⟩ := h (by simp_all) (by simp_all)
  refine ⟨v, ?_, hv⟩
  simp only [TopState.eval, hs, Bool.false_eq_true, ↓reduceDIte]
  generalize evalExpr st.prog st.env tree _ = r
  rw [Eval.det r.2 hv]
  rfl

theorem TopState.eval_some {st : TopState} {tree : Expr} {tainted : Bool}
    {h : st.solving = false → tainted = false → ∃ v, Eval st.prog st.env tree [v]} {v : Value}
    (hv : st.eval tree tainted h = some v) : (st.solving || tainted) = false ∧ Eval st.prog st.env tree [v] := by
  cases hs : (st.solving || tainted)
  · obtain ⟨w, hw, he⟩ := eval_spec (h := h) hs
    rw [hv] at hw
    cases hw
    exact ⟨rfl, he⟩
  · simp [TopState.eval, hs] at hv

/-- `TopState.run` gives the environment `EvalStmt` relates the statement to, unless solving. -/
theorem TopState.run_cert {st : TopState} {s : Stmt} {h : st.solving = false → ∃ env, EvalStmt st.prog st.env s env}
    (hs : st.solving = false) : EvalStmt st.prog st.env s (st.run s h) := by
  simp only [TopState.run, hs, Bool.false_eq_true, ↓reduceDIte]
  exact (evalStmt _ _ _ _).2

/-- An error found by evaluating (§11), which the solving pass (§20), evaluating nothing, does not meet. -/
def evalFail (pos : Pos) (msg : Unit → String) : CheckM α := throw { pos, msg, evaluated := true }

def addSig (st : TopState) (s : Sig) (g : Global) : TopState :=
  { st with sc := { st.sc with sigs := st.sc.sigs ++ [s] }, globals := st.globals ++ [g] }

/-- Rejects the program unless the telescope mentions only top-level entries. -/
def topLevel (st : TopState) (pos : Pos) (tele : Telescope) : CheckM Unit :=
  ensure (tele.all (·.entriesBelow st.sc.Γ.length)) pos "a telescope mentions an entry below the top level"

def declType (st : TopState) (d : Data) : CheckM TopState := do
  let C := st.ctx true
  let _ ← fresh C st.sc [] d.name.name d.name.pos
  ensure (d.name.name != junkHead.name) d.name.pos "a type constructor is named `sorry`"
  let ps ← telescope C st.sc d.params "binder"
  topLevel st d.name.pos ps.tele
  pure (addSig st ⟨⟨.type, d.name.name⟩, ps.tele, .TYPE⟩ (.type d.name.name (some []) false))

def declCtor (owner : String) (st : TopState) (k : Ctor) : CheckM TopState := do
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

/-- A group of `data` declarations (§5): the type constructors, then the value constructors. -/
def dataGroup (st : TopState) (ds : List Data) : CheckM TopState := do
  let st ← ds.foldlM declType st
  let st ← ds.foldlM (fun st d => d.ctors.foldlM (declCtor d.name.name) st) st
  pure { st with globals := st.globals.map fun
    | .type n cs false => .type n cs (ds.any (·.name.name == n))
    | g => g }

def untainted : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 0 else 1) + untainted bs

def spread : List Bool → List Bool → List Bool
  | t :: ts, n :: ns => (t || n) :: spread ts ns
  | ts, _ => ts

/-- Some function untainted in `ts` is tainted in `ns`. -/
def grows : List Bool → List Bool → Bool
  | t :: ts, n :: ns => (!t && n) || grows ts ns
  | _, _ => false

theorem untainted_spread_le : ∀ ts ns, untainted (spread ts ns) ≤ untainted ts
  | t :: ts, n :: ns => by
    have := untainted_spread_le ts ns
    cases t <;> cases n <;> simp [spread, untainted] <;> omega
  | [], _ | _ :: _, [] => by simp [spread]

theorem untainted_spread_lt : ∀ ts ns, grows ts ns = true → untainted (spread ts ns) < untainted ts
  | t :: ts, n :: ns, h => by
    have := untainted_spread_le ts ns
    cases t <;> cases n <;> simp [spread, untainted, grows] at * <;>
      first | omega | (have := untainted_spread_lt ts ns h; omega)
  | [], _, h | _ :: _, [], h => by simp [grows] at h

/-- Checks each item, keeping the snapshots of those checked before an error. -/
def checkAll (step : α → CheckM Out) : List α → CheckM (List Out)
  | [] => pure []
  | a :: as => do
    let o ← step a
    pure (o :: (← keep o.snaps (checkAll step as)))

/-- Re-checks a group's bodies until no further function becomes tainted (§12); the number of untainted
functions decreases at each round. -/
def fixTaint (step : List Bool → CheckM (List Out)) (taint : List Bool) : CheckM (List Bool × List Out) := do
  let bodies ← step taint
  let now := bodies.map fun o => o.res.any (·.tainted)
  if _h : grows taint now then fixTaint step (spread taint now) else pure (taint, bodies)
termination_by untainted taint
decreasing_by exact untainted_spread_lt _ _ ‹_›

structure FnHead where
  f : Fn
  fn : FnCtx
  sig : FnSig
  sc : Scope
  env : List Term

def returnsGiven (h : FnHead) : Given :=
  { wants := h.sig.returns.map Want.of, env := h.env, whole := true,
    label := some fun j => labelled "return" ((h.sig.returns[j]?).bind (·.name)) j h.fn.name }

def setSigs (gs : List Global) (heads : List FnHead) (taint : List Bool) : List Global :=
  gs.map fun
    | .fn n s => match (heads.zip taint).find? (·.1.fn.name == n) with
      | some (h, t) => .fn n (some { h.sig with tainted := t })
      | none => .fn n s
    | g => g

def fnHead (names : List String) (st : TopState) (f : Fn) : CheckM (TopState × FnHead) := do
  let flags := f.header.params.map (·.subterm)
  let subtermNames := (f.header.params.filter (·.subterm)).map fun p => p.binder.name.name.getD "_"
  let fn : FnCtx := ⟨f.name.name, names, [], subtermNames⟩
  let (ps, rs) ← header { st.ctx true with fn := some fn } st.sc f.header
  topLevel st f.name.pos (ps.tele ++ rs.tele)
  let subterms := ((ps.ids.zip flags).filter (·.2)).map fun (i, _) => Term.entry i
  let sig : FnSig := ⟨ps.tele, rs.tele, flags, false⟩
  let st := { st with globals := st.globals.map fun g => if g.name == f.name.name then .fn g.name (some sig) else g }
  pure (st, ⟨f, { fn with subterms }, sig, ps.sc, ps.ids.map .entry⟩)

/-- A group of functions (§8, §9, §12): names, then telescopes, then the bodies to the taint fixed point. -/
def fnGroup (st : TopState) (fs : List Fn) : CheckM TopState := do
  let names := fs.map (·.name.name)
  let C := st.ctx true
  let st0 ← fs.foldlM (fun st f => do
    let _ ← fresh (st.ctx true) st.sc [] f.name.name f.name.pos
    pure { st with globals := st.globals ++ [.fn f.name.name none] }) st
  let (st1, heads) ← fs.foldlM (fun (st, hs) f => do
    let (st, h) ← fnHead names st f
    pure (st, hs ++ [h])) (st0, [])
  let body (taint : List Bool) (h : FnHead) : CheckM Out :=
    let C := { C with globals := setSigs st1.globals heads taint, fn := some h.fn }
    closed h.sc (checkExpr C · (some (returnsGiven h)) h.f.body)
  let step (taint : List Bool) : CheckM (List Out) := checkAll (body taint) heads
  let (taint, bodies) ← fixTaint step (heads.map fun _ => false)
  let pad := (heads.map fun h => h.fn.subterms.length).foldr max 0
  let defs := (heads.zip bodies).map fun (h, o) =>
    ({ name := h.fn.name, params := h.f.header.params.map (·.binder.name), subterm := h.sig.subterm,
       returns := h.sig.returns.length, body := o.tree, globals := st.env, group := st.groups, pad := pad } : FnDef)
  let snaps := st.snaps ++ bodies.flatMap (·.snaps)
  pure { st1 with globals := setSigs st1.globals heads taint, fns := st.fns ++ defs, groups := st.groups + 1, snaps }

def Value.headName : Value → String
  | .app h _ => h.name
  | .removed => "_"

/-- A `comptime` pattern `let` (§11): checked as a pattern `let`, its right-hand side evaluated in between. -/
def comptimeLet (st : TopState) (hw : st.Runs) (p : Pos) (m : Option Mult) (pat : Pattern) (rhs : Expr) :
    CheckM TopState := do
  let C := st.ctx
  if m == some .erased then failAt p fun _ =>
    "a `comptime` pattern `let` evaluates its right-hand side (§11), so it cannot be erased (§16)"
  freshAll C st.sc pat.fields
  let ⟨o, ho⟩ ← certify (closed st.sc (checkExpr C · none rhs))
  keep o.snaps do
  let ⟨r, hr⟩ ← certify (single rhs.pos o.res)
  let fs ← forcings C o.sc r.term rhs.pos [pat] p false
  let v := st.eval o.tree r.tainted fun hs => hw.expr hs _ rhs o r ho hr
  if let some v := v then
    if v.headName != pat.ctor.name then evalFail rhs.pos fun _ =>
      s!"this evaluates to {code (showValue v)}, which is not headed by {code pat.ctor.name} (§11)"
  let sc ← patBind o.sc r rhs.pos true pat fs
  let env ← if sc.taintedBy.isSome then pure st.env else match v with
    | some v => match bindPattern st.env m pat v with
      | .ok env => pure env
      | .error msg => evalFail p fun _ => s!"evaluation stopped: {msg}"
    | none => pure st.env
  pure { st with sc := sc, env := env, snaps := st.snaps ++ o.snaps }

/-- A top-level statement other than a `comptime` pattern `let` (§11): checked, then run unless the scope after it
is tainted (§12). -/
def topStmt (st : TopState) (hw : st.Runs) (s : Stmt) : CheckM TopState := do
  let ⟨o, ho⟩ ← certify (checkStmt st.ctx st.sc s)
  let env := if ht : o.sc.taintedBy.isSome then st.env
    else st.run o.tree fun hs => hw.stmt hs s o ho (by simpa using ht)
  pure { st with sc := o.sc, env := env, snaps := st.snaps ++ o.snaps }

def qedFnGoal (st : TopState) (ps rs : Telescope) (e : Expr) : CheckM TopState := do
  let wrong {α} : CheckM α := failAt e.pos fun _ =>
    "the goal is a function goal, so `qed` names a function declared before it, as in `qed f;`"
  let .var ⟨some n, _⟩ := e | wrong
  let some (.fn _ (some sig)) := st.ctx.global n | wrong
  let counts (a b : Telescope) := s!"{plural a.length "parameter"} and {plural b.length "return"}"
  if sig.params.length ≠ ps.length || sig.returns.length ≠ rs.length then
    failAt e.pos fun _ => s!"{code n} has {counts sig.params sig.returns}, and the goal has {counts ps rs}"
  if let some i := difference st.sc.Γ (ps ++ rs) (sig.params ++ sig.returns) then
    failAt e.pos fun _ =>
      let k := ps.length
      let names := (ps ++ rs).map (·.name.getD "_")
      let shown (tele : Telescope) := match tele[i]? with
        | some b =>
          let m := if b.mult == Mult.erased then "erased " else ""
          code s!"{m}{names.getD i "_"} {if b.is.isSome then "is" else ":"} {st.sc.text (b.is.getD b.type) names}"
        | none => "missing"
      s!"{code n}'s {if i < k then s!"parameter {i + 1}" else s!"return {i - k + 1}"} is " ++
      s!"{shown (sig.params ++ sig.returns)}, and the goal's is {shown (ps ++ rs)} (binders named as in the goal); " ++
      "a function proves a function goal when its parameters and returns are canonically identical to the goal's, " ++
      "position by position, binder names aside (§12)"
  pure { st with qedFn := some n, proved := !sig.tainted }

def printPlace : String := "the expression of a `print`"

/-- One top-level item (§8, §11, §12). -/
def topItem (st : TopState) (hw : st.Runs) : Top → CheckM TopState
  | .data d => dataGroup st [d]
  | .mutualData _ ds => dataGroup st ds
  | .fn f => fnGroup st [f]
  | .mutualFn _ fs => fnGroup st fs
  | .stmt (.patlet p true m pat rhs) => comptimeLet st hw p m pat rhs
  | .stmt s => topStmt st hw s
  | .print p e => do
    let ⟨o, ho⟩ ← certify (closed st.sc (checkExpr { st.ctx with place := printPlace } · none e))
    let ⟨r, hr⟩ ← keep o.snaps (certify (single e.pos o.res))
    let v := st.eval o.tree r.tainted fun hs => hw.expr hs _ e o r ho hr
    let prints := st.prints ++ [(p, (v.map showValue).getD "sorry")]
    pure { st with sc := o.sc, prints := prints, snaps := st.snaps ++ o.snaps }
  | .goal p g => do
    if st.goal.isSome then failAt p fun _ => "a program has at most one `goal` (§12)"
    let goal ← match g with
      | .fn h => do
        let (ps, rs) ← header (st.ctx true) st.sc h
        topLevel st p (ps.tele ++ rs.tele)
        pure ⟨.fn ps.tele rs.tele, ps.tainted || rs.tainted || st.sc.taintedBy.isSome, p⟩
      | .type t => do
        let (ty, _, tainted) ← annotate st.ctx st.sc (.type t)
        ensure (ty.entriesBelow st.sc.Γ.length) t.pos "a goal mentions an entry below the top level"
        pure ⟨.type ty, tainted || st.sc.taintedBy.isSome, t.pos⟩
    pure { st with goal := some goal }
  | .qed p e => do
    if st.qedChecks then failAt p fun _ => "a program has at most one `qed` (§12)"
    let some goal := st.goal | failAt p fun _ =>
      "`qed` comes after `goal`, and no `goal` is set before this `qed` (§12)"
    let st ← match goal.kind with
      | .fn ps rs => qedFnGoal st ps rs e
      | .type _ => do
        if let .var ⟨some n, _⟩ := e then
          if let some (.fn ..) := st.ctx.global n then failAt e.pos fun _ =>
            s!"{code n} is a function, and naming a function proves only a function goal, " ++
            "`goal fn (...) -> (...);`; this goal is a type"
        let o ← closed st.sc (checkExpr st.ctx · (some goal.given) e)
        pure { st with sc := o.sc, proved := !o.res.any (·.tainted), snaps := st.snaps ++ o.snaps }
    pure { st with qedChecks := true, proved := st.proved && st.sc.taintedBy.isNone && !goal.tainted }

/-- The `inspect;` text (§13): Expected, Termination and Scope. -/
def Snapshot.render (s : Snapshot) : String :=
  let sc := s.sc
  let here := match s.decl with
    | some (_, n) => sc.names.take (sc.names.length - n)
    | none => sc.names
  let terms := here.reverse.foldl (fun acc (_, r) => if acc.contains r.term then acc else acc ++ [r.term]) []
  let facts (t : Term) : Term × Option Term := match t with
    | .entry i => match sc.Γ[i]? with
      | some en => (en.type, en.rule)
      | none => (t, none)
    | t => ((typeOf sc.sigs sc.Γ t).getD t, some t)
  let line (names : String) (t : Term) : String :=
    let (ty, rule) := facts t
    s!"  {names} : {sc.text ty}" ++ rule.elim "" (s!" is {sc.text ·}")
  let named := terms.map fun t =>
    let ns := (here.reverse.filter (·.2.term == t)).map fun (n, r) => if r.tainted then n ++ " (tainted)" else n
    line (", ".intercalate ns) t
  let shown := terms.flatMap fun t => let (ty, rule) := facts t
    ((ty :: rule.toList).map (·.canon sc.Γ)).flatMap Term.entries
  let anon := (List.range sc.Γ.length).filter fun i => shown.contains i && (sc.nameOf i).isNone
  let expected := match s.given with
    | none => ["Expected: nothing is given here"]
    | some g => "Expected:" :: g.wants.map fun w =>
      let t (u : Term) := sc.text (u.subst g.env)
      s!"  {w.name.getD "_"}" ++ match w.type, w.is with
        | none, _ => " : (undetermined)"
        | some ty, none => s!" : {t ty}"
        | some _, some e => s!" is {t e}"
  let termination := match s.fn with
    | some f => s!"Termination: {code f.name}, `subterm` parameters ({", ".intercalate f.subtermNames}); " ++
        s!"group {", ".intercalate (f.group.map code)}"
    | none => "Termination: top level, which calls any function unmarked"
  let tainted := (s.sc.taintedBy.map (s!"  the scope is tainted by the scrutinee at {·}")).toList
  "\n".intercalate (expected ++ [termination, "Scope:"] ++ named ++
    anon.map (fun i => line (sc.text (.entry i)) (.entry i)) ++ tainted)

/-- What checking a program reports (§12, §13), and the final state the soundness theorems are about. -/
structure Outcome where
  error : Option (Pos × String)
  prints : List (Pos × String)
  inspects : List (Pos × String)
  qed : String
  goalProved : Option Bool
  containsSorry : Bool
  sigs : Sigs
  entries : Entries
  fns : Fns
  env : Env
  goal : Option CheckedGoal
  qedFn : Option String
  tainted : Bool

/-- The first error checking meets: the error, its item and the number of items after it. -/
abbrev Stop := CheckError × Top × Nat

/-- The outcome of checking that stopped at `st`, after `failed` if checking failed, whose error is reported as
`text` gives it. -/
def outcome (has : String → Bool) (st : TopState) (failed : Option Stop) (syntaxError : Option (Pos × String))
    (text : Stop → Pos × String := fun (e, _) => (e.pos, e.msg ())) : Outcome :=
  let error := (failed.map text).orElse fun _ => syntaxError
  let qed := if !has "qed" then "none"
    else if failed.any fun (_, t, _) => t matches .qed .. then "fails"
    else if st.qedChecks then "checks" else "unreached"
  { error := error, prints := st.prints, inspects := st.snaps.map fun s => (s.pos, s.render), qed := qed,
    goalProved := if has "goal" then some (failed.isNone && syntaxError.isNone && st.proved) else none,
    containsSorry := has "sorry",
    sigs := st.sc.sigs, entries := st.sc.Γ, fns := st.fns, env := st.env, goal := st.goal, qedFn := st.qedFn,
    tainted := st.sc.taintedBy.isSome }

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

def Top.holes : Top → List Pos
  | .data d => d.holes
  | .mutualData _ ds => ds.flatMap Data.holes
  | .fn f => f.header.holes ++ f.body.holes
  | .mutualFn _ fs => fs.flatMap fun f => f.header.holes ++ f.body.holes
  | .stmt s => Stmt.holesList [s]
  | .print _ e | .qed _ e => e.holes
  | .goal _ (.type t) => t.holes
  | .goal _ (.fn h) => h.holes

def unsolved (prog : Program) (table : Table) : Nat :=
  ((prog.flatMap Top.holes).filter fun p => (table.lookup p).isNone).length

end Pledge
