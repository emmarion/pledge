import Pledge.Core

namespace Pledge

/-- What the evaluator knows of the program: its functions, and whether a name that is not a
function's names a type constructor or a value constructor. -/
structure Prog where
  fns : Fns
  kind : String → Option HeadKind

mutual
  def showValue : Value → String
    | .app h args => h.name ++ "(" ++ showValues args ++ ")"
    | .removed => "_"
  def showValues : List Value → String
    | [] => ""
    | [v] => showValue v
    | v :: vs => showValue v ++ ", " ++ showValues vs
end

def Arg.expr : Arg → Expr
  | .mk _ e => e

def Branch.pat : Branch → Pattern
  | .mk p _ => p

def Branch.body : Branch → Expr
  | .mk _ b => b

/-- `vs` as `n` values, a single `removed` standing for as many as needed. -/
def take (n : Nat) (vs : List Value) : Except String (List Value) :=
  if vs.length = n then pure vs
  else if vs = [.removed] then pure (List.replicate n .removed)
  else throw s!"expected {n} values, got {vs.length}"

def one : List Value → Except String Value
  | [v] => pure v
  | vs => throw s!"expected one value, got {vs.length}"

/-- Binds the names among `ids` to the values `vs`, on top of `env`. -/
def bindIds (env : Env) (ids : List Id) (vs : List Value) : Except String Env :=
  if ids.length = vs.length then pure (((ids.zip vs).filterMap fun (i, v) => i.name.map (·, v)).reverse ++ env)
  else throw s!"{ids.length} names for {vs.length} values"

/-- The values a pattern's fields are bound to. -/
def destruct (m : Option Mult) (pat : Pattern) (v : Value) : Except String (List Value) :=
  if m = some .erased then pure (pat.fields.map fun _ => .removed)
  else match v with
    | .app h args => if h.name = pat.ctor.name then pure args else throw s!"pattern {pat.ctor.name} met {showValue v}"
    | .removed => throw "a removed value was inspected"

def bindPattern (env : Env) (m : Option Mult) (pat : Pattern) (v : Value) : Except String Env := do
  bindIds env pat.fields (← destruct m pat v)

/-- The branch a match takes for the value `v`. -/
def pickBranch (m : Option Mult) (v : Value) (bs : List Branch) : Except String Branch :=
  if m = some .erased then
    match bs with
    | [b] => pure b
    | _ => throw s!"an erased match with {bs.length} branches"
  else match v with
    | .app h _ => match bs.find? (·.pat.ctor.name == h.name) with
      | some b => pure b
      | none => throw s!"no branch for {showValue v}"
    | .removed => throw "a removed value was inspected"

def annTake : Tele → List Value → Except String (List Value)
  | .binders bs, vs => take bs.length vs
  | .hole _, vs => pure vs

theorem sizeOf_map_expr (args : List Arg) : sizeOf (args.map Arg.expr) ≤ sizeOf args := by
  induction args with
  | nil => simp
  | cons a args ih => cases a; simp [Arg.expr]; omega

theorem sizeOf_body_lt {b : Branch} {bs : List Branch} (h : b ∈ bs) : sizeOf b.body < sizeOf bs := by
  have := List.sizeOf_lt_of_mem h
  cases b; simp [Branch.body] at *; omega


theorem ok_bind {ε α β} {a : α} {f : α → Except ε β} : (Except.ok a >>= f) = f a := rfl

theorem error_bind {ε α β} {e : ε} {f : α → Except ε β} : (Except.error e >>= f) = .error e := rfl

theorem bind_eq_ok {ε α β} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- `P'` extends `P`: it keeps `P`'s functions, and keeps every name `P` takes for a type
constructor or value constructor as one of the same kind. -/
structure Prog.Ext (P P' : Prog) : Prop where
  fns : ∀ n d, P.fns.find n = some d → P'.fns.find n = some d
  kind : ∀ n k, P.fns.find n = none → P.kind n = some k → P'.fns.find n = none ∧ P'.kind n = some k


mutual
  /-- `Eval P env e vs`: in the program `P`, with the names in scope valued by `env`, the expression `e`
  evaluates to the values `vs` (§11, §12, §16): big-step, eager, left to right. No rule applies to `sorry`, to an
  unbound name or to a `removed` value that is inspected, so those have no evaluation. -/
  inductive Eval (P : Prog) : Env → Expr → List Value → Prop where
    | var {env : Env} {x : Id} {v : Value} : x.name.bind (List.lookup · env) = some v → Eval P env (.var x) [v]
    | call {env : Env} {h : Name} {args : List Arg} {vs : List Value} {d : FnDef} {rs : List Value} :
        EvalList P env (args.map Arg.expr) vs → P.fns.find h.name = some d → CallRel P d vs rs →
        Eval P env (.app h args) rs
    | ctor {env : Env} {h : Name} {args : List Arg} {vs : List Value} {k : HeadKind} :
        EvalList P env (args.map Arg.expr) vs → P.fns.find h.name = none → P.kind h.name = some k →
        Eval P env (.app h args) [.app ⟨k, h.name⟩ vs]
    | tuple {env : Env} {p : Pos} {es : List Expr} {vs : List Value} :
        EvalList P env es vs → Eval P env (.tuple p es) vs
    | block {env : Env} {ss : List Stmt} {e : Expr} {vs : List Value} :
        EvalBlock P env ss e vs → Eval P env (.block ss e) vs
    | «match» {env : Env} {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch}
        {ws : List Value} {v : Value} {br : Branch} {env' : Env} {rs rs' : List Value} :
        Eval P env s ws → one ws = .ok v → pickBranch m v bs = .ok br → bindPattern env m br.pat v = .ok env' →
        Eval P env' br.body rs → annTake ann rs = .ok rs' → Eval P env (.match p m s ann bs) rs'
    | removed {env : Env} : Eval P env .removed [.removed]
  /-- Expressions evaluated left to right, each to one value. -/
  inductive EvalList (P : Prog) : Env → List Expr → List Value → Prop where
    | nil {env : Env} : EvalList P env [] []
    | cons {env : Env} {e : Expr} {es : List Expr} {ws : List Value} {v : Value} {vs : List Value} :
        Eval P env e ws → one ws = .ok v → EvalList P env es vs → EvalList P env (e :: es) (v :: vs)
  /-- A call to `d` on the arguments `vs` returns `rs`: the parameters are bound on top of the environment where
  `d` was declared, and the body runs. -/
  inductive CallRel (P : Prog) : FnDef → List Value → List Value → Prop where
    | mk {d : FnDef} {vs : List Value} {env : Env} {bs rs : List Value} :
        bindIds d.globals d.params vs = .ok env → Eval P env d.body bs → take d.returns bs = .ok rs →
        CallRel P d vs rs
  /-- A block's statements in order, then its final expression. -/
  inductive EvalBlock (P : Prog) : Env → List Stmt → Expr → List Value → Prop where
    | nil {env : Env} {e : Expr} {vs : List Value} : Eval P env e vs → EvalBlock P env [] e vs
    | cons {env env' : Env} {s : Stmt} {ss : List Stmt} {e : Expr} {vs : List Value} :
        EvalStmt P env s env' → EvalBlock P env' ss e vs → EvalBlock P env (s :: ss) e vs
  /-- A statement runs from one environment to the next. -/
  inductive EvalStmt (P : Prog) : Env → Stmt → Env → Prop where
    | «let» {env env' : Env} {p : Pos} {bs : List LetBinder} {rhs : Expr} {ws vs : List Value} :
        Eval P env rhs ws → take bs.length ws = .ok vs → bindIds env (bs.map (·.name)) vs = .ok env' →
        EvalStmt P env (.let p bs rhs) env'
    | patlet {env env' : Env} {p : Pos} {c : Bool} {m : Option Mult} {pat : Pattern} {rhs : Expr}
        {ws : List Value} {v : Value} :
        Eval P env rhs ws → one ws = .ok v → bindPattern env m pat v = .ok env' →
        EvalStmt P env (.patlet p c m pat rhs) env'
    | inspect {env : Env} {p : Pos} : EvalStmt P env (.inspect p) env
end

theorem Except.ok_inj {ε α} {x : Except ε α} {a b : α} (ha : x = .ok a) (hb : x = .ok b) : a = b := by
  rw [ha] at hb; cases hb; rfl

theorem Option.some_inj' {α} {x : Option α} {a b : α} (ha : x = some a) (hb : x = some b) : a = b := by
  rw [ha] at hb; cases hb; rfl

mutual
  /-- Evaluation is deterministic. -/
  theorem Eval.det {P : Prog} {env : Env} {e : Expr} {vs vs' : List Value} :
      Eval P env e vs → Eval P env e vs' → vs = vs'
    | .var h, .var h' => by cases Option.some_inj' h h'; rfl
    | .call hl hd hc, .call hl' hd' hc' => by
      cases EvalList.det hl hl'; cases Option.some_inj' hd hd'; exact CallRel.det hc hc'
    | .call _ hd _, .ctor _ hd' _ => by rw [hd] at hd'; cases hd'
    | .ctor _ hd _, .call _ hd' _ => by rw [hd] at hd'; cases hd'
    | .ctor hl _ hk, .ctor hl' _ hk' => by cases EvalList.det hl hl'; cases Option.some_inj' hk hk'; rfl
    | .tuple h, .tuple h' => EvalList.det h h'
    | .block h, .block h' => EvalBlock.det h h'
    | .match hs ho hp hb he ha, .match hs' ho' hp' hb' he' ha' => by
      cases Eval.det hs hs'
      cases Except.ok_inj ho ho'
      cases Except.ok_inj hp hp'
      cases Except.ok_inj hb hb'
      cases Eval.det he he'
      exact Except.ok_inj ha ha'
    | .removed, .removed => rfl
  termination_by structural h _ => h
  theorem EvalList.det {P : Prog} {env : Env} {es : List Expr} {vs vs' : List Value} :
      EvalList P env es vs → EvalList P env es vs' → vs = vs'
    | .nil, .nil => rfl
    | .cons he ho hs, .cons he' ho' hs' => by
      cases Eval.det he he'; cases Except.ok_inj ho ho'; cases EvalList.det hs hs'; rfl
  termination_by structural h _ => h
  theorem CallRel.det {P : Prog} {d : FnDef} {vs rs rs' : List Value} :
      CallRel P d vs rs → CallRel P d vs rs' → rs = rs'
    | .mk hb he ht, .mk hb' he' ht' => by
      cases Except.ok_inj hb hb'; cases Eval.det he he'; exact Except.ok_inj ht ht'
  termination_by structural h _ => h
  theorem EvalBlock.det {P : Prog} {env : Env} {ss : List Stmt} {e : Expr} {vs vs' : List Value} :
      EvalBlock P env ss e vs → EvalBlock P env ss e vs' → vs = vs'
    | .nil h, .nil h' => Eval.det h h'
    | .cons hs hb, .cons hs' hb' => by cases EvalStmt.det hs hs'; exact EvalBlock.det hb hb'
  termination_by structural h _ => h
  theorem EvalStmt.det {P : Prog} {env : Env} {s : Stmt} {env' env'' : Env} :
      EvalStmt P env s env' → EvalStmt P env s env'' → env' = env''
    | .let he ht hb, .let he' ht' hb' => by
      cases Eval.det he he'; cases Except.ok_inj ht ht'; exact Except.ok_inj hb hb'
    | .patlet he ho hb, .patlet he' ho' hb' => by
      cases Eval.det he he'; cases Except.ok_inj ho ho'; exact Except.ok_inj hb hb'
    | .inspect, .inspect => rfl
  termination_by structural h _ => h
end

mutual
  /-- Evaluation is unchanged by extending the program. -/
  theorem Eval.ext {P P' : Prog} (hP : P.Ext P') {env : Env} {e : Expr} {vs : List Value} :
      Eval P env e vs → Eval P' env e vs
    | .var h => .var h
    | .call hl hd hc => .call (EvalList.ext hP hl) (hP.fns _ _ hd) (CallRel.ext hP hc)
    | .ctor hl hd hk => .ctor (EvalList.ext hP hl) (hP.kind _ _ hd hk).1 (hP.kind _ _ hd hk).2
    | .tuple h => .tuple (EvalList.ext hP h)
    | .block h => .block (EvalBlock.ext hP h)
    | .match hs ho hp hb he ha => .match (Eval.ext hP hs) ho hp hb (Eval.ext hP he) ha
    | .removed => .removed
  termination_by structural h => h
  theorem EvalList.ext {P P' : Prog} (hP : P.Ext P') {env : Env} {es : List Expr} {vs : List Value} :
      EvalList P env es vs → EvalList P' env es vs
    | .nil => .nil
    | .cons he ho hs => .cons (Eval.ext hP he) ho (EvalList.ext hP hs)
  termination_by structural h => h
  theorem CallRel.ext {P P' : Prog} (hP : P.Ext P') {d : FnDef} {vs rs : List Value} :
      CallRel P d vs rs → CallRel P' d vs rs
    | .mk hb he ht => .mk hb (Eval.ext hP he) ht
  termination_by structural h => h
  theorem EvalBlock.ext {P P' : Prog} (hP : P.Ext P') {env : Env} {ss : List Stmt} {e : Expr} {vs : List Value} :
      EvalBlock P env ss e vs → EvalBlock P' env ss e vs
    | .nil h => .nil (Eval.ext hP h)
    | .cons hs hb => .cons (EvalStmt.ext hP hs) (EvalBlock.ext hP hb)
  termination_by structural h => h
  theorem EvalStmt.ext {P P' : Prog} (hP : P.Ext P') {env : Env} {s : Stmt} {env' : Env} :
      EvalStmt P env s env' → EvalStmt P' env s env'
    | .let he ht hb => .let (Eval.ext hP he) ht hb
    | .patlet he ho hb => .patlet (Eval.ext hP he) ho hb
    | .inspect => .inspect
  termination_by structural h => h
end

theorem one_eq_ok {vs : List Value} {v : Value} (h : one vs = .ok v) : vs = [v] := by
  unfold one at h; split at h <;> cases h; rfl

/-- `x`'s result, with the fact that `x` returned it. -/
def certify {ε α} : (x : Except ε α) → Except ε { a // x = .ok a }
  | .ok a => .ok ⟨a, rfl⟩
  | .error e => .error e

mutual
  /-- Evaluates an expression (§11). It is `partial`: a result it returns is certified by its type to be what `Eval`
  relates the expression to, but neither its termination nor the absence of an error result is established about
  it. -/
  partial def evalExpr (P : Prog) (env : Env) : (e : Expr) → Except String { vs // Eval P env e vs }
    | .var x => match h : x.name.bind (List.lookup · env) with
      | some v => pure ⟨[v], .var h⟩
      | none => throw s!"unbound {x.name}"
    | .app h args => do
      let ⟨vs, hvs⟩ ← evalList P env (args.map Arg.expr)
      match hd : P.fns.find h.name with
      | some d => do
        let ⟨rs, hr⟩ ← evalCall P d vs
        pure ⟨rs, .call hvs hd hr⟩
      | none => match hk : P.kind h.name with
        | some _ => pure ⟨_, .ctor hvs hd hk⟩
        | none => throw s!"unknown name {h.name}"
    | .tuple _ es => do
      let ⟨vs, h⟩ ← evalList P env es
      pure ⟨vs, .tuple h⟩
    | .block ss e => do
      let ⟨vs, h⟩ ← evalBlock P env ss e
      pure ⟨vs, .block h⟩
    | .match _ m s ann bs => do
      let ⟨ws, hs⟩ ← evalExpr P env s
      let ⟨v, ho⟩ ← certify (one ws)
      let ⟨br, hp⟩ ← certify (pickBranch m v bs)
      let ⟨env', hb⟩ ← certify (bindPattern env m br.pat v)
      let ⟨rs, he⟩ ← evalExpr P env' br.body
      let ⟨rs', ha⟩ ← certify (annTake ann rs)
      pure ⟨rs', .match hs ho hp hb he ha⟩
    | .sorry _ _ => throw "sorry was reached"
    | .removed => pure ⟨_, .removed⟩
  /-- Evaluates expressions left to right, each to one value; `partial` as `evalExpr` is. -/
  partial def evalList (P : Prog) (env : Env) : (es : List Expr) → Except String { vs // EvalList P env es vs }
    | [] => pure ⟨[], .nil⟩
    | e :: es => do
      let ⟨ws, he⟩ ← evalExpr P env e
      let ⟨v, ho⟩ ← certify (one ws)
      let ⟨vs, hs⟩ ← evalList P env es
      pure ⟨v :: vs, .cons he ho hs⟩
  /-- Runs a call; `partial` as `evalExpr` is. -/
  partial def evalCall (P : Prog) (d : FnDef) (vs : List Value) : Except String { rs // CallRel P d vs rs } := do
    let ⟨env, hb⟩ ← certify (bindIds d.globals d.params vs)
    let ⟨bs, he⟩ ← evalExpr P env d.body
    let ⟨rs, ht⟩ ← certify (take d.returns bs)
    pure ⟨rs, .mk hb he ht⟩
  /-- Runs a block; `partial` as `evalExpr` is. -/
  partial def evalBlock (P : Prog) (env : Env) :
      (ss : List Stmt) → (e : Expr) → Except String { vs // EvalBlock P env ss e vs }
    | [], e => do
      let ⟨vs, h⟩ ← evalExpr P env e
      pure ⟨vs, .nil h⟩
    | s :: ss, e => do
      let ⟨env', hs⟩ ← evalStmt P env s
      let ⟨vs, hb⟩ ← evalBlock P env' ss e
      pure ⟨vs, .cons hs hb⟩
  /-- Runs a statement, giving the environment after it; `partial` as `evalExpr` is. -/
  partial def evalStmt (P : Prog) (env : Env) : (s : Stmt) → Except String { env' // EvalStmt P env s env' }
    | .let _ bs rhs => do
      let ⟨ws, he⟩ ← evalExpr P env rhs
      let ⟨vs, ht⟩ ← certify (take bs.length ws)
      let ⟨env', hb⟩ ← certify (bindIds env (bs.map (·.name)) vs)
      pure ⟨env', .let he ht hb⟩
    | .patlet _ _ m pat rhs => do
      let ⟨ws, he⟩ ← evalExpr P env rhs
      let ⟨v, ho⟩ ← certify (one ws)
      let ⟨env', hb⟩ ← certify (bindPattern env m pat v)
      pure ⟨env', .patlet he ho hb⟩
    | .inspect _ => pure ⟨env, .inspect⟩
end

end Pledge
