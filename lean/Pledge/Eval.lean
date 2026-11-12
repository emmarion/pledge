import Pledge.Core

namespace Pledge

/-- What the evaluator knows of the program: its functions, and whether a name that is not a
function's names a type constructor or a value constructor. -/
structure Prog where
  fns : Fns
  kind : String → Option HeadKind

mutual
  /-- A value as text, a removed one as `_`. -/
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

/-- `x`'s result, given that it has one. -/
def known {ε α} : (x : Except ε α) → (∃ a, x = .ok a) → { a // x = .ok a }
  | .ok a, _ => ⟨a, rfl⟩
  | .error _, h => False.elim (let ⟨_, h⟩ := h; nomatch h)

/-- What the evaluator is asked for: an expression, expressions in order, a call, a block or a statement. -/
inductive Cfg where
  | expr (env : Env) (e : Expr)
  | list (env : Env) (es : List Expr)
  | call (d : FnDef) (vs : List Value)
  | block (env : Env) (ss : List Stmt) (e : Expr)
  | stmt (env : Env) (s : Stmt)

/-- `Cfg.Sub P c' c`: evaluating `c` asks for `c'`, given the results `Eval` gives what it asks for before. -/
inductive Cfg.Sub (P : Prog) : Cfg → Cfg → Prop where
  | args {env : Env} {h : Name} {args : List Arg} : Cfg.Sub P (.list env (args.map Arg.expr)) (.expr env (.app h args))
  | call {env : Env} {h : Name} {args : List Arg} {vs : List Value} {d : FnDef} :
      EvalList P env (args.map Arg.expr) vs → P.fns.find h.name = some d →
      Cfg.Sub P (.call d vs) (.expr env (.app h args))
  | tuple {env : Env} {p : Pos} {es : List Expr} : Cfg.Sub P (.list env es) (.expr env (.tuple p es))
  | block {env : Env} {ss : List Stmt} {e : Expr} : Cfg.Sub P (.block env ss e) (.expr env (.block ss e))
  | scrut {env : Env} {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch} :
      Cfg.Sub P (.expr env s) (.expr env (.match p m s ann bs))
  | branch {env : Env} {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch} {ws : List Value}
      {v : Value} {br : Branch} {env' : Env} : Eval P env s ws → one ws = .ok v → pickBranch m v bs = .ok br →
      bindPattern env m br.pat v = .ok env' → Cfg.Sub P (.expr env' br.body) (.expr env (.match p m s ann bs))
  | head {env : Env} {e : Expr} {es : List Expr} : Cfg.Sub P (.expr env e) (.list env (e :: es))
  | tail {env : Env} {e : Expr} {es : List Expr} : Cfg.Sub P (.list env es) (.list env (e :: es))
  | body {d : FnDef} {vs : List Value} {env : Env} :
      bindIds d.globals d.params vs = .ok env → Cfg.Sub P (.expr env d.body) (.call d vs)
  | last {env : Env} {e : Expr} : Cfg.Sub P (.expr env e) (.block env [] e)
  | first {env : Env} {s : Stmt} {ss : List Stmt} {e : Expr} : Cfg.Sub P (.stmt env s) (.block env (s :: ss) e)
  | rest {env env' : Env} {s : Stmt} {ss : List Stmt} {e : Expr} :
      EvalStmt P env s env' → Cfg.Sub P (.block env' ss e) (.block env (s :: ss) e)
  | «let» {env : Env} {p : Pos} {bs : List LetBinder} {rhs : Expr} :
      Cfg.Sub P (.expr env rhs) (.stmt env (.let p bs rhs))
  | patlet {env : Env} {p : Pos} {c : Bool} {m : Option Mult} {pat : Pattern} {rhs : Expr} :
      Cfg.Sub P (.expr env rhs) (.stmt env (.patlet p c m pat rhs))

mutual
  /-- What has an evaluation asks for nothing without end: `Cfg.Sub` is well-founded below it. -/
  theorem Eval.acc {P : Prog} {env : Env} {e : Expr} {vs : List Value} :
      Eval P env e vs → Acc (Cfg.Sub P) (.expr env e)
    | .var _ => ⟨_, fun _ h => by cases h⟩
    | .call hl hd hc => ⟨_, fun _ h => by
      cases h with
      | args => exact EvalList.acc hl
      | call hl' hd' => cases EvalList.det hl hl'; cases Option.some_inj' hd hd'; exact CallRel.acc hc⟩
    | .ctor hl hd _ => ⟨_, fun _ h => by
      cases h with
      | args => exact EvalList.acc hl
      | call _ hd' => rw [hd] at hd'; cases hd'⟩
    | .tuple h => ⟨_, fun _ h' => by cases h'; exact EvalList.acc h⟩
    | .block h => ⟨_, fun _ h' => by cases h'; exact EvalBlock.acc h⟩
    | .match hs ho hp hb he _ => ⟨_, fun _ h => by
      cases h with
      | scrut => exact Eval.acc hs
      | branch hs' ho' hp' hb' =>
        cases Eval.det hs hs'; cases Except.ok_inj ho ho'; cases Except.ok_inj hp hp'; cases Except.ok_inj hb hb'
        exact Eval.acc he⟩
    | .removed => ⟨_, fun _ h => by cases h⟩
  termination_by structural h => h
  theorem EvalList.acc {P : Prog} {env : Env} {es : List Expr} {vs : List Value} :
      EvalList P env es vs → Acc (Cfg.Sub P) (.list env es)
    | .nil => ⟨_, fun _ h => by cases h⟩
    | .cons he _ hs => ⟨_, fun _ h => by
      cases h with
      | head => exact Eval.acc he
      | tail => exact EvalList.acc hs⟩
  termination_by structural h => h
  theorem CallRel.acc {P : Prog} {d : FnDef} {vs rs : List Value} : CallRel P d vs rs → Acc (Cfg.Sub P) (.call d vs)
    | .mk hb he _ => ⟨_, fun _ h => by cases h with | body hb' => cases Except.ok_inj hb hb'; exact Eval.acc he⟩
  termination_by structural h => h
  theorem EvalBlock.acc {P : Prog} {env : Env} {ss : List Stmt} {e : Expr} {vs : List Value} :
      EvalBlock P env ss e vs → Acc (Cfg.Sub P) (.block env ss e)
    | .nil h => ⟨_, fun _ h' => by cases h'; exact Eval.acc h⟩
    | .cons hs hb => ⟨_, fun _ h => by
      cases h with
      | first => exact EvalStmt.acc hs
      | rest hs' => cases EvalStmt.det hs hs'; exact EvalBlock.acc hb⟩
  termination_by structural h => h
  theorem EvalStmt.acc {P : Prog} {env : Env} {s : Stmt} {env' : Env} :
      EvalStmt P env s env' → Acc (Cfg.Sub P) (.stmt env s)
    | .let he _ _ => ⟨_, fun _ h => by cases h; exact Eval.acc he⟩
    | .patlet he _ _ => ⟨_, fun _ h => by cases h; exact Eval.acc he⟩
    | .inspect => ⟨_, fun _ h => by cases h⟩
  termination_by structural h => h
end

instance {α} {r : α → α → Prop} : WellFoundedRelation { a // Acc r a } where
  rel x y := r x.1 y.1
  wf := ⟨fun ⟨a, h⟩ => by
    induction h with
    | intro a _ ih => exact ⟨_, fun ⟨b, _⟩ hr => ih b hr⟩⟩

/-- The match of an evaluation, once its scrutinee's values are known. -/
theorem Eval.match_inv {P : Prog} {env : Env} {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele}
    {bs : List Branch} {ws : List Value} (h : ∃ rs, Eval P env (.match p m s ann bs) rs) (hs : Eval P env s ws) :
    ∃ v br env' rs, one ws = .ok v ∧ pickBranch m v bs = .ok br ∧ bindPattern env m br.pat v = .ok env' ∧
      Eval P env' br.body rs ∧ ∃ rs', annTake ann rs = .ok rs' := by
  obtain ⟨_, h⟩ := h
  cases h with
  | «match» hs' ho hp hb he ha => cases Eval.det hs hs'; exact ⟨_, _, _, _, ho, hp, hb, he, _, ha⟩

mutual
  /-- Evaluates an expression that has an evaluation (§11), to the values `Eval` relates it to, which are unique
  (`Eval.det`). It recurses on what it asks for (`Cfg.Sub`), well-founded below what has an evaluation
  (`Eval.acc`). -/
  def evalExpr (P : Prog) (env : Env) : (e : Expr) → (∃ vs, Eval P env e vs) → { vs // Eval P env e vs }
    | .var x, h => match hv : x.name.bind (List.lookup · env) with
      | some v => ⟨[v], .var hv⟩
      | none => False.elim (by obtain ⟨_, h⟩ := h; cases h; simp_all)
    | .app f args, h =>
      let ⟨vs, hvs⟩ := evalList P env (args.map Arg.expr) (by obtain ⟨_, h⟩ := h; cases h <;> exact ⟨_, ‹_›⟩)
      match hd : P.fns.find f.name with
      | some d =>
        let ⟨rs, hr⟩ := evalCall P d vs (by
          obtain ⟨_, h⟩ := h
          cases h with
          | call hl hd' hc => cases EvalList.det hvs hl; cases Option.some_inj' hd hd'; exact ⟨_, hc⟩
          | ctor _ hd' _ => rw [hd] at hd'; cases hd')
        ⟨rs, .call hvs hd hr⟩
      | none => match hk : P.kind f.name with
        | some _ => ⟨_, .ctor hvs hd hk⟩
        | none => False.elim (by obtain ⟨_, h⟩ := h; cases h <;> simp_all)
    | .tuple _ es, h =>
      let ⟨vs, hvs⟩ := evalList P env es (by obtain ⟨_, h⟩ := h; cases h; exact ⟨_, ‹_›⟩)
      ⟨vs, .tuple hvs⟩
    | .block ss e, h =>
      let ⟨vs, hvs⟩ := evalBlock P env ss e (by obtain ⟨_, h⟩ := h; cases h; exact ⟨_, ‹_›⟩)
      ⟨vs, .block hvs⟩
    | .match _ m s ann bs, h =>
      let ⟨ws, hs⟩ := evalExpr P env s (by obtain ⟨_, h⟩ := h; cases h; exact ⟨_, ‹Eval _ _ s _›⟩)
      let ⟨v, ho⟩ := known (one ws) (by obtain ⟨_, _, _, _, ho, -⟩ := Eval.match_inv h hs; exact ⟨_, ho⟩)
      let ⟨br, hp⟩ := known (pickBranch m v bs) (by
        obtain ⟨_, _, _, _, ho', hp, -⟩ := Eval.match_inv h hs; cases Except.ok_inj ho ho'; exact ⟨_, hp⟩)
      let ⟨env', hb⟩ := known (bindPattern env m br.pat v) (by
        obtain ⟨_, _, _, _, ho', hp', hb, -⟩ := Eval.match_inv h hs
        cases Except.ok_inj ho ho'; cases Except.ok_inj hp hp'; exact ⟨_, hb⟩)
      let ⟨rs, he⟩ := evalExpr P env' br.body (by
        obtain ⟨_, _, _, _, ho', hp', hb', he, -⟩ := Eval.match_inv h hs
        cases Except.ok_inj ho ho'; cases Except.ok_inj hp hp'; cases Except.ok_inj hb hb'; exact ⟨_, he⟩)
      let ⟨rs', ha⟩ := known (annTake ann rs) (by
        obtain ⟨_, _, _, _, ho', hp', hb', he', ha⟩ := Eval.match_inv h hs
        cases Except.ok_inj ho ho'; cases Except.ok_inj hp hp'; cases Except.ok_inj hb hb'; cases Eval.det he he'
        exact ha)
      ⟨rs', .match hs ho hp hb he ha⟩
    | .sorry _ _, h => False.elim (by obtain ⟨_, h⟩ := h; cases h)
    | .removed, _ => ⟨_, .removed⟩
  termination_by e h => (⟨.expr env e, h.elim fun _ d => d.acc⟩ : { c // Acc (Cfg.Sub P) c })
  decreasing_by
    all_goals first
      | exact .args | exact .call ‹_› ‹_› | exact .tuple | exact .block | exact .scrut
      | exact .branch ‹_› ‹_› ‹_› ‹_›
  /-- Evaluates expressions that have an evaluation, left to right, as `evalExpr` does. -/
  def evalList (P : Prog) (env : Env) : (es : List Expr) → (∃ vs, EvalList P env es vs) →
      { vs // EvalList P env es vs }
    | [], _ => ⟨[], .nil⟩
    | e :: es, h =>
      let ⟨ws, he⟩ := evalExpr P env e (by obtain ⟨_, h⟩ := h; cases h; exact ⟨_, ‹_›⟩)
      let ⟨v, ho⟩ := known (one ws) (by
        obtain ⟨_, h⟩ := h; cases h with | cons he' ho _ => cases Eval.det he he'; exact ⟨_, ho⟩)
      let ⟨vs, hs⟩ := evalList P env es (by obtain ⟨_, h⟩ := h; cases h; exact ⟨_, ‹_›⟩)
      ⟨v :: vs, .cons he ho hs⟩
  termination_by es h => (⟨.list env es, h.elim fun _ d => d.acc⟩ : { c // Acc (Cfg.Sub P) c })
  decreasing_by all_goals first | exact .head | exact .tail
  /-- Runs a call that has a run, as `evalExpr` does. -/
  def evalCall (P : Prog) (d : FnDef) (vs : List Value) (h : ∃ rs, CallRel P d vs rs) :
      { rs // CallRel P d vs rs } :=
    let ⟨env, hb⟩ := known (bindIds d.globals d.params vs) (by obtain ⟨_, h⟩ := h; cases h; exact ⟨_, ‹_›⟩)
    let ⟨bs, he⟩ := evalExpr P env d.body (by
      obtain ⟨_, h⟩ := h; cases h with | mk hb' he _ => cases Except.ok_inj hb hb'; exact ⟨_, he⟩)
    let ⟨rs, ht⟩ := known (take d.returns bs) (by
      obtain ⟨_, h⟩ := h
      cases h with | mk hb' he' ht => cases Except.ok_inj hb hb'; cases Eval.det he he'; exact ⟨_, ht⟩)
    ⟨rs, .mk hb he ht⟩
  termination_by (⟨.call d vs, h.elim fun _ d => d.acc⟩ : { c // Acc (Cfg.Sub P) c })
  decreasing_by exact .body ‹_›
  /-- Runs a block that has a run, as `evalExpr` does. -/
  def evalBlock (P : Prog) (env : Env) : (ss : List Stmt) → (e : Expr) → (∃ vs, EvalBlock P env ss e vs) →
      { vs // EvalBlock P env ss e vs }
    | [], e, h =>
      let ⟨vs, he⟩ := evalExpr P env e (by obtain ⟨_, h⟩ := h; cases h; exact ⟨_, ‹_›⟩)
      ⟨vs, .nil he⟩
    | s :: ss, e, h =>
      let ⟨env', hs⟩ := evalStmt P env s (by obtain ⟨_, h⟩ := h; cases h; exact ⟨_, ‹_›⟩)
      let ⟨vs, hb⟩ := evalBlock P env' ss e (by
        obtain ⟨_, h⟩ := h; cases h with | cons hs' hb => cases EvalStmt.det hs hs'; exact ⟨_, hb⟩)
      ⟨vs, .cons hs hb⟩
  termination_by ss e h => (⟨.block env ss e, h.elim fun _ d => d.acc⟩ : { c // Acc (Cfg.Sub P) c })
  decreasing_by all_goals first | exact .last | exact .first | exact .rest ‹_›
  /-- Runs a statement that has a run, giving the environment after it, as `evalExpr` does. -/
  def evalStmt (P : Prog) (env : Env) : (s : Stmt) → (∃ env', EvalStmt P env s env') →
      { env' // EvalStmt P env s env' }
    | .let _ bs rhs, h =>
      let ⟨ws, he⟩ := evalExpr P env rhs (by obtain ⟨_, h⟩ := h; cases h; exact ⟨_, ‹_›⟩)
      let ⟨vs, ht⟩ := known (take bs.length ws) (by
        obtain ⟨_, h⟩ := h; cases h with | «let» he' ht _ => cases Eval.det he he'; exact ⟨_, ht⟩)
      let ⟨env', hb⟩ := known (bindIds env (bs.map (·.name)) vs) (by
        obtain ⟨_, h⟩ := h
        cases h with | «let» he' ht' hb => cases Eval.det he he'; cases Except.ok_inj ht ht'; exact ⟨_, hb⟩)
      ⟨env', .let he ht hb⟩
    | .patlet _ _ m pat rhs, h =>
      let ⟨ws, he⟩ := evalExpr P env rhs (by obtain ⟨_, h⟩ := h; cases h; exact ⟨_, ‹_›⟩)
      let ⟨v, ho⟩ := known (one ws) (by
        obtain ⟨_, h⟩ := h; cases h with | patlet he' ho _ => cases Eval.det he he'; exact ⟨_, ho⟩)
      let ⟨env', hb⟩ := known (bindPattern env m pat v) (by
        obtain ⟨_, h⟩ := h
        cases h with | patlet he' ho' hb => cases Eval.det he he'; cases Except.ok_inj ho ho'; exact ⟨_, hb⟩)
      ⟨env', .patlet he ho hb⟩
    | .inspect _, _ => ⟨env, .inspect⟩
  termination_by s h => (⟨.stmt env s, h.elim fun _ d => d.acc⟩ : { c // Acc (Cfg.Sub P) c })
  decreasing_by all_goals first | exact .let | exact .patlet
end

end Pledge
