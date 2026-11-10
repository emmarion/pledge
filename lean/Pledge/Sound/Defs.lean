import Pledge.Sound.Plain
import Pledge.Sound.Measure
import Pledge.UnifySound

namespace Pledge

/-- A world, meant to stand for the program as it is at some top-level item or later: the evaluator's view of
the program, closed signatures typing values, and the values of the top-level entries. -/
structure World where
  P : Prog
  Sc : Sigs
  ρ : List Value

/-- `W'` is meant to be a later world than `W`: it keeps `W`'s functions, kinds, closed signatures and values,
and a signature it adds never returns a data type of `W` (its return is headed by a type constructor that is
`Type` or new). -/
structure World.Le (W W' : World) : Prop where
  prog : W.P.Ext W'.P
  sigs : W.Sc.Sub W'.Sc
  val : W.ρ <+: W'.ρ
  fresh : ∀ h sig' ws hd us, W.Sc.find h = none → W'.Sc.find h = some sig' →
    sig'.ret.eval [] ws = some (.app hd us) → hd.kind = .type ∧ (hd = Head.Type ∨ W.Sc.find hd = none)

/-- The value `v` meets the entry `w` of what a position is given, `env` holding the values of its bound
variables; an entry with no type imposes nothing but its `is` clause. -/
def WantSat (S : Sigs) (ρ : List Value) (w : Want) (env : List Value) (v : Value) : Prop :=
  (∀ T, w.type = some T → ∃ A, T.eval ρ env = some A ∧ HasType S v A) ∧ ∀ e, w.is = some e → e.eval ρ env = some v

/-- `WantSat`, entry by entry, each entry's bound variables standing for `env` and then the earlier values. -/
def WantsSat (S : Sigs) (ρ : List Value) : List Want → List Value → List Value → Prop
  | [], _, [] => True
  | w :: ws, env, v :: vs => WantSat S ρ w env v ∧ WantsSat S ρ ws (env ++ [v]) vs
  | _, _, _ => False

/-- A scope in which the taint, erasure and `_` machinery is meant to do nothing (phase 1 without `sorry`). -/
structure Scope.Inert (sc : Scope) : Prop where
  holes : sc.holes = []
  taintedBy : sc.taintedBy = none
  names : ∀ p ∈ sc.names, p.2.tainted = false

/-- What a position is given is meant to have terms with values and no erased entry. -/
structure Given.Ok (ρ : List Value) (g : Given) : Prop where
  env : ∃ envv, Term.evalList ρ [] g.env = some envv
  mult : ∀ w ∈ g.wants, w.mult = .many

/-- Facts about the checker's signatures that hold in every scope of a declaration whose top level had `n0`
entries: they mention only top-level entries, a return's bound variables are fields, and nothing is erased. -/
def SigsOk (n0 : Nat) (S : Sigs) : Prop :=
  ∀ sig ∈ S, sig.entriesBelow n0 = true ∧ sig.ret.boundsBelow sig.params.length = true ∧
    ∀ b ∈ sig.params, b.mult = .many

/-- A type constructor or value constructor `n` of kind `k`, as the world's evaluator and the checker's signatures
see it. -/
structure HeadOk (S : Sigs) (W : World) (k : HeadKind) (n : String) : Prop where
  fns : W.P.fns.find n = none
  kind : W.P.kind n = some k
  sig : ∃ sig, S.find ⟨k, n⟩ = some sig

/-- The closed signatures whose return is headed by the name `T` are those of the value constructors `cs`. -/
def Complete (W : World) (T : String) (cs : List String) : Prop :=
  ∀ h sig' ws hd us, W.Sc.find h = some sig' → sig'.ret.eval [] ws = some (.app hd us) → hd.name = T →
    h.kind = .ctor ∧ h.name ∈ cs

/-- What a call to `d` is meant to do from an activation `act`: on arguments satisfying the parameters, if the
measure decreases, the call returns results satisfying the returns. `act` is only the measure the totality proof
inducts on; the call's evaluation (`CallRel`) does not consult it. -/
def CallSpec (W : World) (d : FnDef) (sig : FnSig) (act : Act) : Prop :=
  ∀ vs, TeleSat W.Sc W.ρ sig.params [] vs → Act.lt (calleeAct d vs) act →
    ∃ rs, CallRel W.P d vs rs ∧ TeleSat W.Sc W.ρ sig.returns vs rs

/-- `CallSpec` from every activation. -/
def FnSpec (W : World) (d : FnDef) (sig : FnSig) : Prop :=
  ∀ vs, TeleSat W.Sc W.ρ sig.params [] vs → ∃ rs, CallRel W.P d vs rs ∧ TeleSat W.Sc W.ρ sig.returns vs rs

/-- A function global `n` with the signature `sig`, called from the activation `act` inside the function `fn` (or at
the top level). -/
structure FnOk (n0 : Nat) (W : World) (fn : Option FnCtx) (act : Act) (n : String) (sig : FnSig) : Prop where
  tainted : sig.tainted = false
  params : ∀ b ∈ sig.params, b.entriesBelow n0 = true ∧ b.mult = .many
  returns : ∀ b ∈ sig.returns, b.entriesBelow n0 = true ∧ b.mult = .many
  subterm : sig.subterm.length = sig.params.length
  defn : ∃ d, W.P.fns.find n = some d ∧ d.params.length = sig.params.length ∧ d.subterm = sig.subterm ∧
    d.returns = sig.returns.length ∧ d.subterm.count true ≤ d.pad ∧ CallSpec W d sig act ∧
    if fn.any (·.group.contains n) then d.group = act.group ∧ d.pad = act.subs.length else d.group < act.group

/-- What each name the globals `gs` can resolve is meant to be in the world `W`. -/
def GlobalsOk (n0 : Nat) (gs : List Global) (fn : Option FnCtx) (S : Sigs) (W : World) (act : Act) : Prop :=
  ∀ n g, gs.find? (·.name == n) = some g → match g with
    | .fn _ none => True
    | .fn _ (some sig) => FnOk n0 W fn act n sig
    | .type _ cs done => HeadOk S W .type n ∧ ∀ cs', cs = some cs' → done = true →
        n ≠ "Type" ∧ (∃ s, W.Sc.find ⟨.type, n⟩ = some s) ∧ Complete W n cs' ∧
        ∀ c ∈ cs', gs.find? (·.name == c) = some (.ctor c)
    | .ctor _ => HeadOk S W .ctor n

/-- Inside the function `fn`, the activation is the one a call to it with the current values of its `subterm`
parameters has. -/
def ActOk (fn : Option FnCtx) (ρ : List Value) (act : Act) : Prop :=
  ∀ f, fn = some f → ∃ ss, Term.evalList ρ [] f.subterms = some ss ∧
    act.subs = ss.map some ++ List.replicate (act.subs.length - ss.length) none

/-- What checking a term needs: a satisfied scope whose names have typed values, bridged signatures, and no
taint. -/
structure TermInv (sc : Scope) (n0 : Nat) (Sc : Sigs) (ρ : List Value) : Prop where
  sat : Sat Sc sc.Γ ρ
  n0_le : n0 ≤ ρ.length
  sigs : SigsClose sc.sigs ρ Sc
  sigsOk : SigsOk n0 sc.sigs
  names : ∀ n r, sc.lookup n = some r → ∃ v V, r.term.eval ρ [] = some v ∧ HasType Sc v V
  inert : sc.Inert

/-- The invariant of the main lemma, inside a declaration whose top level had `n0` entries: `ρ` values the scope's
entries, agreeing with the world on the top-level ones, and `env` is the evaluator's environment. -/
structure Inv (C : Ctx) (sc : Scope) (n0 : Nat) (W : World) (ρ : List Value) (env : Env) (act : Act) : Prop where
  phase : C.phase = 1
  erased : C.erased = false
  sat : Sat W.Sc sc.Γ ρ
  n0_world : n0 ≤ W.ρ.length
  agree : ρ.take n0 = W.ρ.take n0
  sigs : ∀ ρ', ρ'.take n0 = W.ρ.take n0 → SigsClose sc.sigs ρ' W.Sc
  sigsOk : SigsOk n0 sc.sigs
  names : ∀ n r, sc.lookup n = some r → ∃ v V, env.lookup n = some v ∧ r.term.eval ρ [] = some v ∧ HasType W.Sc v V
  globals : GlobalsOk n0 C.globals C.fn sc.sigs W act
  act : ActOk C.fn ρ act
  inert : sc.Inert

/-- What checking an expression is meant to guarantee: it runs to values of its results, typed, meeting what the
position is given, with the scope after it satisfied by an extension of the valuation. -/
def ExprPost (C : Ctx) (sc : Scope) (g : Option Given) (n0 : Nat) (W : World) (ρ : List Value) (env : Env)
    (act : Act) (o : Out) : Prop :=
  o.sc.sigs = sc.sigs ∧ o.sc.names = sc.names ∧ (∀ r ∈ o.res, r.tainted = false ∧ r.erased = false) ∧
  ∃ ρ' vs, Eval W.P env o.tree vs ∧ Inv C o.sc n0 W (ρ ++ ρ') env act ∧
    Term.evalList (ρ ++ ρ') [] (o.res.map (·.term)) = some vs ∧ (∀ v ∈ vs, ∃ V, HasType W.Sc v V) ∧
    ∀ g', g = some g' → ∀ envv, Term.evalList ρ [] g'.env = some envv → WantsSat W.Sc (ρ ++ ρ') g'.wants envv vs

def ExprSound (e : Expr) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (g : Option Given) (n0 : Nat) (W : World) (ρ : List Value) (env : Env) (act : Act)
    (o : Out), Inv C sc n0 W ρ env act → (∀ g', g = some g' → g'.Ok ρ) → checkExpr C sc g e = .ok o →
    ExprPost C sc g n0 W ρ env act o

def StmtSound (s : Stmt) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (n0 : Nat) (W : World) (ρ : List Value) (env : Env) (act : Act) (o : StmtOut),
    Inv C sc n0 W ρ env act → checkStmt C sc s = .ok o →
    o.sc.sigs = sc.sigs ∧ ∃ ρ' env', EvalStmt W.P env o.tree env' ∧ Inv C o.sc n0 W (ρ ++ ρ') env' act

/-- What a goal states, in a world. -/
def GoalHolds (W : World) (g : CheckedGoal) : Prop :=
  match g.kind with
  | .type t => ∃ v V, t.eval W.ρ [] = some V ∧ HasType W.Sc v V
  | .fn ps rs => ∀ vs, TeleSat W.Sc W.ρ ps [] vs → ∃ ws, TeleSat W.Sc W.ρ rs vs ws

def GoalBelow (n : Nat) (g : CheckedGoal) : Prop :=
  match g.kind with
  | .type t => t.entriesBelow n = true
  | .fn ps rs => ∀ b ∈ ps ++ rs, b.entriesBelow n = true

/-- The world of a top-level state, given the values of its entries. -/
def TopState.world (st : TopState) (ρ : List Value) : World :=
  ⟨st.prog, st.sc.sigs.map (Sig.close ρ), ρ⟩

/-- The invariant of the top level, between items, for the valuation `ρ` of the top-level entries. -/
structure TopInv (st : TopState) (ρ : List Value) : Prop where
  phase : st.phase = 1
  sat : Sat (st.world ρ).Sc st.sc.Γ ρ
  names : ∀ n r, st.sc.lookup n = some r →
    ∃ v V, st.env.lookup n = some v ∧ r.term.eval ρ [] = some v ∧ HasType (st.world ρ).Sc v V
  inert : st.sc.Inert
  sigsOk : SigsOk st.sc.Γ.length st.sc.sigs
  rets : ∀ sig ∈ st.sc.sigs, ∃ hd args, sig.ret = .app hd args ∧ hd.kind = .type ∧ ∃ s, st.sc.sigs.find hd = some s
  sigNames : ∀ h sig, st.sc.sigs.find h = some sig → kindOf st.globals h.name = some h.kind
  fnNames : ∀ d ∈ st.fns, ∃ sig, st.globals.find? (·.name == d.name) = some (.fn d.name sig)
  groups : ∀ d ∈ st.fns, d.group < st.groups
  globals : ∀ W', (st.world ρ).Le W' → ∀ act, (∀ d ∈ st.fns, d.group < act.group) →
    GlobalsOk st.sc.Γ.length st.globals none st.sc.sigs W' act
  goal : ∀ g, st.goal = some g → g.tainted = false ∧ GoalBelow st.sc.Γ.length g
  proved : st.proved = true → ∃ g, st.goal = some g ∧ ∀ W', (st.world ρ).Le W' → GoalHolds W' g
  typeSig : ∃ s, st.sc.sigs.find Head.Type = some s

end Pledge
