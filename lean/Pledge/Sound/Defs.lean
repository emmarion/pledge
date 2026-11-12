import Pledge.Check.Top
import Pledge.Sound.Measure
import Pledge.UnifySound

namespace Pledge

/-- Only a type constructor's signature returns `Type()`, so every value of type `Type()` is headed by a type
constructor. -/
def TypeHeads (S : Sigs) : Prop :=
  ∀ h sig vs, S.find h = some sig → sig.ret.eval [] vs = some Value.TYPE → h.kind = .type

/-- A world, meant to stand for the program as it is at some top-level item or later: the evaluator's view of
the program, closed signatures typing values, and the ideal values of the top-level entries. -/
structure World where
  P : Prog
  Sc : Sigs
  ρ : List Value

/-- `W'` is meant to be a later world than `W`: it keeps `W`'s functions, kinds, closed signatures and values,
and a signature it adds never returns a data type of `W` (its return is headed by a type constructor that is
`Type` or new) nor is one for `junkHead`, if `W` has none. -/
structure World.Le (W W' : World) : Prop where
  prog : W.P.Ext W'.P
  sigs : W.Sc.Sub W'.Sc
  val : W.ρ <+: W'.ρ
  fresh : ∀ h sig' ws hd us, W.Sc.find h = none → W'.Sc.find h = some sig' →
    sig'.ret.eval [] ws = some (.app hd us) → hd.kind = .type ∧ (hd = Head.Type ∨ W.Sc.find hd = none)
  noJunk : W.Sc.find junkHead = none → W'.Sc.find junkHead = none
  typeHeads : TypeHeads W.Sc → TypeHeads W'.Sc

/-- The value `v` meets the entry `w` of what a position is given, `env` holding the values of its bound
variables: it has the wanted type by its head, and, if `typed`, has it; an entry with no type imposes nothing but
its `is` clause. -/
def WantSat (S : Sigs) (ρ : List Value) (w : Want) (env : List Value) (typed : Bool) (v : Value) : Prop :=
  (∀ T, w.type = some T → ∃ A, T.eval ρ env = some A ∧ v.noRemoved = true ∧ WType S v A ∧
    (typed = true → HasType S v A)) ∧
  ∀ e, w.is = some e → e.eval ρ env = some v

/-- `WantSat`, entry by entry, each entry's bound variables standing for `env` and then the earlier values;
`typed` says which values must have their types. -/
def WantsSat (S : Sigs) (ρ : List Value) : List Want → List Value → List Bool → List Value → Prop
  | [], _, [], [] => True
  | w :: ws, env, t :: ts, v :: vs => WantSat S ρ w env t v ∧ WantsSat S ρ ws (env ++ [v]) ts vs
  | _, _, _, _ => False

/-- The wants `ws` can be opened to values whatever is chosen for those without an `is` clause: each wanted
type has a value, each `is` clause's value has the wanted type by its head, and so on for every value meeting
the entry. It holds of what the checker builds from a checked telescope (`telescope_cons`); opening a tainted
result relies on it (§12). -/
def WantsCons (S : Sigs) (ρ : List Value) : List Want → List Value → Prop
  | [], _ => True
  | w :: ws, env =>
    (∀ T, w.type = some T → ∃ A, T.eval ρ env = some A ∧ A.noRemoved = true) ∧
    (∀ e, w.is = some e → ∃ v, e.eval ρ env = some v ∧ v.noRemoved = true ∧
      ∀ T A, w.type = some T → T.eval ρ env = some A → WType S v A) ∧
    ∀ v, WantSat S ρ w env false v → WantsCons S ρ ws (env ++ [v])

/-- What a position is given has terms with values, and, when `_` may stand for it, can be opened (§10, §12). -/
structure Given.Ok (S : Sigs) (ρ : List Value) (g : Given) : Prop where
  env : ∃ envv, Term.evalList ρ [] g.env = some envv
  cons : g.whole = true → ∀ envv, Term.evalList ρ [] g.env = some envv → WantsCons S ρ g.wants envv

/-- Facts about the checker's signatures that hold in every scope of a declaration whose top level had `n0`
entries: they mention only top-level entries, and a return's bound variables are fields. -/
def SigsOk (n0 : Nat) (S : Sigs) : Prop :=
  ∀ sig ∈ S, sig.entriesBelow n0 = true ∧ sig.ret.boundsBelow sig.params.length = true

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

/-- What a call to `d` is meant to do from an activation `act` (SOUNDNESS.md parts 5, 6 and 9): on ideal arguments
satisfying the parameters, if the measure decreases, there are ideal results satisfying the returns, and on
run-time arguments related to the ideal ones by the parameters' multiplicities the call returns run-time results
related to those ideal results by the returns' multiplicities. `act` is only the measure the totality proof
inducts on; the call's evaluation (`CallRel`) does not consult it. -/
def CallSpec (W : World) (phase : Nat) (d : FnDef) (sig : FnSig) (act : Act) : Prop :=
  ∀ vs, TeleSat W.Sc W.ρ sig.params [] vs → Act.lt (calleeAct d vs) act →
    ∃ rs, TeleSat W.Sc W.ρ sig.returns vs rs ∧ ∀ as, MultsRel W.Sc phase (sig.params.map (·.mult)) as vs →
      ∃ rs', CallRel W.P d as rs' ∧ MultsRel W.Sc phase (sig.returns.map (·.mult)) rs' rs

/-- `CallSpec` from every activation. -/
def FnSpec (W : World) (phase : Nat) (d : FnDef) (sig : FnSig) : Prop :=
  ∀ vs, TeleSat W.Sc W.ρ sig.params [] vs →
    ∃ rs, TeleSat W.Sc W.ρ sig.returns vs rs ∧ ∀ as, MultsRel W.Sc phase (sig.params.map (·.mult)) as vs →
      ∃ rs', CallRel W.P d as rs' ∧ MultsRel W.Sc phase (sig.returns.map (·.mult)) rs' rs

/-- A function global `n` with the signature `sig`, called from the activation `act` inside the function `fn` (or at
the top level). A tainted function has no specification: a call to it only produces tainted results (§12). -/
structure FnOk (n0 phase : Nat) (W : World) (fn : Option FnCtx) (act : Act) (n : String) (sig : FnSig) : Prop where
  params : ∀ b ∈ sig.params, b.entriesBelow n0 = true
  returns : ∀ b ∈ sig.returns, b.entriesBelow n0 = true
  cons : ∀ ρ', ρ'.take n0 = W.ρ.take n0 → ∀ pvals, WantsSat W.Sc ρ' (sig.params.map Want.of) []
    (sig.params.map fun _ => false) pvals → WantsCons W.Sc ρ' (sig.returns.map Want.of) pvals
  subterm : sig.subterm.length = sig.params.length
  defn : sig.tainted = false → ∃ d, W.P.fns.find n = some d ∧ d.params.length = sig.params.length ∧
    d.subterm = sig.subterm ∧ d.returns = sig.returns.length ∧ d.subterm.count true ≤ d.pad ∧
    CallSpec W phase d sig act ∧
    if fn.any (·.group.contains n) then d.group = act.group ∧ d.pad = act.subs.length else d.group < act.group

/-- What each name the globals `gs` can resolve is meant to be in the world `W`. -/
def GlobalsOk (n0 phase : Nat) (gs : List Global) (fn : Option FnCtx) (S : Sigs) (W : World) (act : Act) : Prop :=
  ∀ n g, gs.find? (·.name == n) = some g → match g with
    | .fn _ none => True
    | .fn _ (some sig) => FnOk n0 phase W fn act n sig
    | .type _ cs done => HeadOk S W .type n ∧ ∀ cs', cs = some cs' → done = true →
        n ≠ "Type" ∧ (∃ s, W.Sc.find ⟨.type, n⟩ = some s) ∧ Complete W n cs' ∧
        ∀ c ∈ cs', gs.find? (·.name == c) = some (.ctor c)
    | .ctor _ => HeadOk S W .ctor n

/-- Inside the function `fn`, the activation is the one a call to it with the current values of its `subterm`
parameters has. -/
def ActOk (fn : Option FnCtx) (ρ : List Value) (act : Act) : Prop :=
  ∀ f, fn = some f → ∃ ss, Term.evalList ρ [] f.subterms = some ss ∧
    act.subs = ss.map some ++ List.replicate (act.subs.length - ss.length) none

/-- What a result's ideal value is meant to be: without `removed`, with a type by its head, and with a type when
the result is untainted (§12). -/
def ResOk (S : Sigs) (r : Res) (v : Value) : Prop :=
  v.noRemoved = true ∧ (∃ A, WType S v A) ∧ (r.tainted = false → ∃ V, HasType S v V)

/-- `ResOk`, result by result. -/
def ResOks (S : Sigs) : List Res → List Value → Prop
  | [], [] => True
  | r :: rs, v :: vs => ResOk S r v ∧ ResOks S rs vs
  | _, _ => False

/-- The invariant of the main lemma in an untainted scope, inside a declaration whose top level had `n0` entries:
`ρ` is the ideal valuation of the scope's entries, agreeing with the world on the top-level ones; every name has an
ideal value, as `ResOk` says. -/
structure Inv (C : Ctx) (sc : Scope) (n0 : Nat) (W : World) (ρ : List Value) (act : Act) : Prop where
  untainted : sc.taintedBy = none
  sat : Sat W.Sc sc.Γ ρ
  n0_world : n0 ≤ W.ρ.length
  agree : ρ.take n0 = W.ρ.take n0
  sigs : ∀ ρ', ρ'.take n0 = W.ρ.take n0 → SigsClose sc.sigs ρ' W.Sc
  sigsOk : SigsOk n0 sc.sigs
  noJunk : W.Sc.find junkHead = none
  names : ∀ n r, sc.lookup n = some r → ∃ v, r.term.eval ρ [] = some v ∧ ResOk W.Sc r v
  globals : GlobalsOk n0 C.phase C.globals C.fn sc.sigs W act
  act : ActOk C.fn ρ act
  typeHeads : TypeHeads W.Sc

/-- The multiplicity a name bound to `r` has in `sc`, as `checkExpr` reads it at a variable. -/
def Scope.multOf (sc : Scope) (r : Res) : Mult := if r.erased || sc.erasedEntry r.term then .erased else .many

/-- The evaluator's environment `env` holds, for every untainted name, a run-time value related to its ideal
value by the name's multiplicity. -/
def EnvRel (S : Sigs) (phase : Nat) (sc : Scope) (ρ : List Value) (env : Env) : Prop :=
  ∀ n r, sc.lookup n = some r → r.tainted = false →
    ∃ a v, env.lookup n = some a ∧ r.term.eval ρ [] = some v ∧ MultRel S phase (sc.multOf r) a v

/-- The multiplicity of the position of result `i` of an expression checked under `C` and given `g` (§16). -/
def Ctx.posMult (C : Ctx) (g : Option Given) (i : Nat) : Mult :=
  if C.erased || g.any (·.erasedAt i) then .erased else .many

/-- The run-time values `us` of the results `rs`, read as `rs.length` values (`take`), are related to their ideal
values `ideal` by the positions' multiplicities, for every untainted result. -/
def ResRel (S : Sigs) (phase : Nat) (mult : Nat → Mult) (rs : List Res) (ideal us : List Value) : Prop :=
  ∃ us', take rs.length us = .ok us' ∧ ∀ (i : Nat) (r : Res) (a v : Value), rs[i]? = some r → us'[i]? = some a →
    ideal[i]? = some v → r.tainted = false → MultRel S phase (mult i) a v

/-- What checking an expression in an untainted scope is meant to guarantee (§12, §16): if the scope after it is
untainted, its results have ideal values under an extension of the valuation satisfying that scope (`ResOk`: the
untainted ones typed), all meeting what the position is given; and, outside a type constructor's argument, which is
never evaluated, for every run-time environment related to the ideal valuation, its tree evaluates to run-time values
related to the ideal values of its untainted results. -/
def ExprPost (C : Ctx) (sc : Scope) (g : Option Given) (n0 : Nat) (W : World) (ρ : List Value) (act : Act)
    (o : Out) : Prop :=
  o.sc.taintedBy = none → ∃ ρ' vs, Inv C o.sc n0 W (ρ ++ ρ') act ∧
    Term.evalList (ρ ++ ρ') [] (o.res.map (·.term)) = some vs ∧
    (∀ (i : Nat) (r : Res) (v : Value), o.res[i]? = some r → vs[i]? = some v → ResOk W.Sc r v) ∧
    (∀ g', g = some g' → ∀ envv, Term.evalList ρ [] g'.env = some envv →
      WantsSat W.Sc (ρ ++ ρ') g'.wants envv (o.res.map (!·.tainted)) vs) ∧
    (C.inType = false → ∀ env, EnvRel W.Sc C.phase sc ρ env → ∃ us, Eval W.P env o.tree us ∧
      ResRel W.Sc C.phase (C.posMult g) o.res vs us)

/-- `ExprPost`, and: an absurd expression (§16) checked in an untainted scope that stays untainted has only tainted
results, since no value constructor can head its scrutinee's ideal value. -/
def ExprSound (e : Expr) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (g : Option Given) (n0 : Nat) (W : World) (ρ : List Value) (act : Act) (o : Out),
    Inv C sc n0 W ρ act → (∀ g', g = some g' → g'.Ok W.Sc ρ) → checkExpr C sc g e = .ok o →
    ExprPost C sc g n0 W ρ act o ∧ (o.sc.taintedBy = none → e.absurd = true → ∀ r ∈ o.res, r.tainted = true)

/-- What checking a statement in an untainted scope is meant to guarantee: if the scope after it is untainted, an
extension of the valuation satisfies it, and, outside an erased position or a type constructor's argument, the
statement runs from every run-time
environment related to the ideal valuation to one related to the extended valuation. -/
def StmtPost (C : Ctx) (sc : Scope) (n0 : Nat) (W : World) (ρ : List Value) (act : Act) (o : StmtOut) : Prop :=
  o.sc.taintedBy = none → ∃ ρ', Inv C o.sc n0 W (ρ ++ ρ') act ∧ (C.erased = false → C.inType = false →
    ∀ env, EnvRel W.Sc C.phase sc ρ env → ∃ env', EvalStmt W.P env o.tree env' ∧
      EnvRel W.Sc C.phase o.sc (ρ ++ ρ') env')

def StmtSound (s : Stmt) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (n0 : Nat) (W : World) (ρ : List Value) (act : Act) (o : StmtOut),
    Inv C sc n0 W ρ act → checkStmt C sc s = .ok o → StmtPost C sc n0 W ρ act o

/-- What a goal states, in a world (§12): a type goal's type has a value that has type `Type()` and a value of its
own; for a function goal, the function the `qed` names computes, from run-time arguments related to ideal ones
satisfying the parameters, run-time results related to ideal ones satisfying the returns. -/
def GoalHolds (W : World) (phase : Nat) (g : CheckedGoal) (qedFn : Option String) : Prop :=
  match g.kind with
  | .type t => ∃ v V, t.eval W.ρ [] = some V ∧ HasType W.Sc v V ∧ HasType W.Sc V Value.TYPE
  | .fn ps rs => ∃ n d, qedFn = some n ∧ W.P.fns.find n = some d ∧ ∀ vs, TeleSat W.Sc W.ρ ps [] vs →
      ∃ ws, TeleSat W.Sc W.ρ rs vs ws ∧ ∀ as, MultsRel W.Sc phase (ps.map (·.mult)) as vs →
        ∃ ws', CallRel W.P d as ws' ∧ MultsRel W.Sc phase (rs.map (·.mult)) ws' ws

/-- An untainted type goal's type is a type in the world `W`. -/
def GoalTyped (W : World) (g : CheckedGoal) : Prop :=
  ∀ t, g.kind = .type t → g.tainted = false → ∃ V, t.eval W.ρ [] = some V ∧ HasType W.Sc V Value.TYPE

def GoalBelow (n : Nat) (g : CheckedGoal) : Prop :=
  match g.kind with
  | .type t => t.entriesBelow n = true
  | .fn ps rs => ∀ b ∈ ps ++ rs, b.entriesBelow n = true

/-- The world of a top-level state, given the ideal values of its entries. -/
def TopState.world (st : TopState) (ρ : List Value) : World :=
  ⟨st.prog, st.sc.sigs.map (Sig.close ρ), ρ⟩

/-- What the top level knows while its scope is untainted (§12). -/
structure TopLive (st : TopState) (ρ : List Value) : Prop where
  sat : Sat (st.world ρ).Sc st.sc.Γ ρ
  names : ∀ n r, st.sc.lookup n = some r → ∃ v, r.term.eval ρ [] = some v ∧ ResOk (st.world ρ).Sc r v
  env : EnvRel (st.world ρ).Sc st.phase st.sc ρ st.env
  globals : ∀ W', (st.world ρ).Le W' → ∀ act, (∀ d ∈ st.fns, d.group < act.group) →
    GlobalsOk st.sc.Γ.length st.phase st.globals none st.sc.sigs W' act

/-- The invariant of the top level, between items, for the ideal values `ρ` of the top-level entries. Once the
scope is tainted, only the facts that do not depend on the valuation are kept, and a goal proved before stays
proved (§12). -/
structure TopInv (st : TopState) (ρ : List Value) : Prop where
  len : ρ.length = st.sc.Γ.length
  noRemoved : ∀ v ∈ ρ, v.noRemoved = true
  sigsOk : SigsOk st.sc.Γ.length st.sc.sigs
  noJunk : st.sc.sigs.find junkHead = none
  rets : ∀ sig ∈ st.sc.sigs, ∃ hd args, sig.ret = .app hd args ∧ hd.kind = .type ∧ ∃ s, st.sc.sigs.find hd = some s
  sigNames : ∀ h sig, st.sc.sigs.find h = some sig → kindOf st.globals h.name = some h.kind
  fnNames : ∀ d ∈ st.fns, ∃ sig, st.globals.find? (·.name == d.name) = some (.fn d.name sig)
  groups : ∀ d ∈ st.fns, d.group < st.groups
  typeSig : ∃ s, st.sc.sigs.find Head.Type = some s
  goal : ∀ g, st.goal = some g → GoalBelow st.sc.Γ.length g ∧
    (st.sc.taintedBy = none → (∀ t, g.kind = .type t → t.closed = true) ∧
      ∀ W', (st.world ρ).Le W' → GoalTyped W' g)
  proved : st.proved = true → ∃ g, st.goal = some g ∧ ∀ W', (st.world ρ).Le W' → GoalHolds W' st.phase g st.qedFn
  live : st.sc.taintedBy = none → TopLive st ρ
  typeHeads : ∀ sig ∈ st.sc.sigs, (∃ args, sig.ret = .app Head.Type args) → sig.head.kind = .type

end Pledge
