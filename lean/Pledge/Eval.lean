import Pledge.Core

namespace Pledge

mutual
  /-- `v.isSub w`: `v` is a strict subtree of `w`. -/
  def Value.isSub (v : Value) : Value → Bool
    | .app _ args => Value.isSubList v args
    | .removed => false
  def Value.isSubList (v : Value) : List Value → Bool
    | [] => false
    | a :: as => v == a || v.isSub a || Value.isSubList v as
end

/-- `v.lt w`: `v` is a strict subtree of `w`. -/
def Value.lt (v w : Value) : Prop := v.isSub w = true

instance : DecidableRel Value.lt := fun v w => inferInstanceAs (Decidable (v.isSub w = true))

mutual
  theorem Value.sizeOf_isSub (v : Value) : (w : Value) → v.isSub w = true → sizeOf v < sizeOf w
    | .app h args, hs => by
      have := Value.sizeOf_isSubList v args hs
      simp only [Value.app.sizeOf_spec]; omega
    | .removed, hs => by simp [Value.isSub] at hs
  theorem Value.sizeOf_isSubList (v : Value) :
      (as : List Value) → Value.isSubList v as = true → sizeOf v < sizeOf as
    | [], hs => by simp [Value.isSubList] at hs
    | a :: as, hs => by
      simp only [Value.isSubList, Bool.or_eq_true, beq_iff_eq] at hs
      simp only [List.cons.sizeOf_spec]
      rcases hs with (rfl | hs) | hs
      · omega
      · have := Value.sizeOf_isSub v a hs; omega
      · have := Value.sizeOf_isSubList v as hs; omega
end

theorem Value.lt_wf : WellFounded Value.lt :=
  Subrelation.wf (fun {v w} h => Value.sizeOf_isSub v w h) (measure sizeOf).wf

/-- `SubsLt as bs`: lists of equal length that agree up to some `k`, where `as` holds a strict
subtree of the value `bs` holds. -/
def SubsLt (as bs : List (Option Value)) : Prop :=
  as.length = bs.length ∧
  ∃ k x y, as.take k = bs.take k ∧ as[k]? = some (some x) ∧ bs[k]? = some (some y) ∧ x.lt y

/-- An activation's measure is below another's (SOUNDNESS.md part 6). -/
def Act.lt (a b : Act) : Prop := a.group < b.group ∨ a.group = b.group ∧ SubsLt a.subs b.subs

theorem Act.lt_of_group {a b : Act} (h : a.group < b.group) : Act.lt a b := .inl h

theorem Act.lt_of_subs {a b : Act} {k : Nat} {x y : Value} (hg : a.group = b.group)
    (hl : a.subs.length = b.subs.length) (ht : a.subs.take k = b.subs.take k)
    (ha : a.subs[k]? = some (some x)) (hb : b.subs[k]? = some (some y)) (hxy : x.lt y) : Act.lt a b :=
  .inr ⟨hg, hl, k, x, y, ht, ha, hb, hxy⟩

def OptLt : Option Value → Option Value → Prop
  | some x, some y => x.lt y
  | _, _ => False

instance : DecidableRel OptLt := fun a b => match a, b with
  | some x, some y => inferInstanceAs (Decidable (x.lt y))
  | none, _ => isFalse id
  | some _, none => isFalse id

theorem SubsLt.nil_left {bs} : ¬ SubsLt [] bs := fun ⟨_, _, _, _, _, h, _⟩ => by simp at h

theorem SubsLt.nil_right {as} : ¬ SubsLt as [] := fun ⟨_, _, _, _, _, _, h, _⟩ => by simp at h

theorem SubsLt.cons_iff {a b as bs} :
    SubsLt (a :: as) (b :: bs) ↔ as.length = bs.length ∧ OptLt a b ∨ a = b ∧ SubsLt as bs := by
  constructor
  · rintro ⟨hl, k, x, y, ht, ha, hb, hxy⟩
    cases k with
    | zero => simp at ha hb; subst ha hb; exact .inl ⟨by simpa using hl, hxy⟩
    | succ k =>
      simp only [List.take_succ_cons, List.cons.injEq] at ht
      exact .inr ⟨ht.1, by simpa using hl, k, x, y, ht.2, by simpa using ha, by simpa using hb, hxy⟩
  · rintro (⟨hl, h⟩ | ⟨rfl, hl, k, x, y, ht, ha, hb, hxy⟩)
    · match a, b, h with
      | some x, some y, h => exact ⟨by simp [hl], 0, x, y, by simp, rfl, rfl, h⟩
    · exact ⟨by simp [hl], k + 1, x, y, by simp [ht], ha, hb, hxy⟩

instance SubsLt.dec : (as bs : List (Option Value)) → Decidable (SubsLt as bs)
  | [], _ => isFalse SubsLt.nil_left
  | _ :: _, [] => isFalse SubsLt.nil_right
  | _ :: as, _ :: bs => have := SubsLt.dec as bs; decidable_of_iff _ SubsLt.cons_iff.symm

instance : DecidableRel Act.lt := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∧ _))

theorem OptLt.acc : ∀ a, Acc OptLt a
  | none => ⟨_, fun b h => by cases b <;> simp [OptLt] at h⟩
  | some v => by
    induction Value.lt_wf.apply v with
    | intro v _ ih =>
      exact ⟨_, fun b h => by
        cases b with
        | none => simp [OptLt] at h
        | some w => exact ih w h⟩

theorem SubsLt.acc_len : ∀ n (as : List (Option Value)), as.length = n → Acc SubsLt as
  | 0, as, h => ⟨_, fun _ hb => absurd (List.length_eq_zero_iff.1 h ▸ hb) SubsLt.nil_right⟩
  | _ + 1, [], h => by simp at h
  | n + 1, a :: as, h => by
    have ih := SubsLt.acc_len n
    suffices ∀ a, Acc OptLt a → ∀ as, Acc SubsLt as → as.length = n → Acc SubsLt (a :: as) from
      this a (OptLt.acc a) as (ih as (by simpa using h)) (by simpa using h)
    intro a ha
    induction ha with
    | intro a _ iha =>
      intro as has
      induction has with
      | intro as _ ihs =>
        intro hl
        refine ⟨_, fun cs hc => ?_⟩
        match cs, hc with
        | [], hc => exact absurd hc SubsLt.nil_left
        | c :: cs, hc =>
          rcases SubsLt.cons_iff.1 hc with ⟨hl', hca⟩ | ⟨rfl, hcs⟩
          · exact iha c hca cs (ih cs (by omega)) (by omega)
          · exact ihs cs hcs (hcs.1.trans hl)

theorem Act.lt_wf : WellFounded Act.lt := by
  suffices ∀ g subs, Acc Act.lt ⟨g, subs⟩ from ⟨fun ⟨g, subs⟩ => this g subs⟩
  intro g
  induction g using Nat.strongRecOn with
  | _ g ihg =>
    intro subs
    induction SubsLt.acc_len _ subs rfl with
    | intro subs _ ihs =>
      refine ⟨_, fun ⟨g', subs'⟩ h => ?_⟩
      rcases h with h | ⟨h, hs⟩
      · exact ihg g' h subs'
      · cases h; exact ihs subs' hs

instance : WellFoundedRelation Act := ⟨Act.lt, Act.lt_wf⟩

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

theorem pickBranch_mem {m v bs b} (h : pickBranch m v bs = .ok b) : b ∈ bs := by
  unfold pickBranch at h
  split at h
  · split at h <;> simp_all [pure, Except.pure]
  · split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact List.mem_of_find?_eq_some ‹_›
      · cases h
    · cases h

/-- The measure of a call to `d` with arguments `vs`. -/
def calleeAct (d : FnDef) (vs : List Value) : Act :=
  let s := (d.subterm.zip vs).filterMap fun (b, v) => if b then some (some v) else none
  ⟨d.group, s ++ List.replicate (d.pad - s.length) none⟩

/-- The measure of top-level code: above every function's group. -/
def Act.top (F : Fns) : Act := ⟨F.foldr (fun d n => max d.group n) 0 + 1, []⟩

theorem Act.lt_top {F : Fns} {n d} (h : F.find n = some d) (vs : List Value) :
    Act.lt (calleeAct d vs) (Act.top F) := by
  refine Act.lt_of_group ?_
  have hm := List.mem_of_find?_eq_some h
  simp only [calleeAct, Act.top]
  clear h
  induction F with
  | nil => cases hm
  | cons e F ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hm with rfl | hm
    · omega
    · have := ih hm; omega

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

macro "eval_decreasing" : tactic =>
  `(tactic| first | exact Prod.Lex.left _ _ ‹_› | (apply Prod.Lex.right; simp <;> omega))

mutual
  /-- Evaluates an expression under the activation `act` (§11). -/
  def evalExpr (P : Prog) (act : Act) (env : Env) : Expr → Except String (List Value)
    | .var x => match x.name.bind (List.lookup · env) with
      | some v => pure [v]
      | none => throw s!"unbound {x.name}"
    | .app h args => do
      let vs ← evalList P act env (args.map Arg.expr)
      match P.fns.find h.name with
      | some d =>
        if _ : Act.lt (calleeAct d vs) act then do
          take d.returns (← evalExpr P (calleeAct d vs) (← bindIds d.globals d.params vs) d.body)
        else throw s!"the call to {h.name} does not decrease"
      | none => match P.kind h.name with
        | some k => pure [.app ⟨k, h.name⟩ vs]
        | none => throw s!"unknown name {h.name}"
    | .tuple _ es => evalList P act env es
    | .block ss e => evalBlock P act env ss e
    | .match _ m s ann bs => do
      let v ← one (← evalExpr P act env s)
      match _ : pickBranch m v bs with
      | .ok br => do annTake ann (← evalExpr P act (← bindPattern env m br.pat v) br.body)
      | .error e => throw e
    | .sorry _ _ => throw "sorry was reached"
    | .removed => pure [.removed]
  termination_by e => (act, sizeOf e)
  decreasing_by
    all_goals
      try have := sizeOf_body_lt (pickBranch_mem ‹_›)
      try have := sizeOf_map_expr args
      eval_decreasing
  /-- Evaluates expressions left to right, each to one value. -/
  def evalList (P : Prog) (act : Act) (env : Env) : List Expr → Except String (List Value)
    | [] => pure []
    | e :: es => do
      let v ← one (← evalExpr P act env e)
      pure (v :: (← evalList P act env es))
  termination_by es => (act, sizeOf es)
  decreasing_by all_goals eval_decreasing
  def evalBlock (P : Prog) (act : Act) (env : Env) : List Stmt → Expr → Except String (List Value)
    | [], e => evalExpr P act env e
    | s :: ss, e => do evalBlock P act (← evalStmt P act env s) ss e
  termination_by ss e => (act, sizeOf ss + sizeOf e)
  decreasing_by all_goals eval_decreasing
  /-- Runs a statement, giving the environment after it. -/
  def evalStmt (P : Prog) (act : Act) (env : Env) : Stmt → Except String Env
    | .let _ bs rhs => do bindIds env (bs.map (·.name)) (← take bs.length (← evalExpr P act env rhs))
    | .patlet _ _ m pat rhs => do bindPattern env m pat (← one (← evalExpr P act env rhs))
    | .inspect _ => pure env
  termination_by s => (act, sizeOf s)
  decreasing_by all_goals eval_decreasing
end

section Unfold
variable {P : Prog} {act : Act} {env : Env}

theorem ok_bind {ε α β} {a : α} {f : α → Except ε β} : (Except.ok a >>= f) = f a := rfl

theorem error_bind {ε α β} {e : ε} {f : α → Except ε β} : (Except.error e >>= f) = .error e := rfl

theorem bind_eq_ok {ε α β} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem evalExpr_var {x : Id} : evalExpr P act env (.var x) = (match x.name.bind (List.lookup · env) with
    | some v => pure [v]
    | none => throw s!"unbound {x.name}") := by
  rw [evalExpr]

theorem evalExpr_app {h : Name} {args : List Arg} : evalExpr P act env (.app h args) = (do
    let vs ← evalList P act env (args.map Arg.expr)
    match P.fns.find h.name with
    | some d =>
      if Act.lt (calleeAct d vs) act then do
        take d.returns (← evalExpr P (calleeAct d vs) (← bindIds d.globals d.params vs) d.body)
      else throw s!"the call to {h.name} does not decrease"
    | none => match P.kind h.name with
      | some k => pure [.app ⟨k, h.name⟩ vs]
      | none => throw s!"unknown name {h.name}") := by
  rw [evalExpr]; rfl

/-- A call whose arguments evaluate to `vs` and whose measure decreases runs the callee's body. -/
theorem evalExpr_call {h : Name} {args : List Arg} {vs : List Value} {d : FnDef}
    (hvs : evalList P act env (args.map Arg.expr) = .ok vs) (hd : P.fns.find h.name = some d)
    (hlt : Act.lt (calleeAct d vs) act) : evalExpr P act env (.app h args) = (do
      take d.returns (← evalExpr P (calleeAct d vs) (← bindIds d.globals d.params vs) d.body)) := by
  rw [evalExpr_app, hvs, ok_bind]; simp only [hd, hlt, ite_true]

/-- An application of a type constructor or value constructor builds a value. -/
theorem evalExpr_ctor {h : Name} {args : List Arg} {vs : List Value} {k : HeadKind}
    (hvs : evalList P act env (args.map Arg.expr) = .ok vs) (hd : P.fns.find h.name = none)
    (hk : P.kind h.name = some k) : evalExpr P act env (.app h args) = .ok [.app ⟨k, h.name⟩ vs] := by
  rw [evalExpr_app, hvs, ok_bind]; simp only [hd, hk]; rfl

theorem evalExpr_tuple {p : Pos} {es : List Expr} : evalExpr P act env (.tuple p es) = evalList P act env es := by
  rw [evalExpr]

theorem evalExpr_block {ss : List Stmt} {e : Expr} :
    evalExpr P act env (.block ss e) = evalBlock P act env ss e := by
  rw [evalExpr]

theorem evalExpr_match {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch} :
    evalExpr P act env (.match p m s ann bs) = (do
      let v ← one (← evalExpr P act env s)
      let br ← pickBranch m v bs
      annTake ann (← evalExpr P act (← bindPattern env m br.pat v) br.body)) := by
  rw [evalExpr]
  cases evalExpr P act env s with
  | error => rfl
  | ok vs =>
    simp only [ok_bind]
    cases one vs with
    | error => rfl
    | ok v => simp only [ok_bind]; split <;> simp_all [bind, Except.bind] <;> rfl

theorem evalExpr_sorry {p : Pos} {t : Tele} : evalExpr P act env (.sorry p t) = throw "sorry was reached" := by
  rw [evalExpr]

theorem evalExpr_removed : evalExpr P act env .removed = .ok [.removed] := by
  rw [evalExpr]; rfl

theorem evalList_nil : evalList P act env [] = .ok [] := by
  rw [evalList]; rfl

theorem evalList_cons {e : Expr} {es : List Expr} : evalList P act env (e :: es) = (do
    let v ← one (← evalExpr P act env e)
    pure (v :: (← evalList P act env es))) := by
  rw [evalList]

theorem evalBlock_nil {e : Expr} : evalBlock P act env [] e = evalExpr P act env e := by
  rw [evalBlock]

theorem evalBlock_cons {s : Stmt} {ss : List Stmt} {e : Expr} :
    evalBlock P act env (s :: ss) e = (do evalBlock P act (← evalStmt P act env s) ss e) := by
  rw [evalBlock]

theorem evalStmt_let {p : Pos} {bs : List LetBinder} {rhs : Expr} : evalStmt P act env (.let p bs rhs) = (do
    bindIds env (bs.map (·.name)) (← take bs.length (← evalExpr P act env rhs))) := by
  rw [evalStmt]

theorem evalStmt_patlet {p : Pos} {c : Bool} {m : Option Mult} {pat : Pattern} {rhs : Expr} :
    evalStmt P act env (.patlet p c m pat rhs) =
      (do bindPattern env m pat (← one (← evalExpr P act env rhs))) := by
  rw [evalStmt]

theorem evalStmt_inspect {p : Pos} : evalStmt P act env (.inspect p) = .ok env := by
  rw [evalStmt]; rfl

end Unfold

/-- `P'` extends `P`: it keeps `P`'s functions, and keeps every name `P` takes for a type
constructor or value constructor as one of the same kind. -/
structure Prog.Ext (P P' : Prog) : Prop where
  fns : ∀ n d, P.fns.find n = some d → P'.fns.find n = some d
  kind : ∀ n k, P.fns.find n = none → P.kind n = some k → P'.fns.find n = none ∧ P'.kind n = some k

mutual
  /-- Evaluation that succeeds is unchanged by extending the program. -/
  theorem evalExpr_ext {P P' : Prog} (hP : P.Ext P') {act : Act} {env : Env} {vs : List Value} :
      (e : Expr) → evalExpr P act env e = .ok vs → evalExpr P' act env e = .ok vs
    | .var _, h => by rw [evalExpr_var] at h ⊢; exact h
    | .app f args, h => by
      rw [evalExpr_app] at h ⊢
      obtain ⟨ws, hl, h⟩ := bind_eq_ok.1 h
      rw [evalList_ext hP (args.map Arg.expr) hl, ok_bind]
      split at h
      · rename_i d hd
        rw [hP.fns _ _ hd]
        simp only at h ⊢
        split at h
        · rename_i hlt
          simp only [hlt, ite_true]
          obtain ⟨env', hb, h⟩ := bind_eq_ok.1 h
          obtain ⟨rs, hr, h⟩ := bind_eq_ok.1 h
          rw [hb, ok_bind, evalExpr_ext hP d.body hr, ok_bind]; exact h
        · cases h
      · rename_i hd
        split at h
        · rename_i k hk
          obtain ⟨hd', hk'⟩ := hP.kind _ _ hd hk
          simp only [hd', hk']; exact h
        · cases h
    | .tuple _ es, h => by rw [evalExpr_tuple] at h ⊢; exact evalList_ext hP es h
    | .block ss e, h => by rw [evalExpr_block] at h ⊢; exact evalBlock_ext hP ss e h
    | .match _ m s ann bs, h => by
      rw [evalExpr_match] at h ⊢
      obtain ⟨ws, hs, h⟩ := bind_eq_ok.1 h
      obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
      obtain ⟨br, hbr, h⟩ := bind_eq_ok.1 h
      obtain ⟨env', hb, h⟩ := bind_eq_ok.1 h
      obtain ⟨rs, hr, h⟩ := bind_eq_ok.1 h
      have := sizeOf_body_lt (pickBranch_mem hbr)
      rw [evalExpr_ext hP s hs, ok_bind, hv, ok_bind, hbr, ok_bind, hb, ok_bind, evalExpr_ext hP br.body hr, ok_bind]
      exact h
    | .sorry _ _, h => by rw [evalExpr_sorry] at h; cases h
    | .removed, h => by rw [evalExpr_removed] at h ⊢; exact h
  termination_by e => (act, sizeOf e)
  decreasing_by
    all_goals
      try have := sizeOf_map_expr args
      eval_decreasing
  theorem evalList_ext {P P' : Prog} (hP : P.Ext P') {act : Act} {env : Env} {vs : List Value} :
      (es : List Expr) → evalList P act env es = .ok vs → evalList P' act env es = .ok vs
    | [], h => by rw [evalList_nil] at h ⊢; exact h
    | e :: es, h => by
      rw [evalList_cons] at h ⊢
      obtain ⟨ws, he, h⟩ := bind_eq_ok.1 h
      obtain ⟨v, hv, h⟩ := bind_eq_ok.1 h
      obtain ⟨us, hs, h⟩ := bind_eq_ok.1 h
      rw [evalExpr_ext hP e he, ok_bind, hv, ok_bind, evalList_ext hP es hs, ok_bind]; exact h
  termination_by es => (act, sizeOf es)
  decreasing_by all_goals eval_decreasing
  theorem evalBlock_ext {P P' : Prog} (hP : P.Ext P') {act : Act} {env : Env} {vs : List Value} :
      (ss : List Stmt) → (e : Expr) → evalBlock P act env ss e = .ok vs → evalBlock P' act env ss e = .ok vs
    | [], e, h => by rw [evalBlock_nil] at h ⊢; exact evalExpr_ext hP e h
    | s :: ss, e, h => by
      rw [evalBlock_cons] at h ⊢
      obtain ⟨env', hs, h⟩ := bind_eq_ok.1 h
      rw [evalStmt_ext hP s hs, ok_bind]; exact evalBlock_ext hP ss e h
  termination_by ss e => (act, sizeOf ss + sizeOf e)
  decreasing_by all_goals eval_decreasing
  theorem evalStmt_ext {P P' : Prog} (hP : P.Ext P') {act : Act} {env env' : Env} :
      (s : Stmt) → evalStmt P act env s = .ok env' → evalStmt P' act env s = .ok env'
    | .let _ bs rhs, h => by
      rw [evalStmt_let] at h ⊢
      obtain ⟨ws, he, h⟩ := bind_eq_ok.1 h
      rw [evalExpr_ext hP rhs he, ok_bind]; exact h
    | .patlet _ _ m pat rhs, h => by
      rw [evalStmt_patlet] at h ⊢
      obtain ⟨ws, he, h⟩ := bind_eq_ok.1 h
      rw [evalExpr_ext hP rhs he, ok_bind]; exact h
    | .inspect _, h => by rw [evalStmt_inspect] at h ⊢; exact h
  termination_by s => (act, sizeOf s)
  decreasing_by all_goals eval_decreasing
end

end Pledge
