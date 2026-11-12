import Pledge.Sound.InternalTop

namespace Pledge.Parser

/-- A token as the lexer gives it: a name token is not `sorry`. -/
def Token.ok (t : Token) : Prop := t.kind = .name → t.text ≠ "sorry"

def St.ok {b : Nat} (s : St b) : Prop := (∀ t ∈ s.toks, Token.ok t) ∧ Token.ok s.last

/-- From a state of tokens as the lexer gives them, `x` succeeds only with a result meeting `P`, leaving such a
state. -/
def Ok {b : Nat} {α : Type} (x : M b α) (P : α → Prop) : Prop :=
  ∀ s : St b, s.ok → ∀ a s', x s = .ok (a, s') → P a ∧ s'.ok

namespace Ok

variable {b : Nat} {α β : Type} {x : M b α} {P Q : α → Prop}

theorem bind {f : α → M b β} {R : β → Prop} (hx : Ok x Q) (hf : ∀ a, Q a → Ok (f a) R) : Ok (x >>= f) R := by
  intro s hs c s' h
  simp only [Bind.bind, StateT.bind] at h
  cases hxs : x s with
  | error e => simp [hxs, Except.bind] at h
  | ok r =>
    obtain ⟨a, s1⟩ := r
    simp only [hxs, Except.bind] at h
    obtain ⟨hq, h1⟩ := hx s hs a s1 hxs
    exact hf a hq s1 h1 c s' h

theorem pure {a : α} (h : P a) : Ok (Pure.pure a : M b α) P := by
  intro s hs c s' hc
  simp only [Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact ⟨h, hs⟩

theorem imp (h : Ok x Q) (hq : ∀ a, Q a → P a) : Ok x P := fun s hs a s' hx =>
  let ⟨h1, h2⟩ := h s hs a s' hx; ⟨hq a h1, h2⟩

theorem fail {t : Token} {m : Unit → String} : Ok (Parser.fail t m : M b α) P := by
  intro s _ a s' h
  simp [Parser.fail, throw, throwThe, MonadExceptOf.throw, StateT.lift, Bind.bind, Except.bind] at h

theorem next : Ok (Parser.next : M b Token) Token.ok := by
  intro s hs a s' h
  obtain ⟨toks, l, hl⟩ := s
  cases toks with
  | nil => simp only [Parser.next, Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hs.2, hs⟩
  | cons t r =>
    simp only [Parser.next, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hs.1 _ List.mem_cons_self, fun u hu => hs.1 u (List.mem_cons_of_mem _ hu), hs.2⟩

theorem peekAt {k : Nat} : Ok (Parser.peekAt k : M b Token) Token.ok := by
  intro s hs a s' h
  simp only [Parser.peekAt, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, Pure.pure,
    StateT.pure, Except.pure, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, hs⟩
  rw [List.getD_eq_getElem?_getD]
  cases hk : s.toks[k]? with
  | none => exact hs.2
  | some t => exact hs.1 t (List.mem_of_getElem? hk)

theorem map {f : α → β} {R : β → Prop} (h : Ok x Q) (hf : ∀ a, Q a → R (f a)) : Ok (f <$> x) R := by
  rw [map_eq_pure_bind]; exact h.bind fun a ha => Ok.pure (hf a ha)

theorem seqRight {y : M b β} {R : β → Prop} (hx : Ok x Q) (hy : Ok y R) : Ok (x *> y) R := by
  rw [seqRight_eq_bind]; exact hx.bind fun _ _ => hy

theorem seqLeft {y : M b β} {R : β → Prop} (hx : Ok x P) (hy : Ok y R) : Ok (x <* y) P := by
  rw [seqLeft_eq_bind]; exact hx.bind fun a ha => hy.bind fun _ _ => Ok.pure ha

theorem tryCatch {h : Err → M b α} (hx : Ok x P) (hh : ∀ e, Ok (h e) P) : Ok (tryCatch x h) P := by
  intro s hs a s' hc
  simp only [MonadExcept.tryCatch, MonadExceptOf.tryCatch, tryCatchThe] at hc
  cases hxs : x s with
  | ok r =>
    rw [hxs] at hc
    simp only [Except.tryCatch, Except.ok.injEq] at hc
    subst hc; exact hx s hs a s' hxs
  | error e => rw [hxs] at hc; exact hh e s hs a s' (by simpa [Except.tryCatch] using hc)

theorem discard {Q : α → Prop} (h : Ok x Q) : Ok (Functor.discard x) (fun _ => True) := by
  simp only [Functor.discard, map_const, Function.comp_apply]; exact h.map fun _ _ => trivial

theorem peek : Ok (Parser.peek : M b Token) Token.ok := peekAt

theorem see {text : String} : Ok (Parser.see text : M b Bool) (fun _ => True) := peek.map fun _ _ => trivial

theorem eat {text : String} : Ok (Parser.eat text : M b Bool) (fun _ => True) := by
  unfold Parser.eat
  refine see.bind fun c _ => ?_
  split
  · exact (discard next).bind fun _ _ => Ok.pure trivial
  · exact Ok.pure trivial

theorem expect {text : String} : Ok (Parser.expect text : M b Unit) (fun _ => True) := by
  unfold Parser.expect
  refine next.bind fun t _ => ?_
  split
  · exact Ok.pure trivial
  · exact fail

theorem failHere {m : Unit → String} : Ok (Parser.failHere m : M b α) P := peek.bind fun _ _ => fail

theorem many {step : M b (Option α)} (h : Ok step (fun o => ∀ a, o = some a → P a)) :
    Ok (Parser.many step) (fun l => ∀ a ∈ l, P a) := by
  unfold Parser.many
  suffices ∀ n (s : St b), s.toks.length = n → s.ok → ∀ l s', many.go step s = .ok (l, s') →
      (∀ a ∈ l, P a) ∧ s'.ok from fun s hs l s' hg => this _ s rfl hs l s' hg
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro s hn hs l s' hg
  rw [many.go] at hg
  cases hst : step s with
  | error e => simp [hst, Bind.bind, Except.bind] at hg
  | ok r =>
    obtain ⟨o, s1⟩ := r
    obtain ⟨ho, hs1⟩ := h s hs o s1 hst
    simp only [hst, Bind.bind, Except.bind] at hg
    cases o with
    | none =>
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨by simp, hs1⟩
    | some a =>
      simp only at hg
      split at hg
      · rename_i hlt
        cases hgo : many.go step s1 with
        | error e => simp [hgo] at hg
        | ok r2 =>
          obtain ⟨as, s2⟩ := r2
          simp only [hgo, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hg
          obtain ⟨rfl, rfl⟩ := hg
          obtain ⟨h1, h2⟩ := ih _ (hn ▸ hlt) s1 rfl hs1 as s2 hgo
          exact ⟨fun x hx => (List.mem_cons.1 hx).elim (fun e => e ▸ ho a rfl) (h1 x), h2⟩
      · simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hg
        obtain ⟨rfl, rfl⟩ := hg
        exact ⟨by simpa using ho a rfl, hs1⟩

theorem whenTok {p : Token → Bool} {k : Token → M b α} (hk : ∀ t, Token.ok t → Ok (k t) P) :
    Ok (Parser.whenTok p k) (fun o => ∀ a, o = some a → P a) := by
  unfold Parser.whenTok
  refine peek.bind fun t ht => ?_
  split
  · exact (discard next).bind fun _ _ => (hk t ht).map fun a ha a' he => by cases he; exact ha
  · exact Ok.pure fun _ h => by cases h

theorem manyAfter {text : String} {item : M b α} (h : Ok item P) :
    Ok (Parser.manyAfter text item) (fun l => ∀ a ∈ l, P a) := many (whenTok fun _ _ => h)

theorem skipSemis : Ok (Parser.skipSemis : M b Unit) (fun _ => True) :=
  discard (manyAfter (P := fun _ => True) (Ok.pure trivial))

theorem endStatement : Ok (Parser.endStatement : M b Unit) (fun _ => True) := expect.seqRight skipSemis

theorem commaList {item : M b α} {close : String} {minOne : Bool} (h : Ok item P) :
    Ok (Parser.commaList item close minOne) (fun l => (∀ a ∈ l, P a) ∧ (minOne = true → l ≠ [])) := by
  unfold Parser.commaList
  refine (if hm : minOne = true then ?_ else ?_)
  · simp only [hm, Bool.true_or, ↓reduceIte]
    exact h.bind fun a ha => (manyAfter h).bind fun l hl =>
      Ok.pure ⟨fun x hx => (List.mem_cons.1 hx).elim (fun e => e ▸ ha) (hl x), fun _ => by simp⟩
  · simp only [Bool.eq_false_iff.2 hm, Bool.false_or]
    refine see.bind fun c _ => ?_
    split
    · exact h.bind fun a ha => (manyAfter h).bind fun l hl =>
        Ok.pure ⟨fun x hx => (List.mem_cons.1 hx).elim (fun e => e ▸ ha) (hl x), fun _ => by simp⟩
    · exact Ok.pure ⟨by simp, fun e => by cases e⟩

theorem parensAfter {item : M b α} {minOne : Bool} (h : Ok item P) :
    Ok (Parser.parensAfter item minOne) (fun l => (∀ a ∈ l, P a) ∧ (minOne = true → l ≠ [])) :=
  (commaList h).seqLeft expect

theorem parens {item : M b α} {minOne : Bool} (h : Ok item P) :
    Ok (Parser.parens item minOne) (fun l => (∀ a ∈ l, P a) ∧ (minOne = true → l ≠ [])) :=
  expect.seqRight (parensAfter h)

theorem braces {item : M b α} (h : Ok item P) : Ok (Parser.braces item) (fun l => ∀ a ∈ l, P a) := by
  unfold Parser.braces
  refine (expect.seqRight (many ?_)).seqLeft expect
  refine see.bind fun c _ => ?_
  split
  · exact Ok.pure fun _ h => by cases h
  · exact h.map fun a ha a' he => by cases he; exact ha

theorem fix {f : {c : Nat} → M c α → Token → M c α}
    (hf : ∀ {c : Nat} (r : M c α), Ok r P → ∀ t, Token.ok t → Ok (f r t) P) : ∀ {n : Nat}, Ok (Parser.fix (n := n) f) P := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro s hs a s' h
  rw [Parser.fix] at h
  split at h
  · exact hf _ fail s.last hs.2 s hs a s' h
  · rename_i t rest heq
    have hlt : rest.length < n := by have := s.le; rw [heq] at this; simp at this; omega
    have hr : Ok (fun s' => Parser.fix f s' : M rest.length α) P := ih _ hlt
    have hst : (⟨rest, s.last, Nat.le_refl _⟩ : St rest.length).ok :=
      ⟨fun u hu => hs.1 u (by rw [heq]; exact List.mem_cons_of_mem _ hu), hs.2⟩
    cases hfs : f (fun s' => Parser.fix f s') t ⟨rest, s.last, Nat.le_refl _⟩ with
    | error e => simp [hfs, Bind.bind, Except.bind] at h
    | ok r =>
      obtain ⟨a', s1⟩ := r
      simp only [hfs, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := hf _ hr t (hs.1 t (by rw [heq]; exact List.mem_cons_self)) _ hst a' s1 hfs
      exact ⟨h1, h2⟩

end Ok

theorem Expr.shapedArgs_iff : ∀ {as : List Arg}, Expr.shapedArgs as = true ↔ ∀ a ∈ as, a.expr.shaped = true
  | [] => by simp [Expr.shapedArgs]
  | .mk _ e :: as => by simp [Expr.shapedArgs, Expr.shapedArgs_iff, Arg.expr]

theorem Expr.shapedList_iff : ∀ {es : List Expr}, Expr.shapedList es = true ↔ ∀ e ∈ es, e.shaped = true
  | [] => by simp [Expr.shapedList]
  | e :: es => by simp [Expr.shapedList, Expr.shapedList_iff]

theorem Expr.shapedStmts_iff : ∀ {ss : List Stmt}, Expr.shapedStmts ss = true ↔ ∀ s ∈ ss, s.shaped = true
  | [] => by simp [Expr.shapedStmts]
  | s :: ss => by simp [Expr.shapedStmts, Expr.shapedStmts_iff]

theorem Expr.shapedBranches_iff : ∀ {bs : List Branch},
    Expr.shapedBranches bs = true ↔ ∀ b ∈ bs, b.body.shaped = true
  | [] => by simp [Expr.shapedBranches]
  | .mk _ e :: bs => by simp [Expr.shapedBranches, Expr.shapedBranches_iff, Branch.body]

theorem Top.shaped_stmt {s : Stmt} (h : s.shaped = true) : (Top.stmt s).shaped = true := by
  cases s with
  | patlet p ct m pat rhs => cases ct <;> simp_all [Top.shaped, Stmt.shaped]
  | _ => simpa [Top.shaped] using h

theorem Kind.eq_name {k : Kind} (h : (k == .name) = true) : k = .name := by
  cases k <;> first | rfl | nomatch h

namespace Ok

variable {b : Nat}

theorem nameOf {t : Token} (ht : Token.ok t) : Ok (Parser.nameOf t : M b Name) (·.name ≠ "sorry") := by
  unfold Parser.nameOf
  split
  · rename_i hk; exact Ok.pure (ht (Kind.eq_name hk))
  · exact fail

theorem name : Ok (Parser.name : M b Name) (·.name ≠ "sorry") := next.bind fun _ ht => nameOf ht

theorem tryCatch' {α : Type} {x : M b α} {h : Err → M b α} {P : α → Prop} (hx : Ok x P) (hh : ∀ e, Ok (h e) P) :
    Ok (MonadExcept.tryCatch x h) P := Ok.tryCatch hx hh

end Ok

set_option hygiene false in
/-- Proves `Ok` of a parser built from the ones before it: binds, `if`s and `match`es are taken apart, and what is
returned meets the predicate by `simp_all`. -/
macro "ok_auto" : tactic => `(tactic| (
  (try simp only [map_eq_pure_bind, seqRight_eq_bind, seqLeft_eq_bind, Functor.discard, map_const,
    Function.comp_apply, Parser.expected, Parser.failHere]);
  repeat' (first
    | exact Ok.fail | exact Ok.failHere
    | rw [map_eq_pure_bind] | rw [seqRight_eq_bind] | rw [seqLeft_eq_bind] | rw [bind_assoc] | rw [pure_bind]
    | exact Ok.pure ⟨_, _, _, rfl, by assumption⟩
    | (refine Ok.pure ?_; exact Top.shaped_stmt ‹_›)
    | (refine Ok.pure ?_; simp only [Top.shaped, List.all_eq_true]; assumption)
    | (refine Ok.pure ?_; obtain ⟨_, _, _, rfl, h⟩ := ‹∃ _ _ _, _›; exact h)
    | (refine Ok.pure ?_; simp_all [Expr.shaped, Stmt.shaped, Tele.shaped, Top.shaped, Data.shaped, Fn.shaped,
        Expr.shapedArgs_iff, Expr.shapedList_iff, Expr.shapedStmts_iff, Expr.shapedBranches_iff, Arg.expr, Branch.body,
        imp_and, forall_and]; done)
    | (apply Ok.bind; (first
        | exact Ok.next | exact Ok.discard Ok.next | exact Ok.parens ‹_› | exact Ok.peek | exact Ok.peekAt | exact Ok.see | exact Ok.eat | exact Ok.expect
        | exact Ok.endStatement | exact Ok.skipSemis | exact Ok.name | exact Ok.nameOf ‹_›
        | exact Ok.id | exact Ok.mult | exact Ok.term | exact Ok.annOpt | exact Ok.letBinder | exact Ok.binder
        | exact Ok.tele | exact Ok.hole | exact Ok.param | exact Ok.field | exact Ok.pattern | exact Ok.atPatLet
        | exact Ok.expr | exact Ok.data | exact Ok.header | exact Ok.fn | exact Ok.mutualAfter | exact Ok.topAfter
        | exact Ok.patLet ‹_› | exact Ok.stmtAfter ‹_› | exact Ok.blockAfter ‹_› | exact Ok.arg ‹_›
        | exact Ok.parens Ok.binder | exact Ok.parens Ok.letBinder | exact Ok.parens Ok.param
        | exact Ok.parens Ok.field | exact Ok.parens (Ok.arg ‹_›) | exact Ok.parensAfter ‹_›
        | exact Ok.commaList Ok.binder | exact Ok.manyAfter Ok.data | exact Ok.manyAfter Ok.fn
        | exact Ok.many (Ok.whenTok fun _ _ => Ok.stmtAfter ‹_›)
        | exact Ok.whenTok (P := fun _ => True) fun _ _ => Ok.pure trivial
        | assumption); intro _ _)
    | split)))

namespace Ok

variable {b : Nat}

theorem id : Ok (Parser.id : M b Id) (fun _ => True) := by unfold Parser.id; ok_auto
theorem mult : Ok (Parser.mult : M b (Option Mult)) (fun _ => True) := by unfold Parser.mult; ok_auto
theorem term : Ok (Parser.term : M b WTerm) (fun _ => True) := by
  unfold Parser.term; exact fix fun r hr t ht => by ok_auto
theorem annOpt : Ok (Parser.annOpt : M b (Option Ann)) (fun _ => True) := by unfold Parser.annOpt; ok_auto
theorem letBinder {m : Bool} : Ok (Parser.letBinder m : M b LetBinder) (fun _ => True) := by
  unfold Parser.letBinder; ok_auto
theorem binder {m : Bool} : Ok (Parser.binder m : M b Binder) (fun _ => True) := by unfold Parser.binder; ok_auto
theorem tele : Ok (Parser.tele : M b (List Binder)) (· ≠ []) := (parens binder).imp fun _ h => h.2 rfl
theorem hole : Ok (Parser.hole : M b Tele) (·.shaped = true) := by
  unfold Parser.hole; ok_auto
theorem param : Ok (Parser.param : M b Param) (fun _ => True) := by unfold Parser.param; ok_auto
theorem field : Ok (Parser.field : M b Id) (fun _ => True) := by unfold Parser.field; ok_auto
theorem pattern : Ok (Parser.pattern : M b Pattern) (fun _ => True) := by unfold Parser.pattern; ok_auto
theorem atPatLet : Ok (Parser.atPatLet : M b Bool) (fun _ => True) := by unfold Parser.atPatLet; ok_auto

theorem patLet {pos : Pos} {ct : Bool} {e : M b Expr} (he : Ok e (·.shaped = true)) :
    Ok (Parser.patLet pos ct e) (fun s => ∃ m pat rhs, s = .patlet pos ct m pat rhs ∧ rhs.shaped = true) := by
  unfold Parser.patLet; ok_auto

theorem stmtAfter {e : M b Expr} (he : Ok e (·.shaped = true)) {t : Token} :
    Ok (Parser.stmtAfter e t) (·.shaped = true) := by
  unfold Parser.stmtAfter; ok_auto

theorem blockAfter {e : M b Expr} (he : Ok e (·.shaped = true)) : Ok (Parser.blockAfter e) (·.shaped = true) := by
  unfold Parser.blockAfter; ok_auto

theorem arg {e : M b Expr} (he : Ok e (·.shaped = true)) : Ok (Parser.arg e) (·.expr.shaped = true) := by
  unfold Parser.arg; ok_auto

theorem branch {e : M b Expr} (he : Ok e (·.shaped = true)) :
    Ok (do
      let pat ← Parser.pattern
      Parser.expect "=>"
      let body ← e
      Parser.endStatement
      Pure.pure (Branch.mk pat body)) (·.body.shaped = true) := by ok_auto

theorem expr : Ok (Parser.expr : M b Expr) (·.shaped = true) := by
  unfold Parser.expr
  refine fix fun r hr t ht => ?_
  have hb := braces (branch hr)
  ok_auto

theorem ctor : Ok (do
      let c ← Parser.name
      let fs ← Parser.parens (Parser.binder true) false
      Parser.expect ":"
      let r ← Parser.term
      Parser.endStatement
      Pure.pure (⟨c, fs, r⟩ : Ctor) : M b Ctor) (·.name.name ≠ "sorry") := by ok_auto

theorem data : Ok (Parser.data : M b Data) (·.shaped = true) := by
  unfold Parser.data
  have hp := parens (b := b) (minOne := false) (P := fun _ => True) (item := do
    let i ← Parser.id; Parser.expect ":"; Pure.pure (⟨i, .type (← Parser.term), none⟩ : Binder)) (by ok_auto)
  have hc := braces ctor (b := b)
  ok_auto

theorem header : Ok (Parser.header : M b Header) (·.returns ≠ []) := by unfold Parser.header; ok_auto

theorem fn : Ok (Parser.fn : M b Fn) (·.shaped = true) := by
  unfold Parser.fn
  have he := expr (b := b)
  ok_auto

theorem mutualAfter {pos : Pos} : Ok (Parser.mutualAfter pos : M b Top) (·.shaped = true) := by
  unfold Parser.mutualAfter; ok_auto

theorem topAfter {t : Token} : Ok (Parser.topAfter t : M b Top) (·.shaped = true) := by
  unfold Parser.topAfter
  have he := expr (b := b)
  ok_auto

theorem program : Ok (Parser.program : M b (Program × Option Err)) (fun r => ∀ t ∈ r.1, t.shaped = true) := by
  unfold Parser.program
  refine fix fun r hr t _ => ?_
  dsimp only
  split
  · exact Ok.pure (by simp)
  · exact Ok.tryCatch' (by ok_auto) fun _ => Ok.pure (by simp)

end Ok

end Pledge.Parser

namespace Pledge


/-- The parser's output meets `Top.shaped`: no `removed` node, no `comptime` below the top level, no type or value
constructor named `sorry`, and at least one element, binder, annotation entry or return where the grammar has one. -/
theorem parse_shaped (source : String) (phase : Nat) : ∀ t ∈ (parse source phase).1, t.shaped = true := by
  unfold parse
  dsimp only
  have hl := lex_name source phase
  have hs : (⟨(lex source phase).dropLast, (lex source phase).getLastD ⟨.eof, "", source.length⟩,
      Nat.le_refl _⟩ : Parser.St _).ok := by
    refine ⟨fun t ht => hl t ((List.dropLast_sublist _).subset ht), ?_⟩
    rw [List.getLastD_eq_getLast?]
    cases h : (lex source phase).getLast? with
    | none => intro hk; cases hk
    | some t => exact hl t (List.mem_of_getLast? h)
  split
  · rename_i tops e s' hp
    exact (Parser.Ok.program _ hs _ _ hp).1
  · simp

/-- `runProgram_noInternal` for source text, with no hypothesis: the error `run` reports for an item is not
internal. -/
theorem run_noInternal (source : String) (phase : Nat) :
    let prog := (parse source phase).1
    ∀ e t n, (checkItems phase (solution phase prog) prog).2.map
        (report (checkItems phase (solution phase prog) prog).1) = some (e, t, n) →
      e.internal = false ∧ (run source phase).error = some (e.pos, e.msg ()) :=
  runProgram_noInternal phase _ _ _ (parse_shaped source phase)

end Pledge
