import Pledge.Sound.Wf
import Pledge.Sound.Shape

namespace Pledge

/-- `x` reports no internal error, and what it returns satisfies `P`. -/
def NoInt {α : Type} (x : CheckM α) (P : α → Prop) : Prop :=
  (∀ e, x = .error e → e.internal = false) ∧ ∀ a, x = .ok a → P a

namespace NoInt

variable {α β : Type} {x : CheckM α} {P Q : α → Prop}

theorem bind {f : α → CheckM β} {R : β → Prop} (hx : NoInt x Q) (hf : ∀ a, Q a → NoInt (f a) R) :
    NoInt (x >>= f) R := by
  refine ⟨fun e h => ?_, fun b h => ?_⟩
  · cases hx' : x with
    | error e' => rw [hx'] at h; cases h; exact hx.1 _ hx'
    | ok a => rw [hx', ok_bind] at h; exact (hf a (hx.2 a hx')).1 e h
  · obtain ⟨a, ha, hb⟩ := bind_eq_ok.1 h
    exact (hf a (hx.2 a ha)).2 b hb

theorem pure {a : α} (h : P a) : NoInt (Pure.pure a : CheckM α) P :=
  ⟨fun _ h => by simp [Pure.pure, Except.pure] at h, fun _ h' => by
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h'; subst h'; exact h⟩

theorem ok {a : α} (hx : x = .ok a) (h : P a) : NoInt x P := hx ▸ NoInt.pure h

theorem failAt {pos : Pos} {m : Unit → String} : NoInt (Pledge.failAt pos m : CheckM α) P :=
  ⟨fun _ h => by simp only [failAt_eq, Except.error.injEq] at h; subst h; rfl, fun _ h => by
    simp [failAt_eq] at h⟩

theorem keep {s : List Snapshot} (h : NoInt x P) : NoInt (Pledge.keep s x) P := by
  cases hx : x with
  | ok a =>
    rw [hx] at h
    exact ⟨fun _ h' => by simp [Pledge.keep] at h', fun b h' => h.2 b (by simpa [Pledge.keep] using h')⟩
  | error e =>
    rw [hx] at h
    refine ⟨fun e' h' => ?_, fun _ h' => by simp [Pledge.keep] at h'⟩
    simp only [Pledge.keep, Except.error.injEq] at h'
    subst h'
    exact h.1 e rfl

theorem failAt_bind {f : α → CheckM β} {R : β → Prop} {pos : Pos} {m : Unit → String} :
    NoInt (Pledge.failAt pos m >>= f) R := NoInt.bind (Q := fun _ => False) failAt fun _ h => h.elim

theorem miscount_bind {f : α → CheckM β} {R : β → Prop} {pos : Pos} {n : Nat} {s : String} :
    NoInt (Pledge.miscount pos n s >>= f) R := NoInt.bind (Q := fun _ => False) failAt fun _ h => h.elim

theorem imp (h : NoInt x Q) (hq : ∀ a, Q a → P a) : NoInt x P := ⟨h.1, fun a ha => hq a (h.2 a ha)⟩

theorem miscount {pos : Pos} {n : Nat} {s : String} : NoInt (Pledge.miscount pos n s : CheckM α) P := failAt

theorem single {pos : Pos} {rs : List Res} : NoInt (Pledge.single pos rs) (fun r => rs = [r]) := by
  unfold Pledge.single; split
  · exact NoInt.pure rfl
  · exact miscount

theorem ensure {b : Bool} {pos : Pos} {s : String} (hb : b = true) : NoInt (Pledge.ensure b pos s) (fun _ => True) := by
  subst hb; exact NoInt.pure trivial

theorem unless_fail {b : Bool} {pos : Pos} {m : Unit → String} :
    NoInt (unless b do Pledge.failAt pos m : CheckM Unit) (fun _ => b = true) := by
  cases b
  · exact failAt
  · exact NoInt.pure rfl

theorem certify (h : NoInt x P) : NoInt (Pledge.certify x) (fun a => P a.1) := by
  cases hx : x with
  | ok a => rw [hx] at h; exact ⟨fun _ h' => by simp [Pledge.certify] at h', fun b h' => by
      simp only [Pledge.certify, Except.ok.injEq] at h'; subst h'; exact h.2 a rfl⟩
  | error e =>
    rw [hx] at h
    refine ⟨fun e' h' => ?_, fun _ h' => by simp [Pledge.certify] at h'⟩
    simp only [Pledge.certify, Except.error.injEq] at h'
    subst h'
    exact h.1 e rfl

theorem arity {pos : Pos} {n : String} {p a : Nat} : NoInt (Pledge.arity pos n p a) (fun _ => a = p) := by
  unfold Pledge.arity; split
  · exact failAt
  · exact NoInt.pure (by omega)

end NoInt

theorem NoInt.forM {γ : Type} {f : γ → CheckM Unit} :
    ∀ {l : List γ}, (∀ a ∈ l, NoInt (f a) (fun _ => True)) → NoInt (l.forM f) (fun _ => True)
  | [], _ => NoInt.pure trivial
  | a :: l, h => by
    rw [List.forM]
    exact NoInt.bind (h a List.mem_cons_self) fun _ _ =>
      NoInt.forM fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem NoInt.mapM {γ δ : Type} {f : γ → CheckM δ} {R : δ → Prop} :
    ∀ {l : List γ}, (∀ a ∈ l, NoInt (f a) R) → NoInt (l.mapM f) (fun l' => l'.length = l.length ∧ ∀ b ∈ l', R b)
  | [], _ => NoInt.pure ⟨rfl, by simp⟩
  | a :: l, h => by
    rw [List.mapM_cons]
    refine NoInt.bind (h a List.mem_cons_self) fun b hb => ?_
    refine NoInt.bind (NoInt.mapM fun c hc => h c (List.mem_cons_of_mem _ hc)) fun bs hbs => NoInt.pure ?_
    exact ⟨by simp [hbs.1], by simpa [hb] using hbs.2⟩

theorem NoInt.foldlM {γ δ : Type} {f : δ → γ → CheckM δ} {I : δ → Prop} :
    ∀ {l : List γ} {init : δ}, I init → (∀ s, I s → ∀ a ∈ l, NoInt (f s a) I) → NoInt (l.foldlM f init) I
  | [], _, hi, _ => NoInt.pure hi
  | a :: l, init, hi, h => by
    rw [List.foldlM_cons]
    exact NoInt.bind (h init hi a List.mem_cons_self) fun s hs =>
      NoInt.foldlM hs fun s' hs' b hb => h s' hs' b (List.mem_cons_of_mem _ hb)

mutual
theorem coreType_wf {S : Sigs} {Γ : Entries} :
    ∀ (t : Term) (ty : Term), coreType S Γ t = some ty → t.wf S Γ.length 0 = true
  | .entry i, _, h => by
    simp only [coreType, Option.map_eq_some_iff] at h
    obtain ⟨en, hen, -⟩ := h
    simpa [Term.wf] using (List.getElem?_eq_some_iff.1 hen).1
  | .bound _, _, h => by simp [coreType] at h
  | .app hd as, ty, h => by
    simp only [coreType, Option.bind_eq_some_iff] at h
    obtain ⟨sig, hs, h⟩ := h
    split at h
    · rename_i hc
      obtain ⟨hl, hw⟩ := coreArgs_wf sig.params [] as hc
      exact Term.wf_app.2 ⟨⟨sig, hs, hl⟩, hw⟩
    · cases h
theorem coreArgs_wf {S : Sigs} {Γ : Entries} :
    ∀ (ps : Telescope) (prev as : List Term), coreArgs S Γ ps prev as = true →
      ps.length = as.length ∧ ∀ a ∈ as, a.wf S Γ.length 0 = true
  | [], _, [], _ => ⟨rfl, by simp⟩
  | p :: ps, prev, a :: as, h => by
    simp only [coreArgs, Bool.and_eq_true, Option.any_eq_true] at h
    obtain ⟨⟨⟨ty, hty, -⟩, -⟩, h⟩ := h
    obtain ⟨hl, hw⟩ := coreArgs_wf ps (prev ++ [a]) as h
    exact ⟨by simp [hl], fun b hb => (List.mem_cons.1 hb).elim (fun e => e ▸ coreType_wf a ty hty) (hw b)⟩
  | [], _, _ :: _, h | _ :: _, _, [], h => by simp [coreArgs] at h
end

/-- What every function checking terms and expressions keeps: a well-formed scope and signatures; names standing for
well-formed terms; and globals with signatures. -/
def GlobOk (gs : List Global) (S : Sigs) (n : Nat) : Prop :=
  ∀ g ∈ gs, match g with
    | .type nm cs _ => (∃ s, S.find ⟨.type, nm⟩ = some s) ∧
        ∀ cs', cs = some cs' → ∀ c ∈ cs', ∃ s, S.find ⟨.ctor, c⟩ = some s
    | .ctor nm => ∃ s, S.find ⟨.ctor, nm⟩ = some s
    | .fn _ (some sig) => Telescope.wf S n 0 sig.params = true ∧
        Telescope.wf S n sig.params.length sig.returns = true ∧ sig.subterm.length = sig.params.length ∧
        sig.returns ≠ []
    | .fn _ none => True

structure ScOk (C : Ctx) (sc : Scope) : Prop where
  Γ : Entries.Wf sc.sigs sc.Γ
  sigs : Sigs.Wf sc.sigs sc.Γ.length
  names : ∀ p ∈ sc.names, p.2.term.wf sc.sigs sc.Γ.length 0 = true
  globals : GlobOk C.globals sc.sigs sc.Γ.length

theorem ScOk.lookup {C : Ctx} {sc : Scope} (h : ScOk C sc) {n : String} {r : Res} (hl : sc.lookup n = some r) :
    r.term.wf sc.sigs sc.Γ.length 0 = true := h.names _ (lookup_mem hl)

theorem ScOk.global {C : Ctx} {sc : Scope} (_h : ScOk C sc) {n : String} {g : Global} (hg : C.global n = some g) :
    g.name = n ∧ g ∈ C.globals := by
  have hm := List.mem_of_find?_eq_some hg
  have := List.find?_some hg
  simp only [beq_iff_eq] at this
  exact ⟨this, hm⟩

theorem meets_noInt {g : Given} {sc : Scope} {pos : Pos} {i : Nat} {w : Want} {env : List Term} {r : Res}
    {has : Term} : NoInt (g.meets sc pos i w env r has) (fun _ => True) := by
  unfold Given.meets
  dsimp only
  repeat' (first | exact NoInt.failAt | exact NoInt.pure trivial | split)

/-- `against` reports no internal error when the results are well-formed. -/
theorem against_noInt {sc : Scope} {g : Given} {pos : Pos} {rs : List Res}
    (hΓ : Entries.Wf sc.sigs sc.Γ) (hS : Sigs.Wf sc.sigs sc.Γ.length)
    (hr : ∀ r ∈ rs, r.term.wf sc.sigs sc.Γ.length 0 = true) : NoInt (against sc g pos rs) (fun _ => True) := by
  unfold against
  dsimp only
  suffices hgo : ∀ prev ws (rs : List Res), (∀ r ∈ rs, r.term.wf sc.sigs sc.Γ.length 0 = true) →
      NoInt (against.go sc g pos prev ws rs) (fun _ => True) by
    split
    · exact NoInt.miscount_bind
    · exact hgo _ _ _ hr
  intro prev ws rs hr
  induction ws generalizing prev rs with
  | nil => cases rs <;> (unfold against.go; exact NoInt.pure trivial)
  | cons w ws ih =>
    cases rs with
    | nil => unfold against.go; exact NoInt.pure trivial
    | cons r rs =>
      obtain ⟨ty, hty, -⟩ := typeOf_wf hΓ hS (hr r List.mem_cons_self)
      have ih' := ih (prev ++ [r.term]) rs (fun r' h' => hr r' (List.mem_cons_of_mem _ h'))
      unfold against.go
      simp only [Scope.typeOf, hty, pure, Except.pure, ok_bind]
      exact NoInt.bind meets_noInt fun _ _ => ih'

theorem solution_noInt {C : Ctx} {sc : Scope} {ts : List Term} {pos : Pos} {type : Term} {is : Option Term}
    {erased : Bool} :
    NoInt (sc.solution C ts pos type is erased) (fun r => r.term.wf sc.sigs sc.Γ.length 0 = true) := by
  unfold Scope.solution
  dsimp only
  split
  · rename_i t ht
    refine NoInt.pure ?_
    have h := List.find?_some ht
    simp only at h ⊢
    cases hc : coreType sc.sigs sc.Γ t with
    | none => simp [hc] at h
    | some ty => exact coreType_wf t ty hc
  · exact NoInt.failAt

/-- A `_` takes a well-formed term, or fails with an error that is not internal. -/
theorem hole_noInt {C : Ctx} {sc : Scope} {pos : Pos} {type : Term} {is : Option Term} {erased : Bool} :
    NoInt (sc.hole C pos type is erased) (fun r => r.term.wf sc.sigs sc.Γ.length 0 = true) := by
  unfold Scope.hole
  split
  · exact solution_noInt
  · exact NoInt.failAt

theorem holeType_noInt {C : Ctx} {sc : Scope} {g : Given} {p : TBinder} {prev : List Res} {pos : Pos} :
    NoInt (holeType C sc g p prev pos) (fun _ => True) := by
  unfold holeType
  dsimp only
  repeat' (first | exact NoInt.failAt | exact NoInt.pure trivial | split)

theorem holeArg_noInt {C : Ctx} {sc : Scope} {g : Given} {p : TBinder} {prev : List Res} {pos : Pos} :
    NoInt (holeArg C sc g p prev pos) (fun o => o.sc = sc ∧ ∃ r, o.res = [r] ∧
      r.term.wf sc.sigs sc.Γ.length 0 = true) := by
  unfold holeArg
  exact NoInt.bind holeType_noInt fun ⟨_, _, _⟩ _ => NoInt.bind hole_noInt fun r hr => NoInt.pure ⟨rfl, r, rfl, hr⟩

theorem ScOk.ctx {C C' : Ctx} {sc : Scope} (h : ScOk C sc) (hg : C'.globals = C.globals) : ScOk C' sc :=
  ⟨h.Γ, h.sigs, h.names, hg ▸ h.globals⟩

theorem global_sig {C : Ctx} {sc : Scope} (hsc : ScOk C sc) {n : String} {g : Global} (hg : C.global n = some g) :
    (∀ cs d, g = .type n cs d → ∃ s, sc.sigs.find ⟨.type, n⟩ = some s) ∧
      (g = .ctor n → ∃ s, sc.sigs.find ⟨.ctor, n⟩ = some s) := by
  obtain ⟨hn, hm⟩ := hsc.global hg
  refine ⟨fun cs d he => ?_, fun he => ?_⟩
  · subst he; exact (hsc.globals _ hm).1
  · subst he; exact hsc.globals _ hm

theorem NoInt.notApplied_bind {α β : Type} {sc : Scope} {h : Name} {f : α → CheckM β} {R : β → Prop} :
    NoInt (notApplied sc h >>= f) R := NoInt.failAt_bind

theorem sig_noInt {sc : Scope} {pos : Pos} {h : Head} {sig : Sig} (hs : sc.sigs.find h = some sig) :
    NoInt (sc.sig pos h) (fun s => s = sig ∧ sc.sigs.find h = some sig) := by
  unfold Scope.sig; rw [hs]; exact NoInt.pure ⟨rfl, rfl⟩

mutual
/-- Checking a term reports no internal error, and gives a well-formed term. -/
theorem checkTerm_noInt {sc : Scope} : ∀ (C : Ctx) (whole : Bool) (t : WTerm), ScOk C sc →
    NoInt (checkTerm C sc whole t) (fun r => r.term.wf sc.sigs sc.Γ.length 0 = true)
  | C, whole, .hole p, hsc => by
    unfold checkTerm
    split
    · exact hole_noInt
    · exact NoInt.failAt
  | C, whole, .var x, hsc => by
    unfold checkTerm
    split
    · rename_i r hr; have := hsc.lookup hr; exact NoInt.pure this
    · exact NoInt.failAt
  | C, whole, .app h args, hsc => by
    have rest : ∀ kind s, sc.sigs.find ⟨kind, h.name⟩ = some s → NoInt (do
        let sig ← sc.sig h.pos ⟨kind, h.name⟩
        arity h.pos h.name sig.params.length args.length
        let rs ← checkTerms { C with inType := C.inType || kind == .type } sc h.name
          (if kind = .type then "parameter" else "field") (kind = .type && C.phase ≥ 2) sig.params [] args
        pure (⟨.app sig.head (rs.map (·.term)), rs.any (·.tainted) || sc.taintedBy.isSome, false⟩ : Res))
        (fun r => r.term.wf sc.sigs sc.Γ.length 0 = true) := fun kind s hs => by
      refine NoInt.bind (sig_noInt hs) fun s' ⟨hss, _⟩ => ?_
      subst hss
      refine NoInt.bind NoInt.arity fun _ har => ?_
      refine NoInt.bind (checkTerms_noInt _ _ _ _ _ _ args (hsc.ctx rfl) har.symm)
        fun rs ⟨hl, hw⟩ => NoInt.pure ?_
      refine Term.wf_app.2 ⟨⟨s', by rw [Sigs.find_head hs]; exact hs, by simp [hl, har]⟩, ?_⟩
      simpa using hw
    unfold checkTerm
    dsimp only
    cases hg : C.global h.name with
    | none => exact NoInt.notApplied_bind
    | some gl =>
      have hgs := global_sig hsc hg
      cases gl with
      | fn => exact NoInt.failAt_bind
      | type nm cs d =>
        obtain ⟨s, hs⟩ := hgs.1 cs d (by have := (hsc.global hg).1; simp only [Global.name] at this; rw [this])
        exact rest .type s hs
      | ctor nm =>
        obtain ⟨s, hs⟩ := hgs.2 (by have := (hsc.global hg).1; simp only [Global.name] at this; rw [this])
        exact rest .ctor s hs
theorem checkTerms_noInt {sc : Scope} : ∀ (C : Ctx) (owner role : String) (erased : Bool) (params : Telescope)
    (prev : List Res) (as : List WTerm), ScOk C sc → params.length = as.length →
    NoInt (checkTerms C sc owner role erased params prev as)
      (fun rs => rs.length = as.length ∧ ∀ r ∈ rs, r.term.wf sc.sigs sc.Γ.length 0 = true)
  | C, owner, role, erased, params, prev, [], hsc, _ => by
    unfold checkTerms; exact NoInt.pure ⟨rfl, by simp⟩
  | C, owner, role, erased, [], prev, a :: as, hsc, hl => by simp at hl
  | C, owner, role, erased, p :: ps, prev, a :: as, hsc, hl => by
    have rest := fun (r : Res) => checkTerms_noInt C owner role erased ps (prev ++ [r]) as hsc (by simpa using hl)
    have fin : ∀ r : Res, r.term.wf sc.sigs sc.Γ.length 0 = true →
        NoInt (do let rs ← checkTerms C sc owner role erased ps (prev ++ [r]) as; pure (r :: rs))
          (fun rs => rs.length = (a :: as).length ∧ ∀ r ∈ rs, r.term.wf sc.sigs sc.Γ.length 0 = true) :=
      fun r hr => NoInt.bind (rest r) fun rs ⟨h1, h2⟩ => NoInt.pure ⟨by simp [h1], by simpa [hr] using h2⟩
    cases a with
    | hole pos =>
      unfold checkTerms
      exact NoInt.bind holeArg_noInt fun o ho =>
        NoInt.bind NoInt.single fun r hr => fin r (by obtain ⟨_, r', h1, h2⟩ := ho; rw [h1] at hr; cases hr; exact h2)
    | var x =>
      unfold checkTerms
      exact NoInt.bind (checkTerm_noInt C false (.var x) hsc) fun r hr =>
        NoInt.bind (against_noInt (rs := [r]) hsc.Γ hsc.sigs
          (fun r' h' => by rw [List.mem_singleton.1 h']; exact hr)) fun _ _ => fin r hr
    | app h bs =>
      unfold checkTerms
      exact NoInt.bind (checkTerm_noInt C false (.app h bs) hsc) fun r hr =>
        NoInt.bind (against_noInt (rs := [r]) hsc.Γ hsc.sigs
          (fun r' h' => by rw [List.mem_singleton.1 h']; exact hr)) fun _ _ => fin r hr
end

theorem Telescope.wf_mono {S S' : Sigs} {n n' : Nat} (hS : ∀ h sig, S.find h = some sig → S'.find h = some sig)
    (hn : n ≤ n') : ∀ {k : Nat} {tele : Telescope}, Telescope.wf S n k tele = true → Telescope.wf S' n' k tele = true
  | _, [], _ => rfl
  | k, b :: bs, h => by
    simp only [Telescope.wf, Bool.and_eq_true, Option.all_eq_true] at *
    exact ⟨⟨Term.wf_mono hS hn (Nat.le_refl _) _ h.1.1, fun e he => Term.wf_mono hS hn (Nat.le_refl _) _ (h.1.2 e he)⟩,
      Telescope.wf_mono hS hn h.2⟩

theorem Telescope.wf_iff {S : Sigs} {n : Nat} : ∀ {k : Nat} {tele : Telescope}, Telescope.wf S n k tele = true ↔
    ∀ (j : Nat) (b : TBinder), tele[j]? = some b → b.type.wf S n (k + j) = true ∧ ∀ e, b.is = some e →
      e.wf S n (k + j) = true
  | k, [] => by simp [Telescope.wf]
  | k, b :: bs => by
    simp only [Telescope.wf, Bool.and_eq_true, Option.all_eq_true, Telescope.wf_iff (tele := bs)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩ j b' hb
      cases j with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hb; subst hb; exact ⟨h1, h2⟩
      | succ j =>
        obtain ⟨a, c⟩ := h3 j b' (by simpa using hb)
        exact ⟨by rw [show k + (j + 1) = k + 1 + j by omega]; exact a,
          fun e he => by rw [show k + (j + 1) = k + 1 + j by omega]; exact c e he⟩
    · intro h
      obtain ⟨a, c⟩ := h 0 b rfl
      refine ⟨⟨a, c⟩, fun j b' hb => ?_⟩
      obtain ⟨a', c'⟩ := h (j + 1) b' (by simpa using hb)
      exact ⟨by rw [show k + 1 + j = k + (j + 1) by omega]; exact a',
        fun e he => by rw [show k + 1 + j = k + (j + 1) by omega]; exact c' e he⟩

theorem GlobOk.mono {gs : List Global} {S : Sigs} {n n' : Nat} (h : GlobOk gs S n) (hn : n ≤ n') :
    GlobOk gs S n' := by
  intro g hg
  have := h g hg
  cases g with
  | fn _ sig => cases sig with
    | none => trivial
    | some sig => exact ⟨Telescope.wf_mono (fun _ _ h => h) hn this.1, Telescope.wf_mono (fun _ _ h => h) hn this.2.1,
        this.2.2.1, this.2.2.2⟩
  | type => exact this
  | ctor => exact this

/-- A later scope of the same declaration keeps `ScOk`. -/
theorem ScOk.grow {C : Ctx} {sc sc' : Scope} (h : ScOk C sc) (hs : sc'.sigs = sc.sigs)
    (hΓ : Entries.Wf sc'.sigs sc'.Γ) (hl : sc.Γ.length ≤ sc'.Γ.length)
    (hn : ∀ p ∈ sc'.names, p ∈ sc.names ∨ p.2.term.wf sc'.sigs sc'.Γ.length 0 = true) : ScOk C sc' := by
  refine ⟨hΓ, hs ▸ h.sigs.mono hl, fun p hp => ?_, hs ▸ h.globals.mono hl⟩
  rcases hn p hp with hp | hp
  · rw [hs]; exact Term.wf_le hl (Nat.le_refl _) (h.names p hp)
  · exact hp

mutual
theorem Term.closed_of_wf' {S : Sigs} {n : Nat} : ∀ t : Term, t.wf S n 0 = true → t.boundsBelow 0 = true
  | .entry _, _ => rfl
  | .bound _, h => by simp [Term.wf] at h
  | .app _ as, h => by simp only [Term.wf, Bool.and_eq_true] at h; exact Term.closedList_of_wf' as h.2
theorem Term.closedList_of_wf' {S : Sigs} {n : Nat} :
    ∀ as : List Term, Term.wfList S n 0 as = true → Term.boundsBelowList 0 as = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.wfList, Term.boundsBelowList, Bool.and_eq_true] at *
    exact ⟨Term.closed_of_wf' a h.1, Term.closedList_of_wf' as h.2⟩
end

theorem Term.closed_of_wf {S : Sigs} {n : Nat} {t : Term} (h : t.wf S n 0 = true) : t.closed = true :=
  Term.closed_of_wf' t h

mutual
theorem Term.entriesBelow_of_wf' {S : Sigs} {n k : Nat} : ∀ t : Term, t.wf S n k = true → t.entriesBelow n = true
  | .entry _, h => by simpa [Term.wf, Term.entriesBelow] using h
  | .bound _, _ => rfl
  | .app _ as, h => by simp only [Term.wf, Bool.and_eq_true] at h; exact Term.entriesBelowList_of_wf' as h.2
theorem Term.entriesBelowList_of_wf' {S : Sigs} {n k : Nat} :
    ∀ as : List Term, Term.wfList S n k as = true → Term.entriesBelowList n as = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.wfList, Term.entriesBelowList, Bool.and_eq_true] at *
    exact ⟨Term.entriesBelow_of_wf' a h.1, Term.entriesBelowList_of_wf' as h.2⟩
end

theorem Term.entriesBelow_of_wf {S : Sigs} {n k : Nat} {t : Term} (h : t.wf S n k = true) :
    t.entriesBelow n = true := Term.entriesBelow_of_wf' t h

theorem Term.lt_of_occurs_wf {S : Sigs} {n k i : Nat} {t : Term} (h : t.wf S n k = true) (ho : t.occurs i = true) :
    i < n := Term.lt_of_occurs t (Term.entriesBelow_of_wf h) ho

theorem Term.mapEntriesList_length {f : Nat → Term} : ∀ as : List Term, (Term.mapEntriesList f as).length = as.length
  | [] => rfl
  | _ :: as => by simp [Term.mapEntriesList, Term.mapEntriesList_length as]

mutual
theorem Term.wf_mapEntries {S : Sigs} {m n K : Nat} {f : Nat → Term} :
    ∀ t : Term, t.wf S m 0 = true → (∀ i, t.occurs i = true → (f i).wf S n K = true) →
      (t.mapEntries f).wf S n K = true
  | .entry i, _, hf => hf i (by simp [Term.occurs])
  | .bound _, h, _ => by simp [Term.wf] at h
  | .app hd as, h, hf => by
    simp only [Term.wf, Bool.and_eq_true, Option.any_eq_true, Term.mapEntries] at *
    obtain ⟨⟨sig, hs, hl⟩, has⟩ := h
    exact ⟨⟨sig, hs, by rw [Term.mapEntriesList_length]; exact hl⟩, Term.wfList_mapEntries as has hf⟩
theorem Term.wfList_mapEntries {S : Sigs} {m n K : Nat} {f : Nat → Term} :
    ∀ as : List Term, Term.wfList S m 0 as = true → (∀ i, Term.occursList i as = true → (f i).wf S n K = true) →
      Term.wfList S n K (Term.mapEntriesList f as) = true
  | [], _, _ => rfl
  | a :: as, h, hf => by
    simp only [Term.wfList, Term.mapEntriesList, Bool.and_eq_true] at *
    exact ⟨Term.wf_mapEntries a h.1 fun i hi => hf i (by simp [Term.occursList, hi]),
      Term.wfList_mapEntries as h.2 fun i hi => hf i (by simp [Term.occursList, hi])⟩
end

/-- An abstracted term is well-formed with entries below `n` and bound variables below `K` when every entry of the
original term not abstracted is below `n`, every entry abstracted takes an index below `K`, and the rules of entries
below `n` mention only entries below `n`. -/
theorem abstract_wf {S : Sigs} {Γ : Entries} {t : Term} {ids : List Nat} {m n K : Nat} (ht : t.wf S m 0 = true)
    (hn : n ≤ m) (hA : ∀ i, i < m → ids.idxOf? i = none → i < n)
    (hB : ∀ i k, i < m → ids.idxOf? i = some k → k < K)
    (hC : ∀ i en r, i < n → Γ[i]? = some en → en.rule = some r → r.wf S n 0 = true) :
    (abstract Γ t ids).wf S n K = true := by
  refine Term.wf_mapEntries t ht fun i hi => ?_
  dsimp only
  have him := Term.lt_of_occurs_wf ht hi
  cases hk : ids.idxOf? i with
  | some k => simpa [Term.wf] using hB i k him hk
  | none =>
    have hin := hA i him hk
    simp only [Option.map_none, Option.getD_none]
    cases hen : Γ[i]? with
    | none => simpa [Term.wf] using hin
    | some en =>
      cases hru : en.rule with
      | none => simpa [hru, Term.wf] using hin
      | some r =>
        simp only [Option.bind_some, hru, Option.elim_some]
        have hr := hC i en r hin hen hru
        refine Term.wf_mapEntries r (Term.wf_le hn (Nat.le_refl _) hr) fun j hj => ?_
        have hjn := Term.lt_of_occurs_wf hr hj
        cases hk' : ids.idxOf? j with
        | some k => simpa [Term.wf] using hB j k (by omega) hk'
        | none => simpa [Term.wf] using hjn

theorem abstractChecked_noInt {S : Sigs} {Γ : Entries} {t : Term} {ids : List Nat} {pos : Pos}
    (hΓ : Entries.Wf S Γ) (ht : t.wf S Γ.length 0 = true) :
    NoInt (abstractChecked Γ t ids pos) (fun u => u = abstract Γ t ids) := by
  unfold abstractChecked abstract?
  simp only [Term.closed_of_wf (Term.canon_wf hΓ t ht).1, ↓reduceIte]
  exact NoInt.pure rfl

theorem term_noInt {C : Ctx} {sc : Scope} {t : WTerm} {whole : Bool} (hsc : ScOk C sc) :
    NoInt (term C sc t whole) (fun r => r.term.wf sc.sigs sc.Γ.length 0 = true) :=
  checkTerm_noInt _ whole t (hsc.ctx rfl)

theorem isType_noInt {sc : Scope} {pos : Pos} {t : Term} (hΓ : Entries.Wf sc.sigs sc.Γ)
    (hS : Sigs.Wf sc.sigs sc.Γ.length) (ht : t.wf sc.sigs sc.Γ.length 0 = true) :
    NoInt (isType sc pos t) (fun _ => True) := by
  obtain ⟨ty, hty, -⟩ := typeOf_wf hΓ hS ht
  unfold isType
  simp only [Scope.typeOf, hty, pure, Except.pure, ok_bind]
  split <;> first | exact NoInt.failAt | exact NoInt.pure trivial

theorem annotate_noInt {C : Ctx} {sc : Scope} {ann : Ann} (hsc : ScOk C sc) :
    NoInt (annotate C sc ann) (fun a => a.1.wf sc.sigs sc.Γ.length 0 = true ∧
      ∀ e, a.2.1 = some e → e.wf sc.sigs sc.Γ.length 0 = true) := by
  cases ann with
  | «is» t =>
    unfold annotate
    refine NoInt.bind (term_noInt hsc) fun r hr => ?_
    obtain ⟨ty, hty, htw⟩ := typeOf_wf hsc.Γ hsc.sigs hr
    simp only [Scope.typeOf, hty, pure, Except.pure, ok_bind]
    exact NoInt.pure ⟨htw, fun e he => by cases he; exact hr⟩
  | type t =>
    unfold annotate
    refine NoInt.bind (term_noInt hsc) fun r hr => ?_
    exact NoInt.bind (isType_noInt hsc.Γ hsc.sigs hr) fun _ _ => NoInt.pure ⟨hr, fun e he => by cases he⟩

/-- Opening a binder whose type and `is` term are well-formed keeps `ScOk`, appending one entry. -/
theorem openBinder_ok {C : Ctx} {sc : Scope} {name : Id} {type : Term} {is : Option Term} {mult : Option Mult}
    {kind : String} {tainted : Bool} (hsc : ScOk C sc) (ht : type.wf sc.sigs sc.Γ.length 0 = true)
    (hi : ∀ e, is = some e → e.wf sc.sigs sc.Γ.length 0 = true) :
    ScOk C (sc.openBinder name type is mult kind tainted).sc ∧
      (sc.openBinder name type is mult kind tainted).sc.sigs = sc.sigs ∧
      (sc.openBinder name type is mult kind tainted).sc.Γ.length = sc.Γ.length + 1 ∧
      sc.Γ <+: (sc.openBinder name type is mult kind tainted).sc.Γ ∧
      (sc.openBinder name type is mult kind tainted).id = sc.Γ.length := by
  have hw : Telescope.wf sc.sigs sc.Γ.length ([] : List Term).length
      [⟨name.name, type, is, mult.getD .many⟩] = true := by
    simp only [Telescope.wf, List.length_nil, Bool.and_eq_true, Option.all_eq_true, and_true]
    exact ⟨ht, hi⟩
  unfold Scope.openBinder
  dsimp only
  generalize (fun (_ : TBinder) (_ : Nat) (en : Entry) => { en with origin := s!"{kind}@{name.pos}" }) = mk
  obtain ⟨hΓ, -⟩ := openTele_wf mk hsc.Γ (Nat.le_refl _) hw (by simp)
  have hl := openTele_length sc.Γ [⟨name.name, type, is, mult.getD .many⟩] [] mk
  obtain ⟨Δ, hΔ, -⟩ := openTele_shape sc.Γ [⟨name.name, type, is, mult.getD .many⟩] [] mk
  rw [Scope.bind_eq]
  refine ⟨hsc.grow rfl hΓ (by rw [hl]; simp) fun p hp => ?_, rfl, by rw [hl]; rfl, ⟨Δ, hΔ.symm⟩, rfl⟩
  rcases List.mem_append.1 hp with hp | hp
  · obtain ⟨i, hi⟩ := pushed_mem hp
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; rw [← hi]; simp [Term.wf, hl]
    | succ => simp at hi
  · exact .inl hp

theorem opening_noInt {C : Ctx} {sc : Scope} {name : Id} {ann : Ann} {mult : Option Mult} {kind : String}
    (hsc : ScOk C sc) :
    NoInt (opening C sc name ann mult kind) (fun o => ScOk C o.sc ∧ o.sc.sigs = sc.sigs ∧
      o.sc.Γ.length = sc.Γ.length + 1 ∧ sc.Γ <+: o.sc.Γ ∧ o.id = sc.Γ.length ∧
      o.type.wf sc.sigs sc.Γ.length 0 = true ∧ ∀ e, o.is = some e → e.wf sc.sigs sc.Γ.length 0 = true) := by
  unfold opening
  exact NoInt.bind (annotate_noInt hsc) fun ⟨ty, is, t⟩ ⟨h1, h2⟩ => NoInt.pure
    (by have := openBinder_ok (name := name) (mult := mult) (kind := kind) (tainted := t) hsc h1 h2; exact
      ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2, h1, h2⟩)

theorem fresh_noInt {C : Ctx} {sc : Scope} {seen : List String} {name : Option String} {pos : Pos} :
    NoInt (fresh C sc seen name pos) (fun _ => True) := by
  unfold fresh
  repeat (first | exact NoInt.failAt | exact NoInt.pure trivial | split)

theorem freshAll_noInt {C : Ctx} {sc : Scope} {ids : List Id} : NoInt (freshAll C sc ids) (fun _ => True) := by
  unfold freshAll discard
  exact NoInt.bind (NoInt.foldlM (I := fun _ => True) trivial fun _ _ _ _ => fresh_noInt) fun _ _ =>
    NoInt.pure trivial

theorem telescope_go_noInt {C : Ctx} {kind : String} : ∀ (bs : List Binder) (sc : Scope) (seen : List String)
    (acc : List (Binder × Opening)), ScOk C sc →
    NoInt (telescope.go C kind sc seen acc bs) (fun res => ScOk C res.1 ∧ res.1.sigs = sc.sigs ∧ sc.Γ <+: res.1.Γ ∧
      res.1.Γ.length = sc.Γ.length + bs.length ∧ ∃ new, res.2.2 = acc ++ new ∧ new.length = bs.length ∧
        ∀ (j : Nat) (o : Binder × Opening), new[j]? = some o → o.2.type.wf sc.sigs (sc.Γ.length + j) 0 = true ∧
          ∀ e : Term, o.2.is = some e → e.wf sc.sigs (sc.Γ.length + j) 0 = true)
  | [], sc, seen, acc, hsc => by
    unfold telescope.go
    exact NoInt.pure ⟨hsc, rfl, List.prefix_refl _, rfl, [], by simp, rfl, by simp⟩
  | b :: bs, sc, seen, acc, hsc => by
    unfold telescope.go
    refine NoInt.bind fresh_noInt fun seen' _ => ?_
    refine NoInt.bind (opening_noInt hsc) fun o ho => ?_
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ho
    refine NoInt.imp (telescope_go_noInt bs o.sc seen' (acc ++ [(b, o)]) h1)
      fun res ⟨r1, r2, r3, r4, new, r5, r6, r7⟩ => ?_
    refine ⟨r1, r2.trans h2, h4.trans r3, by rw [r4, h3]; simp; omega, (b, o) :: new, by simp [r5], by simp [r6],
      fun j o' hj => ?_⟩
    cases j with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; exact ⟨h6, h7⟩
    | succ j =>
      obtain ⟨a, c⟩ := r7 j o' (by simpa using hj)
      rw [h2, h3] at a c
      exact ⟨by rw [show sc.Γ.length + (j + 1) = sc.Γ.length + 1 + j by omega]; exact a,
        fun e he => by rw [show sc.Γ.length + (j + 1) = sc.Γ.length + 1 + j by omega]; exact c e he⟩

theorem abstracted_noInt {S : Sigs} {Γ : Entries} {name : Option String} {mult : Option Mult} {pos : Pos}
    {type : Term} {is : Option Term} {ids : List Nat} (hΓ : Entries.Wf S Γ) (ht : type.wf S Γ.length 0 = true)
    (hi : ∀ e, is = some e → e.wf S Γ.length 0 = true) :
    NoInt (abstracted Γ name mult pos type is ids) (fun b => b.type = abstract Γ type ids ∧
      ∀ e', b.is = some e' → ∃ e, is = some e ∧ e' = abstract Γ e ids) := by
  unfold abstracted
  refine NoInt.bind (abstractChecked_noInt hΓ ht) fun u hu => ?_
  cases is with
  | none => exact NoInt.pure ⟨hu, fun e' he' => by simp at he'⟩
  | some e =>
    refine NoInt.bind (Q := fun o => o = some (abstract Γ e ids)) ?_ fun o ho => NoInt.pure ⟨hu, fun e' he' => by
      simp only [ho, Option.some.injEq] at he'; exact ⟨e, rfl, he'.symm⟩⟩
    simp only [Option.mapM]
    exact NoInt.bind (abstractChecked_noInt hΓ (hi e rfl)) fun v hv => NoInt.pure (by rw [hv])

theorem idxOf?_range' {outer : List Nat} {n0 len j i k : Nat} (_hj : j ≤ len) (hi : i < n0 + j)
    (h : (outer ++ List.range' n0 len).idxOf? i = some k) : k < outer.length + j := by
  obtain ⟨hk, he, -⟩ := List.idxOf?_eq_some_iff.1 h
  by_cases hko : k < outer.length
  · omega
  · rw [List.getElem_append_right (by omega), List.getElem_range'] at he
    omega

theorem idxOf?_range'_none {outer : List Nat} {n n0 len j i : Nat} (hj : j ≤ len) (hi : i < n0 + j)
    (houter : ∀ i, n ≤ i → i < n0 → i ∈ outer) (h : (outer ++ List.range' n0 len).idxOf? i = none) : i < n := by
  have hn := List.idxOf?_eq_none_iff.1 h
  simp only [List.mem_append, List.mem_range'_1, not_or] at hn
  rcases Nat.lt_or_ge i n with hc | hc
  · exact hc
  · exfalso
    by_cases h0 : i < n0
    · exact hn.1 (houter i hc h0)
    · exact hn.2 ⟨by omega, by omega⟩

/-- A telescope checked in a well-formed scope is well-formed, its bound variables standing for `outer` and then its
own binders, and its other entries below `n` when every entry from `n` on is in `outer`. -/
theorem telescope_noInt {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat} {n : Nat}
    (hsc : ScOk C sc) (hn : n ≤ sc.Γ.length)
    (hrule : ∀ i en r, i < n → sc.Γ[i]? = some en → en.rule = some r → r.wf sc.sigs n 0 = true)
    (houter : ∀ i, n ≤ i → i < sc.Γ.length → i ∈ outer) :
    NoInt (telescope C sc bs kind outer) (fun out => ScOk C out.sc ∧ out.sc.sigs = sc.sigs ∧ sc.Γ <+: out.sc.Γ ∧
      out.sc.Γ.length = sc.Γ.length + bs.length ∧ out.ids = List.range' sc.Γ.length bs.length ∧
      out.tele.length = bs.length ∧ Telescope.wf sc.sigs n outer.length out.tele = true) := by
  refine ⟨?_, fun out h => ?_⟩
  · unfold telescope
    refine (NoInt.bind (R := fun _ : Checked => True) (telescope_go_noInt bs sc [] [] hsc)
      fun ⟨sc', seen, opens⟩ hres => ?_).1
    obtain ⟨r1, r2, r3, r4, new, r5, r6, r7⟩ := hres
    simp only [List.nil_append] at r5 r1 r2 r3 r4
    subst r5
    refine NoInt.bind (NoInt.mapM (R := fun _ => True) fun x hx => ?_) fun _ _ => NoInt.pure trivial
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    have hj' := List.getElem?_zip_eq_some.1 hj
    obtain ⟨a, c⟩ := r7 j _ hj'.2
    have hjl : j < bs.length := by have := (List.getElem?_eq_some_iff.1 hj'.2).1; omega
    rw [← r2] at a c
    obtain ⟨b, f, o⟩ := x
    exact NoInt.imp (abstracted_noInt r1.Γ (Term.wf_le (by omega) (Nat.le_refl _) a)
      fun e he => Term.wf_le (by omega) (Nat.le_refl _) (c e he)) fun _ _ => trivial
  · obtain ⟨res, hgo, h⟩ := bind_eq_ok.1 h
    obtain ⟨sc', seen, opens⟩ := res
    obtain ⟨tele, htele, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨r1, r2, r3, r4, new, r5, r6, r7⟩ := (telescope_go_noInt bs sc [] [] hsc).2 _ hgo
    simp only [List.nil_append] at r5 r1 r2 r3 r4
    subst r5
    obtain ⟨new', hnew', -, hids, -⟩ := telescope_go_shape bs sc [] [] hgo
    simp only [List.nil_append] at hnew'
    subst hnew'
    obtain ⟨hl, hi⟩ := mapM_ok htele
    refine ⟨r1, r2, r3, r4, hids, by simp [hl, r6], Telescope.wf_iff.2 fun j b hb => ?_⟩
    have hjl : j < bs.length := by have := (List.getElem?_eq_some_iff.1 hb).1; simp [hl, r6] at this; omega
    obtain ⟨x, hx⟩ : ∃ x, (bs.zip opens)[j]? = some x := ⟨_, List.getElem?_eq_getElem (by simp [r6]; omega)⟩
    have hx' := List.getElem?_zip_eq_some.1 hx
    obtain ⟨a, c⟩ := r7 j _ hx'.2
    have hab := hi j x b hx hb
    obtain ⟨xb, xf, xo⟩ := x
    simp only at a c hab
    have hA := (abstracted_noInt (name := xb.name.name) (mult := xb.mult) (pos := xb.name.pos)
      (ids := outer ++ opens.map (·.2.id)) r1.Γ (Term.wf_le (by omega) (Nat.le_refl _) (r2 ▸ a))
      fun e he => Term.wf_le (by omega) (Nat.le_refl _) (r2 ▸ c e he)).2 b hab
    rw [hids] at hA
    have hC : ∀ i en r, i < n → sc'.Γ[i]? = some en → en.rule = some r → r.wf sc.sigs n 0 = true := by
      intro i en r hi hen hr
      obtain ⟨t, ht⟩ := r3
      rw [← ht, List.getElem?_append_left (by omega)] at hen
      exact hrule i en r hi hen hr
    have wfab := fun (t : Term) (ht : t.wf sc.sigs (sc.Γ.length + j) 0 = true) =>
      abstract_wf (Γ := sc'.Γ) (ids := outer ++ List.range' sc.Γ.length bs.length) (K := outer.length + j) ht
        (by omega) (fun i hi hk => idxOf?_range'_none (Nat.le_of_lt hjl) hi houter hk)
        (fun i k hi hk => idxOf?_range' (Nat.le_of_lt hjl) hi hk) hC
    refine ⟨by rw [hA.1]; exact wfab _ a, fun e' he' => ?_⟩
    obtain ⟨e, he, rfl⟩ := hA.2 e' he'
    exact wfab _ (c e he)

/-- Entry `j` of `ws` mentions entries below `n` and bound variables below `k + j`. -/
def Wants.wf (S : Sigs) (n k : Nat) (ws : List Want) : Prop :=
  ∀ (j : Nat) (w : Want), ws[j]? = some w → (∀ t, w.type = some t → t.wf S n (k + j) = true) ∧
    ∀ e, w.is = some e → e.wf S n (k + j) = true

/-- What a position is given is well-formed where `_` may stand for it (§10): its environment's terms, and its
entries, all with a type and at least one. -/
structure GivenOk (S : Sigs) (n : Nat) (g : Given) : Prop where
  env : g.whole = true → ∀ u ∈ g.env, u.wf S n 0 = true
  wants : g.whole = true → Wants.wf S n g.env.length g.wants
  whole : g.whole = true → g.wants ≠ [] ∧ ∀ w ∈ g.wants, w.type.isSome = true

theorem Wants.wf_of_tele {S : Sigs} {n k : Nat} {tele : Telescope} {ws : List Want}
    (ht : Telescope.wf S n k tele = true) (hl : ws.length = tele.length)
    (hw : ∀ (j : Nat) (w : Want) (b : TBinder), ws[j]? = some w → tele[j]? = some b →
      w.type = some b.type ∧ w.is = b.is) : Wants.wf S n k ws := by
  intro j w hj
  obtain ⟨b, hb⟩ : ∃ b, tele[j]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hj).1)⟩
  obtain ⟨h1, h2⟩ := hw j w b hj hb
  obtain ⟨a, c⟩ := Telescope.wf_iff.1 ht j b hb
  exact ⟨fun t htt => by rw [h1] at htt; cases htt; exact a, fun e he => by rw [h2] at he; exact c e he⟩

theorem Telescope.wf_of_wants {S : Sigs} {n k : Nat} {tele : Telescope} {ws : List Want} (hw : Wants.wf S n k ws)
    (hl : ws.length = tele.length)
    (h : ∀ (j : Nat) (w : Want) (b : TBinder), ws[j]? = some w → tele[j]? = some b →
      w.type = some b.type ∧ w.is = b.is) :
    Telescope.wf S n k tele = true := by
  refine Telescope.wf_iff.2 fun j b hb => ?_
  obtain ⟨w, hj⟩ : ∃ w, ws[j]? = some w :=
    ⟨_, List.getElem?_eq_getElem (by rw [hl]; exact (List.getElem?_eq_some_iff.1 hb).1)⟩
  obtain ⟨h1, h2⟩ := h j w b hj hb
  obtain ⟨a, c⟩ := hw j w hj
  exact ⟨a _ h1, fun e he => c e (h2.trans he)⟩

theorem Wants.wf_mono {S : Sigs} {n n' k : Nat} {ws : List Want} (h : Wants.wf S n k ws) (hn : n ≤ n') :
    Wants.wf S n' k ws := fun j w hj =>
  ⟨fun t ht => Term.wf_le hn (Nat.le_refl _) ((h j w hj).1 t ht),
    fun e he => Term.wf_le hn (Nat.le_refl _) ((h j w hj).2 e he)⟩

theorem GivenOk.mono {S : Sigs} {n n' : Nat} {g : Given} (h : GivenOk S n g) (hn : n ≤ n') : GivenOk S n' g :=
  ⟨fun hw u hu => Term.wf_le hn (Nat.le_refl _) (h.env hw u hu), fun hw => Wants.wf_mono (h.wants hw) hn, h.whole⟩

theorem GivenOk.of_not_whole {S : Sigs} {n : Nat} {g : Given} (h : g.whole = false) : GivenOk S n g :=
  ⟨fun hw => by simp [h] at hw, fun hw => by simp [h] at hw, fun hw => by simp [h] at hw⟩

/-- A telescope a `match` annotation or `sorry` stands for is well-formed over its environment, and has an entry. -/
theorem annotation_noInt {C : Ctx} {sc : Scope} {g : Option Given} {ann : Tele} (hsc : ScOk C sc)
    (hg : ∀ g', g = some g' → GivenOk sc.sigs sc.Γ.length g')
    (hc : ∀ bs, ann = .binders bs → bs ≠ []) :
    NoInt (annotation C sc g ann) (fun te => te.1 ≠ [] ∧ (∀ u ∈ te.2, u.wf sc.sigs sc.Γ.length 0 = true) ∧
      Telescope.wf sc.sigs sc.Γ.length te.2.length te.1 = true) := by
  cases ann with
  | binders bs =>
    have hne := hc bs rfl
    unfold annotation
    refine NoInt.bind (telescope_noInt (n := sc.Γ.length) (outer := []) hsc (Nat.le_refl _)
      (fun i en r _ hen hr => ((hsc.Γ i en hen).2 r hr).1) fun i h1 h2 => absurd h2 (by omega))
      fun out ⟨_, _, _, _, _, hl, hw⟩ => NoInt.pure ⟨fun h => hne (List.eq_nil_of_length_eq_zero (by
        simp only at h; rw [← hl, h]; rfl)), by simp, by simpa using hw⟩
  | hole p =>
    unfold annotation
    cases g with
    | none => exact NoInt.failAt
    | some g =>
      simp only
      split
      · rename_i hw
        obtain ⟨hne, hty⟩ := (hg g rfl).whole hw
        have hmap : NoInt (g.wants.mapM fun w => match w.type with
            | some t => pure ⟨w.name, t, w.is, w.mult⟩
            | none => internal p "an undetermined entry in a whole telescope")
            (fun tele => tele.length = g.wants.length ∧ ∀ (j : Nat) (w : Want) (b : TBinder),
              g.wants[j]? = some w → tele[j]? = some b →
              w.type = some b.type ∧ w.is = b.is) := by
          refine ⟨(NoInt.mapM (R := fun _ => True) fun w hw' => ?_).1, fun tele h => ?_⟩
          · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hty w hw')
            simp only [ht]
            exact NoInt.pure trivial
          · obtain ⟨hl, hi⟩ := mapM_ok h
            refine ⟨hl, fun j w b hw hb => ?_⟩
            have := hi j w b hw hb
            obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hty w (List.mem_of_getElem? hw))
            simp only [ht, pure, Except.pure, Except.ok.injEq] at this
            subst this
            exact ⟨ht, rfl⟩
        refine NoInt.bind hmap fun tele ⟨hl, hi⟩ => NoInt.pure ⟨?_, (hg g rfl).env hw, ?_⟩
        · intro h; subst h; exact hne (List.eq_nil_of_length_eq_zero hl.symm)
        · exact Telescope.wf_of_wants ((hg g rfl).wants hw) hl.symm hi
      · exact NoInt.failAt

/-- Opening a well-formed telescope keeps `ScOk`; its results are the fresh entries. -/
theorem opened_ok {C : Ctx} {sc : Scope} {tele : Telescope} {env : List Term} {kind : String} {pos : Pos}
    {taint : Nat → Bool} (hsc : ScOk C sc) (ht : Telescope.wf sc.sigs sc.Γ.length env.length tele = true)
    (he : ∀ u ∈ env, u.wf sc.sigs sc.Γ.length 0 = true) :
    ScOk C (opened sc tele env kind pos taint).1 ∧ (opened sc tele env kind pos taint).1.sigs = sc.sigs ∧
      (opened sc tele env kind pos taint).1.names = sc.names ∧
      sc.Γ <+: (opened sc tele env kind pos taint).1.Γ ∧
      (opened sc tele env kind pos taint).2.length = tele.length ∧
      ∀ r ∈ (opened sc tele env kind pos taint).2,
        r.term.wf sc.sigs (opened sc tele env kind pos taint).1.Γ.length 0 = true := by
  unfold opened
  dsimp only
  generalize (fun (b : TBinder) (i : Nat) (en : Entry) =>
    { en with origin := s!"{kind}.{b.name.getD (toString (i + 1))}@{pos}", tainted := taint i }) = mk
  obtain ⟨hΓ, -⟩ := openTele_wf mk hsc.Γ (Nat.le_refl _) ht he
  have hl := openTele_length sc.Γ tele env mk
  obtain ⟨Δ, hΔ, -, hids, -⟩ := openTele_shape sc.Γ tele env mk
  refine ⟨hsc.grow rfl hΓ (by rw [hl]; omega) fun p hp => .inl hp, rfl, rfl, ⟨Δ, hΔ.symm⟩,
    by simp [hids], fun r hr => ?_⟩
  simp only [List.mem_mapIdx] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  simp only [hids, List.getElem_range'] at hi ⊢
  simp only [Term.wf, decide_eq_true_eq, hl]
  simp at hi
  omega

theorem ScOk.bind {C : Ctx} {sc : Scope} {ids : List Id} {rs : List Res} (hsc : ScOk C sc)
    (hr : ∀ r ∈ rs, r.term.wf sc.sigs sc.Γ.length 0 = true) : ScOk C (sc.bind ids rs) := by
  rw [Scope.bind_eq]
  refine hsc.grow rfl hsc.Γ (Nat.le_refl _) fun p hp => ?_
  rcases List.mem_append.1 hp with hp | hp
  · obtain ⟨i, hi⟩ := pushed_mem hp
    exact .inr (hr _ (List.mem_of_getElem? hi))
  · exact .inl hp

theorem typedBefore_noInt {untyped : List String} {ann : Ann} : NoInt (typedBefore untyped ann) (fun _ => True) := by
  unfold typedBefore
  split
  · exact NoInt.failAt
  · exact NoInt.pure trivial

theorem letBinders_noInt {C : Ctx} {sc : Scope} {pos : Pos} {bs : List LetBinder} {rs : List Res} (hsc : ScOk C sc)
    (hr : ∀ r ∈ rs, r.term.wf sc.sigs sc.Γ.length 0 = true) :
    NoInt (letBinders C sc pos bs rs) (fun _ => True) := by
  unfold letBinders
  suffices ∀ (sc : Scope) untyped i (l : List (LetBinder × Res)), ScOk C sc → (∀ x ∈ l, x.1 ∈ bs ∧
      x.2.term.wf sc.sigs sc.Γ.length 0 = true) → NoInt (letBinders.go C pos sc untyped i l) (fun _ => True) from
    this sc [] 0 _ hsc fun x hx => ⟨(List.of_mem_zip hx).1, hr _ (List.of_mem_zip hx).2⟩
  intro sc untyped i l hsc hl
  induction l generalizing sc untyped i with
  | nil => unfold letBinders.go; exact NoInt.pure trivial
  | cons x l ih =>
    obtain ⟨b, r⟩ := x
    unfold letBinders.go
    obtain ⟨hb, hrw⟩ := hl _ List.mem_cons_self
    have next : ∀ u, NoInt (letBinders.go C pos (sc.bind [b.name] [{ r with erased := b.mult == some .erased }]) u
        (i + 1) l) (fun _ => True) := fun u => by
      have hb' := hsc.bind (ids := [b.name]) (rs := [{ r with erased := b.mult == some .erased }])
        (by simpa using hrw)
      refine ih _ u (i + 1) hb' fun y hy => ⟨(hl y (List.mem_cons_of_mem _ hy)).1, ?_⟩
      rw [Scope.bind_eq]; exact (hl y (List.mem_cons_of_mem _ hy)).2
    dsimp only
    cases ha : b.ann with
    | none => exact next _
    | some a =>
      simp only
      refine NoInt.bind typedBefore_noInt fun _ _ => ?_
      refine NoInt.bind (annotate_noInt hsc) fun _ _ => ?_
      refine NoInt.bind (against_noInt (rs := [{ r with erased := b.mult == some .erased }]) hsc.Γ hsc.sigs
        (by simpa using hrw)) fun _ _ => ?_
      exact NoInt.bind (Q := fun _ => True) (NoInt.pure trivial) fun _ _ => next _

theorem header_noInt {C : Ctx} {sc : Scope} {h : Header} (hsc : ScOk C sc) :
    NoInt (header C sc h) (fun pr => ScOk C pr.2.sc ∧ pr.2.sc.sigs = sc.sigs ∧ sc.Γ <+: pr.2.sc.Γ ∧
      pr.1.tele.length = h.params.length ∧ pr.2.tele.length = h.returns.length ∧
      Telescope.wf sc.sigs sc.Γ.length 0 pr.1.tele = true ∧
      Telescope.wf sc.sigs sc.Γ.length pr.1.tele.length pr.2.tele = true ∧
      pr.1.ids = List.range' sc.Γ.length h.params.length ∧ pr.1.sc.Γ.length = sc.Γ.length + h.params.length ∧
      ScOk C pr.1.sc ∧ pr.1.sc.sigs = sc.sigs ∧ sc.Γ <+: pr.1.sc.Γ) := by
  unfold header
  refine NoInt.bind (telescope_noInt (n := sc.Γ.length) (outer := []) hsc (Nat.le_refl _)
    (fun i en r _ hen hr => ((hsc.Γ i en hen).2 r hr).1) fun i h1 h2 => absurd h2 (by omega))
    fun ps ⟨p1, p2, p3, p4, p5, p6, p7⟩ => ?_
  have hrule : ∀ i en r, i < sc.Γ.length → ps.sc.Γ[i]? = some en → en.rule = some r →
      r.wf ps.sc.sigs sc.Γ.length 0 = true := by
    intro i en r hi hen hr
    obtain ⟨t, ht⟩ := p3
    rw [← ht, List.getElem?_append_left hi] at hen
    rw [p2]; exact ((hsc.Γ i en hen).2 r hr).1
  refine NoInt.bind (telescope_noInt (n := sc.Γ.length) (outer := ps.ids) p1 (by omega) hrule fun i h1 h2 => ?_)
    fun rs ⟨r1, r2, r3, r4, r5, r6, r7⟩ => NoInt.pure ⟨r1, r2.trans p2, p3.trans r3, by simpa using p6, r6,
      by simpa using p7, ?_, by simpa using p5, by simpa using p4, p1, p2, p3⟩
  · have := p4; rw [p5]; simp [List.mem_range'_1] at this ⊢; omega
  · rw [p2] at r7; rw [p6]; rwa [p5, List.length_range'] at r7

theorem letWants_go_noInt {C : Ctx} : ∀ (bs : List LetBinder) (sc : Scope) (untyped : List String)
    (acc : List (Option Opening)), ScOk C sc →
    NoInt (letWants.go C sc untyped acc bs) (fun res => ScOk C res.1 ∧ res.1.sigs = sc.sigs ∧
      sc.Γ <+: res.1.Γ ∧ ∃ new, res.2 = acc ++ new ∧ new.length = bs.length ∧
      (∀ o ∈ new, ∀ o' : Opening, o = some o' → o'.type.wf sc.sigs res.1.Γ.length 0 = true ∧
        ∀ e, o'.is = some e → e.wf sc.sigs res.1.Γ.length 0 = true) ∧
      (bs.all (·.ann.isSome) = true → ∀ (j : Nat) o, new[j]? = some o → ∃ o' : Opening, o = some o' ∧
        o'.id = sc.Γ.length + j ∧ o'.type.wf sc.sigs (sc.Γ.length + j) 0 = true ∧
        ∀ e, o'.is = some e → e.wf sc.sigs (sc.Γ.length + j) 0 = true))
  | [], sc, untyped, acc, hsc => by
    unfold letWants.go
    exact NoInt.pure ⟨hsc, rfl, List.prefix_refl _, [], by simp, rfl, by simp, by simp⟩
  | b :: bs, sc, untyped, acc, hsc => by
    unfold letWants.go
    cases ha : b.ann with
    | none =>
      simp only
      refine NoInt.imp (letWants_go_noInt bs sc _ _ hsc)
        fun res ⟨r1, r2, r3, new, r4, r5, r6, _⟩ => ⟨r1, r2, r3, none :: new, by simp [r4], by simp [r5],
          fun o ho o' he => ?_, fun hall => by simp [ha] at hall⟩
      rcases List.mem_cons.1 ho with rfl | ho
      · cases he
      · exact r6 o ho o' he
    | some a =>
      simp only
      refine NoInt.bind typedBefore_noInt fun _ _ => ?_
      refine NoInt.bind (opening_noInt hsc) fun o ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ?_
      refine NoInt.imp (letWants_go_noInt bs o.sc untyped _ h1)
        fun res ⟨r1, r2, r3, new, r4, r5, r6, r7⟩ => ?_
      have hle : sc.Γ.length ≤ res.1.Γ.length := by
        have := r3.length_le; omega
      refine ⟨r1, r2.trans h2, h4.trans r3, some o :: new, by simp [r4], by simp [r5], fun o₁ ho o' he => ?_,
        fun hall j o₁ hj => ?_⟩
      · rcases List.mem_cons.1 ho with rfl | ho
        · cases he
          exact ⟨Term.wf_le (by omega) (Nat.le_refl _) h6, fun e he => Term.wf_le (by omega) (Nat.le_refl _) (h7 e he)⟩
        · rw [← h2]; exact r6 o₁ ho o' he
      · simp only [List.all_cons, Bool.and_eq_true] at hall
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
          exact ⟨o, rfl, h5, h6, h7⟩
        | succ j =>
          obtain ⟨o', ho', a1, a2, a3⟩ := r7 hall.2 j o₁ (by simpa using hj)
          rw [h2, h3] at a2 a3
          refine ⟨o', ho', by rw [a1, h3]; omega, ?_, ?_⟩
          · rw [show sc.Γ.length + (j + 1) = sc.Γ.length + 1 + j by omega]; exact a2
          · intro e he; rw [show sc.Γ.length + (j + 1) = sc.Γ.length + 1 + j by omega]; exact a3 e he

/-- What a tuple `let` with no `_` in its binders gives its right-hand side is well-formed where `_` may stand for
it. -/
theorem letWants_noInt {C : Ctx} {sc : Scope} {bs : List LetBinder} (hsc : ScOk C sc) :
    NoInt (letWants C sc bs) (fun ws => ws.length = bs.length ∧
      (bs.all (·.ann.isSome) = true → Wants.wf sc.sigs sc.Γ.length 0 ws ∧ ∀ w ∈ ws, w.type.isSome = true)) := by
  unfold letWants
  refine NoInt.bind (letWants_go_noInt bs sc [] [] hsc) fun ⟨sc', opens⟩ ⟨r1, r2, r3, new, r4, r5, r6, r7⟩ => ?_
  simp only [List.nil_append] at r4 r1 r2 r3
  subst r4
  refine ⟨(NoInt.mapM (R := fun _ => True) fun x hx => ?_).1, fun ws h => ?_⟩
  · obtain ⟨b, o⟩ := x
    cases o with
    | none => exact NoInt.pure trivial
    | some o =>
      obtain ⟨a, c⟩ := r6 _ (List.of_mem_zip hx).2 o rfl
      rw [← r2] at a c
      exact NoInt.bind (abstracted_noInt r1.Γ a c) fun _ _ => NoInt.pure trivial
  · obtain ⟨hl, hi⟩ := mapM_ok h
    refine ⟨by simp [hl, r5], fun hall => ⟨fun j w hw => ?_, fun w hw => ?_⟩⟩
    · have hjl : j < bs.length := by have := (List.getElem?_eq_some_iff.1 hw).1; simp [hl, r5] at this; omega
      obtain ⟨x, hx⟩ : ∃ x, (bs.zip opens)[j]? = some x := ⟨_, List.getElem?_eq_getElem (by simp [r5]; omega)⟩
      have hx' := List.getElem?_zip_eq_some.1 hx
      obtain ⟨o, ho, h1, a, c⟩ := r7 hall j _ hx'.2
      have hab := hi j x w hx hw
      obtain ⟨xb, xo⟩ := x
      simp only at ho hab
      subst ho
      simp only [letWant] at hab
      obtain ⟨t, ht, hab⟩ := bind_eq_ok.1 hab
      simp only [pure, Except.pure, Except.ok.injEq] at hab
      subst hab
      have hids : opens.map (fun o => (o.map (·.id)).getD sc'.Γ.length) = List.range' sc.Γ.length bs.length := by
        refine List.ext_getElem? fun k => ?_
        simp only [List.getElem?_map]
        rcases Nat.lt_or_ge k bs.length with hk | hk
        · obtain ⟨o', ho', h1', -⟩ := r7 hall k (opens[k]'(by omega)) (List.getElem?_eq_getElem (by omega))
          rw [List.getElem?_eq_getElem (by omega : k < opens.length), ho']
          simp [h1', hk]
        · rw [List.getElem?_eq_none (by omega)]; simp; omega
      obtain ⟨a', c'⟩ := r6 _ (List.mem_of_getElem? hx'.2) o rfl
      rw [← r2] at a' c'
      have hA := (abstracted_noInt (name := xb.name.name) (mult := xb.mult) (pos := xb.name.pos)
        (ids := opens.map fun o => (o.map (·.id)).getD sc'.Γ.length) r1.Γ a' c').2 t ht
      rw [hids] at hA
      have hC : ∀ i en r, i < sc.Γ.length → sc'.Γ[i]? = some en → en.rule = some r →
          r.wf sc.sigs sc.Γ.length 0 = true := by
        intro i en r hi hen hr
        obtain ⟨u, hu⟩ := r3
        rw [← hu, List.getElem?_append_left hi] at hen
        exact ((hsc.Γ i en hen).2 r hr).1
      have wfab := fun (u : Term) (hu : u.wf sc.sigs (sc.Γ.length + j) 0 = true) =>
        abstract_wf (Γ := sc'.Γ) (ids := [] ++ List.range' sc.Γ.length bs.length) (K := [].length + j) hu
          (Nat.le_add_right _ _)
          (fun i hi hk => idxOf?_range'_none (Nat.le_of_lt hjl) hi (fun i h1 h2 => absurd h2 (by omega)) hk)
          (fun i k hi hk => idxOf?_range' (Nat.le_of_lt hjl) hi hk) hC
      simp only [List.nil_append, List.length_nil, Nat.zero_add] at wfab
      refine ⟨fun u hu => ?_, fun e he => ?_⟩
      · simp only [Want.of, Option.some.injEq] at hu; subst hu
        rw [hA.1]; simpa using wfab _ a
      · obtain ⟨e₀, he₀, rfl⟩ := hA.2 e he
        simpa using wfab _ (c e₀ he₀)
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hw
      have hjl : j < bs.length := by have := (List.getElem?_eq_some_iff.1 hj).1; simp [hl, r5] at this; omega
      obtain ⟨x, hx⟩ : ∃ x, (bs.zip opens)[j]? = some x := ⟨_, List.getElem?_eq_getElem (by simp [r5]; omega)⟩
      have hx' := List.getElem?_zip_eq_some.1 hx
      obtain ⟨o, ho, -⟩ := r7 hall j _ hx'.2
      have hab := hi j x w hx hj
      obtain ⟨xb, xo⟩ := x
      simp only at ho hab
      subst ho
      simp only [letWant] at hab
      obtain ⟨t, -, hab⟩ := bind_eq_ok.1 hab
      simp only [pure, Except.pure, Except.ok.injEq] at hab
      subst hab
      rfl

/-- What checking an expression from `sc` leaves: a scope meeting `ScOk` with the same signatures, no fewer entries,
and at least one result, each a well-formed term of that scope. -/
structure OutOk (C : Ctx) (sc : Scope) (o : Out) : Prop where
  ok : ScOk C o.sc
  sigs : o.sc.sigs = sc.sigs
  len : sc.Γ.length ≤ o.sc.Γ.length
  res : ∀ r ∈ o.res, r.term.wf sc.sigs o.sc.Γ.length 0 = true
  ne : o.res ≠ []

theorem produced_noInt {C : Ctx} {sc : Scope} {g : Option Given} {pos : Pos} {rs : List Res} {tree : Expr}
    (hsc : ScOk C sc) (hr : ∀ r ∈ rs, r.term.wf sc.sigs sc.Γ.length 0 = true) :
    NoInt (produced sc g pos rs tree) (fun o => o.sc = sc ∧ o.res = rs) := by
  unfold produced
  dsimp only
  cases g with
  | none => exact NoInt.pure ⟨rfl, rfl⟩
  | some g => exact NoInt.bind (against_noInt hsc.Γ hsc.sigs hr) fun _ _ => NoInt.pure ⟨rfl, rfl⟩

theorem applied_noInt {C : Ctx} {sc : Scope} {g : Option Given} {pos : Pos} {rs : List Res} {tree : Expr}
    {snaps : List Snapshot} (hsc : ScOk C sc) (hr : ∀ r ∈ rs, r.term.wf sc.sigs sc.Γ.length 0 = true) :
    NoInt (applied sc g pos rs tree snaps) (fun o => o.sc = sc ∧ o.res = rs) := by
  unfold applied
  exact NoInt.keep (NoInt.bind (produced_noInt hsc hr) fun o ⟨h1, h2⟩ => NoInt.pure ⟨h1, h2⟩)

theorem finish_noInt {C C₀ : Ctx} {whole : Bool} {g : Option Given} {e : Expr} {o : Out} {sc : Scope}
    (ho : OutOk C₀ sc o) : NoInt (finish C whole g e o) (OutOk C₀ sc) := by
  refine ⟨fun err h => ?_, fun o' h => ?_⟩
  · unfold finish at h
    have hne : (!o.res.isEmpty) = true := by simpa [List.isEmpty_iff] using ho.ne
    simp only [hne, Pledge.ensure, ↓reduceIte, pure, Except.pure, ok_bind] at h
    split at h
    · cases h
    · split at h
      · simp only [failAt_eq, bind, Except.bind, Except.error.injEq] at h; subst h; rfl
      · cases h
  · obtain ⟨hne, hsc, -, hres, -⟩ := finish_spec h
    have hres' : ∀ r ∈ o'.res, ∃ r0 ∈ o.res, r0.term = r.term := by
      intro r hr; rw [hres] at hr; split at hr
      · obtain ⟨r0, h0, rfl⟩ := List.mem_map.1 hr; exact ⟨r0, h0, rfl⟩
      · exact ⟨r, hr, rfl⟩
    refine ⟨hsc ▸ ho.ok, hsc ▸ ho.sigs, hsc ▸ ho.len, fun r hr => ?_, ?_⟩
    · obtain ⟨r0, h0, he⟩ := hres' r hr
      rw [← he, hsc]; exact ho.res r0 h0
    · rw [hres]; split <;> simpa using hne

theorem unmarked_noInt {args : List Arg} {why : Unit → String} : NoInt (unmarked args why) (fun _ => True) := by
  unfold unmarked; split
  · exact NoInt.failAt
  · exact NoInt.pure trivial

theorem NoInt.ok_true {α : Type} {a : α} : NoInt (Except.ok a : CheckM α) (fun _ => True) :=
  ⟨fun _ h => (nomatch h), fun _ _ => trivial⟩

theorem NoInt.mapIdxM {γ δ : Type} {f : Nat → γ → CheckM δ} (hf : ∀ i a, NoInt (f i a) (fun _ => True)) :
    ∀ (l : List γ), NoInt (l.mapIdxM f) (fun _ => True) := by
  intro l
  unfold List.mapIdxM
  suffices ∀ (l : List γ) (acc : Array δ), NoInt (List.mapIdxM.go f l acc) (fun _ => True) from this l #[]
  intro l
  induction l with
  | nil => intro acc; exact NoInt.pure trivial
  | cons a l ih => intro acc; exact NoInt.bind (hf _ a) fun b _ => ih _

theorem marks_noInt {pos : Pos} {args : List Arg} {name : String} {sig : FnSig} {fn : FnCtx} :
    NoInt (marks pos args name sig fn) (fun _ => True) := by
  unfold marks
  dsimp only
  split
  · simp only [pure, Except.pure, ok_bind]
    refine NoInt.bind (NoInt.mapIdxM (fun i a => ?_) _) fun _ _ => ?_
    · repeat (first | exact NoInt.failAt | exact NoInt.ok_true | exact NoInt.pure trivial | split)
    · split
      · exact NoInt.failAt_bind
      · exact NoInt.pure trivial
  · exact NoInt.failAt_bind

/-- The decrease check of §9 at a call whose marks passed: the positions it reads are there. -/
theorem decrease_noInt {sc : Scope} {pos : Pos} {args : List Arg} {rs : List Res} {fn : FnCtx} {subs : List Nat}
    {k : Nat} (hk : k < subs.length) (hf : k < fn.subterms.length) (hr : ∀ p ∈ subs, p < rs.length) :
    NoInt (decrease sc pos args rs fn subs k) (fun _ => True) := by
  unfold decrease
  refine NoInt.forM fun j hj => ?_
  have hj' : j < k + 1 := List.mem_range.1 hj
  rw [List.getElem?_eq_getElem (show j < subs.length by omega)]
  simp only
  rw [List.getElem?_eq_getElem (show subs[j] < rs.length from hr _ (List.getElem_mem _))]
  simp only
  rw [List.getElem?_eq_getElem (show j < fn.subterms.length by omega)]
  simp only
  repeat (first | exact NoInt.failAt | exact NoInt.ok_true | exact NoInt.pure trivial | split)

theorem NoInt.of_ok {α : Type} {x : CheckM α} {P : α → Prop} (h : NoInt x (fun _ => True))
    (hp : ∀ a, x = .ok a → P a) : NoInt x P := ⟨h.1, hp⟩

theorem dataCtors_noInt {C : Ctx} {sc : Scope} {t : Term} {pos : Pos} (hsc : ScOk C sc)
    (ht : t.wf sc.sigs sc.Γ.length 0 = true) :
    NoInt (dataCtors C sc t pos) (fun ctors => ∀ c sig, (c, sig) ∈ ctors → sc.sigs.find ⟨.ctor, c⟩ = some sig) := by
  refine NoInt.of_ok ?_ fun ctors h => by
    obtain ⟨_, _, _, _, _, -, -, -, -, h⟩ := dataCtors_spec h; exact h
  obtain ⟨ty, hty, -⟩ := typeOf_wf hsc.Γ hsc.sigs ht
  unfold dataCtors
  simp only [Scope.typeOf, hty, pure, Except.pure, ok_bind]
  split
  · rename_i h args hc
    split
    · rename_i T cs hg
      obtain ⟨hn, hm⟩ := hsc.global hg
      have hcs := (hsc.globals _ hm).2 cs rfl
      refine NoInt.imp (NoInt.mapM (R := fun _ => True) fun c hc => ?_) fun _ _ => trivial
      obtain ⟨s, hs⟩ := hcs c hc
      exact NoInt.bind (sig_noInt hs) fun _ _ => NoInt.ok_true
    all_goals exact NoInt.failAt
  · exact NoInt.failAt

/-- What every forcing of a well-formed scope leaves: none stuck, and a well-formed longer scope with the fields'
entries in it. -/
def FsOk (S : Sigs) (n : Nat) (fs : List Forcing) : Prop :=
  ∀ f ∈ fs, (∀ msg, f.forced ≠ .stuck msg) ∧ ∀ Γ ids, f.forced = .ok Γ ids → Entries.Wf S Γ ∧ n ≤ Γ.length ∧
    ∀ i ∈ ids, i < Γ.length

theorem forcings_noInt {C : Ctx} {sc : Scope} {t : Term} {sp at_ : Pos} {pats : List Pattern} {erased : Bool}
    (hsc : ScOk C sc) (ht : t.wf sc.sigs sc.Γ.length 0 = true) :
    NoInt (forcings C sc t sp pats at_ erased) (fun fs => FsOk sc.sigs sc.Γ.length fs ∧
      ∀ p ∈ pats, ∃ f ∈ fs, f.name = p.ctor.name) := by
  refine NoInt.of_ok ?_ fun fs h => ?_
  · unfold forcings
    refine NoInt.bind (dataCtors_noInt hsc ht) fun ctors hctors => ?_
    refine NoInt.bind (NoInt.foldlM (I := fun _ => True) trivial fun s _ p _ => ?_) fun _ _ => ?_
    · dsimp only
      repeat (first | exact NoInt.failAt_bind | exact NoInt.failAt | exact NoInt.pure trivial | split |
        (simp only [pure, Except.pure, ok_bind]))
    · refine NoInt.imp (NoInt.mapM (R := fun _ => True) fun x hx => ?_) fun _ _ => trivial
      obtain ⟨n, sig⟩ := x
      have hs := hctors n sig hx
      dsimp only
      split
      · rename_i msg hm
        exact absurd hm (force_not_stuck hsc.Γ hsc.sigs (by rw [Sigs.find_head hs]; exact hs) ht)
      · exact NoInt.pure trivial
  · obtain ⟨ctors, hc, hpats, hl, hi⟩ := forcings_spec h
    have hctors := (dataCtors_noInt (pos := sp) hsc ht).2 ctors hc
    refine ⟨fun f hf => ?_, fun p hp => ?_⟩
    · obtain ⟨i, hfi⟩ := List.getElem?_of_mem hf
      obtain ⟨sig, mk, hci, hforce, -, hns, -⟩ := hi i f hfi
      refine ⟨hns, fun Γ ids hok => ?_⟩
      have hs := hctors _ _ (List.mem_of_getElem? hci)
      have := force_wf mk hsc.Γ hsc.sigs (by rw [Sigs.find_head hs]; exact hs) ht
      rw [← hforce, hok] at this
      obtain ⟨h1, h2, h3⟩ := this
      refine ⟨h1, by omega, fun j hj => ?_⟩
      rw [h3, List.mem_range'_1] at hj
      omega
    · obtain ⟨sig, hm, -⟩ := hpats p hp
      obtain ⟨i, hci⟩ := List.getElem?_of_mem hm
      obtain ⟨f, hf⟩ : ∃ f, fs[i]? = some f :=
        ⟨_, List.getElem?_eq_getElem (by rw [hl]; exact (List.getElem?_eq_some_iff.1 hci).1)⟩
      obtain ⟨sig', mk, hci', -⟩ := hi i f hf
      rw [hci] at hci'
      simp only [Option.some.injEq, Prod.mk.injEq] at hci'
      exact ⟨f, List.mem_of_getElem? hf, hci'.1.symm⟩

theorem survivor_noInt {sc : Scope} {fs : List Forcing} {n : String} {pos : Pos} {cons : String} {S : Sigs} {m : Nat}
    (hfs : FsOk S m fs) (hn : ∃ f ∈ fs, f.name = n) :
    NoInt (survivor sc fs n pos cons) (fun p => Entries.Wf S p.1 ∧ m ≤ p.1.length ∧ ∀ i ∈ p.2, i < p.1.length) := by
  unfold survivor
  split
  · rename_i n' Γ ids pat hf
    exact NoInt.pure ((hfs _ (List.mem_of_find?_eq_some hf)).2 Γ ids rfl)
  · exact NoInt.failAt
  · rename_i hf
    exact absurd rfl ((hfs _ (List.mem_of_find?_eq_some hf)).1 _)
  · rename_i hf
    obtain ⟨f, hf', rfl⟩ := hn
    exact absurd (List.find?_eq_none.1 hf f hf') (by simp)

theorem ScOk.forced {C : Ctx} {sc : Scope} {Γ : Entries} {ids : List Nat} {t : Option Pos} {ns : List Id}
    (hsc : ScOk C sc) (hΓ : Entries.Wf sc.sigs Γ) (hl : sc.Γ.length ≤ Γ.length) (hi : ∀ i ∈ ids, i < Γ.length) :
    ScOk C (Scope.bind { sc with Γ, taintedBy := t } ns (fieldRes ids)) := by
  refine ScOk.bind (hsc.grow rfl hΓ hl fun p hp => .inl hp) fun r hr => ?_
  simp only [fieldRes, List.mem_map] at hr
  obtain ⟨i, hi', rfl⟩ := hr
  simpa [Term.wf] using hi i hi'

theorem patBind_noInt {C : Ctx} {sc : Scope} {r : Res} {rhsPos : Pos} {ct : Bool} {pat : Pattern} {fs : List Forcing}
    (hsc : ScOk C sc) (hfs : FsOk sc.sigs sc.Γ.length fs) (hn : ∃ f ∈ fs, f.name = pat.ctor.name) :
    NoInt (patBind sc r rhsPos ct pat fs) (fun sc' => ScOk C sc' ∧ sc'.sigs = sc.sigs ∧
      sc.Γ.length ≤ sc'.Γ.length) := by
  unfold patBind
  refine NoInt.bind (survivor_noInt hfs hn) fun ⟨Γ, ids⟩ ⟨h1, h2, h3⟩ => ?_
  have fin : NoInt (pure (Scope.bind { sc with Γ, taintedBy := reach sc r rhsPos } pat.fields (fieldRes ids)) :
      CheckM Scope) (fun sc' => ScOk C sc' ∧ sc'.sigs = sc.sigs ∧ sc.Γ.length ≤ sc'.Γ.length) :=
    NoInt.pure ⟨hsc.forced h1 h2 h3, by rw [Scope.bind_eq], by rw [Scope.bind_eq]; exact h2⟩
  dsimp only
  split
  · exact fin
  · split
    · exact NoInt.failAt_bind
    · exact fin

def Tele.shaped : Tele → Bool
  | .binders bs => !bs.isEmpty
  | .hole _ => true

mutual
  /-- The program as the checking pass's internal checks are proved unreachable for it: no `removed`, no `comptime`
  below the top level, and at least one element, binder or annotation entry where the grammar has one. -/
  def Expr.shaped : Expr → Bool
    | .var _ => true
    | .app _ args => Expr.shapedArgs args
    | .tuple _ es => !es.isEmpty && Expr.shapedList es
    | .block ss f => Expr.shapedStmts ss && f.shaped
    | .match _ _ s ann bs => s.shaped && Tele.shaped ann && Expr.shapedBranches bs
    | .sorry _ t => Tele.shaped t
    | .removed => false
  def Expr.shapedList : List Expr → Bool
    | [] => true
    | e :: es => e.shaped && Expr.shapedList es
  def Expr.shapedArgs : List Arg → Bool
    | [] => true
    | .mk _ e :: as => e.shaped && Expr.shapedArgs as
  def Expr.shapedStmts : List Stmt → Bool
    | [] => true
    | s :: ss => Stmt.shaped s && Expr.shapedStmts ss
  def Expr.shapedBranches : List Branch → Bool
    | [] => true
    | .mk _ b :: bs => b.shaped && Expr.shapedBranches bs
  def Stmt.shaped : Stmt → Bool
    | .let _ bs rhs => !bs.isEmpty && rhs.shaped
    | .patlet _ ct _ _ rhs => !ct && rhs.shaped
    | .inspect _ => true
end

/-- `checkExpr` reports no internal error from a scope meeting `ScOk`, given what meets `GivenOk`. -/
def ExprNI (e : Expr) : Prop :=
  ∀ (C : Ctx) (sc : Scope) (g : Option Given), ScOk C sc → e.shaped = true →
    (∀ g', g = some g' → GivenOk sc.sigs sc.Γ.length g') → NoInt (checkExpr C sc g e) (OutOk C sc)

def StmtNI (s : Stmt) : Prop :=
  ∀ (C : Ctx) (sc : Scope), ScOk C sc → s.shaped = true →
    NoInt (checkStmt C sc s) (fun o => ScOk C o.sc ∧ o.sc.sigs = sc.sigs ∧ sc.Γ.length ≤ o.sc.Γ.length)

theorem GivenOk.erase {S : Sigs} {n : Nat} {g : Given} (h : GivenOk S n g) : GivenOk S n g.erase := by
  refine ⟨h.env, fun hw j w hj => ?_, fun hw => ?_⟩
  · simp only [Given.erase, List.getElem?_map, Option.map_eq_some_iff] at hj
    obtain ⟨w', hw', rfl⟩ := hj
    exact h.wants hw j w' hw'
  · obtain ⟨h1, h2⟩ := h.whole hw
    refine ⟨by simpa [Given.erase] using h1, fun w hw' => ?_⟩
    simp only [Given.erase, List.mem_map] at hw'
    obtain ⟨w', hw'', rfl⟩ := hw'
    exact h2 w' hw''

theorem OutOk.of {C : Ctx} {sc sc' : Scope} {rs : List Res} {tree : Expr} {snaps : List Snapshot}
    (h : ScOk C sc') (hs : sc'.sigs = sc.sigs) (hl : sc.Γ.length ≤ sc'.Γ.length)
    (hr : ∀ r ∈ rs, r.term.wf sc.sigs sc'.Γ.length 0 = true) (hne : rs ≠ []) : OutOk C sc ⟨sc', rs, tree, snaps⟩ :=
  ⟨h, hs, hl, hr, hne⟩

theorem NoInt.notValue {α β : Type} {C : Ctx} {sc : Scope} {n : Name} {f : α → CheckM β} {R : β → Prop} :
    NoInt (Pledge.notValue C sc n >>= f) R := by unfold Pledge.notValue; exact NoInt.failAt_bind

theorem NoInt.notValue' {α : Type} {C : Ctx} {sc : Scope} {n : Name} {R : α → Prop} :
    NoInt (Pledge.notValue C sc n : CheckM α) R := by unfold Pledge.notValue; exact NoInt.failAt

theorem OutOk.ctx {C C' : Ctx} {sc : Scope} {o : Out} (h : OutOk C sc o) (hg : C'.globals = C.globals) :
    OutOk C' sc o := ⟨h.ok.ctx hg, h.sigs, h.len, h.res, h.ne⟩

theorem given_erased {S : Sigs} {n : Nat} {g : Option Given} (hg : ∀ g', g = some g' → GivenOk S n g') (b : Bool) :
    ∀ g', (if b = true then g.map (·.erase) else g) = some g' → GivenOk S n g' := by
  intro g' h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨g'', h1, rfl⟩ := h
    exact (hg g'' h1).erase
  · exact hg g' h

theorem var_noInt (x : Id) : ExprNI (.var x) := by
  intro C sc g hsc hok hg
  unfold checkExpr
  dsimp only
  refine NoInt.bind ?_ fun o ho => finish_noInt ho
  obtain ⟨name, pos⟩ := x
  cases name with
  | none => exact NoInt.failAt
  | some n =>
    simp only
    split
    · rename_i r hr
      exact NoInt.imp (produced_noInt hsc (by simpa using hsc.lookup hr)) fun o ⟨h1, h2⟩ => by
        obtain ⟨osc, ores, otree, osn⟩ := o
        simp only at h1 h2; subst h1 h2
        exact OutOk.of hsc rfl (Nat.le_refl _) (by simpa using hsc.lookup hr) (by simp)
    · exact NoInt.notValue'

theorem sorry_noInt (p : Pos) (t : Tele) : ExprNI (.sorry p t) := by
  intro C sc g hsc hok hg
  unfold checkExpr
  dsimp only
  refine NoInt.bind ?_ fun o ho => finish_noInt ho
  have hg' := given_erased hg C.erased
  generalize (if C.erased = true then Option.map (fun x => x.erase) g else g) = g' at hg' ⊢
  simp only [Expr.shaped] at hok
  refine NoInt.bind (annotation_noInt (hsc.ctx rfl) hg' fun bs he => ?_) fun ⟨tele, env⟩ ⟨h1, h2, h3⟩ => ?_
  · subst he
    simpa [Tele.shaped] using hok
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := opened_ok (kind := "sorry") (pos := p) (taint := fun _ => true) hsc h3 h2
  refine NoInt.imp (produced_noInt o1 (by rw [o2]; exact o6)) fun o ⟨e1, e2⟩ => ?_
  obtain ⟨osc, ores, otree, osn⟩ := o
  simp only at e1 e2; subst e1 e2
  exact OutOk.of o1 o2 (by have := o4.length_le; omega) (by rw [← o2]; exact o6)
    (by intro h; simp only at h1; rw [← List.length_eq_zero_iff, o5] at h; exact h1 (List.eq_nil_of_length_eq_zero h))

theorem removed_noInt : ExprNI .removed := by
  intro C sc g hsc hok hg
  simp [Expr.shaped] at hok

theorem elems_noInt {es : List Expr} (ih : ∀ e ∈ es, ExprNI e) :
    ∀ {C : Ctx} {sc : Scope} {g : Option Given} {prev : List Res}, ScOk C sc → Expr.shapedList es = true →
      NoInt (checkElems C sc g prev es) (fun o => ScOk C o.sc ∧ o.sc.sigs = sc.sigs ∧
        sc.Γ.length ≤ o.sc.Γ.length ∧ o.res.length = es.length ∧
        ∀ r ∈ o.res, r.term.wf sc.sigs o.sc.Γ.length 0 = true) := by
  induction es with
  | nil => intro C sc g prev hsc _; unfold checkElems; exact NoInt.pure ⟨hsc, rfl, Nat.le_refl _, rfl, by simp⟩
  | cons e es ihs =>
    intro C sc g prev hsc hok
    simp only [Expr.shapedList, Bool.and_eq_true] at hok
    unfold checkElems
    refine NoInt.bind (ih e List.mem_cons_self C sc _ hsc hok.1 fun g' hg' => ?_) fun o ho => ?_
    · simp only [elemGiven, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hg'
      obtain ⟨_, _, _, _, rfl⟩ := hg'
      exact GivenOk.of_not_whole rfl
    refine NoInt.bind (NoInt.keep NoInt.single) fun r hr => ?_
    refine NoInt.bind (NoInt.keep (ihs (fun e' he' => ih e' (List.mem_cons_of_mem _ he')) ho.ok hok.2))
      fun rest ⟨r1, r2, r3, r4, r5⟩ => NoInt.pure ⟨r1, r2.trans ho.sigs, Nat.le_trans ho.len r3, by simp [r4], ?_⟩
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact Term.wf_le r3 (Nat.le_refl _) (ho.res r' (by rw [hr]; exact List.mem_cons_self))
    · rw [← ho.sigs]; exact r5 r' hr'

theorem tuple_noInt (p : Pos) {es : List Expr} (ih : ∀ e ∈ es, ExprNI e) : ExprNI (.tuple p es) := by
  intro C sc g hsc hok hg
  unfold checkExpr
  dsimp only
  refine NoInt.bind ?_ fun o ho => finish_noInt ho
  simp only [Expr.shaped, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hok
  have rest : NoInt (do
      let o ← checkElems (C.enter (C.erased || Option.any (fun x => x.allErased) g)) sc
        (if C.erased = true then Option.map (fun x => x.erase) g else g) [] es
      pure (⟨o.sc, o.res, .tuple p o.trees, o.snaps⟩ : Out)) (OutOk C sc) :=
    NoInt.bind (elems_noInt ih (hsc.ctx rfl) hok.2) fun o ⟨h1, h2, h3, h4, h5⟩ =>
      NoInt.pure (OutOk.of (h1.ctx rfl) h2 h3 h5 (by
        intro h; rw [h] at h4; exact hok.1 (List.eq_nil_of_length_eq_zero h4.symm)))
  split
  · split
    · exact NoInt.miscount_bind
    · exact rest
  · exact rest

theorem stmts_noInt {ss : List Stmt} (ih : ∀ s ∈ ss, StmtNI s) :
    ∀ {C : Ctx} {sc : Scope}, ScOk C sc → Expr.shapedStmts ss = true →
      NoInt (checkStmts C sc ss) (fun o => ScOk C o.sc ∧ o.sc.sigs = sc.sigs ∧ sc.Γ.length ≤ o.sc.Γ.length) := by
  induction ss with
  | nil => intro C sc hsc _; unfold checkStmts; exact NoInt.pure ⟨hsc, rfl, Nat.le_refl _⟩
  | cons s ss ihs =>
    intro C sc hsc hok
    simp only [Expr.shapedStmts, Bool.and_eq_true] at hok
    unfold checkStmts
    refine NoInt.bind (ih s List.mem_cons_self C sc hsc hok.1) fun o ⟨h1, h2, h3⟩ => ?_
    refine NoInt.bind (NoInt.keep (ihs (fun s' hs' => ih s' (List.mem_cons_of_mem _ hs')) h1 hok.2))
      fun rest ⟨r1, r2, r3⟩ => NoInt.pure ⟨r1, r2.trans h2, Nat.le_trans h3 r3⟩

theorem block_noInt {ss : List Stmt} {f : Expr} (ihs : ∀ s ∈ ss, StmtNI s) (ihf : ExprNI f) :
    ExprNI (.block ss f) := by
  intro C sc g hsc hok hg
  unfold checkExpr
  dsimp only
  refine NoInt.bind ?_ fun o ho => finish_noInt ho
  have hg' := given_erased hg C.erased
  generalize (if C.erased = true then Option.map (fun x => x.erase) g else g) = g' at hg' ⊢
  simp only [Expr.shaped, Bool.and_eq_true] at hok
  refine NoInt.bind (stmts_noInt ihs (hsc.ctx rfl) hok.1) fun s ⟨s1, s2, s3⟩ => ?_
  refine NoInt.bind (NoInt.keep (ihf _ s.sc g' s1 hok.2 fun g'' h => by rw [s2]; exact (hg' g'' h).mono s3))
    fun o ho => NoInt.pure ?_
  exact OutOk.of (hsc.grow (sc' := { o.sc with names := sc.names }) (ho.sigs.trans s2) ho.ok.Γ
    (Nat.le_trans s3 ho.len) fun p hp => .inl hp) (ho.sigs.trans s2) (Nat.le_trans s3 ho.len)
    (by rw [← s2]; exact ho.res) ho.ne

theorem args_noInt {args : List Arg} (ih : ∀ a ∈ args, ExprNI a.expr) :
    ∀ {C : Ctx} {sc : Scope} {owner role : String} {erased : Bool} {params : Telescope} {prev : List Res},
      ScOk C sc → Expr.shapedArgs args = true → params.length = args.length →
      NoInt (checkArgs C sc owner role erased params prev args) (fun a => ScOk C a.sc ∧ a.sc.sigs = sc.sigs ∧
        sc.Γ.length ≤ a.sc.Γ.length ∧ a.res.length = args.length ∧
        ∀ r ∈ a.res, r.term.wf sc.sigs a.sc.Γ.length 0 = true) := by
  induction args with
  | nil => intro C sc _ _ _ _ _ hsc _ _; unfold checkArgs; exact NoInt.pure ⟨hsc, rfl, Nat.le_refl _, rfl, by simp⟩
  | cons arg args ihs =>
    intro C sc owner role erased params prev hsc hok hl
    obtain ⟨m, e⟩ := arg
    cases params with
    | nil => simp at hl
    | cons p ps =>
      simp only [Expr.shapedArgs, Bool.and_eq_true] at hok
      unfold checkArgs
      dsimp only
      have cont : ∀ o : Out, (ScOk C o.sc ∧ o.sc.sigs = sc.sigs ∧ sc.Γ.length ≤ o.sc.Γ.length ∧
          ∀ r ∈ o.res, r.term.wf sc.sigs o.sc.Γ.length 0 = true) → NoInt (do
            let r ← keep o.snaps (single e.pos o.res)
            let rest ← keep o.snaps (checkArgs C o.sc owner role erased ps (prev ++ [r]) args)
            pure (⟨rest.sc, r :: rest.res, .mk m o.tree :: rest.trees, o.snaps ++ rest.snaps⟩ : ArgsOut))
          (fun a => ScOk C a.sc ∧ a.sc.sigs = sc.sigs ∧ sc.Γ.length ≤ a.sc.Γ.length ∧
            a.res.length = (Arg.mk m e :: args).length ∧
            ∀ r ∈ a.res, r.term.wf sc.sigs a.sc.Γ.length 0 = true) := by
        intro o ⟨h1, h2, h3, h4⟩
        refine NoInt.bind (NoInt.keep NoInt.single) fun r hr => ?_
        refine NoInt.bind (NoInt.keep (ihs (fun a ha => ih a (List.mem_cons_of_mem _ ha)) h1 hok.2
          (by simpa using hl))) fun rest ⟨r1, r2, r3, r4, r5⟩ =>
            NoInt.pure ⟨r1, r2.trans h2, Nat.le_trans h3 r3, by simp [r4], ?_⟩
        intro r' hr'
        rcases List.mem_cons.1 hr' with rfl | hr'
        · exact Term.wf_le r3 (Nat.le_refl _) (h4 r' (by rw [hr]; exact List.mem_cons_self))
        · rw [← h2]; exact r5 r' hr'
      split
      · rename_i hh
        obtain ⟨pp, rfl⟩ : ∃ pp, e = .var ⟨none, pp⟩ := by
          cases e with
          | var x =>
            obtain ⟨n, pp⟩ := x
            cases n with
            | none => exact ⟨pp, rfl⟩
            | some => simp [isHole] at hh
          | _ => simp [isHole] at hh
        exact NoInt.bind holeArg_noInt fun o ⟨e1, r, e2, e3⟩ => cont o
          ⟨e1 ▸ hsc, by rw [e1], by rw [e1]; exact Nat.le_refl _, by
            rw [e2, e1]; intro r' hr'; rw [List.mem_singleton.1 hr']; exact e3⟩
      · exact NoInt.bind (ih (.mk m e) List.mem_cons_self C sc _ hsc hok.1 fun g' hg' => by
          cases hg'; exact GivenOk.of_not_whole rfl) fun o ho => cont o ⟨ho.ok, ho.sigs, ho.len, ho.res⟩

theorem NoInt.map {α β : Type} {x : CheckM α} {Q : α → Prop} {f : α → β} (h : NoInt x Q) :
    NoInt (f <$> x) (fun b => ∃ a, Q a ∧ b = f a) := by
  cases hx : x with
  | ok a =>
    rw [hx] at h
    exact NoInt.ok (rfl : (f <$> (Except.ok a : CheckM α)) = .ok (f a)) ⟨a, h.2 a rfl, rfl⟩
  | error e =>
    rw [hx] at h
    exact ⟨fun e' h' => by cases h'; exact h.1 e rfl, fun _ h' => by cases h'⟩

theorem app_noInt (hd : Name) {args : List Arg} (ih : ∀ a ∈ args, ExprNI a.expr) : ExprNI (.app hd args) := by
  intro C sc g hsc hok hg
  unfold checkExpr
  dsimp only
  refine NoInt.bind ?_ fun o ho => finish_noInt ho
  have hg' := given_erased hg C.erased
  generalize (if C.erased = true then Option.map (fun x => x.erase) g else g) = g' at hg' ⊢
  generalize (C.erased || Option.any (fun x => x.allErased) g) = w
  simp only [Expr.shaped] at hok
  have hsc' : ScOk (C.enter w) sc := hsc.ctx rfl
  cases hgl : (C.enter w).global hd.name with
  | none => unfold notApplied; exact NoInt.failAt
  | some gl =>
    obtain ⟨hn, hm⟩ := hsc'.global hgl
    cases gl with
    | fn nm sig =>
      cases sig with
      | none => exact NoInt.failAt
      | some sig =>
        simp only [Global.name] at hn
        subst hn
        obtain ⟨hpw, hrw, hsub, hrne⟩ := hsc.globals _ hm
        simp only
        have rest : ∀ plan : Option (List Nat × Nat), (∀ fn subs k, (C.fn.filter (·.group.contains hd.name)) = some fn →
            plan = some (subs, k) → k < subs.length ∧ k < fn.subterms.length ∧ ∀ p ∈ subs, p < sig.params.length) →
            NoInt (do
              arity hd.pos hd.name sig.params.length args.length
              let a ← checkArgs (C.enter w) sc hd.name "parameter" false sig.params [] args
              keep a.snaps (match (C.fn.filter (·.group.contains hd.name), plan) with
                | (some fn, some (subs, k)) => do
                  decrease a.sc hd.pos args a.res fn subs k
                  applied (opened a.sc sig.returns (a.res.map (·.term)) hd.name hd.pos fun _ =>
                      sig.tainted || a.res.any (·.tainted)).1 g' hd.pos
                    (opened a.sc sig.returns (a.res.map (·.term)) hd.name hd.pos fun _ =>
                      sig.tainted || a.res.any (·.tainted)).2 (.app hd a.trees) a.snaps
                | _ => applied (opened a.sc sig.returns (a.res.map (·.term)) hd.name hd.pos fun _ =>
                      sig.tainted || a.res.any (·.tainted)).1 g' hd.pos
                    (opened a.sc sig.returns (a.res.map (·.term)) hd.name hd.pos fun _ =>
                      sig.tainted || a.res.any (·.tainted)).2 (.app hd a.trees) a.snaps))
              (OutOk C sc) := by
          intro plan hplan
          refine NoInt.bind NoInt.arity fun _ har => ?_
          refine NoInt.bind (args_noInt ih hsc' hok har.symm) fun a ⟨a1, a2, a3, a4, a5⟩ => ?_
          have hgm := a1.globals _ hm
          simp only at hgm
          obtain ⟨-, hrw', -, -⟩ := hgm
          rw [a2] at hrw'
          obtain ⟨o1, o2, o3, o4, o5, o6⟩ := opened_ok (sc := a.sc) (tele := sig.returns)
            (env := a.res.map (·.term)) (kind := hd.name) (pos := hd.pos)
            (taint := fun _ => sig.tainted || a.res.any (·.tainted)) a1
            (by rw [a2]; simpa [a4, har] using hrw') (by simpa [a2] using a5)
          have tail : NoInt (applied _ g' hd.pos _ (.app hd a.trees) a.snaps) (OutOk C sc) :=
            NoInt.imp (applied_noInt (rs := (opened a.sc sig.returns (a.res.map (·.term)) hd.name hd.pos fun _ =>
              sig.tainted || a.res.any (·.tainted)).2) o1 (by rw [o2]; exact o6)) fun o ⟨e1, e2⟩ => by
              obtain ⟨osc, ores, otree, osn⟩ := o
              simp only at e1 e2; subst e1 e2
              exact OutOk.of (o1.ctx rfl) (o2.trans a2) (Nat.le_trans a3 o4.length_le)
                (by rw [← a2, ← o2]; exact o6) (by
                  intro h; rw [← List.length_eq_zero_iff, o5] at h; exact hrne (List.eq_nil_of_length_eq_zero h))
          refine NoInt.keep ?_
          split
          · rename_i fn subs k heq
            simp only [Prod.mk.injEq] at heq
            obtain ⟨k1, k2, k3⟩ := hplan fn subs k heq.1 heq.2
            exact NoInt.bind (decrease_noInt k1 k2 fun p hp => by rw [a4, har]; exact k3 p hp) fun _ _ =>
              tail
          · exact tail
        split
        · rename_i fn hfn
          refine NoInt.bind (NoInt.map (NoInt.of_ok (marks_noInt (pos := hd.pos) (args := args) (name := hd.name)
            (sig := sig) (fn := fn)) fun sk h => marks_spec h)) fun plan ⟨⟨subs, k⟩, hsk, hpl⟩ => rest plan ?_
          intro fn' subs' k' hfn' hpl'
          rw [hfn] at hfn'; cases hfn'
          rw [hpl] at hpl'; cases hpl'
          obtain ⟨hs, hk1, hk2⟩ := hsk
          simp only at hs hk1 hk2
          refine ⟨hk1, hk2, fun p hp => ?_⟩
          rw [hs, List.mem_filter, List.mem_range] at hp
          omega
        · refine NoInt.bind unmarked_noInt fun _ _ => ?_
          exact NoInt.bind (NoInt.pure (P := fun p => p = none) rfl) fun plan hpl => rest plan fun _ _ _ _ h => by
            rw [hpl] at h; cases h
    | type nm cs d =>
      simp only [Global.name] at hn
      subst hn
      obtain ⟨⟨s, hs⟩, -⟩ := hsc.globals _ hm
      refine NoInt.bind unmarked_noInt fun _ _ => ?_
      refine NoInt.bind (sig_noInt hs) fun s' ⟨hss, _⟩ => ?_
      subst hss
      refine NoInt.bind NoInt.arity fun _ har => ?_
      refine NoInt.bind (args_noInt ih (hsc'.ctx rfl) hok har.symm) fun a ⟨a1, a2, a3, a4, a5⟩ => ?_
      refine NoInt.imp (applied_noInt (a1.ctx rfl) ?_) ?_
      · intro r hr
        rw [List.mem_singleton.1 hr, a2]
        exact Term.wf_app.2 ⟨⟨s', by rw [Sigs.find_head hs]; exact hs, by simp [a4, har]⟩, by simpa using a5⟩
      · intro o ⟨e1, e2⟩
        obtain ⟨osc, ores, otree, osn⟩ := o
        simp only at e1 e2; subst e1 e2
        refine OutOk.of (a1.ctx rfl) a2 a3 (fun r hr => ?_) (by simp)
        rw [List.mem_singleton.1 hr]
        exact Term.wf_app.2 ⟨⟨s', by rw [Sigs.find_head hs]; exact hs, by simp [a4, har]⟩, by simpa using a5⟩
    | ctor nm =>
      simp only [Global.name] at hn
      subst hn
      obtain ⟨s, hs⟩ := hsc.globals _ hm
      refine NoInt.bind unmarked_noInt fun _ _ => ?_
      refine NoInt.bind (sig_noInt hs) fun s' ⟨hss, _⟩ => ?_
      subst hss
      refine NoInt.bind NoInt.arity fun _ har => ?_
      refine NoInt.bind (args_noInt ih (hsc'.ctx rfl) hok har.symm) fun a ⟨a1, a2, a3, a4, a5⟩ => ?_
      refine NoInt.imp (applied_noInt (a1.ctx rfl) ?_) ?_
      · intro r hr
        rw [List.mem_singleton.1 hr, a2]
        exact Term.wf_app.2 ⟨⟨s', by rw [Sigs.find_head hs]; exact hs, by simp [a4, har]⟩, by simpa using a5⟩
      · intro o ⟨e1, e2⟩
        obtain ⟨osc, ores, otree, osn⟩ := o
        simp only at e1 e2; subst e1 e2
        refine OutOk.of (a1.ctx rfl) a2 a3 (fun r hr => ?_) (by simp)
        rw [List.mem_singleton.1 hr]
        exact Term.wf_app.2 ⟨⟨s', by rw [Sigs.find_head hs]; exact hs, by simp [a4, har]⟩, by simpa using a5⟩

theorem Telescope.entriesBelow_of_wf {S : Sigs} {n : Nat} :
    ∀ {k : Nat} {tele : Telescope}, Telescope.wf S n k tele = true → tele.all (·.entriesBelow n) = true
  | _, [], _ => rfl
  | k, b :: bs, h => by
    simp only [Telescope.wf, Bool.and_eq_true, Option.all_eq_true] at h
    simp only [List.all_cons, Bool.and_eq_true, TBinder.entriesBelow, Option.all_eq_true]
    exact ⟨⟨Term.entriesBelow_of_wf h.1.1, fun e he => Term.entriesBelow_of_wf (h.1.2 e he)⟩,
      Telescope.entriesBelow_of_wf h.2⟩

theorem branches_noInt {bs : List Branch} (ih : ∀ b ∈ bs, ExprNI b.body) :
    ∀ {C : Ctx} {inner : Scope} {r : Res} {sp : Pos} {fs : List Forcing} {g : Given}, ScOk C inner →
      FsOk inner.sigs inner.Γ.length fs → (∀ b ∈ bs, ∃ f ∈ fs, f.name = b.pat.ctor.name) →
      GivenOk inner.sigs inner.Γ.length g → Expr.shapedBranches bs = true →
      NoInt (checkBranches C inner r sp fs g bs) (fun _ => True) := by
  induction bs with
  | nil => intro C inner r sp fs g _ _ _ _ _; unfold checkBranches; exact NoInt.pure trivial
  | cons b bs ihs =>
    intro C inner r sp fs g hsc hfs hn hg hok
    obtain ⟨pat, body⟩ := b
    simp only [Expr.shapedBranches, Bool.and_eq_true] at hok
    unfold checkBranches
    refine NoInt.bind (survivor_noInt hfs (hn _ List.mem_cons_self)) fun ⟨Γ, ids⟩ ⟨h1, h2, h3⟩ => ?_
    have hb := hsc.forced (t := reach inner r sp) (ns := pat.fields) h1 h2 h3
    have hbs : (Scope.bind { inner with Γ, taintedBy := reach inner r sp } pat.fields
        (fieldRes ids)).sigs = inner.sigs := by rw [Scope.bind_eq]
    have hbl : inner.Γ.length ≤ (Scope.bind { inner with Γ, taintedBy := reach inner r sp } pat.fields
        (fieldRes ids)).Γ.length := by rw [Scope.bind_eq]; exact h2
    refine NoInt.bind (ih _ List.mem_cons_self C _ _ hb hok.1 fun g' hg' => by
      cases hg'; rw [hbs]; exact hg.mono hbl) fun o _ => ?_
    exact NoInt.bind (NoInt.keep (ihs (fun b hb => ih b (List.mem_cons_of_mem _ hb)) hsc hfs
      (fun b hb => hn b (List.mem_cons_of_mem _ hb)) hg hok.2)) fun _ _ => NoInt.pure trivial

theorem match_noInt (p : Pos) (m : Option Mult) {s : Expr} (ann : Tele) {bs : List Branch} (ihs : ExprNI s)
    (ihb : ∀ b ∈ bs, ExprNI b.body) : ExprNI (.match p m s ann bs) := by
  intro C sc g hsc hok hg
  unfold checkExpr
  dsimp only
  refine NoInt.bind ?_ fun o ho => finish_noInt ho
  have hg' := given_erased hg C.erased
  generalize (if C.erased = true then Option.map (fun x => x.erase) g else g) = g' at hg' ⊢
  generalize (C.erased || Option.any (fun x => x.allErased) g) = w
  simp only [Expr.shaped, Bool.and_eq_true] at hok
  obtain ⟨⟨hoks, hokt⟩, hokb⟩ := hok
  refine NoInt.bind (NoInt.imp (ihs _ sc none (hsc.ctx rfl) hoks (by simp))
    fun o h => h.ctx rfl) fun so hso => NoInt.keep ?_
  have hsc' : ScOk (C.enter w) so.sc := hso.ok.ctx rfl
  refine NoInt.bind NoInt.single fun r hr => ?_
  have hrw : r.term.wf so.sc.sigs so.sc.Γ.length 0 = true := by
    rw [hso.sigs]; exact hso.res r (by rw [hr]; exact List.mem_cons_self)
  refine NoInt.bind (annotation_noInt hsc' (fun g'' h => by rw [hso.sigs]; exact (hg' g'' h).mono hso.len)
    fun bs' he => ?_) fun ⟨tele, env⟩ ⟨t1, t2, t3⟩ => ?_
  · subst he
    simpa [Tele.shaped] using hokt
  refine NoInt.bind (forcings_noInt hsc' hrw) fun fs ⟨f1, f2⟩ => ?_
  refine NoInt.bind (NoInt.forM fun b hb => NoInt.bind (survivor_noInt f1 (f2 _ (List.mem_map_of_mem hb)))
    fun _ _ => freshAll_noInt) fun _ _ => ?_
  simp only at t1 t2 t3
  have hens : ((tele.all fun x => TBinder.entriesBelow so.sc.Γ.length x) &&
      env.all fun x => Term.entriesBelow so.sc.Γ.length x) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true]
    exact ⟨List.all_eq_true.1 (Telescope.entriesBelow_of_wf t3), fun u hu => Term.entriesBelow_of_wf (t2 u hu)⟩
  have hgiven : ∀ (ws : List Want), ws.length = tele.length → (∀ (j : Nat) (w : Want) (b : TBinder),
      ws[j]? = some w → tele[j]? = some b → w.type = some b.type ∧ w.is = b.is) →
      ∀ lab, GivenOk so.sc.sigs so.sc.Γ.length { wants := ws, env := env, whole := true, label := lab } := by
    intro ws hl hw lab
    refine ⟨fun _ => t2, fun _ => Wants.wf_of_tele t3 hl hw, fun _ => ⟨fun h => ?_, fun w hw' => ?_⟩⟩
    · simp only at h; rw [h] at hl; exact t1 (List.eq_nil_of_length_eq_zero hl.symm)
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hw'
      obtain ⟨b, hb⟩ : ∃ b, tele[j]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hj).1)⟩
      simp [(hw j w b hj hb).1]
  have hwants : ∀ f : Nat → TBinder → Mult, (∀ (j : Nat) (w : Want) (b : TBinder),
      (tele.mapIdx fun i b => ({ Want.of b with mult := f i b } : Want))[j]? = some w → tele[j]? = some b →
      w.type = some b.type ∧ w.is = b.is) := by
    intro f j w b hw hb
    simp only [List.getElem?_mapIdx, hb, Option.map_some, Option.some.injEq] at hw
    subst hw; exact ⟨rfl, rfl⟩
  have tail : ∀ (lab : Option (Nat → String)),
      NoInt (do
        ensure ((tele.all fun x => TBinder.entriesBelow so.sc.Γ.length x) &&
          env.all fun x => Term.entriesBelow so.sc.Γ.length x) p
          "an annotation mentions an entry created after the scrutinee"
        let bo ← checkBranches (C.enter w) so.sc r s.pos fs (⟨tele.mapIdx fun i b =>
          ({ Want.of b with mult := if g'.any (·.erasedAt i) then .erased else b.mult } : Want), env, true, none,
          lab⟩ : Given) bs
        let o ← keep bo.snaps (produced (opened so.sc tele env "match" p fun i =>
            r.tainted || bo.outs.any fun o => ((o.res[i]?).map (·.tainted)).getD false).1 g' p
          (opened so.sc tele env "match" p fun i =>
            r.tainted || bo.outs.any fun o => ((o.res[i]?).map (·.tainted)).getD false).2
          (.match p m so.tree ann ((bs.zip bo.trees).filterMap fun x =>
            if (m == some Mult.erased && x.1.body.absurd) = true then none else some x.2)))
        pure ({ o with snaps := so.snaps ++ bo.snaps } : Out)) (OutOk C sc) := by
    intro lab
    refine NoInt.bind (NoInt.ensure hens) fun _ _ => ?_
    refine NoInt.bind (branches_noInt ihb hsc' f1 (fun b hb => f2 _ (List.mem_map_of_mem hb))
      (hgiven _ (by simp) (hwants _) lab) hokb) fun bo _ => ?_
    obtain ⟨o1, o2, o3, o4, o5, o6⟩ := opened_ok (kind := "match") (pos := p) (taint := fun i =>
      r.tainted || bo.outs.any fun o => ((o.res[i]?).map (·.tainted)).getD false) hso.ok t3 t2
    refine NoInt.bind (NoInt.keep (produced_noInt (g := g') o1 (by rw [o2]; exact o6))) fun o ⟨e1, e2⟩ =>
      NoInt.pure ?_
    obtain ⟨osc, ores, otree, osn⟩ := o
    simp only at e1 e2; subst e1 e2
    exact OutOk.of (o1.ctx rfl) (o2.trans hso.sigs) (Nat.le_trans hso.len o4.length_le)
      (by rw [← hso.sigs, ← o2]; exact o6) (by
        intro h; rw [← List.length_eq_zero_iff, o5] at h; exact t1 (List.eq_nil_of_length_eq_zero h))
  split
  · split
    · split
      · exact NoInt.failAt_bind
      · exact tail _
    · exact tail _
  · exact NoInt.failAt_bind

theorem inspect_noInt (p : Pos) : StmtNI (.inspect p) := by
  intro C sc hsc _
  unfold checkStmt
  exact NoInt.pure ⟨hsc, rfl, Nat.le_refl _⟩

theorem let_noInt (p : Pos) {bs : List LetBinder} {rhs : Expr} (ih : ExprNI rhs) : StmtNI (.let p bs rhs) := by
  intro C sc hsc hok
  simp only [Stmt.shaped, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hok
  obtain ⟨hne, hokr⟩ := hok
  unfold checkStmt
  dsimp only
  refine NoInt.bind freshAll_noInt fun _ _ => ?_
  have fin : ∀ o : Out, OutOk C sc o → NoInt (pure (⟨o.sc.bind (bs.map (·.name)) ((bs.zip o.res).map
      fun x => ({ term := x.2.term, tainted := x.2.tainted, erased := x.1.mult == some Mult.erased } : Res)),
      .let p bs o.tree, o.snaps⟩ : StmtOut) : CheckM StmtOut)
      (fun o' => ScOk C o'.sc ∧ o'.sc.sigs = sc.sigs ∧ sc.Γ.length ≤ o'.sc.Γ.length) := by
    intro o ho
    refine NoInt.pure ⟨ho.ok.bind fun r hr => ?_, by rw [Scope.bind_eq]; exact ho.sigs, by
      rw [Scope.bind_eq]; exact ho.len⟩
    simp only [List.mem_map] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    rw [ho.sigs]; exact ho.res x.2 (List.of_mem_zip hx).2
  split
  · rename_i hr
    have hw : (anyGiven bs).whole = false := by
      simp only [anyGiven, letGiven, List.all_eq_false]
      simp only [holedLet, List.any_eq_true, Option.any_eq_true] at hr
      obtain ⟨b, hb, t, ht, hh⟩ := hr
      exact ⟨b, hb, by simp [ht, hh]⟩
    refine NoInt.bind (ih C sc _ hsc hokr fun g h => by cases h; exact GivenOk.of_not_whole hw) fun o ho => ?_
    refine NoInt.bind (NoInt.keep (letBinders_noInt ho.ok (by rw [ho.sigs]; exact ho.res))) fun _ _ => ?_
    simp only [pure, Except.pure, ok_bind]
    exact fin o ho
  · refine NoInt.bind (letWants_noInt hsc) fun ws ⟨w2, w3⟩ => ?_
    refine NoInt.bind (ih C sc _ hsc hokr fun g h => ?_) fun o ho => fin o ho
    cases h
    refine ⟨fun _ => by simp [letGiven], fun hw => ?_, fun hw => ?_⟩
    · have hall : bs.all (·.ann.isSome) = true := by
        simp only [letGiven, List.all_eq_true, Option.any_eq_true] at hw ⊢
        intro b hb; obtain ⟨a, ha, -⟩ := hw b hb; simp [ha]
      simpa [letGiven] using (w3 hall).1
    · have hall : bs.all (·.ann.isSome) = true := by
        simp only [letGiven, List.all_eq_true, Option.any_eq_true] at hw ⊢
        intro b hb; obtain ⟨a, ha, -⟩ := hw b hb; simp [ha]
      refine ⟨fun h => hne ?_, (w3 hall).2⟩
      simp only [letGiven] at h
      rw [h] at w2
      exact List.eq_nil_of_length_eq_zero w2.symm

theorem patlet_noInt (p : Pos) (ct : Bool) (m : Option Mult) (pat : Pattern) {rhs : Expr} (ih : ExprNI rhs) :
    StmtNI (.patlet p ct m pat rhs) := by
  intro C sc hsc hok
  simp only [Stmt.shaped, Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨hct, hokr⟩ := hok
  subst hct
  unfold checkStmt
  dsimp only
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine NoInt.bind (NoInt.ensure rfl) fun _ _ => ?_
  refine NoInt.bind freshAll_noInt fun _ _ => ?_
  refine NoInt.bind (NoInt.imp (ih _ sc none (hsc.ctx rfl) hokr (by simp))
    fun o h => h.ctx (C' := C) rfl) fun o ho => NoInt.keep ?_
  refine NoInt.bind NoInt.single fun r hr => ?_
  have hrw : r.term.wf o.sc.sigs o.sc.Γ.length 0 = true := by
    rw [ho.sigs]; exact ho.res r (by rw [hr]; exact List.mem_cons_self)
  refine NoInt.bind (forcings_noInt ho.ok hrw) fun fs ⟨f1, f2⟩ => ?_
  exact NoInt.bind (patBind_noInt ho.ok f1 (f2 pat List.mem_cons_self)) fun sc' ⟨s1, s2, s3⟩ =>
    NoInt.pure ⟨s1, s2.trans ho.sigs, Nat.le_trans ho.len s3⟩

mutual
/-- `checkExpr` reports no internal error on a well-formed expression. -/
theorem Expr.noInt : (e : Expr) → ExprNI e
  | .var x => var_noInt x
  | .app h args => app_noInt h fun a _ => Expr.noInt a.expr
  | .tuple p es => tuple_noInt p fun e _ => Expr.noInt e
  | .block ss f => block_noInt (fun s _ => Stmt.noInt s) (Expr.noInt f)
  | .match p m s ann bs => match_noInt p m ann (Expr.noInt s) fun b _ => Expr.noInt b.body
  | .sorry p t => sorry_noInt p t
  | .removed => removed_noInt
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | (have := Arg.sizeOf_expr_lt ‹_›; simp only [Expr.app.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem ‹_›; simp only [Expr.tuple.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem ‹_›; simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.block.sizeOf_spec]; omega)
    | (simp only [Expr.match.sizeOf_spec]; omega)
    | (have := Branch.sizeOf_body_lt' ‹_›; simp only [Expr.match.sizeOf_spec]; omega)
theorem Stmt.noInt : (s : Stmt) → StmtNI s
  | .let p bs rhs => let_noInt p (Expr.noInt rhs)
  | .patlet p ct m pat rhs => patlet_noInt p ct m pat (Expr.noInt rhs)
  | .inspect p => inspect_noInt p
termination_by s => sizeOf s
decreasing_by all_goals (simp only [Stmt.let.sizeOf_spec, Stmt.patlet.sizeOf_spec]; omega)
end

end Pledge
