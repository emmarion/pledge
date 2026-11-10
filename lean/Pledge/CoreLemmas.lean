import Pledge.Core

namespace Pledge

theorem getElem?_append_of_some {α} {l l' : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    (l ++ l')[i]? = some a := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1, h]

theorem Term.substList_eq_map (env : List Term) (as : List Term) : Term.substList env as = as.map (Term.subst env) := by
  induction as <;> simp_all [Term.substList]

theorem Term.replaceList_eq_map (x : Nat) (e : Term) (as : List Term) :
    Term.replaceList x e as = as.map (Term.replace x e) := by
  induction as <;> simp_all [Term.replaceList]

theorem Term.canonList_eq_map (Γ : Entries) (as : List Term) : Term.canonList Γ as = as.map (Term.canon Γ) := by
  induction as <;> simp_all [Term.canonList]

theorem Term.occursList_eq_any (x : Nat) (as : List Term) : Term.occursList x as = as.any (Term.occurs x) := by
  induction as <;> simp_all [Term.occursList]

theorem Term.evalList_cons (ρ env : List Value) (a : Term) (as : List Term) :
    Term.evalList ρ env (a :: as) = (a.eval ρ env).bind fun v => (Term.evalList ρ env as).map (v :: ·) := by
  simp only [Term.evalList]; cases a.eval ρ env <;> cases Term.evalList ρ env as <;> rfl

theorem Term.evalList_eq_mapM (ρ env : List Value) (as : List Term) :
    Term.evalList ρ env as = as.mapM (Term.eval ρ env) := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [List.mapM_cons, ← ih]; rfl

theorem Term.evalList_cons_eq_some {ρ env : List Value} {a : Term} {as : List Term} {vs : List Value} :
    Term.evalList ρ env (a :: as) = some vs ↔
      ∃ v vs', a.eval ρ env = some v ∧ Term.evalList ρ env as = some vs' ∧ vs = v :: vs' := by
  rw [Term.evalList_cons]
  cases a.eval ρ env <;> cases Term.evalList ρ env as <;> simp [eq_comm]

/-- The value of each argument, by position. -/
theorem Term.evalList_getElem? {ρ env : List Value} :
    ∀ {as : List Term} {vs : List Value} {i : Nat},
      Term.evalList ρ env as = some vs → vs[i]? = as[i]?.bind (Term.eval ρ env)
  | [], vs, i, h => by cases h; simp
  | a :: as, vs, i, h => by
    obtain ⟨v, vs', hv, hvs, rfl⟩ := Term.evalList_cons_eq_some.1 h
    cases i <;> simp [hv, Term.evalList_getElem? hvs]

theorem Term.length_evalList {ρ env : List Value} :
    ∀ {as : List Term} {vs : List Value}, Term.evalList ρ env as = some vs → vs.length = as.length
  | [], vs, h => by cases h; rfl
  | a :: as, vs, h => by
    obtain ⟨v, vs', _, hvs, rfl⟩ := Term.evalList_cons_eq_some.1 h
    simp [Term.length_evalList hvs]

theorem Term.evalList_eq_some_iff {ρ env : List Value} :
    ∀ {as : List Term} {vs : List Value}, Term.evalList ρ env as = some vs ↔
      vs.length = as.length ∧ ∀ (i : Nat) (a : Term), as[i]? = some a → a.eval ρ env = vs[i]?
  | [], vs => by cases vs <;> simp [Term.evalList]
  | a :: as, [] => by simp [Term.evalList_cons_eq_some]
  | a :: as, v :: vs => by
    rw [Term.evalList_cons_eq_some]
    constructor
    · rintro ⟨v', vs', hv, hvs, h⟩
      cases h
      refine ⟨by simp [Term.length_evalList hvs], fun i b hb => ?_⟩
      cases i with
      | zero => cases hb; simpa using hv
      | succ i => simpa using (Term.evalList_eq_some_iff.1 hvs).2 i b (by simpa using hb)
    · rintro ⟨hl, h⟩
      refine ⟨v, vs, by simpa using h 0 a rfl,
        Term.evalList_eq_some_iff.2 ⟨by simpa using hl, fun i b hb => ?_⟩, rfl⟩
      simpa using h (i + 1) b (by simpa using hb)

theorem Term.eval_app {ρ env : List Value} {h : Head} {as : List Term} {v : Value} :
    (Term.app h as).eval ρ env = some v ↔ ∃ vs, Term.evalList ρ env as = some vs ∧ v = .app h vs := by
  simp only [Term.eval, Option.map_eq_some_iff]
  constructor <;> rintro ⟨vs, h1, h2⟩ <;> exact ⟨vs, h1, h2.symm⟩

mutual
/-- Evaluation is unchanged by extending the valuation and the environment. -/
theorem Term.eval_frame {ρ env : List Value} (ρ' env' : List Value) :
    ∀ (t : Term) {v : Value}, t.eval ρ env = some v → t.eval (ρ ++ ρ') (env ++ env') = some v
  | .entry _, _, h => getElem?_append_of_some h
  | .bound _, _, h => getElem?_append_of_some h
  | .app _ as, _, h => by
    obtain ⟨vs, hvs, rfl⟩ := Term.eval_app.1 h
    exact Term.eval_app.2 ⟨vs, Term.evalList_frame ρ' env' as hvs, rfl⟩
theorem Term.evalList_frame {ρ env : List Value} (ρ' env' : List Value) :
    ∀ (as : List Term) {vs : List Value}, Term.evalList ρ env as = some vs →
      Term.evalList (ρ ++ ρ') (env ++ env') as = some vs
  | [], _, h => h
  | a :: as, _, h => by
    obtain ⟨v, vs, hv, hvs, rfl⟩ := Term.evalList_cons_eq_some.1 h
    exact Term.evalList_cons_eq_some.2
      ⟨v, vs, Term.eval_frame ρ' env' a hv, Term.evalList_frame ρ' env' as hvs, rfl⟩
end

theorem Term.eval_frame_env {ρ env : List Value} (env' : List Value) {t : Term} {v : Value}
    (h : t.eval ρ env = some v) : t.eval ρ (env ++ env') = some v := by
  simpa using Term.eval_frame [] env' t h

theorem Term.eval_frame_ρ {ρ env : List Value} (ρ' : List Value) {t : Term} {v : Value}
    (h : t.eval ρ env = some v) : t.eval (ρ ++ ρ') env = some v := by
  simpa using Term.eval_frame ρ' [] t h

mutual
/-- Substituting closed terms for the bound variables is evaluating under their values. -/
theorem Term.eval_subst {ρ : List Value} {env : List Term} {vs : List Value}
    (hvs : Term.evalList ρ [] env = some vs) : ∀ t : Term, (t.subst env).eval ρ [] = t.eval ρ vs
  | .entry _ => rfl
  | .bound i => by
    simp only [Term.subst, Term.eval, Term.evalList_getElem? hvs]
    cases env[i]? <;> simp [Term.eval]
  | .app h as => by simp only [Term.subst, Term.eval, Term.evalList_subst hvs as]
theorem Term.evalList_subst {ρ : List Value} {env : List Term} {vs : List Value}
    (hvs : Term.evalList ρ [] env = some vs) :
    ∀ as : List Term, Term.evalList ρ [] (Term.substList env as) = Term.evalList ρ vs as
  | [] => rfl
  | a :: as => by simp only [Term.substList, Term.evalList, Term.eval_subst hvs a, Term.evalList_subst hvs as]
end

mutual
/-- Replacing an entry by a term of the same value keeps the value. -/
theorem Term.eval_replace {ρ env : List Value} {x : Nat} {e : Term} (he : e.eval ρ env = ρ[x]?) :
    ∀ t : Term, (Term.replace x e t).eval ρ env = t.eval ρ env
  | .entry i => by
    simp only [Term.replace]
    split <;> simp_all [Term.eval]
  | .bound _ => rfl
  | .app h as => by simp only [Term.replace, Term.eval, Term.evalList_replace he as]
theorem Term.evalList_replace {ρ env : List Value} {x : Nat} {e : Term} (he : e.eval ρ env = ρ[x]?) :
    ∀ as : List Term, Term.evalList ρ env (Term.replaceList x e as) = Term.evalList ρ env as
  | [] => rfl
  | a :: as => by simp only [Term.replaceList, Term.evalList, Term.eval_replace he a, Term.evalList_replace he as]
end

/-- Every rule of `Γ` holds under `ρ`. -/
def RulesHold (Γ : Entries) (ρ : List Value) : Prop :=
  ∀ (i : Nat) (en : Entry) (r : Term), Γ[i]? = some en → en.rule = some r →
    ∃ v, ρ[i]? = some v ∧ r.eval ρ [] = some v

mutual
/-- Canonicalization is sound (SOUNDNESS.md Lemma 3.1). -/
theorem Term.eval_canon {Γ : Entries} {ρ : List Value} (hΓ : RulesHold Γ ρ) (env : List Value) :
    ∀ t : Term, (t.canon Γ).eval ρ env = t.eval ρ env
  | .entry i => by
    simp only [Term.canon]
    cases hi : Γ[i]? with
    | none => rfl
    | some en =>
      cases hr : en.rule with
      | none => simp [hr]
      | some r =>
        obtain ⟨v, hv, hr'⟩ := hΓ i en r hi hr
        simpa [Term.eval, hr, hv] using Term.eval_frame_env env hr'
  | .bound _ => rfl
  | .app h as => by simp only [Term.canon, Term.eval, Term.evalList_canon hΓ env as]
theorem Term.evalList_canon {Γ : Entries} {ρ : List Value} (hΓ : RulesHold Γ ρ) (env : List Value) :
    ∀ as : List Term, Term.evalList ρ env (Term.canonList Γ as) = Term.evalList ρ env as
  | [] => rfl
  | a :: as => by simp only [Term.canonList, Term.evalList, Term.eval_canon hΓ env a, Term.evalList_canon hΓ env as]
end

theorem identical.eval_eq {Γ : Entries} {ρ env : List Value} {a b : Term} (hΓ : RulesHold Γ ρ)
    (h : identical Γ a b = true) : a.eval ρ env = b.eval ρ env := by
  rw [← Term.eval_canon hΓ env a, ← Term.eval_canon hΓ env b, eq_of_beq h]

theorem HasType.app_iff {S : Sigs} {h : Head} {vs : List Value} {V : Value} :
    HasType S (.app h vs) V ↔
      ∃ sig, S.find h = some sig ∧ TeleSat S [] sig.params [] vs ∧ sig.ret.eval [] vs = some V :=
  ⟨fun | .app hs ht hr => ⟨_, hs, ht, hr⟩, fun ⟨_, hs, ht, hr⟩ => .app hs ht hr⟩

theorem HasType.not_removed {S : Sigs} {V : Value} : ¬ HasType S .removed V := nofun

/-- Unique types (SOUNDNESS.md Lemma 2.2). -/
theorem HasType.unique {S : Sigs} {v V V' : Value} : HasType S v V → HasType S v V' → V = V'
  | .app hs _ hr, .app hs' _ hr' => by
    rw [hs] at hs'; cases hs'; rw [hr] at hr'; cases hr'; rfl

/-- `S'` has every signature `S` has. -/
def Sigs.Sub (S S' : Sigs) : Prop := ∀ h sig, S.find h = some sig → S'.find h = some sig

theorem Sigs.Sub.refl (S : Sigs) : S.Sub S := fun _ _ h => h

mutual
theorem HasType.mono_sigs {S S' : Sigs} (hS : S.Sub S') {v V : Value} : HasType S v V → HasType S' v V
  | .app hs ht hr => .app (hS _ _ hs) (TeleSat.mono_sigs hS ht) hr
theorem TeleSat.mono_sigs {S S' : Sigs} (hS : S.Sub S') {ρ : List Value} {Δ : Telescope} {env vs : List Value} :
    TeleSat S ρ Δ env vs → TeleSat S' ρ Δ env vs
  | .nil => .nil
  | .cons hA hv his ht => .cons hA (HasType.mono_sigs hS hv) his (TeleSat.mono_sigs hS ht)
end

mutual
theorem HasType.noRemoved {S : Sigs} {v V : Value} : HasType S v V → v.noRemoved = true
  | .app _ ht _ => by simp only [Value.noRemoved]; exact TeleSat.noRemoved ht
theorem TeleSat.noRemoved {S : Sigs} {ρ : List Value} {Δ : Telescope} {env vs : List Value} :
    TeleSat S ρ Δ env vs → Value.noRemovedList vs = true
  | .nil => rfl
  | .cons _ hv _ ht => by simp only [Value.noRemovedList, HasType.noRemoved hv, TeleSat.noRemoved ht, Bool.and_self]
end

/-- The value `v` satisfies the binder `b` when `env` holds the values of the earlier bound variables. -/
def BinderSat (S : Sigs) (ρ : List Value) (b : TBinder) (env : List Value) (v : Value) : Prop :=
  ∃ A, b.type.eval ρ env = some A ∧ HasType S v A ∧ ∀ e, b.is = some e → e.eval ρ env = some v

theorem TeleSat.nil_iff {S : Sigs} {ρ env vs : List Value} : TeleSat S ρ [] env vs ↔ vs = [] :=
  ⟨fun | .nil => rfl, fun h => h ▸ .nil⟩

theorem TeleSat.cons_iff {S : Sigs} {ρ : List Value} {b : TBinder} {Δ : Telescope} {env vs : List Value} :
    TeleSat S ρ (b :: Δ) env vs ↔
      ∃ v vs', vs = v :: vs' ∧ BinderSat S ρ b env v ∧ TeleSat S ρ Δ (env ++ [v]) vs' :=
  ⟨fun | .cons hA hv his ht => ⟨_, _, rfl, ⟨_, hA, hv, his⟩, ht⟩,
   fun ⟨_, _, h, ⟨_, hA, hv, his⟩, ht⟩ => h ▸ .cons hA hv his ht⟩

theorem TeleSat.length_eq {S : Sigs} {ρ : List Value} :
    ∀ {Δ : Telescope} {env vs : List Value}, TeleSat S ρ Δ env vs → vs.length = Δ.length
  | [], _, _, h => by rw [TeleSat.nil_iff.1 h]; rfl
  | _ :: _, _, _, h => by
    obtain ⟨_, _, rfl, _, ht⟩ := TeleSat.cons_iff.1 h
    simp [TeleSat.length_eq ht]

/-- Satisfaction of a telescope carries over between binder lists that agree binder by binder. -/
theorem TeleSat.congr {S : Sigs} {ρ ρ' : List Value} :
    ∀ {Δ Δ' : Telescope} {env vs : List Value}, Telescope.Agree ρ ρ' Δ Δ' →
      (TeleSat S ρ Δ env vs ↔ TeleSat S ρ' Δ' env vs)
  | [], [], _, _, _ => by simp [TeleSat.nil_iff]
  | b :: Δ, b' :: Δ', env, vs, ⟨hb, hΔ⟩ => by
    simp only [TeleSat.cons_iff, BinderSat]
    refine exists_congr fun v => exists_congr fun vs' => and_congr_right fun _ =>
      and_congr (exists_congr fun A => ?_) (TeleSat.congr hΔ)
    rw [hb.type env]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    have hi := hb.is env
    cases h₁ : b.is <;> cases h₂ : b'.is <;> simp_all
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => h.elim

theorem TeleSat.frame {S : Sigs} {ρ : List Value} (ρ' : List Value) :
    ∀ {Δ : Telescope} {env vs : List Value}, TeleSat S ρ Δ env vs → TeleSat S (ρ ++ ρ') Δ env vs
  | [], _, _, h => by rw [TeleSat.nil_iff.1 h]; exact .nil
  | _ :: _, _, _, h => by
    obtain ⟨_, _, rfl, ⟨_, hA, hv, his⟩, ht⟩ := TeleSat.cons_iff.1 h
    exact .cons (Term.eval_frame_ρ ρ' hA) hv (fun e he => Term.eval_frame_ρ ρ' (his e he)) (TeleSat.frame ρ' ht)

/-- A telescope is satisfied binder by binder, the `i`-th under the values before it. -/
theorem TeleSat.iff_getElem? {S : Sigs} {ρ : List Value} :
    ∀ {Δ : Telescope} {env vs : List Value}, TeleSat S ρ Δ env vs ↔
      vs.length = Δ.length ∧ ∀ (i : Nat) (b : TBinder) (v : Value), Δ[i]? = some b → vs[i]? = some v →
        BinderSat S ρ b (env ++ vs.take i) v
  | [], env, vs => by cases vs <;> simp [TeleSat.nil_iff]
  | b :: Δ, env, [] => by simp [TeleSat.cons_iff]
  | b :: Δ, env, v :: vs => by
    rw [TeleSat.cons_iff]
    constructor
    · rintro ⟨_, _, h, hb, ht⟩
      cases h
      refine ⟨by simp [ht.length_eq], fun i b' v' hb' hv' => ?_⟩
      cases i with
      | zero => cases hb'; cases hv'; simpa using hb
      | succ i => simpa using (TeleSat.iff_getElem?.1 ht).2 i b' v' (by simpa using hb') (by simpa using hv')
    · rintro ⟨hl, h⟩
      refine ⟨v, vs, rfl, by simpa using h 0 b v rfl rfl, TeleSat.iff_getElem?.2 ⟨by simpa using hl, ?_⟩⟩
      intro i b' v' hb' hv'
      simpa using h (i + 1) b' v' (by simpa using hb') (by simpa using hv')

theorem TeleSat.append_iff {S : Sigs} {ρ : List Value} :
    ∀ {Δ₁ Δ₂ : Telescope} {env vs₁ vs₂ : List Value}, vs₁.length = Δ₁.length →
      (TeleSat S ρ (Δ₁ ++ Δ₂) env (vs₁ ++ vs₂) ↔
        TeleSat S ρ Δ₁ env vs₁ ∧ TeleSat S ρ Δ₂ (env ++ vs₁) vs₂)
  | [], _, _, vs₁, _, hl => by cases vs₁ <;> simp_all [TeleSat.nil_iff]
  | _ :: _, _, _, [], _, hl => by simp at hl
  | b :: Δ₁, Δ₂, env, v :: vs₁, vs₂, hl => by
    simp only [List.cons_append, TeleSat.cons_iff, List.cons.injEq]
    have ih := @TeleSat.append_iff S ρ Δ₁ Δ₂ (env ++ [v]) vs₁ vs₂ (by simpa using hl)
    simp only [List.append_assoc, List.singleton_append] at ih
    constructor
    · rintro ⟨_, _, ⟨rfl, rfl⟩, hb, ht⟩
      exact ⟨⟨_, _, ⟨rfl, rfl⟩, hb, (ih.1 ht).1⟩, (ih.1 ht).2⟩
    · rintro ⟨⟨_, _, ⟨rfl, rfl⟩, hb, ht⟩, ht'⟩
      exact ⟨_, _, ⟨rfl, rfl⟩, hb, ih.2 ⟨ht, ht'⟩⟩

theorem HasType.inv {S : Sigs} {v V : Value} (h : HasType S v V) :
    ∃ hd ws sig, v = .app hd ws ∧ S.find hd = some sig ∧ TeleSat S [] sig.params [] ws ∧
      sig.ret.eval [] ws = some V :=
  match h with
  | .app hs ht hr => ⟨_, _, _, rfl, hs, ht, hr⟩

/-- A value whose type applies a type constructor is built by a signature whose return evaluates
to that type (cf. SOUNDNESS.md Lemma 2.1). -/
theorem HasType.inv_type {S : Sigs} {v : Value} {T : String} {us : List Value}
    (h : HasType S v (.app ⟨.type, T⟩ us)) :
    ∃ hd ws sig, v = .app hd ws ∧ S.find hd = some sig ∧ sig.ret.eval [] ws = some (.app ⟨.type, T⟩ us) :=
  let ⟨hd, ws, sig, hv, hs, _, hr⟩ := h.inv
  ⟨hd, ws, sig, hv, hs, hr⟩

theorem TBinder.Agree.refl (ρ : List Value) (b : TBinder) : TBinder.Agree ρ ρ b b :=
  ⟨fun _ => rfl, fun _ => rfl, rfl⟩

theorem TBinder.Agree.trans {ρ₁ ρ₂ ρ₃ : List Value} {b₁ b₂ b₃ : TBinder} (h : TBinder.Agree ρ₁ ρ₂ b₁ b₂)
    (h' : TBinder.Agree ρ₂ ρ₃ b₂ b₃) : TBinder.Agree ρ₁ ρ₃ b₁ b₃ :=
  ⟨fun env => (h.type env).trans (h'.type env), fun env => (h.is env).trans (h'.is env), h.mult.trans h'.mult⟩

theorem Telescope.Agree.trans {ρ₁ ρ₂ ρ₃ : List Value} :
    ∀ {Δ₁ Δ₂ Δ₃ : Telescope}, Telescope.Agree ρ₁ ρ₂ Δ₁ Δ₂ → Telescope.Agree ρ₂ ρ₃ Δ₂ Δ₃ →
      Telescope.Agree ρ₁ ρ₃ Δ₁ Δ₃
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨hb, hΔ⟩, ⟨hb', hΔ'⟩ => ⟨hb.trans hb', Telescope.Agree.trans hΔ hΔ'⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ | _, [], _ :: _, _, h | _, _ :: _, [], _, h => h.elim

theorem Sig.Agree.trans {ρ₁ ρ₂ ρ₃ : List Value} {s₁ s₂ s₃ : Sig} (h : Sig.Agree ρ₁ ρ₂ s₁ s₂)
    (h' : Sig.Agree ρ₂ ρ₃ s₂ s₃) : Sig.Agree ρ₁ ρ₃ s₁ s₃ :=
  ⟨h.params.trans h'.params, fun env => (h.ret env).trans (h'.ret env)⟩

mutual
theorem Term.eval_entriesBelow {n : Nat} {ρ ρ' : List Value} (hρ : ρ.take n = ρ'.take n) (env : List Value) :
    ∀ t : Term, t.entriesBelow n = true → t.eval ρ env = t.eval ρ' env
  | .entry i, h => by
    simp only [Term.entriesBelow, decide_eq_true_eq] at h
    have := congrArg (·[i]?) hρ
    simpa [List.getElem?_take, h, Term.eval] using this
  | .bound _, _ => rfl
  | .app _ as, h => by simp only [Term.eval, Term.evalList_entriesBelow hρ env as h]
theorem Term.evalList_entriesBelow {n : Nat} {ρ ρ' : List Value} (hρ : ρ.take n = ρ'.take n) (env : List Value) :
    ∀ as : List Term, Term.entriesBelowList n as = true → Term.evalList ρ env as = Term.evalList ρ' env as
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.entriesBelowList, Bool.and_eq_true] at h
    simp only [Term.evalList, Term.eval_entriesBelow hρ env a h.1, Term.evalList_entriesBelow hρ env as h.2]
end

theorem TBinder.agree_of_entriesBelow {n : Nat} {ρ ρ' : List Value} (hρ : ρ.take n = ρ'.take n) {b : TBinder}
    (h : b.entriesBelow n = true) : TBinder.Agree ρ ρ' b b := by
  simp only [TBinder.entriesBelow, Bool.and_eq_true] at h
  refine ⟨fun env => Term.eval_entriesBelow hρ env _ h.1, fun env => ?_, rfl⟩
  cases hb : b.is with
  | none => rfl
  | some e => simp_all [Term.eval_entriesBelow hρ env e]

theorem Telescope.agree_of_entriesBelow {n : Nat} {ρ ρ' : List Value} (hρ : ρ.take n = ρ'.take n) :
    ∀ {Δ : Telescope}, Δ.all (·.entriesBelow n) = true → Telescope.Agree ρ ρ' Δ Δ
  | [], _ => trivial
  | _ :: _, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact ⟨TBinder.agree_of_entriesBelow hρ h.1, Telescope.agree_of_entriesBelow hρ h.2⟩

theorem Sig.agree_of_entriesBelow {n : Nat} {ρ ρ' : List Value} (hρ : ρ.take n = ρ'.take n) {sig : Sig}
    (h : sig.entriesBelow n = true) : Sig.Agree ρ ρ' sig sig := by
  simp only [Sig.entriesBelow, Bool.and_eq_true] at h
  exact ⟨Telescope.agree_of_entriesBelow hρ h.1, fun env => Term.eval_entriesBelow hρ env _ h.2⟩

/-- A telescope whose entries are below `n` is satisfied alike under valuations that agree below `n`. -/
theorem TeleSat.iff_of_entriesBelow {S : Sigs} {n : Nat} {ρ ρ' : List Value} (hρ : ρ.take n = ρ'.take n)
    {Δ : Telescope} {env vs : List Value} (h : Δ.all (·.entriesBelow n) = true) :
    TeleSat S ρ Δ env vs ↔ TeleSat S ρ' Δ env vs :=
  TeleSat.congr (Telescope.agree_of_entriesBelow hρ h)

mutual
theorem Value.eval_toTerm {ρ env : List Value} : ∀ v : Value, v.noRemoved = true → v.toTerm.eval ρ env = some v
  | .app _ vs, h => by simp only [Value.toTerm, Term.eval, Value.evalList_toTermList vs h]; rfl
  | .removed, h => by simp [Value.noRemoved] at h
theorem Value.evalList_toTermList {ρ env : List Value} :
    ∀ vs : List Value, Value.noRemovedList vs = true → Term.evalList ρ env (Value.toTermList vs) = some vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [Value.noRemovedList, Bool.and_eq_true] at h
    simp only [Value.toTermList, Term.evalList, Value.eval_toTerm v h.1, Value.evalList_toTermList vs h.2]; rfl
end

mutual
/-- Closing a term under `ρ` keeps its value, when no value in `ρ` has a `removed` subtree. -/
theorem Term.eval_close {ρ : List Value} (hρ : ∀ v ∈ ρ, v.noRemoved = true) (env : List Value) :
    ∀ t : Term, (t.close ρ).eval [] env = t.eval ρ env
  | .entry i => by
    cases h : ρ[i]? with
    | none => simp [Term.close, Term.eval, h]
    | some v => simp [Term.close, h, Value.eval_toTerm v (hρ v (List.mem_of_getElem? h)), Term.eval]
  | .bound _ => rfl
  | .app _ as => by simp only [Term.close, Term.eval, Term.evalList_close hρ env as]
theorem Term.evalList_close {ρ : List Value} (hρ : ∀ v ∈ ρ, v.noRemoved = true) (env : List Value) :
    ∀ as : List Term, Term.evalList [] env (Term.closeList ρ as) = Term.evalList ρ env as
  | [] => rfl
  | a :: as => by simp only [Term.closeList, Term.evalList, Term.eval_close hρ env a, Term.evalList_close hρ env as]
end

theorem Sig.agree_close {ρ : List Value} (hρ : ∀ v ∈ ρ, v.noRemoved = true) (sig : Sig) :
    Sig.Agree ρ [] sig (sig.close ρ) := by
  refine ⟨?_, fun env => (Term.eval_close hρ env sig.ret).symm⟩
  simp only [Sig.close]
  induction sig.params with
  | nil => trivial
  | cons b Δ ih =>
    refine ⟨⟨fun env => (Term.eval_close hρ env b.type).symm, fun env => ?_, rfl⟩, ih⟩
    cases h : b.is <;> simp [TBinder.close, h, Term.eval_close hρ env]

theorem Sigs.find_map_close (S : Sigs) (ρ : List Value) (h : Head) :
    Sigs.find (S.map (Sig.close ρ)) h = (S.find h).map (Sig.close ρ) := by
  simp only [Sigs.find, List.find?_map]
  rfl

theorem Sigs.find_head {S : Sigs} {h : Head} {sig : Sig} (hs : S.find h = some sig) : sig.head = h := by
  simpa using List.find?_some hs

/-- Closing every signature under `ρ` gives closed signatures that `SigsClose` relates to them. -/
theorem SigsClose.close {S : Sigs} {ρ : List Value} (hρ : ∀ v ∈ ρ, v.noRemoved = true) :
    SigsClose S ρ (S.map (Sig.close ρ)) := fun h sig hs =>
  ⟨sig.close ρ, by rw [Sigs.find_map_close, hs]; rfl, Sig.agree_close hρ sig⟩

theorem SigsClose.find {S Sc : Sigs} {ρ : List Value} (hS : SigsClose S ρ Sc) {h : Head} {sig : Sig}
    (hs : S.find h = some sig) : ∃ sig', Sc.find h = some sig' ∧ Sig.Agree ρ [] sig sig' := hS h sig hs

theorem SigsClose.agree {S Sc : Sigs} {ρ : List Value} (hS : SigsClose S ρ Sc) {h : Head} {sig sig' : Sig}
    (hs : S.find h = some sig) (hc : Sc.find h = some sig') : Sig.Agree ρ [] sig sig' := by
  obtain ⟨_, hc', ha⟩ := hS.find hs
  exact Option.some.inj (hc'.symm.trans hc) ▸ ha

/-- Along the bridge, a closed signature's telescope is satisfied exactly when the original one is under `ρ`. -/
theorem SigsClose.teleSat_iff {S Sc : Sigs} {ρ : List Value} (hS : SigsClose S ρ Sc) {h : Head} {sig sig' : Sig}
    (hs : S.find h = some sig) (hc : Sc.find h = some sig') {env vs : List Value} :
    TeleSat Sc [] sig'.params env vs ↔ TeleSat Sc ρ sig.params env vs :=
  (TeleSat.congr (hS.agree hs hc).params).symm

theorem SigsClose.ret_eval {S Sc : Sigs} {ρ : List Value} (hS : SigsClose S ρ Sc) {h : Head} {sig sig' : Sig}
    (hs : S.find h = some sig) (hc : Sc.find h = some sig') (env : List Value) :
    sig'.ret.eval [] env = sig.ret.eval ρ env :=
  ((hS.agree hs hc).ret env).symm

/-- Typing an application of a head the checker has a signature for, by closed signatures, read through the
bridge as the checker's signature under `ρ`. -/
theorem SigsClose.hasType_app_iff {S Sc : Sigs} {ρ : List Value} (hS : SigsClose S ρ Sc) {h : Head} {sig : Sig}
    (hs : S.find h = some sig) {vs : List Value} {V : Value} :
    HasType Sc (.app h vs) V ↔ TeleSat Sc ρ sig.params [] vs ∧ sig.ret.eval ρ vs = some V := by
  obtain ⟨sig', hc, -⟩ := hS.find hs
  rw [HasType.app_iff]
  constructor
  · rintro ⟨sig'', hc', ht, hr⟩
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    exact ⟨(hS.teleSat_iff hs hc).1 ht, by rw [← hS.ret_eval hs hc]; exact hr⟩
  · rintro ⟨ht, hr⟩
    exact ⟨sig', hc, (hS.teleSat_iff hs hc).2 ht, by rw [hS.ret_eval hs hc]; exact hr⟩

/-- The bridge carries over between valuations that agree on the entries the signatures mention. -/
theorem SigsClose.of_entriesBelow {S Sc : Sigs} {n : Nat} {ρ ρ' : List Value} (hρ : ρ.take n = ρ'.take n)
    (hn : ∀ sig ∈ S, sig.entriesBelow n = true) (hS : SigsClose S ρ Sc) : SigsClose S ρ' Sc := fun h sig hs => by
  obtain ⟨sig', hc, ha⟩ := hS h sig hs
  exact ⟨sig', hc, (Sig.agree_of_entriesBelow hρ.symm (hn sig (List.mem_of_find?_eq_some hs))).trans ha⟩

theorem SigsClose.frame {S Sc : Sigs} {ρ : List Value} (ρ' : List Value)
    (hn : ∀ sig ∈ S, sig.entriesBelow ρ.length = true) (hS : SigsClose S ρ Sc) : SigsClose S (ρ ++ ρ') Sc :=
  hS.of_entriesBelow (by simp) hn

/-- The bridge carries over to more closed signatures. -/
theorem SigsClose.mono {S Sc Sc' : Sigs} {ρ : List Value} (hS : SigsClose S ρ Sc) (hSc : Sc.Sub Sc') :
    SigsClose S ρ Sc' := fun h sig hs =>
  let ⟨sig', hc, ha⟩ := hS h sig hs
  ⟨sig', hSc _ _ hc, ha⟩

/-- The bridge extends by a signature and a closed signature for the same head that agrees with it, when `Sc` has
no signature for that head. -/
theorem SigsClose.push {S Sc : Sigs} {ρ : List Value} {sig sig' : Sig} (hS : SigsClose S ρ Sc)
    (hh : sig'.head = sig.head) (hn : Sc.find sig.head = none) (ha : Sig.Agree ρ [] sig sig') :
    SigsClose (S ++ [sig]) ρ (Sc ++ [sig']) := fun h s hs => by
  simp only [Sigs.find, List.find?_append] at hs ⊢
  cases hs₀ : List.find? (fun s => s.head == h) S with
  | some s₀ =>
    rw [hs₀] at hs
    obtain ⟨s', hc, ha'⟩ := hS h s₀ hs₀
    simp only [Sigs.find] at hc
    refine ⟨s', by rw [hc]; rfl, ?_⟩
    cases hs; exact ha'
  | none =>
    rw [hs₀] at hs
    simp only [Option.none_or, List.find?_cons, List.find?_nil] at hs
    split at hs
    · rename_i hsh
      cases hs
      have hsh : sig.head = h := by simpa using hsh
      subst hsh
      have hn' : List.find? (fun s => s.head == sig.head) Sc = none := hn
      simp [hn', hh, ha]
    · cases hs

/-- No value has a type that no closed signature's return gives (cf. SOUNDNESS.md Corollary 2.3). -/
theorem HasType.empty {Sc : Sigs} {V : Value}
    (hV : ∀ h sig' ws, Sc.find h = some sig' → sig'.ret.eval [] ws ≠ some V) {v : Value} : ¬ HasType Sc v V :=
  fun h => by
    obtain ⟨_, ws, _, -, hc, -, hr⟩ := h.inv
    exact hV _ _ ws hc hr

theorem WType.unique {S : Sigs} {v A B : Value} (ha : WType S v A) (hb : WType S v B) : A = B := by
  cases v with
  | removed => exact ha.elim
  | app h vs =>
    simp only [WType] at ha hb
    split at ha
    · rename_i hh
      simp only [hh, ↓reduceIte] at hb
      rw [ha] at hb; exact (List.cons.inj hb).1
    · rename_i hh
      simp only [hh, ↓reduceIte] at hb
      obtain ⟨s, hs, hr⟩ := ha
      obtain ⟨s', hs', hr'⟩ := hb
      rw [hs] at hs'; cases hs'; rw [hr] at hr'; exact Option.some.inj hr'

theorem WType.junk (S : Sigs) (A : Value) : WType S (.junk A) A := by simp [WType, Value.junk]

theorem WType.mono_sigs {S S' : Sigs} (hS : S.Sub S') {v A : Value} (h : WType S v A) : WType S' v A := by
  cases v with
  | removed => exact h.elim
  | app hd vs =>
    simp only [WType] at h ⊢
    split at h
    · rename_i hn; simp only [hn, ↓reduceIte]; exact h
    · rename_i hn
      obtain ⟨s, hs, hr⟩ := h
      simp only [hn, ↓reduceIte]
      exact ⟨s, hS _ _ hs, hr⟩

/-- A typed value has its type by its head, when no signature has `junkHead`. -/
theorem HasType.wtype {S : Sigs} (hJ : S.find junkHead = none) {v A : Value} (h : HasType S v A) : WType S v A := by
  obtain ⟨hd, ws, sig, rfl, hs, -, hr⟩ := h.inv
  have : hd ≠ junkHead := fun e => by rw [e, hJ] at hs; cases hs
  simp only [WType, this, ↓reduceIte]
  exact ⟨sig, hs, hr⟩

theorem HasType.not_junk {S : Sigs} (hJ : S.find junkHead = none) {A B : Value} : ¬ HasType S (.junk A) B :=
  fun h => by obtain ⟨_, _, _, he, hs, -⟩ := h.inv; cases he; rw [hJ] at hs; cases hs

theorem Value.noRemoved_junk {A : Value} : (Value.junk A).noRemoved = A.noRemoved := by
  simp [Value.junk, Value.noRemoved, Value.noRemovedList]

theorem WSat.rulesHold {S : Sigs} {Γ : Entries} {ρ : List Value} (h : WSat S Γ ρ) : RulesHold Γ ρ :=
  fun i en r hen hr =>
    let ⟨v, _, hv, _, _, _, hrv⟩ := h.2 i en hen
    ⟨v, hv, hrv r hr⟩

theorem Sat.rulesHold {S : Sigs} {Γ : Entries} {ρ : List Value} (h : Sat S Γ ρ) : RulesHold Γ ρ := h.1.rulesHold

theorem WSat.eval_canon {S : Sigs} {Γ : Entries} {ρ : List Value} (h : WSat S Γ ρ) (env : List Value) (t : Term) :
    (t.canon Γ).eval ρ env = t.eval ρ env := Term.eval_canon h.rulesHold env t

theorem Sat.eval_canon {S : Sigs} {Γ : Entries} {ρ : List Value} (h : Sat S Γ ρ) (env : List Value) (t : Term) :
    (t.canon Γ).eval ρ env = t.eval ρ env := Term.eval_canon h.rulesHold env t

theorem WSat.eval_eq_of_identical {S : Sigs} {Γ : Entries} {ρ env : List Value} {a b : Term} (h : WSat S Γ ρ)
    (hab : identical Γ a b = true) : a.eval ρ env = b.eval ρ env := identical.eval_eq h.rulesHold hab

theorem Sat.eval_eq_of_identical {S : Sigs} {Γ : Entries} {ρ env : List Value} {a b : Term} (h : Sat S Γ ρ)
    (hab : identical Γ a b = true) : a.eval ρ env = b.eval ρ env := identical.eval_eq h.rulesHold hab

/-- A satisfying valuation has no `removed` subtree, so closing under it keeps values. -/
theorem WSat.noRemoved {S : Sigs} {Γ : Entries} {ρ : List Value} (h : WSat S Γ ρ) : ∀ v ∈ ρ, v.noRemoved = true :=
  fun v hv => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    obtain ⟨en, hen⟩ : ∃ en, Γ[i]? = some en := ⟨Γ[i]'(h.1 ▸ hi), by simp⟩
    obtain ⟨w, _, hw, _, hwr, -⟩ := h.2 i en hen
    rw [List.getElem?_eq_getElem hi] at hw
    exact Option.some.inj hw ▸ hwr

theorem Sat.noRemoved {S : Sigs} {Γ : Entries} {ρ : List Value} (h : Sat S Γ ρ) : ∀ v ∈ ρ, v.noRemoved = true :=
  h.1.noRemoved

theorem WSat.mono_sigs {S S' : Sigs} {Γ : Entries} {ρ : List Value} (hS : S.Sub S') (h : WSat S Γ ρ) :
    WSat S' Γ ρ :=
  ⟨h.1, fun i en hen =>
    let ⟨v, A, hv, hA, hr, hw, hru⟩ := h.2 i en hen
    ⟨v, A, hv, hA, hr, hw.mono_sigs hS, hru⟩⟩

theorem Sat.mono_sigs {S S' : Sigs} {Γ : Entries} {ρ : List Value} (hS : S.Sub S') (h : Sat S Γ ρ) :
    Sat S' Γ ρ :=
  ⟨h.1.mono_sigs hS, fun i en v A hen hv hA ht => (h.2 i en v A hen hv hA ht).mono_sigs hS⟩

/-- What `Sat` asks of one entry and its value. -/
def EntryOk (S : Sigs) (ρ : List Value) (en : Entry) (v : Value) : Prop :=
  ∃ A, en.type.eval ρ [] = some A ∧ v.noRemoved = true ∧ WType S v A ∧ (en.tainted = false → HasType S v A) ∧
    ∀ r : Term, en.rule = some r → r.eval ρ [] = some v

theorem Sat.entryOk {S : Sigs} {Γ : Entries} {ρ : List Value} (h : Sat S Γ ρ) {i : Nat} {en : Entry}
    (hen : Γ[i]? = some en) : ∃ v, ρ[i]? = some v ∧ EntryOk S ρ en v := by
  obtain ⟨v, A, hv, hA, hr, hw, hru⟩ := h.1.2 i en hen
  exact ⟨v, hv, A, hA, hr, hw, fun ht => h.2 i en v A hen hv hA ht, hru⟩

theorem EntryOk.frame {S : Sigs} {ρ : List Value} {en : Entry} {v : Value} (ρ' : List Value) (h : EntryOk S ρ en v) :
    EntryOk S (ρ ++ ρ') en v :=
  let ⟨A, hA, hr, hw, ht, hru⟩ := h
  ⟨A, Term.eval_frame_ρ ρ' hA, hr, hw, ht, fun r h => Term.eval_frame_ρ ρ' (hru r h)⟩

/-- `Sat`, entry by entry. -/
theorem Sat.iff {S : Sigs} {Γ : Entries} {ρ : List Value} :
    Sat S Γ ρ ↔ ρ.length = Γ.length ∧
      ∀ (i : Nat) (en : Entry), Γ[i]? = some en → ∃ v, ρ[i]? = some v ∧ EntryOk S ρ en v := by
  refine ⟨fun h => ⟨h.1.1, fun i en hen => h.entryOk hen⟩, fun ⟨hl, h⟩ => ⟨⟨hl, fun i en hen => ?_⟩, ?_⟩⟩
  · obtain ⟨v, hv, A, hA, hr, hw, -, hru⟩ := h i en hen
    exact ⟨v, A, hv, hA, hr, hw, hru⟩
  · intro i en v A hen hv hA ht
    obtain ⟨v', hv', A', hA', -, -, hty, -⟩ := h i en hen
    rw [hv] at hv'; cases hv'; rw [hA] at hA'; cases hA'
    exact hty ht

/-- Extending a scope by entries whose values satisfy them, under the extended valuation. -/
theorem Sat.append {S : Sigs} {Γ Δ : Entries} {ρ vs : List Value} (hΓ : Sat S Γ ρ) (hl : vs.length = Δ.length)
    (hΔ : ∀ (i : Nat) (en : Entry), Δ[i]? = some en → ∃ v, vs[i]? = some v ∧ EntryOk S (ρ ++ vs) en v) :
    Sat S (Γ ++ Δ) (ρ ++ vs) := by
  refine Sat.iff.2 ⟨by simp [hΓ.1.1, hl], fun i en hen => ?_⟩
  by_cases hi : i < Γ.length
  · rw [List.getElem?_append_left hi] at hen
    obtain ⟨v, hv, hok⟩ := hΓ.entryOk hen
    exact ⟨v, getElem?_append_of_some hv, hok.frame vs⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hen
    obtain ⟨v, hv, rest⟩ := hΔ _ en hen
    refine ⟨v, ?_, rest⟩
    rw [List.getElem?_append_right (by rw [hΓ.1.1]; omega), hΓ.1.1]
    exact hv

theorem Sat.push {S : Sigs} {Γ : Entries} {ρ : List Value} {en : Entry} {v : Value} (hΓ : Sat S Γ ρ)
    (h : EntryOk S (ρ ++ [v]) en v) : Sat S (Γ ++ [en]) (ρ ++ [v]) :=
  hΓ.append rfl fun i en' hen => by
    cases i with
    | zero => cases hen; exact ⟨v, rfl, h⟩
    | succ => simp at hen

theorem addRule_length (Γ : Entries) (x : Nat) (e : Term) : (addRule Γ x e).length = Γ.length :=
  List.length_mapIdx

theorem addRule_getElem? (Γ : Entries) (x : Nat) (e : Term) (i : Nat) :
    (addRule Γ x e)[i]? = Γ[i]?.map fun en =>
      if i = x then { en with rule := some e } else { en with rule := en.rule.map (Term.replace x e) } :=
  List.getElem?_mapIdx

/-- Adding a rule that holds keeps the scope satisfied. -/
theorem WSat.addRule {S : Sigs} {Γ : Entries} {ρ : List Value} {x : Nat} {e : Term} {v : Value}
    (hΓ : WSat S Γ ρ) (hx : ρ[x]? = some v) (he : e.eval ρ [] = some v) : WSat S (addRule Γ x e) ρ := by
  refine ⟨by rw [addRule_length]; exact hΓ.1, fun i en hen => ?_⟩
  rw [addRule_getElem?, Option.map_eq_some_iff] at hen
  obtain ⟨en₀, hen₀, rfl⟩ := hen
  obtain ⟨w, A, hw, hA, hwr, hwA, hr⟩ := hΓ.2 i en₀ hen₀
  by_cases hix : i = x
  · subst hix
    rw [hx] at hw; cases hw
    exact ⟨v, A, hx, by simpa using hA, hwr, hwA, by simpa using he⟩
  · refine ⟨w, A, hw, by simpa [hix] using hA, hwr, hwA, fun r hr' => ?_⟩
    simp only [hix, ↓reduceIte, Option.map_eq_some_iff] at hr'
    obtain ⟨r₀, hr₀, rfl⟩ := hr'
    rw [Term.eval_replace (he.trans hx.symm)]
    exact hr r₀ hr₀

/-- Between two scopes that differ only in rules, what `Sat` asks beyond `WSat` carries over. -/
theorem Sat.of_eraseRules {S : Sigs} {Γ Γ' : Entries} {ρ : List Value} (hΓ : Sat S Γ ρ) (hW : WSat S Γ' ρ)
    (he : Γ'.map (fun en => { en with rule := none }) = Γ.map (fun en => { en with rule := none })) :
    Sat S Γ' ρ := by
  refine ⟨hW, fun i en v A hen hv hA ht => ?_⟩
  have h1 := congrArg (·[i]?) he
  simp only [List.getElem?_map, hen, Option.map_some] at h1
  cases hen₀ : Γ[i]? with
  | none => simp [hen₀] at h1
  | some en₀ =>
    simp only [hen₀, Option.map_some, Option.some.injEq] at h1
    have hty : en₀.type = en.type := (congrArg Entry.type h1).symm
    have hta : en₀.tainted = en.tainted := (congrArg Entry.tainted h1).symm
    exact hΓ.2 i en₀ v A hen₀ hv (hty ▸ hA) (hta ▸ ht)

theorem Sat.addRule {S : Sigs} {Γ : Entries} {ρ : List Value} {x : Nat} {e : Term} {v : Value}
    (hΓ : Sat S Γ ρ) (hx : ρ[x]? = some v) (he : e.eval ρ [] = some v) : Sat S (addRule Γ x e) ρ := by
  refine hΓ.of_eraseRules (hΓ.1.addRule hx he) ?_
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, addRule_getElem?]
  cases Γ[i]? <;> simp only [Option.map_none, Option.map_some]
  split <;> rfl

/-- `typeOf` gives a term whose value is the type a term's value has by its head. -/
theorem typeOf_eval {S Sc : Sigs} {Γ : Entries} {ρ : List Value} {t T : Term} {v A : Value} (hΓ : WSat Sc Γ ρ)
    (hS : SigsClose S ρ Sc) (hJ : Sc.find junkHead = none) (ht : t.eval ρ [] = some v) (hv : WType Sc v A)
    (hT : typeOf S Γ t = some T) : T.eval ρ [] = some A := by
  cases t with
  | entry i =>
    simp only [typeOf, Option.map_eq_some_iff] at hT
    obtain ⟨en, hen, rfl⟩ := hT
    obtain ⟨w, B, hw, hB, -, hwB, -⟩ := hΓ.2 i en hen
    simp only [Term.eval] at ht
    rw [ht] at hw; cases hw
    rw [hB, hwB.unique hv]
  | bound => simp [Term.eval] at ht
  | app h as =>
    obtain ⟨vs, hvs, rfl⟩ := Term.eval_app.1 ht
    simp only [typeOf, Option.map_eq_some_iff] at hT
    obtain ⟨sig, hs, rfl⟩ := hT
    obtain ⟨sig', hc, ha⟩ := hS h sig hs
    have hne : h ≠ junkHead := fun e => by rw [e, hJ] at hc; cases hc
    simp only [WType, hne, ↓reduceIte] at hv
    obtain ⟨sig'', hc', hr⟩ := hv
    rw [hc] at hc'; cases hc'
    rw [Term.eval_subst hvs, ha.ret vs]
    exact hr

/-- `typeOf` gives a term whose value is the type of the term's value. -/
theorem typeOf_sound {S Sc : Sigs} {Γ : Entries} {ρ : List Value} {t T : Term} {v V : Value} (hΓ : WSat Sc Γ ρ)
    (hS : SigsClose S ρ Sc) (hJ : Sc.find junkHead = none) (ht : t.eval ρ [] = some v) (hv : HasType Sc v V)
    (hT : typeOf S Γ t = some T) : T.eval ρ [] = some V :=
  typeOf_eval hΓ hS hJ ht (hv.wtype hJ) hT

end Pledge
