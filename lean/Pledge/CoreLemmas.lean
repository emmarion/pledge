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

theorem HasType.app_iff {S : Sigs} {ρ : List Value} {h : Head} {vs : List Value} {V : Value} :
    HasType S ρ (.app h vs) V ↔
      ∃ sig, S.find h = some sig ∧ TeleSat S ρ sig.params [] vs ∧ sig.ret.eval ρ vs = some V :=
  ⟨fun | .app hs ht hr => ⟨_, hs, ht, hr⟩, fun ⟨_, hs, ht, hr⟩ => .app hs ht hr⟩

theorem HasType.not_removed {S : Sigs} {ρ : List Value} {V : Value} : ¬ HasType S ρ .removed V := nofun

/-- Unique types (SOUNDNESS.md Lemma 2.2). -/
theorem HasType.unique {S : Sigs} {ρ : List Value} {v V V' : Value} :
    HasType S ρ v V → HasType S ρ v V' → V = V'
  | .app hs _ hr, .app hs' _ hr' => by
    rw [hs] at hs'; cases hs'; rw [hr] at hr'; cases hr'; rfl

/-- `S'` has every signature `S` has. -/
def Sigs.Sub (S S' : Sigs) : Prop := ∀ h sig, S.find h = some sig → S'.find h = some sig

mutual
theorem HasType.mono {S S' : Sigs} {ρ : List Value} (hS : S.Sub S') (ρ' : List Value) {v V : Value} :
    HasType S ρ v V → HasType S' (ρ ++ ρ') v V
  | .app hs ht hr => .app (hS _ _ hs) (TeleSat.mono hS ρ' ht) (Term.eval_frame_ρ ρ' hr)
theorem TeleSat.mono {S S' : Sigs} {ρ : List Value} (hS : S.Sub S') (ρ' : List Value)
    {Δ : Telescope} {env vs : List Value} : TeleSat S ρ Δ env vs → TeleSat S' (ρ ++ ρ') Δ env vs
  | .nil => .nil
  | .cons hA hv his ht =>
    .cons (Term.eval_frame_ρ ρ' hA) (HasType.mono hS ρ' hv) (fun e he => Term.eval_frame_ρ ρ' (his e he))
      (TeleSat.mono hS ρ' ht)
end

theorem Sigs.Sub.refl (S : Sigs) : S.Sub S := fun _ _ h => h

theorem HasType.frame {S : Sigs} {ρ : List Value} (ρ' : List Value) {v V : Value} (h : HasType S ρ v V) :
    HasType S (ρ ++ ρ') v V := h.mono (Sigs.Sub.refl S) ρ'

theorem TeleSat.frame {S : Sigs} {ρ : List Value} (ρ' : List Value) {Δ : Telescope} {env vs : List Value}
    (h : TeleSat S ρ Δ env vs) : TeleSat S (ρ ++ ρ') Δ env vs := h.mono (Sigs.Sub.refl S) ρ'

theorem HasType.mono_sigs {S S' : Sigs} {ρ : List Value} (hS : S.Sub S') {v V : Value} (h : HasType S ρ v V) :
    HasType S' ρ v V := by simpa using h.mono hS []

theorem TeleSat.mono_sigs {S S' : Sigs} {ρ : List Value} (hS : S.Sub S') {Δ : Telescope} {env vs : List Value}
    (h : TeleSat S ρ Δ env vs) : TeleSat S' ρ Δ env vs := by simpa using h.mono hS []

/-- The value `v` satisfies the binder `b` when `env` holds the values of the earlier bound variables. -/
def BinderSat (S : Sigs) (ρ : List Value) (b : TBinder) (env : List Value) (v : Value) : Prop :=
  ∃ A, b.type.eval ρ env = some A ∧ HasType S ρ v A ∧ ∀ e, b.is = some e → e.eval ρ env = some v

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

theorem HasType.inv {S : Sigs} {ρ : List Value} {v V : Value} (h : HasType S ρ v V) :
    ∃ hd ws sig, v = .app hd ws ∧ S.find hd = some sig ∧ TeleSat S ρ sig.params [] ws ∧
      sig.ret.eval ρ ws = some V :=
  match h with
  | .app hs ht hr => ⟨_, _, _, rfl, hs, ht, hr⟩

/-- A value whose type applies a type constructor is built by a signature whose return evaluates
to that type (cf. SOUNDNESS.md Lemma 2.1). -/
theorem HasType.inv_type {S : Sigs} {ρ : List Value} {v : Value} {T : String} {us : List Value}
    (h : HasType S ρ v (.app ⟨.type, T⟩ us)) :
    ∃ hd ws sig, v = .app hd ws ∧ S.find hd = some sig ∧ sig.ret.eval ρ ws = some (.app ⟨.type, T⟩ us) :=
  let ⟨hd, ws, sig, hv, hs, _, hr⟩ := h.inv
  ⟨hd, ws, sig, hv, hs, hr⟩

/-- No value has a type whose head no signature returns (SOUNDNESS.md Corollary 2.3). -/
theorem HasType.empty {S : Sigs} {ρ : List Value} {H : Head} {us : List Value}
    (hS : ∀ sig ∈ S, ∃ h' args, sig.ret = .app h' args ∧ h' ≠ H) {v : Value} :
    ¬ HasType S ρ v (.app H us) :=
  fun h => by
    obtain ⟨_, ws, sig, -, hs, -, hr⟩ := h.inv
    obtain ⟨h', args, hret, hne⟩ := hS sig (List.mem_of_find?_eq_some hs)
    rw [hret] at hr
    obtain ⟨_, -, he⟩ := Term.eval_app.1 hr
    exact hne (Value.app.inj he).1.symm

theorem Sat.rulesHold {S : Sigs} {Γ : Entries} {ρ : List Value} (h : Sat S Γ ρ) : RulesHold Γ ρ :=
  fun i en r hen hr =>
    let ⟨v, _, hv, _, _, hrv⟩ := h.2 i en hen
    ⟨v, hv, hrv r hr⟩

theorem Sat.eval_canon {S : Sigs} {Γ : Entries} {ρ : List Value} (h : Sat S Γ ρ) (env : List Value) (t : Term) :
    (t.canon Γ).eval ρ env = t.eval ρ env := Term.eval_canon h.rulesHold env t

theorem Sat.eval_eq_of_identical {S : Sigs} {Γ : Entries} {ρ env : List Value} {a b : Term} (h : Sat S Γ ρ)
    (hab : identical Γ a b = true) : a.eval ρ env = b.eval ρ env := identical.eval_eq h.rulesHold hab

theorem Sat.mono_sigs {S S' : Sigs} {Γ : Entries} {ρ : List Value} (hS : S.Sub S') (h : Sat S Γ ρ) :
    Sat S' Γ ρ :=
  ⟨h.1, fun i en hen =>
    let ⟨v, A, hv, hA, hvA, hr⟩ := h.2 i en hen
    ⟨v, A, hv, hA, hvA.mono_sigs hS, hr⟩⟩

/-- Extending a scope by entries whose values satisfy them, under the extended valuation. -/
theorem Sat.append {S : Sigs} {Γ Δ : Entries} {ρ vs : List Value} (hΓ : Sat S Γ ρ) (hl : vs.length = Δ.length)
    (hΔ : ∀ (i : Nat) (en : Entry), Δ[i]? = some en → ∃ v A, vs[i]? = some v ∧
      en.type.eval (ρ ++ vs) [] = some A ∧ HasType S (ρ ++ vs) v A ∧
      ∀ r : Term, en.rule = some r → r.eval (ρ ++ vs) [] = some v) :
    Sat S (Γ ++ Δ) (ρ ++ vs) := by
  refine ⟨by simp [hΓ.1, hl], fun i en hen => ?_⟩
  by_cases hi : i < Γ.length
  · rw [List.getElem?_append_left hi] at hen
    obtain ⟨v, A, hv, hA, hvA, hr⟩ := hΓ.2 i en hen
    exact ⟨v, A, getElem?_append_of_some hv, Term.eval_frame_ρ vs hA, hvA.frame vs,
      fun r h => Term.eval_frame_ρ vs (hr r h)⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hen
    obtain ⟨v, A, hv, rest⟩ := hΔ _ en hen
    refine ⟨v, A, ?_, rest⟩
    rw [List.getElem?_append_right (by rw [hΓ.1]; omega), hΓ.1]
    exact hv

theorem Sat.push {S : Sigs} {Γ : Entries} {ρ : List Value} {en : Entry} {v A : Value} (hΓ : Sat S Γ ρ)
    (hA : en.type.eval (ρ ++ [v]) [] = some A) (hv : HasType S (ρ ++ [v]) v A)
    (hr : ∀ r : Term, en.rule = some r → r.eval (ρ ++ [v]) [] = some v) : Sat S (Γ ++ [en]) (ρ ++ [v]) :=
  hΓ.append rfl fun i en' hen => by
    cases i with
    | zero => cases hen; exact ⟨v, A, rfl, hA, hv, hr⟩
    | succ => simp at hen

theorem addRule_length (Γ : Entries) (x : Nat) (e : Term) : (addRule Γ x e).length = Γ.length :=
  List.length_mapIdx

theorem addRule_getElem? (Γ : Entries) (x : Nat) (e : Term) (i : Nat) :
    (addRule Γ x e)[i]? = Γ[i]?.map fun en =>
      if i = x then { en with rule := some e } else { en with rule := en.rule.map (Term.replace x e) } :=
  List.getElem?_mapIdx

/-- Adding a rule that holds keeps the scope satisfied. -/
theorem Sat.addRule {S : Sigs} {Γ : Entries} {ρ : List Value} {x : Nat} {e : Term} {v : Value}
    (hΓ : Sat S Γ ρ) (hx : ρ[x]? = some v) (he : e.eval ρ [] = some v) : Sat S (addRule Γ x e) ρ := by
  refine ⟨by rw [addRule_length]; exact hΓ.1, fun i en hen => ?_⟩
  rw [addRule_getElem?, Option.map_eq_some_iff] at hen
  obtain ⟨en₀, hen₀, rfl⟩ := hen
  obtain ⟨w, A, hw, hA, hwA, hr⟩ := hΓ.2 i en₀ hen₀
  by_cases hix : i = x
  · subst hix
    rw [hx] at hw; cases hw
    exact ⟨v, A, hx, by simpa using hA, hwA, by simpa using he⟩
  · refine ⟨w, A, hw, by simpa [hix] using hA, hwA, fun r hr' => ?_⟩
    simp only [hix, ↓reduceIte, Option.map_eq_some_iff] at hr'
    obtain ⟨r₀, hr₀, rfl⟩ := hr'
    rw [Term.eval_replace (he.trans hx.symm)]
    exact hr r₀ hr₀

/-- `typeOf` gives a term whose value is the type of the term's value. -/
theorem typeOf_sound {S : Sigs} {Γ : Entries} {ρ : List Value} {t T : Term} {v V : Value} (hΓ : Sat S Γ ρ)
    (ht : t.eval ρ [] = some v) (hv : HasType S ρ v V) (hT : typeOf S Γ t = some T) : T.eval ρ [] = some V := by
  cases t with
  | entry i =>
    simp only [typeOf, Option.map_eq_some_iff] at hT
    obtain ⟨en, hen, rfl⟩ := hT
    obtain ⟨w, A, hw, hA, hwA, -⟩ := hΓ.2 i en hen
    simp only [Term.eval] at ht
    rw [ht] at hw; cases hw
    rw [hA, hv.unique hwA]
  | bound => simp [Term.eval] at ht
  | app h as =>
    obtain ⟨vs, hvs, rfl⟩ := Term.eval_app.1 ht
    obtain ⟨sig, hs, -, hr⟩ := HasType.app_iff.1 hv
    simp only [typeOf, hs, Option.map_some, Option.some.injEq] at hT
    subst hT
    rw [Term.eval_subst hvs]
    exact hr

theorem typeOf_isSome {S : Sigs} {Γ : Entries} {ρ : List Value} {t : Term} {v V : Value} (hΓ : Sat S Γ ρ)
    (ht : t.eval ρ [] = some v) (hv : HasType S ρ v V) : ∃ T, typeOf S Γ t = some T := by
  cases t with
  | entry i =>
    have hi : i < Γ.length := hΓ.1 ▸ (List.getElem?_eq_some_iff.1 ht).1
    exact ⟨Γ[i].type, by simp [typeOf, List.getElem?_eq_getElem hi]⟩
  | bound => simp [Term.eval] at ht
  | app h as =>
    obtain ⟨vs, -, rfl⟩ := Term.eval_app.1 ht
    obtain ⟨sig, hs, -⟩ := HasType.app_iff.1 hv
    exact ⟨sig.ret.subst as, by simp [typeOf, hs]⟩

theorem typeOf_sound' {S : Sigs} {Γ : Entries} {ρ : List Value} {t : Term} {v V : Value} (hΓ : Sat S Γ ρ)
    (ht : t.eval ρ [] = some v) (hv : HasType S ρ v V) : ∃ T, typeOf S Γ t = some T ∧ T.eval ρ [] = some V :=
  let ⟨T, hT⟩ := typeOf_isSome hΓ ht hv
  ⟨T, hT, typeOf_sound hΓ ht hv hT⟩

end Pledge
