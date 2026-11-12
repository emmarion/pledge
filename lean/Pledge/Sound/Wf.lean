import Pledge.UnifySound

namespace Pledge

mutual
  /-- Entries below `n`, bound variables below `k`, and every application has a signature in `S` and one argument per
  parameter. -/
  def Term.wf (S : Sigs) (n k : Nat) : Term → Bool
    | .entry i => decide (i < n)
    | .bound i => decide (i < k)
    | .app h as => (S.find h).any (·.params.length == as.length) && Term.wfList S n k as
  def Term.wfList (S : Sigs) (n k : Nat) : List Term → Bool
    | [] => true
    | a :: as => a.wf S n k && Term.wfList S n k as
end

mutual
  /-- No entry with a rule occurs. -/
  def Term.free (Γ : Entries) : Term → Bool
    | .entry i => ((Γ[i]?).bind (·.rule)).isNone
    | .bound _ => true
    | .app _ as => Term.freeList Γ as
  def Term.freeList (Γ : Entries) : List Term → Bool
    | [] => true
    | a :: as => a.free Γ && Term.freeList Γ as
end

/-- Binder `j` mentions entries below `n` and bound variables below `k + j`. -/
def Telescope.wf (S : Sigs) (n k : Nat) : Telescope → Bool
  | [] => true
  | b :: bs => b.type.wf S n k && b.is.all (·.wf S n k) && Telescope.wf S n (k + 1) bs

def Sig.wf (S : Sigs) (n : Nat) (sig : Sig) : Bool := Telescope.wf S n 0 sig.params && sig.ret.wf S n sig.params.length

def Sigs.Wf (S : Sigs) (n : Nat) : Prop := ∀ sig ∈ S, sig.wf S n = true

/-- Every entry's type and rule are closed well-formed terms of the scope, and no rule mentions an entry with a
rule. -/
def Entries.Wf (S : Sigs) (Γ : Entries) : Prop :=
  ∀ (i : Nat) (en : Entry), Γ[i]? = some en → en.type.wf S Γ.length 0 = true ∧
    ∀ r : Term, en.rule = some r → r.wf S Γ.length 0 = true ∧ r.free Γ = true

theorem Term.wfList_iff {S : Sigs} {n k : Nat} :
    ∀ {as : List Term}, Term.wfList S n k as = true ↔ ∀ a ∈ as, a.wf S n k = true
  | [] => by simp [Term.wfList]
  | a :: as => by simp [Term.wfList, Term.wfList_iff]

theorem Term.freeList_iff {Γ : Entries} :
    ∀ {as : List Term}, Term.freeList Γ as = true ↔ ∀ a ∈ as, a.free Γ = true
  | [] => by simp [Term.freeList]
  | a :: as => by simp [Term.freeList, Term.freeList_iff]

theorem Term.wf_app {S : Sigs} {n k : Nat} {h : Head} {as : List Term} :
    (Term.app h as).wf S n k = true ↔
      (∃ sig, S.find h = some sig ∧ sig.params.length = as.length) ∧ ∀ a ∈ as, a.wf S n k = true := by
  simp only [Term.wf, Bool.and_eq_true, Term.wfList_iff, Option.any_eq_true, beq_iff_eq]

mutual
theorem Term.wf_mono {S S' : Sigs} {n n' k k' : Nat} (hS : ∀ h sig, S.find h = some sig → S'.find h = some sig)
    (hn : n ≤ n') (hk : k ≤ k') : ∀ t : Term, t.wf S n k = true → t.wf S' n' k' = true
  | .entry _, h => by simp only [Term.wf, decide_eq_true_eq] at *; omega
  | .bound _, h => by simp only [Term.wf, decide_eq_true_eq] at *; omega
  | .app hd as, h => by
    simp only [Term.wf, Bool.and_eq_true, Option.any_eq_true] at *
    obtain ⟨⟨sig, hs, hl⟩, has⟩ := h
    exact ⟨⟨sig, hS _ _ hs, hl⟩, Term.wfList_mono hS hn hk as has⟩
theorem Term.wfList_mono {S S' : Sigs} {n n' k k' : Nat} (hS : ∀ h sig, S.find h = some sig → S'.find h = some sig)
    (hn : n ≤ n') (hk : k ≤ k') : ∀ as : List Term, Term.wfList S n k as = true → Term.wfList S' n' k' as = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.wfList, Bool.and_eq_true] at *
    exact ⟨Term.wf_mono hS hn hk a h.1, Term.wfList_mono hS hn hk as h.2⟩
end

theorem Term.wf_le {S : Sigs} {n n' k k' : Nat} (hn : n ≤ n') (hk : k ≤ k') {t : Term} (h : t.wf S n k = true) :
    t.wf S n' k' = true := Term.wf_mono (fun _ _ h => h) hn hk t h

mutual
theorem Term.wf_subst {S : Sigs} {n k : Nat} {env : List Term} (hk : k ≤ env.length)
    (henv : ∀ u ∈ env, u.wf S n 0 = true) : ∀ t : Term, t.wf S n k = true → (t.subst env).wf S n 0 = true
  | .entry _, h => h
  | .bound i, h => by
    simp only [Term.wf, decide_eq_true_eq] at h
    simp only [Term.subst, List.getElem?_eq_getElem (show i < env.length by omega), Option.getD_some]
    exact henv _ (List.getElem_mem _)
  | .app hd as, h => by
    simp only [Term.wf, Bool.and_eq_true, Option.any_eq_true, Term.subst] at *
    obtain ⟨⟨sig, hs, hl⟩, has⟩ := h
    exact ⟨⟨sig, hs, by rw [Term.substList_eq_map, List.length_map]; exact hl⟩, Term.wfList_subst hk henv as has⟩
theorem Term.wfList_subst {S : Sigs} {n k : Nat} {env : List Term} (hk : k ≤ env.length)
    (henv : ∀ u ∈ env, u.wf S n 0 = true) :
    ∀ as : List Term, Term.wfList S n k as = true → Term.wfList S n 0 (Term.substList env as) = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.wfList, Term.substList, Bool.and_eq_true] at *
    exact ⟨Term.wf_subst hk henv a h.1, Term.wfList_subst hk henv as h.2⟩
end

mutual
theorem Term.wf_replace {S : Sigs} {n k x : Nat} {e : Term} (he : e.wf S n 0 = true) :
    ∀ t : Term, t.wf S n k = true → (Term.replace x e t).wf S n k = true
  | .entry i, h => by
    simp only [Term.replace]; split
    · exact Term.wf_le (Nat.le_refl _) (Nat.zero_le _) he
    · exact h
  | .bound _, h => h
  | .app hd as, h => by
    simp only [Term.wf, Bool.and_eq_true, Option.any_eq_true, Term.replace] at *
    obtain ⟨⟨sig, hs, hl⟩, has⟩ := h
    exact ⟨⟨sig, hs, by rw [Term.replaceList_eq_map, List.length_map]; exact hl⟩, Term.wfList_replace he as has⟩
theorem Term.wfList_replace {S : Sigs} {n k x : Nat} {e : Term} (he : e.wf S n 0 = true) :
    ∀ as : List Term, Term.wfList S n k as = true → Term.wfList S n k (Term.replaceList x e as) = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.wfList, Term.replaceList, Bool.and_eq_true] at *
    exact ⟨Term.wf_replace he a h.1, Term.wfList_replace he as h.2⟩
end

theorem addRule_rule {Γ : Entries} {x : Nat} {e : Term} {i : Nat} :
    ((addRule Γ x e)[i]?).bind (·.rule) =
      if i = x then (Γ[i]?).map fun _ => e else ((Γ[i]?).bind (·.rule)).map (Term.replace x e) := by
  rw [addRule_getElem?]
  cases Γ[i]? <;> simp only [Option.map_none, Option.bind_none, Option.map_some, Option.bind_some] <;> split <;> rfl

mutual
theorem Term.free_addRule {Γ : Entries} {x : Nat} {e : Term} :
    ∀ t : Term, t.free Γ = true → t.occurs x = false → t.free (addRule Γ x e) = true
  | .entry i, h, ho => by
    simp only [Term.occurs, beq_eq_false_iff_ne, ne_eq] at ho
    simp only [Term.free, addRule_rule, ho, ↓reduceIte, Option.isNone_map] at *
    exact h
  | .bound _, _, _ => rfl
  | .app _ as, h, ho => Term.freeList_addRule as h ho
theorem Term.freeList_addRule {Γ : Entries} {x : Nat} {e : Term} :
    ∀ as : List Term, Term.freeList Γ as = true → Term.occursList x as = false →
      Term.freeList (addRule Γ x e) as = true
  | [], _, _ => rfl
  | a :: as, h, ho => by
    simp only [Term.freeList, Term.occursList, Bool.and_eq_true, Bool.or_eq_false_iff] at *
    exact ⟨Term.free_addRule a h.1 ho.1, Term.freeList_addRule as h.2 ho.2⟩
end

mutual
theorem Term.free_replace {Γ : Entries} {x : Nat} {e : Term} (he : e.free Γ = true) (ho : e.occurs x = false) :
    ∀ t : Term, t.free Γ = true → (Term.replace x e t).free (addRule Γ x e) = true
  | .entry i, h => by
    simp only [Term.replace]; split
    · exact Term.free_addRule e he ho
    · rename_i hi
      simp only [Term.free, addRule_rule, hi, ↓reduceIte, Option.isNone_map] at *
      exact h
  | .bound _, _ => rfl
  | .app _ as, h => Term.freeList_replace he ho as h
theorem Term.freeList_replace {Γ : Entries} {x : Nat} {e : Term} (he : e.free Γ = true) (ho : e.occurs x = false) :
    ∀ as : List Term, Term.freeList Γ as = true → Term.freeList (addRule Γ x e) (Term.replaceList x e as) = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.freeList, Term.replaceList, Bool.and_eq_true] at *
    exact ⟨Term.free_replace he ho a h.1, Term.freeList_replace he ho as h.2⟩
end

mutual
theorem Term.free_append {Γ : Entries} {n k : Nat} {S : Sigs} (Δ : Entries) (hn : n ≤ Γ.length) :
    ∀ t : Term, t.wf S n k = true → t.free Γ = true → t.free (Γ ++ Δ) = true
  | .entry i, hw, h => by
    simp only [Term.wf, decide_eq_true_eq, Term.free] at *
    rw [List.getElem?_append_left (by omega)]; exact h
  | .bound _, _, _ => rfl
  | .app _ as, hw, h => by
    simp only [Term.wf, Bool.and_eq_true, Term.free] at *
    exact Term.freeList_append Δ hn as hw.2 h
theorem Term.freeList_append {Γ : Entries} {n k : Nat} {S : Sigs} (Δ : Entries) (hn : n ≤ Γ.length) :
    ∀ as : List Term, Term.wfList S n k as = true → Term.freeList Γ as = true → Term.freeList (Γ ++ Δ) as = true
  | [], _, _ => rfl
  | a :: as, hw, h => by
    simp only [Term.wfList, Term.freeList, Bool.and_eq_true] at *
    exact ⟨Term.free_append Δ hn a hw.1 h.1, Term.freeList_append Δ hn as hw.2 h.2⟩
end

mutual
/-- Canonicalizing a well-formed term in a well-formed scope gives a well-formed term with no entry that has a rule. -/
theorem Term.canon_wf {S : Sigs} {Γ : Entries} {k : Nat} (hΓ : Entries.Wf S Γ) :
    ∀ t : Term, t.wf S Γ.length k = true → (t.canon Γ).wf S Γ.length k = true ∧ (t.canon Γ).free Γ = true
  | .entry i, h => by
    simp only [Term.wf, decide_eq_true_eq] at h
    obtain ⟨en, hen⟩ : ∃ en, Γ[i]? = some en := ⟨_, List.getElem?_eq_getElem h⟩
    simp only [Term.canon, hen, Option.bind_some]
    cases hr : en.rule with
    | none =>
      simp only [Option.getD_none]
      exact ⟨by simpa [Term.wf] using h, by simp only [Term.free, hen, Option.bind_some, hr, Option.isNone_none]⟩
    | some r =>
      obtain ⟨hw, hf⟩ := (hΓ i en hen).2 r hr
      exact ⟨Term.wf_le (Nat.le_refl _) (Nat.zero_le _) hw, hf⟩
  | .bound _, h => ⟨h, rfl⟩
  | .app hd as, h => by
    simp only [Term.wf, Bool.and_eq_true, Option.any_eq_true, Term.canon, Term.free] at *
    obtain ⟨⟨sig, hs, hl⟩, has⟩ := h
    obtain ⟨h1, h2⟩ := Term.canonList_wf hΓ as has
    exact ⟨⟨⟨sig, hs, by rw [Term.canonList_eq_map, List.length_map]; exact hl⟩, h1⟩, h2⟩
theorem Term.canonList_wf {S : Sigs} {Γ : Entries} {k : Nat} (hΓ : Entries.Wf S Γ) :
    ∀ as : List Term, Term.wfList S Γ.length k as = true →
      Term.wfList S Γ.length k (Term.canonList Γ as) = true ∧ Term.freeList Γ (Term.canonList Γ as) = true
  | [], _ => ⟨rfl, rfl⟩
  | a :: as, h => by
    simp only [Term.wfList, Term.freeList, Term.canonList, Bool.and_eq_true] at *
    obtain ⟨a1, a2⟩ := Term.canon_wf hΓ a h.1
    obtain ⟨b1, b2⟩ := Term.canonList_wf hΓ as h.2
    exact ⟨⟨a1, b1⟩, a2, b2⟩
end

theorem Sigs.Wf.mono {S : Sigs} {n n' : Nat} (hS : Sigs.Wf S n) (hn : n ≤ n') : Sigs.Wf S n' := by
  intro sig hs
  have := hS sig hs
  simp only [Sig.wf, Bool.and_eq_true] at *
  refine ⟨?_, Term.wf_le hn (Nat.le_refl _) this.2⟩
  have h := this.1
  generalize sig.params = ps at h ⊢
  generalize 0 = k at h ⊢
  induction ps generalizing k with
  | nil => rfl
  | cons b bs ih =>
    simp only [Telescope.wf, Bool.and_eq_true, Option.all_eq_true] at *
    exact ⟨⟨Term.wf_le hn (Nat.le_refl _) h.1.1, fun e he => Term.wf_le hn (Nat.le_refl _) (h.1.2 e he)⟩,
      ih _ h.2⟩

/-- The type `typeOf` gives a closed well-formed term. -/
theorem typeOf_wf {S : Sigs} {Γ : Entries} {t : Term} (hΓ : Entries.Wf S Γ) (hS : Sigs.Wf S Γ.length)
    (ht : t.wf S Γ.length 0 = true) : ∃ ty, typeOf S Γ t = some ty ∧ ty.wf S Γ.length 0 = true := by
  cases t with
  | entry i =>
    simp only [Term.wf, decide_eq_true_eq] at ht
    obtain ⟨en, hen⟩ : ∃ en, Γ[i]? = some en := ⟨_, List.getElem?_eq_getElem ht⟩
    exact ⟨en.type, by simp [typeOf, hen], (hΓ i en hen).1⟩
  | bound => simp [Term.wf] at ht
  | app hd as =>
    obtain ⟨⟨sig, hs, hl⟩, has⟩ := Term.wf_app.1 ht
    refine ⟨sig.ret.subst as, by simp [typeOf, hs], ?_⟩
    have := hS sig (List.mem_of_find?_eq_some hs)
    simp only [Sig.wf, Bool.and_eq_true] at this
    exact Term.wf_subst (by omega) has _ this.2

theorem Entries.Wf.length_type {S : Sigs} {Γ : Entries} (hΓ : Entries.Wf S Γ) {i : Nat} {en : Entry}
    (h : Γ[i]? = some en) : en.type.wf S Γ.length 0 = true := (hΓ i en h).1

/-- Giving an entry with no rule the rule `e`, well-formed, with no entry that has a rule and not mentioning the entry,
keeps the scope well-formed. -/
theorem Entries.Wf.addRule {S : Sigs} {Γ : Entries} {x : Nat} {e : Term} (hΓ : Entries.Wf S Γ)
    (he : e.wf S Γ.length 0 = true) (hf : e.free Γ = true) (ho : e.occurs x = false) :
    Entries.Wf S (addRule Γ x e) := by
  intro i en hi
  rw [addRule_length]
  rw [addRule_getElem?] at hi
  cases h : Γ[i]? with
  | none => simp [h] at hi
  | some en₀ =>
    simp only [h, Option.map_some, Option.some.injEq] at hi
    obtain ⟨ht, hr⟩ := hΓ i en₀ h
    split at hi
    · subst hi
      exact ⟨ht, fun r hr' => by cases hr'; exact ⟨he, Term.free_addRule e hf ho⟩⟩
    · subst hi
      refine ⟨ht, fun r hr' => ?_⟩
      simp only [Option.map_eq_some_iff] at hr'
      obtain ⟨r₀, hr₀, rfl⟩ := hr'
      obtain ⟨h1, h2⟩ := hr r₀ hr₀
      exact ⟨Term.wf_replace he r₀ h1, Term.free_replace hf ho r₀ h2⟩

theorem Entries.Wf.push {S : Sigs} {Γ : Entries} {en : Entry} (hΓ : Entries.Wf S Γ)
    (ht : en.type.wf S (Γ.length + 1) 0 = true)
    (hr : ∀ r, en.rule = some r → r.wf S Γ.length 0 = true ∧ r.free Γ = true) : Entries.Wf S (Γ ++ [en]) := by
  intro i en' hi
  rw [List.length_append, List.length_singleton]
  rcases Nat.lt_or_ge i Γ.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hi
    obtain ⟨h1, h2⟩ := hΓ i en' hi
    refine ⟨Term.wf_le (by omega) (Nat.le_refl _) h1, fun r hr' => ?_⟩
    obtain ⟨h3, h4⟩ := h2 r hr'
    exact ⟨Term.wf_le (by omega) (Nat.le_refl _) h3, Term.free_append _ (Nat.le_refl _) r h3 h4⟩
  · rw [List.getElem?_append_right hge] at hi
    obtain ⟨rfl, -⟩ : i = Γ.length ∧ True := by
      rcases h : i - Γ.length with _ | k
      · exact ⟨by omega, trivial⟩
      · simp [h] at hi
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    refine ⟨ht, fun r hr' => ?_⟩
    obtain ⟨h3, h4⟩ := hr r hr'
    exact ⟨Term.wf_le (by omega) (Nat.le_refl _) h3, Term.free_append _ (Nat.le_refl _) r h3 h4⟩

/-- Both sides of an equation are closed well-formed terms of the scope with no entry that has a rule. -/
def Eqn.Wf (S : Sigs) (Γ : Entries) (q : Eqn) : Prop :=
  q.lhs.wf S Γ.length 0 = true ∧ q.rhs.wf S Γ.length 0 = true ∧ q.lhs.free Γ = true ∧ q.rhs.free Γ = true

theorem argEqns_mem {h : Head} {p : Nat} :
    ∀ {i : Nat} {as bs : List Term} {q : Eqn}, q ∈ argEqns h p i as bs → q.lhs ∈ as ∧ q.rhs ∈ bs
  | i, a :: as, b :: bs, q, hq => by
    simp only [argEqns, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨List.mem_cons_self, List.mem_cons_self⟩
    · obtain ⟨h1, h2⟩ := argEqns_mem hq
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩
  | _, [], _, _, hq | _, _ :: _, [], _, hq => by simp [argEqns] at hq

/-- What `solve` returns from well-formed equations: never `stuck`; a well-formed scope of the same length; and a
`rigid` failure only for an entry that `may` forbids a rule. -/
def SolveWf (S : Sigs) (may : Nat → Bool) (n : Nat) : Solved → Prop
  | .ok Γ' _ => Entries.Wf S Γ' ∧ Γ'.length = n
  | .failed f => Entries.Wf S f.Γ ∧ f.Γ.length = n ∧ ∀ a b, f.clash = .rigid a b → ∃ i, may i = false
  | .stuck _ => False

theorem Term.entry_or_app_of_wf {S : Sigs} {n : Nat} {t : Term} (h : t.wf S n 0 = true) :
    (∃ i, t = .entry i) ∨ ∃ hd as, t = .app hd as := by
  cases t with
  | entry i => exact .inl ⟨i, rfl⟩
  | bound => simp [Term.wf] at h
  | app hd as => exact .inr ⟨hd, as, rfl⟩

theorem solve_wf {S : Sigs} {may : Nat → Bool} {Γ : Entries} {log : List Step} {eqs : List Eqn}
    (hΓ : Entries.Wf S Γ) (hS : Sigs.Wf S Γ.length) (hq : ∀ q ∈ eqs, q.Wf S Γ) :
    SolveWf S may Γ.length (solve S may Γ log eqs) := by
  induction Γ, log, eqs using solve.induct_unfolding S may with
  | case1 Γ log => exact ⟨hΓ, rfl⟩
  | case2 Γ log q qs _ _ _ ih => exact ih hΓ hS fun q' h => hq q' (List.mem_cons_of_mem _ h)
  | case3 Γ log q qs _ _ h as k bs hl hr _ _ ih =>
    refine ih hΓ hS fun q' h' => ?_
    rcases List.mem_append.1 h' with h' | h'
    · exact hq q' (List.mem_cons_of_mem _ h')
    · obtain ⟨w1, w2, f1, f2⟩ := hq q List.mem_cons_self
      rw [hl] at w1 f1; rw [hr] at w2 f2
      obtain ⟨m1, m2⟩ := argEqns_mem h'
      simp only [Term.wf, Term.free, Bool.and_eq_true, Term.wfList_iff, Term.freeList_iff] at w1 w2 f1 f2
      exact ⟨w1.2 _ m1, w2.2 _ m2, f1 _ m1, f2 _ m2⟩
  | case4 => exact ⟨hΓ, rfl, fun a b h => by cases h⟩
  | case5 Γ log q qs _ _ _ hnapp hp =>
    refine ⟨hΓ, rfl, fun a b _ => ?_⟩
    obtain ⟨w1, w2, -, -⟩ := hq q List.mem_cons_self
    rcases Term.entry_or_app_of_wf w1, Term.entry_or_app_of_wf w2 with
      ⟨⟨i, hi⟩ | ⟨h, as, hl⟩, ⟨j, hj⟩ | ⟨k, bs, hr⟩⟩
    · exact ⟨i, pick_none hp (.inl hi)⟩
    · exact ⟨i, pick_none hp (.inl hi)⟩
    · exact ⟨j, pick_none hp (.inr hj)⟩
    · exact (hnapp h as k bs hl hr).elim
  | case6 => exact ⟨hΓ, rfl, fun a b h => by cases h⟩
  | case7 Γ log q qs _ hne x e ho en hx hn te hte _ _ _ hp ih =>
    obtain ⟨w1, w2, f1, f2⟩ := hq q List.mem_cons_self
    have hpe : (Term.entry x).free Γ = true ∧ e.wf S Γ.length 0 = true ∧ e.free Γ = true := by
      rcases pick_some hp with ⟨hl, rfl⟩ | ⟨hr, rfl⟩
      · rw [hl] at f1; exact ⟨f1, w2, f2⟩
      · rw [hr] at f2; exact ⟨f2, w1, f1⟩
    obtain ⟨-, hew, hef⟩ := hpe
    have hoc : e.occurs x = false := by simpa using ho
    have hΓ' := hΓ.addRule hew hef hoc
    have hl' : (addRule Γ x e).length = Γ.length := addRule_length Γ x e
    have := ih hΓ' (by rw [hl']; exact hS) fun q' h' => by
      rw [Eqn.Wf, hl']
      rcases List.mem_append.1 h' with h' | h'
      · obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.1 h'
        obtain ⟨a1, a2, a3, a4⟩ := hq q₀ (List.mem_cons_of_mem _ hq₀)
        exact ⟨Term.wf_replace hew _ a1, Term.wf_replace hew _ a2, Term.free_replace hef hoc _ a3,
          Term.free_replace hef hoc _ a4⟩
      · simp only [List.mem_singleton] at h'
        subst h'
        obtain ⟨ty, hty, htw⟩ := typeOf_wf hΓ hS hew
        rw [hte] at hty; cases hty
        have b1 := Term.canon_wf hΓ' en.type (by rw [hl']; exact (hΓ x en hx).1)
        have b2 := Term.canon_wf hΓ' te (by rw [hl']; exact htw)
        rw [hl'] at b1 b2
        exact ⟨b1.1, b2.1, b1.2, b2.2⟩
    cases h : solve S may (addRule Γ x e) _ _ <;> rw [h] at this
    · exact ⟨this.1, this.2.trans hl'⟩
    · exact ⟨this.1, this.2.1.trans hl', this.2.2⟩
    · exact this
  | case8 Γ log q qs _ x e ho en hx hn hte _ hp =>
    obtain ⟨w1, w2, -, -⟩ := hq q List.mem_cons_self
    have hew : e.wf S Γ.length 0 = true := by rcases pick_some hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    obtain ⟨ty, hty, -⟩ := typeOf_wf hΓ hS hew
    rw [hte] at hty; cases hty
  | case9 Γ log q qs _ x e ho en hx hn _ hp =>
    obtain ⟨-, -, f1, f2⟩ := hq q List.mem_cons_self
    have hxf : (Term.entry x).free Γ = true := by
      rcases pick_some hp with ⟨hl, -⟩ | ⟨hr, -⟩
      · rw [hl] at f1; exact f1
      · rw [hr] at f2; exact f2
    simp [Term.free, hx] at hxf
    exact hn hxf
  | case10 Γ log q qs _ x e ho hx _ hp =>
    obtain ⟨w1, w2, -, -⟩ := hq q List.mem_cons_self
    have hxw : (Term.entry x).wf S Γ.length 0 = true := by
      rcases pick_some hp with ⟨hl, -⟩ | ⟨hr, -⟩
      · rw [hl] at w1; exact w1
      · rw [hr] at w2; exact w2
    simp only [Term.wf, decide_eq_true_eq] at hxw
    rw [List.getElem?_eq_getElem hxw] at hx; cases hx

theorem openTele.go_wf {S : Sigs} (mk : TBinder → Nat → Entry → Entry) {n : Nat} :
    ∀ (tele : Telescope) (i : Nat) (Γ : Entries) (ids : List Nat) (env : List Term),
      Entries.Wf S Γ → n ≤ Γ.length → Telescope.wf S n env.length tele = true →
      (∀ u ∈ env, u.wf S Γ.length 0 = true) → Entries.Wf S (openTele.go mk i tele ⟨Γ, ids, env⟩).Γ
  | [], _, _, _, _, hΓ, _, _, _ => hΓ
  | b :: bs, i, Γ, ids, env, hΓ, hn, ht, henv => by
    simp only [openTele.go]
    simp only [Telescope.wf, Bool.and_eq_true, Option.all_eq_true] at ht
    obtain ⟨⟨hty, his⟩, hbs⟩ := ht
    have hsub := fun {t : Term} (h : t.wf S n env.length = true) =>
      Term.wf_subst (Nat.le_refl _) henv t (Term.wf_le hn (Nat.le_refl _) h)
    refine openTele.go_wf mk bs (i + 1) _ _ _ (hΓ.push ?_ ?_) (Nat.le_trans hn (by simp)) (by simpa using hbs) ?_
    · exact Term.wf_le (by omega) (Nat.le_refl _) (hsub hty)
    · intro r hr
      simp only [Option.map_eq_some_iff] at hr
      obtain ⟨e, he, rfl⟩ := hr
      exact Term.canon_wf hΓ _ (hsub (his e he))
    · intro u hu
      simp only [List.length_append, List.length_singleton]
      rcases List.mem_append.1 hu with hu | hu
      · exact Term.wf_le (by omega) (Nat.le_refl _) (henv u hu)
      · simp only [List.mem_singleton] at hu; subst hu; simp [Term.wf]

/-- Opening a well-formed telescope keeps the scope well-formed, and the terms the bound variables then stand for are
well-formed in it. -/
theorem openTele_wf {S : Sigs} {Γ : Entries} {tele : Telescope} {env : List Term} {n : Nat}
    (mk : TBinder → Nat → Entry → Entry) (hΓ : Entries.Wf S Γ) (hn : n ≤ Γ.length)
    (ht : Telescope.wf S n env.length tele = true) (henv : ∀ u ∈ env, u.wf S Γ.length 0 = true) :
    Entries.Wf S (openTele Γ tele env mk).Γ ∧
      ∀ u ∈ (openTele Γ tele env mk).env, u.wf S (openTele Γ tele env mk).Γ.length 0 = true := by
  refine ⟨openTele.go_wf mk tele 0 Γ [] env hΓ hn ht henv, ?_⟩
  obtain ⟨-, -, -, hids, he⟩ := openTele_shape Γ tele env mk
  rw [openTele_length, he, hids]
  intro u hu
  rcases List.mem_append.1 hu with hu | hu
  · exact Term.wf_le (by omega) (Nat.le_refl _) (henv u hu)
  · simp only [List.mem_map, List.mem_range'_1] at hu
    obtain ⟨j, hj, rfl⟩ := hu
    simp [Term.wf]; omega

theorem Sigs.Wf.sig {S : Sigs} {n : Nat} (hS : Sigs.Wf S n) {h : Head} {sig : Sig} (hs : S.find h = some sig) :
    Telescope.wf S n 0 sig.params = true ∧ sig.ret.wf S n sig.params.length = true := by
  have := hS sig (List.mem_of_find?_eq_some hs)
  simpa [Sig.wf] using this

/-- What `force` returns for a well-formed scrutinee: never `stuck`, and the fields' entries added to a well-formed
scope. -/
def ForceWf (S : Sigs) (n k : Nat) : Forced → Prop
  | .ok Γ' fields => Entries.Wf S Γ' ∧ Γ'.length = n + k ∧ fields = List.range' n k
  | .refuted _ => True
  | .stuck _ => False

theorem force_wf {S : Sigs} {Γ : Entries} {scrut : Term} {ctor : Sig} (mk : TBinder → Nat → Entry → Entry)
    (hΓ : Entries.Wf S Γ) (hS : Sigs.Wf S Γ.length) (hc : S.find ctor.head = some ctor)
    (hs : scrut.wf S Γ.length 0 = true) : ForceWf S Γ.length ctor.params.length (force S Γ scrut ctor mk) := by
  obtain ⟨htw, hrw⟩ := hS.sig hc
  obtain ⟨hΓo, henv⟩ := openTele_wf (n := Γ.length) (tele := ctor.params) (env := []) mk hΓ (Nat.le_refl _)
    (by simpa using htw) (by simp)
  have hlen := openTele_length Γ ctor.params [] mk
  obtain ⟨-, -, -, hids, he⟩ := openTele_shape Γ ctor.params [] mk
  have hS' : Sigs.Wf S (openTele Γ ctor.params [] mk).Γ.length := hS.mono (by omega)
  have hsw : scrut.wf S (openTele Γ ctor.params [] mk).Γ.length 0 = true := Term.wf_le (by omega) (Nat.le_refl _) hs
  have hel : (openTele Γ ctor.params [] mk).env.length = ctor.params.length := by
    rw [he, hids]; simp
  simp only [force]
  split
  · rename_i hty
    obtain ⟨ty, hty', -⟩ := typeOf_wf hΓo hS' hsw
    rw [hty] at hty'; cases hty'
  · rename_i ty hty
    obtain ⟨ty', hty', htyw⟩ := typeOf_wf hΓo hS' hsw
    rw [hty] at hty'; cases hty'
    have hq := solve_wf (may := fun _ => true) (log := []) hΓo hS' (eqs :=
      [⟨scrut.canon (openTele Γ ctor.params [] mk).Γ,
        (Term.app ctor.head (openTele Γ ctor.params [] mk).env).canon (openTele Γ ctor.params [] mk).Γ, .scrutinee⟩,
       ⟨ty.canon (openTele Γ ctor.params [] mk).Γ,
        (ctor.ret.subst (openTele Γ ctor.params [] mk).env).canon (openTele Γ ctor.params [] mk).Γ,
        .scrutineeType⟩]) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl)
      · have a := Term.canon_wf hΓo _ hsw
        have b := Term.canon_wf hΓo (.app ctor.head (openTele Γ ctor.params [] mk).env)
          (Term.wf_app.2 ⟨⟨ctor, hc, hel.symm⟩, henv⟩)
        exact ⟨a.1, b.1, a.2, b.2⟩
      · have a := Term.canon_wf hΓo _ htyw
        have b := Term.canon_wf hΓo (ctor.ret.subst (openTele Γ ctor.params [] mk).env)
          (Term.wf_subst (by omega) henv _ (Term.wf_le (by omega) (Nat.le_refl _) hrw))
        exact ⟨a.1, b.1, a.2, b.2⟩)
    split
    · rename_i Γ' _ h
      rw [h] at hq
      exact ⟨hq.1, by rw [hq.2, hlen], by rw [hids]⟩
    · rename_i h
      rw [h] at hq
      obtain ⟨i, hi⟩ := hq.2.2 _ _ rfl
      cases hi
    · trivial
    · rename_i h
      rw [h] at hq
      exact hq

theorem force_not_stuck {S : Sigs} {Γ : Entries} {scrut : Term} {ctor : Sig} {mk : TBinder → Nat → Entry → Entry}
    {msg : String} (hΓ : Entries.Wf S Γ) (hS : Sigs.Wf S Γ.length) (hc : S.find ctor.head = some ctor)
    (hs : scrut.wf S Γ.length 0 = true) : force S Γ scrut ctor mk ≠ .stuck msg := fun h => by
  have := force_wf mk hΓ hS hc hs; rw [h] at this; exact this

/-- `unify` on well-formed terms never reports an internal error, and keeps the scope well-formed. -/
theorem unify_wf {S : Sigs} {Γ : Entries} {lhs rhs : Term} {hole : Nat → Bool} (hΓ : Entries.Wf S Γ)
    (hS : Sigs.Wf S Γ.length) (hl : lhs.wf S Γ.length 0 = true) (hr : rhs.wf S Γ.length 0 = true) :
    ∃ Γ' st, unify S Γ lhs rhs hole = .ok (Γ', st) ∧ Entries.Wf S Γ' ∧ Γ'.length = Γ.length := by
  have a := Term.canon_wf hΓ _ hl
  have b := Term.canon_wf hΓ _ hr
  have hq := solve_wf (may := hole) (log := []) hΓ hS (eqs := [⟨lhs.canon Γ, rhs.canon Γ, .given⟩])
    (by simp only [List.mem_singleton]; rintro q rfl; exact ⟨a.1, b.1, a.2, b.2⟩)
  simp only [unify]
  split <;> rename_i h <;> rw [h] at hq
  all_goals first | exact ⟨_, _, rfl, hq.1, hq.2.1⟩ | exact ⟨_, _, rfl, hq⟩ | exact hq.elim

end Pledge
