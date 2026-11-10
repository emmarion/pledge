import Pledge.CoreLemmas
import Pledge.Unify

namespace Pledge

mutual
  def Value.size : Value → Nat
    | .app _ as => Value.sizeList as + 1
    | .removed => 1
  def Value.sizeList : List Value → Nat
    | [] => 0
    | a :: as => a.size + Value.sizeList as
end

theorem Value.size_lt_of_mem {a : Value} : ∀ {as : List Value}, a ∈ as → a.size < Value.sizeList as + 1
  | _ :: bs, .head _ => by simp only [Value.sizeList]; omega
  | _ :: bs, .tail _ h => by have := Value.size_lt_of_mem h; simp only [Value.sizeList]; omega

/-- `v` is a strict subtree of `w`. -/
inductive Value.StrictSub : Value → Value → Prop
  | arg {h : Head} {args : List Value} {v : Value} : v ∈ args → Value.StrictSub v (.app h args)
  | deep {h : Head} {args : List Value} {v a : Value} :
      a ∈ args → Value.StrictSub v a → Value.StrictSub v (.app h args)

theorem Value.StrictSub.size_lt {v w : Value} (h : v.StrictSub w) : v.size < w.size := by
  induction h with
  | arg hm => simpa only [Value.size] using Value.size_lt_of_mem hm
  | deep hm _ ih => have := Value.size_lt_of_mem hm; simp only [Value.size]; omega

theorem Value.StrictSub.irrefl (v : Value) : ¬ v.StrictSub v := fun h => Nat.lt_irrefl _ h.size_lt

theorem Value.StrictSub.wf : WellFounded Value.StrictSub :=
  Subrelation.wf (fun h => Value.StrictSub.size_lt h) (InvImage.wf Value.size Nat.lt_wfRel.wf)

theorem Value.StrictSub.app_iff {v : Value} {h : Head} {ws : List Value} :
    v.StrictSub (.app h ws) ↔ ∃ a ∈ ws, v = a ∨ v.StrictSub a :=
  ⟨fun | .arg hm => ⟨_, hm, .inl rfl⟩ | .deep hm hs => ⟨_, hm, .inr hs⟩,
   fun | ⟨_, hm, .inl rfl⟩ => .arg hm | ⟨_, hm, .inr hs⟩ => .deep hm hs⟩

mutual
theorem Term.strictSub_eval {ρ env : List Value} {s : Term} {v : Value} (hs : s.eval ρ env = some v) :
    ∀ (t : Term) {w : Value}, Term.strictSub s t = true → t.eval ρ env = some w → v.StrictSub w
  | .app _ as, _, hst, ht => by
    obtain ⟨ws, hws, rfl⟩ := Term.eval_app.1 ht
    exact Value.StrictSub.app_iff.2 (Term.strictSubList_eval hs as hst hws)
  | .entry _, _, hst, _ | .bound _, _, hst, _ => by simp [Term.strictSub] at hst
theorem Term.strictSubList_eval {ρ env : List Value} {s : Term} {v : Value} (hs : s.eval ρ env = some v) :
    ∀ (as : List Term) {ws : List Value}, Term.strictSubList s as = true → Term.evalList ρ env as = some ws →
      ∃ a ∈ ws, v = a ∨ v.StrictSub a
  | [], _, hst, _ => by simp [Term.strictSubList] at hst
  | a :: as, _, hst, hws => by
    obtain ⟨u, us, hu, hus, rfl⟩ := Term.evalList_cons_eq_some.1 hws
    simp only [Term.strictSubList, Bool.or_eq_true, beq_iff_eq] at hst
    rcases hst with (rfl | hst) | hst
    · exact ⟨u, List.mem_cons_self, .inl (Option.some.inj (hs.symm.trans hu))⟩
    · exact ⟨u, List.mem_cons_self, .inr (Term.strictSub_eval hs a hst hu)⟩
    · obtain ⟨b, hb, hv⟩ := Term.strictSubList_eval hs as hst hus
      exact ⟨b, List.mem_cons_of_mem _ hb, hv⟩
end

mutual
theorem Term.occurs_eval {ρ env : List Value} {x : Nat} {v : Value} (hx : ρ[x]? = some v) :
    ∀ (t : Term) {w : Value}, Term.occurs x t = true → t.eval ρ env = some w → v = w ∨ v.StrictSub w
  | .entry _, _, ho, ht => by
    simp only [Term.occurs, beq_iff_eq] at ho
    subst ho
    exact .inl (Option.some.inj (hx.symm.trans ht))
  | .bound _, _, ho, _ => by simp [Term.occurs] at ho
  | .app _ as, _, ho, ht => by
    obtain ⟨ws, hws, rfl⟩ := Term.eval_app.1 ht
    exact .inr (Value.StrictSub.app_iff.2 (Term.occursList_eval hx as ho hws))
theorem Term.occursList_eval {ρ env : List Value} {x : Nat} {v : Value} (hx : ρ[x]? = some v) :
    ∀ (as : List Term) {ws : List Value}, Term.occursList x as = true → Term.evalList ρ env as = some ws →
      ∃ a ∈ ws, v = a ∨ v.StrictSub a
  | [], _, ho, _ => by simp [Term.occursList] at ho
  | a :: as, _, ho, hws => by
    obtain ⟨u, us, hu, hus, rfl⟩ := Term.evalList_cons_eq_some.1 hws
    simp only [Term.occursList, Bool.or_eq_true] at ho
    rcases ho with ho | ho
    · exact ⟨u, List.mem_cons_self, Term.occurs_eval hx a ho hu⟩
    · obtain ⟨b, hb, hv⟩ := Term.occursList_eval hx as ho hus
      exact ⟨b, List.mem_cons_of_mem _ hb, hv⟩
end

/-- Under a valuation satisfying `Γ`'s rules, a strict subterm's value is a strict subtree. -/
theorem isStrictSubterm_sound {Γ : Entries} {ρ : List Value} {s t : Term} {v w : Value} (hΓ : RulesHold Γ ρ)
    (h : isStrictSubterm Γ s t = true) (hs : s.eval ρ [] = some v) (ht : t.eval ρ [] = some w) : v.StrictSub w :=
  Term.strictSub_eval (by rw [Term.eval_canon hΓ]; exact hs) _ h (by rw [Term.eval_canon hΓ]; exact ht)

theorem pick_some {may : Nat → Bool} {l r e : Term} {x : Nat} (h : pick may l r = some (x, e)) :
    l = .entry x ∧ e = r ∨ r = .entry x ∧ e = l := by
  cases l <;> cases r <;> simp only [pick] at h <;> (try split at h) <;> (try split at h) <;> simp_all

theorem pick_none {may : Nat → Bool} {l r : Term} {i : Nat} (h : pick may l r = none)
    (hi : l = .entry i ∨ r = .entry i) : may i = false := by
  rcases hi with rfl | rfl
  · cases r <;> simp only [pick] at h <;> (try split at h) <;> (try split at h) <;> simp_all
  · cases l <;> simp only [pick] at h <;> (try split at h) <;> (try split at h) <;> simp_all

theorem pick_holds {may : Nat → Bool} {ρ : List Value} {l r e : Term} {x : Nat} {v : Value}
    (hp : pick may l r = some (x, e)) (hl : l.eval ρ [] = some v) (hr : r.eval ρ [] = some v) (hne : ¬ l = r) :
    ρ[x]? = some v ∧ e.eval ρ [] = some v ∧ e ≠ .entry x := by
  rcases pick_some hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hl, hr, fun h => hne h.symm⟩
  · exact ⟨hr, hl, hne⟩

/-- Both sides of the equation have one value under `ρ`. -/
def Eqn.Holds (ρ : List Value) (q : Eqn) : Prop := ∃ v, q.lhs.eval ρ [] = some v ∧ q.rhs.eval ρ [] = some v

theorem argEqns_holds {ρ : List Value} {h : Head} {p : Nat} :
    ∀ (i : Nat) (as bs : List Term) {vs : List Value}, Term.evalList ρ [] as = some vs →
      Term.evalList ρ [] bs = some vs → ∀ q ∈ argEqns h p i as bs, q.Holds ρ
  | i, a :: as, b :: bs, _, ha, hb, q, hq => by
    obtain ⟨u, us, hu, hus, rfl⟩ := Term.evalList_cons_eq_some.1 ha
    obtain ⟨u', us', hu', hus', he⟩ := Term.evalList_cons_eq_some.1 hb
    injection he with h1 h2
    subst h1 h2
    simp only [argEqns, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨u, hu, hu'⟩
    · exact argEqns_holds (i + 1) as bs hus hus' q hq
  | _, [], _, _, _, _, _, hq | _, _ :: _, [], _, _, _, _, hq => by simp [argEqns] at hq

/-- The entries without their rules. -/
def Entries.eraseRules (Γ : Entries) : Entries := Γ.map fun en => { en with rule := none }

theorem Entries.eraseRules_addRule (Γ : Entries) (x : Nat) (e : Term) :
    (addRule Γ x e).eraseRules = Γ.eraseRules := by
  apply List.ext_getElem?
  intro i
  simp only [Entries.eraseRules, List.getElem?_map, addRule_getElem?]
  cases Γ[i]? <;> simp only [Option.map_none, Option.map_some]
  split <;> rfl

theorem Entries.eraseRules_type {Γ Γ' : Entries} (h : Γ.eraseRules <+: Γ'.eraseRules) {i : Nat} {en : Entry}
    (hi : Γ[i]? = some en) : ∃ en', Γ'[i]? = some en' ∧ en'.type = en.type := by
  obtain ⟨t, ht⟩ := h
  have hlt : i < Γ.eraseRules.length := by simpa [Entries.eraseRules] using (List.getElem?_eq_some_iff.1 hi).1
  have := (List.getElem?_append_left (l₂ := t) hlt).symm.trans (congrArg (·[i]?) ht)
  simp only [Entries.eraseRules, List.getElem?_map, hi, Option.map_some] at this
  cases h' : Γ'[i]? with
  | none => simp [h'] at this
  | some en' =>
    simp only [h', Option.map_some, Option.some.injEq] at this
    exact ⟨en', rfl, (congrArg Entry.type this).symm⟩

/-- What `solve` returns when every pending equation holds under a valuation satisfying the scope. -/
def SolveGood (Sc : Sigs) (may : Nat → Bool) (Γ : Entries) (ρ : List Value) : Solved → Prop
  | .ok Γ' _ => WSat Sc Γ' ρ ∧ Γ'.eraseRules = Γ.eraseRules
  | .failed f => (∃ a b, f.clash = .rigid a b) ∧ ∃ i, may i = false
  | .stuck _ => True

theorem SolveGood.of_eraseRules {S : Sigs} {may : Nat → Bool} {Γ Γ' : Entries} {ρ : List Value} {r : Solved}
    (h : SolveGood S may Γ' ρ r) (he : Γ'.eraseRules = Γ.eraseRules) : SolveGood S may Γ ρ r := by
  cases r with
  | ok => exact ⟨h.1, h.2.trans he⟩
  | _ => exact h

theorem Term.eval_entry_or_app {ρ : List Value} {t : Term} {v : Value} (h : t.eval ρ [] = some v) :
    (∃ i, t = .entry i) ∨ ∃ hd as, t = .app hd as := by
  cases t with
  | entry i => exact .inl ⟨i, rfl⟩
  | bound => simp [Term.eval] at h
  | app hd as => exact .inr ⟨hd, as, rfl⟩

/-- `solve` is sound (SOUNDNESS.md Lemma 3.3): when `ρ` satisfies the scope by heads (`WSat`) and every pending
equation holds under it, it fails only on an entry `may` forbids a rule, and a scope it returns is satisfied by
`ρ` and differs from the old one only in rules. Types are equated by `WType`, so values without types, such as
`Value.junk`, are equated soundly too. -/
theorem solve_sound {S Sc : Sigs} {may : Nat → Bool} {ρ : List Value} {Γ : Entries} {log : List Step}
    {eqs : List Eqn} (hΓ : WSat Sc Γ ρ) (hS : SigsClose S ρ Sc) (hJ : Sc.find junkHead = none)
    (hq : ∀ q ∈ eqs, q.Holds ρ) : SolveGood Sc may Γ ρ (solve S may Γ log eqs) := by
  induction Γ, log, eqs using solve.induct_unfolding S may with
  | case1 Γ log => exact ⟨hΓ, rfl⟩
  | case2 Γ log q qs _ _ _ ih => exact ih hΓ fun q' h => hq q' (List.mem_cons_of_mem _ h)
  | case3 Γ log q qs _ _ h as k bs hl hr _ _ ih =>
    refine ih hΓ fun q' h' => ?_
    rcases List.mem_append.1 h' with h' | h'
    · exact hq q' (List.mem_cons_of_mem _ h')
    · obtain ⟨v, hlv, hrv⟩ := hq q List.mem_cons_self
      rw [hl] at hlv; rw [hr] at hrv
      obtain ⟨vs, hvs, rfl⟩ := Term.eval_app.1 hlv
      obtain ⟨ws, hws, he⟩ := Term.eval_app.1 hrv
      cases (Value.app.inj he).2
      exact argEqns_holds 0 as bs hvs hws q' h'
  | case4 Γ log q qs _ _ _ h as k bs hl hr hne =>
    obtain ⟨v, hlv, hrv⟩ := hq q List.mem_cons_self
    rw [hl] at hlv; rw [hr] at hrv
    obtain ⟨vs, hvs, rfl⟩ := Term.eval_app.1 hlv
    obtain ⟨ws, hws, he⟩ := Term.eval_app.1 hrv
    obtain ⟨rfl, rfl⟩ := Value.app.inj he
    exact absurd ⟨rfl, (Term.length_evalList hvs).symm.trans (Term.length_evalList hws)⟩ hne
  | case5 Γ log q qs _ _ _ hnapp hp =>
    obtain ⟨v, hlv, hrv⟩ := hq q List.mem_cons_self
    refine ⟨⟨_, _, rfl⟩, ?_⟩
    rcases Term.eval_entry_or_app hlv, Term.eval_entry_or_app hrv with
      ⟨⟨i, hi⟩ | ⟨h, as, hl⟩, ⟨j, hj⟩ | ⟨k, bs, hr⟩⟩
    · exact ⟨i, pick_none hp (.inl hi)⟩
    · exact ⟨i, pick_none hp (.inl hi)⟩
    · exact ⟨j, pick_none hp (.inr hj)⟩
    · exact (hnapp h as k bs hl hr).elim
  | case6 Γ log q qs _ _ hne x e ho _ hp =>
    obtain ⟨v, hlv, hrv⟩ := hq q List.mem_cons_self
    obtain ⟨hx, he, hex⟩ := pick_holds hp hlv hrv hne
    cases e with
    | entry j => simp only [Term.occurs, beq_iff_eq] at ho; exact absurd (ho ▸ rfl) hex
    | bound => simp [Term.eval] at he
    | app h as =>
      obtain ⟨ws, hws, rfl⟩ := Term.eval_app.1 he
      exact absurd (Value.StrictSub.app_iff.2 (Term.occursList_eval hx as ho hws)) (Value.StrictSub.irrefl _)
  | case7 Γ log q qs _ hne x e _ en hx _ te hte _ _ _ hp ih =>
    obtain ⟨v, hlv, hrv⟩ := hq q List.mem_cons_self
    obtain ⟨hxv, he, -⟩ := pick_holds hp hlv hrv hne
    have hΓ' := hΓ.addRule hxv he
    obtain ⟨w, A, hw, hA, -, hwA, -⟩ := hΓ.2 x en hx
    obtain rfl := Option.some.inj (hxv.symm.trans hw)
    refine (ih hΓ' fun q' h' => ?_).of_eraseRules (Entries.eraseRules_addRule Γ x e)
    rcases List.mem_append.1 h' with h' | h'
    · obtain ⟨q₀, hq₀, rfl⟩ := List.mem_map.1 h'
      obtain ⟨u, hu, hu'⟩ := hq q₀ (List.mem_cons_of_mem _ hq₀)
      exact ⟨u, by rw [Term.eval_replace (he.trans hxv.symm)]; exact hu,
        by rw [Term.eval_replace (he.trans hxv.symm)]; exact hu'⟩
    · simp only [List.mem_singleton] at h'
      subst h'
      exact ⟨A, by rw [hΓ'.eval_canon]; exact hA, by rw [hΓ'.eval_canon]; exact typeOf_eval hΓ hS hJ he hwA hte⟩
  | _ => trivial

/-- `solve` only gives entries rules, whatever the valuation. -/
theorem solve_eraseRules {S : Sigs} {may : Nat → Bool} {Γ Γ' : Entries} {log log' : List Step} {eqs : List Eqn}
    (h : solve S may Γ log eqs = .ok Γ' log') : Γ'.eraseRules = Γ.eraseRules := by
  induction Γ, log, eqs using solve.induct_unfolding S may with
  | case1 Γ log => cases h; rfl
  | case7 Γ log q qs _ hne x e _ en hx _ te hte _ _ _ hp ih =>
    exact (ih h).trans (Entries.eraseRules_addRule Γ x e)
  | _ => first | (cases h; done) | (rename_i ih; exact ih h)

theorem solve_ok {S Sc : Sigs} {may : Nat → Bool} {ρ : List Value} {Γ Γ' : Entries} {log log' : List Step}
    {eqs : List Eqn} (hΓ : WSat Sc Γ ρ) (hS : SigsClose S ρ Sc) (hJ : Sc.find junkHead = none)
    (hq : ∀ q ∈ eqs, q.Holds ρ) (h : solve S may Γ log eqs = .ok Γ' log') :
    WSat Sc Γ' ρ ∧ Γ'.eraseRules = Γ.eraseRules := by
  have := solve_sound (may := may) (log := log) hΓ hS hJ hq; rwa [h] at this

theorem solve_ok_sat {S Sc : Sigs} {may : Nat → Bool} {ρ : List Value} {Γ Γ' : Entries} {log log' : List Step}
    {eqs : List Eqn} (hΓ : Sat Sc Γ ρ) (hS : SigsClose S ρ Sc) (hJ : Sc.find junkHead = none)
    (hq : ∀ q ∈ eqs, q.Holds ρ) (h : solve S may Γ log eqs = .ok Γ' log') :
    Sat Sc Γ' ρ ∧ Γ'.eraseRules = Γ.eraseRules := by
  obtain ⟨hW, he⟩ := solve_ok hΓ.1 hS hJ hq h
  exact ⟨hΓ.of_eraseRules hW he, he⟩

theorem solve_failed {S Sc : Sigs} {may : Nat → Bool} {ρ : List Value} {Γ : Entries} {log : List Step}
    {eqs : List Eqn} {f : Failure} (hΓ : WSat Sc Γ ρ) (hS : SigsClose S ρ Sc) (hJ : Sc.find junkHead = none)
    (hq : ∀ q ∈ eqs, q.Holds ρ) (h : solve S may Γ log eqs = .failed f) :
    (∃ a b, f.clash = .rigid a b) ∧ ∃ i, may i = false := by
  have := solve_sound (may := may) (log := log) hΓ hS hJ hq; rwa [h] at this

theorem solve_total_not_failed {S Sc : Sigs} {ρ : List Value} {Γ : Entries} {log : List Step} {eqs : List Eqn}
    {f : Failure} (hΓ : WSat Sc Γ ρ) (hS : SigsClose S ρ Sc) (hJ : Sc.find junkHead = none)
    (hq : ∀ q ∈ eqs, q.Holds ρ) : solve S (fun _ => true) Γ log eqs ≠ .failed f :=
  fun h => by simpa using (solve_failed hΓ hS hJ hq h).2

theorem Term.evalList_frame_ρ {ρ env : List Value} (ρ' : List Value) {as : List Term} {vs : List Value}
    (h : Term.evalList ρ env as = some vs) : Term.evalList (ρ ++ ρ') env as = some vs := by
  simpa using Term.evalList_frame ρ' [] as h

theorem Term.evalList_append {ρ env : List Value} {as bs : List Term} {vs ws : List Value}
    (ha : Term.evalList ρ env as = some vs) (hb : Term.evalList ρ env bs = some ws) :
    Term.evalList ρ env (as ++ bs) = some (vs ++ ws) := by
  rw [Term.evalList_eq_mapM] at *
  rw [List.mapM_append, ha, hb]
  rfl

theorem openTele.go_shape (mk : TBinder → Nat → Entry → Entry) :
    ∀ (tele : Telescope) (i : Nat) (Γ : Entries) (ids : List Nat) (env : List Term),
      ∃ Δ, (openTele.go mk i tele ⟨Γ, ids, env⟩).Γ = Γ ++ Δ ∧ Δ.length = tele.length ∧
        (openTele.go mk i tele ⟨Γ, ids, env⟩).ids = ids ++ List.range' Γ.length tele.length ∧
        (openTele.go mk i tele ⟨Γ, ids, env⟩).env = env ++ (List.range' Γ.length tele.length).map .entry
  | [], _, _, _, _ => ⟨[], by simp [openTele.go]⟩
  | b :: bs, i, Γ, ids, env => by
    simp only [openTele.go]
    obtain ⟨Δ, h1, h2, h3, h4⟩ := openTele.go_shape mk bs (i + 1) _ (ids ++ [Γ.length]) (env ++ [.entry Γ.length])
    rw [h1, h3, h4]
    exact ⟨_ :: Δ, List.append_assoc .., by simp [h2], by simp [List.range'_succ], by simp [List.range'_succ]⟩

/-- What opening a telescope needs of the values of its fresh entries: each has the binder's type by its head and
meets the binder's `is` clause, and, where `typed` says so, has the binder's type. -/
def TeleOk (S : Sigs) (ρ : List Value) (typed : Nat → Bool) : Telescope → List Value → List Value → Prop
  | [], _, [] => True
  | b :: Δ, env, v :: vs =>
    (∃ A, b.type.eval ρ env = some A ∧ v.noRemoved = true ∧ WType S v A ∧ (typed 0 = true → HasType S v A)) ∧
    (∀ e, b.is = some e → e.eval ρ env = some v) ∧ TeleOk S ρ (fun k => typed (k + 1)) Δ (env ++ [v]) vs
  | _, _, _ => False

theorem TeleOk.length_eq {S : Sigs} {ρ : List Value} :
    ∀ {typed : Nat → Bool} {Δ : Telescope} {env vs : List Value}, TeleOk S ρ typed Δ env vs → vs.length = Δ.length
  | _, [], _, [], _ => rfl
  | _, _ :: _, _, _ :: _, h => by simp [TeleOk.length_eq h.2.2]
  | _, [], _, _ :: _, h | _, _ :: _, _, [], h => h.elim

theorem TeleOk.frame {S : Sigs} {ρ : List Value} (ρ' : List Value) :
    ∀ {typed : Nat → Bool} {Δ : Telescope} {env vs : List Value}, TeleOk S ρ typed Δ env vs →
      TeleOk S (ρ ++ ρ') typed Δ env vs
  | _, [], _, [], _ => trivial
  | _, _ :: _, _, _ :: _, ⟨⟨A, hA, h1, h2, h3⟩, his, ht⟩ =>
    ⟨⟨A, Term.eval_frame_ρ ρ' hA, h1, h2, h3⟩, fun e he => Term.eval_frame_ρ ρ' (his e he), TeleOk.frame ρ' ht⟩
  | _, [], _, _ :: _, h | _, _ :: _, _, [], h => h.elim

theorem TeleOk.imp_typed {S : Sigs} {ρ : List Value} :
    ∀ {f g : Nat → Bool} {Δ : Telescope} {env vs : List Value}, TeleOk S ρ f Δ env vs →
      (∀ k, g k = true → f k = true) → TeleOk S ρ g Δ env vs
  | _, _, [], _, [], _, _ => trivial
  | _, _, _ :: _, _, _ :: _, ⟨⟨A, hA, h1, h2, h3⟩, his, ht⟩, hfg =>
    ⟨⟨A, hA, h1, h2, fun h => h3 (hfg 0 h)⟩, his, TeleOk.imp_typed ht fun k => hfg (k + 1)⟩
  | _, _, [], _, _ :: _, h, _ | _, _, _ :: _, _, [], h, _ => h.elim

/-- Values satisfying a telescope meet it in the sense of `TeleOk`, typed everywhere. -/
theorem TeleSat.teleOk {S : Sigs} {ρ : List Value} (hJ : S.find junkHead = none) (typed : Nat → Bool) :
    ∀ {Δ : Telescope} {env vs : List Value}, TeleSat S ρ Δ env vs → TeleOk S ρ typed Δ env vs
  | [], _, _, h => by rw [TeleSat.nil_iff.1 h]; trivial
  | _ :: _, _, _, h => by
    obtain ⟨v, vs', rfl, ⟨A, hA, hv, his⟩, ht⟩ := TeleSat.cons_iff.1 h
    exact ⟨⟨A, hA, hv.noRemoved, hv.wtype hJ, fun _ => hv⟩, his, TeleSat.teleOk hJ _ ht⟩

theorem openTele.go_sound {S : Sigs} (mk : TBinder → Nat → Entry → Entry) (taint : Nat → Bool)
    (hmk : ∀ b k en, en.tainted = false → (mk b k en).tainted = taint k) :
    ∀ (tele : Telescope) {i : Nat} {Γ : Entries} {ids : List Nat} {env : List Term} {ρ envv vs : List Value},
      Sat S Γ ρ → Term.evalList ρ [] env = some envv → TeleOk S ρ (fun k => !taint (i + k)) tele envv vs →
      Sat S (openTele.go mk i tele ⟨Γ, ids, env⟩).Γ (ρ ++ vs) ∧
        Term.evalList (ρ ++ vs) [] (openTele.go mk i tele ⟨Γ, ids, env⟩).env = some (envv ++ vs)
  | [], _, _, _, _, ρ, _, vs, hΓ, henv, ht => by
    cases vs with
    | nil => simpa [openTele.go] using ⟨hΓ, henv⟩
    | cons => exact ht.elim
  | b :: bs, i, Γ, ids, env, ρ, envv, vs, hΓ, henv, ht => by
    obtain ⟨v, vs, rfl⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => exact ht.elim
      | cons v vs' => exact ⟨v, vs', rfl⟩
    obtain ⟨⟨A, hA, hnr, hw, hty⟩, his, ht⟩ := ht
    have henv' := Term.evalList_frame_ρ [v] henv
    have hx : Term.evalList (ρ ++ [v]) [] [.entry Γ.length] = some [v] := by
      simp [Term.evalList, Term.eval, ← hΓ.1.1]
    have key := fun (en : Entry) (hok : EntryOk S (ρ ++ [v]) en v) =>
      openTele.go_sound mk taint hmk bs (i := i + 1) (ids := ids ++ [Γ.length]) (hΓ.push hok)
        (Term.evalList_append henv' hx) (by
          refine (TeleOk.frame [v] ht).imp_typed fun k hk => ?_
          simp only at hk ⊢
          rwa [show i + (k + 1) = i + 1 + k by omega])
    simp only [List.append_assoc, List.singleton_append] at key
    simp only [openTele.go]
    refine key _ ⟨A, by rw [Term.eval_subst henv']; exact Term.eval_frame_ρ [v] hA, hnr, hw, fun htn => ?_,
      fun r hr => ?_⟩
    · rw [hmk _ _ _ rfl] at htn
      exact hty (by simpa using htn)
    · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hr
      exact Term.eval_frame_ρ [v] (by rw [hΓ.eval_canon, Term.eval_subst henv]; exact his e he)

/-- Opening a telescope to fresh entries whose values meet it keeps the scope satisfied, an entry marked untainted
needing a value of its type, and its environment's terms take the values of the outer environment followed by
`vs`. -/
theorem openTele_sound {S : Sigs} {Γ : Entries} {ρ : List Value} {tele : Telescope} {env : List Term}
    {envv vs : List Value} (mk : TBinder → Nat → Entry → Entry) (taint : Nat → Bool)
    (hmk : ∀ b k en, en.tainted = false → (mk b k en).tainted = taint k) (hΓ : Sat S Γ ρ)
    (henv : Term.evalList ρ [] env = some envv) (ht : TeleOk S ρ (fun k => !taint k) tele envv vs) :
    Sat S (openTele Γ tele env mk).Γ (ρ ++ vs) ∧
      Term.evalList (ρ ++ vs) [] (openTele Γ tele env mk).env = some (envv ++ vs) :=
  openTele.go_sound mk taint hmk tele hΓ henv (by simpa using ht)

/-- `openTele` appends one entry per binder, and its ids are theirs. -/
theorem openTele_shape (Γ : Entries) (tele : Telescope) (env : List Term) (mk : TBinder → Nat → Entry → Entry) :
    ∃ Δ, (openTele Γ tele env mk).Γ = Γ ++ Δ ∧ Δ.length = tele.length ∧
      (openTele Γ tele env mk).ids = List.range' Γ.length tele.length ∧
      (openTele Γ tele env mk).env = env ++ (openTele Γ tele env mk).ids.map .entry := by
  obtain ⟨Δ, h1, h2, h3, h4⟩ := openTele.go_shape mk tele 0 Γ [] env
  exact ⟨Δ, h1, h2, by simpa [openTele] using h3, by rw [openTele, h4, h3]; simp⟩

theorem openTele_ids_length (Γ : Entries) (tele : Telescope) (env : List Term)
    (mk : TBinder → Nat → Entry → Entry) : (openTele Γ tele env mk).ids.length = tele.length := by
  obtain ⟨_, _, _, h, _⟩ := openTele_shape Γ tele env mk; simp [h]

theorem openTele_length (Γ : Entries) (tele : Telescope) (env : List Term) (mk : TBinder → Nat → Entry → Entry) :
    (openTele Γ tele env mk).Γ.length = Γ.length + tele.length := by
  obtain ⟨_, h, hl, _⟩ := openTele_shape Γ tele env mk; simp [h, hl]

/-- Forcing only adds the fields' entries and gives entries rules, whatever the valuation. -/
theorem force_eraseRules {S : Sigs} {Γ Γ' : Entries} {scrut : Term} {ctor : Sig} {mk : TBinder → Nat → Entry → Entry}
    {fields : List Nat} (h : force S Γ scrut ctor mk = .ok Γ' fields) :
    Γ'.eraseRules = (openTele Γ ctor.params [] mk).Γ.eraseRules ∧ Γ.eraseRules <+: Γ'.eraseRules ∧
      fields = (openTele Γ ctor.params [] mk).ids := by
  simp only [force] at h
  split at h
  · cases h
  · split at h
    · rename_i Γ'' _ hs
      cases h
      have he := solve_eraseRules hs
      obtain ⟨Δ, hΔ, -⟩ := openTele_shape Γ ctor.params [] mk
      exact ⟨he, ⟨Δ.eraseRules, by rw [he, hΔ]; simp [Entries.eraseRules]⟩, rfl⟩
    all_goals cases h

/-- What `force` returns when the scrutinee's value is headed by the value constructor forced. -/
def ForceGood (Sc : Sigs) (Γ : Entries) (ρ ws : List Value) (Γo : Entries) : Forced → Prop
  | .ok Γ' fields => Sat Sc Γ' (ρ ++ ws) ∧ Γ'.eraseRules = Γo.eraseRules ∧ Γ.eraseRules <+: Γ'.eraseRules ∧
      Γ'.length = Γ.length + ws.length ∧ fields = List.range' Γ.length ws.length ∧
      Term.evalList (ρ ++ ws) [] (fields.map .entry) = some ws
  | .refuted _ => False
  | .stuck _ => True

/-- Forcing is sound (SOUNDNESS.md Lemma 3.3): forcing the value constructor that heads the scrutinee's typed value
does not refute it, and the fields take the value's arguments. The bridge to the closed signatures is needed under
the valuation before and after the fields' values are appended; `mk` is meant not to mark the fields tainted. -/
theorem force_good {S Sc : Sigs} {Γ : Entries} {ρ ws : List Value} {scrut : Term} {ctor : Sig} {V : Value}
    (mk : TBinder → Nat → Entry → Entry) (hmk : ∀ b k en, en.tainted = false → (mk b k en).tainted = false)
    (hΓ : Sat Sc Γ ρ) (hS : SigsClose S ρ Sc) (hS' : SigsClose S (ρ ++ ws) Sc) (hJ : Sc.find junkHead = none)
    (hs : scrut.eval ρ [] = some (.app ctor.head ws)) (hc : S.find ctor.head = some ctor)
    (hV : HasType Sc (.app ctor.head ws) V) :
    ForceGood Sc Γ ρ ws (openTele Γ ctor.params [] mk).Γ (force S Γ scrut ctor mk) := by
  obtain ⟨ht, hret⟩ := (hS.hasType_app_iff hc).1 hV
  obtain ⟨Δ, hΔ, hΔl, hids, henv⟩ := openTele_shape Γ ctor.params [] mk
  obtain ⟨hΓo, henvo⟩ := openTele_sound mk (fun _ => false) hmk hΓ (rfl : Term.evalList ρ [] [] = some [])
    (ht.teleOk hJ _)
  simp only [List.nil_append] at henvo henv
  have hlen := ht.length_eq
  simp only [force]
  split
  · trivial
  · rename_i ty hty
    have hq : ∀ q ∈ [⟨scrut.canon (openTele Γ ctor.params [] mk).Γ,
        (Term.app ctor.head (openTele Γ ctor.params [] mk).env).canon (openTele Γ ctor.params [] mk).Γ, .scrutinee⟩,
        ⟨ty.canon (openTele Γ ctor.params [] mk).Γ,
          (ctor.ret.subst (openTele Γ ctor.params [] mk).env).canon (openTele Γ ctor.params [] mk).Γ,
          .scrutineeType⟩], Eqn.Holds (ρ ++ ws) q := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl)
      · exact ⟨_, by rw [hΓo.eval_canon]; exact Term.eval_frame_ρ ws hs,
          by rw [hΓo.eval_canon]; exact Term.eval_app.2 ⟨ws, henvo, rfl⟩⟩
      · exact ⟨V, by rw [hΓo.eval_canon]; exact typeOf_sound hΓo.1 hS' hJ (Term.eval_frame_ρ ws hs) hV hty,
          by rw [hΓo.eval_canon, Term.eval_subst henvo]; exact Term.eval_frame_ρ ws hret⟩
    split
    · rename_i Γ' _ h
      obtain ⟨hΓ', he⟩ := solve_ok_sat hΓo hS' hJ hq h
      refine ⟨hΓ', he, ⟨Δ.eraseRules, by rw [he, hΔ]; simp [Entries.eraseRules]⟩, ?_, by rw [hids, hlen], ?_⟩
      · rw [← List.length_map (f := fun en : Entry => { en with rule := none })]
        change Γ'.eraseRules.length = _
        rw [he, Entries.eraseRules, List.length_map, hΔ, List.length_append, hΔl, hlen]
      · rw [← henv]; exact henvo
    all_goals first
      | trivial
      | (rename_i h; exact absurd (solve_failed hΓo.1 hS' hJ hq h).2 (by simp))
      | (rename_i _ h; exact absurd (solve_failed hΓo.1 hS' hJ hq h).2 (by simp))

theorem force_ok {S Sc : Sigs} {Γ Γ' : Entries} {ρ ws : List Value} {scrut : Term} {ctor : Sig} {V : Value}
    {mk : TBinder → Nat → Entry → Entry} {fields : List Nat}
    (hmk : ∀ b k en, en.tainted = false → (mk b k en).tainted = false) (hΓ : Sat Sc Γ ρ) (hS : SigsClose S ρ Sc)
    (hS' : SigsClose S (ρ ++ ws) Sc) (hJ : Sc.find junkHead = none) (hs : scrut.eval ρ [] = some (.app ctor.head ws))
    (hc : S.find ctor.head = some ctor) (hV : HasType Sc (.app ctor.head ws) V)
    (h : force S Γ scrut ctor mk = .ok Γ' fields) :
    Sat Sc Γ' (ρ ++ ws) ∧ Γ'.eraseRules = (openTele Γ ctor.params [] mk).Γ.eraseRules ∧
      Γ.eraseRules <+: Γ'.eraseRules ∧ Γ'.length = Γ.length + ws.length ∧
      fields = List.range' Γ.length ws.length ∧ Term.evalList (ρ ++ ws) [] (fields.map .entry) = some ws := by
  have := force_good mk hmk hΓ hS hS' hJ hs hc hV; rwa [h] at this

/-- If forcing refutes a value constructor, no valuation satisfying the scope, and bridging the signatures to the
closed ones before and after the fields' values are appended, gives the scrutinee a typed value headed by it. -/
theorem force_refuted {S Sc : Sigs} {Γ : Entries} {scrut : Term} {ctor : Sig}
    {mk : TBinder → Nat → Entry → Entry} {f : Failure} (hmk : ∀ b k en, en.tainted = false → (mk b k en).tainted = false)
    (hJ : Sc.find junkHead = none) (hc : S.find ctor.head = some ctor) (h : force S Γ scrut ctor mk = .refuted f) :
    ¬ ∃ ρ ws V, Sat Sc Γ ρ ∧ SigsClose S ρ Sc ∧ SigsClose S (ρ ++ ws) Sc ∧
      scrut.eval ρ [] = some (.app ctor.head ws) ∧ HasType Sc (.app ctor.head ws) V :=
  fun ⟨_, _, _, hΓ, hS, hS', hs, hV⟩ => by have := force_good mk hmk hΓ hS hS' hJ hs hc hV; rwa [h] at this

mutual
theorem Term.eval_boundsBelow {ρ env : List Value} (env' : List Value) :
    ∀ t : Term, t.boundsBelow env.length = true → t.eval ρ (env ++ env') = t.eval ρ env
  | .entry _, _ => rfl
  | .bound _, h => by
    simp only [Term.boundsBelow, decide_eq_true_eq] at h
    simp [Term.eval, List.getElem?_append_left h]
  | .app _ as, h => by simp only [Term.eval, Term.evalList_boundsBelow env' as h]
theorem Term.evalList_boundsBelow {ρ env : List Value} (env' : List Value) :
    ∀ as : List Term, Term.boundsBelowList env.length as = true →
      Term.evalList ρ (env ++ env') as = Term.evalList ρ env as
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.boundsBelowList, Bool.and_eq_true] at h
    simp only [Term.evalList, Term.eval_boundsBelow env' a h.1, Term.evalList_boundsBelow env' as h.2]
end

theorem Term.eval_closed {ρ : List Value} (env : List Value) {t : Term} (h : t.closed = true) :
    t.eval ρ env = t.eval ρ [] := by
  simpa using Term.eval_boundsBelow (ρ := ρ) (env := []) env t h

mutual
theorem Term.closed_subst {env : List Term} (henv : ∀ u ∈ env, u.closed = true) :
    ∀ t : Term, t.boundsBelow env.length = true → (t.subst env).closed = true
  | .entry _, _ => rfl
  | .bound _, h => by
    simp only [Term.boundsBelow, decide_eq_true_eq] at h
    simp only [Term.subst, List.getElem?_eq_getElem h, Option.getD_some]
    exact henv _ (List.getElem_mem h)
  | .app _ as, h => Term.closedList_subst henv as h
theorem Term.closedList_subst {env : List Term} (henv : ∀ u ∈ env, u.closed = true) :
    ∀ as : List Term, Term.boundsBelowList env.length as = true → Term.boundsBelowList 0 (Term.substList env as) = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.boundsBelowList, Bool.and_eq_true] at h
    simp only [Term.substList, Term.boundsBelowList, Bool.and_eq_true]
    exact ⟨Term.closed_subst henv a h.1, Term.closedList_subst henv as h.2⟩
end

mutual
theorem Term.eval_mapEntries {ρ env : List Value} {f : Nat → Term} :
    ∀ t : Term, (∀ i, t.occurs i = true → (f i).eval ρ env = ρ[i]?) → t.closed = true →
      (t.mapEntries f).eval ρ env = t.eval ρ []
  | .entry i, hf, _ => by simp [Term.mapEntries, Term.eval, hf i (by simp [Term.occurs])]
  | .bound _, _, hc => by simp [Term.closed, Term.boundsBelow] at hc
  | .app _ as, hf, hc => by simp only [Term.mapEntries, Term.eval, Term.evalList_mapEntries as hf hc]
theorem Term.evalList_mapEntries {ρ env : List Value} {f : Nat → Term} :
    ∀ as : List Term, (∀ i, Term.occursList i as = true → (f i).eval ρ env = ρ[i]?) →
      Term.boundsBelowList 0 as = true → Term.evalList ρ env (Term.mapEntriesList f as) = Term.evalList ρ [] as
  | [], _, _ => rfl
  | a :: as, hf, hc => by
    simp only [Term.boundsBelowList, Bool.and_eq_true] at hc
    simp only [Term.mapEntriesList, Term.evalList,
      Term.eval_mapEntries a (fun i h => hf i (by simp [Term.occursList, h])) hc.1,
      Term.evalList_mapEntries as (fun i h => hf i (by simp [Term.occursList, h])) hc.2]
end

mutual
theorem Term.closed_of_canon {Γ : Entries} :
    ∀ t : Term, (t.canon Γ).closed = true → t.closed = true ∧
      ∀ i en r, t.occurs i = true → Γ[i]? = some en → en.rule = some r → r.closed = true
  | .entry i, h => ⟨rfl, fun j en r hj hen hr => by
      simp only [Term.occurs, beq_iff_eq] at hj
      subst hj
      simpa [Term.canon, hen, hr] using h⟩
  | .bound _, h => by simp [Term.canon, Term.closed, Term.boundsBelow] at h
  | .app _ as, h => Term.closedList_of_canon as h
theorem Term.closedList_of_canon {Γ : Entries} :
    ∀ as : List Term, Term.boundsBelowList 0 (Term.canonList Γ as) = true → Term.boundsBelowList 0 as = true ∧
      ∀ i en r, Term.occursList i as = true → Γ[i]? = some en → en.rule = some r → r.closed = true
  | [], _ => ⟨rfl, fun _ _ _ h => by simp [Term.occursList] at h⟩
  | a :: as, h => by
    simp only [Term.canonList, Term.boundsBelowList, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := Term.closed_of_canon a h.1
    obtain ⟨h3, h4⟩ := Term.closedList_of_canon as h.2
    refine ⟨by simp only [Term.boundsBelowList, Bool.and_eq_true]; exact ⟨h1, h3⟩, fun i en r hi => ?_⟩
    simp only [Term.occursList, Bool.or_eq_true] at hi
    exact hi.elim (h2 i en r) (h4 i en r)
end

theorem getElem?_of_idxOf? {ids : List Nat} {i k : Nat} (h : ids.idxOf? i = some k) : ids[k]? = some i := by
  obtain ⟨hk, he, -⟩ := List.idxOf?_eq_some_iff.1 h
  simp [List.getElem?_eq_getElem hk, he]

/-- `abstract?` is sound: when the bound variables take the values of the entries abstracted, the abstracted term
has the value of the original. -/
theorem abstract?_eval {Γ : Entries} {ρ env : List Value} {t u : Term} {ids : List Nat} (hΓ : RulesHold Γ ρ)
    (h : abstract? Γ t ids = some u) (henv : ∀ k i : Nat, ids[k]? = some i → env[k]? = ρ[i]?) :
    u.eval ρ env = t.eval ρ [] := by
  simp only [abstract?] at h
  split at h
  · rename_i hc
    cases h
    obtain ⟨htc, hrc⟩ := Term.closed_of_canon t hc
    have leaf : ∀ i (other : Term), other.eval ρ env = ρ[i]? →
        (((ids.idxOf? i).map .bound).getD other).eval ρ env = ρ[i]? := by
      intro i other ho
      cases hk : ids.idxOf? i with
      | none => simpa using ho
      | some k => simpa [Term.eval] using henv k i (getElem?_of_idxOf? hk)
    refine Term.eval_mapEntries t (fun i hi => leaf i _ ?_) htc
    cases hen : Γ[i]? with
    | none => rfl
    | some en =>
      cases hr : en.rule with
      | none => simp [hr, Term.eval]
      | some r =>
        obtain ⟨v, hv, hrv⟩ := hΓ i en r hen hr
        simp only [Option.bind_some, hr, Option.elim_some]
        rw [Term.eval_mapEntries r (fun j _ => leaf j (.entry j) rfl) (hrc i en r hi hen hr), hrv, hv]
  · cases h

end Pledge
