import Pledge.Sound.Basic

namespace Pledge

theorem Approx.refl : ∀ v : Value, Approx v v
  | .removed => .removed
  | .app _ vs => .app rfl fun k a i ha hi => by
    rw [ha] at hi; cases hi
    have : sizeOf a < 1 + sizeOf vs := by have := List.sizeOf_lt_of_mem (List.mem_of_getElem? ha); omega
    exact Approx.refl a
termination_by v => sizeOf v

theorem Rel.approx {S : Sigs} {phase : Nat} {a i : Value} (h : Rel S phase a i) : Approx a i := by
  induction h with
  | app hl hA hR ih =>
    refine .app hl fun k a i ha hi => ?_
    cases he : Sigs.erasedArg _ _ _ k
    · exact ih k a i ha hi he
    · exact hA k a i ha hi he

theorem Value.noRemoved_of_mem : ∀ {vs : List Value}, Value.noRemovedList vs = true → ∀ {a : Value}, a ∈ vs →
    a.noRemoved = true
  | _ :: _, h, _, .head _ => by simp only [Value.noRemovedList, Bool.and_eq_true] at h; exact h.1
  | _ :: _, h, _, .tail _ hm => by
    simp only [Value.noRemovedList, Bool.and_eq_true] at h; exact Value.noRemoved_of_mem h.2 hm

/-- A value without `removed` is related to itself: running on ideal values is allowed. -/
theorem Rel.refl {S : Sigs} {phase : Nat} : ∀ v : Value, v.noRemoved = true → Rel S phase v v
  | .removed, h => by simp [Value.noRemoved] at h
  | .app h vs, hv => by
    refine .app rfl (fun k a i ha hi _ => by rw [ha] at hi; cases hi; exact Approx.refl a) fun k a i ha hi _ => ?_
    rw [ha] at hi; cases hi
    have hm := List.mem_of_getElem? ha
    have : sizeOf a < 1 + sizeOf vs := by have := List.sizeOf_lt_of_mem hm; omega
    exact Rel.refl a (Value.noRemoved_of_mem (by simpa only [Value.noRemoved] using hv) hm)
termination_by v => sizeOf v

theorem Sigs.erasedArg_mono {S S' : Sigs} (hS : S.Sub S') {phase : Nat} {h : Head} {k : Nat}
    (he : S.erasedArg phase h k = true) : S'.erasedArg phase h k = true := by
  simp only [Sigs.erasedArg, Bool.or_eq_true] at he ⊢
  refine he.imp_right fun he => ?_
  cases hs : S.find h with
  | none => simp [hs] at he
  | some sig => rw [hS _ _ hs]; rw [hs] at he; exact he

/-- More signatures relate more: an argument erased by fewer signatures stays erased. -/
theorem Rel.mono_sigs {S S' : Sigs} (hS : S.Sub S') {phase : Nat} {a i : Value} (h : Rel S phase a i) :
    Rel S' phase a i := by
  induction h with
  | app hl hA hR ih =>
    refine .app hl (fun k a i ha hi he' => ?_) fun k a i ha hi he' => ?_
    · cases he : Sigs.erasedArg _ _ _ k
      · exact (hR k a i ha hi he).approx
      · exact hA k a i ha hi he
    · cases he : Sigs.erasedArg _ _ _ k
      · exact ih k a i ha hi he
      · rw [Sigs.erasedArg_mono hS he] at he'; cases he'

theorem MultRel.approx {S : Sigs} {phase : Nat} {m : Mult} {a i : Value} (h : MultRel S phase m a i) : Approx a i := by
  cases m
  · exact Rel.approx h
  · exact h

theorem MultRel.of_rel {S : Sigs} {phase : Nat} (m : Mult) {a i : Value} (h : Rel S phase a i) :
    MultRel S phase m a i := by
  cases m
  · exact h
  · exact h.approx

theorem MultRel.erased {S : Sigs} {phase : Nat} {a i : Value} (h : Approx a i) : MultRel S phase .erased a i := h

theorem MultRel.removed {S : Sigs} {phase : Nat} {i : Value} : MultRel S phase .erased .removed i := Approx.removed

theorem MultRel.mono_sigs {S S' : Sigs} (hS : S.Sub S') {phase : Nat} {m : Mult} {a i : Value}
    (h : MultRel S phase m a i) : MultRel S' phase m a i := by
  cases m
  · exact Rel.mono_sigs hS h
  · exact h

theorem EnvRel.mono_sigs {S S' : Sigs} (hS : S.Sub S') {phase : Nat} {sc : Scope} {ρ : List Value} {env : Env}
    (h : EnvRel S phase sc ρ env) : EnvRel S' phase sc ρ env := fun n r hn ht =>
  let ⟨a, v, ha, hv, hm⟩ := h n r hn ht
  ⟨a, v, ha, hv, hm.mono_sigs hS⟩

/-- An application related by `Rel`: the same head, each argument related by its multiplicity. -/
theorem Rel.app_iff {S : Sigs} {phase : Nat} {h h' : Head} {as is : List Value} :
    Rel S phase (.app h as) (.app h' is) ↔ h = h' ∧ as.length = is.length ∧
      ∀ (k : Nat) (a i : Value), as[k]? = some a → is[k]? = some i →
        MultRel S phase (if S.erasedArg phase h k then .erased else .many) a i := by
  constructor
  · rintro (⟨hl, hA, hR⟩)
    refine ⟨rfl, hl, fun k a i ha hi => ?_⟩
    cases he : S.erasedArg phase h k
    · exact hR k a i ha hi he
    · exact hA k a i ha hi he
  · rintro ⟨rfl, hl, hm⟩
    refine .app hl (fun k a i ha hi he => ?_) fun k a i ha hi he => ?_
    · have := hm k a i ha hi; rw [he] at this; exact this
    · have := hm k a i ha hi; rw [he] at this; exact this

theorem take_removed (n : Nat) : take n [.removed] = .ok (List.replicate n .removed) := by
  unfold take
  split
  · rename_i h; simp at h; subst h; rfl
  · simp [pure, Except.pure]

theorem take_of_length {n : Nat} {vs : List Value} (h : vs.length = n) : take n vs = .ok vs := by
  simp [take, h, pure, Except.pure]

theorem take_ok {n : Nat} {vs vs' : List Value} (h : take n vs = .ok vs') :
    vs'.length = n ∧ (vs' = vs ∨ vs = [.removed] ∧ vs' = List.replicate n .removed) := by
  unfold take at h
  split at h
  · cases h; exact ⟨‹_›, .inl rfl⟩
  · split at h
    · cases h; rename_i hv; exact ⟨by simp, .inr ⟨hv, rfl⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem take_take {n : Nat} {vs vs' : List Value} (h : take n vs = .ok vs') : take n vs' = .ok vs' :=
  take_of_length (take_ok h).1

theorem one_of_take {vs vs' : List Value} (h : take 1 vs = .ok vs') : ∃ v, one vs = .ok v ∧ vs' = [v] := by
  obtain ⟨hl, rfl | ⟨rfl, rfl⟩⟩ := take_ok h
  · match vs', hl with
    | [v], _ => exact ⟨v, rfl, rfl⟩
  · exact ⟨.removed, rfl, rfl⟩

/-- A removed tree's one value stands for every result; this relates it when every untainted result is in an
erased position. -/
theorem ResRel.removed {S : Sigs} {phase : Nat} {mult : Nat → Mult} {rs : List Res} {ideal : List Value}
    (h : ∀ (i : Nat) (r : Res), rs[i]? = some r → r.tainted = false → mult i = .erased) :
    ResRel S phase mult rs ideal [.removed] := by
  refine ⟨_, take_removed rs.length, fun i r a v hr ha _ ht => ?_⟩
  rw [h i r hr ht]
  rw [List.getElem?_replicate] at ha
  split at ha
  · cases ha; exact Approx.removed
  · cases ha

theorem destruct_erased (pat : Pattern) (v : Value) :
    destruct (some .erased) pat v = .ok (pat.fields.map fun _ => .removed) := by
  simp [destruct, pure, Except.pure]

theorem bindPattern_erased (env : Env) (pat : Pattern) (v : Value) :
    bindPattern env (some .erased) pat v = .ok (pushed pat.fields (pat.fields.map fun _ => .removed) ++ env) := by
  simp only [bindPattern, destruct_erased, ok_bind]
  exact bindIds_of_length (by simp)

theorem pickBranch_erased (v : Value) (b : Branch) : pickBranch (some .erased) v [b] = .ok b := by
  simp [pickBranch, pure, Except.pure]

theorem pickBranch_of_find {h : Head} {ws : List Value} {bs : List Branch} {b : Branch}
    (hf : bs.find? (·.pat.ctor.name == h.name) = some b) : pickBranch none (.app h ws) bs = .ok b := by
  simp [pickBranch, hf, pure, Except.pure]

theorem Entries.eraseRules_getElem? {Γ Γ' : Entries} (h : Γ.eraseRules <+: Γ'.eraseRules) {i : Nat}
    (hi : i < Γ.length) :
    (Γ'[i]?).map (fun en => { en with rule := none }) = (Γ[i]?).map (fun en => { en with rule := none }) := by
  obtain ⟨t, ht⟩ := h
  have := congrArg (·[i]?) ht
  simp only [Entries.eraseRules, List.getElem?_map] at this
  rw [← this, List.getElem?_append_left (by simpa using hi)]
  simp [List.getElem?_map]

/-- A name's multiplicity survives adding entries and rules. -/
theorem Scope.multOf_extend {sc sc' : Scope} (h : sc.Γ.eraseRules <+: sc'.Γ.eraseRules) {r : Res} {ρ : List Value}
    {v : Value} (hl : ρ.length = sc.Γ.length) (hv : r.term.eval ρ [] = some v) : sc'.multOf r = sc.multOf r := by
  simp only [Scope.multOf]
  cases ht : r.term with
  | entry i =>
    rw [ht] at hv
    have hi : i < sc.Γ.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hv).1
    have := Entries.eraseRules_getElem? h hi
    have he : (sc'.Γ[i]?).any (·.erased) = (sc.Γ[i]?).any (·.erased) := by
      cases h1 : sc.Γ[i]? <;> cases h2 : sc'.Γ[i]? <;> simp only [h1, h2, Option.map_none, Option.map_some] at this
      · rfl
      · cases this
      · cases this
      · have := congrArg Entry.erased (Option.some.inj this)
        simpa using this
    simp [Scope.erasedEntry, he]
  | _ => rfl

/-- The run-time environment stays related to the ideal valuation when the scope gains entries and rules. -/
theorem EnvRel.extend {S : Sigs} {phase : Nat} {sc sc' : Scope} {ρ : List Value} {env : Env} (ρ' : List Value)
    (h : EnvRel S phase sc ρ env) (hn : sc'.names = sc.names) (he : sc.Γ.eraseRules <+: sc'.Γ.eraseRules)
    (hl : ρ.length = sc.Γ.length) : EnvRel S phase sc' (ρ ++ ρ') env := fun n r hr ht => by
  have hr' : sc.lookup n = some r := by simpa [Scope.lookup, hn] using hr
  obtain ⟨a, v, ha, hv, hm⟩ := h n r hr' ht
  exact ⟨a, v, ha, Term.eval_frame_ρ ρ' hv, by rw [Scope.multOf_extend he hl hv]; exact hm⟩

end Pledge
