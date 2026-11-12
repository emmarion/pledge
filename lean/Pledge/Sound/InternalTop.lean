import Pledge.Sound.Internal
import Pledge.Sound.Top

namespace Pledge

theorem Sigs.find_append_of {S : Sigs} {s : Sig} {h : Head} {sig : Sig} (hs : S.find h = some sig) :
    Sigs.find (S ++ [s]) h = some sig := by
  simp only [Sigs.find] at hs ⊢
  simp only [List.find?_append, hs, Option.some_or]

theorem Sigs.find_append_isSome {S : Sigs} {s : Sig} {h : Head} (hs : s.head = h) :
    ∃ sig, Sigs.find (S ++ [s]) h = some sig := by
  cases hf : S.find h with
  | some sig => exact ⟨sig, Sigs.find_append_of hf⟩
  | none =>
    refine ⟨s, ?_⟩
    simp only [Sigs.find] at hf ⊢
    simp [List.find?_append, hf, hs]

theorem Entries.Wf.sigs {S S' : Sigs} {Γ : Entries} (h : Entries.Wf S Γ)
    (hS : ∀ hd sig, S.find hd = some sig → S'.find hd = some sig) : Entries.Wf S' Γ := fun i en hi =>
  ⟨Term.wf_mono hS (Nat.le_refl _) (Nat.le_refl _) _ (h i en hi).1, fun r hr =>
    ⟨Term.wf_mono hS (Nat.le_refl _) (Nat.le_refl _) _ ((h i en hi).2 r hr).1, ((h i en hi).2 r hr).2⟩⟩

theorem GlobOk.sigs {gs : List Global} {S S' : Sigs} {n : Nat} (h : GlobOk gs S n)
    (hS : ∀ hd sig, S.find hd = some sig → S'.find hd = some sig) : GlobOk gs S' n := by
  intro g hg
  have := h g hg
  cases g with
  | fn _ sig => cases sig with
    | none => trivial
    | some sig => exact ⟨Telescope.wf_mono hS (Nat.le_refl _) this.1, Telescope.wf_mono hS (Nat.le_refl _) this.2.1,
        this.2.2.1, this.2.2.2⟩
  | type =>
    exact ⟨let ⟨s, hs⟩ := this.1; ⟨s, hS _ _ hs⟩, fun cs h c hc => let ⟨s, hs⟩ := this.2 cs h c hc;
      ⟨s, hS _ _ hs⟩⟩
  | ctor => exact let ⟨s, hs⟩ := this; ⟨s, hS _ _ hs⟩

theorem Sigs.Wf.append {S : Sigs} {n : Nat} {s : Sig} (h : Sigs.Wf S n) (hs : s.wf (S ++ [s]) n = true) :
    Sigs.Wf (S ++ [s]) n := by
  intro sig hm
  rcases List.mem_append.1 hm with hm | hm
  · have := h sig hm
    simp only [Sig.wf, Bool.and_eq_true] at this ⊢
    exact ⟨Telescope.wf_mono (fun _ _ => Sigs.find_append_of) (Nat.le_refl _) this.1,
      Term.wf_mono (fun _ _ => Sigs.find_append_of) (Nat.le_refl _) (Nat.le_refl _) _ this.2⟩
  · rw [List.mem_singleton.1 hm]; exact hs

/-- The top level's state, as the internal-check proof needs it: its scope meets `ScOk`, `Type` has a signature, the
global named by each name of a group being declared is the first with that name, and a type goal is well-formed. -/
structure TopWf (st : TopState) : Prop where
  ok : ScOk st.ctx st.sc
  typeSig : ∃ s, st.sc.sigs.find Head.Type = some s ∧ s.params = []
  goal : ∀ g, st.goal = some g → ∀ t, g.kind = .type t → t.wf st.sc.sigs st.sc.Γ.length 0 = true

theorem ScOk.top {st : TopState} (h : ScOk st.ctx st.sc) (b : Bool) : ScOk (st.ctx b) st.sc := h.ctx rfl

theorem TYPE_wf {S : Sigs} {n k : Nat} (h : ∃ s, S.find Head.Type = some s ∧ s.params = []) :
    Term.TYPE.wf S n k = true := by
  obtain ⟨s, hs, hp⟩ := h
  exact Term.wf_app.2 ⟨⟨s, hs, by simp [hp]⟩, by simp⟩

mutual
theorem Term.boundsBelow_of_wf {S : Sigs} {n k : Nat} : ∀ t : Term, t.wf S n k = true → t.boundsBelow k = true
  | .entry _, _ => rfl
  | .bound _, h => by simpa [Term.wf, Term.boundsBelow] using h
  | .app _ as, h => by simp only [Term.wf, Bool.and_eq_true] at h; exact Term.boundsBelowList_of_wf as h.2
theorem Term.boundsBelowList_of_wf {S : Sigs} {n k : Nat} :
    ∀ as : List Term, Term.wfList S n k as = true → Term.boundsBelowList k as = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.wfList, Term.boundsBelowList, Bool.and_eq_true] at *
    exact ⟨Term.boundsBelow_of_wf a h.1, Term.boundsBelowList_of_wf as h.2⟩
end

theorem topLevel_noInt {st : TopState} {pos : Pos} {tele : Telescope} {k : Nat}
    (h : Telescope.wf st.sc.sigs st.sc.Γ.length k tele = true) : NoInt (topLevel st pos tele) (fun _ => True) :=
  NoInt.ensure (Telescope.entriesBelow_of_wf h)

theorem fresh_none {C : Ctx} {sc : Scope} {seen : List String} {n : String} {pos : Pos} :
    NoInt (fresh C sc seen (some n) pos) (fun _ => C.global n = none) := by
  unfold fresh
  simp only
  split
  · exact NoInt.failAt
  · split
    · exact NoInt.failAt
    · rename_i h
      simp only [Bool.or_eq_true, not_or, Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at h
      exact NoInt.pure h.2

/-- The name `n` is a type constructor's at the top level. -/
def TopState.HasType (st : TopState) (n : String) : Prop := ∃ cs b, st.ctx.global n = some (.type n cs b)

theorem TopWf.addSig {st : TopState} {s : Sig} {g : Global} (hst : TopWf st)
    (hs : s.wf (st.sc.sigs ++ [s]) st.sc.Γ.length = true) (hg : GlobOk [g] (st.sc.sigs ++ [s]) st.sc.Γ.length) :
    TopWf (addSig st s g) := by
  have hS := fun hd sig (h : st.sc.sigs.find hd = some sig) => Sigs.find_append_of (s := s) h
  refine ⟨⟨hst.ok.Γ.sigs hS, hst.ok.sigs.append hs, fun p hp => ?_, ?_⟩, ?_,
    ?_⟩
  · exact Term.wf_mono hS (Nat.le_refl _) (Nat.le_refl _) _ (hst.ok.names p hp)
  · intro g' hg'
    rcases List.mem_append.1 hg' with hg' | hg'
    · exact (hst.ok.globals.sigs hS) g' hg'
    · exact hg g' hg'
  · obtain ⟨t, ht, hp⟩ := hst.typeSig; exact ⟨t, hS _ _ ht, hp⟩
  · intro gl hgl t ht
    exact Term.wf_mono hS (Nat.le_refl _) (Nat.le_refl _) _ (hst.goal gl hgl t ht)

theorem declType_noInt {st : TopState} {d : Data} (hst : TopWf st) (hname : d.name.name ≠ "sorry") :
    NoInt (declType st d) (fun st' => TopWf st' ∧ st'.globals = st.globals ++ [.type d.name.name (some []) false] ∧
      st.ctx.global d.name.name = none ∧ st'.sc.Γ = st.sc.Γ) := by
  unfold declType
  refine NoInt.bind fresh_none fun _ hn => ?_
  refine NoInt.bind (NoInt.ensure (by simpa [junkHead] using hname)) fun _ _ => ?_
  refine NoInt.bind (telescope_noInt (n := st.sc.Γ.length) (outer := []) (hst.ok.top true) (Nat.le_refl _)
    (fun i en r _ hen hr => ((hst.ok.Γ i en hen).2 r hr).1) fun i h1 h2 => absurd h2 (by omega))
    fun ps ⟨p1, p2, p3, p4, p5, p6, p7⟩ => ?_
  refine NoInt.bind (topLevel_noInt (k := 0) (by simpa using p7)) fun _ _ => NoInt.pure ⟨?_, rfl, hn, rfl⟩
  refine hst.addSig ?_ fun g hg => ?_
  · simp only [Sig.wf, Bool.and_eq_true]
    exact ⟨Telescope.wf_mono (fun _ _ => Sigs.find_append_of) (Nat.le_refl _) (by simpa using p7),
      TYPE_wf (let ⟨t, ht, hp⟩ := hst.typeSig; ⟨t, Sigs.find_append_of ht, hp⟩)⟩
  · simp only [List.mem_singleton] at hg
    subst hg
    exact ⟨Sigs.find_append_isSome rfl, fun cs h c hc => by cases h; cases hc⟩

theorem checkTerm_type_head {C : Ctx} {sc : Scope} {whole : Bool} {hh : Name} {args : List WTerm} {r : Res}
    {cs : Option (List String)} {b : Bool} (hg : C.global hh.name = some (.type hh.name cs b))
    (h : checkTerm C sc whole (.app hh args) = .ok r) : ∃ as, r.term = .app ⟨.type, hh.name⟩ as := by
  unfold checkTerm at h
  dsimp only at h
  rw [hg] at h
  simp only [pure, Except.pure, ok_bind] at h
  obtain ⟨sig, hsig, h⟩ := bind_eq_ok.1 h
  obtain ⟨_, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨rs, -, h⟩ := bind_eq_ok.1 h
  simp only [Except.ok.injEq] at h
  subst h
  exact ⟨_, by rw [Sigs.find_head (Scope.sig_ok hsig)]⟩

theorem find?_map_type {l : List Global} {f : Global → Global} {n : String} {cs : Option (List String)} {b : Bool}
    (hf : ∀ g, (f g).name = g.name) (ht : ∀ n cs b, ∃ cs', f (.type n cs b) = .type n cs' b)
    (h : l.find? (·.name == n) = some (.type n cs b)) :
    ∃ cs' b', (l.map f).find? (·.name == n) = some (.type n cs' b') := by
  rw [List.find?_map]
  have : ((fun g : Global => g.name == n) ∘ f) = fun g => g.name == n := by funext g; simp [Function.comp, hf]
  rw [this, h]
  obtain ⟨cs', h'⟩ := ht n cs b
  exact ⟨cs', b, by simp [h']⟩

theorem declCtor_noInt {owner : String} {st : TopState} {k : Ctor} (hst : TopWf st)
    (hname : k.name.name ≠ "sorry") (hown : st.HasType owner) :
    NoInt (declCtor owner st k) (fun st' => TopWf st' ∧ ∀ n, st.HasType n → st'.HasType n) := by
  obtain ⟨ocs, ob, hown⟩ := hown
  unfold declCtor
  refine NoInt.bind fresh_none fun _ hn => ?_
  refine NoInt.bind (NoInt.ensure (by simpa [junkHead] using hname)) fun _ _ => ?_
  refine NoInt.bind (telescope_noInt (n := st.sc.Γ.length) (outer := []) (hst.ok.top true) (Nat.le_refl _)
    (fun i en r _ hen hr => ((hst.ok.Γ i en hen).2 r hr).1) fun i h1 h2 => absurd h2 (by omega))
    fun fs ⟨p1, p2, p3, p4, p5, p6, p7⟩ => ?_
  dsimp only
  rcases hret : k.ret with x | ⟨hh, args⟩ | pp
  · exact NoInt.failAt_bind
  rotate_left
  · exact NoInt.failAt_bind
  simp only
  split
  case isFalse => exact NoInt.failAt_bind
  rename_i hm
  have hhn : hh.name = owner := by simpa using hm
  refine NoInt.bind (NoInt.of_ok (P := fun r : Res => r.term.wf fs.sc.sigs fs.sc.Γ.length 0 = true ∧
    ∃ as, r.term = .app ⟨.type, hh.name⟩ as) (NoInt.imp (term_noInt (whole := false) p1) fun _ _ => trivial)
    fun r h => ?_) fun r ⟨hrw, hh'⟩ => ?_
  · have hw := (term_noInt (whole := false) p1).2 r h
    refine ⟨hw, ?_⟩
    exact checkTerm_type_head (by rw [hhn]; exact hown) h
  obtain ⟨as, has⟩ := hh'
  refine NoInt.bind (abstractChecked_noInt p1.Γ hrw) fun ret hret' => ?_
  have hS : fs.sc.sigs = st.sc.sigs := p2
  have hlen : fs.sc.Γ.length = st.sc.Γ.length + k.fields.length := p4
  have hids : fs.ids = List.range' st.sc.Γ.length k.fields.length := p5
  have hrw' : ret.wf st.sc.sigs st.sc.Γ.length fs.tele.length = true := by
    rw [hret', hids, p6, ← hS]
    refine abstract_wf (m := fs.sc.Γ.length) hrw (by omega) (fun i hi hk => ?_) (fun i k' hi hk => ?_) ?_
    · exact idxOf?_range'_none (outer := []) (n := st.sc.Γ.length) (n0 := st.sc.Γ.length) (len := k.fields.length)
        (j := k.fields.length) (Nat.le_refl _) (by omega) (fun i h1 h2 => absurd h2 (by omega)) (by simpa using hk)
    · simpa using idxOf?_range' (outer := []) (n0 := st.sc.Γ.length) (len := k.fields.length)
        (j := k.fields.length) (i := i) (k := k')
        (Nat.le_refl _) (by omega) (by simpa using hk)
    · intro i en r hi hen hr
      obtain ⟨t, ht⟩ := p3
      rw [← ht, List.getElem?_append_left hi] at hen
      rw [hS]; exact ((hst.ok.Γ i en hen).2 r hr).1
  refine NoInt.bind (topLevel_noInt (k := 0) (by simpa using p7)) fun _ _ => ?_
  refine NoInt.bind (NoInt.ensure ?_) fun _ _ => NoInt.pure ⟨?_, ?_⟩
  · simp only [Bool.and_eq_true]
    refine ⟨⟨Term.entriesBelow_of_wf hrw', Term.boundsBelow_of_wf _ hrw'⟩, ?_⟩
    rw [hret', has]
    simp [abstract, Term.mapEntries, hhn]
  · have hw := hst.addSig (s := ⟨⟨.ctor, k.name.name⟩, fs.tele, ret⟩) (g := .ctor k.name.name) (by
      simp only [Sig.wf, Bool.and_eq_true]
      exact ⟨Telescope.wf_mono (fun _ _ => Sigs.find_append_of) (Nat.le_refl _) (by simpa using p7),
        Term.wf_mono (fun _ _ => Sigs.find_append_of) (Nat.le_refl _) (Nat.le_refl _) _ hrw'⟩)
      (fun g hg => by
        simp only [List.mem_singleton] at hg; subst hg
        exact Sigs.find_append_isSome rfl)
    refine ⟨⟨hw.ok.Γ, hw.ok.sigs, hw.ok.names, fun g hg => ?_⟩, hw.typeSig, hw.goal⟩
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have := hw.ok.globals g0 hg0
    cases g0 with
    | type n cs d =>
      cases cs with
      | none => exact this
      | some cs =>
        refine ⟨this.1, fun cs' hcs c hc => ?_⟩
        simp only [Option.some.injEq] at hcs
        subst hcs
        split at hc
        · rcases List.mem_append.1 hc with hc | hc
          · exact this.2 cs rfl c hc
          · simp only [List.mem_singleton] at hc; subst hc
            exact Sigs.find_append_isSome rfl
        · exact this.2 cs rfl c hc
    | fn => exact this
    | ctor => exact this
  · intro n ⟨cs, b, hn⟩
    simp only [TopState.HasType, TopState.ctx, Ctx.global, addSig] at hn ⊢
    refine find?_map_type ?_ ?_ (by rw [List.find?_append, hn]; rfl)
    · intro g; rcases g with ⟨⟩ | ⟨n, _ | cs, d⟩ | ⟨⟩ <;> rfl
    · intro n cs b; rcases cs with _ | cs
      · exact ⟨none, rfl⟩
      · exact ⟨_, rfl⟩

theorem NoInt.foldlM_pre {γ δ : Type} {f : δ → γ → CheckM δ} {I : List γ → δ → Prop} {L : List γ}
    (hf : ∀ pre a s, a ∈ L → I pre s → NoInt (f s a) (I (pre ++ [a]))) :
    ∀ (l pre : List γ) (init : δ), (∀ a ∈ l, a ∈ L) → I pre init → NoInt (l.foldlM f init) (I (pre ++ l))
  | [], pre, _, _, hi => by simpa using NoInt.pure hi
  | a :: l, pre, init, hl, hi => by
    rw [List.foldlM_cons]
    exact NoInt.bind (hf pre a init (hl a List.mem_cons_self) hi) fun s hs => by
      simpa using NoInt.foldlM_pre hf l (pre ++ [a]) s (fun b hb => hl b (List.mem_cons_of_mem _ hb)) hs

/-- A `data` declaration as the internal-check proof needs it: no type constructor or value constructor named
`sorry`. -/
def Data.shaped (d : Data) : Bool := d.name.name != "sorry" && d.ctors.all (·.name.name != "sorry")

theorem dataGroup_noInt {st : TopState} {ds : List Data} (hst : TopWf st)
    (hok : ∀ d ∈ ds, d.shaped = true) : NoInt (dataGroup st ds) (TopWf) := by
  unfold dataGroup
  have hcov : ∀ d ∈ ds, d.name.name ≠ "sorry" ∧ ∀ k ∈ d.ctors, k.name.name ≠ "sorry" := by
    intro d hd
    simpa [Data.shaped] using hok d hd
  refine NoInt.bind (NoInt.foldlM_pre (I := fun pre st' => TopWf st' ∧ (∀ n, st.HasType n → st'.HasType n) ∧
    ∀ d ∈ pre, st'.HasType d.name.name) (L := ds) (fun pre d s hd ⟨h1, h2, h3⟩ => ?_) ds [] st (fun _ h => h)
    ⟨hst, fun _ h => h, by simp⟩) fun st1 ⟨a1, _, a3⟩ => ?_
  · obtain ⟨hn, -⟩ := hcov d hd
    refine NoInt.imp (declType_noInt h1 hn) fun s' ⟨e1, e2, e3, _⟩ => ?_
    have keep : ∀ n, s.HasType n → s'.HasType n := by
      intro n ⟨cs, b, hn⟩
      refine ⟨cs, b, ?_⟩
      simp only [TopState.ctx, Ctx.global] at hn ⊢
      rw [e2, List.find?_append, hn]; rfl
    refine ⟨e1, fun n h => keep n (h2 n h), fun d' hd' => ?_⟩
    rcases List.mem_append.1 hd' with hd' | hd'
    · exact keep _ (h3 d' hd')
    · simp only [List.mem_singleton] at hd'; subst hd'
      refine ⟨some [], false, ?_⟩
      simp only [TopState.ctx, Ctx.global] at e3 ⊢
      rw [e2, List.find?_append, e3]
      simp [Global.name]
  · refine NoInt.bind (NoInt.foldlM_pre (I := fun _ s => TopWf s ∧ ∀ d ∈ ds, s.HasType d.name.name) (L := ds)
      (fun _ d s hd ⟨h1, h2⟩ => ?_) ds [] st1 (fun _ h => h) ⟨a1, by simpa using a3⟩) fun st2 ⟨b1, _⟩ => ?_
    · obtain ⟨-, hk⟩ := hcov d hd
      refine NoInt.foldlM_pre (I := fun _ s => TopWf s ∧ ∀ d ∈ ds, s.HasType d.name.name) (L := d.ctors)
        (fun _ k s hk' ⟨g1, g2⟩ => ?_) d.ctors [] s (fun _ h => h) ⟨h1, h2⟩
      exact NoInt.imp (declCtor_noInt g1 (hk k hk') (g2 d hd)) fun s' ⟨c1, c2⟩ =>
        ⟨c1, fun d' hd' => c2 _ (g2 d' hd')⟩
    · refine NoInt.pure ⟨⟨b1.ok.Γ, b1.ok.sigs, b1.ok.names, fun g hg => ?_⟩,
        b1.typeSig, b1.goal⟩
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      have := b1.ok.globals g0 hg0
      rcases g0 with ⟨⟩ | ⟨n, cs, _ | _⟩ | ⟨⟩ <;> exact this

theorem fixTaint_noInt {step : List Bool → CheckM (List Out)} (h : ∀ t, NoInt (step t) (fun _ => True)) :
    ∀ (n : Nat) (t : List Bool), untainted t = n → NoInt (fixTaint step t) (fun _ => True) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro t hn
  rw [fixTaint]
  refine NoInt.bind (h t) fun bodies _ => ?_
  dsimp only
  split
  · rename_i hg
    exact ih _ (hn ▸ untainted_spread_lt _ _ hg) _ rfl
  · exact NoInt.pure trivial

theorem checkAll_noInt {γ : Type} {step : γ → CheckM Out} :
    ∀ {l : List γ}, (∀ a ∈ l, NoInt (step a) (fun _ => True)) → NoInt (checkAll step l) (fun _ => True)
  | [], _ => by unfold checkAll; exact NoInt.pure trivial
  | a :: l, h => by
    unfold checkAll
    exact NoInt.bind (h a List.mem_cons_self) fun _ _ => NoInt.bind (NoInt.keep (checkAll_noInt fun b hb =>
      h b (List.mem_cons_of_mem _ hb))) fun _ _ => NoInt.pure trivial

/-- A function's checked header, as the internal-check proof needs it: its parameters' scope well-formed, its
signature well-formed with the top level's entries, and what its body is given. -/
structure FnHeadOk (S : Sigs) (n : Nat) (h : FnHead) : Prop where
  Γ : Entries.Wf S h.sc.Γ
  sigsWf : Sigs.Wf S h.sc.Γ.length
  names : ∀ p ∈ h.sc.names, p.2.term.wf S h.sc.Γ.length 0 = true
  sigs : h.sc.sigs = S
  len : n ≤ h.sc.Γ.length
  params : Telescope.wf S n 0 h.sig.params = true
  returns : Telescope.wf S n h.sig.params.length h.sig.returns = true
  subterm : h.sig.subterm.length = h.sig.params.length
  ne : h.sig.returns ≠ []
  env : ∀ u ∈ h.env, u.wf S h.sc.Γ.length 0 = true
  envLen : h.env.length = h.sig.params.length
  body : h.f.body.shaped = true

/-- A function as the internal-check proof needs it: at least one return. -/
def Fn.shaped (f : Fn) : Bool := !f.header.returns.isEmpty && f.body.shaped

theorem GlobOk.fnSig {gs : List Global} {S : Sigs} {n : Nat} {name : String} {sig : FnSig} (h : GlobOk gs S n)
    (hs : Telescope.wf S n 0 sig.params = true ∧ Telescope.wf S n sig.params.length sig.returns = true ∧
      sig.subterm.length = sig.params.length ∧ sig.returns ≠ []) :
    GlobOk (gs.map fun g => if g.name == name then .fn g.name (some sig) else g) S n := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
  by_cases hn : (g0.name == name) = true
  · simp only [hn, ↓reduceIte]; exact hs
  · simp only [hn]; exact h g0 hg0

theorem Telescope.wf_append {S : Sigs} {n : Nat} : ∀ {k : Nat} {a b : Telescope},
    Telescope.wf S n k a = true → Telescope.wf S n (k + a.length) b = true → Telescope.wf S n k (a ++ b) = true
  | k, [], b, _, hb => by simpa using hb
  | k, x :: a, b, ha, hb => by
    simp only [Telescope.wf, List.cons_append, Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1, Telescope.wf_append ha.2 (by
      rw [show k + 1 + a.length = k + (x :: a).length by simp; omega]; exact hb)⟩

theorem fnHead_noInt {names : List String} {st : TopState} {f : Fn} (hst : TopWf st)
    (hok : f.shaped = true) :
    NoInt (fnHead names st f) (fun r => TopWf r.1 ∧ r.1.sc = st.sc ∧ FnHeadOk st.sc.sigs st.sc.Γ.length r.2 ∧
      r.2.fn.name = f.name.name) := by
  simp only [Fn.shaped, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hok
  obtain ⟨hne, hbody⟩ := hok
  unfold fnHead
  dsimp only
  refine NoInt.bind (header_noInt (hst.ok.ctx rfl))
    fun ⟨ps, rs⟩ ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, q1, q2, q3⟩ => ?_
  simp only at r1 r2 r3 r4 r5 r6 r7 r8 r9 q1 q2 q3
  try simp only [List.length_map] at r4 r8 r9
  refine NoInt.bind (topLevel_noInt (k := 0) (Telescope.wf_append r6 (by simpa using r7))) fun _ _ => NoInt.pure ?_
  have hsig : Telescope.wf st.sc.sigs st.sc.Γ.length 0 ps.tele = true ∧
      Telescope.wf st.sc.sigs st.sc.Γ.length ps.tele.length rs.tele = true ∧
      (f.header.params.map (·.subterm)).length = ps.tele.length ∧ rs.tele ≠ [] :=
    ⟨r6, r7, by simp [r4], fun h => hne (List.eq_nil_of_length_eq_zero (by rw [← r5, h]; rfl))⟩
  refine ⟨⟨⟨hst.ok.Γ, hst.ok.sigs, hst.ok.names,
    hst.ok.globals.fnSig hsig⟩, hst.typeSig, hst.goal⟩, rfl, ?_, rfl⟩
  refine ⟨q2 ▸ q1.Γ, q2 ▸ q1.sigs, q2 ▸ q1.names, q2, (by show st.sc.Γ.length ≤ ps.sc.Γ.length; omega),
    r6, r7, hsig.2.2.1, hsig.2.2.2, fun u hu => ?_, by simp [r8, r4], hbody⟩
  simp only [List.mem_map, r8, List.mem_range'_1] at hu
  obtain ⟨i, hi, rfl⟩ := hu
  simp [Term.wf, r9]; omega

theorem GlobOk.set {gs : List Global} {S : Sigs} {n : Nat} {heads : List FnHead} {taint : List Bool}
    (h : GlobOk gs S n) (hh : ∀ hd ∈ heads, Telescope.wf S n 0 hd.sig.params = true ∧
      Telescope.wf S n hd.sig.params.length hd.sig.returns = true ∧ hd.sig.subterm.length = hd.sig.params.length ∧
      hd.sig.returns ≠ []) : GlobOk (Pledge.setSigs gs heads taint) S n := by
  intro g hg
  unfold Pledge.setSigs at hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
  have := h g0 hg0
  cases g0 with
  | fn nm s =>
    dsimp only
    cases hf : List.find? (fun x => x.fst.fn.name == nm) (heads.zip taint) with
    | none => exact this
    | some p =>
      obtain ⟨hd, t⟩ := p
      exact hh hd (List.of_mem_zip (List.mem_of_find?_eq_some hf)).1
  | type => exact this
  | ctor => exact this

theorem FnHeadOk.scOk {S : Sigs} {n : Nat} {hd : FnHead} {C : Ctx} (h : FnHeadOk S n hd)
    (hg : GlobOk C.globals S n) : ScOk C hd.sc :=
  ⟨h.sigs ▸ h.Γ, h.sigs ▸ h.sigsWf, h.sigs ▸ h.names, h.sigs ▸ hg.mono h.len⟩

theorem fnGroup_noInt {st : TopState} {fs : List Fn} (hst : TopWf st) (hok : ∀ f ∈ fs, f.shaped = true) :
    NoInt (fnGroup st fs) (TopWf) := by
  unfold fnGroup
  dsimp only
  refine NoInt.bind (NoInt.foldlM (I := fun s => TopWf s ∧ s.sc = st.sc) ⟨hst, rfl⟩
    fun s ⟨h1, h2⟩ f _ => NoInt.bind fresh_noInt fun _ _ => NoInt.pure ⟨⟨⟨
      h1.ok.Γ, h1.ok.sigs, h1.ok.names, fun g hg => ?_⟩, h1.typeSig, h1.goal⟩, h2⟩) fun st0 ⟨s1, s2⟩ => ?_
  · rcases List.mem_append.1 hg with hg | hg
    · exact h1.ok.globals g hg
    · simp only [List.mem_singleton] at hg; subst hg; trivial
  refine NoInt.bind (NoInt.foldlM_pre (I := fun _ p => TopWf p.1 ∧ p.1.sc = st.sc ∧
    ∀ hd ∈ p.2, FnHeadOk st.sc.sigs st.sc.Γ.length hd) (L := fs) (fun _ f p hf hI => ?_) fs [] (st0, [])
    (fun _ h => h) ⟨s1, s2, by simp⟩) fun r hr => ?_
  · obtain ⟨h1, h2, h3⟩ := hI
    obtain ⟨s, hs⟩ := p
    simp only at h1 h2 h3 ⊢
    refine NoInt.bind (fnHead_noInt h1 (hok f hf)) fun ⟨s', hd⟩ ⟨e1, e2, e3, e4⟩ => NoInt.pure ⟨e1, e2.trans h2, ?_⟩
    simp only at e1 e2 e3 e4 ⊢
    intro hd' hm
    rcases List.mem_append.1 hm with hm | hm
    · exact h3 hd' hm
    · simp only [List.mem_singleton] at hm; subst hm; rw [← h2]; exact e3
  obtain ⟨st1, heads⟩ := r
  obtain ⟨t1, t2, t3⟩ := hr
  simp only at t1 t2 t3 ⊢
  have hsigs : ∀ hd ∈ heads, Telescope.wf st.sc.sigs st.sc.Γ.length 0 hd.sig.params = true ∧
      Telescope.wf st.sc.sigs st.sc.Γ.length hd.sig.params.length hd.sig.returns = true ∧
      hd.sig.subterm.length = hd.sig.params.length ∧ hd.sig.returns ≠ [] :=
    fun hd hm => ⟨(t3 hd hm).params, (t3 hd hm).returns, (t3 hd hm).subterm, (t3 hd hm).ne⟩
  have hglob : ∀ taint, GlobOk (setSigs st1.globals heads taint) st.sc.sigs st.sc.Γ.length := fun taint =>
    (t2 ▸ t1.ok.globals).set hsigs
  refine NoInt.bind (fixTaint_noInt (fun taint => checkAll_noInt fun hd hm => ?_) _ _ rfl) fun _ _ => NoInt.pure ?_
  · have hok' := t3 hd hm
    have hsc := hok'.scOk (C := { st.ctx true with globals := setSigs st1.globals heads taint, fn := some hd.fn })
      (hglob taint)
    refine NoInt.imp (Expr.noInt _ _ _ _ hsc hok'.body fun g hg => ?_) fun _ _ => trivial
    cases hg
    rw [hok'.sigs]
    have hret : Telescope.wf st.sc.sigs hd.sc.Γ.length hd.env.length hd.sig.returns = true := by
      rw [hok'.envLen]; exact Telescope.wf_mono (fun _ _ h => h) hok'.len hok'.returns
    refine ⟨fun _ => hok'.env, fun _ => Wants.wf_of_tele (tele := hd.sig.returns) hret (by simp [returnsGiven])
      fun j w b hw hb => ?_, fun _ => ⟨by simpa [returnsGiven] using hok'.ne, fun w hw => ?_⟩⟩
    · simp only [returnsGiven, List.getElem?_map, hb, Option.map_some, Option.some.injEq] at hw
      subst hw; exact ⟨rfl, rfl⟩
    · simp only [returnsGiven, List.mem_map] at hw
      obtain ⟨b, -, rfl⟩ := hw; rfl
  · rw [← t2] at hglob
    exact ⟨⟨t1.ok.Γ, t1.ok.sigs, t1.ok.names, hglob _⟩, t1.typeSig, t1.goal⟩

/-- The error a `comptime` pattern `let C(...) = rhs;` meets at the state `st` when its right-hand side checks with
one untainted result whose checked tree evaluates to a run-time value `a` not headed by `C` (§11). -/
def HeadMiss (st : TopState) (pat : Pattern) (rhs : Expr) (e : CheckError) : Prop :=
  ∃ o r a, checkExpr st.ctx st.sc none rhs = .ok o ∧ single rhs.pos o.res = .ok r ∧ r.tainted = false ∧
    Eval st.prog st.env o.tree [a] ∧ a.headName ≠ pat.ctor.name ∧ e.pos = rhs.pos ∧
    e.msg () = s!"this evaluates to {code (showValue a)}, which is not headed by {code pat.ctor.name} (§11)"

/-- An error checking the item `t` at the state `st` may meet: not internal, and, if found by evaluating, the error
of a `comptime` pattern `let` whose value has another head (`HeadMiss`). -/
def TopErr (st : TopState) (t : Top) (e : CheckError) : Prop :=
  e.internal = false ∧
    (e.evaluated = true → ∃ p m pat rhs, t = .stmt (.patlet p true m pat rhs) ∧ HeadMiss st pat rhs e)

theorem TopErr.of {st : TopState} {t : Top} {e : CheckError} (h : e.internal = false ∧ e.evaluated = false) :
    TopErr st t e :=
  ⟨h.1, fun h' => by simp [h.2] at h'⟩

/-- A later top-level scope with the same signatures keeps `TopWf`. -/
theorem TopWf.scope {st : TopState} {sc : Scope} (hst : TopWf st) (h : ScOk st.ctx sc)
    (hs : sc.sigs = st.sc.sigs) (hl : st.sc.Γ.length ≤ sc.Γ.length) {st' : TopState}
    (h2 : st'.sc = sc) (h3 : st'.globals = st.globals) (h5 : st'.goal = st.goal) : TopWf st' := by
  refine ⟨?_, by rw [h2, hs]; exact hst.typeSig, fun g hg t ht => ?_⟩
  · rw [h2]; exact h.ctx (by simp [TopState.ctx, h3])
  · rw [h2, hs]; exact Term.wf_le hl (Nat.le_refl _) (hst.goal g (h5 ▸ hg) t ht)

theorem comptimeLet_noInt {st : TopState} {hw : st.Runs} {p : Pos} {m : Option Mult} {pat : Pattern}
    {rhs : Expr} (hst : TopWf st) (hI : TopOk st) (hok : rhs.shaped = true) :
    NoErr (TopErr st (.stmt (.patlet p true m pat rhs))) (comptimeLet st hw p m pat rhs) (TopWf) := by
  obtain ⟨ρ, hI⟩ := hI
  unfold comptimeLet
  dsimp only
  split
  · exact NoInt.weaken NoInt.failAt_bind fun _ => TopErr.of
  rename_i hm
  refine NoInt.bind (NoInt.weaken freshAll_noInt fun _ => TopErr.of) fun _ _ => ?_
  refine NoInt.bind (NoInt.weaken (NoInt.certify (Expr.noInt _ _ _ _ hst.ok hok (by simp))) fun _ => TopErr.of)
    fun ⟨o, ho₀⟩ ho => NoInt.keep ?_
  refine NoInt.bind (NoInt.weaken (NoInt.certify NoInt.single) fun _ => TopErr.of) fun ⟨r, hr₀⟩ hr => ?_
  simp only at ho hr ⊢
  have hrw : r.term.wf o.sc.sigs o.sc.Γ.length 0 = true := by
    rw [ho.sigs]; exact ho.res r (by rw [hr]; exact List.mem_cons_self)
  refine NoInt.bind (NoInt.weaken (NoInt.withEq (forcings_noInt ho.ok hrw)) fun _ => TopErr.of)
    fun fs ⟨hfs, f1, f2⟩ => ?_
  generalize hv : TopState.eval st o.tree r.tainted _ = v
  have pb := fun (k : Scope → CheckM TopState) (hk : ∀ sc', patBind o.sc r rhs.pos true pat fs = .ok sc' →
      ScOk st.ctx sc' ∧ sc'.sigs = st.sc.sigs ∧ st.sc.Γ.length ≤ sc'.Γ.length →
      NoErr (TopErr st (.stmt (.patlet p true m pat rhs))) (k sc') (TopWf)) =>
    NoInt.bind (NoInt.weaken (NoInt.withEq
      (patBind_noInt (r := r) (rhsPos := rhs.pos) (ct := true) ho.ok f1 (f2 pat List.mem_cons_self)))
        fun _ => TopErr.of)
      fun sc' ⟨hsc, h1, h2, h3⟩ => hk sc' hsc ⟨h1, h2.trans ho.sigs, Nat.le_trans ho.len h3⟩
  have tail : ∀ sc', ScOk st.ctx sc' ∧ sc'.sigs = st.sc.sigs ∧ st.sc.Γ.length ≤ sc'.Γ.length → ∀ env snaps,
      NoErr (TopErr st (.stmt (.patlet p true m pat rhs)))
        (pure ({ st with sc := sc', env := env, snaps := snaps } : TopState) : CheckM TopState) (TopWf) :=
    fun sc' ⟨h1, h2, h3⟩ env snaps => NoInt.pure (TopWf.scope hst h1 h2 h3 rfl rfl rfl)
  cases v with
  | none =>
    simp only
    refine pb _ fun sc' _ hsc' => ?_
    split
    · exact tail sc' hsc' _ _
    · exact tail sc' hsc' _ _
  | some v =>
    simp only
    obtain ⟨hrt, hev⟩ := TopState.eval_some hv
    split
    · rename_i hhead
      refine NoInt.bind (Q := fun _ => False) ⟨fun e he => ?_, fun _ he => by simp [evalFail_eq] at he⟩
        fun _ h => h.elim
      simp only [evalFail_eq, Except.error.injEq] at he
      subst he
      exact ⟨rfl, fun _ => ⟨p, m, pat, rhs, rfl, o, r, v, ho₀, hr₀, hrt, hev, by simpa using hhead, rfl, rfl⟩⟩
    · rename_i hhead
      refine pb _ fun sc' hsc hsc' => ?_
      split
      · exact tail sc' hsc' _ _
      · rename_i hts
        split
        · exact tail sc' hsc' _ _
        · rename_i hb
          obtain ⟨env, hb', -⟩ := comptimeLet_bound hI (by simpa using hm) ho₀ hr₀ hfs hsc (by simpa using hts) hev
            (by simpa using hhead)
          rw [hb'] at hb
          cases hb

theorem topStmt_noInt {st : TopState} {hw : st.Runs} {s : Stmt} (hst : TopWf st)
    (hok : s.shaped = true) : NoInt (topStmt st hw s) (TopWf) := by
  unfold topStmt
  refine NoInt.bind (NoInt.certify (Stmt.noInt s _ _ hst.ok hok))
    fun ⟨o, _⟩ ⟨h1, h2, h3⟩ => NoInt.pure (TopWf.scope hst h1 h2 h3 rfl rfl rfl)

theorem print_noInt {st : TopState} {hw : st.Runs} {p : Pos} {e : Expr} (hst : TopWf st)
    (hok : e.shaped = true) : NoInt (topItem st hw (.print p e)) (TopWf) := by
  unfold topItem
  refine NoInt.bind (NoInt.certify (NoInt.imp (Expr.noInt _ _ _ _ (hst.ok.ctx rfl) hok (by simp))
      fun o h => h.ctx (C' := st.ctx) rfl)) fun ⟨o, _⟩ ho => ?_
  refine NoInt.bind (NoInt.keep (NoInt.certify NoInt.single)) fun _ _ => NoInt.pure ?_
  exact TopWf.scope hst ho.ok ho.sigs ho.len rfl rfl rfl

theorem goal_noInt {st : TopState} {hw : st.Runs} {p : Pos} {g : Goal} (hst : TopWf st) :
    NoInt (topItem st hw (.goal p g)) (TopWf) := by
  unfold topItem
  dsimp only
  have fin : ∀ goal : CheckedGoal, (∀ t, goal.kind = .type t → t.wf st.sc.sigs st.sc.Γ.length 0 = true) →
      NoInt (pure ({ st with goal := some goal } : TopState) : CheckM TopState) (TopWf) := fun goal hg =>
    NoInt.pure ⟨hst.ok, hst.typeSig, fun g' hg' t ht => by cases hg'; exact hg t ht⟩
  split
  · exact NoInt.failAt_bind
  cases g with
  | fn h =>
    refine NoInt.bind (header_noInt (hst.ok.ctx rfl)) fun ⟨ps, rs⟩ ⟨_, _, _, _, _, r6, r7, _⟩ => ?_
    exact NoInt.bind (topLevel_noInt (k := 0) (Telescope.wf_append r6 (by simpa using r7))) fun _ _ =>
      fin _ fun t ht => by cases ht
  | type t =>
    refine NoInt.bind (annotate_noInt hst.ok)
      fun ⟨ty, is, tn⟩ ⟨h1, _⟩ => ?_
    exact NoInt.bind (NoInt.ensure (Term.entriesBelow_of_wf h1)) fun _ _ => fin _ fun t' ht => by
      cases ht; exact h1

theorem qedFnGoal_noInt {st : TopState} {ps rs : Telescope} {e : Expr} (hst : TopWf st) :
    NoInt (qedFnGoal st ps rs e) (TopWf) := by
  unfold qedFnGoal
  dsimp only
  repeat (first
    | exact NoInt.failAt
    | exact NoInt.failAt_bind
    | exact NoInt.pure ⟨hst.ok, hst.typeSig, hst.goal⟩
    | split)

theorem qed_noInt {st : TopState} {hw : st.Runs} {p : Pos} {e : Expr} (hst : TopWf st)
    (hok : e.shaped = true) : NoInt (topItem st hw (.qed p e)) (TopWf) := by
  unfold topItem
  dsimp only
  have fin : ∀ st' : TopState, TopWf st' → ∀ b : Bool,
      NoInt (pure ({ st' with qedChecks := true, proved := b } : TopState) : CheckM TopState) (TopWf) :=
    fun st' h b => NoInt.pure ⟨h.ok, h.typeSig, h.goal⟩
  split
  · exact NoInt.failAt_bind
  split
  · rename_i goal hgoal
    split
    · exact NoInt.bind (qedFnGoal_noInt hst) fun st' h' => fin st' h' _
    · rename_i t hk
      have hgiven : GivenOk st.sc.sigs st.sc.Γ.length goal.given := by
        have ht := hst.goal goal hgoal t hk
        simp only [CheckedGoal.given, hk]
        refine ⟨fun _ => by simp, fun _ j w hj => ?_, fun _ => ⟨by simp, by simp⟩⟩
        cases j with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj; exact
            ⟨fun t' h => by cases h; simpa using ht, fun e h => by cases h⟩
        | succ => simp at hj
      have hc := Expr.noInt e st.ctx st.sc (some goal.given) hst.ok hok fun g h => by
          simp only [Option.some.injEq] at h; subst h; exact hgiven
      let mk (o : Out) : TopState :=
        { st with sc := o.sc, proved := !o.res.any (·.tainted), snaps := st.snaps ++ o.snaps }
      repeat (first
        | exact NoInt.failAt_bind
        | exact NoInt.bind hc fun o ho => fin (mk o) (TopWf.scope hst ho.ok ho.sigs ho.len rfl rfl rfl) _
        | split)
  · exact NoInt.failAt

/-- A top-level item as the internal-check proof needs it (`Expr.shaped`, `Data.shaped`, `Fn.shaped`). -/
def Top.shaped : Top → Bool
  | .data d => d.shaped
  | .mutualData _ ds => ds.all (·.shaped)
  | .fn f => f.shaped
  | .mutualFn _ fs => fs.all (·.shaped)
  | .stmt (.patlet _ true _ _ rhs) => rhs.shaped
  | .stmt s => s.shaped
  | .print _ e | .qed _ e => e.shaped
  | .goal _ _ => true

theorem topItem_noInt {st : TopState} {hw : st.Runs} {t : Top} (hst : TopWf st) (hI : TopOk st)
    (hok : t.shaped = true) : NoErr (TopErr st t) (topItem st hw t) (TopWf) := by
  have w {x : CheckM TopState} (h : NoInt x TopWf) : NoErr (TopErr st t) x TopWf := NoInt.weaken h fun _ => TopErr.of
  match t, hok with
  | .data d, hok => unfold topItem; exact w (dataGroup_noInt hst (by simpa [Top.shaped] using hok))
  | .mutualData _ ds, hok =>
    unfold topItem; exact w (dataGroup_noInt hst (by simpa [Top.shaped, List.all_eq_true] using hok))
  | .fn f, hok => unfold topItem; exact w (fnGroup_noInt hst (by simpa [Top.shaped] using hok))
  | .mutualFn _ fs, hok =>
    unfold topItem; exact w (fnGroup_noInt hst (by simpa [Top.shaped, List.all_eq_true] using hok))
  | .stmt (.patlet p true m pat rhs), hok =>
    unfold topItem; exact comptimeLet_noInt hst hI (by simpa [Top.shaped] using hok)
  | .stmt (.patlet p false m pat rhs), hok =>
    unfold topItem; exact w (topStmt_noInt hst (by simpa [Top.shaped] using hok))
  | .stmt (.let p bs rhs), hok => unfold topItem; exact w (topStmt_noInt hst (by simpa [Top.shaped] using hok))
  | .stmt (.inspect p), hok => unfold topItem; exact w (topStmt_noInt hst (by simpa [Top.shaped] using hok))
  | .print p e, hok => exact w (print_noInt hst (by simpa [Top.shaped] using hok))
  | .goal p g, _ => exact w (goal_noInt hst)
  | .qed p e, hok => exact w (qed_noInt hst (by simpa [Top.shaped] using hok))

theorem topItems_wf : ∀ (prog : Program) (st : TopState) (h : TopOk st), TopWf st →
    (∀ t ∈ prog, t.shaped = true) → (topItems st h prog).2 = none → TopWf (topItems st h prog).1
  | [], _, _, hst, _, _ => hst
  | t :: ts, st, h, hst, hok, hn => by
    rcases hc : certify (topItem st h.runs t) with e | ⟨st', ht⟩ <;> simp only [topItems, hc] at hn ⊢
    · simp at hn
    · exact topItems_wf ts st' _ ((topItem_noInt hst h (hok t List.mem_cons_self)).2 _ ht)
        (fun t h => hok t (List.mem_cons_of_mem _ h)) hn

theorem TopWf.init (phase : Nat) (table : Table) : TopWf (TopState.init phase table) := by
  have hT : Sigs.find [⟨.Type, [], .TYPE⟩] Head.Type = some ⟨.Type, [], .TYPE⟩ := by simp [Sigs.find]
  refine ⟨⟨fun i en h => by simp [TopState.init] at h, fun sig hs => ?_,
    fun p hp => by simp [TopState.init] at hp, fun g hg => ?_⟩, ⟨_, hT, rfl⟩, fun g h => by simp [TopState.init] at h⟩
  · simp only [TopState.init, List.mem_singleton] at hs; subst hs
    simp only [Sig.wf, Telescope.wf, Bool.true_and]
    exact Term.wf_app.2 ⟨⟨_, hT, rfl⟩, by simp⟩
  · simp only [TopState.ctx, TopState.init, List.mem_singleton] at hg; subst hg
    exact ⟨⟨_, hT⟩, fun cs h => by cases h⟩

/-- Where checking stops at an error, on a program meeting `Top.shaped`: at an item `t` after items `pre` at which it
stops at no error, with an error that `t` may meet at the state they leave (`TopErr`). -/
theorem checkItems_stop (phase : Nat) (table : Table) (prog : Program) (hok : ∀ t ∈ prog, t.shaped = true)
    {e : CheckError} {t : Top} {n : Nat} (h : (checkItems phase table prog).2 = some (e, t, n)) :
    ∃ pre post, prog = pre ++ t :: post ∧ (checkItems phase table pre).2 = none ∧
      TopErr (checkItems phase table pre).1 t e := by
  obtain ⟨pre, post, rfl, -, hn, ⟨hw, he⟩, -⟩ := topItems_stopAt h
  have hpre : ∀ t ∈ pre, t.shaped = true := fun t ht => hok t (List.mem_append_left _ ht)
  exact ⟨pre, post, rfl, hn, (topItem_noInt (hw := hw) (topItems_wf pre _ _ (TopWf.init phase table) hpre hn)
    (topItems_ok _ pre) (hok t (by simp))).1 e he⟩

/-- On a program meeting `Top.shaped`, with any table, an error found by evaluating (`CheckError.evaluated`) at which
checking stops is met by a `comptime` pattern `let C(...) = rhs;` at the state the items before it leave: its
right-hand side checks with one untainted result whose checked tree evaluates to a run-time value not headed by `C`,
and the error is the one that shows that value (§11). -/
theorem checkItems_evaluated (phase : Nat) (table : Table) (prog : Program) (hok : ∀ t ∈ prog, t.shaped = true)
    {e : CheckError} {t : Top} {n : Nat} (h : (checkItems phase table prog).2 = some (e, t, n))
    (hev : e.evaluated = true) :
    ∃ pre post p m pat rhs, prog = pre ++ t :: post ∧ (checkItems phase table pre).2 = none ∧
      t = .stmt (.patlet p true m pat rhs) ∧ HeadMiss (checkItems phase table pre).1 pat rhs e := by
  obtain ⟨pre, post, hp, hn, -, hm⟩ := checkItems_stop phase table prog hok h
  obtain ⟨p, m, pat, rhs, ht, hh⟩ := hm hev
  exact ⟨pre, post, p, m, pat, rhs, hp, hn, ht, hh⟩

/-- Checking a program with any table reports no internal error, when the program has no `removed` node, no
`comptime` below the top level, no type or value constructor named `sorry`, and the grammar's non-empty lists
(`Top.shaped`). -/
theorem checkItems_noInternal (phase : Nat) (table : Table) (prog : Program)
    (hok : ∀ t ∈ prog, t.shaped = true) :
    ∀ e t n, (checkItems phase table prog).2 = some (e, t, n) → e.internal = false :=
  fun _ _ _ h => by obtain ⟨-, -, -, -, hi, -⟩ := checkItems_stop phase table prog hok h; exact hi

/-- `checkItems_noInternal` for what `runProgramWith` reports: an error it reports with no syntax error is that of an
item, and is not internal. -/
theorem runProgramWith_noInternal (phase : Nat) (table : Table) (prog : Program) (has : String → Bool)
    (hok : ∀ t ∈ prog, t.shaped = true) {err : Pos × String}
    (h : (runProgramWith phase table prog has).error = some err) :
    ∃ e t n, (checkItems phase table prog).2 = some (e, t, n) ∧ err = (e.pos, e.msg ()) ∧ e.internal = false := by
  simp only [runProgramWith, outcome] at h
  cases hc : (checkItems phase table prog).2 with
  | none => simp [hc] at h
  | some et =>
    obtain ⟨e, t, n⟩ := et
    simp only [hc, Option.map_some, Option.orElse_some, Option.some.injEq] at h
    exact ⟨e, t, n, rfl, h.symm, checkItems_noInternal phase table prog hok e t n hc⟩

/-- The error `runProgram` reports for an item, which it reports whatever the syntax error, is not internal: the
checking pass's, by `checkItems_noInternal`, or one the solver meets that is not internal (`report`). -/
theorem runProgram_noInternal (phase : Nat) (prog : Program) (has : String → Bool) (err : Option (Pos × String))
    (hok : ∀ t ∈ prog, t.shaped = true) :
    ∀ e t n, (checkItems phase (solution phase prog) prog).2.map
        (report (checkItems phase (solution phase prog) prog).1) = some (e, t, n) →
      e.internal = false ∧ (runProgram phase prog has err).error = some (e.pos, e.msg ()) := by
  intro e t n h
  cases hc : (checkItems phase (solution phase prog) prog).2 with
  | none => simp [hc] at h
  | some s =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    refine ⟨?_, by simp [runProgram, outcome, hc, h]⟩
    have hi := checkItems_noInternal phase (solution phase prog) prog hok s.1 s.2.1 s.2.2 hc
    obtain ⟨-, hr⟩ := report_spec (checkItems phase (solution phase prog) prog).1 s
    rw [h] at hr
    rcases hr with hr | ⟨-, hr, -⟩
    · simp only at hr; rw [hr]; exact hi
    · exact hr

end Pledge
