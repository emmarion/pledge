import Pledge.Sound.Expr

namespace Pledge

theorem foldlM_induct {α β ε : Type} {f : β → α → Except ε β} (P : List α → β → Prop) :
    ∀ (l pre : List α) {b r : β}, (∀ q x b b', x ∈ l → P q b → f b x = .ok b' → P (q ++ [x]) b') →
      P pre b → l.foldlM f b = .ok r → P (pre ++ l) r
  | [], pre, b, r, _, hb, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simpa using hb
  | a :: l, pre, b, r, hf, hb, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨b', hb', h⟩ := bind_eq_ok.1 h
    have := foldlM_induct P l (pre ++ [a]) (fun q x b b' hx => hf q x b b' (List.mem_cons_of_mem _ hx))
      (hf pre a b b' List.mem_cons_self hb hb') h
    simpa using this

/-- The value constructors of `cs` that the type constructor `T` owns. -/
def ownedBy (cs : List (String × String)) (T : String) : List String := (cs.filter (·.1 == T)).map (·.2)

/-- The globals a group of `data` declarations adds: its type constructors `ts`, each with the value constructors
of `cs` it owns, then those value constructors. -/
def groupGlobals (ts : List String) (cs : List (String × String)) (done : Bool) : List Global :=
  ts.map (fun T => .type T (some (ownedBy cs T)) done) ++ cs.map (fun p => .ctor p.2)

/-- A state reached while checking a group of `data` declarations from `st`: the type constructors `ts` and value
constructors `cs` (each with its owner) declared so far, with their fresh names and their signatures `new`. -/
structure Group (st : TopState) (ts : List String) (cs : List (String × String)) (new : Sigs) (done : Bool)
    (s : TopState) : Prop where
  eq : s = { st with sc := { st.sc with sigs := st.sc.sigs ++ new }, globals := st.globals ++ groupGlobals ts cs done }
  nodup : (ts ++ cs.map (·.2)).Nodup
  fresh : ∀ n ∈ ts ++ cs.map (·.2), ∀ g ∈ st.globals, g.name ≠ n
  owners : ∀ p ∈ cs, p.1 ∈ ts
  sigsOk : SigsOk st.sc.Γ.length new
  sigs : ∀ sig ∈ new, (∃ T ∈ ts, sig.head = ⟨.type, T⟩ ∧ sig.ret = .TYPE) ∨
    (∃ p ∈ cs, sig.head = ⟨.ctor, p.2⟩ ∧ ∃ args, sig.ret = .app ⟨.type, p.1⟩ args)
  types : ∀ T ∈ ts, ∃ sig ∈ new, sig.head = ⟨.type, T⟩
  ctors : ∀ p ∈ cs, ∃ sig ∈ new, sig.head = ⟨.ctor, p.2⟩

theorem find?_old {gs X : List Global} {p : Global → Bool} {g : Global} (h : gs.find? p = some g) :
    (gs ++ X).find? p = some g := by
  simp [List.find?_append, h]

theorem find?_fresh {gs X : List Global} {n : String} (h : ∀ g ∈ gs, g.name ≠ n) :
    (gs ++ X).find? (·.name == n) = X.find? (·.name == n) := by
  rw [List.find?_append, List.find?_eq_none.2 (fun g hg => by simpa using h g hg)]
  simp

theorem groupGlobals_type {ts : List String} {cs : List (String × String)} {done : Bool} {T : String}
    (hT : T ∈ ts) : (groupGlobals ts cs done).find? (·.name == T) = some (.type T (some (ownedBy cs T)) done) := by
  rw [groupGlobals, List.find?_append]
  have : (ts.map (fun T => Global.type T (some (ownedBy cs T)) done)).find? (·.name == T) =
      some (.type T (some (ownedBy cs T)) done) := by
    induction ts with
    | nil => cases hT
    | cons a ts ih =>
      by_cases ha : a = T
      · subst ha; simp [Global.name]
      · have hT' : T ∈ ts := by
          rcases List.mem_cons.1 hT with h | h
          · exact absurd h.symm ha
          · exact h
        rw [List.map_cons, List.find?_cons, show ((Global.type a (some (ownedBy cs a)) done).name == T) = false by
          simp [Global.name, ha]]
        exact ih hT'
  rw [this]; rfl

theorem groupGlobals_ctor {ts : List String} {cs : List (String × String)} {done : Bool} {p : String × String}
    (hp : p ∈ cs) (hn : p.2 ∉ ts) : (groupGlobals ts cs done).find? (·.name == p.2) = some (.ctor p.2) := by
  rw [groupGlobals, List.find?_append, List.find?_eq_none.2 (by simp [Global.name]; exact fun T hT h => hn (h ▸ hT))]
  simp only [Option.none_or]
  induction cs with
  | nil => cases hp
  | cons a cs ih =>
    by_cases ha : a.2 = p.2
    · simp [Global.name, ha]
    · have hp' : p ∈ cs := by
        rcases List.mem_cons.1 hp with h | h
        · exact absurd (h ▸ rfl) ha
        · exact h
      rw [List.map_cons, List.find?_cons, show ((Global.ctor a.2).name == p.2) = false by simp [Global.name, ha]]
      exact ih hp'

theorem groupGlobals_find? {ts : List String} {cs : List (String × String)} {done : Bool} {n : String} {g : Global}
    (h : (groupGlobals ts cs done).find? (·.name == n) = some g) :
    (n ∈ ts ∧ g = .type n (some (ownedBy cs n)) done) ∨ (∃ p ∈ cs, p.2 = n ∧ g = .ctor n) := by
  have hm := List.mem_of_find?_eq_some h
  have hn : g.name = n := by simpa using List.find?_some h
  simp only [groupGlobals, List.mem_append, List.mem_map] at hm
  rcases hm with ⟨T, hT, rfl⟩ | ⟨p, hp, rfl⟩
  · simp only [Global.name] at hn; subst hn; exact .inl ⟨hT, rfl⟩
  · simp only [Global.name] at hn; exact .inr ⟨p, hp, hn, by rw [hn]⟩

theorem fresh_ok {C : Ctx} {sc : Scope} {seen : List String} {n : String} {pos : Pos} {r : List String}
    (h : fresh C sc seen (some n) pos = .ok r) : C.global n = none := by
  simp only [fresh] at h
  split at h
  · simp [failAt_eq] at h
  · split at h
    · simp [failAt_eq] at h
    · rename_i hn; simp at hn; exact hn.2

theorem topLevel_ok {st : TopState} {pos : Pos} {tele : Telescope} {u : Unit} (h : topLevel st pos tele = .ok u) :
    ∀ b ∈ tele, b.entriesBelow st.sc.Γ.length = true := by
  simpa using ensure_ok h

theorem TopState.ctx_global (st : TopState) (inDecl : Bool) (n : String) :
    (st.ctx inDecl).global n = st.globals.find? (·.name == n) := rfl

theorem Group.global_none {st s : TopState} {ts : List String} {cs : List (String × String)} {new : Sigs}
    {done : Bool} (hg : Group st ts cs new done s) {n : String} (h : s.globals.find? (·.name == n) = none) :
    (∀ g ∈ st.globals, g.name ≠ n) ∧ n ∉ ts ∧ n ∉ cs.map (·.2) := by
  rw [hg.eq] at h
  have h' := List.find?_eq_none.1 h
  simp only [List.mem_append, beq_iff_eq] at h'
  refine ⟨fun g hg hn => h' g (.inl hg) hn, fun hT => ?_, fun hc => ?_⟩
  · exact h' _ (.inr (by simp [groupGlobals]; exact .inl ⟨n, hT, rfl⟩)) rfl
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
    exact h' _ (.inr (by simp [groupGlobals]; exact .inr ⟨p.1, p.2, hp, rfl⟩)) rfl

theorem declType_group {st s s' : TopState} {ts : List String} {new : Sigs} {d : Data}
    (hg : Group st ts [] new false s) (h : declType s d = .ok s') :
    ∃ sig, Group st (ts ++ [d.name.name]) [] (new ++ [sig]) false s' := by
  unfold declType at h
  obtain ⟨_, hf, h⟩ := bind_eq_ok.1 h
  obtain ⟨ps, hps, h⟩ := bind_eq_ok.1 h
  obtain ⟨_, htl, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hfr, hts, -⟩ := hg.global_none (by simpa [TopState.ctx_global] using fresh_ok hf)
  have hbelow := topLevel_ok htl
  obtain ⟨heq, hnd, hfresh, -, hok, hsigs, htypes, -⟩ := hg
  subst heq
  refine ⟨⟨⟨.type, d.name.name⟩, ps.tele, .TYPE⟩, ⟨?_, ?_, ?_, by simp, ?_, ?_, ?_, by simp⟩⟩
  · simp [addSig, groupGlobals, ownedBy]
  · simp only [List.map_nil, List.append_nil] at hnd ⊢
    refine List.nodup_append.2 ⟨hnd, by simp, fun a ha b hb hab => hts ?_⟩
    simp only [List.mem_singleton] at hb
    exact hb ▸ hab ▸ ha
  · intro n hn g hg'
    simp only [List.map_nil, List.append_nil, List.mem_append, List.mem_singleton] at hn
    rcases hn with hn | rfl
    · exact hfresh n (by simpa using hn) g hg'
    · exact hfr g hg'
  · intro sig hs
    rcases List.mem_append.1 hs with hs | hs
    · exact hok sig hs
    · simp only [List.mem_singleton] at hs
      subst hs
      refine ⟨?_, by simp [Term.TYPE, Term.boundsBelow, Term.boundsBelowList]⟩
      simp only [Sig.entriesBelow, Bool.and_eq_true, List.all_eq_true]
      exact ⟨hbelow, by simp [Term.TYPE, Term.entriesBelow, Term.entriesBelowList]⟩
  · intro sig hs
    rcases List.mem_append.1 hs with hs | hs
    · rcases hsigs sig hs with ⟨T, hT, h1, h2⟩ | ⟨p, hp, -⟩
      · exact .inl ⟨T, List.mem_append_left _ hT, h1, h2⟩
      · cases hp
    · simp only [List.mem_singleton] at hs
      subst hs
      exact .inl ⟨d.name.name, by simp, rfl, rfl⟩
  · intro T hT
    rcases List.mem_append.1 hT with hT | hT
    · obtain ⟨sig, hs, h⟩ := htypes T hT
      exact ⟨sig, List.mem_append_left _ hs, h⟩
    · simp only [List.mem_singleton] at hT
      subst hT
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

theorem abstractChecked_app {Γ : Entries} {hd : Head} {as : List Term} {ids : List Nat} {pos : Pos} {ret : Term}
    (h : abstractChecked Γ (.app hd as) ids pos = .ok ret) : ∃ args, ret = .app hd args := by
  unfold abstractChecked abstract? at h
  split at h
  · rename_i u hu
    split at hu
    · cases hu; cases h; exact ⟨_, rfl⟩
    · cases hu
  · simp [internal, failAt_eq] at h

theorem ownedBy_append (cs : List (String × String)) (T c T' : String) :
    ownedBy (cs ++ [(T, c)]) T' = if (T' == T) = true then ownedBy cs T' ++ [c] else ownedBy cs T' := by
  by_cases h : T' = T
  · subst h; simp [ownedBy]
  · have : (T == T') = false := by simpa using Ne.symm h
    simp [ownedBy, List.filter_append, h, this]

theorem map_owner {F : Global → Global} {gs : List Global} {ts : List String} {cs : List (String × String)}
    {T c : String} (h1 : ∀ g ∈ gs, F g = g)
    (h2 : ∀ T' X, F (.type T' (some X) false) = .type T' (some (if (T' == T) = true then X ++ [c] else X)) false)
    (h3 : ∀ n, F (.ctor n) = .ctor n) :
    (gs ++ groupGlobals ts cs false ++ [Global.ctor c]).map F = gs ++ groupGlobals ts (cs ++ [(T, c)]) false := by
  have hgs : gs.map F = gs := by
    conv => rhs; rw [← List.map_id gs]
    exact List.map_congr_left h1
  simp only [List.map_append, hgs, groupGlobals, List.map_map, Function.comp_def, h2, h3, List.map_cons,
    List.map_nil, ownedBy_append, List.append_assoc]

theorem declCtor_group {st s s' : TopState} {ts : List String} {cs : List (String × String)} {new : Sigs}
    {T : String} {k : Ctor} (hg : Group st ts cs new false s) (hT : T ∈ ts)
    (h : declCtor T s k = .ok s') : ∃ sig, Group st ts (cs ++ [(T, k.name.name)]) (new ++ [sig]) false s' := by
  unfold declCtor at h
  obtain ⟨_, hf, h⟩ := bind_eq_ok.1 h
  obtain ⟨fs, hfs, h⟩ := bind_eq_ok.1 h
  dsimp only at h
  obtain ⟨hd, args, hkr⟩ : ∃ hd args, k.ret = .app hd args := by
    cases hkr : k.ret with
    | var x => simp [hkr, failAt_eq, bind, Except.bind] at h
    | app hd args => exact ⟨hd, args, rfl⟩
  simp only [hkr] at h
  split at h
  rotate_left
  · simp [failAt_eq, bind, Except.bind] at h
  rename_i hc
  obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
  obtain ⟨ret, hret, h⟩ := bind_eq_ok.1 h
  obtain ⟨_, htl, h⟩ := bind_eq_ok.1 h
  obtain ⟨_, he, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  clear h
  have hn : hd.name = T := by simpa using hc
  subst hn
  obtain ⟨hfr, hts, hcs⟩ := hg.global_none (by simpa [TopState.ctx_global] using fresh_ok hf)
  have hglob : (s.ctx true).global hd.name = some (.type hd.name (some (ownedBy cs hd.name)) false) := by
    rw [TopState.ctx_global, hg.eq]
    exact (find?_fresh fun g hg' => hg.fresh _ (List.mem_append_left _ hT) g hg').trans (groupGlobals_type hT)
  unfold checkTerm at hr
  simp only [hglob] at hr
  obtain ⟨kind, hk, hr⟩ := bind_eq_ok.1 hr
  cases hk
  obtain ⟨sig, hsig, hr⟩ := bind_eq_ok.1 hr
  obtain ⟨_, -, hr⟩ := bind_eq_ok.1 hr
  obtain ⟨rs, -, hr⟩ := bind_eq_ok.1 hr
  simp only [pure, Except.pure, Except.ok.injEq] at hr
  subst hr
  rw [Sigs.find_head (Scope.sig_ok hsig)] at hret
  obtain ⟨args', rfl⟩ := abstractChecked_app hret
  have hbelow := topLevel_ok htl
  have hens := ensure_ok he
  obtain ⟨heq, hnd, hfresh, hown, hok, hsigs, htypes, hctors⟩ := hg
  subst heq
  refine ⟨⟨⟨.ctor, k.name.name⟩, fs.tele, .app ⟨.type, hd.name⟩ args'⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [addSig]
    rw [map_owner (T := hd.name) (c := k.name.name) (fun g hg' => ?h1) (fun _ _ => rfl) (fun _ => rfl)]
    · simp
    case h1 =>
      cases g with
      | type n cs' d =>
        cases cs' with
        | none => rfl
        | some cs' =>
          have : (n == hd.name) = false := by simpa [Global.name] using hfresh _ (List.mem_append_left _ hT) _ hg'
          simp [this]
      | _ => rfl
  · rw [List.map_append, ← List.append_assoc]
    refine List.nodup_append.2 ⟨hnd, by simp, fun a ha b hb hab => ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb hab
    rcases List.mem_append.1 ha with ha | ha
    · exact hts ha
    · exact hcs ha
  · intro n hn g hg'
    rw [List.map_append, ← List.append_assoc] at hn
    rcases List.mem_append.1 hn with hn | hn
    · exact hfresh n hn g hg'
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hn
      subst hn
      exact hfr g hg'
  · intro p hp'
    rcases List.mem_append.1 hp' with hp' | hp'
    · exact hown p hp'
    · simp only [List.mem_singleton] at hp'
      subst hp'
      exact hT
  · intro sig hs
    rcases List.mem_append.1 hs with hs | hs
    · exact hok sig hs
    · simp only [List.mem_singleton] at hs
      subst hs
      simp only [Bool.and_eq_true] at hens
      refine ⟨?_, hens.2⟩
      simp only [Sig.entriesBelow, Bool.and_eq_true, List.all_eq_true]
      exact ⟨hbelow, hens.1⟩
  · intro sig hs
    rcases List.mem_append.1 hs with hs | hs
    · rcases hsigs sig hs with h | ⟨p, hp', h⟩
      · exact .inl h
      · exact .inr ⟨p, List.mem_append_left _ hp', h⟩
    · simp only [List.mem_singleton] at hs
      subst hs
      exact .inr ⟨(hd.name, k.name.name), by simp, rfl, args', rfl⟩
  · exact fun T hT => let ⟨sig, hs, h⟩ := htypes T hT; ⟨sig, List.mem_append_left _ hs, h⟩
  · intro p hp'
    rcases List.mem_append.1 hp' with hp' | hp'
    · obtain ⟨sig, hs, h⟩ := hctors p hp'
      exact ⟨sig, List.mem_append_left _ hs, h⟩
    · simp only [List.mem_singleton] at hp'
      subst hp'
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

theorem map_done {F : Global → Global} {gs : List Global} {ts : List String} {cs : List (String × String)}
    (h1 : ∀ g ∈ gs, F g = g) (h2 : ∀ T ∈ ts, ∀ X, F (.type T X false) = .type T X true)
    (h3 : ∀ n, F (.ctor n) = .ctor n) : (gs ++ groupGlobals ts cs false).map F = gs ++ groupGlobals ts cs true := by
  have hgs : gs.map F = gs := by
    conv => rhs; rw [← List.map_id gs]
    exact List.map_congr_left h1
  simp only [List.map_append, hgs, groupGlobals, List.map_map, Function.comp_def, h3]
  congr 2
  exact List.map_congr_left fun T hT => h2 T hT _

/-- The value constructors a group of `data` declarations declares, each with its owner. -/
def groupCtors (ds : List Data) : List (String × String) := ds.flatMap fun d => d.ctors.map (d.name.name, ·.name.name)

/-- What checking a group of `data` declarations adds: `Group`, for all its type and value constructors. -/
theorem dataGroup_group {st st' : TopState} {ds : List Data}
    (h : dataGroup st ds = .ok st') : ∃ new, Group st (ds.map (·.name.name)) (groupCtors ds) new true st' := by
  unfold dataGroup at h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok.1 h
  obtain ⟨s2, h2, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have g0 : Group st [] [] [] false st :=
    ⟨by cases st; simp [groupGlobals], by simp, by simp, by simp, by simp [SigsOk], by simp, by simp, by simp⟩
  obtain ⟨new1, g1⟩ : ∃ new, Group st (ds.map (·.name.name)) [] new false s1 := by
    have := foldlM_induct (fun pre s => ∃ new, Group st (pre.map (·.name.name)) [] new false s) ds []
      (fun q x b b' hx ⟨new, hb⟩ hf => by
        obtain ⟨sig, hg⟩ := declType_group hb hf
        exact ⟨new ++ [sig], by simpa using hg⟩) ⟨[], g0⟩ h1
    simpa using this
  obtain ⟨new2, g2⟩ : ∃ new, Group st (ds.map (·.name.name)) (groupCtors ds) new false s2 := by
    have := foldlM_induct (fun pre s => ∃ new, Group st (ds.map (·.name.name)) (groupCtors pre) new false s) ds []
      (fun q x b b' hx ⟨new, hb⟩ hf => by
        have := foldlM_induct (fun kq s => ∃ new, Group st (ds.map (·.name.name))
            (groupCtors q ++ kq.map (x.name.name, ·.name.name)) new false s) x.ctors []
          (fun kq k c c' hk ⟨new, hc⟩ hf' => by
            obtain ⟨sig, hg⟩ := declCtor_group hc (List.mem_map_of_mem hx) hf'
            exact ⟨new ++ [sig], by simpa using hg⟩) ⟨new, by simpa using hb⟩ hf
        simpa [groupCtors] using this) ⟨new1, g1⟩ h2
    simpa using this
  obtain ⟨heq, hnd, hfresh, hown, hok, hsigs, htypes, hctors⟩ := g2
  subst heq
  refine ⟨new2, ⟨?_, hnd, hfresh, hown, hok, hsigs, htypes, hctors⟩⟩
  simp only
  rw [map_done (fun g hg => ?h1) (fun T hT X => ?h2) (fun _ => rfl)]
  case h1 =>
    cases g with
    | type n cs' d =>
      cases d with
      | true => rfl
      | false =>
        have : ∀ d ∈ ds, ¬ d.name.name = n := fun d hd hn =>
          hfresh n (List.mem_append_left _ (hn ▸ List.mem_map_of_mem hd)) _ hg rfl
        simpa using this
    | _ => rfl
  case h2 =>
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hT
    simpa using ⟨d, hd, rfl⟩

theorem kindOf_some {gs : List Global} {n : String} {k : HeadKind} (h : kindOf gs n = some k) :
    ∃ g, gs.find? (·.name == n) = some g := by
  cases hf : gs.find? (·.name == n) with
  | none => simp [kindOf, hf] at h
  | some g => exact ⟨g, rfl⟩

theorem Sigs.find_append_old {S S' : Sigs} {h : Head} {s : Sig} (hs : S.find h = some s) :
    (S ++ S').find h = some s := by
  simp only [Sigs.find, List.find?_append] at hs ⊢
  simp [hs]

theorem Sigs.find_append_new {S S' : Sigs} {h : Head} {s : Sig} (hn : S.find h = none)
    (hs : (S ++ S').find h = some s) : s ∈ S' := by
  simp only [Sigs.find, List.find?_append] at hn hs
  rw [hn, Option.none_or] at hs
  exact List.mem_of_find?_eq_some hs

theorem Sigs.find_of_mem {S : Sigs} {s : Sig} {h : Head} (hs : s ∈ S) (hh : s.head = h) : ∃ s', S.find h = some s' :=
  Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨s, hs, by simp [hh]⟩)

theorem Sigs.sub_append_close (S S' : Sigs) (ρ : List Value) :
    Sigs.Sub (S.map (Sig.close ρ)) ((S ++ S').map (Sig.close ρ)) := fun _ _ hs => by
  rw [List.map_append]; exact Sigs.find_append_old hs

theorem Sig.close_ret_head {s : Sig} {ρ env ws : List Value} {hd hd' : Head} {args : List Term} {us : List Value}
    (h : s.ret = .app hd args) (hr : (s.close ρ).ret.eval env ws = some (.app hd' us)) : hd' = hd := by
  simp only [Sig.close, h, Term.close] at hr
  obtain ⟨vs, -, he⟩ := Term.eval_app.1 hr
  exact (Value.app.inj he).1

section
variable {st st' : TopState} {ρ : List Value} {ts : List String} {cs : List (String × String)} {new : Sigs}
  {done : Bool}

theorem Group.names_fresh (hg : Group st ts cs new done st') {n : String} (hn : n ∈ ts ++ cs.map (·.2)) :
    st.globals.find? (·.name == n) = none :=
  List.find?_eq_none.2 fun g hg' => by simpa using hg.fresh n hn g hg'

theorem Group.find?_old (hg : Group st ts cs new done st') {p : Global → Bool} {g : Global}
    (h : st.globals.find? p = some g) : st'.globals.find? p = some g := by
  rw [hg.eq]; exact Pledge.find?_old h

theorem Group.kindOf_old (hg : Group st ts cs new done st') {n : String} {k : HeadKind}
    (h : kindOf st.globals n = some k) : kindOf st'.globals n = some k := by
  obtain ⟨g, hgn⟩ := kindOf_some h
  unfold kindOf at h ⊢
  rw [hg.find?_old hgn]; rwa [hgn] at h

theorem Group.find?_type (hg : Group st ts cs new done st') {T : String} (hT : T ∈ ts) :
    st'.globals.find? (·.name == T) = some (.type T (some (ownedBy cs T)) done) := by
  rw [hg.eq]
  exact (find?_fresh fun g hg' => hg.fresh T (List.mem_append_left _ hT) g hg').trans (groupGlobals_type hT)

theorem Group.find?_ctor (hg : Group st ts cs new done st') {p : String × String} (hp : p ∈ cs) :
    st'.globals.find? (·.name == p.2) = some (.ctor p.2) := by
  have hm : p.2 ∈ cs.map (·.2) := List.mem_map_of_mem hp
  rw [hg.eq]
  refine (find?_fresh fun g hg' => hg.fresh _ (List.mem_append_right _ hm) g hg').trans (groupGlobals_ctor hp ?_)
  exact fun hT => (List.nodup_append.1 hg.nodup).2.2 _ hT _ hm rfl

theorem Group.sig_none (hI : TopInv st ρ) (hg : Group st ts cs new done st') {n : String}
    (hn : n ∈ ts ++ cs.map (·.2)) (k : HeadKind) : st.sc.sigs.find ⟨k, n⟩ = none := by
  cases hf : st.sc.sigs.find ⟨k, n⟩ with
  | none => rfl
  | some s =>
    obtain ⟨g, hgn⟩ := kindOf_some (hI.sigNames _ _ hf)
    rw [hg.names_fresh hn] at hgn
    cases hgn

theorem Group.ne_Type (hI : TopInv st ρ) (hg : Group st ts cs new done st') {n : String}
    (hn : n ∈ ts ++ cs.map (·.2)) : n ≠ "Type" := by
  rintro rfl
  obtain ⟨s, hs⟩ := hI.typeSig
  rw [show Head.Type = ⟨.type, "Type"⟩ from rfl, hg.sig_none hI hn] at hs
  cases hs

theorem Group.fns_none (hI : TopInv st ρ) (hg : Group st ts cs new done st') {n : String}
    (hn : n ∈ ts ++ cs.map (·.2)) : st.fns.find n = none :=
  List.find?_eq_none.2 fun d hd hdn => by
    obtain ⟨sig, hs⟩ := hI.fnNames d hd
    exact hg.fresh n hn _ (List.mem_of_find?_eq_some hs) (by simpa [Global.name] using hdn)

theorem Group.sigs_eq (hg : Group st ts cs new done st') : st'.sc.sigs = st.sc.sigs ++ new := by rw [hg.eq]

theorem Group.world_Sc (hg : Group st ts cs new done st') :
    (st'.world ρ).Sc = (st.sc.sigs ++ new).map (Sig.close ρ) := by
  simp only [TopState.world, hg.sigs_eq]

theorem Group.le (hI : TopInv st ρ) (hg : Group st ts cs new true st') : (st.world ρ).Le (st'.world ρ) := by
  have hfns : st'.fns = st.fns := by rw [hg.eq]
  refine ⟨⟨fun n d h => by simpa [TopState.world, TopState.prog, hfns] using h,
    fun n k hf hk => ⟨by simpa [TopState.world, TopState.prog, hfns] using hf, hg.kindOf_old hk⟩⟩, ?_,
    List.prefix_refl _, ?_⟩
  · rw [hg.world_Sc]; exact Sigs.sub_append_close _ _ _
  · intro h sig' ws hd us hn hs hr
    rw [hg.world_Sc, List.map_append] at hs
    simp only [TopState.world, Sigs.find_map_close, Option.map_eq_none_iff] at hn
    have hm := Sigs.find_append_new (by simpa [Sigs.find_map_close] using hn) hs
    obtain ⟨s, hs', rfl⟩ := List.mem_map.1 hm
    rcases hg.sigs s hs' with ⟨T, -, -, hret⟩ | ⟨p, hp, -, args, hret⟩
    · obtain rfl := Sig.close_ret_head (hd := Head.Type) (args := []) hret hr
      exact ⟨rfl, .inl rfl⟩
    · obtain rfl := Sig.close_ret_head hret hr
      refine ⟨rfl, .inr ?_⟩
      simp [TopState.world, Sigs.find_map_close, hg.sig_none hI (List.mem_append_left _ (hg.owners p hp))]

theorem Group.complete (hI : TopInv st ρ) (hg : Group st ts cs new true st') {T : String} (hT : T ∈ ts) :
    Complete (st'.world ρ) T (ownedBy cs T) := by
  intro h sig' ws hd us hf hr hn
  rw [hg.world_Sc, Sigs.find_map_close] at hf
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 hf
  have hh := Sigs.find_head hs
  cases ho : st.sc.sigs.find h with
  | some s0 =>
    rw [Sigs.find_append_old ho] at hs
    cases hs
    obtain ⟨hd0, args, hret, -, s1, hs1⟩ := hI.rets _ (List.mem_of_find?_eq_some ho)
    obtain rfl := Sig.close_ret_head hret hr
    have := hg.sig_none hI (List.mem_append_left _ hT) hd.kind
    rw [← hn] at this
    rw [this] at hs1
    cases hs1
  | none =>
    rcases hg.sigs s (Sigs.find_append_new ho hs) with ⟨T', -, -, hret⟩ | ⟨p, hp, hph, args, hret⟩
    · obtain rfl := Sig.close_ret_head (hd := Head.Type) (args := []) hret hr
      exact absurd hn.symm (hg.ne_Type hI (List.mem_append_left _ hT))
    · obtain rfl := Sig.close_ret_head hret hr
      rw [← hh, hph]
      exact ⟨rfl, List.mem_map_of_mem (List.mem_filter.2 ⟨hp, by simpa using hn⟩)⟩

theorem HeadOk.append {S S' : Sigs} {W : World} {k : HeadKind} {n : String} (h : HeadOk S W k n) :
    HeadOk (S ++ S') W k n :=
  ⟨h.fns, h.kind, let ⟨_, hs⟩ := h.sig; ⟨_, Sigs.find_append_old hs⟩⟩

namespace DataTop

theorem ResOk.mono_sigs {S S' : Sigs} (hS : S.Sub S') {r : Res} {v : Value} (h : ResOk S r v) : ResOk S' r v :=
  ⟨h.1, let ⟨A, hA⟩ := h.2.1; ⟨A, hA.mono_sigs hS⟩, fun ht => let ⟨V, hV⟩ := h.2.2 ht; ⟨V, hV.mono_sigs hS⟩⟩

theorem Group.noJunk (hI : TopInv st ρ) (hg : Group st ts cs new done st')
    (hj : ∀ n ∈ ts ++ cs.map (·.2), n ≠ junkHead.name) : (st.sc.sigs ++ new).find junkHead = none := by
  cases hf : (st.sc.sigs ++ new).find junkHead with
  | none => rfl
  | some s =>
    have hm := Sigs.find_append_new hI.noJunk hf
    have hh := Sigs.find_head hf
    rcases hg.sigs s hm with ⟨T, hT, h1, -⟩ | ⟨p, hp, h1, -⟩
    · rw [hh] at h1; cases h1
    · rw [hh] at h1
      exact absurd (congrArg Head.name h1).symm (hj _ (List.mem_append_right _ (List.mem_map_of_mem hp)))

end DataTop

/-- A group of `data` declarations, none named `sorry`, keeps the top level's invariant: the world extends by the
new signatures, closed under the same ideal values, which add no value constructor to an earlier data type. -/
theorem Group.topInv (hI : TopInv st ρ) (hg : Group st ts cs new true st')
    (hj : ∀ n ∈ ts ++ cs.map (·.2), n ≠ junkHead.name) : TopInv st' ρ := by
  have hle := hg.le hI
  have hsub := Sigs.sub_append_close st.sc.sigs new ρ
  have hwSc := hg.world_Sc (ρ := ρ)
  have hJ := DataTop.Group.noJunk hI hg hj
  obtain ⟨heq, -, -, hown, hok, hsigs, htypes, hctors⟩ := id hg
  subst heq
  refine ⟨hI.len, hI.noRemoved, hI.holes, fun sig hs => ?_, hJ, fun sig hs => ?_, fun h sig hs => ?_,
    fun d hd => ?_, hI.groups, let ⟨_, hs⟩ := hI.typeSig; ⟨_, Sigs.find_append_old hs⟩, hI.goal, fun hp => ?_,
    fun ht => ?_⟩
  · rcases List.mem_append.1 hs with hs | hs
    · exact hI.sigsOk sig hs
    · exact hok sig hs
  · rcases List.mem_append.1 hs with hs | hs
    · obtain ⟨hd, args, h1, h2, s, h3⟩ := hI.rets sig hs
      exact ⟨hd, args, h1, h2, s, Sigs.find_append_old h3⟩
    · rcases hsigs sig hs with ⟨T, -, -, hret⟩ | ⟨p, hp, -, args, hret⟩
      · obtain ⟨s, h3⟩ := hI.typeSig
        exact ⟨_, _, hret, rfl, s, Sigs.find_append_old h3⟩
      · obtain ⟨s, hs', hh⟩ := htypes p.1 (hown p hp)
        exact ⟨_, _, hret, rfl, Sigs.find_of_mem (List.mem_append_right _ hs') hh⟩
  · cases ho : st.sc.sigs.find h with
    | some s0 => exact hg.kindOf_old (hI.sigNames h s0 ho)
    | none =>
      have hh := Sigs.find_head hs
      subst hh
      rcases hsigs sig (Sigs.find_append_new ho hs) with ⟨T, hT, h1, -⟩ | ⟨p, hp, h1, -⟩
      · rw [h1]; simp [kindOf, hg.find?_type hT]
      · rw [h1]; simp [kindOf, hg.find?_ctor hp]
  · obtain ⟨sig, hs⟩ := hI.fnNames d hd
    exact ⟨sig, hg.find?_old hs⟩
  · obtain ⟨g, h1, h2⟩ := hI.proved hp
    exact ⟨g, h1, fun W' hW' => h2 W' (hle.trans hW')⟩
  have L := hI.live ht
  refine ⟨hwSc ▸ L.sat.mono_sigs hsub, fun n r h => ?_, hwSc ▸ L.env.mono_sigs hsub, ?_⟩
  · obtain ⟨v, h1, h2⟩ := L.names n r h
    exact ⟨v, h1, hwSc ▸ DataTop.ResOk.mono_sigs hsub h2⟩
  intro W' hW' act hact n g hfind
  have hle' := hle.trans hW'
  cases h0 : st.globals.find? (·.name == n) with
  | some g0 =>
    rw [hg.find?_old h0] at hfind
    cases hfind
    have hold := L.globals W' hle' act hact n g h0
    cases g with
    | fn _ s => cases s <;> exact hold
    | type T cs0 dn =>
      exact ⟨hold.1.append, fun cs' h1 h2 =>
        let ⟨a, b, c, d⟩ := hold.2 cs' h1 h2
        ⟨a, b, c, fun c hc => hg.find?_old (d c hc)⟩⟩
    | ctor _ => exact HeadOk.append hold
  | none =>
    have hfr : ∀ g ∈ st.globals, g.name ≠ n := fun g hg' hn => by
      have := List.find?_eq_none.1 h0 g hg'
      simp [hn] at this
    rw [find?_fresh hfr] at hfind
    rcases groupGlobals_find? hfind with ⟨hT, rfl⟩ | ⟨p, hp, rfl, rfl⟩
    · have hn' := List.mem_append_left (cs.map (·.2)) hT
      have hS : ∃ s, (st.sc.sigs ++ new).find ⟨.type, n⟩ = some s :=
        let ⟨_, hs, hh⟩ := htypes n hT
        Sigs.find_of_mem (List.mem_append_right _ hs) hh
      have hSc : ∃ s, Sigs.find ((st.sc.sigs ++ new).map (Sig.close ρ)) ⟨.type, n⟩ = some s := by
        rw [Sigs.find_map_close]
        obtain ⟨s, hs⟩ := hS
        exact ⟨_, by rw [hs]; rfl⟩
      have hne := hg.ne_Type hI hn'
      refine ⟨HeadOk.mono hW' ⟨hg.fns_none hI hn',
        by simp [TopState.world, TopState.prog, kindOf, hg.find?_type hT], hS⟩, ?_⟩
      rintro cs' ⟨⟩ -
      refine ⟨hne, let ⟨s, hs⟩ := hSc; ⟨s, hW'.sigs _ _ hs⟩, Complete.mono hW' hne hSc (hg.complete hI hT),
        fun c hc => ?_⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
      exact hg.find?_ctor (List.mem_filter.1 hp).1
    · have hn' := List.mem_append_right ts (List.mem_map_of_mem (f := (·.2)) hp)
      exact HeadOk.mono hW' ⟨hg.fns_none hI hn', by simp [TopState.world, TopState.prog, kindOf, hg.find?_ctor hp],
        let ⟨_, hs, hh⟩ := hctors p hp; Sigs.find_of_mem (List.mem_append_right _ hs) hh⟩

end

/-- What a `goal` statement does: it sets the goal, when none is set, to its checked type or telescopes. -/
theorem goal_spec {st st' : TopState} {p : Pos} {g : Goal} (h : topItem st (.goal p g) = .ok st') :
    st.goal = none ∧ ∃ goal : CheckedGoal, st' = { st with goal := some goal } ∧ match g with
      | .fn hdr => ∃ ps rs u, header (st.ctx true) st.sc hdr = .ok (ps, rs) ∧
          topLevel st p (ps.tele ++ rs.tele) = .ok u ∧
          goal = ⟨.fn ps.tele rs.tele, ps.tainted || rs.tainted || st.sc.taintedBy.isSome, p⟩
      | .type t => ∃ ty is tainted, annotate st.ctx st.sc (.type t) = .ok (ty, is, tainted) ∧
          ty.entriesBelow st.sc.Γ.length = true ∧ goal = ⟨.type ty, tainted || st.sc.taintedBy.isSome, t.pos⟩ := by
  simp only [topItem] at h
  split at h
  · simp [failAt_eq, bind, Except.bind] at h
  rename_i hs
  refine ⟨by simpa using hs, ?_⟩
  cases g with
  | fn hdr =>
    obtain ⟨⟨ps, rs⟩, h1, h⟩ := bind_eq_ok.1 h
    obtain ⟨u, h2, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at h
    exact ⟨_, h.symm, ps, rs, u, h1, h2, rfl⟩
  | type t =>
    obtain ⟨⟨ty, is, tainted⟩, h1, h⟩ := bind_eq_ok.1 h
    obtain ⟨u, h2, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at h
    exact ⟨_, h.symm, ty, is, tainted, h1, ensure_ok h2, rfl⟩

namespace DataTop

mutual
theorem Term.boundsBelow_of_eval {ρ env : List Value} :
    ∀ (t : Term) {v : Value}, t.eval ρ env = some v → t.boundsBelow env.length = true
  | .entry _, _, _ => rfl
  | .bound i, _, h => by
    simp only [Term.eval] at h
    simpa [Term.boundsBelow] using (List.getElem?_eq_some_iff.1 h).1
  | .app _ as, _, h => by
    obtain ⟨vs, hvs, -⟩ := Term.eval_app.1 h
    exact Term.boundsBelowList_of_evalList as hvs
theorem Term.boundsBelowList_of_evalList {ρ env : List Value} :
    ∀ (as : List Term) {vs : List Value}, Term.evalList ρ env as = some vs → Term.boundsBelowList env.length as = true
  | [], _, _ => rfl
  | a :: as, _, h => by
    obtain ⟨v, vs, hv, hvs, -⟩ := Term.evalList_cons_eq_some.1 h
    simp only [Term.boundsBelowList, Term.boundsBelow_of_eval a hv, Term.boundsBelowList_of_evalList as hvs,
      Bool.and_self]
end

theorem TopLive.wtermInv {st : TopState} {ρ : List Value} (hI : TopInv st ρ) (L : TopLive st ρ) :
    WTermInv st.sc st.sc.Γ.length (st.world ρ).Sc ρ :=
  ⟨L.sat.1, by rw [hI.len]; exact Nat.le_refl _, SigsClose.close hI.noRemoved, hI.sigsOk,
    by simp [TopState.world, Sigs.find_map_close, hI.noJunk],
    fun n r hn => let ⟨v, hv, h⟩ := L.names n r hn; ⟨v, hv, h.2.1⟩⟩

end DataTop

/-- A `goal` statement keeps the top level's invariant: the goal it sets mentions only top-level entries (§12), and,
in an untainted scope, a type goal's type is closed. -/
theorem goalItem_sound {st st' : TopState} {ρ : List Value} {p : Pos} {g : Goal} (hI : TopInv st ρ)
    (h : topItem st (.goal p g) = .ok st') : (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ := by
  obtain ⟨hnone, goal, rfl, hgoal⟩ := goal_spec h
  refine ⟨World.Le.refl _, ⟨hI.len, hI.noRemoved, hI.holes, hI.sigsOk, hI.noJunk, hI.rets, hI.sigNames, hI.fnNames,
    hI.groups, hI.typeSig, fun g' hg' => ?_, fun hpr => ?_, fun ht =>
      let L := hI.live ht; ⟨L.sat, L.names, L.env, L.globals⟩⟩⟩
  · cases hg'
    cases g with
    | fn hdr =>
      obtain ⟨ps, rs, u, -, h2, rfl⟩ := hgoal
      exact ⟨topLevel_ok h2, fun _ t ht => by cases ht⟩
    | type t =>
      obtain ⟨ty, is, tainted, h1, h2, rfl⟩ := hgoal
      refine ⟨h2, fun hts t' ht' => ?_⟩
      cases ht'
      obtain ⟨A, hA⟩ := (annotate_eval (DataTop.TopLive.wtermInv hI (hI.live hts)) h1).1
      exact DataTop.Term.boundsBelow_of_eval _ hA
  · obtain ⟨g', hg', -⟩ := hI.proved hpr
    rw [hnone] at hg'
    cases hg'

theorem fnGroup_goal {st st' : TopState} {fs : List Fn} (h : fnGroup st fs = .ok st') : st'.goal = st.goal := by
  unfold fnGroup at h
  obtain ⟨st0, h0, h⟩ := bind_eq_ok.1 h
  obtain ⟨⟨st1, heads⟩, h1, h⟩ := bind_eq_ok.1 h
  obtain ⟨⟨taint, bodies⟩, -, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have e0 := foldlM_induct (fun _ s => s.goal = st.goal) fs [] (fun q x b b' _ hb hf => by
    obtain ⟨_, -, hf⟩ := bind_eq_ok.1 hf
    simp only [pure, Except.pure, Except.ok.injEq] at hf
    rw [← hf]; exact hb) rfl h0
  have e1 := foldlM_induct (fun _ p => p.1.goal = st.goal) fs [] (fun q x b b' _ hb hf => by
    obtain ⟨⟨s, hd⟩, hh, hf⟩ := bind_eq_ok.1 hf
    simp only [pure, Except.pure, Except.ok.injEq] at hf
    rw [← hf]
    unfold fnHead at hh
    obtain ⟨_, -, hh⟩ := bind_eq_ok.1 hh
    obtain ⟨_, -, hh⟩ := bind_eq_ok.1 hh
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hh
    rw [← hh.1]; exact hb) e0 h1
  exact e1

/-- Takes apart a hypothesis `h : x = .ok r` about checking code down to its successful paths. -/
macro "unwind_ok " h:ident : tactic => `(tactic| repeat' (first
  | (simp [failAt_eq, bind, Except.bind] at $h:ident; done)
  | (rw [keep_ok] at $h:ident)
  | (obtain ⟨_, hx, $h:ident⟩ := bind_eq_ok.1 $h:ident; try (simp [failAt_eq] at hx; done))
  | (dsimp only at $h:ident)
  | (split at $h:ident)))

theorem qedFnGoal_goal {st st' : TopState} {ps rs : Telescope} {e : Expr} (h : qedFnGoal st ps rs e = .ok st') :
    st'.goal = st.goal := by
  unfold qedFnGoal at h
  unwind_ok h
  all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h])

/-- No item but a `goal` statement changes the goal once it is set. -/
theorem topItem_goal {st st' : TopState} {t : Top} {g : CheckedGoal}
    (h : topItem st t = .ok st') (hg : st.goal = some g) : st'.goal = some g := by
  unfold topItem at h
  split at h
  · obtain ⟨_, hgr⟩ := dataGroup_group h
    rw [hgr.eq]; exact hg
  · obtain ⟨_, hgr⟩ := dataGroup_group h
    rw [hgr.eq]; exact hg
  · rw [fnGroup_goal h]; exact hg
  · rw [fnGroup_goal h]; exact hg
  · unfold comptimeLet at h
    unwind_ok h
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h]; exact hg)
  · unwind_ok h
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h]; exact hg)
  · unwind_ok h
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h]; exact hg)
  · have := (goal_spec (by unfold topItem; exact h)).1
    rw [hg] at this; cases this
  · unwind_ok h
    all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h])
    all_goals dsimp only
    all_goals first
      | exact (qedFnGoal_goal (by assumption)).trans hg
      | (simp only [pure, Except.pure, Except.ok.injEq] at *; subst_vars; exact hg)

/-- When checking a program stops at no error, each item was checked, from the state the items before it left. -/
theorem topItems_split : ∀ {st : TopState} {pre post : List Top} {t : Top},
    (topItems st (pre ++ t :: post)).2 = none → ∃ s', (topItems st pre).2 = none ∧
      topItem (topItems st pre).1 t = .ok s' ∧ topItems s' post = topItems st (pre ++ t :: post)
  | st, [], post, t, h => by
    simp only [List.nil_append, topItems] at h ⊢
    split at h
    · rename_i s' hs
      refine ⟨s', ?_, hs, ?_⟩ <;> simp
    · simp at h
  | st, a :: pre, post, t, h => by
    simp only [List.cons_append, topItems] at h ⊢
    split at h
    · rename_i s1 hs1
      exact topItems_split h
    · simp at h

theorem topItems_goal : ∀ {st : TopState} {l : List Top} {g : CheckedGoal},
    (topItems st l).2 = none → st.goal = some g → (topItems st l).1.goal = some g
  | st, [], g, _, hg => by simpa [topItems] using hg
  | st, t :: l, g, h, hg => by
    simp only [topItems] at h ⊢
    split at h
    · rename_i s' hs
      exact topItems_goal h (topItem_goal hs hg)
    · simp at h

theorem List.eq_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l →
    f a = f b → a = b
  | x :: l, hn, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · exact absurd hab.symm (hn.1 b hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd hab (hn.1 a ha')
      · exact List.eq_of_nodup_map hn.2 ha' hb' hab

/-- A data type declared with no value constructors owns none, its name being declared once in its group. -/
theorem ownedBy_empty {ds : List Data} {d : Data} (hn : (ds.map (·.name.name)).Nodup) (hd : d ∈ ds)
    (hc : d.ctors = []) : ownedBy (groupCtors ds) d.name.name = [] := by
  simp only [ownedBy, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq]
  intro p hp hpd
  simp only [groupCtors, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨d', hd', k, hk, rfl⟩ := hp
  obtain rfl := List.eq_of_nodup_map hn hd' hd hpd
  rw [hc] at hk
  cases hk

theorem checkTerm_app_head {C : Ctx} {sc : Scope} {hn : Name} {args : List WTerm} {r : Res}
    (h : checkTerm C sc (.app hn args) = .ok r) : ∃ k ts, r.term = .app ⟨k, hn.name⟩ ts := by
  unfold checkTerm at h
  split at h
  · simp [failAt_eq, error_bind] at h
  all_goals first
    | (simp [notApplied, failAt_eq, error_bind] at h; done)
    | (obtain ⟨k, -, h⟩ := bind_eq_ok.1 h
       obtain ⟨sig, hsig, h⟩ := bind_eq_ok.1 h
       obtain ⟨_, -, h⟩ := bind_eq_ok.1 h
       obtain ⟨rs, -, h⟩ := bind_eq_ok.1 h
       simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h
       exact ⟨k, _, by rw [Sigs.find_head (Scope.sig_ok hsig)]⟩)

theorem annotate_type {C : Ctx} {sc : Scope} {t : WTerm} {ty : Term} {is : Option Term} {tn : Bool}
    (h : annotate C sc (.type t) = .ok (ty, is, tn)) : ∃ r, checkTerm C sc t = .ok r ∧ ty = r.term := by
  simp only [annotate] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
  obtain ⟨_, -, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨r, hr, h.1.symm⟩

/-- Every type a value has in a world of the top level applies a type constructor. -/
theorem TopInv.hasType_kind {st : TopState} {ρ : List Value} {v : Value} {hd : Head} {us : List Value}
    (hI : TopInv st ρ) (h : HasType (st.world ρ).Sc v (.app hd us)) : hd.kind = .type := by
  obtain ⟨_, _, _, -, hf, -, hr⟩ := h.inv
  simp only [TopState.world, Sigs.find_map_close, Option.map_eq_some_iff] at hf
  obtain ⟨s, hs, rfl⟩ := hf
  obtain ⟨_, _, hret, hk, -⟩ := hI.rets s (List.mem_of_find?_eq_some hs)
  obtain rfl := Sig.close_ret_head hret hr
  exact hk

end Pledge
