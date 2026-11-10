import Pledge.Sound.Expr

namespace Pledge

namespace FnGroup

theorem fresh_global {C : Ctx} {sc : Scope} {seen : List String} {n : String} {pos : Pos} {x : List String}
    (h : fresh C sc seen (some n) pos = .ok x) : C.global n = none := by
  simp only [fresh] at h
  split at h
  · simp [failAt_eq] at h
  · split at h
    · simp [failAt_eq] at h
    · rename_i hc
      cases hg : C.global n
      · rfl
      · simp [hg] at hc

theorem fold0_spec : ∀ (fs : List Fn) (s s' : TopState),
    List.foldlM (fun st f => do
      let _ ← fresh (st.ctx true) st.sc [] (some f.name.name) f.name.pos
      pure { st with globals := st.globals ++ [Global.fn f.name.name none] }) s fs = .ok s' →
    s' = { s with globals := s.globals ++ fs.map fun f => .fn f.name.name none } ∧ (fs.map (·.name.name)).Nodup ∧
      ∀ f ∈ fs, s.globals.find? (·.name == f.name.name) = none
  | [], s, s', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | f :: fs, s, s', h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨s1, hs1, h⟩ := bind_eq_ok.1 h
    obtain ⟨x, hx, hs1⟩ := bind_eq_ok.1 hs1
    simp only [pure, Except.pure, Except.ok.injEq] at hs1
    subst hs1
    have hfr : s.globals.find? (·.name == f.name.name) = none := fresh_global hx
    obtain ⟨rfl, hnd, hfr'⟩ := fold0_spec fs _ s' h
    have hfr'' : ∀ f' ∈ fs, s.globals.find? (·.name == f'.name.name) = none ∧ f.name.name ≠ f'.name.name := by
      intro f' hf'
      have := hfr' f' hf'
      rw [List.find?_append, Option.or_eq_none_iff] at this
      refine ⟨this.1, fun he => ?_⟩
      simp [Global.name, he] at this
    refine ⟨by simp, ?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
      exact ⟨fun f' hf' he => (hfr'' f' hf').2 he.symm, hnd⟩
    · intro f' hf'
      rcases List.mem_cons.1 hf' with rfl | hf'
      · exact hfr
      · exact (hfr'' f' hf').1

/-- What `fnHead` checked of a function's head: its telescopes, in the top-level scope `sc`, mention only top-level
entries, and the head records them. -/
structure HeadSpec (sc : Scope) (names : List String) (h : FnHead) : Prop where
  name : h.fn.name = h.f.name.name
  group : h.fn.group = names
  tele : ∃ (C : Ctx) (ps rs : Checked), telescope C sc (h.f.header.params.map (·.binder)) "param" = .ok ps ∧
    telescope C ps.sc h.f.header.returns "binder" ps.ids = .ok rs ∧
    (ps.tele ++ rs.tele).all (·.entriesBelow sc.Γ.length) = true ∧
    h.sig = ⟨ps.tele, rs.tele, h.f.header.params.map (·.subterm), false⟩ ∧ h.sc = ps.sc ∧ h.env = ps.ids.map .entry ∧
    h.fn.subterms = ((ps.ids.zip (h.f.header.params.map (·.subterm))).filter (·.2)).map fun (i, _) => Term.entry i

theorem fnHead_spec {names : List String} {st st' : TopState} {f : Fn} {h : FnHead}
    (hh : fnHead names st f = .ok (st', h)) :
    h.f = f ∧ HeadSpec st.sc names h ∧
      st' = { st with
        globals := st.globals.map fun g => if g.name == h.fn.name then .fn g.name (some h.sig) else g } := by
  simp only [fnHead] at hh
  obtain ⟨⟨ps, rs⟩, hhd, hh⟩ := bind_eq_ok.1 hh
  obtain ⟨u, htl, hh⟩ := bind_eq_ok.1 hh
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hh
  obtain ⟨rfl, rfl⟩ := hh
  simp only [header] at hhd
  obtain ⟨ps', hps, hhd⟩ := bind_eq_ok.1 hhd
  obtain ⟨rs', hrs, hhd⟩ := bind_eq_ok.1 hhd
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hhd
  obtain ⟨rfl, rfl⟩ := hhd
  exact ⟨rfl, ⟨rfl, rfl, _, ps', rs', hps, hrs, ensure_ok htl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- The globals after the signatures of `hs` are recorded one after the other, as `fnHead` does. -/
def updSigs : List FnHead → List Global → List Global
  | [], gs => gs
  | h :: hs, gs => updSigs hs (gs.map fun g => if g.name == h.fn.name then .fn g.name (some h.sig) else g)

theorem fold1_spec (names : List String) : ∀ (fs : List Fn) (s : TopState) (acc : List FnHead) (s' : TopState)
    (hs : List FnHead), List.foldlM (fun x f => do
        let __x ← fnHead names x.fst f
        pure (__x.fst, x.snd ++ [__x.snd])) (s, acc) fs = .ok (s', hs) →
      ∃ hs', hs = acc ++ hs' ∧ hs'.map (·.f) = fs ∧ (∀ h ∈ hs', HeadSpec s.sc names h) ∧
        s' = { s with globals := updSigs hs' s.globals }
  | [], s, acc, s', hs, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, rfl, by simp, rfl⟩
  | f :: fs, s, acc, s', hs, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨x, hx, h⟩ := bind_eq_ok.1 h
    obtain ⟨y, hy, hx⟩ := bind_eq_ok.1 hx
    simp only [pure, Except.pure, Except.ok.injEq] at hx
    subst hx
    obtain ⟨hf, hspec, hst⟩ := fnHead_spec (st' := y.1) (h := y.2) hy
    obtain ⟨hs', rfl, hmap, hall, rfl⟩ := fold1_spec names fs _ _ s' hs h
    rw [hst] at hall ⊢
    refine ⟨y.2 :: hs', by simp, by simp [hf, hmap], ?_, rfl⟩
    intro h' hh'
    rcases List.mem_cons.1 hh' with rfl | hh'
    · exact hspec
    · exact hall h' hh'

/-- A global after the signatures of `hs` are recorded: the last of them with its name, if any. -/
def lastSig (hs : List FnHead) (g : Global) : Global :=
  match hs.reverse.find? (·.fn.name == g.name) with
  | some h => .fn g.name (some h.sig)
  | none => g

theorem lastSig_cons (h : FnHead) (hs : List FnHead) (g : Global) :
    lastSig (h :: hs) g = lastSig hs (if g.name == h.fn.name then .fn g.name (some h.sig) else g) := by
  have hn : (if g.name == h.fn.name then Global.fn g.name (some h.sig) else g).name = g.name := by
    split <;> rfl
  unfold lastSig
  rw [hn, List.reverse_cons, List.find?_append]
  cases hf : hs.reverse.find? (·.fn.name == g.name) with
  | some h' => rfl
  | none =>
    simp only [Option.none_or, List.find?_cons, List.find?_nil]
    by_cases e : h.fn.name = g.name
    · simp [e]
    · have e' : (g.name == h.fn.name) = false := by simpa using Ne.symm e
      have e'' : (h.fn.name == g.name) = false := by simpa using e
      simp [e', e'']

theorem updSigs_eq : ∀ (hs : List FnHead) (gs : List Global), updSigs hs gs = gs.map (lastSig hs)
  | [], gs => by
    simp only [updSigs]
    induction gs with
    | nil => rfl
    | cons g gs ih => exact congrArg (g :: ·) ih
  | h :: hs, gs => by
    rw [updSigs, updSigs_eq hs, List.map_map]
    exact List.map_congr_left fun g _ => (lastSig_cons h hs g).symm

theorem find?_name_map {gs : List Global} {f : Global → Global} (hf : ∀ g, (f g).name = g.name) (n : String) :
    (gs.map f).find? (·.name == n) = (gs.find? (·.name == n)).map f := by
  rw [List.find?_map]
  have : ((fun g : Global => g.name == n) ∘ f) = fun g => g.name == n := funext fun g => by simp [hf]
  rw [this]

theorem find?_unique {α : Type} {k : α → String} : ∀ {l : List α}, (l.map k).Nodup → ∀ {x}, x ∈ l →
    l.find? (fun y => k y == k x) = some x
  | y :: l, hnd, x, hx => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · simp
    · have : (k y == k x) = false := by
        simpa using fun he => hnd.1 x hx he.symm
      rw [this]
      exact find?_unique hnd.2 hx

/-- What `setSigs` does to one global. -/
def setSig (heads : List FnHead) (taint : List Bool) : Global → Global
  | .fn n s => match (heads.zip taint).find? (·.1.fn.name == n) with
    | some (h, t) => .fn n (some { h.sig with tainted := t })
    | none => .fn n s
  | g => g

theorem setSigs_eq (gs : List Global) (heads : List FnHead) (taint : List Bool) :
    setSigs gs heads taint = gs.map (setSig heads taint) := by
  simp only [setSigs]
  congr 1

theorem setSig_name (heads : List FnHead) (taint : List Bool) (g : Global) : (setSig heads taint g).name = g.name := by
  cases g <;> simp only [setSig] <;> try rfl
  split <;> rfl

theorem lastSig_name (hs : List FnHead) (g : Global) : (lastSig hs g).name = g.name := by
  unfold lastSig; split <;> rfl

theorem zip_false {α : Type} : ∀ l : List α, l.zip (l.map fun _ => false) = l.map (·, false)
  | [] => rfl
  | a :: l => by simp [zip_false l]

theorem FnSig.with_untainted {s : FnSig} (h : s.tainted = false) : { s with tainted := false } = s := by
  cases s; simp_all

theorem zip_find_none {heads : List FnHead} {taint : List Bool} {n : String}
    (h : ∀ h ∈ heads, ¬(h.fn.name == n) = true) : (heads.zip taint).find? (·.1.fn.name == n) = none :=
  List.find?_eq_none.2 fun p hp => h p.1 (List.of_mem_zip hp).1

theorem zip_find_some {heads : List FnHead} {taint : List Bool} (hl : taint.length = heads.length) {h : FnHead}
    (hh : h ∈ heads) {n : String} (hn : h.fn.name = n) : ∃ q, (heads.zip taint).find? (·.1.fn.name == n) = some q := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hh
  cases hq : (heads.zip taint).find? (·.1.fn.name == n) with
  | some q => exact ⟨q, rfl⟩
  | none =>
    have := List.find?_eq_none.1 hq (heads[i], taint[i]'(hl ▸ hi))
      (List.mem_iff_getElem.2 ⟨i, by simp [hl, hi], by simp⟩)
    simp [hn] at this

theorem lastSig_fn (hs : List FnHead) (m : String) (s : Option FnSig) : ∃ s', lastSig hs (.fn m s) = .fn m s' := by
  unfold lastSig; split <;> exact ⟨_, rfl⟩

/-- After a group's heads are checked and its bodies to the taint fixed point `taint` (§12), a name resolves as
among the earlier globals followed by the group's functions with their signatures, tainted as `taint` says. -/
theorem group_find {gs : List Global} {heads : List FnHead} {taint : List Bool} (hnd : (heads.map (·.fn.name)).Nodup)
    (hfr : ∀ h ∈ heads, gs.find? (·.name == h.fn.name) = none) (hl : taint.length = heads.length) (n : String) :
    (setSigs (updSigs heads (gs ++ heads.map fun h => Global.fn h.fn.name none)) heads taint).find? (·.name == n) =
      (gs ++ (heads.zip taint).map fun p : FnHead × Bool => Global.fn p.1.fn.name (some { p.1.sig with tainted := p.2 })).find?
        (·.name == n) := by
  rw [updSigs_eq, setSigs_eq, find?_name_map (setSig_name _ _), find?_name_map (lastSig_name _), List.find?_append,
    List.find?_append, List.find?_map]
  cases hg : gs.find? (·.name == n) with
  | some g =>
    have hgn : g.name = n := by simpa using List.find?_some hg
    have hno : ∀ h ∈ heads, h.fn.name ≠ n := fun h hh he => by rw [← he, hfr h hh] at hg; cases hg
    have hl : lastSig heads g = g := by
      unfold lastSig
      rw [show heads.reverse.find? (·.fn.name == g.name) = none from
        List.find?_eq_none.2 fun h hh he => hno h (List.mem_reverse.1 hh) (by simpa [hgn] using he)]
    simp only [Option.map_some, Option.some_or, hl]
    cases g with
    | fn m s =>
      simp only [setSig, zip_find_none (fun h hh he => hno h hh (by simpa [← hgn, Global.name] using he))]
    | _ => rfl
  | none =>
    rw [List.find?_map]
    simp only [Option.none_or, Function.comp_def, Global.name]
    cases hh : heads.find? (fun h => h.fn.name == n) with
    | none => rw [zip_find_none (List.find?_eq_none.1 hh)]; rfl
    | some h =>
      have hn : h.fn.name = n := by simpa using List.find?_some hh
      obtain ⟨q, hq⟩ := zip_find_some hl (List.mem_of_find?_eq_some hh) hn
      have hqn : q.1.fn.name = n := by simpa using List.find?_some hq
      obtain ⟨s, hs⟩ := lastSig_fn heads h.fn.name none
      subst hn
      simp only [Option.map_some, hs, setSig, hq, hqn]

theorem GlobalsOk.congr_find {n0 phase : Nat} {gs gs' : List Global} {fn : Option FnCtx} {S : Sigs} {W : World}
    {act : Act} (hf : ∀ n, gs.find? (·.name == n) = gs'.find? (·.name == n)) (h : GlobalsOk n0 phase gs fn S W act) :
    GlobalsOk n0 phase gs' fn S W act := by
  intro n g hg
  rw [← hf] at hg
  simpa only [hf] using h n g hg

theorem kindOf_congr {gs gs' : List Global} (hf : ∀ n, gs.find? (·.name == n) = gs'.find? (·.name == n))
    (n : String) : kindOf gs n = kindOf gs' n := by
  unfold kindOf; rw [hf]

theorem FnOk.of_none {n0 phase : Nat} {W : World} {fn : Option FnCtx} {act : Act} {n : String} {sig : FnSig}
    (h : FnOk n0 phase W none act n sig) (hn : ∀ f, fn = some f → f.group.contains n = false) :
    FnOk n0 phase W fn act n sig := by
  have hc : fn.any (·.group.contains n) = false := by
    cases fn with
    | none => rfl
    | some f => simpa using hn f rfl
  refine ⟨h.params, h.returns, h.cons, h.subterm, fun ht => ?_⟩
  obtain ⟨d, h1, h2, h3, h4, h5, h6, h7⟩ := h.defn ht
  have h7' : d.group < act.group := by simpa using h7
  refine ⟨d, h1, h2, h3, h4, h5, h6, ?_⟩
  rw [hc]
  simpa using h7'

/-- The globals of a group's bodies and of the top level after it: the earlier ones, then the group's functions. -/
theorem GlobalsOk.group {n0 phase : Nat} {gs : List Global} {fn : Option FnCtx} {S : Sigs} {W : World} {act : Act}
    {new : List (String × FnSig)} (hbase : GlobalsOk n0 phase gs none S W act)
    (hout : ∀ f, fn = some f → ∀ n g, gs.find? (·.name == n) = some g → f.group.contains n = false)
    (hnew : ∀ p ∈ new, FnOk n0 phase W fn act p.1 p.2) :
    GlobalsOk n0 phase (gs ++ new.map fun p => .fn p.1 (some p.2)) fn S W act := by
  intro n g hg
  rw [List.find?_append] at hg
  cases hgs : gs.find? (·.name == n) with
  | some g0 =>
    rw [hgs, Option.some_or, Option.some.injEq] at hg
    subst hg
    have := hbase n _ hgs
    cases g0 with
    | fn m sig =>
      cases sig with
      | none => trivial
      | some sig => exact FnOk.of_none this fun f hf => hout f hf n _ hgs
    | type T cs d =>
      refine ⟨this.1, fun cs' hcs hd => ?_⟩
      obtain ⟨a, b, c, e⟩ := this.2 cs' hcs hd
      exact ⟨a, b, c, fun c hc => by rw [List.find?_append, e c hc]; rfl⟩
    | ctor c => exact this
  | none =>
    rw [hgs, Option.none_or, List.find?_map, Option.map_eq_some_iff] at hg
    obtain ⟨p, hp, rfl⟩ := hg
    have hn : p.1 = n := by simpa [Global.name] using List.find?_some hp
    subst hn
    exact hnew p (List.mem_of_find?_eq_some hp)

theorem count_filter_zip : ∀ (ids : List Nat) (flags : List Bool), ids.length = flags.length →
    ((ids.zip flags).filter (·.2)).length = flags.count true
  | [], [], _ => rfl
  | i :: ids, b :: flags, h => by
    have := count_filter_zip ids flags (by simpa using h)
    cases b <;> simp [this]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- What a function's head gives, whatever the valuation: its telescopes mention only top-level entries, and its
parameter scope is the top-level scope with the parameters opened and named. -/
theorem HeadSpec.facts {sc : Scope} {names : List String} {h : FnHead} (hs : HeadSpec sc names h) :
    h.sig.tainted = false ∧ (∀ b ∈ h.sig.params, b.entriesBelow sc.Γ.length = true) ∧
      (∀ b ∈ h.sig.returns, b.entriesBelow sc.Γ.length = true) ∧
      h.sig.subterm.length = h.sig.params.length ∧ h.sig.params.length = h.f.header.params.length ∧
      h.fn.subterms.length = h.sig.subterm.count true ∧ h.sc.sigs = sc.sigs ∧ h.sc.holes = sc.holes ∧
      h.sc.taintedBy = sc.taintedBy := by
  obtain ⟨C, ps, rs, hps, hrs, hbelow, hsig, hsc, -, hsub⟩ := hs.tele
  obtain ⟨hpl, hpids, -, -, hpsc, -⟩ := telescope_shape hps
  simp only [List.all_append, Bool.and_eq_true, List.all_eq_true] at hbelow
  rw [hsig]
  refine ⟨rfl, fun b hb => hbelow.1 b hb, fun b hb => hbelow.2 b hb, by simpa using hpl.symm,
    by simpa using hpl, ?_, ?_, ?_, ?_⟩
  · rw [hsub, List.length_map, count_filter_zip _ _ (by simp [hpids])]
  all_goals rw [hsc, hpsc, Scope.bind_eq]

theorem evalList_range' : ∀ (pre vs : List Value),
    Term.evalList (pre ++ vs) [] ((List.range' pre.length vs.length).map .entry) = some vs
  | _, [] => rfl
  | pre, v :: vs => by
    have := evalList_range' (pre ++ [v]) vs
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at this
    simp only [List.length_cons, List.range'_succ, List.map_cons]
    refine Term.evalList_cons_eq_some.2 ⟨v, vs, ?_, this, rfl⟩
    simp [Term.eval]

theorem binder_agree_symm {ρ ρ' : List Value} {b b' : TBinder} (h : TBinder.Agree ρ ρ' b b') :
    TBinder.Agree ρ' ρ b' b :=
  ⟨fun env => (h.type env).symm, fun env => (h.is env).symm, h.mult.symm⟩

theorem wantSat_agree {S : Sigs} {ρ ρ' env : List Value} {t : Bool} {v : Value} {b b' : TBinder}
    (ha : TBinder.Agree ρ ρ' b b') (h : WantSat S ρ (Want.of b) env t v) : WantSat S ρ' (Want.of b') env t v := by
  refine ⟨fun T hT => ?_, fun e he => ?_⟩
  · cases hT
    obtain ⟨A, hA, h1⟩ := h.1 b.type rfl
    exact ⟨A, by rw [← ha.type env]; exact hA, h1⟩
  · have := ha.is env
    change b'.is = some e at he
    rw [he] at this
    cases hb : b.is with
    | none => rw [hb] at this; cases this
    | some e' =>
      rw [hb] at this
      simp only [Option.map_some, Option.some.injEq] at this
      rw [← this]
      exact h.2 e' hb

theorem wantsSat_agree {S : Sigs} {ρ ρ' : List Value} : ∀ {Δ Δ' : Telescope} {env : List Value} {ts : List Bool}
    {vs : List Value}, Telescope.Agree ρ ρ' Δ Δ' → WantsSat S ρ (Δ.map Want.of) env ts vs →
      WantsSat S ρ' (Δ'.map Want.of) env ts vs
  | [], [], _, [], [], _, _ => trivial
  | _ :: _, _ :: _, _, _ :: _, _ :: _, ⟨hb, hΔ⟩, ⟨h1, h2⟩ => ⟨wantSat_agree hb h1, wantsSat_agree hΔ h2⟩
  | [], [], _, [], _ :: _, _, h | [], [], _, _ :: _, _, _, h | _ :: _, _ :: _, _, [], _, _, h
  | _ :: _, _ :: _, _, _ :: _, [], _, h => h.elim
  | [], _ :: _, _, _, _, ha, _ | _ :: _, [], _, _, _, ha, _ => ha.elim

theorem wantsCons_agree {S : Sigs} {ρ ρ' : List Value} : ∀ {Δ Δ' : Telescope} {env : List Value},
    Telescope.Agree ρ ρ' Δ Δ' → WantsCons S ρ (Δ.map Want.of) env → WantsCons S ρ' (Δ'.map Want.of) env
  | [], [], _, _, _ => trivial
  | b :: _, b' :: _, env, ⟨hb, hΔ⟩, ⟨h1, h2, h3⟩ => by
    refine ⟨fun T hT => ?_, fun e he => ?_, fun v hv => wantsCons_agree hΔ (h3 v (wantSat_agree
      (binder_agree_symm hb) hv))⟩
    · cases hT
      obtain ⟨A, hA, hr⟩ := h1 b.type rfl
      exact ⟨A, by rw [← hb.type env]; exact hA, hr⟩
    · have := hb.is env
      change b'.is = some e at he
      rw [he] at this
      cases hbi : b.is with
      | none => rw [hbi] at this; cases this
      | some e' =>
        rw [hbi] at this
        simp only [Option.map_some, Option.some.injEq] at this
        obtain ⟨v, hv, hr, hw⟩ := h2 e' hbi
        refine ⟨v, by rw [← this]; exact hv, hr, fun T A hT hA => ?_⟩
        cases hT
        exact hw b.type A rfl (by rw [hb.type env]; exact hA)
  | [], _ :: _, _, ha, _ | _ :: _, [], _, ha, _ => ha.elim

theorem go_erased {C : Ctx} {kind : String} : ∀ (bs : List Binder) (sc : Scope) (seen : List String)
    (acc : List (Binder × Opening)) {res : Scope × List String × List (Binder × Opening)},
    telescope.go C kind sc seen acc bs = .ok res → ∀ (k : Nat) (b : Binder), bs[k]? = some b →
      (res.1.Γ[sc.Γ.length + k]?).map (·.erased) = some (b.mult.getD .many == .erased)
  | [], _, _, _, _, _, k, b, hb => by simp at hb
  | b :: bs, sc, seen, acc, res, h, k, b', hb => by
    simp only [telescope.go] at h
    obtain ⟨seen', -, h⟩ := bind_eq_ok.1 h
    obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
    unfold opening at ho
    obtain ⟨⟨type, is, tainted⟩, -, ho⟩ := bind_eq_ok.1 ho
    simp only [pure, Except.pure, Except.ok.injEq] at ho
    subst ho
    obtain ⟨-, -, -, -, -, hpre, -, -⟩ := telescope_go_shape bs _ _ _ h
    simp only [Scope.bind, openTele, openTele.go] at h hpre
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      obtain ⟨t, ht⟩ := hpre
      rw [← ht, Nat.add_zero, List.getElem?_append_left (by simp), List.getElem?_append_right (by simp)]
      simp
    | succ k =>
      have := go_erased bs _ _ _ h k b' (by simpa using hb)
      simp only [List.length_append, List.length_singleton] at this
      rw [← this]
      congr 2
      omega

/-- The entry of a telescope's `k`-th binder is erased exactly when the binder is (§16). -/
theorem telescope_erased {C : Ctx} {sc : Scope} {bs : List Binder} {kind : String} {outer : List Nat}
    {out : Checked} (h : telescope C sc bs kind outer = .ok out) :
    ∀ (k : Nat) (b : TBinder), out.tele[k]? = some b →
      (out.sc.Γ[sc.Γ.length + k]?).map (·.erased) = some (b.mult == .erased) := by
  unfold telescope at h
  obtain ⟨⟨sc', seen, opens⟩, hgo, h⟩ := bind_eq_ok.1 h
  obtain ⟨tele, htele, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  intro k b hb
  obtain ⟨hl, hall⟩ := mapM_ok htele
  obtain ⟨⟨bk, x, ok⟩, hp⟩ : ∃ p, (bs.zip opens)[k]? = some p := by
    have : k < (bs.zip opens).length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hb).1
    exact ⟨_, List.getElem?_eq_getElem this⟩
  have hab := (abstracted_ok (hall k _ b hp hb)).2.2.2
  have hbk : bs[k]? = some bk := by
    rw [List.getElem?_zip_eq_some] at hp
    exact hp.1
  have := go_erased bs sc [] [] hgo k bk hbk
  simp only at this ⊢
  rw [this, hab]

/-- A tainted function's head still gives what `FnOk` asks of every function (§12): a tainted call opens the
returns to `junk` or their `is` clauses' values (`telescope_wsound`, `telescope_cons`). -/
theorem HeadSpec.cons {sc : Scope} {names : List String} {h : FnHead} (hs : HeadSpec sc names h) {Sc : Sigs}
    {ρ : List Value} (hT : WTermInv sc sc.Γ.length Sc ρ) (pvals : List Value)
    (hp : WantsSat Sc ρ (h.sig.params.map Want.of) [] (h.sig.params.map fun _ => false) pvals) :
    WantsCons Sc ρ (h.sig.returns.map Want.of) pvals := by
  obtain ⟨C, ps, rs, hps, hrs, hbelow, hsig, -, -, -⟩ := hs.tele
  rw [hsig] at hp ⊢
  dsimp only at hp ⊢
  have hw := telescope_wsound (outer := []) hT hps rfl hp
  obtain ⟨htl, hids, -, -, -, -⟩ := telescope_shape hps
  have hρl : ρ.length = sc.Γ.length := hT.sat.1
  have hpl : pvals.length = ps.tele.length := by simpa using (WantsSat.lengths hp).1
  have hev : Term.evalList (ρ ++ pvals) [] (ps.ids.map .entry) = some pvals := by
    rw [hids, ← hρl, ← htl, ← hpl]; exact evalList_range' ρ pvals
  simp only [List.all_append, Bool.and_eq_true] at hbelow
  refine wantsCons_agree (Telescope.agree_of_entriesBelow (n := sc.Γ.length) ?_ hbelow.2) (telescope_cons hw hrs hev)
  rw [← hρl]; simp

/-- What a group's head gives `FnOk`, its specification as a function of its taint. -/
theorem HeadSpec.fnOk {sc : Scope} {names : List String} {h : FnHead} (hs : HeadSpec sc names h) {phase : Nat}
    {W : World} {ρ : List Value} (hT : WTermInv sc sc.Γ.length W.Sc ρ) (hρ : W.ρ.take sc.Γ.length = ρ)
    {fn : Option FnCtx} {act : Act} {t : Bool}
    (hdefn : t = false → ∃ d, W.P.fns.find h.fn.name = some d ∧ d.params.length = h.sig.params.length ∧
      d.subterm = h.sig.subterm ∧ d.returns = h.sig.returns.length ∧ d.subterm.count true ≤ d.pad ∧
      CallSpec W phase d h.sig act ∧
      if fn.any (·.group.contains h.fn.name) then d.group = act.group ∧ d.pad = act.subs.length
      else d.group < act.group) :
    FnOk sc.Γ.length phase W fn act h.fn.name { h.sig with tainted := t } := by
  obtain ⟨htnt, hpar, hret, hsubl, -⟩ := hs.facts
  have hρl : ρ.length = sc.Γ.length := hT.sat.1
  refine ⟨hpar, hret, fun ρ' hρ' pvals hp => ?_, hsubl, fun ht => ?_⟩
  · have hag : ρ'.take sc.Γ.length = ρ.take sc.Γ.length := by rw [hρ', hρ, ← hρl, List.take_length]
    exact wantsCons_agree (Telescope.agree_of_entriesBelow hag.symm (List.all_eq_true.2 hret))
      (hs.cons hT pvals (wantsSat_agree (Telescope.agree_of_entriesBelow hag (List.all_eq_true.2 hpar)) hp))
  · change t = false at ht
    subst ht
    rw [FnSig.with_untainted htnt]
    exact hdefn rfl

theorem checkAll_spec {α : Type} {f : α → CheckM Out} : ∀ {l : List α} {outs : List Out}, checkAll f l = .ok outs →
    outs.length = l.length ∧ ∀ p ∈ l.zip outs, f p.1 = .ok p.2
  | [], outs, h => by
    simp only [checkAll, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | a :: l, outs, h => by
    simp only [checkAll] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
    obtain ⟨os, hos, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hos
    obtain ⟨hl, hall⟩ := checkAll_spec hos
    refine ⟨by simp [hl], fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ho
    · exact hall p hp

theorem spread_length : ∀ ts ns : List Bool, (spread ts ns).length = ts.length
  | _ :: ts, _ :: ns => by simp [spread, spread_length ts ns]
  | [], _ | _ :: _, [] => by simp [spread]

theorem fixTaint_full {step : List Bool → CheckM (List Out)} :
    ∀ (n : Nat) (t : List Bool) (r : List Bool × List Out), untainted t = n → fixTaint step t = .ok r →
      step r.1 = .ok r.2 ∧ grows r.1 (r.2.map fun o => o.res.any (·.tainted)) = false ∧ r.1.length = t.length := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro t r hn h
  rw [fixTaint] at h
  obtain ⟨bodies, hb, h⟩ := bind_eq_ok.1 h
  dsimp only at h
  split at h
  · rename_i hg
    obtain ⟨h1, h2, h3⟩ := ih _ (hn ▸ untainted_spread_lt _ _ hg) _ _ rfl h
    exact ⟨h1, h2, by rw [h3, spread_length]⟩
  · rename_i hg
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hb, by simpa using hg, rfl⟩

/-- The taint fixed point (§12): the bodies of the last round are checked with the final taint, and no function
untainted in it has a tainted result. -/
theorem fixTaint_spec {step : List Bool → CheckM (List Out)} :
    ∀ {t : List Bool} {r : List Bool × List Out}, fixTaint step t = .ok r →
      step r.1 = .ok r.2 ∧ grows r.1 (r.2.map fun o => o.res.any (·.tainted)) = false :=
  fun h => let ⟨h1, h2, _⟩ := fixTaint_full _ _ _ rfl h; ⟨h1, h2⟩

theorem grows_eq_false {ts ns : List Bool} (h : grows ts ns = false) :
    ∀ (i : Nat), ts[i]? = some false → ns[i]? = some true → False := by
  induction ts generalizing ns with
  | nil => intro i ht; simp at ht
  | cons t ts ih =>
    cases ns with
    | nil => intro i _ hn; simp at hn
    | cons n ns =>
      simp only [grows, Bool.or_eq_false_iff] at h
      intro i ht hn
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ht hn
        subst ht hn
        simp at h
      | succ i => exact ih h.2 i (by simpa using ht) (by simpa using hn)

theorem subterms_eval : ∀ (pre : List Value) (flags : List Bool) (vs : List Value), flags.length = vs.length →
    Term.evalList (pre ++ vs) [] ((((List.range' pre.length flags.length).zip flags).filter (·.2)).map
      fun (i, _) => Term.entry i) = some ((flags.zip vs).filterMap fun (b, v) => if b then some v else none)
  | _, [], [], _ => rfl
  | pre, b :: flags, v :: vs, hl => by
    have := subterms_eval (pre ++ [v]) flags vs (by simpa using hl)
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at this
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.filter_cons, List.filterMap_cons]
    cases b
    · simpa using this
    · simp only [↓reduceIte, List.map_cons]
      refine Term.evalList_cons_eq_some.2 ⟨v, _, by simp [Term.eval], this, rfl⟩
  | _, [], _ :: _, hl | _, _ :: _, [], hl => by simp at hl

theorem filterMap_some : ∀ (flags : List Bool) (vs : List Value),
    (flags.zip vs).filterMap (fun (b, v) => if b then some (some v) else none) =
      ((flags.zip vs).filterMap fun (b, v) => if b then some v else none).map some
  | [], _ | _ :: _, [] => rfl
  | b :: flags, v :: vs => by cases b <;> simp [filterMap_some flags vs]

theorem exists_zip {α β : Type} {l : List α} {l' : List β} (hl : l'.length = l.length) {a : α} (ha : a ∈ l) :
    ∃ b, (a, b) ∈ l.zip l' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  exact ⟨l'[i]'(hl ▸ hi), List.mem_iff_getElem.2 ⟨i, by simp [hl, hi], by simp⟩⟩

theorem le_foldr_max {n : Nat} : ∀ {l : List Nat}, n ∈ l → n ≤ l.foldr max 0
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => by have := le_foldr_max h; simp only [List.foldr_cons]; omega

/-- The function a group's head and checked body make. -/
def mkDef (st : TopState) (pad : Nat) (p : FnHead × Out) : FnDef :=
  { name := p.1.fn.name, params := p.1.f.header.params.map (·.binder.name), subterm := p.1.sig.subterm,
    returns := p.1.sig.returns.length, body := p.2.tree, globals := st.env, group := st.groups, pad := pad }

/-- The globals of a group's bodies: the earlier ones, then the group's functions with their signatures, tainted
as the fixed point says (§12). -/
def groupGlobals (st : TopState) (heads : List FnHead) (taint : List Bool) : List Global :=
  st.globals ++ (heads.zip taint).map fun p : FnHead × Bool => .fn p.1.fn.name (some { p.1.sig with tainted := p.2 })

/-- What checking a group of functions in an untainted top-level scope establishes, before its untainted functions
are known to meet their specifications. -/
structure GroupOk (st : TopState) (ρ : List Value) (heads : List FnHead) (bodies : List Out) (taint : List Bool)
    (pad : Nat) : Prop where
  inv : TopInv st ρ
  live : TopLive st ρ
  untainted : st.sc.taintedBy = none
  len : bodies.length = heads.length
  tlen : taint.length = heads.length
  spec : ∀ h ∈ heads, HeadSpec st.sc (heads.map (·.fn.name)) h ∧ h.f.body.holeFree = true
  nodup : (heads.map (·.fn.name)).Nodup
  fresh : ∀ h ∈ heads, st.globals.find? (·.name == h.fn.name) = none
  pad : ∀ h ∈ heads, h.fn.subterms.length ≤ pad
  body : ∀ p ∈ heads.zip bodies, ∃ C : Ctx, C.phase = st.phase ∧ C.erased = false ∧ C.fn = some p.1.fn ∧
    (∀ n, C.globals.find? (·.name == n) = (groupGlobals st heads taint).find? (·.name == n)) ∧
    checkExpr C p.1.sc (some (returnsGiven p.1)) p.1.f.body = .ok p.2
  clean : ∀ p ∈ heads.zip bodies, (p.1, false) ∈ heads.zip taint → ∀ x ∈ p.2.res, x.tainted = false

theorem teleSat_typed {S : Sigs} {ρ : List Value} :
    ∀ {Δ : Telescope} {env vs : List Value}, TeleSat S ρ Δ env vs → ∀ v ∈ vs, ∃ V, HasType S v V
  | [], _, _, h => by rw [TeleSat.nil_iff.1 h]; simp
  | _ :: _, _, _, h => by
    obtain ⟨v, vs', rfl, ⟨A, -, hA, -⟩, ht⟩ := TeleSat.cons_iff.1 h
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ⟨A, hA⟩
    · exact teleSat_typed ht u hu

theorem groupGlobals_eq (st : TopState) (heads : List FnHead) (taint : List Bool) :
    groupGlobals st heads taint = st.globals ++ ((heads.zip taint).map fun p : FnHead × Bool =>
      (p.1.fn.name, { p.1.sig with tainted := p.2 })).map fun p => .fn p.1 (some p.2) := by
  rw [groupGlobals, List.map_map]; rfl

theorem fieldRes_getElem? {n k : Nat} {ids : List Nat} (hids : ids = List.range' n k) {i : Nat} {r : Res}
    (hr : (fieldRes ids)[i]? = some r) : i < k ∧ r = ⟨.entry (n + i), false, false⟩ := by
  subst hids
  have hi : i < k := by simpa [fieldRes] using (List.getElem?_eq_some_iff.1 hr).1
  rw [fieldRes, List.getElem?_map, List.getElem?_range'] at hr
  · simp only [Option.map_some, Option.some.injEq, Nat.one_mul] at hr
    exact ⟨hi, by rw [← hr]⟩
  · exact hi

theorem multOf_mult {m : Mult} {b : Bool} (h : b = (m == .erased)) : (if b then Mult.erased else .many) = m := by
  subst h; cases m <;> rfl

/-- The top level's invariant gives `TermInv` of its scope in every later world without a signature for
`junkHead`. -/
theorem topTermInv {st : TopState} {ρ : List Value} (hI : TopInv st ρ) (hL : TopLive st ρ) {W : World}
    (hW : (st.world ρ).Le W) (hJ : W.Sc.find junkHead = none) : TermInv st.sc st.sc.Γ.length W.Sc ρ :=
  ⟨hL.sat.mono_sigs hW.sigs, Nat.le_of_eq hI.len.symm, (SigsClose.close hI.noRemoved).mono hW.sigs, hI.sigsOk, hJ,
    fun n r hl => let ⟨v, hv, hr⟩ := hL.names n r hl
      ⟨v, hv, let ⟨A, hA⟩ := hr.2.1; ⟨A, hA.mono_sigs hW.sigs⟩,
        fun ht => let ⟨V, hV⟩ := hr.2.2 ht; ⟨V, hV.mono_sigs hW.sigs⟩⟩⟩

/-- One activation of an untainted function of a group (SOUNDNESS.md Lemma 6.1 and Theorem 6.2, parts 5 and 9):
given that every untainted function of the group meets its specification from this activation, the body's ideal
results satisfy the returns (the main lemma, ideal part), and the body runs on run-time arguments related to the
ideal ones to related results (the main lemma, run-time part). -/
theorem GroupOk.step {st : TopState} {ρ : List Value} {heads : List FnHead} {bodies : List Out} {taint : List Bool}
    {pad : Nat} (G : GroupOk st ρ heads bodies taint pad) {W : World} (hW : (st.world ρ).Le W)
    (hJ : W.Sc.find junkHead = none)
    (hfind : ∀ p ∈ heads.zip bodies, W.P.fns.find p.1.fn.name = some (mkDef st pad p))
    {p : FnHead × Out} (hp : p ∈ heads.zip bodies) (hpt : (p.1, false) ∈ heads.zip taint) {vs : List Value}
    (hvs : TeleSat W.Sc W.ρ p.1.sig.params [] vs)
    (ih : ∀ q ∈ heads.zip bodies, (q.1, false) ∈ heads.zip taint →
      CallSpec W st.phase (mkDef st pad q) q.1.sig (calleeAct (mkDef st pad p) vs)) :
    ∃ rs, TeleSat W.Sc W.ρ p.1.sig.returns vs rs ∧ ∀ as, MultsRel W.Sc st.phase (p.1.sig.params.map (·.mult)) as vs →
      ∃ rs', CallRel W.P (mkDef st pad p) as rs' ∧ MultsRel W.Sc st.phase (p.1.sig.returns.map (·.mult)) rs' rs := by
  obtain ⟨h, o⟩ := p
  have hmem : h ∈ heads := (List.of_mem_zip hp).1
  obtain ⟨hs, hhf⟩ := G.spec h hmem
  obtain ⟨-, hpar, hret, hsubl, hparl, hsubc, -, -, -⟩ := hs.facts
  obtain ⟨C0, ps, rs, hps, hrs, -, hsig, hsc, henv, hsub⟩ := hs.tele
  obtain ⟨C, hph, her, hfn, hgl, hc⟩ := G.body _ hp
  simp only at hc hfn hvs ih hpt ⊢
  have hL := G.live
  have hρl : ρ.length = st.sc.Γ.length := G.inv.len
  have hρt : ρ.take st.sc.Γ.length = ρ := by rw [← hρl]; exact List.take_length
  have hpre : W.ρ.take st.sc.Γ.length = ρ := by rw [← hρl]; exact hW.take
  have hpb : h.sig.params.all (·.entriesBelow st.sc.Γ.length) = true := List.all_eq_true.2 hpar
  have hrb : h.sig.returns.all (·.entriesBelow st.sc.Γ.length) = true := List.all_eq_true.2 hret
  have hvs₀ : TeleSat W.Sc ρ ps.tele [] vs := by
    have := (TeleSat.iff_of_entriesBelow (ρ' := ρ) (by rw [hpre, hρt]) hpb).1 hvs
    rw [hsig] at this
    exact this
  have hSC : SigsClose st.sc.sigs ρ W.Sc := (SigsClose.close G.inv.noRemoved).mono hW.sigs
  have hT := topTermInv G.inv hL hW hJ
  have hT' := telescope_sound (outer := []) (outerv := []) hT hps rfl hvs₀
  obtain ⟨hpl', hids, -, hΓp, hpsc, -⟩ := telescope_shape hps
  have hvl : vs.length = h.f.header.params.length := by simpa [hpl'] using hvs₀.length_eq
  have hids' : ps.ids = List.range' ρ.length vs.length := by rw [hids, hρl, hvl, List.length_map]
  have hevids : Term.evalList (ρ ++ vs) [] (ps.ids.map .entry) = some vs := by rw [hids']; exact evalList_range' ρ vs
  have hpn : (h.f.header.params.map (·.binder)).map (·.name) = (mkDef st pad (h, o)).params := by
    simp [mkDef]
  have hdl : (mkDef st pad (h, o)).subterm.length = vs.length := by simp only [mkDef]; rw [hsubl, hparl, hvl]
  have hdc : (mkDef st pad (h, o)).subterm.count true ≤ (mkDef st pad (h, o)).pad := by
    simp only [mkDef]; rw [← hsubc]; exact G.pad h hmem
  obtain ⟨-, hcl, -⟩ := calleeAct_subs _ vs hdl hdc
  have hI₁ : Inv C { st.sc with Γ := ps.sc.Γ } st.sc.Γ.length W (ρ ++ vs) (calleeAct (mkDef st pad (h, o)) vs) := by
    refine ⟨G.inv.holes, G.untainted, hT'.sat, by rw [← hρl]; exact hW.val.length_le, by rw [hpre, ← hρl]; simp,
      fun ρ'' hρ'' => hSC.of_entriesBelow (by rw [hρ'', hpre, hρt]) fun sig hs => (G.inv.sigsOk sig hs).1,
      G.inv.sigsOk, hJ, fun n r hl => ?_, ?_, ?_⟩
    · obtain ⟨v, hv, hr⟩ := hL.names n r hl
      exact ⟨v, Term.eval_frame_ρ vs hv, hr.1, let ⟨A, hA⟩ := hr.2.1; ⟨A, hA.mono_sigs hW.sigs⟩,
        fun ht => let ⟨V, hV⟩ := hr.2.2 ht; ⟨V, hV.mono_sigs hW.sigs⟩⟩
    · refine GlobalsOk.congr_find (fun n => (hgl n).symm) ?_
      rw [hfn, hph, groupGlobals_eq]
      refine GlobalsOk.group (hL.globals W hW _ fun d hd => G.inv.groups d hd) ?_ fun q hq => ?_
      · intro f hf n g hg
        cases hf
        rw [hs.group]
        refine Bool.eq_false_iff.2 fun hcn => ?_
        obtain ⟨h', hh', rfl⟩ := List.mem_map.1 (by simpa using hcn)
        rw [G.fresh h' hh'] at hg
        cases hg
      · obtain ⟨⟨h', t'⟩, hq', rfl⟩ := List.mem_map.1 hq
        have hh' := (List.of_mem_zip hq').1
        obtain ⟨hs', -⟩ := G.spec h' hh'
        obtain ⟨o', ho'⟩ := exists_zip G.len hh'
        refine hs'.fnOk hT.weak hpre fun ht => ?_
        subst ht
        obtain ⟨-, -, -, -, hparl', hsubc', -⟩ := hs'.facts
        refine ⟨mkDef st pad (h', o'), hfind _ ho', by simp [mkDef, hparl'], rfl, rfl,
          by simp only [mkDef]; rw [← hsubc']; exact G.pad h' hh', ih _ ho' hq', ?_⟩
        have : (some h.fn).any (·.group.contains h'.fn.name) = true := by
          simp [hs.group]; exact ⟨h', hh', rfl⟩
        rw [this]
        exact ⟨rfl, hcl.symm⟩
    · rw [hfn]
      rintro f ⟨⟩
      have hfl : (h.f.header.params.map (·.subterm)).length = vs.length := by simp [hvl]
      have hids'' : ps.ids = List.range' ρ.length (h.f.header.params.map (·.subterm)).length := by rw [hids', hfl]
      rw [hsub, hids'']
      refine ⟨_, subterms_eval ρ _ vs hfl, ?_⟩
      have hst : (mkDef st pad (h, o)).subterm = h.f.header.params.map (·.subterm) := by simp [mkDef, hsig]
      simp only [calleeAct, hst, filterMap_some, List.length_append, List.length_map, List.length_replicate]
      congr 2
      omega
  have hfr : Term.evalList (ρ ++ vs) [] ((fieldRes ps.ids).map (·.term)) = some vs := by
    rw [fieldRes, List.map_map]; exact hevids
  have hI : Inv C h.sc st.sc.Γ.length W (ρ ++ vs) (calleeAct (mkDef st pad (h, o)) vs) := by
    rw [hsc, hpsc]
    refine hI₁.bind hfr fun i r v hr hv => ?_
    obtain ⟨V, hV⟩ := teleSat_typed hvs₀ v (List.mem_of_getElem? hv)
    exact ⟨hV.noRemoved, ⟨V, hV.wtype hJ⟩, fun _ => ⟨V, hV⟩⟩
  have hg : ∀ g', some (returnsGiven h) = some g' → g'.Ok W.Sc (ρ ++ vs) := by
    rintro g' ⟨⟩
    refine ⟨⟨vs, by simp only [returnsGiven]; rw [henv]; exact hevids⟩, fun _ envv henvv => ?_⟩
    simp only [returnsGiven] at henvv ⊢
    rw [henv, hevids] at henvv
    cases henvv
    rw [hsig]
    exact telescope_cons hT'.weak hrs hevids
  obtain ⟨hpost, -⟩ := Expr.sound h.f.body hhf C h.sc _ _ W (ρ ++ vs) _ o hI hg hc
  have hclean := G.clean _ hp hpt
  have hnt : o.sc.taintedBy = none := by
    obtain ⟨hne, htr, -⟩ := checkExpr_removed hc
    cases ht : o.sc.taintedBy with
    | none => rfl
    | some _ =>
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
      have := (htr (by simp [ht])).2 r hr
      rw [hclean r hr] at this
      cases this
  obtain ⟨ρ', vr, -, -, -, hwants, hrun⟩ := hpost hnt
  have hw' := hwants _ rfl vs (by simp only [returnsGiven]; rw [henv]; exact hevids)
  simp only [returnsGiven] at hw'
  have ht := WantsSat.teleSat hw' (by simpa using fun r hr => hclean r hr)
  have hlens := WantsSat.lengths hw'
  simp only [List.length_map] at hlens
  refine ⟨vr, (TeleSat.iff_of_entriesBelow ?_ hrb).1 ht, fun as has => ?_⟩
  · rw [hpre, List.append_assoc, List.take_append_of_le_length (Nat.le_of_eq hρl.symm), hρt]
  obtain ⟨hasl, -, hasr⟩ := has
  simp only [List.length_map] at hasl
  have hE : EnvRel W.Sc C.phase h.sc (ρ ++ vs) (pushed (mkDef st pad (h, o)).params as ++ st.env) := by
    have hE₁ : EnvRel W.Sc C.phase { st.sc with Γ := ps.sc.Γ } (ρ ++ vs) st.env :=
      EnvRel.extend (sc := st.sc) vs (hph ▸ hL.env.mono_sigs hW.sigs) rfl (Entries.eraseRules_prefix hΓp) hρl
    rw [hsc, hpsc, ← hpn]
    refine EnvRel.bind hE₁ (by simp [fieldRes, hids]) (by simp [fieldRes, hids, hasl, hparl]) fun i r a hr ha _ => ?_
    obtain ⟨hi, rfl⟩ := fieldRes_getElem? hids hr
    have hiv : i < vs.length := by rw [hvl]; simpa using hi
    have hit : i < ps.tele.length := by rw [hpl']; simpa using hi
    refine ⟨vs[i], by simp [Term.eval, hρl, hiv], ?_⟩
    have hb : ps.tele[i]? = some ps.tele[i] := List.getElem?_eq_getElem hit
    have hm : (h.sig.params.map (·.mult))[i]? = some ps.tele[i].mult := by rw [hsig]; simp [hb]
    have := hasr i _ a vs[i] hm ha (List.getElem?_eq_getElem hiv)
    rw [hph]
    have he := telescope_erased hps i _ hb
    simp only [Scope.multOf, Scope.erasedEntry, Bool.false_or]
    rw [multOf_mult (m := ps.tele[i].mult)]
    · exact this
    · cases hx : ps.sc.Γ[st.sc.Γ.length + i]? with
      | none => rw [hx] at he; cases he
      | some en => rw [hx] at he; simpa using he
  obtain ⟨us, hev, us', htk, hrel⟩ := hrun _ hE
  have hul := (take_ok htk).1
  refine ⟨us', .mk (bindIds_of_length (by simp [mkDef, hasl, hparl])) hev (by simpa [mkDef, hlens.2] using htk),
    by simp [hul, hlens.2], by simp [hlens.1], fun k m a v hm ha hv => ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, o.res[k]? = some r := by
    have : k < o.res.length := by rw [← hul]; exact (List.getElem?_eq_some_iff.1 ha).1
    exact ⟨_, List.getElem?_eq_getElem this⟩
  have := hrel k r a v hr ha hv (hclean r (List.mem_of_getElem? hr))
  rw [List.getElem?_map] at hm
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hm
  have hpm : C.posMult (some (returnsGiven h)) k = b.mult := by
    simp only [Ctx.posMult, her, Bool.false_or, Option.any_some, Given.erasedAt, returnsGiven, List.getElem?_map, hb,
      Option.map_some, Want.of]
    cases b.mult <;> rfl
  rw [hpm, hph] at this
  exact this

/-- Every untainted function of a checked group meets its specification in every later world without a signature
for `junkHead` (SOUNDNESS.md part 6), by well-founded induction on the measure of its activations' ideal
arguments. -/
theorem GroupOk.fnSpec {st : TopState} {ρ : List Value} {heads : List FnHead} {bodies : List Out}
    {taint : List Bool} {pad : Nat} (G : GroupOk st ρ heads bodies taint pad) {W : World} (hW : (st.world ρ).Le W)
    (hJ : W.Sc.find junkHead = none)
    (hfind : ∀ p ∈ heads.zip bodies, W.P.fns.find p.1.fn.name = some (mkDef st pad p)) :
    ∀ p ∈ heads.zip bodies, (p.1, false) ∈ heads.zip taint → FnSpec W st.phase (mkDef st pad p) p.1.sig := by
  suffices H : ∀ a p, p ∈ heads.zip bodies → (p.1, false) ∈ heads.zip taint → ∀ vs,
      TeleSat W.Sc W.ρ p.1.sig.params [] vs → calleeAct (mkDef st pad p) vs = a →
      ∃ rs, TeleSat W.Sc W.ρ p.1.sig.returns vs rs ∧ ∀ as, MultsRel W.Sc st.phase (p.1.sig.params.map (·.mult)) as vs →
        ∃ rs', CallRel W.P (mkDef st pad p) as rs' ∧ MultsRel W.Sc st.phase (p.1.sig.returns.map (·.mult)) rs' rs from
    fun p hp hpt vs hvs => H _ p hp hpt vs hvs rfl
  intro a
  induction a using WellFounded.induction Act.lt_wf with
  | _ a ih =>
  intro p hp hpt vs hvs ha
  subst ha
  exact G.step hW hJ hfind hp hpt hvs fun q hq hqt vs' hvs' hlt => ih _ hlt q hq hqt vs' hvs' rfl

theorem kindOf_some {gs : List Global} {n : String} {k : HeadKind} (h : kindOf gs n = some k) :
    ∃ g, gs.find? (·.name == n) = some g := by
  unfold kindOf at h
  split at h <;> first | (cases h; done) | exact ⟨_, ‹_›⟩

theorem kindOf_group (st : TopState) (heads : List FnHead) (taint : List Bool) (n : String) :
    kindOf (groupGlobals st heads taint) n = kindOf st.globals n := by
  unfold kindOf groupGlobals
  rw [List.find?_append]
  cases hg : st.globals.find? (·.name == n) with
  | some g => rfl
  | none =>
    rw [Option.none_or, List.find?_map]
    cases (List.find? _ (heads.zip taint)) <;> rfl

theorem zip_index {α β γ : Type} {key : α → String} {l : List α} {as : List β} {bs : List γ}
    (hnd : (l.map key).Nodup) {x : α} {a : β} {b : γ} (ha : (x, a) ∈ l.zip as) (hb : (x, b) ∈ l.zip bs) :
    ∃ i : Nat, l[i]? = some x ∧ as[i]? = some a ∧ bs[i]? = some b := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hb
  rw [List.getElem?_zip_eq_some] at hi hj
  have hl : l.Nodup := List.Pairwise.of_map key (fun _ _ h e => h (e ▸ rfl)) hnd
  have : i = j := (hl.getElem?_inj (List.getElem?_eq_some_iff.1 hi.1).1).1 (by rw [hi.1, hj.1])
  subst this
  exact ⟨i, hi.1, hi.2, hj.2⟩

theorem fns_find_group {st : TopState} {ρ : List Value} {heads : List FnHead} {bodies : List Out} {pad : Nat}
    (hI : TopInv st ρ) (hlen : bodies.length = heads.length) (hnd : (heads.map (·.fn.name)).Nodup)
    (hfr : ∀ h ∈ heads, st.globals.find? (·.name == h.fn.name) = none) {p : FnHead × Out}
    (hp : p ∈ heads.zip bodies) :
    Fns.find (st.fns ++ (heads.zip bodies).map (mkDef st pad)) p.1.fn.name = some (mkDef st pad p) := by
  have hm := (List.of_mem_zip hp).1
  simp only [Fns.find, List.find?_append]
  have hst : st.fns.find? (·.name == p.1.fn.name) = none := List.find?_eq_none.2 fun d hd he => by
    obtain ⟨sig, hs⟩ := hI.fnNames d hd
    rw [show d.name = p.1.fn.name by simpa using he, hfr _ hm] at hs
    cases hs
  rw [hst, Option.none_or, List.find?_map]
  have hz : (heads.zip bodies).map (fun q => q.1.fn.name) = heads.map (·.fn.name) := by
    have hz0 := List.map_fst_zip (l₁ := heads) (l₂ := bodies) (Nat.le_of_eq hlen.symm)
    calc (heads.zip bodies).map (fun q => q.1.fn.name) = ((heads.zip bodies).map Prod.fst).map (·.fn.name) := by
          rw [List.map_map]; rfl
      _ = _ := by rw [hz0]
  have := find?_unique (k := fun q : FnHead × Out => q.1.fn.name) (by rw [hz]; exact hnd) hp
  rw [show ((fun d : FnDef => d.name == p.1.fn.name) ∘ mkDef st pad) = fun q => q.1.fn.name == p.1.fn.name from rfl,
    this]
  rfl

/-- A later world than the top level's has no signature for `junkHead`. -/
theorem later_noJunk {st : TopState} {ρ : List Value} (hI : TopInv st ρ) {W : World} (hW : (st.world ρ).Le W) :
    W.Sc.find junkHead = none :=
  hW.noJunk (by simp [TopState.world, Sigs.find_map_close, hI.noJunk])

/-- The state after a checked group of functions extends the world and keeps the top level's invariant; in an
untainted scope, every untainted function meets its specification. -/
theorem group_post {st : TopState} {ρ : List Value} {heads : List FnHead} {bodies : List Out} {taint : List Bool}
    {pad : Nat} (hI : TopInv st ρ) (hlen : bodies.length = heads.length) (htl : taint.length = heads.length)
    (hspec : ∀ h ∈ heads, HeadSpec st.sc (heads.map (·.fn.name)) h) (hnd : (heads.map (·.fn.name)).Nodup)
    (hfr : ∀ h ∈ heads, st.globals.find? (·.name == h.fn.name) = none) (hpad : ∀ h ∈ heads, h.fn.subterms.length ≤ pad)
    (hG : st.sc.taintedBy = none → GroupOk st ρ heads bodies taint pad) {st' : TopState}
    (hph : st'.phase = st.phase) (hsc : st'.sc = st.sc) (henv : st'.env = st.env) (hgoal : st'.goal = st.goal)
    (hproved : st'.proved = st.proved) (hqed : st'.qedFn = st.qedFn)
    (hfns : st'.fns = st.fns ++ (heads.zip bodies).map (mkDef st pad)) (hgroups : st'.groups = st.groups + 1)
    (hglob : ∀ n, st'.globals.find? (·.name == n) = (groupGlobals st heads taint).find? (·.name == n)) :
    (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ := by
  have hkind : ∀ n, kindOf st'.globals n = kindOf st.globals n := fun n => by
    rw [kindOf_congr hglob, kindOf_group]
  have hSc : (st'.world ρ).Sc = (st.world ρ).Sc := by simp [TopState.world, hsc]
  have hdef : ∀ d ∈ (heads.zip bodies).map (mkDef st pad), ∃ p ∈ heads.zip bodies, d = mkDef st pad p := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hd
    exact ⟨p, hp, rfl⟩
  have hle : (st.world ρ).Le (st'.world ρ) := by
    refine ⟨⟨fun n d hd => ?_, fun n k hd hk => ⟨?_, by simp only [TopState.world, TopState.prog, hkind]; exact hk⟩⟩,
      by rw [hSc]; exact Sigs.Sub.refl _, List.prefix_refl _, fun h' sig' ws hd us hn hs => ?_, fun h => hSc ▸ h⟩
    · simp only [TopState.world, TopState.prog, hfns, Fns.find, List.find?_append] at hd ⊢
      rw [hd]; rfl
    · simp only [TopState.world, TopState.prog, hfns, Fns.find, List.find?_append] at hd ⊢
      rw [hd, Option.none_or]
      refine List.find?_eq_none.2 fun d hdm he => ?_
      obtain ⟨p, hp, rfl⟩ := hdef d hdm
      obtain ⟨g, hg⟩ := kindOf_some hk
      rw [show n = p.1.fn.name from (by simpa [mkDef] using he : p.1.fn.name = n).symm,
        hfr _ (List.of_mem_zip hp).1] at hg
      cases hg
    · rw [hSc] at hs; rw [hs] at hn; cases hn
  refine ⟨hle, ?_⟩
  have hfind : ∀ W, (st'.world ρ).Le W → ∀ p ∈ heads.zip bodies, W.P.fns.find p.1.fn.name = some (mkDef st pad p) :=
    fun W hW p hp => hW.prog.fns _ _ (by
      simp only [TopState.world, TopState.prog, hfns]; exact fns_find_group hI hlen hnd hfr hp)
  refine ⟨hsc ▸ hI.len, hI.noRemoved, hsc ▸ hI.holes, hsc ▸ hI.sigsOk, hsc ▸ hI.noJunk, hsc ▸ hI.rets,
    fun h sig hs => by rw [hkind]; exact hI.sigNames h sig (hsc ▸ hs), ?_, ?_, hsc ▸ hI.typeSig,
    hI.goal_le hle hgoal (by rw [hsc]; exact Nat.le_refl _) (by rw [hsc]; exact id), fun hp => ?_, fun ht => ?_⟩
  · intro d hd
    rw [hglob, groupGlobals, List.find?_append]
    rw [hfns] at hd
    rcases List.mem_append.1 hd with hd | hd
    · obtain ⟨sig, hs⟩ := hI.fnNames d hd
      exact ⟨sig, by rw [hs]; rfl⟩
    · obtain ⟨p, hp, rfl⟩ := hdef d hd
      have hm := (List.of_mem_zip hp).1
      obtain ⟨q, hq⟩ := zip_find_some (taint := taint) htl hm rfl
      have hqn : q.1.fn.name = p.1.fn.name := by simpa using List.find?_some hq
      refine ⟨some { q.1.sig with tainted := q.2 }, ?_⟩
      rw [show (mkDef st pad p).name = p.1.fn.name from rfl, hfr _ hm, Option.none_or, List.find?_map]
      rw [show ((fun g : Global => g.name == p.1.fn.name) ∘ fun q : FnHead × Bool => Global.fn q.1.fn.name
        (some { q.1.sig with tainted := q.2 })) = fun q => q.1.fn.name == p.1.fn.name from rfl, hq]
      simp [hqn]
  · intro d hd
    rw [hfns] at hd
    rw [hgroups]
    rcases List.mem_append.1 hd with hd | hd
    · have := hI.groups d hd; omega
    · obtain ⟨p, hp, rfl⟩ := hdef d hd
      simp [mkDef]
  · obtain ⟨g, hg, hW⟩ := hI.proved (hproved ▸ hp)
    exact ⟨g, hgoal ▸ hg, fun W' hW' => by rw [hph, hqed]; exact hW W' (hle.trans hW')⟩
  · rw [hsc] at ht
    have G := hG ht
    have hL := G.live
    refine ⟨by rw [hSc, hsc]; exact hL.sat, by rw [hSc, hsc]; exact hL.names,
      by rw [hSc, hph, hsc, henv]; exact hL.env, fun W' hW' act hact => ?_⟩
    rw [hsc, hph]
    have hW := hle.trans hW'
    have hJ := later_noJunk hI hW
    refine GlobalsOk.congr_find (fun n => (hglob n).symm) ?_
    rw [groupGlobals_eq]
    refine GlobalsOk.group (hL.globals W' hW act fun d hd => hact d (by rw [hfns]; exact List.mem_append_left _ hd))
      (fun f hf => by cases hf) fun q hq => ?_
    obtain ⟨⟨h', t'⟩, hq', rfl⟩ := List.mem_map.1 hq
    have hh' := (List.of_mem_zip hq').1
    obtain ⟨o', ho'⟩ := exists_zip hlen hh'
    have hpre : W'.ρ.take st.sc.Γ.length = ρ := by rw [← hI.len]; exact hW.take
    refine (hspec h' hh').fnOk (topTermInv hI hL hW hJ).weak hpre fun ht => ?_
    subst ht
    obtain ⟨-, -, -, -, hparl', hsubc', -⟩ := (hspec h' hh').facts
    refine ⟨mkDef st pad (h', o'), hfind W' hW' _ ho', by simp [mkDef, hparl'], rfl, rfl,
      by simp only [mkDef]; rw [← hsubc']; exact hpad h' hh', (G.fnSpec hW hJ (hfind W' hW') _ ho' hq').callSpec act,
      ?_⟩
    simp only [Option.any_none, Bool.false_eq_true, ↓reduceIte]
    exact hact _ (by rw [hfns]; exact List.mem_append_right _ (List.mem_map_of_mem ho'))

/-- A group of functions keeps the top level's invariant (SOUNDNESS.md part 6, with the main lemma for 5.1): the
world extends, and, in an untainted scope, every untainted function meets its specification; in a tainted scope
every function is tainted (§12). -/
theorem fnGroup_ok {st st' : TopState} {ρ : List Value} {fs : List Fn} (hI : TopInv st ρ)
    (hp : fs.all (·.body.holeFree) = true) (h : fnGroup st fs = .ok st') :
    (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ := by
  simp only [fnGroup] at h
  obtain ⟨st0, h0, h⟩ := bind_eq_ok.1 h
  obtain ⟨⟨st1, heads⟩, h1, h⟩ := bind_eq_ok.1 h
  obtain ⟨⟨taint, bodies⟩, h2, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨rfl, hnd, hfr⟩ := fold0_spec fs st st0 h0
  obtain ⟨heads', hh, hmap, hspec, rfl⟩ := fold1_spec _ fs _ [] st1 heads h1
  simp only [List.nil_append] at hh
  subst hh
  have hname : ∀ h ∈ heads, h.fn.name = h.f.name.name := fun h hh => (hspec h hh).name
  have hnames : fs.map (·.name.name) = heads.map (·.fn.name) := by
    rw [← hmap, List.map_map]; exact List.map_congr_left fun h hh => (hname h hh).symm
  have hmemf : ∀ h ∈ heads, h.f ∈ fs := fun h hh => hmap ▸ List.mem_map_of_mem hh
  have hfr' : ∀ h ∈ heads, st.globals.find? (·.name == h.fn.name) = none := fun h hh => by
    rw [hname h hh]; exact hfr _ (hmemf h hh)
  have hnd' : (heads.map (·.fn.name)).Nodup := hnames ▸ hnd
  have hspec' : ∀ h ∈ heads, HeadSpec st.sc (heads.map (·.fn.name)) h ∧ h.f.body.holeFree = true := fun h hh => by
    have := hspec h hh
    rw [hnames] at this
    exact ⟨this, List.all_eq_true.1 hp _ (hmemf h hh)⟩
  have hnews : fs.map (fun f => Global.fn f.name.name none) = heads.map fun h => Global.fn h.fn.name none := by
    rw [← hmap, List.map_map]; exact List.map_congr_left fun h hh => by simp [hname h hh]
  obtain ⟨hstep, hgrow, htl⟩ := fixTaint_full _ _ _ rfl h2
  simp only [List.length_map] at hstep hgrow htl
  have hgg : ∀ n, (setSigs (updSigs heads (st.globals ++ fs.map fun f => Global.fn f.name.name none)) heads
      taint).find? (·.name == n) = (groupGlobals st heads taint).find? (·.name == n) := by
    rw [hnews]; exact group_find hnd' hfr' htl
  obtain ⟨hlen, hall⟩ := checkAll_spec hstep
  have hpad : ∀ h ∈ heads, h.fn.subterms.length ≤ (heads.map fun h => h.fn.subterms.length).foldr max 0 :=
    fun h hh => le_foldr_max (List.mem_map_of_mem hh)
  have hclean : ∀ p ∈ heads.zip bodies, (p.1, false) ∈ heads.zip taint → ∀ x ∈ p.2.res, x.tainted = false := by
    intro p hp hpt x hx
    obtain ⟨i, -, h2, h3⟩ := zip_index hnd' hp hpt
    refine Bool.eq_false_iff.2 fun hxt => grows_eq_false hgrow i h3 ?_
    rw [List.getElem?_map, h2]
    simpa using ⟨x, hx, hxt⟩
  exact group_post hI hlen htl (fun h hh => (hspec' h hh).1) hnd' hfr' hpad
    (fun ht => ⟨hI, hI.live ht, ht, hlen, htl, hspec', hnd', hfr', hpad,
      fun p hp => ⟨_, rfl, rfl, rfl, hgg, hall p hp⟩, hclean⟩) rfl rfl rfl rfl rfl rfl rfl rfl hgg

end FnGroup

end Pledge
