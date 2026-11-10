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

/-- After a group's heads are checked and its bodies to the taint fixed point `taint` (§12), a name resolves as
among the earlier globals followed by the group's functions with their signatures, tainted as `taint` says. -/
theorem group_find {gs : List Global} {heads : List FnHead} {taint : List Bool} (hnd : (heads.map (·.fn.name)).Nodup)
    (hfr : ∀ h ∈ heads, gs.find? (·.name == h.fn.name) = none) (hl : taint.length = heads.length) (n : String) :
    (setSigs (updSigs heads (gs ++ heads.map fun h => Global.fn h.fn.name none)) heads taint).find? (·.name == n) =
      (gs ++ (heads.zip taint).map fun p : FnHead × Bool => Global.fn p.1.fn.name (some { p.1.sig with tainted := p.2 })).find?
        (·.name == n) := by
  sorry

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

/-- A tainted function's head still gives what `FnOk` asks of every function (§12): a tainted call opens the
returns to `junk` or their `is` clauses' values (`telescope_wsound`, `telescope_cons`). -/
theorem HeadSpec.cons {sc : Scope} {names : List String} {h : FnHead} (hs : HeadSpec sc names h) {Sc : Sigs}
    {ρ : List Value} (hT : WTermInv sc sc.Γ.length Sc ρ) (pvals : List Value)
    (hp : WantsSat Sc ρ (h.sig.params.map Want.of) [] (h.sig.params.map fun _ => false) pvals) :
    WantsCons Sc ρ (h.sig.returns.map Want.of) pvals := by
  sorry

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

/-- The taint fixed point (§12): the bodies of the last round are checked with the final taint, and no function
untainted in it has a tainted result. -/
theorem fixTaint_spec {step : List Bool → CheckM (List Out)} :
    ∀ {t : List Bool} {r : List Bool × List Out}, fixTaint step t = .ok r →
      step r.1 = .ok r.2 ∧ grows r.1 (r.2.map fun o => o.res.any (·.tainted)) = false := by
  sorry

theorem grows_eq_false {ts ns : List Bool} (h : grows ts ns = false) :
    ∀ (i : Nat), ts[i]? = some false → ns[i]? = some true → False := by
  sorry

theorem evalList_range' : ∀ (pre vs : List Value),
    Term.evalList (pre ++ vs) [] ((List.range' pre.length vs.length).map .entry) = some vs
  | _, [] => rfl
  | pre, v :: vs => by
    have := evalList_range' (pre ++ [v]) vs
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at this
    simp only [List.length_cons, List.range'_succ, List.map_cons]
    refine Term.evalList_cons_eq_some.2 ⟨v, vs, ?_, this, rfl⟩
    simp [Term.eval]

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

/-- One activation of an untainted function of a group (SOUNDNESS.md Lemma 6.1 and Theorem 6.2, parts 5 and 9):
given that every untainted function of the group meets its specification from this activation, the body's ideal
results satisfy the returns (the main lemma, ideal part), and the body runs on run-time arguments related to the
ideal ones to related results (the main lemma, run-time part). -/
theorem GroupOk.step {st : TopState} {ρ : List Value} {heads : List FnHead} {bodies : List Out} {taint : List Bool}
    {pad : Nat} (G : GroupOk st ρ heads bodies taint pad) {W : World} (hW : (st.world ρ).Le W)
    (hfind : ∀ p ∈ heads.zip bodies, W.P.fns.find p.1.fn.name = some (mkDef st pad p))
    {p : FnHead × Out} (hp : p ∈ heads.zip bodies) (hpt : (p.1, false) ∈ heads.zip taint) {vs : List Value}
    (hvs : TeleSat W.Sc W.ρ p.1.sig.params [] vs)
    (ih : ∀ q ∈ heads.zip bodies, (q.1, false) ∈ heads.zip taint →
      CallSpec W st.phase (mkDef st pad q) q.1.sig (calleeAct (mkDef st pad p) vs)) :
    ∃ rs, TeleSat W.Sc W.ρ p.1.sig.returns vs rs ∧ ∀ as, MultsRel W.Sc st.phase (p.1.sig.params.map (·.mult)) as vs →
      ∃ rs', CallRel W.P (mkDef st pad p) as rs' ∧ MultsRel W.Sc st.phase (p.1.sig.returns.map (·.mult)) rs' rs := by
  sorry

/-- Every untainted function of a checked group meets its specification in every later world (SOUNDNESS.md part
6), by well-founded induction on the measure of its activations' ideal arguments. -/
theorem GroupOk.fnSpec {st : TopState} {ρ : List Value} {heads : List FnHead} {bodies : List Out}
    {taint : List Bool} {pad : Nat} (G : GroupOk st ρ heads bodies taint pad) {W : World} (hW : (st.world ρ).Le W)
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
  exact G.step hW hfind hp hpt hvs fun q hq hqt vs' hvs' hlt => ih _ hlt q hq hqt vs' hvs' rfl

theorem kindOf_some {gs : List Global} {n : String} {k : HeadKind} (h : kindOf gs n = some k) :
    ∃ g, gs.find? (·.name == n) = some g := by
  unfold kindOf at h
  split at h <;> first | (cases h; done) | exact ⟨_, ‹_›⟩

/-- A group of functions keeps the top level's invariant (SOUNDNESS.md part 6, with the main lemma for 5.1): the
world extends, and, in an untainted scope, every untainted function meets its specification; in a tainted scope
every function is tainted (§12). -/
theorem fnGroup_ok {st st' : TopState} {ρ : List Value} {fs : List Fn} (hI : TopInv st ρ)
    (hp : fs.all (·.body.holeFree) = true) (h : fnGroup st fs = .ok st') :
    (st.world ρ).Le (st'.world ρ) ∧ TopInv st' ρ := by
  sorry

end FnGroup

end Pledge
