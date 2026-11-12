import Pledge.Sound.Match

namespace Pledge.Erased

/-- The scrutinee of an erased `match` or pattern `let` (§16), checked in an erased position: its tree is removed,
and in an untainted scope after it, its result has an ideal value. -/
theorem scrut {s : Expr} (ihs : ExprSound s) (ihss : ExprShape s) {C : Ctx} {sc : Scope} {n0 : Nat} {W : World}
    {ρ : List Value} {act : Act} {so : Out} {r : Res} {pl : String} {it : Bool} {pos : Pos} (hI : Inv C sc n0 W ρ act)
    (h : checkExpr { C with erased := true, place := pl, inType := it } sc none s = .ok so)
    (hr : single pos so.res = .ok r) (ht : so.sc.taintedBy = none) :
    so.tree = .removed ∧ so.sc.names = sc.names ∧ sc.Γ.eraseRules <+: so.sc.Γ.eraseRules ∧
      ∃ ρ₁ v, Inv C so.sc n0 W (ρ ++ ρ₁) act ∧ r.term.eval (ρ ++ ρ₁) [] = some v ∧ ResOk W.Sc r v := by
  have htree := (checkExpr_removed h).2.2.1 rfl
  obtain ⟨-, hn, -, hpre, -⟩ := ihss _ _ _ _ (by exact hI.solving) hI.holes h
  obtain ⟨ρ₁, vs, hI₁, hvs, hres, -, -⟩ := (ihs { C with erased := true, place := pl, inType := it } _ _ _ _ _ _ _
    (hI.congr_ctx rfl rfl rfl) (by simp) h).1 ht
  rw [single_ok hr] at hvs hres
  obtain ⟨v, vs', hv, hvs', rfl⟩ := Term.evalList_cons_eq_some.1 hvs
  exact ⟨htree, hn, hpre, ρ₁, v, hI₁.congr_ctx rfl rfl rfl, hv, hres 0 r v (by simp) rfl⟩

/-- Binding an erased pattern's fields to `removed` (§16) keeps the run-time environment related. -/
theorem envRel_erased {C : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {act : Act} {env : Env}
    {c : String} {ws : List Value} {sig : Sig} {Γ' : Entries} {ids : List Nat} {pat : Pattern} {tb : Option Pos}
    {hs : List Hole} (hI : Inv C sc n0 W ρ act) (hE : EnvRel W.Sc C.phase sc ρ env)
    (hsig : sc.sigs.find ⟨.ctor, c⟩ = some sig) (hpre : sc.Γ.eraseRules <+: Γ'.eraseRules)
    (hids : ids = List.range' sc.Γ.length ws.length) (hfl : pat.fields.length = ws.length)
    (hent : ∀ (k : Nat) (b : TBinder), sig.params[k]? = some b → ∃ en, Γ'[sc.Γ.length + k]? = some en ∧
      en.tainted = false ∧ en.erased = (b.mult == .erased || true)) (hpat : pat.ctor.name = c)
    (hwl : ws.length = sig.params.length) :
    ∃ env', bindPattern env (some .erased) pat .removed = .ok env' ∧
      EnvRel W.Sc C.phase (Scope.bind { sc with Γ := Γ', taintedBy := tb, holes := hs } pat.fields (fieldRes ids))
        (ρ ++ ws) env' := by
  obtain ⟨sig', hsig', hm⟩ := (hI.sigsClose []).mults hsig
  have hl := congrArg List.length hm
  simp only [List.length_map] at hl
  refine EnvRel.pattern hE hI.sat.1.1 hpre hids hfl hsig' (fun k b hb => ?_) (fun h => (h rfl).elim) hpat
    (hwl.trans hl.symm)
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, sig.params[k]? = some b₀ :=
    ⟨_, List.getElem?_eq_getElem (hl ▸ (List.getElem?_eq_some_iff.1 hb).1)⟩
  obtain ⟨en, hen, -, her⟩ := hent k b₀ hb₀
  exact ⟨en, hen, by simp [her]⟩

theorem patlet {p : Pos} {ct : Bool} {pat : Pattern} {rhs : Expr} (ih : ExprSound rhs) (ihs : ExprShape rhs) :
    StmtSound (.patlet p ct (some .erased) pat rhs) := by
  intro C sc n0 W ρ act o hI h
  have he : (some Mult.erased == some Mult.erased) = true := rfl
  simp only [checkStmt, he, Bool.and_true, ↓reduceIte, Bool.or_true] at h
  cases ct
  case true => simp [failAt_eq, bind, Except.bind] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨u, -, h⟩ := bind_eq_ok.1 h
  obtain ⟨u', -, h⟩ := bind_eq_ok.1 h
  obtain ⟨so, hso, h⟩ := bind_eq_ok.1 h
  rw [keep_ok] at h
  rw [closed_eq hI.holes fun o h => (ihs _ sc none o (by exact hI.solving) hI.holes h).2.2.1] at hso
  obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
  obtain ⟨fs, hfs, h⟩ := bind_eq_ok.1 h
  obtain ⟨sc', hsc', h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨Γ, ids, ⟨f, hf1, hf2⟩, hone, rfl⟩ := patBind_spec hsc'
  intro ht
  obtain ⟨ht₁, hrt⟩ := MatchMany.reach_eq_none (by simpa [Scope.bind_eq] using ht)
  obtain ⟨htree, hn, hpre₁, ρ₁, v, hI₁, hv, -, -, hV⟩ := scrut ih ihs hI hso hr ht₁
  obtain ⟨V, hV⟩ := hV hrt
  obtain ⟨c, ws, sig, Γ', ids', pat', rfl, hfc, hsig, hws, hsat, hpre, -, hids, -, hent⟩ :=
    forcings_value hI₁ hfs hv hV
  obtain rfl : c = pat.ctor.name := Decidable.byContradiction fun hne =>
    hone rfl _ (List.mem_of_find?_eq_some hfc) hne Γ' ids' rfl
  rw [hfc] at hf1
  cases hf1
  simp only [Forced.ok.injEq] at hf2
  obtain ⟨rfl, rfl⟩ := hf2
  have hfl := forcings_fields hfs (List.mem_singleton_self _) hsig hws
  refine ⟨ρ₁ ++ ws, by simpa using hI₁.pattern hsat hids hws (tb := reach so.sc r rhs.pos) (by
    simp [reach, ht₁, hrt]) hI₁.holes, fun _ _ env hE => ?_⟩
  obtain ⟨env', hb, hE'⟩ := envRel_erased hI₁ (hE.extend ρ₁ hn hpre₁ hI.sat.1.1) hsig hpre hids hfl hent rfl
    hws.length_eq
    (tb := reach so.sc r rhs.pos) (hs := so.sc.holes)
  exact ⟨env', .patlet (by rw [htree]; exact .removed) rfl hb, by simpa using hE'⟩

theorem filterMap_none {α β : Type} (Q : α → Bool) {xs : List α} (ys : List β)
    (h : (xs.filter fun x => !Q x) = []) : (xs.zip ys).filterMap (fun q => if Q q.1 then none else some q.2) = [] := by
  refine List.filterMap_eq_nil_iff.2 fun ⟨x, y⟩ hq => ?_
  have := List.filter_eq_nil_iff.1 h x (List.of_mem_zip hq).1
  simp only [Bool.not_eq_true', Bool.not_eq_false] at this
  simp [this]

/-- When at most one element is live (not `Q`), keeping the partners of the live elements keeps one. -/
theorem filterMap_live {α β : Type} (Q : α → Bool) : ∀ {xs : List α} {ys : List β} {j : Nat} {x : α} {y : β},
    xs.length = ys.length → (xs.filter fun x => !Q x)[1]? = none → xs[j]? = some x → ys[j]? = some y →
      Q x = false → (xs.zip ys).filterMap (fun q => if Q q.1 then none else some q.2) = [y]
  | [], _, _, _, _, _, _, hx, _, _ => by simp at hx
  | _ :: _, [], _, _, _, hl, _, _, _, _ => by simp at hl
  | x₀ :: xs, y₀ :: ys, 0, x, y, hl, h1, hx, hy, hq => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
    subst hx hy
    simp only [List.filter_cons, hq, Bool.not_false, ↓reduceIte, List.getElem?_cons_succ,
      List.getElem?_eq_none_iff, Nat.le_zero, List.length_eq_zero_iff] at h1
    simp [hq, filterMap_none Q ys h1]
  | x₀ :: xs, y₀ :: ys, j + 1, x, y, hl, h1, hx, hy, hq => by
    simp only [List.getElem?_cons_succ] at hx hy
    cases hq₀ : Q x₀
    · simp only [List.filter_cons, hq₀, Bool.not_false, ↓reduceIte, List.getElem?_cons_succ,
        List.getElem?_eq_none_iff, Nat.le_zero, List.length_eq_zero_iff] at h1
      have := List.filter_eq_nil_iff.1 h1 x (List.mem_of_getElem? hx)
      simp [hq] at this
    · simp only [List.filter_cons, hq₀, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
      simpa [hq₀] using filterMap_live Q (by simpa using hl) h1 hx hy hq

theorem teleOk_imp_lt {S : Sigs} {ρ : List Value} :
    ∀ {f g : Nat → Bool} {Δ : Telescope} {env vs : List Value}, TeleOk S ρ f Δ env vs →
      (∀ k < Δ.length, g k = true → f k = true) → TeleOk S ρ g Δ env vs
  | _, _, [], _, [], _, _ => trivial
  | _, _, _ :: _, _, _ :: _, ⟨⟨A, hA, h1, h2, h3⟩, his, ht⟩, hfg =>
    ⟨⟨A, hA, h1, h2, fun h => h3 (hfg 0 (by simp) h)⟩, his,
      teleOk_imp_lt ht fun k hk => hfg (k + 1) (by simpa using hk)⟩
  | _, _, [], _, _ :: _, h, _ | _, _, _ :: _, _, [], h, _ => h.elim

theorem allErased_of {g : Given} (hl : 0 < g.wants.length)
    (h : ∀ i < g.wants.length, g.erasedAt i = true) : g.allErased = true := by
  have hall : ∀ w ∈ g.wants, (w.mult == .erased) = true := fun w hw => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    simpa [Given.erasedAt, List.getElem?_eq_getElem hi] using h i hi
  simp only [Given.allErased, Bool.and_eq_true, List.any_eq_true, List.all_eq_true]
  exact ⟨⟨_, List.getElem_mem hl, hall _ (List.getElem_mem hl)⟩, hall⟩

/-- What a position is given, with its multiplicities erased when the position is (§16), has the same environment
and, but for multiplicities, the same wants. -/
theorem erase_some {C : Ctx} {g : Option Given} {G : Given} (hG : g = some G) :
    ∃ G', (if C.erased then g.map (·.erase) else g) = some G' ∧ G'.env = G.env ∧
      G'.wants.length = G.wants.length ∧ ∀ (i : Nat) (w w' : Want), G'.wants[i]? = some w →
        G.wants[i]? = some w' → w.type = w'.type ∧ w.is = w'.is := by
  subst hG
  split
  · exact ⟨_, rfl, rfl, by simp [Given.erase], MatchMany.erase_wants⟩
  · exact ⟨_, rfl, rfl, rfl, fun i w w' h h' => by rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩⟩

/-- The wants a `match` gives its branches are its annotation's, but for multiplicities (§16). -/
theorem mapIdx_wants (tele : Telescope) (f : Nat → TBinder → Mult) :
    (tele.map Want.of).length = (tele.mapIdx fun i b => { Want.of b with mult := f i b }).length ∧
      ∀ (k : Nat) (w w' : Want), (tele.map Want.of)[k]? = some w →
        (tele.mapIdx fun i b => { Want.of b with mult := f i b })[k]? = some w' →
          w.type = w'.type ∧ w.is = w'.is := by
  refine ⟨by simp, fun k w w' h h' => ?_⟩
  simp only [List.getElem?_map, List.getElem?_mapIdx] at h h'
  cases hk : tele[k]? <;> simp only [hk, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at h h'
  subst h h'
  exact ⟨rfl, rfl⟩

theorem «match» {p : Pos} {s : Expr} {ann : Tele} {bs : List Branch}
    (ihs : ExprSound s) (ihss : ExprShape s) (ihb : ∀ b ∈ bs, ExprSound b.body) (ihbs : ∀ b ∈ bs, ExprShape b.body) :
    ExprSound (.match p (some .erased) s ann bs) := by
  intro C sc g n0 W ρ act o hI hg hc
  unfold checkExpr at hc
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 hc
  clear hc
  have he : (some Mult.erased == some Mult.erased) = true := rfl
  simp only [he, Bool.or_true, ↓reduceIte, Bool.true_and] at h₀
  obtain ⟨so, hso, h₀⟩ := bind_eq_ok.1 h₀
  rw [keep_ok] at h₀
  rw [closed_eq hI.holes fun o h => (ihss _ sc none o (by exact hI.solving) hI.holes h).2.2.1] at hso
  obtain ⟨r, hr, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨⟨tele, tenv⟩, hann, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨fs, hfs, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨u, -, h₀⟩ := bind_eq_ok.1 h₀
  simp only at h₀
  split at h₀
  case isFalse => simp [failAt_eq, bind, Except.bind] at h₀
  rename_i hmiss
  split at h₀
  split at h₀
  · simp [failAt_eq, bind, Except.bind] at h₀
  all_goals
    have hlive : tele.any (·.mult == .many) = true → (bs.filter fun b => !b.body.absurd)[1]? = none := by
      first
        | exact fun h => absurd h ‹_›
        | exact fun _ => by
            cases h : (bs.filter fun b => !b.body.absurd)[1]? with
            | none => rfl
            | some second =>
              exact (‹∀ second, (bs.filter fun b => !b.body.absurd)[1]? = some second → False› second h).elim
  all_goals
    obtain ⟨u, hens, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨bo, hbo, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨o₁, ho₁, h₀⟩ := bind_eq_ok.1 h₀
    simp only [pure, Except.pure, Except.ok.injEq] at h₀
    subst h₀
    have hens := ensure_ok hens
    simp only [Bool.and_eq_true, List.all_eq_true] at hens
    rw [keep_ok] at ho₁
    obtain ⟨-, hn, hsoh, hpre₁, -⟩ := ihss _ _ _ _ (by exact hI.solving) hI.holes hso
    have hprod := ho₁
    obtain rfl := produced_eq (show (opened so.sc tele tenv "match" p _).1.holes = [] from hsoh) ho₁
    obtain ⟨hne, hsc, -, hres, htree, herase⟩ := finish_spec hf
    simp only at hne hsc hres htree herase
    generalize htaint : (fun i : Nat => r.tainted ||
      bo.outs.any fun o : Out => ((o.res[i]?).map fun x : Res => x.tainted).getD false) = t at *
    have hos : o.sc.taintedBy = so.sc.taintedBy := by rw [hsc]; rfl
    by_cases hut : so.sc.taintedBy = none
    case neg => exact ⟨fun h => absurd (hos ▸ h) hut, fun h => absurd (hos ▸ h) hut⟩
    have hores : o.res = (opened so.sc tele tenv "match" p t).2 := by
      rw [hres, opened_fst]; simp [hut]
    obtain ⟨htree_s, -, -, ρ₁, v, hI₁, hv, hrv⟩ := scrut ihs ihss hI hso hr hut
    obtain ⟨envv, henv, hcons⟩ := annotation_cons hI₁.termInv.weak
      (fun g' h => MatchMany.givenOk_frame (MatchMany.given_erased (C := C) hg g' h).1 ρ₁) (by exact hI₁.solving) hann
    obtain ⟨-, -, hrsl, hrs⟩ := opened_shape so.sc tele tenv "match" p t
    have hlen : ∀ G, g = some G → o.res.length = G.wants.length := fun G hG => by
      obtain ⟨G', hG', -, hl, -⟩ := erase_some (C := C) hG
      rw [hG'] at hprod
      rw [hores, (MatchMany.produced_length hprod).2, hl]
    have common : ∀ vsb, TeleOk W.Sc (ρ ++ ρ₁) (fun k => !t k) tele envv vsb →
        (C.inType = false → ∀ env, EnvRel W.Sc C.phase sc ρ env → ∃ us, Eval W.P env o.tree us ∧
          ResRel W.Sc C.phase (C.posMult g) o.res vsb us) → ExprPost C sc g n0 W ρ act o := by
      intro vsb hok hrun _
      obtain ⟨hsat', hevs⟩ := opened_sound (kind := "match") (pos := p) hI₁.sat henv hok
      have hresok : ∀ (i : Nat) (r : Res) (v : Value), (opened so.sc tele tenv "match" p t).2[i]? = some r →
          vsb[i]? = some v → ResOk W.Sc r v := by
        intro i r' v' hr' hv'
        obtain ⟨h1, h2, h3⟩ := MatchMany.TeleOk.getElem hok _ _ hv'
        obtain ⟨b, hb⟩ : ∃ b, tele[i]? = some b :=
          ⟨_, List.getElem?_eq_getElem (hrsl ▸ (List.getElem?_eq_some_iff.1 hr').1)⟩
        rw [(hrs i b hb).1] at hr'
        cases hr'
        exact ⟨h1, h2, fun ht => h3 (by simpa using ht)⟩
      have hI₂ := hI₁.extend hsat' (sc' := (opened so.sc tele tenv "match" p t).1) rfl rfl hsoh hut
      refine ⟨ρ₁ ++ vsb, vsb, by rw [hsc, ← List.append_assoc]; exact hI₂,
        by rw [hores, ← List.append_assoc]; exact hevs, by rw [hores]; exact hresok, ?_, hrun⟩
      intro G hG envG henvG
      obtain ⟨G', hG', henvG', hl, hw⟩ := erase_some (C := C) hG
      rw [hG'] at hprod
      have hok' := ResOks.of_getElem (by rw [Term.length_evalList hevs, List.length_map]) hresok
      obtain ⟨-, hwG⟩ := produced_sound hsat'.1 (hI₁.sigsClose vsb) hI₁.noJunk hsoh hevs hok'
        (fun g'' h'' => by
          cases h''
          obtain ⟨envv', he'⟩ := (hg G hG).env
          exact ⟨envv', by rw [henvG', List.append_assoc]; exact Term.evalList_frame_ρ _ he'⟩) hprod
      rw [hores, ← List.append_assoc]
      exact MatchMany.wantsSat_congr hl hw
        (hwG G' rfl envG (by rw [henvG', List.append_assoc]; exact Term.evalList_frame_ρ _ henvG)).2
    by_cases hall : ∀ i < tele.length, t i = true
    · obtain ⟨vsb, hvsb⟩ := WantsCons.open hcons
      have hok : TeleOk W.Sc (ρ ++ ρ₁) (fun k => !t k) tele envv vsb :=
        teleOk_imp_lt (WantsSat.teleOk (fun _ => false) hvsb (by simp)) fun k hk h => by simp [hall k hk] at h
      have hallr : ∀ r ∈ o.res, r.tainted = true := by
        intro r' hr'
        rw [hores] at hr'
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr'
        obtain ⟨b, hb⟩ : ∃ b, tele[i]? = some b := ⟨_, List.getElem?_eq_getElem (hrsl ▸ hi)⟩
        have h1 := (hrs i b hb).1
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at h1
        rw [h1]
        exact hall i (hrsl ▸ hi)
      have hrm : (C.erased || g.any (·.allErased) || o.res.all (·.tainted)) = true := by
        simp [List.all_eq_true.2 hallr]
      exact ⟨common vsb hok fun _ env _ => ⟨[.removed], by rw [htree]; simp only [hrm, ↓reduceIte]; exact .removed,
        MatchMany.resRel_whole hrm hlen⟩, fun _ _ => hallr⟩
    obtain ⟨i, hi, hti⟩ : ∃ i < tele.length, t i = false := Classical.byContradiction fun h => hall fun i hi => by
      cases hti : t i
      · exact absurd ⟨i, hi, hti⟩ h
      · rfl
    have hto : ∀ k, t k = false →
        r.tainted = false ∧ ∀ o ∈ bo.outs, ((o.res[k]?).map (·.tainted)).getD false = false := fun k hk => by
        rw [← htaint] at hk
        simp only [Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at hk
        exact hk
    obtain ⟨hrt, -⟩ := hto i hti
    obtain ⟨V, hV⟩ := hrv.2.2 hrt
    obtain ⟨c, ws, sig, Γ', ids', pat', rfl, hfc, hsig, hws, hsat, hpre, -, hids, hpat, hent⟩ :=
      forcings_value hI₁ hfs hv hV
    obtain ⟨b, hb, hbn⟩ : ∃ b ∈ bs, b.pat.ctor.name = c := by
      have := List.filter_eq_nil_iff.1 (List.map_eq_nil_iff.1 (List.isEmpty_iff.1 hmiss)) _
        (List.mem_of_find?_eq_some hfc)
      cases hp' : pat' with
      | none => simp [hp'] at this
      | some p0 =>
        rw [hp'] at hpat
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hpat.symm)
        exact ⟨b, hb, by simpa using List.find?_some hpat.symm⟩
    obtain ⟨j, hjl, hjb⟩ := List.getElem_of_mem hb
    have hbj : bs[j]? = some b := by rw [List.getElem?_eq_getElem hjl, hjb]
    obtain ⟨hol, htr, hbr⟩ := MatchMany.checkBranches_spec hbo
    obtain ⟨ob, hobj⟩ : ∃ ob, bo.outs[j]? = some ob := ⟨_, List.getElem?_eq_getElem (hol ▸ hjl)⟩
    have htl : bo.trees.length = bs.length := by simp [htr, hol]
    have hzj : (bs.zip bo.outs)[j]? = some (b, ob) := List.getElem?_zip_eq_some.2 ⟨hbj, hobj⟩
    have htrj : bo.trees[j]? = some (.mk b.pat ob.tree) := by simp [htr, hzj]
    obtain ⟨Γb, idsb, hsurv, hcheck⟩ := hbr b ob (List.mem_of_getElem? hzj)
    rw [closed_eq (by rw [Scope.bind_eq]) fun o h =>
      (ihbs b hb _ _ _ o (by exact hI.solving) (by rw [Scope.bind_eq]) h).2.2.1] at hcheck
    obtain ⟨f, hf1, hf2⟩ := survivor_spec hsurv
    rw [hbn, hfc] at hf1
    cases hf1
    simp only [Forced.ok.injEq] at hf2
    obtain ⟨rfl, rfl⟩ := hf2
    have hsig' : so.sc.sigs.find ⟨.ctor, b.pat.ctor.name⟩ = some sig := by rw [hbn]; exact hsig
    have hfl := forcings_fields hfs (List.mem_map_of_mem hb) hsig' hws
    have hreach : reach so.sc r s.pos = none := by simp [reach, hut, hrt]
    have hIb := (hI₁.pattern hsat hids hws hreach (hs := []) (fields := b.pat.fields) rfl).congr_ctx
      (C' := C.enter (C.erased || g.any (·.allErased))) rfl rfl rfl
    obtain ⟨hpostb, habsb⟩ := ihb b hb _ _ _ n0 W _ act ob hIb (by
      rintro g'' ⟨⟩
      refine ⟨⟨envv, Term.evalList_frame_ρ ws henv⟩, fun _ envv' he' => ?_⟩
      rw [Term.evalList_frame_ρ ws henv, Option.some.injEq] at he'
      subst he'
      exact WantsCons.congr (mapIdx_wants tele _).1 (mapIdx_wants tele _).2 (hcons.frame ws)) hcheck
    have hobl : ob.res.length = tele.length := by rw [MatchMany.checkExpr_length _ hcheck]; simp
    have hob : ∀ k < tele.length, t k = false → ∃ rk, ob.res[k]? = some rk ∧ rk.tainted = false :=
      fun k hk ht => by
      have hk' := (hto k ht).2 ob (List.mem_of_getElem? hobj)
      have hrk : ob.res[k]? = some ob.res[k] := List.getElem?_eq_getElem (hobl ▸ hk)
      exact ⟨_, hrk, by simpa [hrk] using hk'⟩
    obtain ⟨ri, hri, hriu⟩ := hob i hi hti
    have hobu : ob.sc.taintedBy = none := by
      cases h : ob.sc.taintedBy with
      | none => rfl
      | some _ =>
        have := ((checkExpr_removed hcheck).2.1 (by simp [h])).2 ri (List.mem_of_getElem? hri)
        simp [hriu] at this
    have hnab : b.body.absurd = false := by
      cases h : b.body.absurd
      · rfl
      · have := habsb hobu h ri (List.mem_of_getElem? hri)
        simp [hriu] at this
    obtain ⟨ρ₂, vsb, -, -, -, hwb, hrunb⟩ := hpostb hobu
    have hw0 := hwb _ rfl envv (Term.evalList_frame_ρ ws henv)
    have hwt := MatchMany.wantsSat_congr (ws' := tele.map Want.of) (mapIdx_wants tele _).1.symm
      (fun k w w' h h' => let ⟨a, b⟩ := (mapIdx_wants tele _).2 k w' w h' h; ⟨a.symm, b.symm⟩) hw0
    have hok0 := WantsSat.teleOk (fun k => ((ob.res.map (!·.tainted))[k]?).getD false) hwt fun k h => by
      revert h
      cases (ob.res.map (!·.tainted))[k]? <;> simp
    have hok1 := MatchMany.TeleOk.restrict (n := so.sc.Γ.length) (ρ' := ρ ++ ρ₁)
      (by rw [← hI₁.sat.1.1, List.append_assoc (ρ ++ ρ₁), List.take_left, List.take_length])
      (List.all_eq_true.2 hens.1) hok0
    have hok : TeleOk W.Sc (ρ ++ ρ₁) (fun k => !t k) tele envv vsb := teleOk_imp_lt hok1 fun k hk h => by
      obtain ⟨rk, hrk, hrku⟩ := hob k hk (by simpa using h)
      simp [hrk, hrku]
    have habs : (Expr.match p (some .erased) s ann bs).absurd = false := by
      obtain ⟨b0, bs0, h⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hb)
      rw [h]; rfl
    refine ⟨common vsb hok fun hit env hE => ?_, fun _ hab => absurd hab (by simp [habs])⟩
    by_cases hrm : (C.erased || g.any (·.allErased) || o.res.all (·.tainted)) = true
    · exact ⟨[.removed], by rw [htree]; simp only [hrm, ↓reduceIte]; exact .removed,
        MatchMany.resRel_whole hrm hlen⟩
    rw [htree]
    simp only [hrm, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.or_eq_true, not_or] at hrm
    obtain ⟨⟨hC, hga⟩, -⟩ := hrm
    have hC' : C.erased = false := by simpa using hC
    have hwf : (C.erased || g.any (·.allErased)) = false := by simp [hC, hga]
    have hpos : 0 < tele.length := by rw [← hrsl]; exact List.length_pos_iff.2 hne
    have hmany : tele.any (·.mult == .many) = true := by
      refine Classical.byContradiction fun hnm => ?_
      have hgk : ∀ k < tele.length, g.any (·.erasedAt k) = true := fun k hk => by
        obtain ⟨bk, hbk⟩ : ∃ bk, tele[k]? = some bk := ⟨_, List.getElem?_eq_getElem hk⟩
        have hek : bk.mult = .erased := by
          cases hm : bk.mult
          · exact absurd (List.any_eq_true.2 ⟨bk, List.mem_of_getElem? hbk, by simp [hm]⟩) hnm
          · rfl
        simpa [hC'] using herase hwf k _ (by rw [hores]; exact (hrs k bk hbk).1) (by simp [hek])
      cases g with
      | none => simpa using hgk 0 hpos
      | some G =>
        have hGl : G.wants.length = tele.length := by rw [← hlen G rfl, hores, hrsl]
        exact hga (by simpa using allErased_of (hGl ▸ hpos) fun k hk => by simpa using hgk k (hGl ▸ hk))
    rw [filterMap_live (fun b : Branch => b.body.absurd) htl.symm (hlive hmany) hbj htrj hnab]
    obtain ⟨env', hbind, hE'⟩ := envRel_erased hI₁ (hE.extend ρ₁ hn hpre₁ hI.sat.1.1) hsig' hpre hids hfl hent
      rfl hws.length_eq (tb := reach so.sc r s.pos) (hs := [])
    obtain ⟨us, hev, us', htake, hrel⟩ := hrunb hit env' hE'
    rw [hobl] at htake
    obtain ⟨us₂, hat, htake₂⟩ := annotation_annTake hann htake
    refine ⟨us₂, .match (by rw [htree_s]; exact .removed) rfl (pickBranch_erased _ _) hbind hev hat, us',
      by rw [hores, hrsl]; exact htake₂, fun k rk a vk hrk ha hvk htk => ?_⟩
    rw [hores] at hrk
    have hk : k < tele.length := hrsl ▸ (List.getElem?_eq_some_iff.1 hrk).1
    obtain ⟨bk, hbk⟩ : ∃ bk, tele[k]? = some bk := ⟨_, List.getElem?_eq_getElem hk⟩
    rw [(hrs k bk hbk).1, Option.some.injEq] at hrk
    subst hrk
    obtain ⟨rbk, hrbk, hrbku⟩ := hob k hk (by simpa using htk)
    have hm := hrel k rbk a vk hrbk ha hvk hrbku
    cases hgk : g.any (·.erasedAt k)
    · have hbm : bk.mult = .many := by
        cases hm' : bk.mult
        · rfl
        · have := herase hwf k _ (by rw [hores]; exact (hrs k bk hbk).1) (by simp [hm'])
          simp [hC', hgk] at this
      have ht : C.posMult g k = .many := by simp [Ctx.posMult, hC', hgk]
      rw [ht]
      have hgk' : g.any (fun x => (x.wants[k]?).any (·.mult == .erased)) = false := hgk
      simpa [Ctx.posMult, hC', hga, Given.erasedAt, List.getElem?_mapIdx, hbk, hgk', hbm] using hm
    · have ht : C.posMult g k = .erased := by simp [Ctx.posMult, hgk]
      rw [ht]
      exact MultRel.erased hm.approx

end Pledge.Erased
