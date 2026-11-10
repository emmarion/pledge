import Pledge.Sound.Match

namespace Pledge.Simple

/-- What `checkExpr` passes on of what its position is given: in an erased position, every entry erased. -/
abbrev given (C : Ctx) (g : Option Given) : Option Given := if C.erased then g.map (·.erase) else g

abbrev whole (C : Ctx) (g : Option Given) : Bool := C.erased || g.any (·.allErased)

theorem wantsSat_congr {S : Sigs} {ρ : List Value} (f : Want → Want)
    (hf : ∀ w, (f w).type = w.type ∧ (f w).is = w.is) :
    ∀ {ws : List Want} {env : List Value} {ts : List Bool} {vs : List Value},
      WantsSat S ρ (ws.map f) env ts vs → WantsSat S ρ ws env ts vs
  | [], _, [], [], _ => trivial
  | w :: ws, _, _ :: _, _ :: _, ⟨h1, h2⟩ =>
    ⟨⟨fun T hT => h1.1 T (by rw [(hf w).1]; exact hT), fun e he => h1.2 e (by rw [(hf w).2]; exact he)⟩,
      wantsSat_congr f hf h2⟩
  | [], _, [], _ :: _, h | [], _, _ :: _, _, h | _ :: _, _, [], _, h | _ :: _, _, _ :: _, [], h => h.elim

theorem given_ok {C : Ctx} {S : Sigs} {ρ : List Value} {g : Option Given} (hg : ∀ g', g = some g' → g'.Ok S ρ) :
    ∀ g', given C g = some g' → g'.Ok S ρ := by
  intro g' h
  simp only [given] at h
  split at h
  · cases g with
    | none => cases h
    | some g₀ =>
      cases h
      obtain ⟨he, hc⟩ := hg g₀ rfl
      exact ⟨he, fun hw envv henv => WantsCons.congr (by simp [Given.erase])
        (fun i w w' h1 h2 => by
          simp only [Given.erase, List.getElem?_map, h1, Option.map_some, Option.some.injEq] at h2
          subst h2; exact ⟨rfl, rfl⟩) (hc hw envv henv)⟩
  · exact hg g' h

theorem given_wants {C : Ctx} {S : Sigs} {ρ ρ' : List Value} {g : Option Given} {ts : List Bool} {vs : List Value}
    (h : ∀ g', given C g = some g' → ∀ envv, Term.evalList ρ [] g'.env = some envv →
      WantsSat S ρ' g'.wants envv ts vs) :
    ∀ g', g = some g' → ∀ envv, Term.evalList ρ [] g'.env = some envv → WantsSat S ρ' g'.wants envv ts vs := by
  intro g' hg' envv henv
  subst hg'
  cases hC : C.erased
  · exact h g' (by simp [given, hC]) envv henv
  · exact wantsSat_congr (fun w => { w with mult := .erased }) (fun _ => ⟨rfl, rfl⟩)
      (h g'.erase (by simp [given, hC]) envv henv)

theorem given_whole {C : Ctx} {g : Option Given} (hw : whole C g = false) : given C g = g := by
  simp only [whole, Bool.or_eq_false_iff] at hw
  simp [given, hw.1]

theorem ctx_whole {C : Ctx} {g : Option Given} (hw : whole C g = false) :
    ({ C with erased := whole C g } : Ctx) = C := by
  have : C.erased = false := by simp only [whole, Bool.or_eq_false_iff] at hw; exact hw.1
  cases C; simp_all

theorem posMult_whole {C : Ctx} {g : Option Given} {i : Nat} (hw : whole C g = true)
    (hi : ∀ g', g = some g' → i < g'.wants.length) : C.posMult g i = .erased := by
  simp only [Ctx.posMult]
  cases hC : C.erased
  · cases g with
    | none => simp [whole, hC] at hw
    | some g' =>
      simp only [whole, hC, Option.any_some, Bool.false_or, Given.allErased, Bool.and_eq_true, List.all_eq_true] at hw
      have hi' := hi g' rfl
      simp [Given.erasedAt, List.getElem?_eq_getElem hi', hw.2 _ (List.getElem_mem hi')]
  · rfl

theorem inv_ctx {C : Ctx} {b : Bool} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {act : Act} :
    Inv { C with erased := b } sc n0 W ρ act ↔ Inv C sc n0 W ρ act :=
  ⟨fun h => h.congr_ctx rfl rfl rfl, fun h => h.congr_ctx rfl rfl rfl⟩

/-- `finish` on an untainted scope: the scope and results are kept; the tree is removed when the position is
wholly erased or every result is tainted. -/
theorem finish_untainted {C : Ctx} {g : Option Given} {e : Expr} {o₀ o : Out}
    (hf : finish { C with erased := whole C g } (whole C g) (given C g) e o₀ = .ok o) (ht : o₀.sc.taintedBy = none) :
    o.sc = o₀.sc ∧ o.res = o₀.res ∧ o.tree = (if whole C g || o₀.res.all (·.tainted) then .removed else o₀.tree) ∧
      (whole C g = false → ∀ (i : Nat) (r : Res), o₀.res[i]? = some r → r.erased = true →
        g.any (·.erasedAt i) = true) := by
  obtain ⟨-, hsc, -, hres, htree, her⟩ := finish_spec hf
  simp only [ht, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hres
  refine ⟨hsc, hres, by rw [htree, hres], fun hw i r hr he => ?_⟩
  have := her hw i r (by rw [hres]; exact hr) he
  rwa [given_whole hw] at this

/-- The run-time half of `ExprPost` after `finish`, from the run of the tree `finish` was given. -/
theorem finish_run {C : Ctx} {g : Option Given} {e : Expr} {o₀ o : Out} {S : Sigs} {P : Prog} {env : Env}
    {vs : List Value}
    (hf : finish { C with erased := whole C g } (whole C g) (given C g) e o₀ = .ok o) (ht : o₀.sc.taintedBy = none)
    (hlen : ∀ g', g = some g' → o₀.res.length = g'.wants.length)
    (hrun : whole C g = false → o₀.res.all (·.tainted) = false →
      (∀ (i : Nat) (r : Res), o₀.res[i]? = some r → r.erased = true → g.any (·.erasedAt i) = true) →
      ∃ us, Eval P env o₀.tree us ∧ ResRel S C.phase (C.posMult g) o₀.res vs us) :
    ∃ us, Eval P env o.tree us ∧ ResRel S C.phase (C.posMult g) o.res vs us := by
  obtain ⟨-, hres, htree, her⟩ := finish_untainted hf ht
  rw [htree, hres]
  cases hw : whole C g
  · cases ha : o₀.res.all (·.tainted)
    · simpa using hrun hw ha (her hw)
    · refine ⟨_, .removed, ResRel.removed fun i r hr hr' => ?_⟩
      have := List.all_eq_true.1 ha r (List.mem_of_getElem? hr)
      simp_all
  · refine ⟨_, .removed, ResRel.removed fun i r hr _ => posMult_whole hw fun g' hg' => ?_⟩
    rw [← hlen g' hg']; exact (List.getElem?_eq_some_iff.1 hr).1

theorem given_length {C : Ctx} {S : Sigs} {ρ : List Value} {g : Option Given} {n : Nat}
    (hg : ∀ g', g = some g' → g'.Ok S ρ)
    (h : ∀ g', given C g = some g' → ∀ envv, Term.evalList ρ [] g'.env = some envv → n = g'.wants.length) :
    ∀ g', g = some g' → n = g'.wants.length := by
  intro g' hg'
  obtain ⟨envv, henv⟩ := (hg g' hg').env
  subst hg'
  cases hC : C.erased
  · exact h g' (by simp [given, hC]) envv henv
  · simpa [Given.erase] using h g'.erase (by simp [given, hC]) envv henv

theorem var_post {C : Ctx} {sc : Scope} {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    {o₀ o : Out} {x : Id} {n : String} {r : Res} (hI : Inv C sc n0 W ρ act)
    (hg : ∀ g', g = some g' → g'.Ok W.Sc ρ) (hx : x.name = some n) (hl : sc.lookup n = some r)
    (h₀ : produced sc (given C g) x.pos [{ r with erased := r.erased || sc.erasedEntry r.term }] (.var x) = .ok o₀)
    (hf : finish { C with erased := whole C g } (whole C g) (given C g) (.var x) o₀ = .ok o) :
    ExprPost C sc g n0 W ρ act o := by
  intro _
  obtain ⟨v, hv, hok⟩ := hI.names n r hl
  have hvs : Term.evalList ρ [] ([({ r with erased := r.erased || sc.erasedEntry r.term } : Res)].map (·.term)) =
      some [v] := by simp [Term.evalList, hv]
  obtain ⟨rfl, hw⟩ := produced_sound hI.sat.1 (hI.sigs ρ hI.agree) hI.noJunk hI.holes hvs ⟨hok, trivial⟩
    (fun g' h => (given_ok hg g' h).env) h₀
  obtain ⟨hsc, hres, -, -⟩ := finish_untainted hf hI.untainted
  refine ⟨[], [v], by rw [hsc]; simpa using hI, by rw [hres]; simpa using hvs, fun i r₁ v₁ hr hv₁ => ?_,
    fun g' hg' envv henv => ?_, fun env hE => ?_⟩
  · rw [hres] at hr
    cases i with
    | zero => cases hr; cases hv₁; exact hok
    | succ => simp at hr
  · rw [hres]
    simpa using given_wants (fun g'' h'' envv' henv' => (hw g'' h'' envv' henv').2) g' hg' envv henv
  · refine finish_run hf hI.untainted (given_length hg fun g'' h'' envv' henv' => (hw g'' h'' envv' henv').1)
      fun hwh hall her => ?_
    have hrt : r.tainted = false := by simpa using hall
    obtain ⟨a, v', ha, hv', hm⟩ := hE n r hl hrt
    rw [hv] at hv'
    cases hv'
    refine ⟨[a], .var (by simp [hx, ha]), [a], take_of_length rfl, fun i r₁ a₁ v₁ hr ha₁ hv₁ _ => ?_⟩
    cases i with
    | succ => simp at hr
    | zero =>
      cases hr; cases ha₁; cases hv₁
      cases hp : C.posMult g 0
      · have he := her 0 _ rfl
        simp only [whole, Bool.or_eq_false_iff] at hwh
        simp only [Ctx.posMult, hwh.1, Bool.false_or] at hp
        have hmo : sc.multOf r = .many := by
          simp only [Scope.multOf]
          split
          · rename_i hre; simp [hre] at he; simp [he] at hp
          · rfl
        rw [hmo] at hm; exact hm
      · exact hm.approx

theorem wantsSat_resOk {S : Sigs} {ρ : List Value} :
    ∀ {tele : Telescope} {env : List Value} {ts : List Bool} {vs : List Value},
      WantsSat S ρ (tele.map Want.of) env ts vs → ∀ v ∈ vs, v.noRemoved = true ∧ ∃ A, WType S v A
  | [], _, [], [], _ => by simp
  | b :: _, _, _ :: _, _ :: _, ⟨h1, h2⟩ => by
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · obtain ⟨A, -, h, hA, -⟩ := h1.1 b.type rfl
      exact ⟨h, A, hA⟩
    · exact wantsSat_resOk h2 v hv
  | [], _, [], _ :: _, h | [], _, _ :: _, _, h | _ :: _, _, [], _, h | _ :: _, _, _ :: _, [], h => h.elim

theorem sorry_post {C C' : Ctx} {sc : Scope} {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    {o₀ o : Out} {p : Pos} {t : Tele} {tele : Telescope} {tenv : List Term} (hI : Inv C sc n0 W ρ act)
    (hg : ∀ g', g = some g' → g'.Ok W.Sc ρ) (ha : annotation C' sc (given C g) t = .ok (tele, tenv))
    (h₀ : produced (opened sc tele tenv "sorry" p fun _ => true).1 (given C g) p
      (opened sc tele tenv "sorry" p fun _ => true).2 (.sorry p t) = .ok o₀)
    (hf : finish { C with erased := whole C g } (whole C g) (given C g) (.sorry p t) o₀ = .ok o) :
    ExprPost C sc g n0 W ρ act o := by
  intro _
  obtain ⟨envv, henv, hcons⟩ := annotation_cons hI.termInv.weak (given_ok hg) ha
  obtain ⟨vs, hvs⟩ := WantsCons.open hcons
  obtain ⟨hsat, hev⟩ := opened_sound (taint := fun _ => true) (kind := "sorry") (pos := p) hI.sat henv
    (WantsSat.teleOk _ hvs fun k hk => by simp at hk)
  obtain ⟨-, -, hrl, hrs⟩ := opened_shape sc tele tenv "sorry" p fun _ => true
  have hI' : Inv C (opened sc tele tenv "sorry" p fun _ => true).1 n0 W (ρ ++ vs) act :=
    hI.extend hsat rfl rfl hI.holes hI.untainted
  have hvl : vs.length = tele.length := by simpa using (WantsSat.lengths hvs).1
  have hok : ∀ (i : Nat) (r : Res) (v : Value), (opened sc tele tenv "sorry" p fun _ => true).2[i]? = some r →
      vs[i]? = some v → ResOk W.Sc r v := fun i r v hr hv => by
    obtain ⟨b, hb⟩ : ∃ b, tele[i]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hvl]; exact (List.getElem?_eq_some_iff.1 hv).1)⟩
    rw [(hrs i b hb).1] at hr
    cases hr
    obtain ⟨h1, A, h2⟩ := wantsSat_resOk hvs v (List.mem_of_getElem? hv)
    exact ⟨h1, ⟨A, h2⟩, fun h => by cases h⟩
  obtain ⟨rfl, hw⟩ := produced_sound hI'.sat.1 (hI.sigsClose vs) hI.noJunk hI.holes hev
    (ResOks.of_getElem (by rw [hrl, hvl]) hok)
    (fun g' h => let ⟨_, he⟩ := (given_ok hg g' h).env; ⟨_, Term.evalList_frame_ρ vs he⟩)
    h₀
  obtain ⟨hsc, hres, -, -⟩ := finish_untainted hf hI.untainted
  refine ⟨vs, vs, by rw [hsc]; exact hI', by rw [hres]; exact hev,
    fun i r v hr hv => by rw [hres] at hr; exact hok i r v hr hv,
    fun g' hg' envv' henv' => by
      rw [hres]
      exact given_wants (fun g'' h'' envv₁ henv₁ => (hw g'' h'' envv₁ (Term.evalList_frame_ρ vs henv₁)).2) g' hg'
        envv' henv', fun env hE => ?_⟩
  refine finish_run hf hI.untainted (given_length hg fun g'' h'' envv₁ henv₁ =>
    (hw g'' h'' envv₁ (Term.evalList_frame_ρ vs henv₁)).1) fun _ hall _ => ?_
  obtain ⟨r, hr, hrt⟩ : ∃ r ∈ (opened sc tele tenv "sorry" p fun _ => true).2, r.tainted = false := by simpa using hall
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  obtain ⟨b, hb⟩ : ∃ b, tele[i]? = some b := ⟨_, List.getElem?_eq_getElem (by rw [← hrl]; exact hi)⟩
  have := (hrs i b hb).1
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at this
  rw [this] at hrt
  cases hrt

theorem zip_map_term {bs : List LetBinder} {rs : List Res} (h : bs.length = rs.length) :
    ((bs.zip rs).map fun (b, r) => ({ r with erased := b.mult == some Mult.erased } : Res)).map (·.term) =
      rs.map (·.term) := by
  apply List.ext_getElem (by simp [h])
  intro i h₁ h₂
  simp

theorem let_post {C : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {act : Act} {p : Pos}
    {bs : List LetBinder} {rhs : Expr} {ws : List Want} {o : Out} (ih : ExprSound rhs) (ihs : ExprShape rhs)
    (hI : Inv C sc n0 W ρ act) (hws : letWants C sc bs = .ok ws)
    (ho : checkExpr C sc (some (letGiven bs ws)) rhs = .ok o) :
    StmtPost C sc n0 W ρ act ⟨o.sc.bind (bs.map (·.name))
      ((bs.zip o.res).map fun (b, r) => { r with erased := b.mult == some .erased }), .let p bs o.tree, o.snaps⟩ := by
  intro ht
  rw [Scope.bind_eq] at ht
  obtain ⟨hsigs, hnames, -, hpre, -⟩ := ihs C sc _ o hI.holes ho
  have hgok : ∀ g', some (letGiven bs ws) = some g' → g'.Ok W.Sc ρ := by
    rintro g' ⟨⟩
    refine ⟨⟨[], rfl⟩, fun hall envv henv => ?_⟩
    cases henv
    exact letWants_cons hI.termInv.weak hws hall
  obtain ⟨ρ', vs, hI', hvs, hok, hw, hrun⟩ := (ih C sc _ n0 W ρ act o hI hgok ho).1 ht
  obtain ⟨hwl, hwm⟩ := letWants_spec hws
  have hvl : vs.length = bs.length := by rw [(WantsSat.lengths (hw _ rfl [] rfl)).1]; exact hwl
  have hrl : bs.length = o.res.length := by rw [← hvl, Term.length_evalList hvs, List.length_map]
  have hget : ∀ (i : Nat) (r : Res), ((bs.zip o.res).map fun (b, r) =>
      ({ r with erased := b.mult == some Mult.erased } : Res))[i]? = some r →
      ∃ b r₀, bs[i]? = some b ∧ o.res[i]? = some r₀ ∧ r = { r₀ with erased := b.mult == some Mult.erased } :=
    fun i r hr => by
      simp only [List.getElem?_map, Option.map_eq_some_iff, List.getElem?_zip_eq_some] at hr
      obtain ⟨⟨b, r₀⟩, ⟨hb, hr₀⟩, rfl⟩ := hr
      exact ⟨b, r₀, hb, hr₀, rfl⟩
  refine ⟨ρ', Inv.bind hI' (by rw [zip_map_term hrl]; exact hvs) fun i r v hr hv => ?_, fun hC env hE => ?_⟩
  · obtain ⟨b, r₀, -, hr₀, rfl⟩ := hget i r hr
    exact hok i r₀ v hr₀ hv
  obtain ⟨us, hev, us', htk, hm⟩ := hrun env hE
  have hul : us'.length = bs.length := by rw [(take_ok htk).1, hrl]
  have hb := bindIds_of_length (env := env) (ids := bs.map (·.name)) (vs := us') (by simp [hul])
  refine ⟨_, .let hev (by rw [hrl]; exact htk) hb, EnvRel.bind (EnvRel.extend ρ' hE hnames hpre hI.sat.1.1)
    (by simp [hrl]) (by simp [hul, hrl]) fun i r a hr ha hrt => ?_⟩
  obtain ⟨b, r₀, hb, hr₀, rfl⟩ := hget i r hr
  obtain ⟨v, hv⟩ : ∃ v, vs[i]? = some v :=
    ⟨_, List.getElem?_eq_getElem (by rw [hvl]; exact (List.getElem?_eq_some_iff.1 hb).1)⟩
  have hev' : r₀.term.eval (ρ ++ ρ') [] = some v := by
    have := Term.evalList_getElem? (i := i) hvs
    rw [hv, List.getElem?_map, hr₀] at this
    exact this.symm
  refine ⟨v, hev', ?_⟩
  have hm' := hm i r₀ a v hr₀ ha hv hrt
  cases hp : C.posMult (some (letGiven bs ws)) i
  · rw [hp] at hm'; exact MultRel.of_rel _ hm'
  · rw [hp] at hm'
    simp only [Ctx.posMult, hC, Bool.false_or, Option.any_some, Given.erasedAt, letGiven] at hp
    split at hp
    · rename_i hwe
      obtain ⟨w, hw', hwe'⟩ := (Option.any_eq_true _ _).1 hwe
      have := hwm i w b hw' hb
      have hbm : b.mult = some .erased := by
        cases hbm : b.mult with
        | none => simp [hbm] at this; simp [this] at hwe'
        | some m => simp [hbm] at this; rw [this] at hwe'; simpa using hwe'
      simp only [Scope.multOf, hbm]
      simpa using hm'
    · cases hp

theorem checkElems_shape {es : List Expr} (ihs : ∀ e ∈ es, ExprShape e) :
    ∀ {C : Ctx} {sc : Scope} {g : Option Given} {prev : List Res} {o : ElemsOut}, sc.holes = [] →
      checkElems C sc g prev es = .ok o →
      o.sc.sigs = sc.sigs ∧ o.sc.names = sc.names ∧ o.sc.holes = [] ∧ sc.Γ.eraseRules <+: o.sc.Γ.eraseRules ∧
        (sc.taintedBy.isSome → o.sc.taintedBy.isSome) ∧ o.res.length = es.length := by
  induction es with
  | nil =>
    intro C sc g prev o hh h
    simp only [checkElems, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, hh, List.prefix_refl _, id, rfl⟩
  | cons e es ih =>
    intro C sc g prev o hh h
    simp only [checkElems] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨r, -, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    obtain ⟨h1, h2, h3, h4, h5⟩ := ihs e List.mem_cons_self C sc _ o₁ hh ho₁
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := ih (fun e he => ihs e (List.mem_cons_of_mem _ he)) h3 hrest
    exact ⟨k1.trans h1, k2.trans h2, k3, h4.trans k4, k5 ∘ h5, by simp [k6]⟩

theorem posMult_elem (C : Ctx) (g : Option Given) (prev : List Res) :
    C.posMult (elemGiven g prev) 0 = C.posMult g prev.length := by
  cases g with
  | none => rfl
  | some g =>
    cases hw : g.wants[prev.length]? <;> simp [Ctx.posMult, elemGiven, Given.erasedAt, hw]

theorem checkElems_sound {es : List Expr} (ih : ∀ e ∈ es, ExprSound e) (ihs : ∀ e ∈ es, ExprShape e) :
    ∀ {C : Ctx} {sc : Scope} {g : Option Given} {prev : List Res} {o : ElemsOut} {n0 : Nat} {W : World}
      {ρ : List Value} {act : Act} {prevv : List Value}, Inv C sc n0 W ρ act →
      (∀ g', g = some g' → (∃ envv, Term.evalList ρ [] g'.env = some envv) ∧
        g'.wants.length = prev.length + es.length) →
      Term.evalList ρ [] (prev.map (·.term)) = some prevv → checkElems C sc g prev es = .ok o →
      o.sc.taintedBy = none → ∃ ρ' vs, Inv C o.sc n0 W (ρ ++ ρ') act ∧
        Term.evalList (ρ ++ ρ') [] (o.res.map (·.term)) = some vs ∧
        (∀ (i : Nat) (r : Res) (v : Value), o.res[i]? = some r → vs[i]? = some v → ResOk W.Sc r v) ∧
        (∀ g', g = some g' → ∀ envv, Term.evalList ρ [] g'.env = some envv →
          WantsSat W.Sc (ρ ++ ρ') (g'.wants.drop prev.length) (envv ++ prevv) (o.res.map (!·.tainted)) vs) ∧
        ∀ env, EnvRel W.Sc C.phase sc ρ env → ∃ us, EvalList W.P env o.trees us ∧ us.length = vs.length ∧
          ∀ (i : Nat) (r : Res) (a v : Value), o.res[i]? = some r → us[i]? = some a → vs[i]? = some v →
            r.tainted = false → MultRel W.Sc C.phase (C.posMult g (prev.length + i)) a v := by
  induction es with
  | nil =>
    intro C sc g prev o n0 W ρ act prevv hI hg _ h _
    simp only [checkElems, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨[], [], by simpa using hI, rfl, by simp, fun g' hg' envv _ => ?_, fun env _ => ⟨[], .nil, rfl, by simp⟩⟩
    have : g'.wants.drop prev.length = [] := by simp [(hg g' hg').2]
    rw [this]; trivial
  | cons e es ihes =>
    intro C sc g prev o n0 W ρ act prevv hI hg hprev h ht
    simp only [checkElems] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hr hrest
    obtain ⟨-, hnames₁, hh₁, hpre₁, -⟩ := ihs e List.mem_cons_self C sc _ o₁ hI.holes ho₁
    have ht₁ : o₁.sc.taintedBy = none := by
      cases h₁ : o₁.sc.taintedBy with
      | none => rfl
      | some _ =>
        have := (checkElems_shape (fun e he => ihs e (List.mem_cons_of_mem _ he)) hh₁ hrest).2.2.2.2.1 (by simp [h₁])
        simp [show rest.sc.taintedBy = none from ht] at this
    have hgok : ∀ g', elemGiven g prev = some g' → g'.Ok W.Sc ρ := by
      intro g' hg'
      simp only [elemGiven, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hg'
      obtain ⟨g₀, rfl, w, -, rfl⟩ := hg'
      obtain ⟨envv, henv⟩ := (hg g₀ rfl).1
      exact ⟨⟨envv ++ prevv, Term.evalList_append henv hprev⟩, fun h => by cases h⟩
    obtain ⟨ρ₁, vs₁, hI₁, hvs₁, hok₁, hw₁, hrun₁⟩ := (ih e List.mem_cons_self C sc _ n0 W ρ act o₁ hI hgok ho₁).1 ht₁
    rw [single_ok hr] at hvs₁ hok₁ hw₁ hrun₁
    obtain ⟨v, hv, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs₁)
    obtain ⟨ρ₂, vs₂, hI₂, hvs₂, hok₂, hw₂, hrun₂⟩ := ihes (fun a ha => ih a (List.mem_cons_of_mem _ ha))
      (fun a ha => ihs a (List.mem_cons_of_mem _ ha)) hI₁
      (fun g' hg' => by
        obtain ⟨⟨envv, henv⟩, hl⟩ := hg g' hg'
        exact ⟨⟨envv, Term.evalList_frame_ρ ρ₁ henv⟩, by simp [hl]; omega⟩)
      (by
        rw [List.map_append, List.map_singleton]
        exact Term.evalList_append (Term.evalList_frame_ρ ρ₁ hprev) (Term.evalList_singleton.2 ⟨v, hv, rfl⟩))
      hrest ht
    refine ⟨ρ₁ ++ ρ₂, v :: vs₂, by simpa using hI₂, ?_, fun i r' v' hr' hv' => ?_, fun g' hg' envv henv => ?_,
      fun env hE => ?_⟩
    · simp only [List.map_cons]
      rw [← List.append_assoc]
      exact Term.evalList_cons_eq_some.2 ⟨v, vs₂, Term.eval_frame_ρ ρ₂ hv, hvs₂, rfl⟩
    · cases i with
      | zero => cases hr'; cases hv'; exact hok₁ 0 r v rfl rfl
      | succ i => exact hok₂ i r' v' (by simpa using hr') (by simpa using hv')
    · have hl := (hg g' hg').2
      obtain ⟨w, hw⟩ : ∃ w, g'.wants[prev.length]? = some w := ⟨_, List.getElem?_eq_getElem (by simp [hl])⟩
      have hel : elemGiven g prev = some ⟨[w], g'.env ++ prev.map (·.term), false, none,
          g'.label.map fun l _ => l prev.length⟩ := by simp [elemGiven, hg', hw]
      have h1 := hw₁ _ hel (envv ++ prevv) (Term.evalList_append henv hprev)
      have h2 := hw₂ g' hg' envv (Term.evalList_frame_ρ ρ₁ henv)
      rw [List.drop_eq_getElem_cons (by simp [hl]), ← List.append_assoc]
      refine ⟨?_, ?_⟩
      · have := h1.1.frame ρ₂
        simpa [List.getElem?_eq_some_iff.1 hw |>.2] using this
      · simpa [List.length_append] using h2
    · obtain ⟨us₁, hev₁, us₁', htk₁, hm₁⟩ := hrun₁ env hE
      obtain ⟨a, ho, rfl⟩ := one_of_take htk₁
      obtain ⟨us₂, hev₂, hl₂, hm₂⟩ := hrun₂ env (EnvRel.extend ρ₁ hE hnames₁ hpre₁ hI.sat.1.1)
      refine ⟨a :: us₂, .cons hev₁ ho hev₂, by simp [hl₂], fun i r' a' v' hr' ha' hv' hrt => ?_⟩
      cases i with
      | zero =>
        cases hr'; cases ha'; cases hv'
        have := hm₁ 0 r a v rfl rfl rfl hrt
        rwa [posMult_elem] at this
      | succ i =>
        have := hm₂ i r' a' v' (by simpa using hr') (by simpa using ha') (by simpa using hv') hrt
        rwa [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_comm 1 i] at this

theorem tuple_post {C : Ctx} {sc : Scope} {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    {o : Out} {p : Pos} {es : List Expr} {oe : ElemsOut} (ih : ∀ e ∈ es, ExprSound e) (ihs : ∀ e ∈ es, ExprShape e)
    (hI : Inv C sc n0 W ρ act) (hg : ∀ g', g = some g' → g'.Ok W.Sc ρ)
    (hlen : ∀ g', given C g = some g' → g'.wants.length = es.length)
    (hoe : checkElems { C with erased := whole C g } sc (given C g) [] es = .ok oe)
    (hf : finish { C with erased := whole C g } (whole C g) (given C g) (.tuple p es)
      ⟨oe.sc, oe.res, .tuple p oe.trees, oe.snaps⟩ = .ok o) :
    ExprPost C sc g n0 W ρ act o := by
  intro ht
  obtain ⟨-, -, -, -, -, hrl⟩ := checkElems_shape ihs hI.holes hoe
  obtain ⟨hsc, hres, -, -⟩ := finish_untainted hf (by
    obtain ⟨-, hsc, -⟩ := finish_spec hf
    rw [← ht, hsc])
  rw [hsc] at ht
  obtain ⟨ρ', vs, hI', hvs, hok, hw, hrun⟩ := checkElems_sound ih ihs (prev := []) (prevv := [])
    (inv_ctx.2 hI) (fun g' h => ⟨(given_ok hg g' h).env, by simp [hlen g' h]⟩) rfl hoe ht
  refine ⟨ρ', vs, by rw [hsc]; exact inv_ctx.1 hI', by rw [hres]; exact hvs, fun i r v hr hv => ?_,
    fun g' hg' envv henv => ?_, fun env hE => ?_⟩
  · rw [hres] at hr; exact hok i r v hr hv
  · rw [hres]
    exact given_wants (fun g'' h'' envv' henv' => by simpa using hw g'' h'' envv' henv') g' hg' envv henv
  · refine finish_run hf (by exact ht) (given_length hg fun g'' h'' _ _ => by rw [hlen g'' h'', hrl])
      fun hwh _ _ => ?_
    rw [given_whole hwh, ctx_whole hwh] at hrun
    obtain ⟨us, hev, hul, hm⟩ := hrun env hE
    refine ⟨us, .tuple hev, us, take_of_length (by rw [hul, Term.length_evalList hvs, List.length_map]),
      fun i r a v hr ha hv hrt => ?_⟩
    simpa using hm i r a v hr ha hv hrt

theorem checkStmts_shape {ss : List Stmt} (ihss : ∀ s ∈ ss, StmtShape s) :
    ∀ {C : Ctx} {sc : Scope} {o : StmtsOut}, sc.holes = [] → checkStmts C sc ss = .ok o →
      o.sc.sigs = sc.sigs ∧ o.sc.holes = [] ∧ sc.Γ.eraseRules <+: o.sc.Γ.eraseRules ∧
        (sc.taintedBy.isSome → o.sc.taintedBy.isSome) := by
  induction ss with
  | nil =>
    intro C sc o hh h
    simp only [checkStmts, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, hh, List.prefix_refl _, id⟩
  | cons s ss ih =>
    intro C sc o hh h
    simp only [checkStmts] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    obtain ⟨h1, h2, h3, h4⟩ := ihss s List.mem_cons_self C sc o₁ hh ho₁
    obtain ⟨k1, k2, k3, k4⟩ := ih (fun s hs => ihss s (List.mem_cons_of_mem _ hs)) h2 hrest
    exact ⟨k1.trans h1, k2, h3.trans k3, k4 ∘ h4⟩

theorem checkStmts_sound {ss : List Stmt} (ihs : ∀ s ∈ ss, StmtSound s) (ihss : ∀ s ∈ ss, StmtShape s) :
    ∀ {C : Ctx} {sc : Scope} {o : StmtsOut} {n0 : Nat} {W : World} {ρ : List Value} {act : Act},
      Inv C sc n0 W ρ act → checkStmts C sc ss = .ok o → o.sc.taintedBy = none →
      ∃ ρ', Inv C o.sc n0 W (ρ ++ ρ') act ∧ (C.erased = false → ∀ env, EnvRel W.Sc C.phase sc ρ env →
        ∃ env', (∀ f vs, Eval W.P env' f vs → EvalBlock W.P env o.trees f vs) ∧
          EnvRel W.Sc C.phase o.sc (ρ ++ ρ') env') := by
  induction ss with
  | nil =>
    intro C sc o n0 W ρ act hI h _
    simp only [checkStmts, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], by simpa using hI, fun _ env hE => ⟨env, fun _ _ h => .nil h, by simpa using hE⟩⟩
  | cons s ss ih =>
    intro C sc o n0 W ρ act hI h ht
    simp only [checkStmts] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    have ht' : rest.sc.taintedBy = none := ht
    obtain ⟨-, hh₁, -, -⟩ := ihss s List.mem_cons_self C sc o₁ hI.holes ho₁
    have ht₁ : o₁.sc.taintedBy = none := by
      cases h₁ : o₁.sc.taintedBy with
      | none => rfl
      | some _ =>
        have := (checkStmts_shape (fun s hs => ihss s (List.mem_cons_of_mem _ hs)) hh₁ hrest).2.2.2 (by simp [h₁])
        simp [ht'] at this
    obtain ⟨ρ₁, hI₁, hrun₁⟩ := ihs s List.mem_cons_self C sc n0 W ρ act o₁ hI ho₁ ht₁
    obtain ⟨ρ₂, hI₂, hrun₂⟩ := ih (fun s hs => ihs s (List.mem_cons_of_mem _ hs))
      (fun s hs => ihss s (List.mem_cons_of_mem _ hs)) hI₁ hrest ht'
    refine ⟨ρ₁ ++ ρ₂, by simpa using hI₂, fun hC env hE => ?_⟩
    obtain ⟨env₁, hev₁, hE₁⟩ := hrun₁ hC env hE
    obtain ⟨env₂, hb, hE₂⟩ := hrun₂ hC env₁ hE₁
    exact ⟨env₂, fun f vs h => .cons hev₁ (hb f vs h), by simpa using hE₂⟩

theorem givenOk_frame {S : Sigs} {ρ : List Value} (ρ' : List Value) {g : Given} (h : g.Ok S ρ) : g.Ok S (ρ ++ ρ') := by
  obtain ⟨⟨envv, henv⟩, hc⟩ := h
  refine ⟨⟨envv, Term.evalList_frame_ρ ρ' henv⟩, fun hw envv' henv' => ?_⟩
  rw [Term.evalList_frame_ρ ρ' henv, Option.some.injEq] at henv'
  subst henv'
  exact (hc hw envv henv).frame ρ'

/-- The invariant for a scope whose names are put back to those of an earlier scope. -/
theorem inv_restore {C : Ctx} {sc sc' : Scope} {n0 : Nat} {W : World} {ρ ρ' : List Value} {act : Act}
    (hI : Inv C sc n0 W ρ act) (hI' : Inv C sc' n0 W (ρ ++ ρ') act) :
    Inv C { sc' with names := sc.names } n0 W (ρ ++ ρ') act :=
  ⟨hI'.holes, hI'.untainted, hI'.sat, hI'.n0_world, hI'.agree, hI'.sigs, hI'.sigsOk, hI'.noJunk, fun n r h => by
    obtain ⟨v, h1, h2⟩ := hI.names n r h
    exact ⟨v, Term.eval_frame_ρ ρ' h1, h2⟩, hI'.globals, hI'.act⟩

theorem scope_holes {sc : Scope} {hs : List Hole} (h : sc.holes = hs) : ({ sc with holes := hs } : Scope) = sc := by
  cases sc; simp_all

theorem block_post {C : Ctx} {sc : Scope} {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    {o : Out} {ss : List Stmt} {f : Expr} {s : StmtsOut} {of : Out} (ihs : ∀ s ∈ ss, StmtSound s)
    (ihss : ∀ s ∈ ss, StmtShape s) (ihf : ExprSound f) (ihfs : ExprShape f)
    (hI : Inv C sc n0 W ρ act) (hg : ∀ g', g = some g' → g'.Ok W.Sc ρ)
    (hs : checkStmts { C with erased := whole C g } { sc with holes := [] } ss = .ok s)
    (hof : checkExpr { C with erased := whole C g } { s.sc with holes := sc.holes } (given C g) f = .ok of)
    (hf : finish { C with erased := whole C g } (whole C g) (given C g) (.block ss f)
      ⟨{ of.sc with names := sc.names }, of.res, .block s.trees of.tree, s.snaps ++ of.snaps⟩ = .ok o) :
    ExprPost C sc g n0 W ρ act o ∧ (o.sc.taintedBy = none → (Expr.block ss f).absurd = true →
      ∀ r ∈ o.res, r.tainted = true) := by
  rw [scope_holes hI.holes] at hs
  obtain ⟨-, hhs, -, -⟩ := checkStmts_shape ihss hI.holes hs
  rw [hI.holes, scope_holes hhs] at hof
  obtain ⟨-, hsc₀, -⟩ := finish_spec hf
  have key : o.sc.taintedBy = none → of.sc.taintedBy = none ∧ ∃ ρ₁, Inv C s.sc n0 W (ρ ++ ρ₁) act ∧
      (whole C g = false → ∀ env, EnvRel W.Sc C.phase sc ρ env →
        ∃ env', (∀ f vs, Eval W.P env' f vs → EvalBlock W.P env s.trees f vs) ∧
          EnvRel W.Sc C.phase s.sc (ρ ++ ρ₁) env') := fun ht => by
    have ht' : of.sc.taintedBy = none := by rw [hsc₀] at ht; exact ht
    have hts : s.sc.taintedBy = none := by
      cases h₁ : s.sc.taintedBy with
      | none => rfl
      | some _ =>
        have := (ihfs _ _ _ of hhs hof).2.2.2.2 (by simp [h₁])
        simp [ht'] at this
    obtain ⟨ρ₁, hI₁, hrun⟩ := checkStmts_sound ihs ihss (inv_ctx.2 hI) hs hts
    exact ⟨ht', ρ₁, inv_ctx.1 hI₁, fun hw env hE => hrun hw env hE⟩
  have hg₁ : ∀ ρ₁, ∀ g', given C g = some g' → g'.Ok W.Sc (ρ ++ ρ₁) :=
    fun ρ₁ g' h => givenOk_frame ρ₁ (given_ok hg g' h)
  refine ⟨fun ht => ?_, fun ht ha r hr => ?_⟩
  · obtain ⟨ht', ρ₁, hI₁, hrun₁⟩ := key ht
    obtain ⟨ρ₂, vs, hI₂, hvs, hok, hw, hrun₂⟩ := (ihf _ _ _ n0 W (ρ ++ ρ₁) act of (inv_ctx.2 hI₁) (hg₁ ρ₁) hof).1 ht'
    obtain ⟨hsc, hres, -, -⟩ := finish_untainted hf (by exact ht')
    have hwf : ∀ g', given C g = some g' → ∀ envv, Term.evalList ρ [] g'.env = some envv →
        WantsSat W.Sc (ρ ++ (ρ₁ ++ ρ₂)) g'.wants envv (of.res.map (!·.tainted)) vs := fun g' h envv henv => by
      simpa using hw g' h envv (Term.evalList_frame_ρ ρ₁ henv)
    refine ⟨ρ₁ ++ ρ₂, vs, by rw [hsc]; exact inv_restore hI (by simpa using inv_ctx.1 hI₂),
      by rw [hres]; simpa using hvs, fun i r v hr hv => by rw [hres] at hr; exact hok i r v hr hv,
      fun g' hg' envv henv => by rw [hres]; exact given_wants hwf g' hg' envv henv, fun env hE => ?_⟩
    refine finish_run hf (by exact ht') (given_length (C := C) hg fun g'' h'' envv henv => ?_) fun hwh _ _ => ?_
    · rw [← List.length_map (f := fun r : Res => r.term), ← Term.length_evalList hvs]
      exact (WantsSat.lengths (hwf g'' h'' envv henv)).1
    · obtain ⟨env₁, hb, hE₁⟩ := hrun₁ hwh env hE
      obtain ⟨us, hev, hrr⟩ := hrun₂ env₁ hE₁
      rw [given_whole hwh, ctx_whole hwh] at hrr
      exact ⟨us, .block (hb _ _ hev), hrr⟩
  · obtain ⟨ht', ρ₁, hI₁, -⟩ := key ht
    obtain ⟨-, hres, -, -⟩ := finish_untainted hf (by exact ht')
    rw [hres] at hr
    exact (ihf _ _ _ n0 W (ρ ++ ρ₁) act of (inv_ctx.2 hI₁) (hg₁ ρ₁) hof).2 ht' (by simpa [Expr.absurd] using ha) r hr

theorem isHole_false {e : Expr} (h : e.holeFree = true) : isHole e = false := by
  unfold isHole
  split
  · simp [Expr.holeFree] at h
  · rfl

theorem checkArgs_shape {args : List Arg} (ihs : ∀ a ∈ args, ExprShape a.expr)
    (hh : ∀ a ∈ args, a.expr.holeFree = true) :
    ∀ {C : Ctx} {sc : Scope} {owner role : String} {er : Bool} {params : Telescope} {prev : List Res}
      {a : ArgsOut}, sc.holes = [] → checkArgs C sc owner role er params prev args = .ok a →
      a.sc.sigs = sc.sigs ∧ a.sc.names = sc.names ∧ a.sc.holes = [] ∧ sc.Γ.eraseRules <+: a.sc.Γ.eraseRules ∧
        (sc.taintedBy.isSome → a.sc.taintedBy.isSome) := by
  induction args with
  | nil =>
    intro C sc owner role er params prev a hh' h
    simp only [checkArgs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, hh', List.prefix_refl _, id⟩
  | cons arg args ih =>
    intro C sc owner role er params prev a hh' h
    obtain ⟨m, e⟩ := arg
    cases params with
    | nil => simp [checkArgs, internal, failAt_eq] at h
    | cons p ps =>
      simp only [checkArgs, isHole_false (e := e) (hh _ List.mem_cons_self), Bool.and_false, Bool.false_eq_true,
        ↓reduceIte] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
      obtain ⟨r, -, h⟩ := bind_eq_ok.1 h
      obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [keep_ok] at hrest
      obtain ⟨h1, h2, h3, h4, h5⟩ := ihs _ List.mem_cons_self C sc _ o hh' ho
      obtain ⟨k1, k2, k3, k4, k5⟩ := ih (fun a ha => ihs a (List.mem_cons_of_mem _ ha))
        (fun a ha => hh a (List.mem_cons_of_mem _ ha)) h3 hrest
      exact ⟨k1.trans h1, k2.trans h2, k3, h4.trans k4, k5 ∘ h5⟩

theorem posMult_arg (C : Ctx) (p : TBinder) (prev : List Res) (role owner : String) (er : Bool) :
    C.posMult (some (argGiven p prev role owner er)) 0 =
      if C.erased || er || p.mult == .erased then .erased else .many := by
  cases er <;> simp [Ctx.posMult, argGiven, Given.erasedAt]

/-- The arguments of an application (§8): their ideal values meet the telescope, untainted ones typed, and they
run to values related to them, each by its parameter's multiplicity. -/
theorem checkArgs_sound {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr) (ihs : ∀ a ∈ args, ExprShape a.expr)
    (hh : ∀ a ∈ args, a.expr.holeFree = true) :
    ∀ {C : Ctx} {sc : Scope} {owner role : String} {er : Bool} {params : Telescope} {prev : List Res}
      {a : ArgsOut} {n0 : Nat} {W : World} {ρ : List Value} {act : Act} {prevv : List Value},
      Inv C sc n0 W ρ act → params.length = args.length → Term.evalList ρ [] (prev.map (·.term)) = some prevv →
      checkArgs C sc owner role er params prev args = .ok a → a.sc.taintedBy = none →
      ∃ ρ' vs, Inv C a.sc n0 W (ρ ++ ρ') act ∧ Term.evalList (ρ ++ ρ') [] (a.res.map (·.term)) = some vs ∧
        (∀ (i : Nat) (r : Res) (v : Value), a.res[i]? = some r → vs[i]? = some v → ResOk W.Sc r v) ∧
        WantsSat W.Sc (ρ ++ ρ') (params.map Want.of) prevv (a.res.map (!·.tainted)) vs ∧
        ∀ env, EnvRel W.Sc C.phase sc ρ env → ∃ us, EvalList W.P env (a.trees.map Arg.expr) us ∧
          us.length = vs.length ∧ ∀ (i : Nat) (r : Res) (p : TBinder) (u v : Value), a.res[i]? = some r →
            params[i]? = some p → us[i]? = some u → vs[i]? = some v → r.tainted = false →
            MultRel W.Sc C.phase (if C.erased || er || p.mult == .erased then .erased else .many) u v := by
  induction args with
  | nil =>
    intro C sc owner role er params prev a n0 W ρ act prevv hI hl _ h _
    cases params with
    | cons => simp at hl
    | nil =>
      simp only [checkArgs, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨[], [], by simpa using hI, rfl, by simp, trivial, fun env _ => ⟨[], .nil, rfl, by simp⟩⟩
  | cons arg args ihas =>
    intro C sc owner role er params prev a n0 W ρ act prevv hI hl hprev h ht
    obtain ⟨m, e⟩ := arg
    cases params with
    | nil => simp at hl
    | cons p ps =>
      simp only [checkArgs, isHole_false (e := e) (hh _ List.mem_cons_self), Bool.and_false, Bool.false_eq_true,
        ↓reduceIte] at h
      obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
      obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
      obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [keep_ok] at hr hrest
      have ht' : rest.sc.taintedBy = none := ht
      have ih' := fun a ha => ih a (List.mem_cons_of_mem _ ha)
      have ihs' := fun a ha => ihs a (List.mem_cons_of_mem _ ha)
      have hh' := fun a ha => hh a (List.mem_cons_of_mem _ ha)
      obtain ⟨-, hnames₁, hh₁, hpre₁, -⟩ := ihs _ List.mem_cons_self C sc _ o hI.holes ho
      have ht₁ : o.sc.taintedBy = none := by
        cases h₁ : o.sc.taintedBy with
        | none => rfl
        | some _ =>
          have := (checkArgs_shape ihs' hh' hh₁ hrest).2.2.2.2 (by simp [h₁])
          simp [ht'] at this
      have hgok : ∀ g', some (argGiven p prev role owner er) = some g' → g'.Ok W.Sc ρ := by
        rintro g' ⟨⟩
        exact ⟨⟨prevv, by simpa [argGiven] using hprev⟩, fun h => by cases h⟩
      obtain ⟨ρ₁, vs₁, hI₁, hvs₁, hok₁, hw₁, hrun₁⟩ := (ih _ List.mem_cons_self C sc _ n0 W ρ act o hI hgok ho).1 ht₁
      rw [single_ok hr] at hvs₁ hok₁ hw₁ hrun₁
      obtain ⟨v, hv, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs₁)
      have hb : WantSat W.Sc (ρ ++ ρ₁) (Want.of p) prevv (!r.tainted) v :=
        (hw₁ _ rfl prevv (by simpa [argGiven] using hprev)).1
      obtain ⟨ρ₂, vs₂, hI₂, hvs₂, hok₂, hw₂, hrun₂⟩ := ihas ih' ihs' hh' hI₁ (by simpa using hl)
        (by
          rw [List.map_append, List.map_singleton]
          exact Term.evalList_append (Term.evalList_frame_ρ ρ₁ hprev) (Term.evalList_singleton.2 ⟨v, hv, rfl⟩))
        hrest ht'
      refine ⟨ρ₁ ++ ρ₂, v :: vs₂, by simpa using hI₂, ?_, fun i r' v' hr' hv' => ?_, ?_, fun env hE => ?_⟩
      · simp only [List.map_cons]
        rw [← List.append_assoc]
        exact Term.evalList_cons_eq_some.2 ⟨v, vs₂, Term.eval_frame_ρ ρ₂ hv, hvs₂, rfl⟩
      · cases i with
        | zero => cases hr'; cases hv'; exact hok₁ 0 r v rfl rfl
        | succ i => exact hok₂ i r' v' (by simpa using hr') (by simpa using hv')
      · rw [← List.append_assoc]
        exact ⟨hb.frame ρ₂, hw₂⟩
      · obtain ⟨us₁, hev₁, us₁', htk₁, hm₁⟩ := hrun₁ env hE
        obtain ⟨u, hou, rfl⟩ := one_of_take htk₁
        obtain ⟨us₂, hev₂, hl₂, hm₂⟩ := hrun₂ env (EnvRel.extend ρ₁ hE hnames₁ hpre₁ hI.sat.1.1)
        refine ⟨u :: us₂, .cons hev₁ hou hev₂, by simp [hl₂], fun i r' p' u' v' hr' hp' hu' hv' hrt => ?_⟩
        cases i with
        | zero =>
          cases hr'; cases hp'; cases hu'; cases hv'
          have := hm₁ 0 r u v rfl rfl rfl hrt
          rwa [posMult_arg] at this
        | succ i =>
          exact hm₂ i r' p' u' v' (by simpa using hr') (by simpa using hp') (by simpa using hu') (by simpa using hv')
            hrt

/-- An application's run-time value is related to its ideal one when each argument is, by its parameter's
multiplicity, a type constructor's argument erased from phase 2 on (§16). -/
theorem rel_app {S : Sigs} {phase : Nat} {hd : Head} {sig' : Sig} {params : Telescope} {er : Bool}
    {us vs : List Value} (hS : S.find hd = some sig') (hm : sig'.params.map (·.mult) = params.map (·.mult))
    (her : er = (hd.kind == .type && decide (2 ≤ phase))) (hl : us.length = vs.length)
    (hpl : vs.length = params.length)
    (h : ∀ (j : Nat) (p : TBinder) (u v : Value), params[j]? = some p → us[j]? = some u → vs[j]? = some v →
      MultRel S phase (if er || p.mult == .erased then .erased else .many) u v) :
    Rel S phase (.app hd us) (.app hd vs) := by
  refine Rel.app_iff.2 ⟨rfl, hl, fun j u v hu hv => ?_⟩
  obtain ⟨p, hp⟩ : ∃ p, params[j]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by rw [← hpl]; exact (List.getElem?_eq_some_iff.1 hv).1)⟩
  have hmj := congrArg (·[j]?) hm
  simp only [List.getElem?_map, hp, Option.map_some] at hmj
  have := h j p u v hp hu hv
  cases he : S.erasedArg phase hd j
  · simp only [Sigs.erasedArg, hS, Option.bind_some, Bool.or_eq_false_iff] at he
    have hm' : (p.mult == .erased) = false := by
      cases hs : sig'.params[j]? with
      | none => rw [hs] at hmj; cases hmj
      | some b =>
        rw [hs, Option.map_some, Option.some.injEq] at hmj
        rw [hs] at he
        simpa [← hmj] using he.2
    rw [her, he.1, hm'] at this
    exact this
  · exact this.approx

theorem noRemoved_of_resOk {S : Sigs} {ρ : List Value} :
    ∀ {rs : List Res} {vs : List Value}, Term.evalList ρ [] (rs.map (·.term)) = some vs →
      (∀ (i : Nat) (r : Res) (v : Value), rs[i]? = some r → vs[i]? = some v → ResOk S r v) →
      Value.noRemovedList vs = true
  | [], _, h, _ => by cases h; rfl
  | r :: rs, _, h, hok => by
    obtain ⟨v, vs, -, hvs, rfl⟩ := Term.evalList_cons_eq_some.1 h
    simp only [Value.noRemovedList, Bool.and_eq_true]
    exact ⟨(hok 0 r v rfl rfl).1, noRemoved_of_resOk hvs fun i r' v' h1 h2 => hok (i + 1) r' v' h1 h2⟩

theorem ctorApp_post {C : Ctx} {sc : Scope} {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    {o₀ o : Out} {h : Name} {args : List Arg} {k : HeadKind} {sig : Sig} {role : String} {er : Bool} {a : ArgsOut}
    (ih : ∀ a ∈ args, ExprSound a.expr) (ihs : ∀ a ∈ args, ExprShape a.expr) (hh : ∀ a ∈ args, a.expr.holeFree = true)
    (hI : Inv C sc n0 W ρ act) (hg : ∀ g', g = some g' → g'.Ok W.Sc ρ) (hk : HeadOk sc.sigs W k h.name)
    (her : er = (k == .type && decide (2 ≤ C.phase))) (hsig : sc.sigs.find ⟨k, h.name⟩ = some sig)
    (har : sig.params.length = args.length)
    (ha : checkArgs { C with erased := whole C g } sc h.name role er sig.params [] args = .ok a)
    (h₀ : applied a.sc (given C g) h.pos [⟨.app sig.head (a.res.map (·.term)), a.res.any (·.tainted), false⟩]
      (.app h a.trees) sc.holes.length a.snaps = .ok o₀)
    (hf : finish { C with erased := whole C g } (whole C g) (given C g) (.app h args) o₀ = .ok o) :
    ExprPost C sc g n0 W ρ act o := by
  intro ht
  obtain ⟨-, -, hah, -, -⟩ := checkArgs_shape ihs hh hI.holes ha
  obtain ⟨rfl, hpr⟩ := applied_eq hah h₀
  obtain ⟨-, hsc₀, -⟩ := finish_spec hf
  have ht₀ : a.sc.taintedBy = none := by rw [hsc₀] at ht; exact ht
  obtain ⟨ρ', vs, hI', hvs, hok, hw, hrun⟩ := checkArgs_sound ih ihs hh (inv_ctx.2 hI) har rfl ha ht₀
  have hhead : sig.head = ⟨k, h.name⟩ := Sigs.find_head hsig
  obtain ⟨hbelow, hbounds⟩ := hI.sigsOk sig (List.mem_of_find?_eq_some hsig)
  have hvl : vs.length = sig.params.length := by simpa using (WantsSat.lengths hw).1
  have hS := hI.sigsClose ρ'
  obtain ⟨sig', hsig', -⟩ := hS.find hsig
  obtain ⟨V, hV⟩ : ∃ V, sig.ret.eval (ρ ++ ρ') vs = some V := by
    refine Term.eval_isSome _ ?_ (by rw [hvl]; exact hbounds)
    simp only [Sig.entriesBelow, Bool.and_eq_true] at hbelow
    exact Term.entriesBelow_mono hI'.length _ hbelow.2
  have hjunk : sig.head ≠ junkHead := fun e => by rw [hhead] at e; rw [e, hI.noJunk] at hsig'; cases hsig'
  have hres : ResOk W.Sc ⟨.app sig.head (a.res.map (·.term)), a.res.any (·.tainted), false⟩ (.app sig.head vs) := by
    refine ⟨by simpa [Value.noRemoved] using noRemoved_of_resOk hvs hok, ⟨V, ?_⟩, fun hut => ⟨V, ?_⟩⟩
    · simp only [WType, hjunk, ↓reduceIte]
      exact ⟨sig', by rw [hhead]; exact hsig', by rw [hS.ret_eval hsig hsig']; exact hV⟩
    · refine (hS.hasType_app_iff (by rw [hhead]; exact hsig)).2 ⟨WantsSat.teleSat hw fun t ht' => ?_, hV⟩
      simp only [List.any_eq_false] at hut
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ht'
      simp [hut r hr]
  have hvs1 : Term.evalList (ρ ++ ρ') []
      ([(⟨.app sig.head (a.res.map (·.term)), a.res.any (·.tainted), false⟩ : Res)].map (·.term)) =
        some [.app sig.head vs] := Term.evalList_singleton.2 ⟨_, Term.eval_app.2 ⟨vs, hvs, rfl⟩, rfl⟩
  obtain ⟨-, hw'⟩ := produced_sound hI'.sat.1 (hI'.sigs _ hI'.agree) hI.noJunk hI'.holes hvs1 ⟨hres, trivial⟩
    (fun g' h => let ⟨_, he⟩ := (given_ok hg g' h).env; ⟨_, Term.evalList_frame_ρ ρ' he⟩) hpr
  obtain ⟨hsc, hres', -, -⟩ := finish_untainted hf ht₀
  refine ⟨ρ', [.app sig.head vs], by rw [hsc]; exact inv_ctx.1 hI', by rw [hres']; exact hvs1,
    fun i r v hr hv => ?_, fun g' hg' envv henv => ?_, fun env hE => ?_⟩
  · rw [hres'] at hr
    cases i with
    | zero => cases hr; cases hv; exact hres
    | succ => simp at hr
  · rw [hres']
    exact given_wants (fun g'' h'' envv₁ henv₁ => (hw' g'' h'' envv₁ (Term.evalList_frame_ρ ρ' henv₁)).2) g' hg'
      envv henv
  refine finish_run hf ht₀ (given_length (C := C) hg fun g'' h'' envv₁ henv₁ =>
    (hw' g'' h'' envv₁ (Term.evalList_frame_ρ ρ' henv₁)).1) fun hwh hall _ => ?_
  have hCe : C.erased = false := by simp only [whole, Bool.or_eq_false_iff] at hwh; exact hwh.1
  have hut : a.res.any (·.tainted) = false := by simpa using hall
  obtain ⟨us, hev, hul, hm⟩ := hrun env hE
  refine ⟨_, .ctor hev hk.fns hk.kind, _, take_of_length rfl, fun i r u v hr hu hv _ => ?_⟩
  cases i with
  | succ => simp at hr
  | zero =>
    cases hr; cases hu; cases hv
    obtain ⟨sig'', hc, hmults⟩ := SigsClose.mults hS hsig
    rw [hhead]
    refine MultRel.of_rel _ (rel_app hc hmults (er := er) her hul hvl fun j p u v hp hu hv => ?_)
    obtain ⟨r, hr⟩ : ∃ r, a.res[j]? = some r := ⟨_, List.getElem?_eq_getElem (by
      rw [← List.length_map (f := fun r : Res => r.term), ← Term.length_evalList hvs]
      exact (List.getElem?_eq_some_iff.1 hv).1)⟩
    have hrt : r.tainted = false := by
      simp only [List.any_eq_false] at hut
      simpa using hut r (List.mem_of_getElem? hr)
    simpa [whole, hwh] using hm j r p u v hr hp hu hv hrt

end Pledge.Simple
