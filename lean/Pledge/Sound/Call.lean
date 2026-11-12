import Pledge.Sound.Match

namespace Pledge.Call

/-- The multiplicity of an argument's position (§16). -/
abbrev argMult (C : Ctx) (er : Bool) (p : TBinder) : Mult :=
  if C.erased || er || p.mult == .erased then .erased else .many

theorem posMult_arg (C : Ctx) (p : TBinder) (prev : List Res) (role owner : String) (er : Bool) :
    C.posMult (some (argGiven p prev role owner er)) 0 = argMult C er p := by
  cases er <;> simp [Ctx.posMult, argGiven, Given.erasedAt, argMult]

/-- One argument (§8): its ideal value meets its parameter, typed when untainted, and outside a type constructor's
argument it runs to a value related to it by its position's multiplicity; a `_` (§16) runs to `removed`, which is
related to its value since the position is erased or the value is a type. -/
theorem arg_sound {e : Expr} (ih : ExprSound e) (ihs : ExprShape e) {C : Ctx} {sc : Scope} {owner role : String}
    {er : Bool} {p : TBinder} {prev : List Res} {o : Out} {r : Res} {n0 : Nat} {W : World} {ρ prevv : List Value}
    {act : Act} (hI : Inv C sc n0 W ρ act) (hprev : Term.evalList ρ [] (prev.map (·.term)) = some prevv)
    (h : (if isHole e then holeArg C sc (argGiven p prev role owner er) p prev e.pos
      else checkExpr C sc (some (argGiven p prev role owner er)) e) = .ok o) (hr : o.res = [r])
    (ht : o.sc.taintedBy = none) :
    ∃ ρ₁ v, Inv C o.sc n0 W (ρ ++ ρ₁) act ∧ r.term.eval (ρ ++ ρ₁) [] = some v ∧ ResOk W.Sc r v ∧
      WantSat W.Sc (ρ ++ ρ₁) (Want.of p) prevv (!r.tainted) v ∧
      (C.inType = false → ∀ env, EnvRel W.Sc C.phase sc ρ env → ∃ ws u, Eval W.P env o.tree ws ∧ one ws = .ok u ∧
        (r.tainted = false → MultRel W.Sc C.phase (argMult C er p) u v)) := by
  split at h
  · obtain ⟨hc, hsc, htr, -⟩ := holeArg_spec hI.solving h
    obtain ⟨r', v, A, hres, hv, hA, hnr, hw, hty, his⟩ := holeArg_value hI.solving hI.sat.1 (hI.sigs ρ hI.agree)
      hI.noJunk hI.sigsOk hI.length hprev h
    rw [hr] at hres
    obtain rfl : r = r' := by simpa using hres
    refine ⟨[], v, by rw [hsc]; simpa using hI, by simpa using hv, ⟨hnr, ⟨A, hw⟩, fun ht => ⟨A, hty hI.sat ht⟩⟩,
      ⟨fun T hT => by cases hT; exact ⟨A, by simpa using hA, hnr, hw, fun h => hty hI.sat (by simpa using h)⟩,
        fun e he => by simpa using his e he⟩, fun hit env _ => ⟨[.removed], .removed, by rw [htr]; exact .removed,
          rfl, fun hrt => ?_⟩⟩
    cases hm : argMult C er p
    · simp only [argMult, Bool.or_eq_true, beq_iff_eq] at hm
      split at hm
      · cases hm
      · rename_i hne
        simp only [not_or] at hne
        have hce : C.erased = false := by simp at hne; exact hne.1.1
        have hga : (argGiven p prev role owner er).erasedAt 0 = false := by
          cases er <;> simp_all [argGiven, Given.erasedAt]
        rw [hce, hga, hit] at hc
        simp only [Bool.false_or] at hc
        have hTA : A = Value.TYPE := by
          rw [← Term.eval_subst hprev, hI.sat.eval_eq_of_identical hc] at hA
          simpa [Term.TYPE, Value.TYPE, Term.eval, Term.evalList] using hA.symm
        subst hTA
        exact removed_rel_type hI.typeHeads (hty hI.sat hrt)
    · exact MultRel.removed
  · obtain ⟨-, hnames, -, hpre, -⟩ := ihs C sc _ o hI.solving hI.holes h
    have hgok : ∀ g', some (argGiven p prev role owner er) = some g' → g'.Ok W.Sc ρ := by
      rintro g' ⟨⟩
      exact ⟨⟨prevv, by simpa [argGiven] using hprev⟩, fun h => by cases h⟩
    obtain ⟨ρ₁, vs₁, hI₁, hvs₁, hok₁, hw₁, hrun₁⟩ := (ih C sc _ n0 W ρ act o hI hgok h).1 ht
    rw [hr] at hvs₁ hok₁ hw₁ hrun₁
    obtain ⟨v, hv, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs₁)
    refine ⟨ρ₁, v, hI₁, hv, hok₁ 0 r v rfl rfl, (hw₁ _ rfl prevv (by simpa [argGiven] using hprev)).1,
      fun hit env hE => ?_⟩
    obtain ⟨us₁, hev₁, us₁', htk₁, hm₁⟩ := hrun₁ hit env hE
    obtain ⟨u, hou, rfl⟩ := one_of_take htk₁
    exact ⟨us₁, u, hev₁, hou, fun hrt => by simpa [posMult_arg] using hm₁ 0 r u v rfl rfl rfl hrt⟩

/-- The arguments of a call or application (§8): their ideal values meet the telescope, the untainted ones typed, and
outside a type constructor's argument they run to values related to them, each by its position's multiplicity. -/
theorem args_sound {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr) (ihs : ∀ a ∈ args, ExprShape a.expr) :
    ∀ {C : Ctx} {sc : Scope} {owner role : String} {er : Bool} {params : Telescope} {prev : List Res}
      {a : ArgsOut} {n0 : Nat} {W : World} {ρ : List Value} {act : Act} {prevv : List Value},
      Inv C sc n0 W ρ act → params.length = args.length → Term.evalList ρ [] (prev.map (·.term)) = some prevv →
      checkArgs C sc owner role er params prev args = .ok a → a.sc.taintedBy = none →
      ∃ ρ' vs, Inv C a.sc n0 W (ρ ++ ρ') act ∧ Term.evalList (ρ ++ ρ') [] (a.res.map (·.term)) = some vs ∧
        (∀ (i : Nat) (r : Res) (v : Value), a.res[i]? = some r → vs[i]? = some v → ResOk W.Sc r v) ∧
        WantsSat W.Sc (ρ ++ ρ') (params.map Want.of) prevv (a.res.map (!·.tainted)) vs ∧
        (C.inType = false → ∀ env, EnvRel W.Sc C.phase sc ρ env → ∃ us, EvalList W.P env (a.trees.map Arg.expr) us ∧
          us.length = vs.length ∧ ∀ (i : Nat) (r : Res) (p : TBinder) (u v : Value), a.res[i]? = some r →
            params[i]? = some p → us[i]? = some u → vs[i]? = some v → r.tainted = false →
            MultRel W.Sc C.phase (argMult C er p) u v) := by
  induction args with
  | nil =>
    intro C sc owner role er params prev a n0 W ρ act prevv hI hl _ h _
    cases params with
    | cons => simp at hl
    | nil =>
      simp only [checkArgs, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨[], [], by simpa using hI, rfl, by simp, trivial, fun _ env _ => ⟨[], .nil, rfl, by simp⟩⟩
  | cons arg args ihas =>
    intro C sc owner role er params prev a n0 W ρ act prevv hI hl hprev h ht
    obtain ⟨m, e⟩ := arg
    cases params with
    | nil => simp at hl
    | cons p ps =>
      obtain ⟨o, r, rest, ho, hr, hrest, rfl⟩ := checkArgs_cons h
      have ht' : rest.sc.taintedBy = none := ht
      have ih' := fun a ha => ih a (List.mem_cons_of_mem _ ha)
      have ihs' := fun a ha => ihs a (List.mem_cons_of_mem _ ha)
      have hg₁ : ShapeFill.Grows sc o.sc := by
        split at ho
        · rw [(holeArg_spec hI.solving ho).2.1]; exact ShapeFill.Grows.refl hI.holes
        · exact ihs _ List.mem_cons_self C sc _ o hI.solving hI.holes ho
      obtain ⟨-, hnames₁, hh₁, hpre₁, -⟩ := hg₁
      have ht₁ : o.sc.taintedBy = none := by
        cases h₁ : o.sc.taintedBy with
        | none => rfl
        | some _ =>
          have := (ShapeFill.args_grows ihs' hh₁ hrest hI.solving).2.2.2.2 (by simp [h₁])
          simp [ht'] at this
      obtain ⟨ρ₁, v, hI₁, hv, hok₁, hb, hrun₁⟩ := arg_sound (ih _ List.mem_cons_self) (ihs _ List.mem_cons_self) hI
        hprev ho hr ht₁
      obtain ⟨ρ₂, vs₂, hI₂, hvs₂, hok₂, hw₂, hrun₂⟩ := ihas ih' ihs' hI₁ (by simpa using hl)
        (by
          rw [List.map_append, List.map_singleton]
          exact Term.evalList_append (Term.evalList_frame_ρ ρ₁ hprev) (Term.evalList_singleton.2 ⟨v, hv, rfl⟩))
        hrest ht'
      refine ⟨ρ₁ ++ ρ₂, v :: vs₂, by simpa using hI₂, ?_, fun i r' v' hr' hv' => ?_, ?_, fun hit env hE => ?_⟩
      · simp only [List.map_cons]
        rw [← List.append_assoc]
        exact Term.evalList_cons_eq_some.2 ⟨v, vs₂, Term.eval_frame_ρ ρ₂ hv, hvs₂, rfl⟩
      · cases i with
        | zero => cases hr'; cases hv'; exact hok₁
        | succ i => exact hok₂ i r' v' (by simpa using hr') (by simpa using hv')
      · rw [← List.append_assoc]
        exact ⟨hb.frame ρ₂, hw₂⟩
      · obtain ⟨ws, u, hev₁, hou, hm₁⟩ := hrun₁ hit env hE
        obtain ⟨us₂, hev₂, hl₂, hm₂⟩ := hrun₂ hit env (EnvRel.extend ρ₁ hE hnames₁ hpre₁ hI.sat.1.1)
        refine ⟨u :: us₂, .cons hev₁ hou hev₂, by simp [hl₂], fun i r' p' u' v' hr' hp' hu' hv' hrt => ?_⟩
        cases i with
        | zero => cases hr'; cases hp'; cases hu'; cases hv'; exact hm₁ hrt
        | succ i =>
          exact hm₂ i r' p' u' v' (by simpa using hr') (by simpa using hp') (by simpa using hu') (by simpa using hv')
            hrt

/-- Untainted arguments related outside an erased position are related by the parameters' multiplicities. -/
theorem multsRel_of_args {S : Sigs} {phase : Nat} {C : Ctx} {params : Telescope} {rs : List Res}
    {us vs : List Value} (hC : C.erased = false) (hul : us.length = vs.length) (hvl : vs.length = params.length)
    (hrl : rs.length = params.length) (ht : ∀ r ∈ rs, r.tainted = false)
    (h : ∀ (i : Nat) (r : Res) (p : TBinder) (u v : Value), rs[i]? = some r → params[i]? = some p → us[i]? = some u →
      vs[i]? = some v → r.tainted = false → MultRel S phase (argMult C false p) u v) :
    MultsRel S phase (params.map (·.mult)) us vs := by
  refine ⟨by simp [hul, hvl], by simp [hvl], fun k m u v hm hu hv => ?_⟩
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 (by simpa using hm)
  obtain ⟨r, hr⟩ : ∃ r, rs[k]? = some r :=
    ⟨_, List.getElem?_eq_getElem (by rw [hrl, ← hvl]; exact (List.getElem?_eq_some_iff.1 hv).1)⟩
  have := h k r p u v hr hp hu hv (ht r (List.mem_of_getElem? hr))
  cases hpm : p.mult <;> simp_all [argMult]

theorem TeleOk.getElem {S : Sigs} {ρ : List Value} :
    ∀ {typed : Nat → Bool} {tele : Telescope} {env vs : List Value}, TeleOk S ρ typed tele env vs →
      ∀ (i : Nat) (v : Value), vs[i]? = some v →
        v.noRemoved = true ∧ (∃ A, WType S v A) ∧ (typed i = true → ∃ V, HasType S v V)
  | _, [], _, [], _, _, _, hv => by simp at hv
  | _, _ :: _, _, v :: _, ⟨⟨A, _, h1, h2, h3⟩, _, _⟩, 0, _, hv => by
    cases hv; exact ⟨h1, ⟨A, h2⟩, fun h => ⟨A, h3 h⟩⟩
  | _, _ :: _, _, _ :: _, ⟨_, _, ht⟩, i + 1, v, hv => TeleOk.getElem ht i v (by simpa using hv)
  | _, [], _, _ :: _, h, _, _, _ | _, _ :: _, _, [], h, _, _, _ => h.elim

theorem WantsSat.of_erase {S : Sigs} {ρ : List Value} :
    ∀ {ws : List Want} {env : List Value} {ts : List Bool} {vs : List Value},
      WantsSat S ρ (ws.map fun w => { w with mult := .erased }) env ts vs → WantsSat S ρ ws env ts vs
  | [], _, [], [], _ => trivial
  | _ :: _, _, _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨⟨h1.1, h1.2⟩, WantsSat.of_erase h2⟩
  | [], _, [], _ :: _, h | [], _, _ :: _, _, h | _ :: _, _, [], _, h | _ :: _, _, _ :: _, [], h => h.elim

theorem Given.erasedAt_of_allErased {g : Given} (h : g.allErased = true) {i : Nat} (hi : i < g.wants.length) :
    g.erasedAt i = true := by
  simp only [Given.allErased, Bool.and_eq_true, List.all_eq_true] at h
  simp [Given.erasedAt, List.getElem?_eq_getElem hi, h.2 _ (List.getElem_mem hi)]

theorem MultsRel.cons {S : Sigs} {phase : Nat} {m : Mult} {ms : List Mult} {a v : Value} {as vs : List Value}
    (h : MultRel S phase m a v) (hs : MultsRel S phase ms as vs) : MultsRel S phase (m :: ms) (a :: as) (v :: vs) := by
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨by simp [h1], by simp [h2], fun k m' a' v' hm ha hv => ?_⟩
  cases k with
  | zero => cases hm; cases ha; cases hv; exact h
  | succ k => exact h3 k m' a' v' (by simpa using hm) (by simpa using ha) (by simpa using hv)

theorem opened_res {sc : Scope} {tele : Telescope} {env : List Term} {kind : String} {pos : Pos} {taint : Nat → Bool}
    {i : Nat} {r : Res} (hr : (opened sc tele env kind pos taint).2[i]? = some r) :
    ∃ b, tele[i]? = some b ∧ r.tainted = taint i ∧ r.erased = (b.mult == .erased) := by
  obtain ⟨-, -, hl, hent⟩ := opened_shape sc tele env kind pos taint
  have hi : i < tele.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hr).1
  have hb := List.getElem?_eq_getElem hi
  rw [(hent i _ hb).1] at hr
  cases hr
  exact ⟨_, hb, rfl, rfl⟩

/-- A call whose arguments checked, in an untainted scope, with ideal results meeting the returns (typed when the call
is untainted) and, for an untainted call outside a wholly erased position, run-time results related to them. -/
theorem post {C : Ctx} {sc : Scope} {g g₁ : Option Given} {whole : Bool} {n0 : Nat} {W : World}
    {ρ ρ₁ : List Value} {act : Act} {h : Name} {args : List Arg} {sig : FnSig} {a : ArgsOut} {vs rs : List Value}
    {tainted : Bool} {o₀ o : Out}
    (hw : whole = (C.erased || g.any (·.allErased))) (hg₁ : g₁ = if C.erased then g.map (·.erase) else g)
    (hg : ∀ g', g = some g' → g'.Ok W.Sc ρ) (hIa : Inv C a.sc n0 W (ρ ++ ρ₁) act)
    (hvs : Term.evalList (ρ ++ ρ₁) [] (a.res.map (·.term)) = some vs)
    (hrs : TeleOk W.Sc (ρ ++ ρ₁) (fun _ => !tainted) sig.returns vs rs)
    (hrun : tainted = false → whole = false → C.inType = false → ∀ env, EnvRel W.Sc C.phase sc ρ env →
      ∃ us, Eval W.P env (.app h a.trees) us ∧ MultsRel W.Sc C.phase (sig.returns.map (·.mult)) us rs)
    (happ : applied (opened a.sc sig.returns (a.res.map (·.term)) h.name h.pos fun _ => tainted).1 g₁ h.pos
      (opened a.sc sig.returns (a.res.map (·.term)) h.name h.pos fun _ => tainted).2 (.app h a.trees)
      (some sc.holes.length) a.snaps = .ok o₀)
    (hf : finish (C.enter whole) whole g₁ (.app h args) o₀ = .ok o) :
    ExprPost C sc g n0 W ρ act o := by
  generalize hop : opened a.sc sig.returns (a.res.map (·.term)) h.name h.pos (fun _ => tainted) = op at happ
  obtain ⟨-, -, hlen, -⟩ := opened_shape a.sc sig.returns (a.res.map (·.term)) h.name h.pos fun _ => tainted
  rw [hop] at hlen
  have hfst := opened_fst a.sc sig.returns (a.res.map (·.term)) h.name h.pos fun _ => tainted
  rw [hop] at hfst
  have hholes : op.1.holes = [] := by rw [hfst]; exact hIa.holes
  have hunt : op.1.taintedBy = none := by rw [hfst]; exact hIa.untainted
  obtain ⟨rfl, hprod⟩ := applied_eq hholes happ
  obtain ⟨-, hsc, -, hres, htree, herase⟩ := finish_spec hf
  simp only [hunt, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hres
  intro _
  obtain ⟨hsat, hrv⟩ := opened_sound (kind := h.name) (pos := h.pos) (taint := fun _ => tainted) hIa.sat hvs hrs
  rw [hop] at hsat hrv
  have hI' : Inv C op.1 n0 W (ρ ++ ρ₁ ++ rs) act := hIa.extend hsat (by rw [hfst]) (by rw [hfst]) hholes hunt
  have hok : ∀ (i : Nat) (r : Res) (v : Value), op.2[i]? = some r → rs[i]? = some v → ResOk W.Sc r v := by
    intro i r v hr hv
    obtain ⟨b, -, hrt, -⟩ := opened_res (hop ▸ hr)
    obtain ⟨h1, h2, h3⟩ := TeleOk.getElem hrs i v hv
    exact ⟨h1, h2, fun ht => h3 (by simp [← hrt, ht])⟩
  have hframe {t : List Term} {us : List Value} (he : Term.evalList ρ [] t = some us) :
      Term.evalList (ρ ++ ρ₁ ++ rs) [] t = some us := by
    rw [List.append_assoc]; exact Term.evalList_frame_ρ _ he
  have hrl : rs.length = op.2.length := by rw [hrs.length_eq, hlen]
  have hpr := produced_sound hsat.1 (hI'.sigs _ hI'.agree) hI'.noJunk hholes hrv (ResOks.of_getElem hrl.symm hok)
    (fun g'' hg'' => by
      subst hg₁
      cases hce : C.erased <;> simp only [hce, Bool.false_eq_true, ↓reduceIte] at hg''
      · obtain ⟨envv, he⟩ := (hg g'' hg'').env; exact ⟨envv, hframe he⟩
      · obtain ⟨g', rfl, rfl⟩ := Option.map_eq_some_iff.1 hg''
        obtain ⟨envv, he⟩ := (hg g' rfl).env; exact ⟨envv, hframe he⟩) hprod
  refine ⟨ρ₁ ++ rs, rs, by rw [hsc, ← List.append_assoc]; exact hI', by rw [hres, ← List.append_assoc]; exact hrv,
    fun i r v hr hv => hok i r v (hres ▸ hr) hv, fun g' hg' envv henv => ?_, fun hit env hE => ?_⟩
  · rw [hres, ← List.append_assoc]
    subst hg₁
    cases hce : C.erased
    · exact ((hpr.2 g' (by simp [hce, hg']) envv (hframe henv)).2)
    · exact WantsSat.of_erase ((hpr.2 g'.erase (by simp [hce, hg']) envv (hframe henv)).2)
  · rw [htree, hres]
    cases hrm : (whole || op.2.all (·.tainted))
    rotate_left
    · simp only [↓reduceIte]
      refine ⟨_, .removed, ResRel.removed fun i r hr hrt => ?_⟩
      rcases Bool.or_eq_true _ _ ▸ hrm with hwh | hall
      · rw [hw] at hwh
        cases hce : C.erased
        · rw [hce, Bool.false_or] at hwh
          obtain ⟨g', rfl, hg'⟩ := (Option.any_eq_true _ _).1 hwh
          have hl := (hpr.2 g' (by rw [hg₁]; simp [hce]) _ (hframe (hg g' rfl).env.choose_spec)).1
          have hi : i < g'.wants.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hr).1
          simp [Ctx.posMult, hce, Given.erasedAt_of_allErased hg' hi]
        · simp [Ctx.posMult, hce]
      · have := List.all_eq_true.1 hall r (List.mem_of_getElem? hr)
        simp [hrt] at this
    · simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.or_eq_false_iff, List.all_eq_false] at hrm
      obtain ⟨hwf, r₀, hr₀, hr₀t⟩ := hrm
      obtain ⟨i₀, hi₀⟩ := List.getElem_of_mem hr₀
      obtain ⟨-, -, ht₀, -⟩ := opened_res (hop ▸ (List.getElem?_eq_some_iff.2 hi₀))
      have htf : tainted = false := by simpa [ht₀] using hr₀t
      have hcf : C.erased = false := by rw [hw] at hwf; simp at hwf; exact hwf.1
      obtain ⟨us, hev, hl₁, hl₂, hm⟩ := hrun htf hwf hit env hE
      refine ⟨us, hev, us, take_of_length (by simp at hl₁; rw [hl₁, ← hlen]), fun i r u v hr hu hv hrt => ?_⟩
      obtain ⟨b, hb, -, hre⟩ := opened_res (hop ▸ hr)
      have hmr := hm i b.mult u v (by simp [hb]) hu hv
      cases hbm : b.mult
      · rw [hbm] at hmr; exact MultRel.of_rel _ hmr
      · rw [hbm] at hmr
        have := herase hwf i r (by rw [hres]; exact hr) (by rw [hre, hbm]; rfl)
        rw [hg₁, hcf] at this
        simp only [Bool.false_eq_true, ↓reduceIte] at this
        simpa [Ctx.posMult, hcf, this] using hmr

/-- A call whose arguments checked, given that the measure decreases for an untainted call. -/
theorem core {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr)
    (ihs : ∀ a ∈ args, ExprShape a.expr) {C : Ctx} {sc : Scope}
    {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {act : Act} {o o₀ : Out} {sig : FnSig}
    {a : ArgsOut} (hI : Inv C sc n0 W ρ act) (hg : ∀ g', g = some g' → g'.Ok W.Sc ρ)
    (hfo : FnOk n0 C.phase W C.fn act h.name sig) (har : sig.params.length = args.length)
    (ha : checkArgs (C.enter (C.erased || g.any (·.allErased))) sc h.name "parameter" false sig.params []
      args = .ok a)
    (hlt : ∀ ρ' vs d, Inv C a.sc n0 W (ρ ++ ρ') act → Term.evalList (ρ ++ ρ') [] (a.res.map (·.term)) = some vs →
      vs.length = sig.params.length → W.P.fns.find h.name = some d → d.subterm = sig.subterm →
      d.subterm.count true ≤ d.pad →
      (if C.fn.any (·.group.contains h.name) then d.group = act.group ∧ d.pad = act.subs.length
        else d.group < act.group) → Act.lt (calleeAct d vs) act)
    (happ : applied (opened a.sc sig.returns (a.res.map (·.term)) h.name h.pos
        fun _ => sig.tainted || a.res.any (·.tainted)).1 (if C.erased then g.map (·.erase) else g) h.pos
      (opened a.sc sig.returns (a.res.map (·.term)) h.name h.pos fun _ => sig.tainted || a.res.any (·.tainted)).2
      (.app h a.trees) (some sc.holes.length) a.snaps = .ok o₀)
    (hf : finish (C.enter (C.erased || g.any (·.allErased))) (C.erased || g.any (·.allErased))
      (if C.erased then g.map (·.erase) else g) (.app h args) o₀ = .ok o) :
    ExprPost C sc g n0 W ρ act o := by
  intro hnt
  have hI₁ : Inv (C.enter (C.erased || g.any (·.allErased))) sc n0 W ρ act := hI.congr_ctx rfl rfl rfl
  obtain ⟨-, -, hah, -, -⟩ := ShapeFill.args_grows ihs hI.holes ha hI.solving
  have hopf := opened_fst a.sc sig.returns (a.res.map (·.term)) h.name h.pos
    fun _ => sig.tainted || a.res.any (·.tainted)
  obtain ⟨ho₀, -⟩ := applied_eq (by rw [hopf]; exact hah) happ
  obtain ⟨-, hsc, -⟩ := finish_spec hf
  have hat : a.sc.taintedBy = none := by rw [hsc, ho₀, hopf] at hnt; exact hnt
  obtain ⟨ρ₁, vs, hIa, hvs, -, hw, hrun⟩ := args_sound ih ihs hI₁ har rfl ha hat
  have hIa' : Inv C a.sc n0 W (ρ ++ ρ₁) act := hIa.congr_ctx rfl rfl rfl
  have hlen := WantsSat.lengths hw
  simp only [List.length_map] at hlen
  cases ht : (sig.tainted || a.res.any (·.tainted)) with
  | false =>
    simp only [Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at ht
    obtain ⟨hst, hall⟩ := ht
    obtain ⟨d, hd, -, hds, -, hdc, hspec, hgrp⟩ := hfo.defn hst
    have hts : TeleSat W.Sc (ρ ++ ρ₁) sig.params [] vs := WantsSat.teleSat hw fun t ht => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ht
      simp [hall r hr]
    obtain ⟨rs, hrs, hrun'⟩ := hspec vs ((TeleSat.iff_of_entriesBelow hIa.agree (List.all_eq_true.2 hfo.params)).1 hts)
      (hlt ρ₁ vs d hIa' hvs hlen.1 hd hds hdc hgrp)
    have hrs' := (TeleSat.iff_of_entriesBelow hIa.agree (List.all_eq_true.2 hfo.returns)).2 hrs
    refine post rfl rfl hg hIa' hvs (TeleSat.teleOk hIa.noJunk _ hrs')
      (fun _ hwf hit env hE => ?_) happ hf hnt
    obtain ⟨us, hev, hul, hrel⟩ := hrun hit env hE
    obtain ⟨rs', hcall, hmr⟩ := hrun' us (multsRel_of_args hwf hul hlen.1 (by simpa using hlen.2) hall hrel)
    exact ⟨rs', .call hev hd hcall, hmr⟩
  | true =>
    have hcons := hfo.cons (ρ ++ ρ₁) hIa.agree vs (hw.weaken (by simp [hlen.2]) fun i hi => by simp at hi)
    obtain ⟨rs, hrsw⟩ := WantsCons.open hcons
    refine post rfl rfl hg hIa' hvs (by rw [ht]; exact WantsSat.teleOk _ hrsw fun k hk => by simp at hk)
      (fun htf => by rw [ht] at htf; cases htf) happ hf hnt

/-- A call (§8, §9, §12): see `call_sound`. -/
theorem sound {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr)
    (ihs : ∀ a ∈ args, ExprShape a.expr) {C : Ctx} {sc : Scope}
    {g : Option Given} {n0 : Nat} {W : World} {ρ : List Value} {act : Act} {o : Out} {m : String} {sig : FnSig}
    (hI : Inv C sc n0 W ρ act) (hg : ∀ g', g = some g' → g'.Ok W.Sc ρ)
    (hgl : C.global h.name = some (.fn m (some sig))) (hc : checkExpr C sc g (.app h args) = .ok o) :
    ExprPost C sc g n0 W ρ act o := by
  unfold checkExpr at hc
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 hc
  simp only [Ctx.global] at hgl h₀
  simp only [hgl] at h₀
  cases hF : C.fn.filter (·.group.contains h.name) with
  | none =>
    simp only [hF] at h₀
    obtain ⟨u, -, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨plan, -, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨u, har, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨a, ha, h₀⟩ := bind_eq_ok.1 h₀
    rw [keep_ok] at h₀
    refine core ih ihs hI hg (hI.globals.fn hgl) (arity_ok har) ha ?_ h₀ hf
    intro ρ' vs d _ _ _ _ _ _ hgrp
    have hany : C.fn.any (·.group.contains h.name) = false := by
      cases hfn : C.fn with
      | none => rfl
      | some f => simpa [hfn, Option.filter] using hF
    simp only [hany, Bool.false_eq_true, ↓reduceIte] at hgrp
    exact Act.lt_of_group hgrp
  | some fn =>
    simp only [hF] at h₀
    obtain ⟨plan, hplan, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨u, har, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨a, ha, h₀⟩ := bind_eq_ok.1 h₀
    rw [keep_ok] at h₀
    obtain ⟨⟨subs, k⟩, hm, rfl⟩ : ∃ p, marks h.pos args h.name sig fn = .ok p ∧ plan = some p := by
      cases hmk : marks h.pos args h.name sig fn with
      | error e => simp [hmk, Functor.map, Except.map] at hplan
      | ok p => simp [hmk, Functor.map, Except.map] at hplan; exact ⟨p, rfl, hplan.symm⟩
    obtain ⟨u, hdec, h₀⟩ := bind_eq_ok.1 h₀
    have hCfn : C.fn = some fn := by
      cases hfn : C.fn with
      | none => simp [hfn] at hF
      | some f => simp only [hfn, Option.filter] at hF; split at hF <;> simp_all
    have hfo := hI.globals.fn hgl
    refine core ih ihs hI hg hfo (arity_ok har) ha ?_ h₀ hf
    intro ρ' vs d hI' hvs hl _ hds hdc hgrp
    have hany : C.fn.any (·.group.contains h.name) = true := by
      simpa [hCfn] using (Option.filter_eq_some_iff.1 hF).2
    simp only [hany, ↓reduceIte] at hgrp
    obtain ⟨ss, hss, hact⟩ := hI'.act fn hCfn
    exact call_lt hI'.sat.rulesHold hm hdec hvs hss hact hds (hfo.subterm.trans hl.symm) hdc hgrp.1 hgrp.2

end Pledge.Call
