import Pledge.Sound.Match

namespace Pledge.Call

theorem isHole_false {e : Expr} (h : e.holeFree = true) : isHole e = false := by
  cases e with
  | var x => obtain ⟨n, p⟩ := x; cases n <;> simp_all [isHole, Expr.holeFree]
  | _ => rfl

theorem checkArgs_cons {C : Ctx} {sc : Scope} {owner role : String} {p : TBinder} {ps : Telescope} {prev : List Res}
    {m : Option Mark} {e : Expr} {as : List Arg} {out : ArgsOut} (hh : e.holeFree = true)
    (h : checkArgs C sc owner role false (p :: ps) prev (.mk m e :: as) = .ok out) :
    ∃ o r rest, checkExpr C sc (some (argGiven p prev role owner false)) e = .ok o ∧ o.res = [r] ∧
      checkArgs C o.sc owner role false ps (prev ++ [r]) as = .ok rest ∧
      out = ⟨rest.sc, r :: rest.res, .mk m o.tree :: rest.trees, o.snaps ++ rest.snaps⟩ := by
  simp only [checkArgs, isHole_false hh, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
  obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
  obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  rw [keep_ok] at hr hrest
  exact ⟨o, r, rest, ho, single_ok hr, hrest, h.symm⟩

theorem checkArgs_nil {C : Ctx} {sc : Scope} {owner role : String} {params : Telescope} {prev : List Res}
    {out : ArgsOut} (h : checkArgs C sc owner role false params prev [] = .ok out) : out = ⟨sc, [], [], []⟩ := by
  simp only [checkArgs, pure, Except.pure, Except.ok.injEq] at h; exact h.symm

theorem checkArgs_noParam {C : Ctx} {sc : Scope} {owner role : String} {prev : List Res} {a : Arg} {as : List Arg}
    {out : ArgsOut} (h : checkArgs C sc owner role false [] prev (a :: as) = .ok out) : False := by
  obtain ⟨m, e⟩ := a
  simp [checkArgs, internal, failAt_eq] at h

/-- What checking arguments keeps, whatever the scope's taint. -/
theorem args_shape {args : List Arg} (ihs : ∀ a ∈ args, ExprShape a.expr) (hh : ∀ a ∈ args, a.expr.holeFree = true) :
    ∀ {C : Ctx} {sc : Scope} {owner role : String} {params : Telescope} {prev : List Res} {out : ArgsOut},
      sc.holes = [] → checkArgs C sc owner role false params prev args = .ok out →
      out.sc.sigs = sc.sigs ∧ out.sc.names = sc.names ∧ out.sc.holes = [] ∧ sc.Γ.eraseRules <+: out.sc.Γ.eraseRules ∧
        (sc.taintedBy.isSome → out.sc.taintedBy.isSome) := by
  induction args with
  | nil =>
    intro C sc owner role params prev out hho h
    obtain rfl := checkArgs_nil h
    exact ⟨rfl, rfl, hho, List.prefix_refl _, id⟩
  | cons arg args ih =>
    intro C sc owner role params prev out hho h
    obtain ⟨m, e⟩ := arg
    cases params with
    | nil => exact (checkArgs_noParam h).elim
    | cons p ps =>
      obtain ⟨o, r, rest, ho, -, hrest, rfl⟩ := checkArgs_cons (hh _ List.mem_cons_self) h
      obtain ⟨h1, h2, h3, h4, h5⟩ := ihs _ List.mem_cons_self C sc _ o hho ho
      obtain ⟨h1', h2', h3', h4', h5'⟩ := ih (fun a ha => ihs a (List.mem_cons_of_mem _ ha))
        (fun a ha => hh a (List.mem_cons_of_mem _ ha)) h3 hrest
      exact ⟨h1'.trans h1, h2'.trans h2, h3', h4.trans h4', h5' ∘ h5⟩

/-- The multiplicity of an argument's position, under a context erased or not (§16). -/
def argMult (erased : Bool) (p : TBinder) : Mult := if erased || p.mult == .erased then .erased else .many

/-- Run-time arguments related to ideal ones by their positions' multiplicities, where untainted. -/
def ArgsRel (S : Sigs) (phase : Nat) (erased : Bool) : Telescope → List Res → List Value → List Value → Prop
  | [], [], [], [] => True
  | p :: ps, r :: rs, a :: as, v :: vs => (r.tainted = false → MultRel S phase (argMult erased p) a v) ∧
    ArgsRel S phase erased ps rs as vs
  | _, _, _, _ => False

theorem posMult_arg (C : Ctx) (p : TBinder) (prev : List Res) (role owner : String) :
    C.posMult (some (argGiven p prev role owner false)) 0 = argMult C.erased p := by
  simp [Ctx.posMult, argMult, Given.erasedAt, argGiven, Want.of]

theorem want_of (p : TBinder) : ({ Want.of p with mult := if false = true then .erased else p.mult } : Want) =
    Want.of p := rfl

/-- The arguments of a call (§8): their ideal values meet the parameters, the untainted ones typed, and they run to
values related to those by their positions' multiplicities. -/
theorem args_sound {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr) (ihs : ∀ a ∈ args, ExprShape a.expr)
    (hh : ∀ a ∈ args, a.expr.holeFree = true) :
    ∀ {C : Ctx} {sc : Scope} {owner role : String} {params : Telescope} {prev : List Res} {out : ArgsOut}
      {n0 : Nat} {W : World} {ρ : List Value} {act : Act} {prevv : List Value},
      Inv C sc n0 W ρ act → Term.evalList ρ [] (prev.map (·.term)) = some prevv → params.length = args.length →
      checkArgs C sc owner role false params prev args = .ok out → out.sc.taintedBy = none →
      ∃ ρ' vs, Inv C out.sc n0 W (ρ ++ ρ') act ∧ Term.evalList (ρ ++ ρ') [] (out.res.map (·.term)) = some vs ∧
        WantsSat W.Sc (ρ ++ ρ') (params.map Want.of) prevv (out.res.map (!·.tainted)) vs ∧
        ∀ env, EnvRel W.Sc C.phase sc ρ env → ∃ us, EvalList W.P env (out.trees.map Arg.expr) us ∧
          ArgsRel W.Sc C.phase C.erased params out.res us vs := by
  induction args with
  | nil =>
    intro C sc owner role params prev out n0 W ρ act prevv hI _ hl h _
    obtain rfl := checkArgs_nil h
    cases params with
    | cons => simp at hl
    | nil => exact ⟨[], [], by simpa using hI, rfl, trivial, fun env _ => ⟨[], .nil, trivial⟩⟩
  | cons arg args ihr =>
    intro C sc owner role params prev out n0 W ρ act prevv hI hprev hl h hout
    obtain ⟨m, e⟩ := arg
    cases params with
    | nil => exact (checkArgs_noParam h).elim
    | cons p ps =>
      have he := List.mem_cons_self (a := Arg.mk m e) (l := args)
      have ht : ∀ a ∈ args, a ∈ Arg.mk m e :: args := fun a ha => List.mem_cons_of_mem _ ha
      obtain ⟨o, r, rest, ho, hor, hrest, rfl⟩ := checkArgs_cons (hh _ he) h
      obtain ⟨hsig₁, hnam₁, hho₁, hpre₁, -⟩ := ihs _ he C sc _ o hI.holes ho
      have hosc : o.sc.taintedBy = none := by
        cases hx : o.sc.taintedBy with
        | none => rfl
        | some _ =>
          have := (args_shape (fun a ha => ihs a (ht a ha)) (fun a ha => hh a (ht a ha)) hho₁ hrest).2.2.2.2
            (by simp [hx])
          simp [show rest.sc.taintedBy = none from hout] at this
      have hgok : ∀ g', some (argGiven p prev role owner false) = some g' → g'.Ok W.Sc ρ := by
        rintro g' ⟨⟩
        exact ⟨⟨prevv, by simpa [argGiven] using hprev⟩, fun hw => by simp [argGiven] at hw⟩
      obtain ⟨ρ₁, vs₁, hI₁, hvs₁, -, hw₁, hrun₁⟩ := (ih _ he C sc _ n0 W ρ act o hI hgok ho).1 hosc
      rw [hor] at hvs₁ hw₁ hrun₁
      obtain ⟨v, hv, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs₁)
      have hwv : WantSat W.Sc (ρ ++ ρ₁) (Want.of p) prevv (!r.tainted) v := by
        have := hw₁ _ rfl prevv (by simpa [argGiven] using hprev)
        exact this.1
      have hprev' : Term.evalList (ρ ++ ρ₁) [] ((prev ++ [r]).map (·.term)) = some (prevv ++ [v]) := by
        rw [List.map_append, List.map_singleton]
        exact Term.evalList_append (Term.evalList_frame_ρ ρ₁ hprev) (Term.evalList_singleton.2 ⟨v, hv, rfl⟩)
      obtain ⟨ρ₂, vs₂, hI₂, hvs₂, hw₂, hrun₂⟩ := ihr (fun a ha => ih a (ht a ha)) (fun a ha => ihs a (ht a ha))
        (fun a ha => hh a (ht a ha)) hI₁ hprev' (by simpa using hl) hrest hout
      refine ⟨ρ₁ ++ ρ₂, v :: vs₂, by simpa using hI₂, ?_, ?_, fun env hE => ?_⟩
      · simp only [List.map_cons]
        rw [← List.append_assoc]
        exact Term.evalList_cons_eq_some.2 ⟨v, vs₂, Term.eval_frame_ρ ρ₂ hv, hvs₂, rfl⟩
      · rw [← List.append_assoc]
        exact ⟨hwv.frame ρ₂, hw₂⟩
      · obtain ⟨us₁, hev₁, us', htk, hrel⟩ := hrun₁ env hE
        obtain ⟨u, hu, rfl⟩ := one_of_take htk
        obtain ⟨us₂, hev₂, hrel₂⟩ := hrun₂ env (EnvRel.extend ρ₁ hE hnam₁ hpre₁ hI.sat.1.1)
        refine ⟨u :: us₂, .cons hev₁ hu hev₂, fun hrt => ?_, hrel₂⟩
        have := hrel 0 r u v rfl rfl rfl hrt
        rwa [posMult_arg] at this

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

/-- Untainted arguments related outside an erased position are related by the parameters' multiplicities. -/
theorem ArgsRel.multsRel {S : Sigs} {phase : Nat} :
    ∀ {params : Telescope} {rs : List Res} {as vs : List Value}, ArgsRel S phase false params rs as vs →
      (∀ r ∈ rs, r.tainted = false) → MultsRel S phase (params.map (·.mult)) as vs
  | [], [], [], [], _, _ => ⟨rfl, rfl, by simp⟩
  | p :: _, r :: _, _ :: _, _ :: _, ⟨h1, h2⟩, ht => by
    refine MultsRel.cons ?_ (ArgsRel.multsRel h2 fun r' hr' => ht r' (List.mem_cons_of_mem _ hr'))
    have := h1 (ht r List.mem_cons_self)
    cases hm : p.mult <;> simp_all [argMult]
  | [], [], [], _ :: _, h, _ | [], [], _ :: _, _, h, _ | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _
  | _ :: _, _ :: _, [], _, h, _ | _ :: _, _ :: _, _ :: _, [], h, _ => h.elim

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
    (hrun : tainted = false → whole = false → ∀ env, EnvRel W.Sc C.phase sc ρ env →
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
    fun i r v hr hv => hok i r v (hres ▸ hr) hv, fun g' hg' envv henv => ?_, fun env hE => ?_⟩
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
      obtain ⟨us, hev, hl₁, hl₂, hm⟩ := hrun htf hwf env hE
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
    (ihs : ∀ a ∈ args, ExprShape a.expr) (hh : ∀ a ∈ args, a.expr.holeFree = true) {C : Ctx} {sc : Scope}
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
  obtain ⟨-, -, hah, -, -⟩ := args_shape ihs hh hI.holes ha
  have hopf := opened_fst a.sc sig.returns (a.res.map (·.term)) h.name h.pos
    fun _ => sig.tainted || a.res.any (·.tainted)
  obtain ⟨ho₀, -⟩ := applied_eq (by rw [hopf]; exact hah) happ
  obtain ⟨-, hsc, -⟩ := finish_spec hf
  have hat : a.sc.taintedBy = none := by rw [hsc, ho₀, hopf] at hnt; exact hnt
  obtain ⟨ρ₁, vs, hIa, hvs, hw, hrun⟩ := args_sound ih ihs hh hI₁ rfl har ha hat
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
      (fun _ hwf env hE => ?_) happ hf hnt
    obtain ⟨us, hev, hrel⟩ := hrun env hE
    rw [show ((C.enter (C.erased || g.any (·.allErased))) : Ctx).erased = false from hwf] at hrel
    obtain ⟨rs', hcall, hmr⟩ := hrun' us (hrel.multsRel fun r hr => hall r hr)
    exact ⟨rs', .call hev hd hcall, hmr⟩
  | true =>
    have hcons := hfo.cons (ρ ++ ρ₁) hIa.agree vs (hw.weaken (by simp [hlen.2]) fun i hi => by simp at hi)
    obtain ⟨rs, hrsw⟩ := WantsCons.open hcons
    refine post rfl rfl hg hIa' hvs (by rw [ht]; exact WantsSat.teleOk _ hrsw fun k hk => by simp at hk)
      (fun htf => by rw [ht] at htf; cases htf) happ hf hnt

/-- A call (§8, §9, §12): see `call_sound`. -/
theorem sound {h : Name} {args : List Arg} (ih : ∀ a ∈ args, ExprSound a.expr)
    (ihs : ∀ a ∈ args, ExprShape a.expr) (hh : ∀ a ∈ args, a.expr.holeFree = true) {C : Ctx} {sc : Scope}
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
    refine core ih ihs hh hI hg (hI.globals.fn hgl) (arity_ok har) ha ?_ h₀ hf
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
    refine core ih ihs hh hI hg hfo (arity_ok har) ha ?_ h₀ hf
    intro ρ' vs d hI' hvs hl _ hds hdc hgrp
    have hany : C.fn.any (·.group.contains h.name) = true := by
      simpa [hCfn] using (Option.filter_eq_some_iff.1 hF).2
    simp only [hany, ↓reduceIte] at hgrp
    obtain ⟨ss, hss, hact⟩ := hI'.act fn hCfn
    exact call_lt hI'.sat.rulesHold hm hdec hvs hss hact hds (hfo.subterm.trans hl.symm) hdc hgrp.1 hgrp.2

end Pledge.Call
