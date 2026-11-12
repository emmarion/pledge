import Pledge.Sound.Shape

namespace Pledge

theorem evalList_range' {ρ ws : List Value} :
    Term.evalList (ρ ++ ws) [] ((List.range' ρ.length ws.length).map .entry) = some ws := by
  refine Term.evalList_eq_some_iff.2 ⟨by simp, fun i a ha => ?_⟩
  simp only [List.getElem?_map, Option.map_eq_some_iff] at ha
  obtain ⟨j, hj, rfl⟩ := ha
  have hi : i < ws.length := by have := (List.getElem?_eq_some_iff.1 hj).1; simpa using this
  rw [List.getElem?_range' hi] at hj
  cases hj
  simp [Term.eval, List.getElem?_append_right]

/-- The fields a forcing opens, as results, take the values of the value constructor's arguments. -/
theorem evalList_fieldRes {ρ ws : List Value} {ids : List Nat} (hids : ids = List.range' ρ.length ws.length) :
    Term.evalList (ρ ++ ws) [] ((fieldRes ids).map (·.term)) = some ws := by
  subst hids
  simpa [fieldRes, Function.comp_def] using evalList_range' (ρ := ρ) (ws := ws)

/-- The fields of a pattern for a value constructor whose arguments satisfy its fields are as many as the
arguments. -/
theorem forcings_fields {C : Ctx} {sc : Scope} {t : Term} {sp at_ : Pos} {pats : List Pattern} {erased : Bool}
    {fs : List Forcing} {pat : Pattern} {sig : Sig} {S : Sigs} {ρ ws : List Value}
    (h : forcings C sc t sp pats at_ erased = .ok fs) (hp : pat ∈ pats)
    (hsig : sc.sigs.find ⟨.ctor, pat.ctor.name⟩ = some sig) (hws : TeleSat S ρ sig.params [] ws) :
    pat.fields.length = ws.length := by
  obtain ⟨ctors, hct, hpats, -⟩ := forcings_spec h
  obtain ⟨-, -, -, -, -, -, -, -, -, hsigs⟩ := dataCtors_spec hct
  obtain ⟨sig', hm, hl⟩ := hpats pat hp
  have := hsigs _ _ hm
  rw [hsig] at this
  cases this
  rw [hl, hws.length_eq]

theorem TeleSat.typed {S : Sigs} {ρ : List Value} :
    ∀ {Δ : Telescope} {env vs : List Value}, TeleSat S ρ Δ env vs → ∀ v ∈ vs, ∃ V, HasType S v V
  | [], _, _, h => by rw [TeleSat.nil_iff.1 h]; simp
  | _ :: _, _, _, h => by
    obtain ⟨v, vs, rfl, ⟨A, -, hv, -⟩, ht⟩ := TeleSat.cons_iff.1 h
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ⟨A, hv⟩
    · exact TeleSat.typed ht u hu

/-- The invariant for the scope a forcing gave on an untainted scrutinee, with a pattern's names bound to its
fields. -/
theorem Inv.pattern {C : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {act : Act}
    {Γ' : Entries} {ids : List Nat} {fields : List Id} {ρ' ws : List Value} {Δ : Telescope} {tb : Option Pos}
    {hs : List Hole} (hI : Inv C sc n0 W ρ act) (hsat : Sat W.Sc Γ' (ρ ++ ws))
    (hids : ids = List.range' sc.Γ.length ws.length) (hws : TeleSat W.Sc ρ' Δ [] ws) (htb : tb = none)
    (hhs : hs = []) :
    Inv C (Scope.bind { sc with Γ := Γ', taintedBy := tb, holes := hs } fields (fieldRes ids)) n0 W (ρ ++ ws) act := by
  subst htb hhs
  refine (hI.extend (sc' := { sc with Γ := Γ', taintedBy := none, holes := [] }) hsat rfl rfl rfl rfl).bind
    (evalList_fieldRes (by rw [hids, hI.sat.1.1])) fun i r v hr hv => by
      obtain ⟨V, hV⟩ := hws.typed v (List.mem_of_getElem? hv)
      exact ⟨hV.noRemoved, ⟨V, hV.wtype hI.noJunk⟩, fun _ => ⟨V, hV⟩⟩

/-- Along the bridge, a closed signature has the checker's signature's multiplicities. -/
theorem SigsClose.mults {S Sc : Sigs} {ρ : List Value} (hS : SigsClose S ρ Sc) {h : Head} {sig : Sig}
    (hs : S.find h = some sig) : ∃ sig', Sc.find h = some sig' ∧ sig'.params.map (·.mult) = sig.params.map (·.mult) := by
  obtain ⟨sig', hc, ha⟩ := hS h sig hs
  refine ⟨sig', hc, ?_⟩
  have := ha.params
  clear hc ha hs
  generalize sig.params = Δ at this
  generalize sig'.params = Δ' at this
  induction Δ generalizing Δ' with
  | nil => cases Δ' with
    | nil => rfl
    | cons => exact this.elim
  | cons b Δ ih => cases Δ' with
    | nil => exact this.elim
    | cons b' Δ' => simp [this.1.mult, ih Δ' this.2]

namespace MatchMany

theorem bindPattern_of_name {env : Env} {m : Option Mult} {pat : Pattern} {h : Head} {ws : List Value}
    (hm : m ≠ some .erased) (hn : h.name = pat.ctor.name) :
    bindPattern env m pat (.app h ws) = bindIds env pat.fields ws := by
  simp [bindPattern, destruct, hm, hn, pure, Except.pure, ok_bind]

theorem fieldRes_getElem {ids : List Nat} {i : Nat} {r : Res} (h : (fieldRes ids)[i]? = some r) :
    ∃ id, ids[i]? = some id ∧ r = ⟨.entry id, false, false⟩ := by
  simp only [fieldRes, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨id, hid, rfl⟩ := h
  exact ⟨id, hid, rfl⟩

end MatchMany

/-- Binding a pattern's fields (§10, §16) keeps the run-time environment related: from a scrutinee's run-time value
related by `Rel` to its ideal value `c(ws)`, or from anything under an erased `match` or pattern `let`, the fields
take run-time values related to `ws` by the multiplicities of the fields' entries (erased where the field or the
match is). `sig` is the closed signature of `c`. -/
theorem EnvRel.pattern {S : Sigs} {phase : Nat} {sc : Scope} {ρ ws : List Value} {env : Env} {Γ' : Entries}
    {ids : List Nat} {pat : Pattern} {sig : Sig} {c : String} {m : Option Mult} {a : Value} {tb : Option Pos}
    {hs : List Hole} (hE : EnvRel S phase sc ρ env) (hl : ρ.length = sc.Γ.length)
    (hpre : sc.Γ.eraseRules <+: Γ'.eraseRules) (hids : ids = List.range' sc.Γ.length ws.length)
    (hfl : pat.fields.length = ws.length) (hsig : S.find ⟨.ctor, c⟩ = some sig)
    (hent : ∀ (k : Nat) (b : TBinder), sig.params[k]? = some b → ∃ en, Γ'[sc.Γ.length + k]? = some en ∧
      en.erased = (b.mult == .erased || m == some .erased))
    (ha : m ≠ some .erased → Rel S phase a (.app ⟨.ctor, c⟩ ws)) (hpat : pat.ctor.name = c)
    (hwl : ws.length = sig.params.length) :
    ∃ env', bindPattern env m pat a = .ok env' ∧
      EnvRel S phase (Scope.bind { sc with Γ := Γ', taintedBy := tb, holes := hs } pat.fields (fieldRes ids))
        (ρ ++ ws) env' := by
  have hE' := hE.extend (sc' := { sc with Γ := Γ', taintedBy := tb, holes := hs }) ws rfl hpre hl
  have hlf : pat.fields.length = (fieldRes ids).length := by simp [fieldRes, hids, hfl]
  have key : ∀ (i : Nat) (r : Res), (fieldRes ids)[i]? = some r → ∃ b v, sig.params[i]? = some b ∧
      ws[i]? = some v ∧ r.term.eval (ρ ++ ws) [] = some v ∧ r.tainted = false ∧
      ({ sc with Γ := Γ', taintedBy := tb, holes := hs } : Scope).multOf r =
        (if (b.mult == .erased || m == some .erased) = true then .erased else .many) := by
    intro i r hr
    obtain ⟨id, hid, rfl⟩ := MatchMany.fieldRes_getElem hr
    have hi : i < ws.length := by
      rw [hids] at hid; have := (List.getElem?_eq_some_iff.1 hid).1; simpa using this
    rw [hids, List.getElem?_range' hi] at hid
    cases hid
    obtain ⟨b, hb⟩ : ∃ b, sig.params[i]? = some b := ⟨_, List.getElem?_eq_getElem (hwl ▸ hi)⟩
    obtain ⟨en, hen, her⟩ := hent i b hb
    refine ⟨b, ws[i], hb, List.getElem?_eq_getElem hi, ?_, rfl, ?_⟩
    · simp [Term.eval, List.getElem?_append_right, hl]
    · simp only [Scope.multOf, Scope.erasedEntry, Nat.one_mul, hen, Option.any_some, her, Bool.false_or]
  by_cases hm : m = some .erased
  · subst hm
    refine ⟨_, bindPattern_erased env pat a, hE'.bind hlf (by simp [hlf]) fun i r u hr hu _ => ?_⟩
    obtain ⟨b, v, -, -, hv, -, hmult⟩ := key i r hr
    rw [List.getElem?_map, Option.map_eq_some_iff] at hu
    obtain ⟨-, -, rfl⟩ := hu
    refine ⟨v, hv, ?_⟩
    rw [hmult]
    simp only [beq_self_eq_true, Bool.or_true, ↓reduceIte]
    exact MultRel.removed
  · obtain ⟨as, rfl, hlen, hrel⟩ : ∃ as, a = .app ⟨.ctor, c⟩ as ∧ as.length = ws.length ∧
        ∀ (k : Nat) (u v : Value), as[k]? = some u → ws[k]? = some v →
          MultRel S phase (if S.erasedArg phase ⟨.ctor, c⟩ k then .erased else .many) u v := by
      cases ha hm with
      | type h => cases h
      | app hl' _ _ => exact ⟨_, rfl, hl', (Rel.app_iff.1 (ha hm)).2.2⟩
    refine ⟨_, by rw [MatchMany.bindPattern_of_name hm hpat.symm]; exact bindIds_of_length (hfl.trans hlen.symm),
      hE'.bind hlf (by rw [← hlf, hfl, hlen]) fun i r u hr hu _ => ?_⟩
    obtain ⟨b, v, hb, hwv, hv, -, hmult⟩ := key i r hr
    refine ⟨v, hv, ?_⟩
    have := hrel i u v hu hwv
    have hea : S.erasedArg phase ⟨.ctor, c⟩ i = (b.mult == .erased) := by simp [Sigs.erasedArg, hsig, hb]
    have hme : (m == some .erased) = false := by simpa using hm
    rw [hmult, hme, Bool.or_false]
    rwa [hea] at this

namespace MatchMany

theorem checkBranches_spec {C : Ctx} {inner : Scope} {r : Res} {sp : Pos} {fs : List Forcing} {g : Given} :
    ∀ {bs : List Branch} {bo : BranchesOut}, checkBranches C inner r sp fs g bs = .ok bo →
      bo.outs.length = bs.length ∧ bo.trees = (bs.zip bo.outs).map (fun p => .mk p.1.pat p.2.tree) ∧
      ∀ b o, (b, o) ∈ bs.zip bo.outs → ∃ Γ ids,
        survivor inner fs b.pat.ctor.name b.pat.ctor.pos "" = .ok (Γ, ids) ∧
        closed (Scope.bind { inner with Γ, taintedBy := reach inner r sp, holes := [] } b.pat.fields
          (fieldRes ids)) (checkExpr C · (some g) b.body) = .ok o
  | [], bo, h => by
    simp only [checkBranches, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | .mk pat body :: bs, bo, h => by
    simp only [checkBranches] at h
    obtain ⟨⟨Γ, ids⟩, hs, h⟩ := bind_eq_ok.1 h
    obtain ⟨o, ho, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    obtain ⟨h1, h2, h3⟩ := checkBranches_spec hrest
    refine ⟨by simp [h1], by simp [h2]; rfl, fun b o' hm => ?_⟩
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hm
    · exact ⟨Γ, ids, hs, ho⟩
    · exact h3 b o' hm

/-- What checking a `match` that is not erased consists of (§10, §12). -/
theorem checkExpr_match {C : Ctx} {sc : Scope} {g : Option Given} {p : Pos} {m : Option Mult} {s : Expr}
    {ann : Tele} {bs : List Branch} {o : Out} (hm : m ≠ some .erased)
    (h : checkExpr C sc g (.match p m s ann bs) = .ok o) :
    ∃ C₂ so r tele env fs gb bo o', C₂.phase = C.phase ∧ C₂.globals = C.globals ∧ C₂.fn = C.fn ∧
      C₂.erased = (C.erased || g.any (·.allErased)) ∧ closed sc (checkExpr C₂ · none s) = .ok so ∧
      single s.pos so.res = .ok r ∧
      annotation (C.enter (C.erased || g.any (·.allErased))) so.sc
        (if C.erased then g.map (·.erase) else g) ann = .ok (tele, env) ∧
      forcings (C.enter (C.erased || g.any (·.allErased))) so.sc r.term s.pos
        (bs.map Branch.pat) p false =
        .ok fs ∧
      ((fs.filter fun f => f.pat.isNone && f.forced matches .ok ..).map (·.name)).isEmpty = true ∧
      (tele.all (·.entriesBelow so.sc.Γ.length) && env.all (·.entriesBelow so.sc.Γ.length)) = true ∧
      gb.wants = tele.mapIdx (fun i b => { Want.of b with
        mult := if (if C.erased then g.map (·.erase) else g).any (·.erasedAt i) then .erased else b.mult }) ∧
      gb.env = env ∧ gb.whole = true ∧
      checkBranches (C.enter (C.erased || g.any (·.allErased))) so.sc r s.pos fs gb bs = .ok bo ∧
      produced (opened so.sc tele env "match" p fun i =>
          r.tainted || bo.outs.any fun o => ((o.res[i]?).map (·.tainted)).getD false).1
        (if C.erased then g.map (·.erase) else g) p
        (opened so.sc tele env "match" p fun i =>
          r.tainted || bo.outs.any fun o => ((o.res[i]?).map (·.tainted)).getD false).2
        (.match p m so.tree ann bo.trees) = .ok o' ∧
      finish (C.enter (C.erased || g.any (·.allErased))) (C.erased || g.any (·.allErased))
        (if C.erased then g.map (·.erase) else g) (.match p m s ann bs) { o' with snaps := so.snaps ++ bo.snaps } =
        .ok o := by
  unfold checkExpr at h
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 h
  clear h
  simp only at h₀
  obtain ⟨so, hso, h₀⟩ := bind_eq_ok.1 h₀
  rw [keep_ok] at h₀
  obtain ⟨r, hr, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨⟨tele, env⟩, hann, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨fs, hfs, h₀⟩ := bind_eq_ok.1 h₀
  obtain ⟨u1, -, h₀⟩ := bind_eq_ok.1 h₀
  have hme : (m == some .erased) = false := by simpa using hm
  simp only [hme, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.or_false] at h₀ hso hfs
  split at h₀
  case isFalse => simp [failAt_eq, bind, Except.bind] at h₀
  rename_i hmiss
  split at h₀
  all_goals
    obtain ⟨u4, hens, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨bo, hbo, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨o'', ho'', h₀⟩ := bind_eq_ok.1 h₀
    simp only [pure, Except.pure, Except.ok.injEq] at h₀
    subst h₀
    rw [keep_ok] at ho''
    have htrees : List.filterMap (fun x => some x.snd) (bs.zip bo.trees) = bo.trees := by
      obtain ⟨hol, htr, -⟩ := checkBranches_spec hbo
      rw [show (fun x : Branch × Branch => some x.snd) = some ∘ Prod.snd from rfl, List.filterMap_eq_map]
      exact List.map_snd_zip (by rw [htr]; simp [hol])
    rw [htrees] at ho''
    exact ⟨{ C.enter (C.erased || g.any (·.allErased)) with
        place := "the scrutinee of a `many` match" }, so, r,
      tele, env, fs, _, bo, o'', rfl, rfl, rfl, rfl, hso, hr, hann, hfs, hmiss, ensure_ok hens,
      rfl, rfl, rfl, hbo, ho'', hf⟩

theorem produced_length {sc : Scope} {g : Given} {pos : Pos} {rs : List Res} {tree : Expr} {o : Out}
    (h : produced sc (some g) pos rs tree = .ok o) : o.res = rs ∧ rs.length = g.wants.length := by
  simp only [produced] at h
  obtain ⟨sc', hsc, h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only [against] at hsc
  by_cases hl : rs.length = g.wants.length
  · exact ⟨rfl, hl⟩
  · simp [hl, miscount, failAt_eq, bind, Except.bind] at hsc

theorem applied_length {sc : Scope} {g : Given} {pos : Pos} {rs : List Res} {tree : Expr} {since : Option Nat}
    {snaps : List Snapshot} {o : Out} (h : applied sc (some g) pos rs tree since snaps = .ok o) :
    o.res.length = g.wants.length := by
  cases since <;> simp only [applied, keep_ok] at h <;> obtain ⟨o', ho', h₁⟩ := bind_eq_ok.1 h <;>
    obtain ⟨rfl, hl⟩ := produced_length ho'
  · simp only [pure, Except.pure, ok_bind, Except.ok.injEq] at h₁; subst h₁; simp [hl]
  · obtain ⟨o'', ho'', h₂⟩ := bind_eq_ok.1 h₁
    simp only [pure, Except.pure, Except.ok.injEq] at h₂
    subst h₂
    simp [close_ok ho'', hl]

theorem checkElems_length {C : Ctx} {g : Option Given} : ∀ {es : List Expr} {sc : Scope} {prev : List Res}
    {eo : ElemsOut}, checkElems C sc g prev es = .ok eo → eo.res.length = es.length
  | [], sc, prev, eo, h => by
    simp only [checkElems, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | e :: es, sc, prev, eo, h => by
    simp only [checkElems] at h
    obtain ⟨o, -, h⟩ := bind_eq_ok.1 h
    obtain ⟨r, -, h⟩ := bind_eq_ok.1 h
    obtain ⟨rest, hrest, h⟩ := bind_eq_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [keep_ok] at hrest
    simp [checkElems_length hrest]

/-- An expression checked against what its position is given produces one result per entry (§8). -/
theorem checkExpr_length : ∀ (e : Expr) {C : Ctx} {sc : Scope} {g : Given} {o : Out},
    checkExpr C sc (some g) e = .ok o → o.res.length = g.wants.length := by
  intro e C sc g o h
  unfold checkExpr at h
  obtain ⟨o₀, h₀, hf⟩ := bind_eq_ok.1 h
  clear h
  obtain ⟨-, -, -, hres, -⟩ := finish_spec hf
  have hl : o.res.length = o₀.res.length := by rw [hres]; split <;> simp
  rw [hl]
  obtain ⟨g', hg', hgl⟩ : ∃ g', (if C.erased then (some g).map (·.erase) else some g) = some g' ∧
      g'.wants.length = g.wants.length := by
    cases C.erased <;> simp [Given.erase]
  simp only [hg'] at h₀
  rw [← hgl]
  clear hf hres hl hg' hgl
  cases e with
  | tuple p es =>
    simp only at h₀
    split at h₀
    · simp [failAt_eq, miscount, bind, Except.bind] at h₀
    · obtain ⟨eo, heo, h₀⟩ := bind_eq_ok.1 h₀
      simp only [pure, Except.pure, Except.ok.injEq] at h₀
      subst h₀
      rename_i hne
      simp only [ne_eq, Decidable.not_not] at hne
      rw [checkElems_length heo, hne]
  | block ss f =>
    simp only at h₀
    obtain ⟨s, -, h₀⟩ := bind_eq_ok.1 h₀
    obtain ⟨of, hof, h₀⟩ := bind_eq_ok.1 h₀
    simp only [pure, Except.pure, Except.ok.injEq] at h₀
    subst h₀
    rw [keep_ok] at hof
    exact checkExpr_length f (o := of) hof
  | _ =>
    simp only at h₀
    repeat' (first
      | exact applied_length h₀
      | exact (produced_length h₀).1 ▸ (produced_length h₀).2
      | (simp [failAt_eq, notApplied, notValue, internal, bind, Except.bind] at h₀; done)
      | (obtain ⟨_, hx, h₀⟩ := bind_eq_ok.1 h₀; obtain ⟨hres, hl⟩ := produced_length (keep_ok.1 hx)
         simp only [pure, Except.pure, Except.ok.injEq] at h₀; subst h₀; simp [hres, hl])
      | (obtain ⟨_, _, h₀⟩ := bind_eq_ok.1 h₀)
      | (rw [keep_ok] at h₀)
      | (split at h₀)
      | (simp only at h₀))

/-- Values meeting wants with a telescope's types and `is` clauses meet the telescope (`TeleOk`). -/
theorem teleOk_of_wantsSat {S : Sigs} {ρ : List Value} : ∀ {tele : Telescope} {ws : List Want} {env : List Value}
    {ts : List Bool} {vs : List Value} {typed : Nat → Bool}, WantsSat S ρ ws env ts vs →
    ws.length = tele.length → (∀ (i : Nat) (w : Want) (b : TBinder), ws[i]? = some w → tele[i]? = some b →
      w.type = some b.type ∧ w.is = b.is) →
    (∀ k, k < tele.length → typed k = true → ts[k]? = some true) → TeleOk S ρ typed tele env vs
  | [], [], _, [], [], _, _, _, _, _ => trivial
  | b :: tele, w :: ws, env, t :: ts, v :: vs, typed, ⟨⟨h1, h2⟩, h3⟩, hl, hwb, hty => by
    obtain ⟨ht, hi⟩ := hwb 0 w b rfl rfl
    obtain ⟨A, hA, a, c, d⟩ := h1 b.type ht
    exact ⟨⟨A, hA, a, c, fun h => d (by simpa using hty 0 (by simp) h)⟩, fun e he => h2 e (hi ▸ he),
      teleOk_of_wantsSat h3 (by simpa using hl) (fun i w' b' h1 h2 => hwb (i + 1) w' b' h1 h2)
        fun k hk h => by simpa using hty (k + 1) (by simp; omega) h⟩
  | [], _ :: _, _, _, _, _, _, hl, _, _ | _ :: _, [], _, _, _, _, _, hl, _, _ => by simp at hl
  | [], [], _, _ :: _, _, _, h, _, _, _ | [], [], _, [], _ :: _, _, h, _, _, _ => h.elim
  | _ :: _, _ :: _, _, [], _, _, h, _, _, _ | _ :: _, _ :: _, _, _ :: _, [], _, h, _, _, _ => h.elim

theorem TeleOk.restrict {S : Sigs} {n : Nat} {ρ ρ' : List Value} (hρ : ρ.take n = ρ'.take n) :
    ∀ {typed : Nat → Bool} {Δ : Telescope} {env vs : List Value}, Δ.all (·.entriesBelow n) = true →
      TeleOk S ρ typed Δ env vs → TeleOk S ρ' typed Δ env vs
  | _, [], _, [], _, _ => trivial
  | _, b :: _, env, _ :: _, h, ⟨⟨A, hA, h1, h2, h3⟩, his, ht⟩ => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hb := TBinder.agree_of_entriesBelow hρ h.1
    refine ⟨⟨A, by rw [← hb.type env]; exact hA, h1, h2, h3⟩, fun e he => ?_, TeleOk.restrict hρ h.2 ht⟩
    have := hb.is env
    rw [he] at this
    simp only [Option.map_some] at this
    exact (Option.some.inj this) ▸ his e he
  | _, [], _, _ :: _, _, h | _, _ :: _, _, [], _, h => h.elim

theorem TeleOk.getElem {S : Sigs} {ρ : List Value} : ∀ {typed : Nat → Bool} {Δ : Telescope} {env vs : List Value},
    TeleOk S ρ typed Δ env vs → ∀ (i : Nat) (v : Value), vs[i]? = some v →
      v.noRemoved = true ∧ (∃ A, WType S v A) ∧ (typed i = true → ∃ V, HasType S v V)
  | _, [], _, [], _, _, _, hv => by simp at hv
  | _, _ :: _, _, _ :: _, ⟨⟨A, _, h1, h2, h3⟩, _, ht⟩, i, v, hv => by
    cases i with
    | zero => cases hv; exact ⟨h1, ⟨A, h2⟩, fun h => ⟨A, h3 h⟩⟩
    | succ i => exact TeleOk.getElem ht i v (by simpa using hv)
  | _, [], _, _ :: _, h, _, _, _ | _, _ :: _, _, [], h, _, _, _ => h.elim

/-- `WantsSat` reads only the wants' types and `is` clauses. -/
theorem wantsSat_congr {S : Sigs} {ρ : List Value} : ∀ {ws ws' : List Want} {env : List Value} {ts : List Bool}
    {vs : List Value}, ws.length = ws'.length →
    (∀ (i : Nat) (w w' : Want), ws[i]? = some w → ws'[i]? = some w' → w.type = w'.type ∧ w.is = w'.is) →
    WantsSat S ρ ws env ts vs → WantsSat S ρ ws' env ts vs
  | [], [], _, [], [], _, _, _ => trivial
  | w :: ws, w' :: ws', env, t :: ts, v :: vs, hl, hw, ⟨⟨h1, h2⟩, h3⟩ => by
    obtain ⟨ht, hi⟩ := hw 0 w w' rfl rfl
    exact ⟨⟨fun T hT => h1 T (ht ▸ hT), fun e he => h2 e (hi ▸ he)⟩, wantsSat_congr (by simpa using hl)
      (fun i a b ha hb => hw (i + 1) a b (by simpa using ha) (by simpa using hb)) h3⟩
  | [], _ :: _, _, _, _, hl, _, _ | _ :: _, [], _, _, _, hl, _, _ => by simp at hl
  | [], [], _, _ :: _, _, _, _, h | [], [], _, [], _ :: _, _, _, h => h.elim
  | _ :: _, _ :: _, _, [], _, _, _, h | _ :: _, _ :: _, _, _ :: _, [], _, _, h => h.elim

theorem erase_wants {g : Given} (i : Nat) (w w' : Want) (h : g.erase.wants[i]? = some w)
    (h' : g.wants[i]? = some w') : w.type = w'.type ∧ w.is = w'.is := by
  simp only [Given.erase, List.getElem?_map, h', Option.map_some, Option.some.injEq] at h
  subst h; exact ⟨rfl, rfl⟩

/-- What a position is given, erased in an erased position (§16), is still `Given.Ok`, with the original's types. -/
theorem given_erased {S : Sigs} {ρ : List Value} {C : Ctx} {g : Option Given}
    (hg : ∀ g', g = some g' → g'.Ok S ρ) :
    ∀ g', (if C.erased then g.map (·.erase) else g) = some g' → g'.Ok S ρ ∧
      ∃ g₀, g = some g₀ ∧ g'.wants.length = g₀.wants.length ∧ g'.env = g₀.env ∧
        ∀ (i : Nat) (w w' : Want), g'.wants[i]? = some w → g₀.wants[i]? = some w' →
          w.type = w'.type ∧ w.is = w'.is := by
  intro g' h
  cases hC : C.erased <;> simp only [hC, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
  · subst h
    exact ⟨hg g' rfl, g', rfl, rfl, rfl, fun i w w' h1 h2 => by rw [h1] at h2; cases h2; exact ⟨rfl, rfl⟩⟩
  · obtain ⟨g₀, rfl, rfl⟩ := h
    have h0 := hg g₀ rfl
    refine ⟨⟨h0.env, fun hw envv he => WantsCons.congr (by simp [Given.erase]) (fun i w w' h1 h2 => ?_)
      (h0.cons hw envv he)⟩, g₀, rfl, by simp [Given.erase], rfl, erase_wants⟩
    exact (erase_wants i w' w h2 h1).imp Eq.symm Eq.symm

/-- The scrutinee of a `match` or pattern `let` that is not erased, in a scope that stays untainted: its one result
has an ideal value, and, outside an erased position, it runs to one value related to it when it is untainted. -/
theorem scrut {s : Expr} (ihs : ExprSound s) (ihss : ExprShape s) {C C₂ : Ctx} {sc : Scope} {n0 : Nat} {W : World}
    {ρ : List Value} {act : Act} {so : Out} {pos : Pos} {r : Res} (hI : Inv C sc n0 W ρ act)
    (hph : C₂.phase = C.phase) (hgl : C₂.globals = C.globals) (hfn : C₂.fn = C.fn)
    (h : checkExpr C₂ sc none s = .ok so) (hr : single pos so.res = .ok r) (hu : so.sc.taintedBy = none) :
    ∃ ρ₁ v, Inv C so.sc n0 W (ρ ++ ρ₁) act ∧ r.term.eval (ρ ++ ρ₁) [] = some v ∧ ResOk W.Sc r v ∧
      ∀ env, EnvRel W.Sc C.phase sc ρ env → EnvRel W.Sc C.phase so.sc (ρ ++ ρ₁) env ∧
        (C₂.erased = false → ∃ us a, Eval W.P env so.tree us ∧ one us = .ok a ∧
          (r.tainted = false → Rel W.Sc C.phase a v)) := by
  obtain ⟨-, hnames, -, hpre, -⟩ := ihss C₂ sc none so hI.holes h
  obtain ⟨hpost, -⟩ := ihs C₂ sc none n0 W ρ act so (hI.congr_ctx hph hgl hfn) (by simp) h
  obtain ⟨ρ₁, vs, hI₁, hvs, hok, -, hrun⟩ := hpost hu
  rw [single_ok hr] at hvs hok hrun
  obtain ⟨v, hv, rfl⟩ := Term.evalList_singleton.1 (by simpa using hvs)
  refine ⟨ρ₁, v, hI₁.congr_ctx hph.symm hgl.symm hfn.symm, hv, hok 0 r v rfl rfl, fun env hE =>
    ⟨hE.extend ρ₁ hnames hpre hI.sat.1.1, fun her => ?_⟩⟩
  obtain ⟨us, hev, us', htake, hrel⟩ := hrun env (hph ▸ hE)
  obtain ⟨a, hone, rfl⟩ := one_of_take htake
  refine ⟨us, a, hev, hone, fun ht => ?_⟩
  have := hrel 0 r a v rfl rfl rfl ht
  simp only [Ctx.posMult, her, Option.any_none, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hph] at this
  exact this

theorem params_mult {sig sig' : Sig} (h : sig'.params.map (·.mult) = sig.params.map (·.mult)) {k : Nat}
    {b' : TBinder} (hb : sig'.params[k]? = some b') : ∃ b, sig.params[k]? = some b ∧ b.mult = b'.mult := by
  have := congrArg (·[k]?) h
  simp only [List.getElem?_map, hb, Option.map_some] at this
  cases hk : sig.params[k]? with
  | none => rw [hk] at this; cases this
  | some b => rw [hk] at this; exact ⟨b, rfl, (Option.some.inj this).symm⟩

/-- The scope of a branch, or after a pattern `let`, for the value constructor heading the untainted scrutinee's
ideal value: the invariant holds with the fields valued by its arguments, and, from a run-time value related to the
scrutinee's ideal one, binding the pattern keeps the run-time environment related. -/
theorem branch {C : Ctx} {sc : Scope} {n0 : Nat} {W : World} {ρ : List Value} {act : Act} {pat : Pattern}
    {sig : Sig} {ws : List Value} {Γ : Entries} {ids : List Nat} (hI : Inv C sc n0 W ρ act)
    (hsig : sc.sigs.find ⟨.ctor, pat.ctor.name⟩ = some sig) (hws : TeleSat W.Sc ρ sig.params [] ws)
    (hsat : Sat W.Sc Γ (ρ ++ ws)) (hpre : sc.Γ.eraseRules <+: Γ.eraseRules)
    (hids : ids = List.range' sc.Γ.length ws.length) (hfl : pat.fields.length = ws.length)
    (hent : ∀ (k : Nat) (b : TBinder), sig.params[k]? = some b → ∃ en, Γ[sc.Γ.length + k]? = some en ∧
      en.tainted = false ∧ en.erased = (b.mult == .erased || false)) :
    Inv C (Scope.bind { sc with Γ, taintedBy := none, holes := [] } pat.fields (fieldRes ids)) n0 W (ρ ++ ws) act ∧
      ∀ env m a, m ≠ some .erased → EnvRel W.Sc C.phase sc ρ env →
        Rel W.Sc C.phase a (.app ⟨.ctor, pat.ctor.name⟩ ws) →
        ∃ env', bindPattern env m pat a = .ok env' ∧
          EnvRel W.Sc C.phase (Scope.bind { sc with Γ, taintedBy := none, holes := [] } pat.fields (fieldRes ids))
            (ρ ++ ws) env' := by
  refine ⟨hI.pattern hsat hids hws rfl rfl, fun env m a hm hE ha => ?_⟩
  obtain ⟨sig', hsig', hmult⟩ := SigsClose.mults (hI.sigs ρ hI.agree) hsig
  have hme : (m == some .erased) = false := by simpa using hm
  refine EnvRel.pattern hE hI.sat.1.1 hpre hids hfl hsig' (fun k b' hb' => ?_) (fun _ => ha) rfl ?_
  · obtain ⟨b, hb, hbm⟩ := params_mult hmult hb'
    obtain ⟨en, hen, -, her⟩ := hent k b hb
    exact ⟨en, hen, by rw [her, hme, hbm]⟩
  · rw [hws.length_eq]
    simpa using (congrArg List.length hmult).symm

theorem mem_zip_left {α β : Type} {l : List α} {l' : List β} (hl : l.length ≤ l'.length) {x : α} (hx : x ∈ l) :
    ∃ y, (x, y) ∈ l.zip l' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact ⟨l'[i]'(by omega), by rw [← List.getElem_zip (h := by simp; omega)]; exact List.getElem_mem _⟩

theorem pickBranch_many {m : Option Mult} (hm : m ≠ some .erased) {h : Head} {ws : List Value} {bs : List Branch}
    {b : Branch} (hf : bs.find? (·.pat.ctor.name == h.name) = some b) : pickBranch m (.app h ws) bs = .ok b := by
  simp [pickBranch, hm, hf, pure, Except.pure]

theorem mapIdx_want {tele : Telescope} {M : Nat → TBinder → Mult} (i : Nat) (w : Want) (b : TBinder)
    (hw : (tele.mapIdx fun i b => { Want.of b with mult := M i b })[i]? = some w) (hb : tele[i]? = some b) :
    w.type = some b.type ∧ w.is = b.is := by
  rw [List.getElem?_mapIdx, hb] at hw
  cases hw
  exact ⟨rfl, rfl⟩

theorem map_want {tele : Telescope} (i : Nat) (w : Want) (b : TBinder) (hw : (tele.map Want.of)[i]? = some w)
    (hb : tele[i]? = some b) : w.type = some b.type ∧ w.is = b.is := by
  rw [List.getElem?_map, hb] at hw
  cases hw
  exact ⟨rfl, rfl⟩

theorem givenOk_frame {S : Sigs} {ρ : List Value} {g : Given} (h : g.Ok S ρ) (ρ' : List Value) :
    g.Ok S (ρ ++ ρ') := by
  obtain ⟨envv, he⟩ := h.env
  refine ⟨⟨envv, Term.evalList_frame_ρ ρ' he⟩, fun hw envv' he' => ?_⟩
  rw [Term.evalList_frame_ρ ρ' he] at he'
  cases he'
  exact WantsCons.frame ρ' (h.cons hw envv he)

theorem of_erased {C : Ctx} {g : Option Given} {P : Given → Prop} (hP : ∀ g', P g'.erase → P g')
    (h : ∀ g₁, (if C.erased then g.map (·.erase) else g) = some g₁ → P g₁) :
    ∀ g', g = some g' → P g' := by
  intro g' hg'
  subst hg'
  cases hC : C.erased
  · exact h g' (by simp [hC])
  · exact hP g' (h _ (by simp [hC]))

/-- A tree removed in a wholly erased position, or with only tainted results, relates its results (§12, §16). -/
theorem resRel_whole {S : Sigs} {phase : Nat} {C : Ctx} {g : Option Given} {rs : List Res} {ideal : List Value}
    (hw : (C.erased || g.any (·.allErased) || rs.all (·.tainted)) = true)
    (hl : ∀ g', g = some g' → rs.length = g'.wants.length) :
    ResRel S phase (C.posMult g) rs ideal [.removed] := by
  refine ResRel.removed fun i r hr ht => ?_
  simp only [Bool.or_eq_true, List.all_eq_true] at hw
  rcases hw with (hC | hg) | ha
  · simp [Ctx.posMult, hC]
  · cases g with
    | none => simp at hg
    | some g' =>
      simp only [Option.any_some, Given.allErased, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hg
      have hi : i < g'.wants.length := by rw [← hl g' rfl]; exact (List.getElem?_eq_some_iff.1 hr).1
      simp [Ctx.posMult, Given.erasedAt, List.getElem?_eq_getElem hi, hg.2 _ (List.getElem_mem hi)]
  · rw [ha r (List.mem_of_getElem? hr)] at ht; cases ht

/-- `matchMany_sound`: a match's results take the ideal values of the branch for the value constructor heading
the scrutinee's ideal value, or, when every result is tainted, values meeting the annotation by their heads. -/
theorem sound {p : Pos} {m : Option Mult} {s : Expr} {ann : Tele} {bs : List Branch}
    (hm : m ≠ some .erased) (hta : ∀ bs', ann = .binders bs' → ∀ b ∈ bs', b.ann.term.holed = false)
    (ihs : ExprSound s) (ihss : ExprShape s) (ihb : ∀ b ∈ bs, ExprSound b.body)
    (ihbs : ∀ b ∈ bs, ExprShape b.body) : ExprSound (.match p m s ann bs) := by
  intro C sc g n0 W ρ act o hI hg hc
  obtain ⟨C₂, so, r, tele, env, fs, gb, bo, o', hph, hgl, hfn, her, hso, hr, hann, hfs, hmiss, hens, hgbw, hgbe,
    -, hbo, ho', hf⟩ := checkExpr_match hm hc
  rw [closed_eq hI.holes fun o h => (ihss C₂ sc none o hI.holes h).2.2.1] at hso
  obtain ⟨-, hosc, -, hores, hotree, herr⟩ := finish_spec hf
  obtain ⟨-, -, hholes₁, -, -⟩ := ihss C₂ sc none so hI.holes hso
  obtain rfl := produced_eq (by exact hholes₁) ho'
  simp only at hosc hores hotree herr
  generalize htaint : (fun (i : Nat) =>
    r.tainted || bo.outs.any fun (o : Out) => ((o.res[i]?).map (·.tainted)).getD false) = taint
    at hosc hores hotree herr ho'
  generalize hrsdef : (opened so.sc tele env "match" p taint).2 = rs at hores hotree herr ho'
  obtain ⟨-, -, hrsl, hrs⟩ := opened_shape so.sc tele env "match" p taint
  rw [hrsdef] at hrsl hrs
  by_cases hu : so.sc.taintedBy = none
  case neg =>
    exact ⟨fun h => absurd (by rw [hosc] at h; exact h) hu, fun h => absurd (by rw [hosc] at h; exact h) hu⟩
  have hu' : (opened so.sc tele env "match" p taint).1.taintedBy = none := hu
  have hores' : o.res = rs := by rw [hores, hu']; rfl
  obtain ⟨ρ₁, v, hI₁, hv, hokv, hrun₁⟩ := scrut ihs ihss hI hph hgl hfn hso hr hu
  have hg₁ := given_erased (C := C) hg
  obtain ⟨envv, henv, hcons⟩ :=
    annotation_cons hI₁.termInv.weak (fun g' h => givenOk_frame (hg₁ g' h).1 ρ₁) hta hann
  have hens' : tele.all (·.entriesBelow so.sc.Γ.length) = true := by
    simp only [Bool.and_eq_true] at hens; exact hens.1
  have hlenρ : (ρ ++ ρ₁).length = so.sc.Γ.length := hI₁.sat.1.1
  have hrs' : ∀ i r', rs[i]? = some r' → r'.tainted = taint i ∧ (r'.erased = true → ∃ b, tele[i]? = some b ∧
      b.mult = .erased) := fun i r' h' => by
    obtain ⟨b, hb⟩ : ∃ b, tele[i]? = some b := ⟨_, List.getElem?_eq_getElem (by
      have := (List.getElem?_eq_some_iff.1 h').1; rw [hrsl] at this; exact this)⟩
    rw [(hrs i b hb).1] at h'
    cases h'
    exact ⟨rfl, fun he => ⟨b, hb, by simpa using he⟩⟩
  have fin : ∀ vs, TeleOk W.Sc (ρ ++ ρ₁) (fun k => !taint k) tele envv vs →
      ((C.erased || g.any (·.allErased) || rs.all (·.tainted)) = false → ∀ env, EnvRel W.Sc C.phase sc ρ env →
        ∃ us, Eval W.P env (.match p m so.tree ann bo.trees) us ∧ ResRel W.Sc C.phase (C.posMult g) rs vs us) →
      ExprPost C sc g n0 W ρ act o := by
    unfold ExprPost
    intro vs htele hrunv _
    obtain ⟨hsat', hvs'⟩ := opened_sound (kind := "match") (pos := p) hI₁.sat henv htele
    rw [hrsdef] at hvs'
    have hok : ∀ (i : Nat) (r' : Res) (v' : Value), rs[i]? = some r' → vs[i]? = some v' → ResOk W.Sc r' v' :=
      fun i r' v' hr' hv' => by
        obtain ⟨h1, h2, h3⟩ := TeleOk.getElem htele i v' hv'
        exact ⟨h1, h2, fun ht => h3 (by rw [← (hrs' i r' hr').1, ht]; rfl)⟩
    have hlv : rs.length = vs.length := by rw [hrsl, htele.length_eq]
    obtain ⟨-, hwo⟩ := produced_sound hsat'.1 (hI₁.sigsClose vs) hI₁.noJunk hholes₁ hvs'
      (ResOks.of_getElem hlv hok) (fun g' h =>
        let ⟨envv', he⟩ := (givenOk_frame (hg₁ g' h).1 (ρ₁ ++ vs)).env; ⟨envv', by simpa using he⟩) ho'
    have hwo' := of_erased (fun g' h envv he => (h envv he).imp (by simpa [Given.erase] using ·)
      (wantsSat_congr (by simp [Given.erase]) erase_wants)) hwo
    have hlen : ∀ g', g = some g' → rs.length = g'.wants.length := fun g' h => by
      obtain ⟨envv', he⟩ := (hg g' h).env
      exact (hwo' g' h envv' (by simpa using Term.evalList_frame_ρ (ρ₁ ++ vs) he)).1
    refine ⟨ρ₁ ++ vs, vs, ?_, ?_, ?_, fun g' h envv' he => ?_, fun env hE => ?_⟩
    · rw [hosc, ← List.append_assoc]; exact hI₁.extend hsat' rfl rfl hholes₁ hu
    · rw [hores', ← List.append_assoc]; exact hvs'
    · rw [hores']; exact hok
    · rw [hores', ← List.append_assoc]
      exact (hwo' g' h envv' (by simpa using Term.evalList_frame_ρ (ρ₁ ++ vs) he)).2
    · rw [hotree, hores']
      split
      · exact ⟨_, .removed, resRel_whole (by assumption) hlen⟩
      · rename_i hnr
        exact hrunv (by rwa [Bool.not_eq_true] at hnr) env hE
  have hall : (∀ k < tele.length, taint k = true) → ∀ r' ∈ rs, r'.tainted = true := fun hJ r' hr' => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr'
    rw [(hrs' i _ (List.getElem?_eq_getElem hi)).1]
    exact hJ i (by rw [← hrsl]; exact hi)
  by_cases hJ : ∀ k < tele.length, taint k = true
  · obtain ⟨vs, hvs⟩ := WantsCons.open hcons
    refine ⟨fin vs (teleOk_of_wantsSat hvs (by simp) map_want fun k hk h => ?_) fun hnr => ?_,
      fun _ _ r' hr' => hall hJ r' (hores' ▸ hr')⟩
    · simp [hJ k hk] at h
    · simp [List.all_eq_true.2 (hall hJ)] at hnr
  obtain ⟨k, hk, hkt⟩ : ∃ k, k < tele.length ∧ taint k = false := Classical.byContradiction fun hn =>
    hJ fun k hk => by
      cases h : taint k
      · exact absurd ⟨k, hk, h⟩ hn
      · rfl
  have hrt : r.tainted = false := by
    rw [← htaint] at hkt; simp only [Bool.or_eq_false_iff] at hkt; exact hkt.1
  obtain ⟨V, hV⟩ := hokv.2.2 hrt
  have hI₁' : Inv (C.enter (C.erased || g.any (·.allErased))) so.sc n0 W (ρ ++ ρ₁) act :=
    hI₁.congr_ctx rfl rfl rfl
  obtain ⟨c, ws, sig, Γ', ids, pat, rfl, hfc, hsig, hws, hsat, hpre, -, hids, hpat, hent⟩ :=
    forcings_value hI₁' hfs hv hV
  obtain ⟨b₀, hb₀, hb₀n⟩ : ∃ b ∈ bs, b.pat.ctor.name = c := by
    have := List.filter_eq_nil_iff.1 (List.map_eq_nil_iff.1 (List.isEmpty_iff.1 hmiss)) _
      (List.mem_of_find?_eq_some hfc)
    cases hp' : pat with
    | none => simp [hp'] at this
    | some p0 =>
      rw [hp'] at hpat
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hpat.symm)
      exact ⟨b, hb, by simpa using List.find?_some hpat.symm⟩
  obtain ⟨hol, htr, hbr⟩ := checkBranches_spec hbo
  obtain ⟨⟨b, ob⟩, hfind⟩ : ∃ q, (bs.zip bo.outs).find? (fun q => q.1.pat.ctor.name == c) = some q := by
    apply Option.isSome_iff_exists.1
    apply List.find?_isSome.2
    obtain ⟨o₀, ho₀⟩ := mem_zip_left (l' := bo.outs) (by omega) hb₀
    exact ⟨_, ho₀, by simpa using hb₀n⟩
  have hbm : (b, ob) ∈ bs.zip bo.outs := List.mem_of_find?_eq_some hfind
  have hbn : b.pat.ctor.name = c := by simpa using List.find?_some hfind
  have hbmem : b ∈ bs := (List.of_mem_zip hbm).1
  have hobm : ob ∈ bo.outs := (List.of_mem_zip hbm).2
  have hpick : ∀ as, pickBranch m (.app ⟨.ctor, c⟩ as) bo.trees = .ok (.mk b.pat ob.tree) := by
    intro as
    apply pickBranch_many hm
    rw [htr, List.find?_map]
    simp only [Function.comp_def, Branch.pat]
    simp only [Branch.pat] at hfind
    rw [hfind]
    rfl
  obtain ⟨Γb, idsb, hsurv, hcheck⟩ := hbr b ob hbm
  obtain ⟨f, hf1, hf2⟩ := survivor_spec hsurv
  rw [hbn, hfc] at hf1
  cases hf1
  simp only [Forced.ok.injEq] at hf2
  obtain ⟨rfl, rfl⟩ := hf2
  have hreach : reach so.sc r s.pos = none := by simp [reach, hu, hrt]
  rw [hreach] at hcheck
  subst hbn
  have hfl := forcings_fields hfs (List.mem_map_of_mem hbmem) hsig hws
  obtain ⟨hIb, hEb⟩ := branch hI₁' hsig hws hsat hpre hids hfl hent
  have hgb : ∀ g', some gb = some g' → g'.Ok W.Sc (ρ ++ ρ₁ ++ ws) := by
    rintro g' ⟨⟩
    refine ⟨⟨envv, by rw [hgbe]; exact Term.evalList_frame_ρ ws henv⟩, fun _ envv' he => ?_⟩
    rw [hgbe, Term.evalList_frame_ρ ws henv] at he
    cases he
    rw [hgbw]
    refine WantsCons.frame ws (WantsCons.congr (by simp) (fun i w w' h1 h2 => ?_) hcons)
    rw [List.getElem?_map] at h1
    rw [List.getElem?_mapIdx] at h2
    cases hb : tele[i]? <;> simp only [hb, Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq] at h1 h2
    subst h1 h2
    exact ⟨rfl, rfl⟩
  rw [closed_eq (by rw [Scope.bind_eq]) fun o h => (ihbs b hbmem _ _ _ o (by rw [Scope.bind_eq]) h).2.2.1]
    at hcheck
  obtain ⟨hpostb, -⟩ := ihb b hbmem _ _ (some gb) n0 W (ρ ++ ρ₁ ++ ws) act ob hIb hgb hcheck
  have hobl : ob.res.length = tele.length := by rw [checkExpr_length _ hcheck, hgbw, List.length_mapIdx]
  have hobt : ∀ i r'', taint i = false → ob.res[i]? = some r'' → r''.tainted = false := fun i r'' h hr'' => by
    rw [← htaint] at h
    simp only [Bool.or_eq_false_iff, List.any_eq_false] at h
    simpa [hr''] using h.2 ob hobm
  have hobu : ob.sc.taintedBy = none := by
    cases hob : ob.sc.taintedBy with
    | none => rfl
    | some _ =>
      have hall' := ((checkExpr_removed hcheck).2.1 (by simp [hob])).2
      obtain ⟨r'', hr''⟩ : ∃ r'', ob.res[k]? = some r'' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have := hobt k r'' hkt hr''
      rw [hall' r'' (List.mem_of_getElem? hr'')] at this
      cases this
  obtain ⟨ρ₂, vsb, -, -, -, hwb, hrunb⟩ := hpostb hobu
  have hwb' := hwb gb rfl envv (by rw [hgbe]; exact Term.evalList_frame_ρ ws henv)
  have htele : TeleOk W.Sc (ρ ++ ρ₁) (fun k => !taint k) tele envv vsb := by
    refine TeleOk.restrict (n := so.sc.Γ.length) ?_ hens' (teleOk_of_wantsSat hwb'
      (by rw [hgbw, List.length_mapIdx]) (fun i w b' h1 h2 => ?_) fun k hk h => ?_)
    · rw [← hlenρ, List.append_assoc (ρ ++ ρ₁) ws ρ₂, List.take_append_length, List.take_length]
    · rw [hgbw] at h1; exact mapIdx_want i w b' h1 h2
    · obtain ⟨r'', hr''⟩ : ∃ r'', ob.res[k]? = some r'' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      simp [hr'', hobt k r'' (by simpa using h) hr'']
  refine ⟨fin vsb htele fun hnr env hE => ?_, fun _ habs => ?_⟩
  · have hw : (C.erased || g.any (·.allErased)) = false := by
      simp only [Bool.or_eq_false_iff] at hnr ⊢; exact hnr.1
    have hCe : C.erased = false := by simp only [Bool.or_eq_false_iff] at hw; exact hw.1
    obtain ⟨hE₁, hrun⟩ := hrun₁ env hE
    obtain ⟨us₁, a, hev₁, hone, hrel⟩ := hrun (by rw [her, hw])
    obtain ⟨as, rfl⟩ : ∃ as, a = .app ⟨.ctor, b.pat.ctor.name⟩ as := by
      cases hrel hrt with
      | type h => cases h
      | app => exact ⟨_, rfl⟩
    obtain ⟨env', hbind, hE'⟩ := hEb env m _ hm hE₁ (hrel hrt)
    obtain ⟨usb, hevb, usb', htakeb, hrelb⟩ := hrunb env' hE'
    obtain ⟨us, hannt, htake⟩ := annotation_annTake hann (show take tele.length usb = .ok usb' by
      rw [← hobl]; exact htakeb)
    refine ⟨us, .match hev₁ hone (hpick as) hbind hevb hannt, usb', by rw [hrsl]; exact htake,
      fun i r' a' v' hr' ha' hv' ht' => ?_⟩
    have hi : i < tele.length := by rw [← hrsl]; exact (List.getElem?_eq_some_iff.1 hr').1
    obtain ⟨bi, hbi⟩ : ∃ bi, tele[i]? = some bi := ⟨_, List.getElem?_eq_getElem hi⟩
    have hri := (hrs i bi hbi).1
    rw [hr'] at hri
    cases hri
    obtain ⟨r'', hr''⟩ : ∃ r'', ob.res[i]? = some r'' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hm' := hrelb i r'' a' v' hr'' ha' hv' (hobt i r'' ht' hr'')
    have hgbi : gb.wants[i]? = some { Want.of bi with
        mult := if g.any (·.erasedAt i) then .erased else bi.mult } := by
      rw [hgbw, List.getElem?_mapIdx, hbi]; simp [hCe]
    by_cases hgi : g.any (·.erasedAt i) = true
    · have : C.posMult g i = .erased := by simp [Ctx.posMult, hgi]
      rw [this]; exact MultRel.erased hm'.approx
    · have hbe : bi.mult ≠ .erased := fun he => hgi (by
        have := herr hw i _ (hores' ▸ hr') (by simp [he])
        simpa [hCe] using this)
      have h1 : C.posMult g i = .many := by simp [Ctx.posMult, hCe, hgi]
      have h2 : Ctx.posMult (C.enter (C.erased || g.any (·.allErased))) (some gb) i = .many := by
        simp only [Given.erasedAt] at hgi
        simp [Ctx.posMult, hw, Given.erasedAt, hgbi, hgi, hbe]
      rw [h1]; rw [h2] at hm'; exact hm'
  · cases bs with
    | nil => cases hbmem
    | cons => simp [Expr.absurd] at habs

theorem reach_eq_none {sc : Scope} {r : Res} {pos : Pos} (h : reach sc r pos = none) :
    sc.taintedBy = none ∧ r.tainted = false := by
  unfold reach at h
  cases ht : sc.taintedBy <;> cases hr : r.tainted <;> simp_all

theorem with_holes {sc : Scope} {Γ : Entries} {tb : Option Pos} (h : sc.holes = []) :
    ({ sc with Γ, taintedBy := tb } : Scope) = { sc with Γ, taintedBy := tb, holes := [] } := by
  cases sc; simp_all

/-- `patletMany_sound`. -/
theorem patletSound {p : Pos} {ct : Bool} {m : Option Mult} {pat : Pattern} {rhs : Expr}
    (hm : m ≠ some .erased) (ih : ExprSound rhs) (ihs : ExprShape rhs) : StmtSound (.patlet p ct m pat rhs) := by
  intro C sc n0 W ρ act o hI h
  have hme : (m == some .erased) = false := by simpa using hm
  simp only [checkStmt, hme, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.or_false] at h
  obtain ⟨u, hct, h⟩ := bind_eq_ok.1 h
  obtain rfl : ct = false := by simpa using ensure_ok hct
  obtain ⟨u', -, h⟩ := bind_eq_ok.1 h
  obtain ⟨o', ho', h⟩ := bind_eq_ok.1 h
  rw [keep_ok] at h
  rw [closed_eq hI.holes fun o h => (ihs _ sc none o hI.holes h).2.2.1] at ho'
  obtain ⟨r, hr, h⟩ := bind_eq_ok.1 h
  obtain ⟨fs, hfs, h⟩ := bind_eq_ok.1 h
  obtain ⟨sc', hsc', h⟩ := bind_eq_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨Γ, ids, ⟨f, hf1, hf2⟩, hone, rfl⟩ := patBind_spec hsc'
  intro hu
  have hreach : reach o'.sc r rhs.pos = none := by rw [Scope.bind_eq] at hu; exact hu
  obtain ⟨hu₁, hrt⟩ := reach_eq_none hreach
  obtain ⟨ρ₁, v, hI₁, hv, hokv, hrun₁⟩ :=
    scrut (C₂ := { C with place := "the right-hand side of a `many` pattern `let`" }) ih ihs hI rfl rfl rfl ho' hr
      hu₁
  obtain ⟨V, hV⟩ := hokv.2.2 hrt
  obtain ⟨c, ws, sig, Γ', ids', pat', rfl, hfc, hsig, hws, hsat, hpre, -, hids, -, hent⟩ :=
    forcings_value hI₁ hfs hv hV
  obtain rfl : c = pat.ctor.name := Decidable.byContradiction fun hne =>
    hone rfl _ (List.mem_of_find?_eq_some hfc) hne Γ' ids' rfl
  rw [hfc] at hf1
  cases hf1
  simp only [Forced.ok.injEq] at hf2
  obtain ⟨rfl, rfl⟩ := hf2
  have hfl := forcings_fields hfs (List.mem_singleton_self _) hsig hws
  obtain ⟨hIb, hEb⟩ := branch hI₁ hsig hws hsat hpre hids hfl hent
  simp only
  rw [hreach, with_holes hI₁.holes]
  refine ⟨ρ₁ ++ ws, by rw [← List.append_assoc]; exact hIb, fun hCe env hE => ?_⟩
  obtain ⟨hE₁, hrun⟩ := hrun₁ env hE
  obtain ⟨us, a, hev, hone', hrel⟩ := hrun (by simp [hCe])
  obtain ⟨env', hbind, hE'⟩ := hEb env m a hm hE₁ (hrel hrt)
  exact ⟨env', .patlet hev hone' hbind, by rw [← List.append_assoc]; exact hE'⟩

end MatchMany

end Pledge
