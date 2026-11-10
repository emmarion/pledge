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
    (evalList_fieldRes (by rw [hids, hI.sat.1.1])) fun i r v hr hv _ => hws.typed v (List.mem_of_getElem? hv)

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
    (ha : m ≠ some .erased → Rel S phase a (.app ⟨.ctor, c⟩ ws)) (hpat : pat.ctor.name = c) :
    ∃ env', bindPattern env m pat a = .ok env' ∧
      EnvRel S phase (Scope.bind { sc with Γ := Γ', taintedBy := tb, holes := hs } pat.fields (fieldRes ids))
        (ρ ++ ws) env' := by
  sorry

end Pledge
