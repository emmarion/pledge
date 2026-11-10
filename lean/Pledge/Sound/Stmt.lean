import Pledge.Sound.Expr

namespace Pledge

mutual
theorem Term.close_append {ρ : List Value} (ρ' : List Value) :
    ∀ t : Term, t.entriesBelow ρ.length = true → t.close (ρ ++ ρ') = t.close ρ
  | .entry i, h => by
    simp only [Term.entriesBelow, decide_eq_true_eq] at h
    simp [Term.close, List.getElem?_append_left h]
  | .bound _, _ => rfl
  | .app _ as, h => by simp only [Term.close, Term.closeList_append ρ' as h]
theorem Term.closeList_append {ρ : List Value} (ρ' : List Value) :
    ∀ as : List Term, Term.entriesBelowList ρ.length as = true → Term.closeList (ρ ++ ρ') as = Term.closeList ρ as
  | [], _ => rfl
  | a :: as, h => by
    simp only [Term.entriesBelowList, Bool.and_eq_true] at h
    simp only [Term.closeList, Term.close_append ρ' a h.1, Term.closeList_append ρ' as h.2]
end

theorem Sig.close_append {ρ : List Value} (ρ' : List Value) {sig : Sig} (h : sig.entriesBelow ρ.length = true) :
    sig.close (ρ ++ ρ') = sig.close ρ := by
  simp only [Sig.entriesBelow, Bool.and_eq_true, List.all_eq_true] at h
  simp only [Sig.close, Term.close_append ρ' _ h.2, Sig.mk.injEq, and_true, true_and]
  refine List.map_congr_left fun b hb => ?_
  have hb' := h.1 b hb
  simp only [TBinder.entriesBelow, Bool.and_eq_true, Option.all_eq_true] at hb'
  simp only [TBinder.close, Term.close_append ρ' _ hb'.1, TBinder.mk.injEq, true_and]
  cases hi : b.is with
  | none => simp
  | some e => simp [Term.close_append ρ' e (hb'.2 e hi)]

theorem SigsOk.mono {n m : Nat} {S : Sigs} (hnm : n ≤ m) (h : SigsOk n S) : SigsOk m S := fun sig hs =>
  let ⟨h1, h2⟩ := h sig hs
  ⟨Sig.entriesBelow_mono hnm h1, h2⟩

theorem GlobalsOk.mono {n m phase : Nat} {gs : List Global} {fn : Option FnCtx} {S : Sigs} {W : World} {act : Act}
    (hnm : n ≤ m) (h : GlobalsOk n phase gs fn S W act) : GlobalsOk m phase gs fn S W act := by
  intro x g hg
  have := h x g hg
  match g, this with
  | .fn _ none, _ => trivial
  | .fn _ (some _), ⟨h1, h2, h3, h4, h5⟩ =>
    refine ⟨fun b hb => TBinder.entriesBelow_mono hnm (h1 b hb), fun b hb => TBinder.entriesBelow_mono hnm (h2 b hb),
      fun ρ' hρ' => h3 ρ' ?_, h4, h5⟩
    have := congrArg (List.take n) hρ'
    simpa [List.take_take, Nat.min_eq_left hnm] using this
  | .type .., h' => exact h'
  | .ctor _, h' => exact h'

theorem GoalBelow.mono {n m : Nat} {g : CheckedGoal} (hnm : n ≤ m) (h : GoalBelow n g) : GoalBelow m g := by
  unfold GoalBelow at h ⊢
  split at h
  · exact Term.entriesBelow_mono hnm _ h
  · exact fun b hb => TBinder.entriesBelow_mono hnm (h b hb)

theorem World.Le.extend (W : World) (ρ' : List Value) : W.Le { W with ρ := W.ρ ++ ρ' } :=
  ⟨Prog.Ext.refl _, Sigs.Sub.refl _, List.prefix_append _ _, fun _ _ _ _ _ h h' => by
    simp only at h'; rw [h] at h'; cases h'⟩

theorem TopState.world_extend {st st' : TopState} {ρ : List Value} (ρ' : List Value)
    (hok : SigsOk ρ.length st.sc.sigs) (hs : st'.sc.sigs = st.sc.sigs) (hf : st'.fns = st.fns)
    (hg : st'.globals = st.globals) : st'.world (ρ ++ ρ') = { st.world ρ with ρ := ρ ++ ρ' } := by
  simp only [TopState.world, TopState.prog, hs, hf, hg, World.mk.injEq, and_true, true_and]
  exact List.map_congr_left fun sig hsig => Sig.close_append ρ' (hok sig hsig).1

theorem Act.top_group {F : Fns} {d : FnDef} (h : d ∈ F) : d.group < (Act.top F).group := by
  simp only [Act.top]
  induction F with
  | nil => cases h
  | cons e F ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem TopInv.sigsClose {st : TopState} {ρ : List Value} (hI : TopInv st ρ) :
    SigsClose st.sc.sigs ρ (st.world ρ).Sc :=
  SigsClose.close hI.noRemoved

/-- Top-level code in an untainted scope is checked under the main lemma's invariant, in the world of the state. -/
theorem TopInv.inv {st : TopState} {ρ : List Value} {C : Ctx} (hI : TopInv st ρ) (ht : st.sc.taintedBy = none)
    (hph : C.phase = st.phase) (hgl : C.globals = st.globals) (hfn : C.fn = none) :
    Inv C st.sc st.sc.Γ.length (st.world ρ) ρ (Act.top st.fns) := by
  have hL := hI.live ht
  refine ⟨hI.holes, ht, hL.sat, by simp [TopState.world, hI.len], rfl, fun ρ' hρ' => ?_, hI.sigsOk, ?_,
    hL.names, ?_, fun f hf => by simp [hfn] at hf⟩
  · refine hI.sigsClose.of_entriesBelow (n := st.sc.Γ.length) ?_ fun sig hs => (hI.sigsOk sig hs).1
    simpa [TopState.world] using hρ'.symm
  · simp [TopState.world, Sigs.find_map_close, hI.noJunk]
  · rw [hgl, hfn, hph]
    exact hL.globals _ (World.Le.refl _) _ fun d hd => Act.top_group hd

/-- A top-level statement other than a `comptime` pattern `let` keeps the invariant for the valuation extended by
ideal values of its new entries (§11, §12): in an untainted scope by `Stmt.sound`, the run giving the new
environment; in a tainted one, by any values, nothing being run. -/
theorem topStmt_sound {st st' : TopState} {ρ : List Value} {s : Stmt} (hI : TopInv st ρ) (hp : s.holeFree = true)
    (hc : ∀ p m pat rhs, s ≠ .patlet p true m pat rhs) (h : topItem st (.stmt s) = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  sorry

/-- A `comptime` pattern `let` (§11) keeps the invariant: with an untainted scrutinee, the run's value, related to
the ideal one, is headed by the pattern's value constructor, so the ideal value is too and its forcing survived. -/
theorem comptimeLet_sound {st st' : TopState} {ρ : List Value} {p : Pos} {m : Option Mult} {pat : Pattern}
    {rhs : Expr} (hI : TopInv st ρ) (hp : rhs.holeFree = true) (h : comptimeLet st p m pat rhs = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  sorry

/-- `print` keeps the invariant. -/
theorem print_sound {st st' : TopState} {ρ : List Value} {p : Pos} {e : Expr} (hI : TopInv st ρ)
    (hp : e.holeFree = true) (h : topItem st (.print p e) = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  sorry

theorem GoalBelow.type {n : Nat} {g : CheckedGoal} {t : Term} (h : GoalBelow n g) (hk : g.kind = .type t) :
    t.entriesBelow n = true := by
  unfold GoalBelow at h; rw [hk] at h; exact h

theorem GoalBelow.fn {n : Nat} {g : CheckedGoal} {ps rs : Telescope} (h : GoalBelow n g) (hk : g.kind = .fn ps rs) :
    ∀ b ∈ ps ++ rs, b.entriesBelow n = true := by
  unfold GoalBelow at h; rw [hk] at h; exact h

/-- `qed e;` against a type goal (§12): if it proves the goal, `e`'s untainted result has an ideal value of the goal's
type, in an untainted scope. -/
theorem typeQed_sound {st st' : TopState} {ρ : List Value} {p : Pos} {e : Expr} {goal : CheckedGoal} {t : Term}
    (hI : TopInv st ρ) (hp : e.holeFree = true) (hgoal : st.goal = some goal) (hk : goal.kind = .type t)
    (h : (do
        let o ← checkExpr st.ctx st.sc (some goal.given) e
        let _ ← keep o.snaps (st.eval p o.tree (o.res.any fun x => x.tainted))
        let st ← pure { st with sc := o.sc, proved := !o.res.any fun x => x.tainted, snaps := st.snaps ++ o.snaps }
        pure { st with qedChecks := true, proved := st.proved && st.sc.taintedBy.isNone && !goal.tainted } :
        CheckM TopState) = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  sorry

/-- Telescopes with no `difference` agree by value, binder by binder, under a valuation satisfying the scope's rules,
multiplicities included. -/
theorem difference_agree {Γ : Entries} {ρ : List Value} (hΓ : RulesHold Γ ρ) :
    ∀ {Δ Δ' : Telescope}, difference Γ Δ Δ' = none → Telescope.Agree ρ ρ Δ Δ'
  | [], [], _ => trivial
  | ⟨xn, xt, xi, xm⟩ :: xs, ⟨yn, yt, yi, ym⟩ :: ys, h => by
    cases xi <;> cases yi <;> simp [difference] at h <;> split at h <;> try cases h
    · rename_i hc
      exact ⟨⟨fun env => identical.eval_eq hΓ hc.2, fun env => rfl, hc.1⟩, difference_agree hΓ (by simpa using h)⟩
    · rename_i hc
      exact ⟨⟨fun env => identical.eval_eq hΓ hc.2.1, fun env => by simp [identical.eval_eq hΓ hc.2.2], hc.1⟩,
        difference_agree hΓ (by simpa using h)⟩
  | [], _ :: _, h | _ :: _, [], h => by simp [difference] at h

theorem Telescope.Agree.append {ρ ρ' : List Value} : ∀ {Δ₁ Δ₁' Δ₂ Δ₂' : Telescope}, Δ₁.length = Δ₁'.length →
    Telescope.Agree ρ ρ' (Δ₁ ++ Δ₂) (Δ₁' ++ Δ₂') → Telescope.Agree ρ ρ' Δ₁ Δ₁' ∧ Telescope.Agree ρ ρ' Δ₂ Δ₂'
  | [], [], _, _, _, h => ⟨trivial, h⟩
  | _ :: _, _ :: _, _, _, hl, h =>
    let ⟨h1, h2⟩ := Telescope.Agree.append (by simpa using hl) h.2
    ⟨⟨h.1, h1⟩, h2⟩
  | [], _ :: _, _, _, hl, _ | _ :: _, [], _, _, hl, _ => by simp at hl

/-- A function whose telescopes have no `difference` from a function goal's, and that is untainted, proves it in every
later world (§12): its specification gives the returns, and its run on related arguments related results. -/
theorem fnGoal_holds {st : TopState} {ρ : List Value} {g : CheckedGoal} {ps rs : Telescope} {n m : String}
    {sig : FnSig} {W' : World} (hI : TopInv st ρ) (hk : g.kind = .fn ps rs) (ht : st.sc.taintedBy = none) (hb : ∀ b ∈ ps ++ rs, b.entriesBelow st.sc.Γ.length = true)
    (hg : st.globals.find? (·.name == n) = some (.fn m (some sig))) (hst : sig.tainted = false)
    (hpl : sig.params.length = ps.length)
    (hd : difference st.sc.Γ (ps ++ rs) (sig.params ++ sig.returns) = none) (hW : (st.world ρ).Le W') :
    GoalHolds W' st.phase g (some n) := by
  sorry

theorem qedFnGoal_spec {st st' : TopState} {ps rs : Telescope} {e : Expr} (h : qedFnGoal st ps rs e = .ok st') :
    ∃ n m sig, st.globals.find? (·.name == n) = some (.fn m (some sig)) ∧ sig.params.length = ps.length ∧
      sig.returns.length = rs.length ∧ difference st.sc.Γ (ps ++ rs) (sig.params ++ sig.returns) = none ∧
      st' = { st with qedFn := some n, proved := !sig.tainted } := by
  unfold qedFnGoal at h
  simp only at h
  split at h
  · rename_i n pos
    split at h
    · rename_i name sig hgl
      split at h
      · simp [failAt_eq, bind, Except.bind] at h
      · rename_i hlen
        split at h
        · simp [failAt_eq, bind, Except.bind] at h
        · rename_i hdiff
          simp only [pure, Except.pure, Except.ok.injEq] at h
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, ne_eq, Decidable.not_not] at hlen
          refine ⟨n, name, sig, hgl, hlen.1, hlen.2, ?_, h.symm⟩
          cases hd : difference st.sc.Γ (ps ++ rs) (sig.params ++ sig.returns) with
          | none => rfl
          | some i => exact (hdiff i hd).elim
    · simp [failAt_eq] at h
  · simp [failAt_eq] at h

/-- A `qed` keeps the invariant, and, if it proves the goal, the goal holds in every later world (§12). -/
theorem qed_sound {st st' : TopState} {ρ : List Value} {p : Pos} {e : Expr} (hI : TopInv st ρ)
    (hp : e.holeFree = true) (h : topItem st (.qed p e) = .ok st') :
    ∃ ρ', (st.world ρ).Le (st'.world (ρ ++ ρ')) ∧ TopInv st' (ρ ++ ρ') := by
  sorry

end Pledge
