import Pledge.Core

namespace Pledge

/-- An activation's measure (SOUNDNESS.md part 6): the group of the running function and
the values of its `subterm` parameters, padded with `none` to the group's largest number of
`subterm` parameters. Top-level code runs with a group above every function's. It is meant only
for the totality proof, which inducts on it; evaluation does not consult it. -/
structure Act where
  group : Nat
  subs : List (Option Value)
  deriving Repr, DecidableEq, Inhabited

mutual
  /-- `v.isSub w`: `v` is a strict subtree of `w`. -/
  def Value.isSub (v : Value) : Value → Bool
    | .app _ args => Value.isSubList v args
    | .removed => false
  def Value.isSubList (v : Value) : List Value → Bool
    | [] => false
    | a :: as => v == a || v.isSub a || Value.isSubList v as
end

/-- `v.lt w`: `v` is a strict subtree of `w`. -/
def Value.lt (v w : Value) : Prop := v.isSub w = true

instance : DecidableRel Value.lt := fun v w => inferInstanceAs (Decidable (v.isSub w = true))

mutual
  theorem Value.sizeOf_isSub (v : Value) : (w : Value) → v.isSub w = true → sizeOf v < sizeOf w
    | .app h args, hs => by
      have := Value.sizeOf_isSubList v args hs
      simp only [Value.app.sizeOf_spec]; omega
    | .removed, hs => by simp [Value.isSub] at hs
  theorem Value.sizeOf_isSubList (v : Value) :
      (as : List Value) → Value.isSubList v as = true → sizeOf v < sizeOf as
    | [], hs => by simp [Value.isSubList] at hs
    | a :: as, hs => by
      simp only [Value.isSubList, Bool.or_eq_true, beq_iff_eq] at hs
      simp only [List.cons.sizeOf_spec]
      rcases hs with (rfl | hs) | hs
      · omega
      · have := Value.sizeOf_isSub v a hs; omega
      · have := Value.sizeOf_isSubList v as hs; omega
end

theorem Value.lt_wf : WellFounded Value.lt :=
  Subrelation.wf (fun {v w} h => Value.sizeOf_isSub v w h) (measure sizeOf).wf

/-- `SubsLt as bs`: lists of equal length that agree up to some `k`, where `as` holds a strict
subtree of the value `bs` holds. -/
def SubsLt (as bs : List (Option Value)) : Prop :=
  as.length = bs.length ∧
  ∃ k x y, as.take k = bs.take k ∧ as[k]? = some (some x) ∧ bs[k]? = some (some y) ∧ x.lt y

/-- An activation's measure is below another's (SOUNDNESS.md part 6). -/
def Act.lt (a b : Act) : Prop := a.group < b.group ∨ a.group = b.group ∧ SubsLt a.subs b.subs

theorem Act.lt_of_group {a b : Act} (h : a.group < b.group) : Act.lt a b := .inl h

theorem Act.lt_of_subs {a b : Act} {k : Nat} {x y : Value} (hg : a.group = b.group)
    (hl : a.subs.length = b.subs.length) (ht : a.subs.take k = b.subs.take k)
    (ha : a.subs[k]? = some (some x)) (hb : b.subs[k]? = some (some y)) (hxy : x.lt y) : Act.lt a b :=
  .inr ⟨hg, hl, k, x, y, ht, ha, hb, hxy⟩

def OptLt : Option Value → Option Value → Prop
  | some x, some y => x.lt y
  | _, _ => False

instance : DecidableRel OptLt := fun a b => match a, b with
  | some x, some y => inferInstanceAs (Decidable (x.lt y))
  | none, _ => isFalse id
  | some _, none => isFalse id

theorem SubsLt.nil_left {bs} : ¬ SubsLt [] bs := fun ⟨_, _, _, _, _, h, _⟩ => by simp at h

theorem SubsLt.nil_right {as} : ¬ SubsLt as [] := fun ⟨_, _, _, _, _, _, h, _⟩ => by simp at h

theorem SubsLt.cons_iff {a b as bs} :
    SubsLt (a :: as) (b :: bs) ↔ as.length = bs.length ∧ OptLt a b ∨ a = b ∧ SubsLt as bs := by
  constructor
  · rintro ⟨hl, k, x, y, ht, ha, hb, hxy⟩
    cases k with
    | zero => simp at ha hb; subst ha hb; exact .inl ⟨by simpa using hl, hxy⟩
    | succ k =>
      simp only [List.take_succ_cons, List.cons.injEq] at ht
      exact .inr ⟨ht.1, by simpa using hl, k, x, y, ht.2, by simpa using ha, by simpa using hb, hxy⟩
  · rintro (⟨hl, h⟩ | ⟨rfl, hl, k, x, y, ht, ha, hb, hxy⟩)
    · match a, b, h with
      | some x, some y, h => exact ⟨by simp [hl], 0, x, y, by simp, rfl, rfl, h⟩
    · exact ⟨by simp [hl], k + 1, x, y, by simp [ht], ha, hb, hxy⟩

instance SubsLt.dec : (as bs : List (Option Value)) → Decidable (SubsLt as bs)
  | [], _ => isFalse SubsLt.nil_left
  | _ :: _, [] => isFalse SubsLt.nil_right
  | _ :: as, _ :: bs => have := SubsLt.dec as bs; decidable_of_iff _ SubsLt.cons_iff.symm

instance : DecidableRel Act.lt := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∧ _))

theorem OptLt.acc : ∀ a, Acc OptLt a
  | none => ⟨_, fun b h => by cases b <;> simp [OptLt] at h⟩
  | some v => by
    induction Value.lt_wf.apply v with
    | intro v _ ih =>
      exact ⟨_, fun b h => by
        cases b with
        | none => simp [OptLt] at h
        | some w => exact ih w h⟩

theorem SubsLt.acc_len : ∀ n (as : List (Option Value)), as.length = n → Acc SubsLt as
  | 0, as, h => ⟨_, fun _ hb => absurd (List.length_eq_zero_iff.1 h ▸ hb) SubsLt.nil_right⟩
  | _ + 1, [], h => by simp at h
  | n + 1, a :: as, h => by
    have ih := SubsLt.acc_len n
    suffices ∀ a, Acc OptLt a → ∀ as, Acc SubsLt as → as.length = n → Acc SubsLt (a :: as) from
      this a (OptLt.acc a) as (ih as (by simpa using h)) (by simpa using h)
    intro a ha
    induction ha with
    | intro a _ iha =>
      intro as has
      induction has with
      | intro as _ ihs =>
        intro hl
        refine ⟨_, fun cs hc => ?_⟩
        match cs, hc with
        | [], hc => exact absurd hc SubsLt.nil_left
        | c :: cs, hc =>
          rcases SubsLt.cons_iff.1 hc with ⟨hl', hca⟩ | ⟨rfl, hcs⟩
          · exact iha c hca cs (ih cs (by omega)) (by omega)
          · exact ihs cs hcs (hcs.1.trans hl)

theorem Act.lt_wf : WellFounded Act.lt := by
  suffices ∀ g subs, Acc Act.lt ⟨g, subs⟩ from ⟨fun ⟨g, subs⟩ => this g subs⟩
  intro g
  induction g using Nat.strongRecOn with
  | _ g ihg =>
    intro subs
    induction SubsLt.acc_len _ subs rfl with
    | intro subs _ ihs =>
      refine ⟨_, fun ⟨g', subs'⟩ h => ?_⟩
      rcases h with h | ⟨h, hs⟩
      · exact ihg g' h subs'
      · cases h; exact ihs subs' hs

instance : WellFoundedRelation Act := ⟨Act.lt, Act.lt_wf⟩

/-- The measure of a call to `d` with arguments `vs`. -/
def calleeAct (d : FnDef) (vs : List Value) : Act :=
  let s := (d.subterm.zip vs).filterMap fun (b, v) => if b then some (some v) else none
  ⟨d.group, s ++ List.replicate (d.pad - s.length) none⟩

/-- The measure of top-level code: above every function's group. -/
def Act.top (F : Fns) : Act := ⟨F.foldr (fun d n => max d.group n) 0 + 1, []⟩

theorem Act.lt_top {F : Fns} {n d} (h : F.find n = some d) (vs : List Value) :
    Act.lt (calleeAct d vs) (Act.top F) := by
  refine Act.lt_of_group ?_
  have hm := List.mem_of_find?_eq_some h
  simp only [calleeAct, Act.top]
  clear h
  induction F with
  | nil => cases hm
  | cons e F ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hm with rfl | hm
    · omega
    · have := ih hm; omega


end Pledge
