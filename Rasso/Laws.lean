import Rasso.WF

/-!
# Rasso: laws of the finite algebra

The usual laws, as corollaries of the membership lemmas (`Rasso.Mem`) and of
well-formedness (`Rasso.WF`):

* ⋈ is commutative and associative (`Finrel.join_comm`, `Finrel.join_assoc`).
* σ distributes over ∪ (`Finrel.select_union`).
* σ moves into the operand of a join it reads (`Finrel.select_join`).

Each law says two finite relations have the same **body** (the same tuples). Because a
body is a quotient (a set of tuples), this is equality, not a statement about lists.

Conventions:

* For ⋈, the two sides' headings have the same attributes but may list them in a
  different order, so the law states equality of bodies plus equality of attribute
  sets, not equality of the finite relations. The domains of shared attributes are both
  `Domain.inter` of the operands' domains, in the other order; that `Domain.inter` is
  commutative is not proved here.
* The laws take each side's success (`= .ok _`) as hypotheses. They say nothing about
  when one side is refused and the other is not; σ of a join, for instance, does not
  test a tuple of `R` that joins nothing, so it can succeed where σ of `R` is refused.
* "σ reads only `R`'s attributes" is the hypothesis `hp`: the test gives the same answer
  on a merged tuple as on its `R` part. For a σ written with a term, this would follow
  from "a term's value depends only on the attributes it names", which is not proved
  here.
-/

namespace Rasso

/-! ## Tuples as finite maps -/

/-- Two tuples agree: where both have an attribute, they have the same value. -/
def Compat (u v : Tuple) : Prop := ∀ a x y, (a, x) ∈ u → (a, y) ∈ v → x = y

theorem Compat.symm {u v : Tuple} (h : Compat u v) : Compat v u :=
  fun a x y hx hy => (h a y x hy hx).symm

theorem agrees_iff {u v : Tuple} (hv : v.attrs.Nodup) : u.agrees v = true ↔ Compat u v := by
  constructor
  · intro h a x y hx hy; exact Finrel.agrees_eq h hx (mem_lookup hv hy)
  · intro h
    refine List.all_eq_true.mpr fun ⟨a, x⟩ hx => ?_
    cases hl : v.get? a with
    | none => simp only [hl]
    | some y => simp only [hl, beq_iff_eq]; exact h a x y hx (lookup_mem hl)

/-- The pairs `merge` sorts. -/
def mergeList (u v : Tuple) : List (String × Value) :=
  u ++ v.filter fun p => (u.get? p.1).isNone

theorem merge_eq (u v : Tuple) : u.merge v = Tuple.ofPairs (mergeList u v) := rfl

theorem mergeList_nodup {u v : Tuple} (hu : u.attrs.Nodup) (hv : v.attrs.Nodup) :
    ((mergeList u v).map (·.1)).Nodup := by
  rw [mergeList, List.map_append, List.nodup_append]
  refine ⟨hu, hv.sublist (List.filter_sublist.map _), fun a ha b hb e => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
  have h1 := (List.mem_filter.mp hp).2
  have h2 := lookup_isSome_iff_mem (e ▸ ha)
  simp only [Tuple.get?] at h1
  cases hl : u.lookup p.1 with
  | none => rw [hl] at h2; cases h2
  | some _ => rw [hl] at h1; cases h1

theorem mem_mergeList {u v : Tuple} (hc : Compat u v) {p : String × Value} :
    p ∈ mergeList u v ↔ p ∈ u ∨ p ∈ v := by
  rw [mergeList, List.mem_append, List.mem_filter]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨a, y⟩ := p
      simp only [Tuple.get?]
      cases hl : u.lookup a with
      | none => exact Or.inr ⟨h, rfl⟩
      | some x =>
        have := hc a x y (lookup_mem hl) h
        subst this
        exact Or.inl (lookup_mem hl)

theorem mem_merge {u v : Tuple} (hc : Compat u v) {p : String × Value} :
    p ∈ u.merge v ↔ p ∈ u ∨ p ∈ v := by
  rw [merge_eq, mem_ofPairs, mem_mergeList hc]

theorem merge_attrs_nodup {u v : Tuple} (hu : u.attrs.Nodup) (hv : v.attrs.Nodup) :
    (u.merge v).attrs.Nodup :=
  ((List.mergeSort_perm _ _).map _).nodup_iff.mpr (mergeList_nodup hu hv)

/-- Sorting two lists of pairs with the same members, names all different, gives the same
tuple. -/
theorem ofPairs_eq {L₁ L₂ : List (String × Value)} (h₁ : (L₁.map (·.1)).Nodup)
    (h₂ : (L₂.map (·.1)).Nodup) (hm : ∀ p, p ∈ L₁ ↔ p ∈ L₂) :
    Tuple.ofPairs L₁ = Tuple.ofPairs L₂ := by
  have nd : ∀ {L : List (String × Value)}, (L.map (·.1)).Nodup → L.Nodup := fun {L} h =>
    List.nodup_iff_pairwise_ne.mpr ((List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp h)).imp
      fun {a b} (h : a.1 ≠ b.1) (e : a = b) => h (e ▸ rfl))
  have trans : ∀ (a b c : String × Value), decide (a.1 ≤ b.1) = true → decide (b.1 ≤ c.1) = true →
      decide (a.1 ≤ c.1) = true := fun _ _ _ h₁ h₂ => by
    simp only [decide_eq_true_eq] at *; exact String.le_trans h₁ h₂
  have total : ∀ (a b : String × Value), (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1)) = true :=
    fun a b => by simpa using String.le_total a.1 b.1
  apply List.Perm.eq_of_pairwise (le := fun p q => decide (p.1 ≤ q.1) = true)
  · intro a b ha hb hab hba
    simp only [decide_eq_true_eq] at hab hba
    have ha' := (hm a).mp (mem_ofPairs.mp ha)
    exact inj_of_nodup_map h₂ a ha' b (mem_ofPairs.mp hb) (String.le_antisymm hab hba)
  · exact List.pairwise_mergeSort trans total _
  · exact List.pairwise_mergeSort trans total _
  · exact (List.mergeSort_perm _ _).trans
      (((List.perm_ext_iff_of_nodup (nd h₁) (nd h₂)).mpr hm).trans (List.mergeSort_perm _ _).symm)

theorem merge_comm {u v : Tuple} (hu : u.attrs.Nodup) (hv : v.attrs.Nodup) (hc : Compat u v) :
    u.merge v = v.merge u := by
  rw [merge_eq, merge_eq]
  refine ofPairs_eq (mergeList_nodup hu hv) (mergeList_nodup hv hu) fun p => ?_
  rw [mem_mergeList hc, mem_mergeList hc.symm, Or.comm]

theorem compat_merge_left {u v w : Tuple} (hc : Compat u v) :
    Compat (u.merge v) w ↔ Compat u w ∧ Compat v w := by
  constructor
  · intro h
    exact ⟨fun a x y hx hy => h a x y ((mem_merge hc).mpr (Or.inl hx)) hy,
      fun a x y hx hy => h a x y ((mem_merge hc).mpr (Or.inr hx)) hy⟩
  · rintro ⟨h1, h2⟩ a x y hx hy
    cases (mem_merge hc).mp hx with
    | inl hx => exact h1 a x y hx hy
    | inr hx => exact h2 a x y hx hy

theorem compat_merge_right {u v w : Tuple} (hc : Compat v w) :
    Compat u (v.merge w) ↔ Compat u v ∧ Compat u w := by
  constructor
  · intro h; have := (compat_merge_left hc).mp h.symm; exact ⟨this.1.symm, this.2.symm⟩
  · rintro ⟨h1, h2⟩; exact ((compat_merge_left hc).mpr ⟨h1.symm, h2.symm⟩).symm

theorem merge_assoc {u v w : Tuple} (hu : u.attrs.Nodup) (hv : v.attrs.Nodup)
    (hw : w.attrs.Nodup) (huv : Compat u v) (huw : Compat u w) (hvw : Compat v w) :
    (u.merge v).merge w = u.merge (v.merge w) := by
  have h1 : Compat (u.merge v) w := (compat_merge_left huv).mpr ⟨huw, hvw⟩
  have h2 : Compat u (v.merge w) := (compat_merge_right hvw).mpr ⟨huv, huw⟩
  show Tuple.ofPairs (mergeList (u.merge v) w) = Tuple.ofPairs (mergeList u (v.merge w))
  refine ofPairs_eq (mergeList_nodup (merge_attrs_nodup hu hv) hw)
    (mergeList_nodup hu (merge_attrs_nodup hv hw)) fun p => ?_
  rw [mem_mergeList h1, mem_mergeList h2, mem_merge huv, mem_merge hvw, or_assoc]

/-! ## The laws -/

namespace Finrel

theorem join_heading {r s q : Finrel} (h : r.join s = .ok q) :
    joinHeading r.heading s.heading = .ok q.heading := by
  simp only [join, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i j hj
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hj

/-- Two finite relations with the same tuples have the same body. -/
theorem body_eq {q q' : Finrel} (h : ∀ t, t ∈ q.tuples ↔ t ∈ q'.tuples) : q.body = q'.body :=
  Body.ext h

/-- ⋈ is commutative: the same tuples, and the same attributes (in another order). -/
theorem join_comm {r s q q' : Finrel} (h : r.join s = .ok q) (h' : s.join r = .ok q')
    (hr : r.WF) (hs : s.WF) :
    q.body = q'.body ∧ ∀ a, a ∈ q.attrs ↔ a ∈ q'.attrs := by
  refine ⟨body_eq fun t => ?_, fun a => ?_⟩
  · rw [mem_join h, mem_join h']
    constructor
    · rintro ⟨u, hu, v, hv, ha, rfl⟩
      have fu := hr.fits u hu; have fv := hs.fits v hv
      have hc := (agrees_iff fv.nodup).mp ha
      exact ⟨v, hv, u, hu, (agrees_iff fu.nodup).mpr hc.symm, merge_comm fu.nodup fv.nodup hc⟩
    · rintro ⟨v, hv, u, hu, ha, rfl⟩
      have fu := hr.fits u hu; have fv := hs.fits v hv
      have hc := (agrees_iff fu.nodup).mp ha
      exact ⟨u, hu, v, hv, (agrees_iff fv.nodup).mpr hc.symm, merge_comm fv.nodup fu.nodup hc⟩
  · have e1 := (joinHeading_spec (join_heading h) hr.nodup hs.nodup).2.1 a
    have e2 := (joinHeading_spec (join_heading h') hs.nodup hr.nodup).2.1 a
    exact e1.trans (Or.comm.trans e2.symm)

/-- ⋈ is associative: `(R ⋈ S) ⋈ W` and `R ⋈ (S ⋈ W)` have the same tuples. -/
theorem join_assoc {r s w rs sw q q' : Finrel} (h₁ : r.join s = .ok rs) (h₂ : rs.join w = .ok q)
    (h₃ : s.join w = .ok sw) (h₄ : r.join sw = .ok q') (hr : r.WF) (hs : s.WF) (hw : w.WF) :
    q.body = q'.body := by
  have hrs := join_wf h₁ hr hs
  have hsw := join_wf h₃ hs hw
  refine body_eq fun t => ?_
  rw [mem_join h₂, mem_join h₄]
  constructor
  · rintro ⟨x, hx, c, hc, ha, rfl⟩
    obtain ⟨u, hu, v, hv, huv, rfl⟩ := (mem_join h₁ x).mp hx
    have fu := hr.fits u hu; have fv := hs.fits v hv; have fc := hw.fits c hc
    have cuv := (agrees_iff fv.nodup).mp huv
    obtain ⟨cuc, cvc⟩ := (compat_merge_left cuv).mp ((agrees_iff fc.nodup).mp ha)
    refine ⟨u, hu, v.merge c, (mem_join h₃ _).mpr ⟨v, hv, c, hc, (agrees_iff fc.nodup).mpr cvc, rfl⟩,
      (agrees_iff (merge_attrs_nodup fv.nodup fc.nodup)).mpr ((compat_merge_right cvc).mpr ⟨cuv, cuc⟩),
      merge_assoc fu.nodup fv.nodup fc.nodup cuv cuc cvc⟩
  · rintro ⟨u, hu, y, hy, ha, rfl⟩
    obtain ⟨v, hv, c, hc, hvc, rfl⟩ := (mem_join h₃ y).mp hy
    have fu := hr.fits u hu; have fv := hs.fits v hv; have fc := hw.fits c hc
    have cvc := (agrees_iff fc.nodup).mp hvc
    obtain ⟨cuv, cuc⟩ := (compat_merge_right cvc).mp
      ((agrees_iff (merge_attrs_nodup fv.nodup fc.nodup)).mp ha)
    refine ⟨u.merge v, (mem_join h₁ _).mpr ⟨u, hu, v, hv, (agrees_iff fv.nodup).mpr cuv, rfl⟩, c, hc,
      (agrees_iff fc.nodup).mpr ((compat_merge_left cuv).mpr ⟨cuc, cvc⟩),
      (merge_assoc fu.nodup fv.nodup fc.nodup cuv cuc cvc).symm⟩

/-- σ distributes over ∪. -/
theorem select_union {p : Tuple → Except String Bool} {r s q q₁ r₁ s₁ q₂ : Finrel}
    (h₁ : r.union s = .ok q) (h₂ : q.select p = .ok q₁) (h₃ : r.select p = .ok r₁)
    (h₄ : s.select p = .ok s₁) (h₅ : r₁.union s₁ = .ok q₂) : q₁.body = q₂.body := by
  refine body_eq fun t => ?_
  rw [mem_select h₂, mem_union h₁, mem_union h₅, mem_select h₃, mem_select h₄, or_and_right]

/-- σ moves into the operand of a join whose attributes it reads: `σ_p(R ⋈ S) = σ_p(R) ⋈ S`
when `p` gives the same answer on a merged tuple as on its `R` part. -/
theorem select_join {p : Tuple → Except String Bool} {r s q q₁ r₁ q₂ : Finrel}
    (h₁ : r.join s = .ok q) (h₂ : q.select p = .ok q₁) (h₃ : r.select p = .ok r₁)
    (h₄ : r₁.join s = .ok q₂)
    (hp : ∀ u ∈ r.tuples, ∀ v ∈ s.tuples, u.agrees v = true → p (u.merge v) = p u) :
    q₁.body = q₂.body := by
  refine body_eq fun t => ?_
  rw [mem_select h₂, mem_join h₁, mem_join h₄]
  constructor
  · rintro ⟨⟨u, hu, v, hv, ha, rfl⟩, hpt⟩
    exact ⟨u, (mem_select h₃ u).mpr ⟨hu, hp u hu v hv ha ▸ hpt⟩, v, hv, ha, rfl⟩
  · rintro ⟨u, hu, v, hv, ha, rfl⟩
    obtain ⟨hu, hpu⟩ := (mem_select h₃ u).mp hu
    exact ⟨⟨u, hu, v, hv, ha, rfl⟩, (hp u hu v hv ha).symm ▸ hpu⟩

end Finrel

end Rasso
