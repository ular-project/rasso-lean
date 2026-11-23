import Rasso.WF
import Rasso.Laws
import Rasso.FSpace

/-!
# Rasso: what a finite relation represents

`Rep H P r` says the finite relation `r` has heading `H` (up to the order of attributes) and
holds exactly the tuples that fit `H` and satisfy `P`. The lemmas here say how each operator
of the finite algebra acts on what its operands represent:

* σ adds a test, ∪ is "or", − is "and not", on one heading;
* ⋈ is "and" on the union of the headings;
* π is "there is an extension".

These are the steps of Codd's translation of first-order logic into the algebra, which
the ESO construction (`Rasso.ESO.ToProgram.compile`) uses.

Conventions:

* `P` is read on whole tuples. For the ESO construction `P` only looks at the values of
  the heading's attributes, which is what makes π and ⋈ work out.
-/

set_option linter.unusedSimpArgs false

namespace Rasso

open Finrel

/-- `r` has heading `H` (attribute by attribute) and holds the tuples that fit `H` and
satisfy `P`. -/
structure Rep (H : Heading) (P : Tuple → Prop) (r : Finrel) : Prop where
  wf : r.WF
  head : ∀ a, r.heading.lookup a = H.lookup a
  mem : ∀ t, t ∈ r.tuples ↔ t.Fits H ∧ P t

theorem attrs_congr {h k : Heading} (e : ∀ a, h.lookup a = k.lookup a) (a : String) :
    a ∈ h.attrs ↔ a ∈ k.attrs := by
  rw [Finrel.mem_attrs_iff, Finrel.mem_attrs_iff, e]

theorem Tuple.Fits.congr {h k : Heading} (e : ∀ a, h.lookup a = k.lookup a) {t : Tuple}
    (f : t.Fits h) : t.Fits k where
  sorted := f.sorted
  attrs a := (f.attrs a).trans (attrs_congr e a)
  dom p hp d hd := f.dom p hp d ((e p.1).trans hd)

theorem fits_congr {h k : Heading} (e : ∀ a, h.lookup a = k.lookup a) {t : Tuple} :
    t.Fits h ↔ t.Fits k :=
  ⟨Tuple.Fits.congr e, Tuple.Fits.congr fun a => (e a).symm⟩

/-- In a well-formed relation, membership of a tuple that fits. -/
theorem Rep.mem_fits {H : Heading} {P : Tuple → Prop} {r : Finrel} (hr : Rep H P r)
    {t : Tuple} (ht : t ∈ r.tuples) : t.Fits H :=
  ((hr.mem t).mp ht).1

/-! ## σ -/

theorem rep_select {H : Heading} {P : Tuple → Prop} {r s : Finrel} {p : Tuple → Except String Bool}
    (hr : Rep H P r) (hs : r.select p = .ok s) :
    Rep H (fun t => P t ∧ p t = .ok true) s where
  wf := select_wf hs hr.wf
  head a := by rw [Finrel.select_heading hs]; exact hr.head a
  mem t := by
    rw [Finrel.mem_select hs, hr.mem]
    exact ⟨fun ⟨⟨f, hp⟩, h⟩ => ⟨f, hp, h⟩, fun ⟨f, hp, h⟩ => ⟨⟨f, hp⟩, h⟩⟩

theorem select_succeeds {r : Finrel} {p : Tuple → Except String Bool}
    (h : ∀ t ∈ r.tuples, ∃ b, p t = .ok b) : ∃ s, r.select p = .ok s :=
  Finrel.select_ok.mpr h

/-! ## ∪ and − on one heading -/

theorem union_heading {r s q : Finrel} (h : r.union s = .ok q) : q.heading = r.heading := by
  simp only [union, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl

theorem diff_heading {r s q : Finrel} (h : r.diff s = .ok q) : q.heading = r.heading := by
  simp only [diff, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl

/-- Two lists of names with no repeats and the same members sort to the same list. -/
theorem mergeSort_eq_of_mem {l l' : List String} (hn : l.Nodup) (hn' : l'.Nodup)
    (h : ∀ a, a ∈ l ↔ a ∈ l') : l.mergeSort (· ≤ ·) = l'.mergeSort (· ≤ ·) := by
  have hp : l.Perm l' := (List.perm_ext_iff_of_nodup hn hn').mpr h
  have trans : ∀ (a b c : String), decide (a ≤ b) = true → decide (b ≤ c) = true → decide (a ≤ c) = true :=
    fun a b c h₁ h₂ => decide_eq_true (String.le_trans (of_decide_eq_true h₁) (of_decide_eq_true h₂))
  have total : ∀ (a b : String), (decide (a ≤ b) || decide (b ≤ a)) = true := fun a b => by
    rcases String.le_total a b with h | h <;> simp [h]
  apply List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b) = true)
  · exact fun a b _ _ h₁ h₂ => String.le_antisymm (of_decide_eq_true h₁) (of_decide_eq_true h₂)
  · exact List.pairwise_mergeSort trans total _
  · exact List.pairwise_mergeSort trans total _
  · exact ((List.mergeSort_perm _ _).trans hp).trans (List.mergeSort_perm _ _).symm

theorem sameHeading_of_rep {H : Heading} {P Q : Tuple → Prop} {r s : Finrel}
    (hr : Rep H P r) (hs : Rep H Q s) : SameHeading r s := by
  refine ⟨mergeSort_eq_of_mem hr.wf.nodup hs.wf.nodup fun a => ?_, fun p hp => ?_⟩
  · exact (attrs_congr hr.head a).trans (attrs_congr hs.head a).symm
  · show s.heading.lookup p.1 = some p.2
    rw [hs.head, ← hr.head]
    exact mem_lookup hr.wf.nodup hp

theorem rep_union {H : Heading} {P Q : Tuple → Prop} {r s : Finrel}
    (hr : Rep H P r) (hs : Rep H Q s) :
    ∃ q, r.union s = .ok q ∧ Rep H (fun t => P t ∨ Q t) q := by
  obtain ⟨q, hq⟩ := Finrel.union_ok.mpr (sameHeading_of_rep hr hs)
  refine ⟨q, hq, union_wf hq hr.wf hs.wf, fun a => ?_, fun t => ?_⟩
  · rw [union_heading hq]; exact hr.head a
  · rw [Finrel.mem_union hq, hr.mem, hs.mem]
    constructor
    · rintro (⟨f, h⟩ | ⟨f, h⟩)
      · exact ⟨f, Or.inl h⟩
      · exact ⟨f, Or.inr h⟩
    · rintro ⟨f, h | h⟩
      · exact Or.inl ⟨f, h⟩
      · exact Or.inr ⟨f, h⟩

theorem rep_diff {H : Heading} {P Q : Tuple → Prop} {r s : Finrel}
    (hr : Rep H P r) (hs : Rep H Q s) :
    ∃ q, r.diff s = .ok q ∧ Rep H (fun t => P t ∧ ¬ Q t) q := by
  obtain ⟨q, hq⟩ := Finrel.diff_ok.mpr (sameHeading_of_rep hr hs)
  refine ⟨q, hq, diff_wf hq hr.wf, fun a => ?_, fun t => ?_⟩
  · rw [diff_heading hq]; exact hr.head a
  · rw [Finrel.mem_diff hq, hr.mem, hs.mem]
    constructor
    · rintro ⟨⟨f, h⟩, hn⟩; exact ⟨f, h, fun hq => hn ⟨f, hq⟩⟩
    · rintro ⟨f, h, hn⟩; exact ⟨⟨f, h⟩, fun ⟨_, hq⟩ => hn hq⟩

/-! ## Restricting a tuple -/

theorem get?_restrict {as : List String} (a : String) :
    ∀ (t : Tuple), Tuple.get? (t.restrict as) a = if a ∈ as then Tuple.get? t a else none
  | [] => by simp [Tuple.restrict, Tuple.get?]
  | (b, v) :: t => by
    have ih := get?_restrict (as := as) a t
    simp only [Tuple.restrict, List.filter_cons] at ih ⊢
    by_cases hb : as.contains b = true
    · rw [ite_eq_left hb]
      by_cases hab : a = b
      · subst hab
        simp only [Tuple.get?, lookup_cons_self]
        rw [ite_eq_left (List.contains_iff_mem.mp hb)]
      · simp only [Tuple.get?] at ih ⊢
        rw [lookup_cons_ne hab, lookup_cons_ne hab, ih]
    · rw [ite_eq_right hb]
      by_cases hab : a = b
      · subst hab
        have hn : a ∉ as := fun h => hb (List.contains_iff_mem.mpr h)
        rw [ih, ite_eq_right hn, ite_eq_right hn]
      · simp only [Tuple.get?] at ih ⊢
        rw [lookup_cons_ne hab, ih]

theorem sorted_restrict {as : List String} {t : Tuple} (ht : Tuple.Sorted t) :
    Tuple.Sorted (t.restrict as) := ht.sublist List.filter_sublist

theorem mem_restrict {as : List String} {t : Tuple} {p : String × Value} :
    p ∈ t.restrict as ↔ p ∈ t ∧ p.1 ∈ as := by
  simp [Tuple.restrict, List.mem_filter]

/-- A tuple that fits `J` restricts to one that fits `H`, when every attribute of `H` is
in `J` with the same domain. -/
theorem Tuple.Fits.restrict {H J : Heading} {t : Tuple} (f : t.Fits J)
    (hsub : ∀ a d, H.lookup a = some d → J.lookup a = some d) : (t.restrict H.attrs).Fits H where
  sorted := sorted_restrict f.sorted
  attrs a := by
    constructor
    · intro ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact (mem_restrict.mp hp).2
    · intro ha
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp ha)
      have hj : a ∈ J.attrs := Finrel.mem_attrs_iff.mpr (by rw [hsub a d hd]; rfl)
      obtain ⟨p, hp, e⟩ := List.mem_map.mp ((f.attrs a).mpr hj)
      exact List.mem_map.mpr ⟨p, mem_restrict.mpr ⟨hp, e ▸ ha⟩, e⟩
  dom p hp d hd := f.dom p (mem_restrict.mp hp).1 d (hsub _ _ hd)

/-- The value of an attribute in a tuple that fits a heading is there exactly when the
attribute is. -/
theorem Tuple.Fits.get?_isSome {H : Heading} {t : Tuple} (f : t.Fits H) (a : String) :
    (Tuple.get? t a).isSome ↔ a ∈ H.attrs := by
  rw [← f.attrs a]
  exact Finrel.lookup_isSome

theorem Tuple.Fits.get?_none {H : Heading} {t : Tuple} (f : t.Fits H) {a : String}
    (ha : a ∉ H.attrs) : Tuple.get? t a = none := by
  cases h : Tuple.get? t a with
  | none => rfl
  | some v => exact absurd ((f.get?_isSome a).mp (by rw [h]; rfl)) ha

/-! ## ⋈ -/

/-- The heading of a join, attribute by attribute: the left's, else the right's. -/
def joinH (H K : Heading) : Heading := H ++ K.filter fun p => (H.lookup p.1).isNone

theorem lookup_filter_key {β : Type} {a : String} {c : String → Bool} (hc : c a = true) :
    ∀ (l : List (String × β)), (l.filter fun p => c p.1).lookup a = l.lookup a
  | [] => rfl
  | (b, x) :: l => by
    rw [List.filter_cons]
    by_cases hab : a = b
    · subst hab; simp [hc, List.lookup]
    · have hne : (a == b) = false := by simpa using hab
      split
      · simp only [List.lookup, hne]; exact lookup_filter_key hc l
      · simp only [List.lookup, hne]; exact lookup_filter_key hc l

theorem lookup_joinH (H K : Heading) (a : String) :
    (joinH H K).lookup a = (H.lookup a).or (K.lookup a) := by
  unfold joinH
  rw [List.lookup_append]
  cases h : H.lookup a with
  | some d => rfl
  | none => simp only [Option.none_or]; exact lookup_filter_key (c := fun b => (H.lookup b).isNone) (by simp [h]) K


theorem rep_join {H K : Heading} {P Q : Tuple → Prop} {r s : Finrel}
    (hr : Rep H P r) (hs : Rep K Q s)
    (hc : ∀ a d e, H.lookup a = some d → K.lookup a = some e → d = e) :
    ∃ q, r.join s = .ok q ∧
      Rep (joinH H K) (fun t => P (t.restrict H.attrs) ∧ Q (t.restrict K.attrs)) q := by
  -- the join is not refused: shared attributes have the same domain
  obtain ⟨j, hj⟩ : ∃ j, joinHeading r.heading s.heading = .ok j := by
    refine Finrel.joinHeading_ok.mpr fun p hp e he => ⟨p.2, ?_⟩
    have hd : H.lookup p.1 = some p.2 := by rw [← hr.head]; exact mem_lookup hr.wf.nodup hp
    rw [hs.head] at he
    rw [hc _ _ _ hd he]; simp [Domain.inter]
  obtain ⟨q, hq⟩ := Finrel.join_ok.mpr ⟨j, hj⟩
  have hqh := join_heading hq
  rw [hj] at hqh; cases hqh
  have hwf := join_wf hq hr.wf hs.wf
  -- the heading, attribute by attribute
  have hhead : ∀ a, q.heading.lookup a = (joinH H K).lookup a := by
    intro a
    obtain ⟨_, hjattrs, hjlook⟩ := joinHeading_spec hj hr.wf.nodup hs.wf.nodup
    rw [lookup_joinH, ← hr.head, ← hs.head]
    cases hl : q.heading.lookup a with
    | none =>
      have hn : a ∉ q.heading.attrs := fun h => by
        rw [Finrel.mem_attrs_iff, hl] at h; cases h
      rw [hjattrs] at hn
      have h1 : r.heading.lookup a = none := by
        cases h : r.heading.lookup a with
        | none => rfl
        | some _ => exact absurd (Finrel.mem_attrs_iff.mpr (by rw [h]; rfl)) (fun h' => hn (Or.inl h'))
      have h2 : s.heading.lookup a = none := by
        cases h : s.heading.lookup a with
        | none => rfl
        | some _ => exact absurd (Finrel.mem_attrs_iff.mpr (by rw [h]; rfl)) (fun h' => hn (Or.inr h'))
      rw [h1, h2]; rfl
    | some f =>
      rcases hjlook a f hl with ⟨d, hd, (⟨_, rfl⟩ | ⟨e, he, hi⟩)⟩ | ⟨hna, hk⟩
      · rw [mem_lookup hr.wf.nodup hd]; rfl
      · have hd' := mem_lookup hr.wf.nodup hd
        have := hc a d e (by rw [← hr.head]; exact hd') (by rw [← hs.head]; exact he)
        subst this
        simp [Domain.inter] at hi
        rw [hd', hi]; rfl
      · have : r.heading.lookup a = none := by
          cases h : r.heading.lookup a with
          | none => rfl
          | some _ => exact absurd (Finrel.mem_attrs_iff.mpr (by rw [h]; rfl)) hna
        rw [this, hk]; rfl
  refine ⟨q, hq, hwf, hhead, fun t => ?_⟩
  have subH : ∀ a d, H.lookup a = some d → (joinH H K).lookup a = some d := by
    intro a d h; rw [lookup_joinH, h]; rfl
  have subK : ∀ a e, K.lookup a = some e → (joinH H K).lookup a = some e := by
    intro a e h
    rw [lookup_joinH]
    cases h' : H.lookup a with
    | none => rw [h]; rfl
    | some d => rw [hc a d e h' h]; rfl
  rw [Finrel.mem_join hq]
  constructor
  · rintro ⟨u, hu, v, hv, ha, rfl⟩
    have fu := hr.mem_fits hu
    have fv := hs.mem_fits hv
    have ft : (u.merge v).Fits (joinH H K) := (hwf.fits _ ((Finrel.mem_join hq _).mpr ⟨u, hu, v, hv, ha, rfl⟩)).congr hhead
    have hm : ∀ a, Tuple.get? (u.merge v) a = (Tuple.get? u a).or (Tuple.get? v a) :=
      Tuple.get?_merge fu.sorted fv.sorted
    have eu : (u.merge v).restrict H.attrs = u := by
      refine Tuple.ext_get? (sorted_restrict ft.sorted) fu.sorted fun a => ?_
      rw [get?_restrict, hm]
      by_cases haH : a ∈ H.attrs
      · rw [ite_eq_left haH]
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((fu.get?_isSome a).mpr haH)
        rw [hx]; rfl
      · rw [ite_eq_right haH, fu.get?_none haH]
    have ev : (u.merge v).restrict K.attrs = v := by
      refine Tuple.ext_get? (sorted_restrict ft.sorted) fv.sorted fun a => ?_
      rw [get?_restrict, hm]
      by_cases haK : a ∈ K.attrs
      · rw [ite_eq_left haK]
        obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((fv.get?_isSome a).mpr haK)
        cases hx : Tuple.get? u a with
        | none => rfl
        | some x =>
          rw [hy]
          have := Finrel.agrees_eq ha (lookup_mem_val hx) hy
          rw [this]; rfl
      · rw [ite_eq_right haK, fv.get?_none haK]
    refine ⟨ft, ?_, ?_⟩
    · rw [eu]; exact ((hr.mem u).mp hu).2
    · rw [ev]; exact ((hs.mem v).mp hv).2
  · rintro ⟨ft, hP, hQ⟩
    refine ⟨t.restrict H.attrs, (hr.mem _).mpr ⟨ft.restrict subH, hP⟩,
      t.restrict K.attrs, (hs.mem _).mpr ⟨ft.restrict subK, hQ⟩, ?_, ?_⟩
    · have hvn : (t.restrict K.attrs).attrs.Nodup := (ft.restrict subK).nodup
      refine (agrees_iff hvn).mpr fun a x y hx hy => ?_
      have h1 := (mem_restrict.mp hx).1
      have h2 := (mem_restrict.mp hy).1
      have e1 := mem_lookup ft.nodup h1
      have e2 := mem_lookup ft.nodup h2
      rw [e1] at e2; cases e2; rfl
    · have fu := ft.restrict subH
      have fv := ft.restrict subK
      have hL : (((t.restrict H.attrs) ++ (t.restrict K.attrs).filter fun p =>
          (Tuple.get? (t.restrict H.attrs) p.1).isNone).map (fun p : String × Value => p.1)).Nodup := by
        have h0 := merge_attrs_nodup fu.nodup fv.nodup
        unfold Tuple.merge Tuple.ofPairs Tuple.attrs at h0
        exact ((List.mergeSort_perm _ _).map (fun p : String × Value => p.1)).nodup_iff.mp h0
      refine (Tuple.ext_get? ft.sorted (Tuple.sorted_ofPairs hL) fun a => ?_)
      · rw [Tuple.get?_merge fu.sorted fv.sorted, get?_restrict, get?_restrict]
        by_cases haH : a ∈ H.attrs
        · rw [ite_eq_left haH]
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((ft.get?_isSome a).mpr
            (Finrel.mem_attrs_iff.mpr (by obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp haH); rw [subH a d hd]; rfl)))
          rw [hx]; rfl
        · rw [ite_eq_right haH, Option.none_or]
          by_cases haK : a ∈ K.attrs
          · rw [ite_eq_left haK]
          · rw [ite_eq_right haK]
            refine ft.get?_none fun hj' => ?_
            rw [Finrel.mem_attrs_iff, lookup_joinH] at hj'
            have h1 : H.lookup a = none := by
              cases h : H.lookup a with
              | none => rfl
              | some _ => exact absurd (Finrel.mem_attrs_iff.mpr (by rw [h]; rfl)) haH
            have h2 : K.lookup a = none := by
              cases h : K.lookup a with
              | none => rfl
              | some _ => exact absurd (Finrel.mem_attrs_iff.mpr (by rw [h]; rfl)) haK
            rw [h1, h2] at hj'; cases hj'


/-! ## π -/

theorem lookup_filter_key_false {β : Type} {a : String} {c : String → Bool} (hc : c a = false) :
    ∀ (l : List (String × β)), (l.filter fun p => c p.1).lookup a = none
  | [] => rfl
  | (b, x) :: l => by
    rw [List.filter_cons]
    by_cases hab : a = b
    · subst hab; simp only [hc]; exact lookup_filter_key_false hc l
    · have hne : (a == b) = false := by simpa using hab
      split
      · simp only [List.lookup, hne]; exact lookup_filter_key_false hc l
      · exact lookup_filter_key_false hc l

/-- The part of a heading on some attributes. -/
def restrictH (H : Heading) (as : List String) : Heading := H.filter fun p => as.contains p.1

theorem lookup_restrictH (H : Heading) (as : List String) (a : String) :
    (restrictH H as).lookup a = if a ∈ as then H.lookup a else none := by
  unfold restrictH
  by_cases ha : a ∈ as
  · rw [ite_eq_left ha]; exact lookup_filter_key (c := fun b => as.contains b) (List.contains_iff_mem.mpr ha) H
  · rw [ite_eq_right ha]
    exact lookup_filter_key_false (c := fun b => as.contains b) (by simpa using ha) H

theorem restrict_eq_of_fits {H : Heading} {as : List String} {u : Tuple} (fu : u.Fits H) :
    u.restrict as = u.restrict (restrictH H as).attrs := by
  unfold Tuple.restrict
  apply List.filter_congr
  intro p hp
  have hpH : p.1 ∈ H.attrs := (fu.attrs p.1).mp (List.mem_map_of_mem hp)
  have key : p.1 ∈ as ↔ p.1 ∈ (restrictH H as).attrs := by
    rw [Finrel.mem_attrs_iff, lookup_restrictH]
    by_cases ha : p.1 ∈ as
    · rw [ite_eq_left ha]; exact ⟨fun _ => Finrel.mem_attrs_iff.mp hpH, fun _ => ha⟩
    · rw [ite_eq_right ha]; simp [ha]
  by_cases h : p.1 ∈ as
  · rw [List.contains_iff_mem.mpr h, List.contains_iff_mem.mpr (key.mp h)]
  · have h' : p.1 ∉ (restrictH H as).attrs := fun h' => h (key.mpr h')
    rw [show as.contains p.1 = false by simpa using h,
        show (restrictH H as).attrs.contains p.1 = false by simpa using h']

theorem rep_project {H : Heading} {P : Tuple → Prop} {r : Finrel} {as : List String}
    (hr : Rep H P r) (has : ∀ a ∈ as, a ∈ H.attrs) (hn : as.Nodup) :
    ∃ s, r.project as = .ok s ∧
      Rep (restrictH H as) (fun t => ∃ u, u.Fits H ∧ P u ∧ u.restrict as = t) s := by
  obtain ⟨s, hs⟩ := Finrel.project_ok.mpr ⟨fun a ha => (attrs_congr hr.head a).mpr (has a ha), hn⟩
  have hattrs := Finrel.project_heading hs
  obtain ⟨hlook, _⟩ := project_spec hs
  have hhead : ∀ a, s.heading.lookup a = (restrictH H as).lookup a := by
    intro a
    rw [lookup_restrictH]
    by_cases ha : a ∈ as
    · rw [ite_eq_left ha]
      rw [← hattrs] at ha
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp ha)
      rw [hd, ← hr.head, hlook a d hd]
    · rw [ite_eq_right ha]
      cases h : s.heading.lookup a with
      | none => rfl
      | some _ => exact absurd (hattrs ▸ Finrel.mem_attrs_iff.mpr (by rw [h]; rfl)) ha
  have sub : ∀ a d, (restrictH H as).lookup a = some d → H.lookup a = some d := by
    intro a d h
    rw [lookup_restrictH] at h
    split at h
    · exact h
    · cases h
  refine ⟨s, hs, project_wf hs hr.wf, hhead, fun t => ?_⟩
  rw [Finrel.mem_project hs]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have fu := hr.mem_fits hu
    refine ⟨?_, u, fu, ((hr.mem u).mp hu).2, rfl⟩
    rw [restrict_eq_of_fits fu]
    exact fu.restrict sub
  · rintro ⟨_, u, fu, hP, rfl⟩
    exact ⟨u, (hr.mem u).mpr ⟨fu, hP⟩, rfl⟩

end Rasso
