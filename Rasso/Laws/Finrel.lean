import Rasso.Laws
import Rasso.Rep
import Rasso.Unrel

/-!
# Rasso: the laws of finite relations

The laws of the finite algebra, stated and proved for Rasso's own finite relations. The
table of rows, with each status, is in the laws appendix of the Rasso blueprint.

How a law is stated:

* **When both sides succeed.** Each operator can refuse, so a law takes the success of every
  operation on both sides as a hypothesis, and says the two results have the same **body**
  (Lean equality: a body is a quotient) and equivalent headings.
* **Definedness** is a separate theorem, where it holds: both sides refuse together. Where it
  does not hold, `Rasso/Laws/FinrelExamples.lean` has an example of one side refusing alone.
* **Well-formedness** (`Finrel.WF`) is a hypothesis where a law needs tuples to fit the
  heading, or the heading to name no attribute twice.

Conventions:

* "Equivalent headings" for ∪, ∩ and − is `SameHeading`, the operators' own check, which these
  operators require of their operands anyway. For ⋈ it is: the same attributes, and for each
  attribute two domains with the same members (`join_comm_heading`). Whether `Domain.inter` is
  commutative as data (not only as a set) is not proved here.
-/

namespace Rasso
namespace FinrelLaws

open Rasso.Finrel

/-! ## The constants -/

/-- DEE: no attributes, one tuple (the empty tuple). -/
def dee : Rasso.Finrel := Rasso.Finrel.ofTuples [] [[]]

/-- DUM: no attributes, no tuple. -/
def dum : Rasso.Finrel := Rasso.Finrel.ofTuples [] []

/-- The empty relation over a heading. -/
def empty (h : Heading) : Rasso.Finrel := Rasso.Finrel.ofTuples h []

@[simp] theorem mem_dee {t : Tuple} : t ∈ dee.tuples ↔ t = [] := by
  simp [dee]

@[simp] theorem not_mem_dum {t : Tuple} : t ∉ dum.tuples := by
  simp [dum]

@[simp] theorem not_mem_empty {h : Heading} {t : Tuple} : t ∉ (empty h).tuples := by
  simp [empty]

@[simp] theorem empty_heading {h : Heading} : (empty h).heading = h := rfl

/-! ## The heading check of ∪, ∩, − -/

theorem SameHeading.attrs_iff {r s : Rasso.Finrel} (h : SameHeading r s) (a : String) :
    a ∈ r.attrs ↔ a ∈ s.attrs := by
  have := congrArg (a ∈ ·) h.1
  simp only [List.mem_mergeSort] at this
  exact propext_iff.mp this

theorem SameHeading.trans {r s u : Rasso.Finrel} (h₁ : SameHeading r s)
    (h₂ : SameHeading s u) : SameHeading r u :=
  ⟨h₁.1.trans h₂.1, fun p hp => h₂.2 _ (lookup_mem (h₁.2 p hp))⟩


/-- The check reads only the headings. -/
theorem SameHeading.of_heading {r s r' s' : Rasso.Finrel} (e : r'.heading = r.heading)
    (e' : s'.heading = s.heading) (h : SameHeading r s) : SameHeading r' s' := by
  unfold SameHeading Rasso.Finrel.attrs Rasso.Finrel.domainOf? at *
  rw [e, e']; exact h

/-- With no attribute named twice, the check is reflexive. -/
theorem SameHeading.refl {r : Rasso.Finrel} (hn : r.heading.attrs.Nodup) : SameHeading r r :=
  ⟨rfl, fun _ hp => mem_lookup hn hp⟩

/-- With no attribute named twice on the right, the check is symmetric. -/
theorem SameHeading.symm {r s : Rasso.Finrel} (hs : s.heading.attrs.Nodup)
    (h : SameHeading r s) : SameHeading s r := by
  refine ⟨h.1.symm, fun ⟨a, d⟩ hp => ?_⟩
  -- `a` is an attribute of `r`; its domain in `r` is its domain in `s`
  have ha : a ∈ r.attrs := (SameHeading.attrs_iff h a).mpr (List.mem_map_of_mem (f := (·.1)) hp)
  obtain ⟨e, he⟩ : ∃ e, r.heading.lookup a = some e := by
    exact Option.isSome_iff_exists.mp (lookup_isSome_iff_mem ha)
  have h1 := h.2 _ (lookup_mem he)
  have h2 := mem_lookup hs hp
  simp only [domainOf?] at h1 ⊢
  rw [h1] at h2; cases h2; exact he


/-! ## ∪ -/

theorem union_comm {r s q q' : Rasso.Finrel} (h : r.union s = .ok q) (h' : s.union r = .ok q') :
    q.body = q'.body := body_eq fun t => by rw [mem_union h, mem_union h', Or.comm]

theorem union_assoc {r s u rs su q q' : Rasso.Finrel} (h₁ : r.union s = .ok rs)
    (h₂ : rs.union u = .ok q) (h₃ : s.union u = .ok su) (h₄ : r.union su = .ok q') :
    q.body = q'.body := body_eq fun t => by
  rw [mem_union h₂, mem_union h₁, mem_union h₄, mem_union h₃, or_assoc]

theorem union_idem {r q : Rasso.Finrel} (h : r.union r = .ok q) : q.body = r.body := by
  have e : q.body = (Rasso.Finrel.ofTuples r.heading r.tuples).body :=
    body_eq fun t => by rw [mem_union h, or_self, mem_ofTuples]
  rw [e]; exact Body.ofList_toList r.body

theorem union_empty {r q : Rasso.Finrel} (h : r.union (empty r.heading) = .ok q) :
    q.body = r.body := by
  have e : q.body = (Rasso.Finrel.ofTuples r.heading r.tuples).body :=
    body_eq fun t => by simp [mem_union h]
  rw [e]; exact Body.ofList_toList r.body

/-- The heading of ∪ is its left operand's; both orders pass the same check. -/
theorem union_comm_heading {r s q q' : Rasso.Finrel}
    (h : r.union s = .ok q) (h' : s.union r = .ok q') : SameHeading q q' :=
  SameHeading.of_heading (union_heading h) (union_heading h') (union_ok.mp ⟨_, h⟩)

/-- Definedness: with no attribute named twice, `r ∪ s` and `s ∪ r` refuse together. -/
theorem union_comm_ok {r s : Rasso.Finrel} (hr : r.heading.attrs.Nodup)
    (hs : s.heading.attrs.Nodup) :
    (∃ q, r.union s = .ok q) ↔ (∃ q, s.union r = .ok q) := by
  rw [union_ok, union_ok]; exact ⟨SameHeading.symm hs, SameHeading.symm hr⟩

/-! ## ∩ -/

theorem inter_comm {r s q q' : Rasso.Finrel} (h : r.inter s = .ok q) (h' : s.inter r = .ok q') :
    q.body = q'.body := body_eq fun t => by rw [mem_inter h, mem_inter h', And.comm]

theorem inter_assoc {r s u rs su q q' : Rasso.Finrel} (h₁ : r.inter s = .ok rs)
    (h₂ : rs.inter u = .ok q) (h₃ : s.inter u = .ok su) (h₄ : r.inter su = .ok q') :
    q.body = q'.body := body_eq fun t => by
  rw [mem_inter h₂, mem_inter h₁, mem_inter h₄, mem_inter h₃, and_assoc]

theorem inter_idem {r q : Rasso.Finrel} (h : r.inter r = .ok q) : q.body = r.body := by
  have e : q.body = (Rasso.Finrel.ofTuples r.heading r.tuples).body :=
    body_eq fun t => by rw [mem_inter h, and_self, mem_ofTuples]
  rw [e]; exact Body.ofList_toList r.body

/-- ∩ is r − (r − s). -/
theorem inter_eq_diff_diff {r s d q q' : Rasso.Finrel} (h₁ : r.diff s = .ok d)
    (h₂ : r.diff d = .ok q) (h : r.inter s = .ok q') : q.body = q'.body := body_eq fun t => by
  rw [mem_diff h₂, mem_diff h₁, mem_inter h]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, Classical.byContradiction fun h3 => h2 ⟨h1, h3⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun ⟨_, h3⟩ => h3 h2⟩

theorem union_inter_absorb {r s i q : Rasso.Finrel} (h₁ : r.inter s = .ok i)
    (h₂ : r.union i = .ok q) : q.body = r.body := by
  have e : q.body = (Rasso.Finrel.ofTuples r.heading r.tuples).body :=
    body_eq fun t => by
      rw [mem_union h₂, mem_inter h₁, mem_ofTuples]
      exact ⟨fun h => h.elim id (·.1), Or.inl⟩
  rw [e]; exact Body.ofList_toList r.body

theorem inter_union_absorb {r s u q : Rasso.Finrel} (h₁ : r.union s = .ok u)
    (h₂ : r.inter u = .ok q) : q.body = r.body := by
  have e : q.body = (Rasso.Finrel.ofTuples r.heading r.tuples).body :=
    body_eq fun t => by
      rw [mem_inter h₂, mem_union h₁, mem_ofTuples]
      exact ⟨(·.1), fun h => ⟨h, Or.inl h⟩⟩
  rw [e]; exact Body.ofList_toList r.body

theorem union_inter_distrib {r s u su rs ru q q' : Rasso.Finrel} (h₁ : s.inter u = .ok su)
    (h₂ : r.union su = .ok q) (h₃ : r.union s = .ok rs) (h₄ : r.union u = .ok ru)
    (h₅ : rs.inter ru = .ok q') : q.body = q'.body := body_eq fun t => by
  rw [mem_union h₂, mem_inter h₁, mem_inter h₅, mem_union h₃, mem_union h₄, or_and_left]

theorem inter_union_distrib {r s u su rs ru q q' : Rasso.Finrel} (h₁ : s.union u = .ok su)
    (h₂ : r.inter su = .ok q) (h₃ : r.inter s = .ok rs) (h₄ : r.inter u = .ok ru)
    (h₅ : rs.union ru = .ok q') : q.body = q'.body := body_eq fun t => by
  rw [mem_inter h₂, mem_union h₁, mem_union h₅, mem_inter h₃, mem_inter h₄, and_or_left]

/-! ## − -/

theorem diff_self {r q : Rasso.Finrel} (h : r.diff r = .ok q) : q.body = (empty r.heading).body :=
  body_eq fun t => by simp [mem_diff h]

theorem diff_empty {r q : Rasso.Finrel} (h : r.diff (empty r.heading) = .ok q) :
    q.body = r.body := by
  have e : q.body = (Rasso.Finrel.ofTuples r.heading r.tuples).body :=
    body_eq fun t => by simp [mem_diff h]
  rw [e]; exact Body.ofList_toList r.body

theorem empty_diff {h : Heading} {r q : Rasso.Finrel} (hq : (empty h).diff r = .ok q) :
    q.body = (empty h).body := body_eq fun t => by simp [mem_diff hq]

/-- De Morgan: r − (s ∪ u) = (r − s) − u. -/
theorem diff_union {r s u su rs q q' : Rasso.Finrel} (h₁ : s.union u = .ok su)
    (h₂ : r.diff su = .ok q) (h₃ : r.diff s = .ok rs) (h₄ : rs.diff u = .ok q') :
    q.body = q'.body := body_eq fun t => by
  rw [mem_diff h₂, mem_union h₁, mem_diff h₄, mem_diff h₃, not_or, and_assoc]

/-- (r ∪ s) − u = (r − u) ∪ (s − u). -/
theorem union_diff {r s u rs ru su q q' : Rasso.Finrel} (h₁ : r.union s = .ok rs)
    (h₂ : rs.diff u = .ok q) (h₃ : r.diff u = .ok ru) (h₄ : s.diff u = .ok su)
    (h₅ : ru.union su = .ok q') : q.body = q'.body := body_eq fun t => by
  rw [mem_diff h₂, mem_union h₁, mem_union h₅, mem_diff h₃, mem_diff h₄, or_and_right]

/-! ## Tuples: what ⋈ needs -/

/-- Sorting a tuple that is already sorted changes nothing. -/
theorem ofPairs_self {u : Tuple} (hs : u.Pairwise fun p q => p.1 < q.1) : Tuple.ofPairs u = u :=
  List.mergeSort_of_pairwise (hs.imp fun h => by
    simp only [decide_eq_true_eq]
    exact (String.le_total _ _).resolve_right fun h' => String.not_le.mpr h h')

/-- Two sorted tuples with the same attributes that agree are equal. -/
theorem eq_of_compat {u v : Tuple} (hu : u.Pairwise fun p q => p.1 < q.1)
    (hv : v.Pairwise fun p q => p.1 < q.1) (hnu : u.attrs.Nodup) (hnv : v.attrs.Nodup)
    (ha : ∀ a, a ∈ u.attrs ↔ a ∈ v.attrs) (hc : Compat u v) : u = v := by
  rw [← ofPairs_self hu, ← ofPairs_self hv]
  refine ofPairs_eq hnu hnv fun ⟨a, x⟩ => ⟨fun hx => ?_, fun hy => ?_⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp
      (lookup_isSome_iff_mem ((ha a).mp (List.mem_map_of_mem (f := (·.1)) hx)))
    have := hc a x y hx (lookup_mem hy); subst this; exact lookup_mem hy
  · obtain ⟨y, hx⟩ := Option.isSome_iff_exists.mp
      (lookup_isSome_iff_mem ((ha a).mpr (List.mem_map_of_mem (f := (·.1)) hy)))
    have := hc a y x (lookup_mem hx) hy; subst this; exact lookup_mem hx

theorem compat_self (u : Tuple) (hn : u.attrs.Nodup) : Compat u u := fun a x y hx hy =>
  by have h1 := mem_lookup hn hx; have h2 := mem_lookup hn hy; rw [h1] at h2; cases h2; rfl

theorem compat_nil (u : Tuple) : Compat u [] := fun _ _ _ _ hy => by cases hy

theorem merge_self {u : Tuple} (hs : u.Pairwise fun p q => p.1 < q.1) :
    u.merge u = u := by
  rw [merge_eq, mergeList]
  have : u.filter (fun p => (u.get? p.1).isNone) = [] := by
    refine List.filter_eq_nil_iff.mpr fun p hp => ?_
    have hs' : (u.get? p.1).isSome = true :=
      lookup_isSome_iff_mem (List.mem_map_of_mem (f := (·.1)) hp)
    cases hg : u.get? p.1 with
    | none => rw [hg] at hs'; cases hs'
    | some _ => simp
  rw [this, List.append_nil, ofPairs_self hs]

theorem merge_nil {u : Tuple} (hs : u.Pairwise fun p q => p.1 < q.1) : u.merge [] = u := by
  rw [merge_eq, mergeList]; simp only [List.filter_nil, List.append_nil]; exact ofPairs_self hs

theorem nil_merge {v : Tuple} (hs : v.Pairwise fun p q => p.1 < q.1) : Tuple.merge [] v = v := by
  rw [merge_eq, mergeList]
  have : v.filter (fun p => (Tuple.get? [] p.1).isNone) = v :=
    List.filter_eq_self.mpr fun _ _ => rfl
  rw [List.nil_append, this, ofPairs_self hs]

theorem agrees_nil (u : Tuple) : u.agrees [] = true :=
  List.all_eq_true.mpr fun _ _ => by simp [Tuple.get?]

theorem nil_agrees (v : Tuple) : Tuple.agrees [] v = true := rfl

/-! ## ⋈ -/

theorem join_idem {r q : Rasso.Finrel} (hr : r.WF) (h : r.join r = .ok q) : q.body = r.body := by
  have e : q.body = (Rasso.Finrel.ofTuples r.heading r.tuples).body := body_eq fun t => by
    rw [mem_join h, mem_ofTuples]
    constructor
    · rintro ⟨u, hu, v, hv, ha, rfl⟩
      have fu := hr.fits u hu; have fv := hr.fits v hv
      have : u = v := eq_of_compat fu.sorted fv.sorted fu.nodup fv.nodup
        (fun a => (fu.attrs a).trans (fv.attrs a).symm) ((agrees_iff fv.nodup).mp ha)
      subst this; rw [merge_self fu.sorted]; exact hu
    · intro ht
      have ft := hr.fits t ht
      exact ⟨t, ht, t, ht, (agrees_iff ft.nodup).mpr (compat_self t ft.nodup),
        (merge_self ft.sorted).symm⟩
  rw [e]; exact Body.ofList_toList r.body

/-- DEE is a right identity of ⋈. -/
theorem join_dee {r q : Rasso.Finrel} (hr : r.WF) (h : r.join dee = .ok q) : q.body = r.body := by
  have e : q.body = (Rasso.Finrel.ofTuples r.heading r.tuples).body := body_eq fun t => by
    rw [mem_join h, mem_ofTuples]
    constructor
    · rintro ⟨u, hu, v, hv, _, rfl⟩
      rw [mem_dee.mp hv, merge_nil (hr.fits u hu).sorted]; exact hu
    · intro ht
      exact ⟨t, ht, [], mem_dee.mpr rfl, agrees_nil t, (merge_nil (hr.fits t ht).sorted).symm⟩
  rw [e]; exact Body.ofList_toList r.body

/-- DEE is a left identity of ⋈. -/
theorem dee_join {r q : Rasso.Finrel} (hr : r.WF) (h : dee.join r = .ok q) : q.body = r.body := by
  have e : q.body = (Rasso.Finrel.ofTuples r.heading r.tuples).body := body_eq fun t => by
    rw [mem_join h, mem_ofTuples]
    constructor
    · rintro ⟨u, hu, v, hv, _, rfl⟩
      rw [mem_dee.mp hu, nil_merge (hr.fits v hv).sorted]; exact hv
    · intro ht
      exact ⟨[], mem_dee.mpr rfl, t, ht, nil_agrees t, (nil_merge (hr.fits t ht).sorted).symm⟩
  rw [e]; exact Body.ofList_toList r.body

/-- ⋈ with an empty relation, on either side and over any headings, is empty. -/
theorem join_empty_right {r s q : Rasso.Finrel} (hs : s.tuples = []) (h : r.join s = .ok q) :
    q.tuples = [] := List.eq_nil_iff_forall_not_mem.mpr fun t ht => by
  obtain ⟨_, _, v, hv, _⟩ := (mem_join h t).mp ht; rw [hs] at hv; cases hv

theorem join_empty_left {r s q : Rasso.Finrel} (hr : r.tuples = []) (h : r.join s = .ok q) :
    q.tuples = [] := List.eq_nil_iff_forall_not_mem.mpr fun t ht => by
  obtain ⟨u, hu, _⟩ := (mem_join h t).mp ht; rw [hr] at hu; cases hu

theorem join_dum {r q : Rasso.Finrel} (h : r.join dum = .ok q) : q.tuples = [] :=
  join_empty_right (List.eq_nil_iff_forall_not_mem.mpr fun _ => not_mem_dum) h

theorem dum_join {r q : Rasso.Finrel} (h : dum.join r = .ok q) : q.tuples = [] :=
  join_empty_left (List.eq_nil_iff_forall_not_mem.mpr fun _ => not_mem_dum) h

/-- ⋈ distributes over ∪. -/
theorem join_union {r s u su rs ru q q' : Rasso.Finrel} (h₁ : s.union u = .ok su)
    (h₂ : r.join su = .ok q) (h₃ : r.join s = .ok rs) (h₄ : r.join u = .ok ru)
    (h₅ : rs.union ru = .ok q') : q.body = q'.body := body_eq fun t => by
  rw [mem_join h₂, mem_union h₅, mem_join h₃, mem_join h₄]
  constructor
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    cases (mem_union h₁ b).mp hb with
    | inl hb => exact Or.inl ⟨a, ha, b, hb, hab, rfl⟩
    | inr hb => exact Or.inr ⟨a, ha, b, hb, hab, rfl⟩
  · rintro (⟨a, ha, b, hb, hab, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
    · exact ⟨a, ha, b, (mem_union h₁ b).mpr (Or.inl hb), hab, rfl⟩
    · exact ⟨a, ha, b, (mem_union h₁ b).mpr (Or.inr hb), hab, rfl⟩

/-- On one heading, ⋈ is ∩. -/
theorem join_same_heading {r s q q' : Rasso.Finrel} (hr : r.WF) (hs : s.WF)
    (hh : SameHeading r s) (h : r.join s = .ok q) (h' : r.inter s = .ok q') :
    q.body = q'.body := body_eq fun t => by
  rw [mem_join h, mem_inter h']
  constructor
  · rintro ⟨u, hu, v, hv, ha, rfl⟩
    have fu := hr.fits u hu; have fv := hs.fits v hv
    have : u = v := eq_of_compat fu.sorted fv.sorted fu.nodup fv.nodup
      (fun a => (fu.attrs a).trans ((SameHeading.attrs_iff hh a).trans (fv.attrs a).symm))
      ((agrees_iff fv.nodup).mp ha)
    subst this; rw [merge_self fu.sorted]; exact ⟨hu, hv⟩
  · rintro ⟨hu, hv⟩
    have ft := hr.fits t hu
    exact ⟨t, hu, t, hv, (agrees_iff ft.nodup).mpr (compat_self t ft.nodup),
      (merge_self ft.sorted).symm⟩

/-! ## σ -/

/-- Two tests, the first then the second: refused if the first refuses, false if the first
is false, else the second. -/
def andThen (q p : Tuple → Except String Bool) (t : Tuple) : Except String Bool := do
  if ← q t then p t else pure false

theorem andThen_true {q p : Tuple → Except String Bool} {t : Tuple} :
    andThen q p t = .ok true ↔ q t = .ok true ∧ p t = .ok true := by
  unfold andThen
  cases hq : q t with
  | error e => simp [bind, Except.bind]
  | ok b => cases b <;> simp [bind, Except.bind, pure, Except.pure]

theorem select_comm {p q : Tuple → Except String Bool} {r rq rp s s' : Rasso.Finrel}
    (h₁ : r.select q = .ok rq) (h₂ : rq.select p = .ok s) (h₃ : r.select p = .ok rp)
    (h₄ : rp.select q = .ok s') : s.body = s'.body := body_eq fun t => by
  rw [mem_select h₂, mem_select h₁, mem_select h₄, mem_select h₃, and_assoc, and_assoc,
    and_comm (a := q t = .ok true)]

theorem select_idem {p : Tuple → Except String Bool} {r rp s : Rasso.Finrel}
    (h₁ : r.select p = .ok rp) (h₂ : rp.select p = .ok s) : s = rp := by
  have hb : s.body = rp.body := by
    have e : s.body = (Rasso.Finrel.ofTuples rp.heading rp.tuples).body := body_eq fun t => by
      rw [mem_select h₂, mem_ofTuples, mem_select h₁, and_assoc, and_self]
    rw [e]; exact Body.ofList_toList rp.body
  cases s; cases rp
  simp only [Rasso.Finrel.mk.injEq]
  exact ⟨select_heading h₂, hb⟩

/-- Definedness: σ_p σ_p r is refused exactly when σ_p r is. -/
theorem select_idem_ok {p : Tuple → Except String Bool} {r rp : Rasso.Finrel}
    (h₁ : r.select p = .ok rp) : ∃ s, rp.select p = .ok s :=
  select_ok.mpr fun t ht => ⟨true, ((mem_select h₁ t).mp ht).2⟩

theorem select_cascade {p q : Tuple → Except String Bool} {r rq s s' : Rasso.Finrel}
    (h₁ : r.select q = .ok rq) (h₂ : rq.select p = .ok s) (h₃ : r.select (andThen q p) = .ok s') :
    s.body = s'.body := body_eq fun t => by
  rw [mem_select h₂, mem_select h₁, mem_select h₃, andThen_true, and_assoc]

theorem select_diff {p : Tuple → Except String Bool} {r u d s rp s' : Rasso.Finrel}
    (h₁ : r.diff u = .ok d) (h₂ : d.select p = .ok s) (h₃ : r.select p = .ok rp)
    (h₄ : rp.diff u = .ok s') : s.body = s'.body := body_eq fun t => by
  rw [mem_select h₂, mem_diff h₁, mem_diff h₄, mem_select h₃, and_assoc, and_assoc,
    and_comm (a := t ∉ u.tuples)]

theorem select_inter {p : Tuple → Except String Bool} {r u i s rp s' : Rasso.Finrel}
    (h₁ : r.inter u = .ok i) (h₂ : i.select p = .ok s) (h₃ : r.select p = .ok rp)
    (h₄ : rp.inter u = .ok s') : s.body = s'.body := body_eq fun t => by
  rw [mem_select h₂, mem_inter h₁, mem_inter h₄, mem_select h₃, and_assoc, and_assoc,
    and_comm (a := t ∈ u.tuples)]

theorem select_true {r s : Rasso.Finrel} (h : r.select (fun _ => .ok true) = .ok s) :
    s.body = r.body := by
  have e : s.body = (Rasso.Finrel.ofTuples r.heading r.tuples).body :=
    body_eq fun t => by rw [mem_select h, mem_ofTuples]; simp
  rw [e]; exact Body.ofList_toList r.body

theorem select_false {r s : Rasso.Finrel} (h : r.select (fun _ => .ok false) = .ok s) :
    s.tuples = [] := List.eq_nil_iff_forall_not_mem.mpr fun t ht => by
  have := ((mem_select h t).mp ht).2; cases this

/-- A constant test never refuses. -/
theorem select_const_ok (b : Bool) (r : Rasso.Finrel) : ∃ s, r.select (fun _ => .ok b) = .ok s :=
  select_ok.mpr fun _ _ => ⟨b, rfl⟩

/-! ## π -/

theorem nodup_of_sorted {u : Tuple} (hs : u.Pairwise fun p q => p.1 < q.1) :
    (u.map (·.1)).Nodup :=
  List.nodup_iff_pairwise_ne.mpr (List.pairwise_map.mpr
    (hs.imp fun {a b} (hlt : a.1 < b.1) (e : a.1 = b.1) => String.lt_irrefl b.1 (e ▸ hlt)))

/-- Two sorted tuples with the same pairs are equal. -/
theorem eq_of_mem_iff {u v : Tuple} (hu : u.Pairwise fun p q => p.1 < q.1)
    (hv : v.Pairwise fun p q => p.1 < q.1) (hm : ∀ p, p ∈ u ↔ p ∈ v) : u = v := by
  rw [← ofPairs_self hu, ← ofPairs_self hv]
  exact ofPairs_eq (nodup_of_sorted hu) (nodup_of_sorted hv) hm

theorem restrict_sorted {u : Tuple} (hs : u.Pairwise fun p q => p.1 < q.1) (as : List String) :
    (u.restrict as).Pairwise fun p q => p.1 < q.1 := hs.sublist List.filter_sublist

theorem mem_restrict {u : Tuple} {as : List String} {p : String × Value} :
    p ∈ u.restrict as ↔ p ∈ u ∧ p.1 ∈ as := by
  simp [Tuple.restrict, List.mem_filter]

/-- π onto all the attributes, in the heading's order, changes nothing. -/
theorem project_self {r s : Rasso.Finrel} (hr : r.WF) (h : r.project r.attrs = .ok s) :
    s.body = r.body := by
  have e : s.body = (Rasso.Finrel.ofTuples r.heading r.tuples).body := body_eq fun t => by
    rw [mem_project h, mem_ofTuples]
    have key : ∀ u ∈ r.tuples, u.restrict r.attrs = u := fun u hu =>
      List.filter_eq_self.mpr fun p hp => by
        simpa [Rasso.Finrel.attrs] using
          ((hr.fits u hu).attrs p.1).mp (List.mem_map_of_mem (f := (·.1)) hp)
    constructor
    · rintro ⟨u, hu, rfl⟩; rw [key u hu]; exact hu
    · intro ht; exact ⟨t, ht, (key t ht).symm⟩
  rw [e]; exact Body.ofList_toList r.body

/-- π cascade: projecting onto `as`, then onto `bs` ⊆ `as`, is projecting onto `bs`. -/
theorem project_project {as bs : List String} {r s₁ s₂ s₃ : Rasso.Finrel}
    (hsub : ∀ b ∈ bs, b ∈ as) (h₁ : r.project as = .ok s₁) (h₂ : s₁.project bs = .ok s₂)
    (h₃ : r.project bs = .ok s₃) : s₂.body = s₃.body := body_eq fun t => by
  rw [mem_project h₂, mem_project h₃]
  have key : ∀ u : Tuple, (u.restrict as).restrict bs = u.restrict bs := fun u => by
    simp only [Tuple.restrict, List.filter_filter]
    congr 1; funext p
    cases hb : bs.contains p.1
    · simp
    · have : p.1 ∈ as := hsub _ (by simpa using hb)
      simp [this]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu, rfl⟩ := (mem_project h₁ w).mp hw
    exact ⟨u, hu, key u⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.restrict as, (mem_project h₁ _).mpr ⟨u, hu, rfl⟩, (key u).symm⟩

theorem project_union {as : List String} {r s u pr ps q q' : Rasso.Finrel}
    (h₁ : r.union s = .ok u) (h₂ : u.project as = .ok q) (h₃ : r.project as = .ok pr)
    (h₄ : s.project as = .ok ps) (h₅ : pr.union ps = .ok q') : q.body = q'.body :=
  body_eq fun t => by
    rw [mem_project h₂, mem_union h₅, mem_project h₃, mem_project h₄]
    constructor
    · rintro ⟨w, hw, rfl⟩
      cases (mem_union h₁ w).mp hw with
      | inl hw => exact Or.inl ⟨w, hw, rfl⟩
      | inr hw => exact Or.inr ⟨w, hw, rfl⟩
    · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
      · exact ⟨w, (mem_union h₁ w).mpr (Or.inl hw), rfl⟩
      · exact ⟨w, (mem_union h₁ w).mpr (Or.inr hw), rfl⟩

theorem project_empty {as : List String} {r s : Rasso.Finrel} (hr : r.tuples = [])
    (h : r.project as = .ok s) : s.tuples = [] := List.eq_nil_iff_forall_not_mem.mpr fun t ht => by
  obtain ⟨u, hu, _⟩ := (mem_project h t).mp ht; rw [hr] at hu; cases hu

/-- π is monotone (stated by membership: Rasso has no ⊆ on bodies). -/
theorem project_mono {as : List String} {r s pr ps : Rasso.Finrel}
    (hsub : ∀ t ∈ r.tuples, t ∈ s.tuples) (h₁ : r.project as = .ok pr)
    (h₂ : s.project as = .ok ps) : ∀ t ∈ pr.tuples, t ∈ ps.tuples := fun t ht => by
  obtain ⟨u, hu, rfl⟩ := (mem_project h₁ t).mp ht
  exact (mem_project h₂ _).mpr ⟨u, hsub u hu, rfl⟩

/-- π onto no attributes gives DEE when the operand has a tuple. -/
theorem project_nil_dee {r s : Rasso.Finrel} (hr : r.tuples ≠ []) (h : r.project [] = .ok s) :
    s.body = dee.body := body_eq fun t => by
  rw [mem_project h, mem_dee]
  constructor
  · rintro ⟨u, _, rfl⟩; simp [Tuple.restrict]
  · rintro rfl
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hr
    exact ⟨u, hu, by simp [Tuple.restrict]⟩

/-- π onto no attributes gives DUM when the operand has no tuple. -/
theorem project_nil_dum {r s : Rasso.Finrel} (hr : r.tuples = []) (h : r.project [] = .ok s) :
    s.body = dum.body := body_eq fun t => by
  rw [mem_project h]; simp [hr, dum]

/-- The semijoin bound: projecting `r ⋈ s` back onto `r`'s attributes gives tuples of `r`. -/
theorem project_join_sub {r s q p : Rasso.Finrel} (hr : r.WF) (hs : s.WF)
    (h₁ : r.join s = .ok q) (h₂ : q.project r.attrs = .ok p) :
    ∀ t ∈ p.tuples, t ∈ r.tuples := fun t ht => by
  obtain ⟨w, hw, rfl⟩ := (mem_project h₂ t).mp ht
  obtain ⟨u, hu, v, hv, ha, rfl⟩ := (mem_join h₁ w).mp hw
  have fu := hr.fits u hu; have fv := hs.fits v hv
  have hc := (agrees_iff fv.nodup).mp ha
  have hms : (u.merge v).Pairwise fun p q => p.1 < q.1 := by
    rw [merge_eq]; exact ofPairs_sorted (mergeList_nodup fu.nodup fv.nodup)
  have : (u.merge v).restrict r.attrs = u := by
    refine eq_of_mem_iff (restrict_sorted hms _) fu.sorted fun ⟨a, x⟩ => ?_
    rw [mem_restrict, mem_merge hc]
    constructor
    · rintro ⟨hx | hx, har⟩
      · exact hx
      · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp
          (lookup_isSome_iff_mem ((fu.attrs a).mpr har))
        have := hc a y x (lookup_mem hy) hx; subst this; exact lookup_mem hy
    · intro hx
      exact ⟨Or.inl hx, (fu.attrs a).mp (List.mem_map_of_mem (f := (·.1)) hx)⟩
  rw [this]; exact hu

/-! ## ρ -/

theorem rename_union {ren : List (String × String)} {r s u ρr ρs q q' : Rasso.Finrel}
    (h₁ : r.union s = .ok u) (h₂ : u.rename ren = .ok q) (h₃ : r.rename ren = .ok ρr)
    (h₄ : s.rename ren = .ok ρs) (h₅ : ρr.union ρs = .ok q') : q.body = q'.body :=
  body_eq fun t => by
    rw [mem_rename h₂, mem_union h₅, mem_rename h₃, mem_rename h₄]
    constructor
    · rintro ⟨w, hw, rfl⟩
      cases (mem_union h₁ w).mp hw with
      | inl hw => exact Or.inl ⟨w, hw, rfl⟩
      | inr hw => exact Or.inr ⟨w, hw, rfl⟩
    · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
      · exact ⟨w, (mem_union h₁ w).mpr (Or.inl hw), rfl⟩
      · exact ⟨w, (mem_union h₁ w).mpr (Or.inr hw), rfl⟩

/-- Renaming nothing changes nothing. -/
theorem rename_nil {r s : Rasso.Finrel} (hr : r.WF) (h : r.rename [] = .ok s) :
    s.body = r.body := by
  have key : ∀ u : Tuple, u.Pairwise (fun p q => p.1 < q.1) → renameTuple [] u = u := by
    intro u hu
    have : (u.map fun (a, v) => (renameAttr [] a, v)) = u := by
      conv => rhs; rw [← List.map_id u]
      congr 1
    rw [renameTuple, this, ofPairs_self hu]
  have e : s.body = (Rasso.Finrel.ofTuples r.heading r.tuples).body := body_eq fun t => by
    rw [mem_rename h, mem_ofTuples]
    constructor
    · rintro ⟨u, hu, rfl⟩; rw [key u (hr.fits u hu).sorted]; exact hu
    · intro ht; exact ⟨t, ht, (key t (hr.fits t ht).sorted).symm⟩
  rw [e]; exact Body.ofList_toList r.body

/-! ## More ⋈ -/

/-- Inside a merge of agreeing tuples, a sorted tuple over given attributes is determined by
those attributes: two such parts over the same attributes are equal. -/
theorem part_unique {t b c : Tuple} (ht : t.attrs.Nodup) (fb : b.Pairwise fun p q => p.1 < q.1)
    (fc : c.Pairwise fun p q => p.1 < q.1) (hb : ∀ p ∈ b, p ∈ t) (hc : ∀ p ∈ c, p ∈ t)
    (ha : ∀ a, a ∈ b.attrs ↔ a ∈ c.attrs) : b = c := by
  refine eq_of_mem_iff fb fc fun ⟨a, x⟩ => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨⟨a', y⟩, hy, e⟩ := List.mem_map.mp ((ha a).mp (List.mem_map_of_mem (f := (·.1)) hx))
    simp only at e; subst e
    have h1 := mem_lookup ht (hb _ hx); have h2 := mem_lookup ht (hc _ hy)
    rw [h1] at h2; cases h2; exact hy
  · obtain ⟨⟨a', y⟩, hy, e⟩ := List.mem_map.mp ((ha a).mpr (List.mem_map_of_mem (f := (·.1)) hx))
    simp only at e; subst e
    have h1 := mem_lookup ht (hc _ hx); have h2 := mem_lookup ht (hb _ hy)
    rw [h1] at h2; cases h2; exact hy

/-- ⋈ distributes over −. -/
theorem join_diff {r s u d q rs ru q' : Rasso.Finrel} (hr : r.WF) (hs : s.WF) (hu : u.WF)
    (h₁ : s.diff u = .ok d) (h₂ : r.join d = .ok q) (h₃ : r.join s = .ok rs)
    (h₄ : r.join u = .ok ru) (h₅ : rs.diff ru = .ok q') : q.body = q'.body := body_eq fun t => by
  have hh := diff_ok.mp ⟨_, h₁⟩
  rw [mem_join h₂, mem_diff h₅, mem_join h₃, mem_join h₄]
  constructor
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    obtain ⟨hbs, hbu⟩ := (mem_diff h₁ b).mp hb
    refine ⟨⟨a, ha, b, hbs, hab, rfl⟩, ?_⟩
    rintro ⟨a', ha', c, hc, hac, e⟩
    have fa := hr.fits a ha; have fb := hs.fits b hbs
    have fa' := hr.fits a' ha'; have fc := hu.fits c hc
    have cab := (agrees_iff fb.nodup).mp hab; have cac := (agrees_iff fc.nodup).mp hac
    have hn : (a.merge b).attrs.Nodup := merge_attrs_nodup fa.nodup fb.nodup
    have : b = c := part_unique hn fb.sorted fc.sorted
      (fun p hp => (mem_merge cab).mpr (Or.inr hp))
      (fun p hp => e ▸ (mem_merge cac).mpr (Or.inr hp))
      (fun x => (fb.attrs x).trans ((SameHeading.attrs_iff hh x).trans (fc.attrs x).symm))
    subst this; exact hbu hc
  · rintro ⟨⟨a, ha, b, hbs, hab, rfl⟩, hn⟩
    refine ⟨a, ha, b, (mem_diff h₁ b).mpr ⟨hbs, fun hbu => hn ⟨a, ha, b, hbu, hab, rfl⟩⟩, hab, rfl⟩

/-- Every well-formed relation with no attributes is DEE or DUM. -/
theorem nullary_dee_or_dum {r : Rasso.Finrel} (hr : r.WF) (h0 : r.heading = []) :
    r.body = dee.body ∨ r.body = dum.body := by
  have hnil : ∀ u ∈ r.tuples, u = [] := fun u hu => by
    have f := hr.fits u hu
    cases u with
    | nil => rfl
    | cons p _ =>
      have := (f.attrs p.1).mp (List.mem_cons_self ..)
      rw [h0] at this; cases this
  by_cases he : r.tuples = []
  · right
    exact body_eq fun t => by rw [he]; simp [dum]
  · left
    exact body_eq fun t => by
      rw [mem_dee]
      constructor
      · exact hnil t
      · rintro rfl
        obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ he
        exact hnil u hu ▸ hu

/-! ## The heading of ⋈ -/

/-- A value is in a join's domain for an attribute exactly when it is in that attribute's
domain on each side that has it. -/
theorem joinHeading_mem {h k j : Heading} (hj : joinHeading h k = .ok j) (hh : h.attrs.Nodup)
    (hk : k.attrs.Nodup) {a : String} {f : Domain} (hf : j.lookup a = some f) (x : Value) :
    f.mem x = true ↔ (∀ d, h.lookup a = some d → d.mem x = true) ∧
      (∀ e, k.lookup a = some e → e.mem x = true) := by
  rcases (joinHeading_spec hj hh hk).2.2 a f hf with ⟨d, hd, (⟨hk0, rfl⟩ | ⟨e, he, hi⟩)⟩ | ⟨hna, hkf⟩
  · have hl := mem_lookup hh hd
    constructor
    · intro hx; exact ⟨fun d' h' => by rw [hl] at h'; cases h'; exact hx,
        fun e h' => by rw [hk0] at h'; cases h'⟩
    · rintro ⟨h1, _⟩; exact h1 _ hl
  · have hl := mem_lookup hh hd
    constructor
    · intro hx
      have := Domain.inter_complete hi hx
      exact ⟨fun d' h' => by rw [hl] at h'; cases h'; exact this.1,
        fun e' h' => by rw [he] at h'; cases h'; exact this.2⟩
    · rintro ⟨h1, h2⟩; exact Domain.inter_sound hi (h1 _ hl) (h2 _ he)
  · have hl : h.lookup a = none := by
      cases hc : h.lookup a with
      | none => rfl
      | some d => exact absurd (List.mem_map_of_mem (f := (·.1)) (lookup_mem hc)) hna
    constructor
    · intro hx
      exact ⟨fun d' h' => (by rw [hl] at h'; cases h'),
        fun e h' => (by rw [hkf] at h'; cases h'; exact hx)⟩
    · rintro ⟨_, h2⟩; exact h2 _ hkf

/-- The headings of `r ⋈ s` and `s ⋈ r` have the same attributes, and each attribute's two
domains have the same members. -/
theorem join_comm_heading {r s q q' : Rasso.Finrel} (hr : r.heading.attrs.Nodup)
    (hs : s.heading.attrs.Nodup) (h : r.join s = .ok q) (h' : s.join r = .ok q') :
    (∀ a, a ∈ q.attrs ↔ a ∈ q'.attrs) ∧
      ∀ a f f', q.heading.lookup a = some f → q'.heading.lookup a = some f' →
        ∀ x, f.mem x = f'.mem x := by
  have hj := join_heading h; have hj' := join_heading h'
  refine ⟨fun a => ?_, fun a f f' hf hf' x => ?_⟩
  · have e1 := (joinHeading_spec hj hr hs).2.1 a
    have e2 := (joinHeading_spec hj' hs hr).2.1 a
    exact e1.trans (Or.comm.trans e2.symm)
  · have m1 := joinHeading_mem hj hr hs hf x
    have m2 := joinHeading_mem hj' hs hr hf' x
    exact Bool.eq_iff_iff.mpr (m1.trans (And.comm.trans m2.symm))

/-! ## Definedness -/

/-- σ cascade: σ_p (σ_q r) and σ_(q then p) r refuse together. -/
theorem select_cascade_ok {p q : Tuple → Except String Bool} {r : Rasso.Finrel} :
    (∃ rq s, r.select q = .ok rq ∧ rq.select p = .ok s) ↔
      ∃ s', r.select (andThen q p) = .ok s' := by
  constructor
  · rintro ⟨rq, s, h₁, h₂⟩
    have hq := select_ok.mp ⟨_, h₁⟩
    have hp := select_ok.mp ⟨_, h₂⟩
    refine select_ok.mpr fun t ht => ?_
    obtain ⟨b, hb⟩ := hq t ht
    cases b with
    | false => exact ⟨false, by simp [andThen, hb, bind, Except.bind, pure, Except.pure]⟩
    | true =>
      obtain ⟨c, hc⟩ := hp t ((mem_select h₁ t).mpr ⟨ht, hb⟩)
      exact ⟨c, by simp [andThen, hb, hc, bind, Except.bind]⟩
  · rintro ⟨s', h⟩
    have hqp := select_ok.mp ⟨_, h⟩
    have hq : ∃ rq, r.select q = .ok rq := select_ok.mpr fun t ht => by
      obtain ⟨b, hb⟩ := hqp t ht
      unfold andThen at hb
      cases hqt : q t with
      | error e => rw [hqt] at hb; cases hb
      | ok c => exact ⟨c, rfl⟩
    obtain ⟨rq, h₁⟩ := hq
    have hp : ∃ s, rq.select p = .ok s := select_ok.mpr fun t ht => by
      obtain ⟨ht, hqt⟩ := (mem_select h₁ t).mp ht
      obtain ⟨b, hb⟩ := hqp t ht
      unfold andThen at hb
      rw [hqt] at hb
      exact ⟨b, by simpa [bind, Except.bind] using hb⟩
    obtain ⟨s, h₂⟩ := hp
    exact ⟨rq, s, h₁, h₂⟩

/-- σ over ∪ refuses together: σ_p (r ∪ s) and σ_p r ∪ σ_p s test the same tuples. -/
theorem select_union_ok {p : Tuple → Except String Bool} {r s u : Rasso.Finrel}
    (h₁ : r.union s = .ok u) :
    (∃ q, u.select p = .ok q) ↔ (∃ rp, r.select p = .ok rp) ∧ (∃ sp, s.select p = .ok sp) := by
  rw [select_ok, select_ok, select_ok]
  constructor
  · intro h
    exact ⟨fun t ht => h t ((mem_union h₁ t).mpr (Or.inl ht)),
      fun t ht => h t ((mem_union h₁ t).mpr (Or.inr ht))⟩
  · rintro ⟨h1, h2⟩ t ht
    cases (mem_union h₁ t).mp ht with
    | inl ht => exact h1 t ht
    | inr ht => exact h2 t ht

/-! ## × -/

/-- × is ⋈ on headings that share no attribute. -/
theorem product_eq_join {r s q : Rasso.Finrel} (h : r.product s = .ok q) : r.join s = .ok q := by
  simp only [Rasso.Finrel.product, bind, Except.bind] at h
  split at h
  · cases h
  · exact h

/-- × refuses headings that share an attribute. -/
theorem product_ok_disjoint {r s q : Rasso.Finrel} (h : r.product s = .ok q) :
    Heading.disjoint "×" r.heading s.heading = .ok () := by
  simp only [Rasso.Finrel.product, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i u hu; cases u; exact hu

/-! ## ρ is injective on tuples that fit -/

theorem mem_renameTuple {ren : List (String × String)} {u : Tuple} {p : String × Value} :
    p ∈ renameTuple ren u ↔ ∃ q ∈ u, p = (renameAttr ren q.1, q.2) := by
  simp only [renameTuple, mem_ofPairs, List.mem_map]
  exact ⟨fun ⟨q, hq, e⟩ => ⟨q, hq, e.symm⟩, fun ⟨q, hq, e⟩ => ⟨q, hq, e.symm⟩⟩

theorem renameAttr_inj {ren : List (String × String)} {h : Heading}
    (hn : (renameHeading ren h).attrs.Nodup) {a b : String} (ha : a ∈ h.attrs) (hb : b ∈ h.attrs)
    (e : renameAttr ren a = renameAttr ren b) : a = b := by
  obtain ⟨⟨a', d⟩, hd, rfl⟩ := List.mem_map.mp ha
  obtain ⟨⟨b', d'⟩, hd', rfl⟩ := List.mem_map.mp hb
  have hn' : (h.map fun p => renameAttr ren p.1).Nodup := by
    simp only [renameHeading, Heading.attrs, List.map_map] at hn
    exact hn
  exact congrArg Prod.fst (inj_of_nodup_map hn' _ hd _ hd' e)

theorem renameTuple_inj {ren : List (String × String)} {h : Heading} {u v : Tuple}
    (hn : (renameHeading ren h).attrs.Nodup) (fu : u.Fits h) (fv : v.Fits h)
    (e : renameTuple ren u = renameTuple ren v) : u = v := by
  have side : ∀ {u v : Tuple}, u.Fits h → v.Fits h → renameTuple ren u = renameTuple ren v →
      ∀ p ∈ u, p ∈ v := by
    intro u v fu fv e ⟨a, x⟩ hx
    have : (renameAttr ren a, x) ∈ renameTuple ren v :=
      e ▸ mem_renameTuple.mpr ⟨(a, x), hx, rfl⟩
    obtain ⟨⟨b, y⟩, hy, e'⟩ := mem_renameTuple.mp this
    simp only [Prod.mk.injEq] at e'
    obtain ⟨e1, rfl⟩ := e'
    have : a = b := renameAttr_inj hn
      ((fu.attrs a).mp (List.mem_map_of_mem (f := (·.1)) hx))
      ((fv.attrs b).mp (List.mem_map_of_mem (f := (·.1)) hy)) e1
    subst this; exact hy
  exact eq_of_mem_iff fu.sorted fv.sorted fun p => ⟨side fu fv e p, side fv fu e.symm p⟩

/-- ρ distributes over −. -/
theorem rename_diff {ren : List (String × String)} {r s d ρr ρs q q' : Rasso.Finrel}
    (hr : r.WF) (hs : s.WF) (h₁ : r.diff s = .ok d) (h₂ : d.rename ren = .ok q)
    (h₃ : r.rename ren = .ok ρr) (h₄ : s.rename ren = .ok ρs) (h₅ : ρr.diff ρs = .ok q') :
    q.body = q'.body := body_eq fun t => by
  have hh := diff_ok.mp ⟨_, h₁⟩
  have hn := (rename_eq_ok.mp h₃).2.1
  rw [mem_rename h₂, mem_diff h₅, mem_rename h₃, mem_rename h₄]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hur, hus⟩ := (mem_diff h₁ u).mp hu
    refine ⟨⟨u, hur, rfl⟩, ?_⟩
    rintro ⟨v, hv, e⟩
    have := renameTuple_inj hn (hr.fits u hur) (SameHeading.fits hh (hs.fits v hv)) e
    subst this; exact hus hv
  · rintro ⟨⟨u, hur, rfl⟩, hn'⟩
    exact ⟨u, (mem_diff h₁ u).mpr ⟨hur, fun hus => hn' ⟨u, hus, rfl⟩⟩, rfl⟩

/-- ρ distributes over ∩. -/
theorem rename_inter {ren : List (String × String)} {r s i ρr ρs q q' : Rasso.Finrel}
    (hr : r.WF) (hs : s.WF) (h₁ : r.inter s = .ok i) (h₂ : i.rename ren = .ok q)
    (h₃ : r.rename ren = .ok ρr) (h₄ : s.rename ren = .ok ρs) (h₅ : ρr.inter ρs = .ok q') :
    q.body = q'.body := body_eq fun t => by
  have hh := inter_ok.mp ⟨_, h₁⟩
  have hn := (rename_eq_ok.mp h₃).2.1
  rw [mem_rename h₂, mem_inter h₅, mem_rename h₃, mem_rename h₄]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hur, hus⟩ := (mem_inter h₁ u).mp hu
    exact ⟨⟨u, hur, rfl⟩, ⟨u, hus, rfl⟩⟩
  · rintro ⟨⟨u, hur, rfl⟩, ⟨v, hv, e⟩⟩
    have := renameTuple_inj hn (hr.fits u hur) (SameHeading.fits hh (hs.fits v hv)) e
    subst this
    exact ⟨u, (mem_inter h₁ u).mpr ⟨hur, hv⟩, rfl⟩

end FinrelLaws
end Rasso
