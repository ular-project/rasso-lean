import Rasso.Laws.Finrel
import Rasso.Classes

/-!
# Rasso: the laws of unrestricted relations

The laws of unrestricted relations, and the facts that hold per heading, for Rasso's own
unrestricted relations (a heading and one Boolean term). The rows are in the laws appendix
of the Rasso blueprint.

How a law is stated:

* **Same result.** Two unrestricted relations are compared by what they hold
  (`Same u v`: the same tuples fit and make the term true), always with a statement about the
  headings, since `Same` alone does not see them.
* **When both sides succeed**, as for finite relations.
* **Totality only where it is needed.** Rasso's `and` and `or` evaluate every operand, so a
  refusal propagates. ∩, σ and ⋈ need no totality; ∪ and − need it (`union_holds`,
  `diff_holds`). `Rasso/Laws/UnrelExamples.lean` shows laws that fail without it.

Conventions:

* The empty relation over a heading is the term `false` (`empty`); Rasso has no constructor
  for it. The top is `Unrel.omega h` (the term `true`).
-/

namespace Rasso
namespace UnrelLaws

open Rasso.Unrel

/-- Two unrestricted relations hold the same tuples. -/
def Same (u v : Unrel) : Prop := ∀ t, u.Holds t ↔ v.Holds t

theorem Same.refl (u : Unrel) : Same u u := fun _ => Iff.rfl
theorem Same.symm {u v : Unrel} (h : Same u v) : Same v u := fun t => (h t).symm
theorem Same.trans {u v x : Unrel} (h₁ : Same u v) (h₂ : Same v x) : Same u x :=
  fun t => (h₁ t).trans (h₂ t)

/-! ## The constants -/

/-- The empty relation over a heading: the term `false`. -/
def empty (h : Heading) : Unrel := ⟨h, .val (.bool false)⟩

theorem empty_term_holds (h : Heading) (t : Tuple) : (empty h).term.holds t = .ok false := by
  simp [empty, Term.holds, Term.eval, asBool, bind, Except.bind]

theorem not_holds_empty (h : Heading) (t : Tuple) : ¬ (empty h).Holds t := fun ⟨_, e⟩ => by
  rw [empty_term_holds] at e; cases e

theorem empty_total (h : Heading) : (empty h).Total := fun t _ => ⟨false, empty_term_holds h t⟩

/-- DEE: no attributes, the term `true`. DUM: no attributes, the term `false`. -/
def dee : Unrel := omega []
def dum : Unrel := empty []

theorem fits_nil {t : Tuple} : t.Fits [] ↔ t = [] := by
  constructor
  · intro f
    cases t with
    | nil => rfl
    | cons p _ =>
      have := (f.attrs p.1).mp (List.mem_cons_self ..)
      simp [Heading.attrs] at this
  · rintro rfl; exact ⟨List.Pairwise.nil, fun a => by simp [Tuple.attrs, Heading.attrs],
      fun _ hp => by cases hp⟩

/-- Every total relation with no attributes holds what DEE holds, or what DUM holds: the
nullary relations are a two-element algebra. -/
theorem nullary_dee_or_dum {u : Unrel} (h0 : u.heading = []) (hu : u.Total) :
    Same u dee ∨ Same u dum := by
  obtain ⟨b, hb⟩ := hu [] (h0 ▸ fits_nil.mpr rfl)
  cases b
  · right; intro t
    simp only [Holds, h0, fits_nil, dum, empty_term_holds]
    constructor
    · rintro ⟨rfl, e⟩; rw [hb] at e; cases e
    · rintro ⟨_, e⟩; cases e
  · left; intro t
    simp only [Holds, h0, fits_nil, dee, omega_term_holds]
    constructor
    · rintro ⟨rfl, _⟩; exact ⟨fits_nil.mpr rfl, by first | rfl | trivial⟩
    · rintro ⟨f, _⟩; have := fits_nil.mp f; subst this; exact ⟨rfl, hb⟩

/-! ## ∪ -/

theorem union_comm {u v w w' : Unrel} (hu : u.Total) (hv : v.Total) (h : u.union v = .ok w)
    (h' : v.union u = .ok w') : Same w w' := fun t => by
  rw [union_holds h hu hv, union_holds h' hv hu, Or.comm]

theorem union_assoc {u v x uv vx w w' : Unrel} (hu : u.Total) (hv : v.Total) (hx : x.Total)
    (h₁ : u.union v = .ok uv) (h₂ : uv.union x = .ok w) (h₃ : v.union x = .ok vx)
    (h₄ : u.union vx = .ok w') : Same w w' := fun t => by
  rw [union_holds h₂ (union_total h₁ hu hv) hx, union_holds h₁ hu hv,
    union_holds h₄ hu (union_total h₃ hv hx), union_holds h₃ hv hx, or_assoc]

theorem union_idem {u w : Unrel} (hu : u.Total) (h : u.union u = .ok w) : Same w u := fun t => by
  rw [union_holds h hu hu, or_self]

theorem union_empty {u w : Unrel} (hu : u.Total) (h : u.union (empty u.heading) = .ok w) :
    Same w u := fun t => by
  rw [union_holds h hu (empty_total _)]
  exact ⟨fun h => h.elim id fun h' => absurd h' (not_holds_empty _ t), Or.inl⟩

theorem union_top {u w : Unrel} (hu : u.Total) (h : u.union (omega u.heading) = .ok w) :
    Same w (omega u.heading) := fun t => by
  rw [union_holds h hu (omega_total _), omega_holds]
  exact ⟨fun h => h.elim (·.1) id, Or.inr⟩

/-! ## ∩ -/

theorem inter_comm {u v w w' : Unrel} (h : u.inter v = .ok w) (h' : v.inter u = .ok w') :
    Same w w' := fun t => by rw [inter_holds h, inter_holds h', And.comm]

theorem inter_assoc {u v x uv vx w w' : Unrel}
    (h₁ : u.inter v = .ok uv) (h₂ : uv.inter x = .ok w) (h₃ : v.inter x = .ok vx)
    (h₄ : u.inter vx = .ok w') : Same w w' := fun t => by
  rw [inter_holds h₂, inter_holds h₁, inter_holds h₄, inter_holds h₃, and_assoc]

theorem inter_idem {u w : Unrel} (h : u.inter u = .ok w) : Same w u := fun t => by
  rw [inter_holds h, and_self]

theorem inter_top {u w : Unrel} (h : u.inter (omega u.heading) = .ok w) : Same w u := fun t => by
  rw [inter_holds h, omega_holds]; exact ⟨(·.1), fun h => ⟨h, h.1⟩⟩

theorem union_inter_absorb {u v i w : Unrel} (hu : u.Total) (hv : v.Total)
    (h₁ : u.inter v = .ok i) (h₂ : u.union i = .ok w) : Same w u := fun t => by
  rw [union_holds h₂ hu (inter_total h₁ hu hv), inter_holds h₁]
  exact ⟨fun h => h.elim id (·.1), Or.inl⟩

theorem inter_union_absorb {u v x w : Unrel} (hu : u.Total) (hv : v.Total)
    (h₁ : u.union v = .ok x) (h₂ : u.inter x = .ok w) : Same w u := fun t => by
  rw [inter_holds h₂, union_holds h₁ hu hv]
  exact ⟨(·.1), fun h => ⟨h, Or.inl h⟩⟩

theorem union_inter_distrib {u v x vx uv ux w w' : Unrel} (hu : u.Total) (hv : v.Total)
    (hx : x.Total) (h₁ : v.inter x = .ok vx) (h₂ : u.union vx = .ok w) (h₃ : u.union v = .ok uv)
    (h₄ : u.union x = .ok ux) (h₅ : uv.inter ux = .ok w') : Same w w' := fun t => by
  rw [union_holds h₂ hu (inter_total h₁ hv hx), inter_holds h₁, inter_holds h₅,
    union_holds h₃ hu hv, union_holds h₄ hu hx, or_and_left]

theorem inter_union_distrib {u v x vx uv ux w w' : Unrel} (hu : u.Total) (hv : v.Total)
    (hx : x.Total) (h₁ : v.union x = .ok vx) (h₂ : u.inter vx = .ok w) (h₃ : u.inter v = .ok uv)
    (h₄ : u.inter x = .ok ux) (h₅ : uv.union ux = .ok w') : Same w w' := fun t => by
  rw [inter_holds h₂, union_holds h₁ hv hx, union_holds h₅ (inter_total h₃ hu hv)
    (inter_total h₄ hu hx), inter_holds h₃, inter_holds h₄, and_or_left]

/-! ## − -/

theorem diff_self {u w : Unrel} (hu : u.Total) (h : u.diff u = .ok w) :
    Same w (empty u.heading) := fun t => by
  rw [diff_holds h hu]
  exact ⟨fun ⟨a, b⟩ => absurd a b, fun h => absurd h (not_holds_empty _ t)⟩

theorem diff_empty {u w : Unrel} (h : u.diff (empty u.heading) = .ok w) : Same w u := fun t => by
  rw [diff_holds h (empty_total _)]
  exact ⟨(·.1), fun h => ⟨h, not_holds_empty _ t⟩⟩

theorem empty_diff {hd : Heading} {u w : Unrel} (hu : u.Total) (h : (empty hd).diff u = .ok w) :
    Same w (empty hd) := fun t => by
  rw [diff_holds h hu]
  exact ⟨fun ⟨a, _⟩ => a, fun h => absurd h (not_holds_empty _ t)⟩

theorem diff_union {u v x vx uv w w' : Unrel} (hv : v.Total) (hx : x.Total)
    (h₁ : v.union x = .ok vx) (h₂ : u.diff vx = .ok w) (h₃ : u.diff v = .ok uv)
    (h₄ : uv.diff x = .ok w') : Same w w' := fun t => by
  rw [diff_holds h₂ (union_total h₁ hv hx), union_holds h₁ hv hx, diff_holds h₄ hx,
    diff_holds h₃ hv, not_or, and_assoc]

theorem union_diff {u v x uv ux vx w w' : Unrel} (hu : u.Total) (hv : v.Total) (hx : x.Total)
    (h₁ : u.union v = .ok uv) (h₂ : uv.diff x = .ok w) (h₃ : u.diff x = .ok ux)
    (h₄ : v.diff x = .ok vx) (h₅ : ux.union vx = .ok w') : Same w w' := fun t => by
  rw [diff_holds h₂ hx, union_holds h₁ hu hv, union_holds h₅ (diff_total h₃ hu hx)
    (diff_total h₄ hv hx), diff_holds h₃ hx, diff_holds h₄ hx, or_and_right]

theorem inter_eq_diff_diff {u v d w w' : Unrel} (hu : u.Total) (hv : v.Total)
    (h₁ : u.diff v = .ok d) (h₂ : u.diff d = .ok w) (h : u.inter v = .ok w') : Same w w' :=
  fun t => by
    rw [diff_holds h₂ (diff_total h₁ hu hv), diff_holds h₁ hv, inter_holds h]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, Classical.byContradiction fun h3 => h2 ⟨h1, h3⟩⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun ⟨_, h3⟩ => h3 h2⟩

/-! ## Complement: a Boolean algebra per heading -/

theorem union_compl {u c w : Unrel} (hu : u.Total) (h₁ : (omega u.heading).diff u = .ok c)
    (h₂ : u.union c = .ok w) : Same w (omega u.heading) := fun t => by
  rw [union_holds h₂ hu (diff_total h₁ (omega_total _) hu), diff_holds h₁ hu, omega_holds]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact h.1
    · exact h
  · intro f
    exact (Classical.em (u.Holds t)).elim Or.inl fun hn => Or.inr ⟨f, hn⟩

theorem inter_compl {u c w : Unrel} (hu : u.Total) (h₁ : (omega u.heading).diff u = .ok c)
    (h₂ : u.inter c = .ok w) : Same w (empty u.heading) := fun t => by
  rw [inter_holds h₂, diff_holds h₁ hu]
  exact ⟨fun ⟨a, _, b⟩ => absurd a b, fun h => absurd h (not_holds_empty _ t)⟩

theorem compl_compl {u c w : Unrel} (hu : u.Total) (h₁ : (omega u.heading).diff u = .ok c)
    (h₂ : (omega u.heading).diff c = .ok w) : Same w u := fun t => by
  rw [diff_holds h₂ (diff_total h₁ (omega_total _) hu), diff_holds h₁ hu, omega_holds]
  constructor
  · rintro ⟨f, h⟩; exact Classical.byContradiction fun hn => h ⟨f, hn⟩
  · intro h; exact ⟨h.1, fun ⟨_, hn⟩ => hn h⟩

/-! ## ⋈ -/

/-- `x` is allowed for `a` by a heading: in its domain there, if the heading has `a`. -/
def DomOK (h : Heading) (a : String) (x : Value) : Prop := ∀ d, h.lookup a = some d → d.mem x = true

theorem joinHeading_domOK {h k j : Heading} (hj : Finrel.joinHeading h k = .ok j)
    (hh : h.attrs.Nodup) (hk : k.attrs.Nodup) (a : String) (x : Value) :
    DomOK j a x ↔ DomOK h a x ∧ DomOK k a x := by
  cases hl : j.lookup a with
  | some f =>
    have := FinrelLaws.joinHeading_mem hj hh hk hl x
    unfold DomOK
    constructor
    · intro hf; exact this.mp (hf f hl)
    · intro hb f' hf'; rw [hl] at hf'; cases hf'; exact this.mpr hb
  | none =>
    have hna : a ∉ j.attrs := fun ha => by rw [Finrel.mem_attrs_iff, hl] at ha; cases ha
    have hjattrs := (Finrel.joinHeading_spec hj hh hk).2.1 a
    have hnh : h.lookup a = none := by
      cases hc : h.lookup a with
      | none => rfl
      | some _ => exact absurd (hjattrs.mpr (.inl (Finrel.mem_attrs_iff.mpr (by rw [hc]; rfl)))) hna
    have hnk : k.lookup a = none := by
      cases hc : k.lookup a with
      | none => rfl
      | some _ => exact absurd (hjattrs.mpr (.inr (Finrel.mem_attrs_iff.mpr (by rw [hc]; rfl)))) hna
    unfold DomOK; rw [hl, hnh, hnk]; simp

/-- Fitting depends on a heading only through its attributes and what each allows. -/
theorem fits_congr {j j' : Heading} (ha : ∀ a, a ∈ j.attrs ↔ a ∈ j'.attrs)
    (hd : ∀ a x, DomOK j a x ↔ DomOK j' a x) {t : Tuple} : t.Fits j ↔ t.Fits j' :=
  ⟨fun f => ⟨f.sorted, fun a => (f.attrs a).trans (ha a), fun p hp => (hd p.1 p.2).mp (f.dom p hp)⟩,
   fun f => ⟨f.sorted, fun a => (f.attrs a).trans (ha a).symm,
     fun p hp => (hd p.1 p.2).mpr (f.dom p hp)⟩⟩

/-- What a join holds, read off its term: no well-formedness needed. -/
theorem join_holds' {u v w : Unrel} (h : u.join v = .ok w) (t : Tuple) :
    w.Holds t ↔ t.Fits w.heading ∧ u.term.holds t = .ok true ∧ v.term.holds t = .ok true := by
  obtain ⟨_, ht⟩ := join_heading h
  simp only [Holds, ht, holds_and2]
  constructor
  · rintro ⟨f, a, b, ha, hb, e⟩
    have : a = true ∧ b = true := by simpa using e.symm
    rw [this.1] at ha; rw [this.2] at hb
    exact ⟨f, ha, hb⟩
  · rintro ⟨f, ha, hb⟩; exact ⟨f, true, true, ha, hb, rfl⟩

theorem join_comm {u v w w' : Unrel} (hu : u.heading.attrs.Nodup) (hv : v.heading.attrs.Nodup)
    (h : u.join v = .ok w) (h' : v.join u = .ok w') : Same w w' := fun t => by
  have hj := (join_heading h).1; have hj' := (join_heading h').1
  rw [join_holds' h, join_holds' h', and_comm (a := u.term.holds t = .ok true),
    fits_congr (j := w.heading) (j' := w'.heading)
      (fun a => ((Finrel.joinHeading_spec hj hu hv).2.1 a).trans
        (Or.comm.trans ((Finrel.joinHeading_spec hj' hv hu).2.1 a).symm))
      (fun a x => (joinHeading_domOK hj hu hv a x).trans
        (And.comm.trans (joinHeading_domOK hj' hv hu a x).symm))]

theorem join_assoc {u v x uv vx w w' : Unrel} (hu : u.heading.attrs.Nodup)
    (hv : v.heading.attrs.Nodup) (hx : x.heading.attrs.Nodup)
    (h₁ : u.join v = .ok uv) (h₂ : uv.join x = .ok w) (h₃ : v.join x = .ok vx)
    (h₄ : u.join vx = .ok w') : Same w w' := fun t => by
  have j1 := (join_heading h₁).1; have j2 := (join_heading h₂).1
  have j3 := (join_heading h₃).1; have j4 := (join_heading h₄).1
  have nuv := (Finrel.joinHeading_spec j1 hu hv).1
  have nvx := (Finrel.joinHeading_spec j3 hv hx).1
  have a1 := (Finrel.joinHeading_spec j1 hu hv).2.1
  have a2 := (Finrel.joinHeading_spec j2 nuv hx).2.1
  have a3 := (Finrel.joinHeading_spec j3 hv hx).2.1
  have a4 := (Finrel.joinHeading_spec j4 hu nvx).2.1
  have hf : t.Fits w.heading ↔ t.Fits w'.heading := fits_congr
    (fun a => by rw [a2, a1, a4, a3, or_assoc])
    (fun a y => by
      rw [joinHeading_domOK j2 nuv hx, joinHeading_domOK j1 hu hv,
        joinHeading_domOK j4 hu nvx, joinHeading_domOK j3 hv hx, and_assoc])
  rw [join_holds' h₂, join_holds' h₄, hf]
  simp only [(join_heading h₁).2, (join_heading h₃).2, holds_and2]
  constructor
  · rintro ⟨f, ⟨a, b, ha, hb, e⟩, hc⟩
    have : a = true ∧ b = true := by simpa using e.symm
    rw [this.1] at ha; rw [this.2] at hb
    exact ⟨f, ha, true, true, hb, hc, rfl⟩
  · rintro ⟨f, ha, ⟨a, b, hb, hc, e⟩⟩
    have : a = true ∧ b = true := by simpa using e.symm
    rw [this.1] at hb; rw [this.2] at hc
    exact ⟨f, ⟨true, true, ha, hb, rfl⟩, hc⟩

/-- The heading of the join of two same headings is the left one. -/
theorem mapM_self {f : String × Domain → Except String (String × Domain)} :
    ∀ {l : List (String × Domain)}, (∀ p ∈ l, f p = .ok p) → l.mapM f = .ok l
  | [], _ => rfl
  | p :: l, h => by
    rw [List.mapM_cons, h p List.mem_cons_self,
      mapM_self (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    rfl

theorem joinHeading_same {h k : Heading} (hs : Heading.Same h k) :
    Finrel.joinHeading h k = .ok h := by
  unfold Finrel.joinHeading
  rw [mapM_self (fun p hp => by
    obtain ⟨a, d⟩ := p
    have := hs.2 _ hp
    simp only at this
    simp only [this, Domain.inter]; rfl)]
  have : k.filter (fun p => (h.lookup p.1).isNone) = [] :=
    List.filter_eq_nil_iff.mpr fun p hp => by
      have : p.1 ∈ h.attrs := (hs.attrs p.1).mpr (List.mem_map_of_mem (f := (·.1)) hp)
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp this)
      simp [hd]
  simp [bind, Except.bind, this, pure, Except.pure]

/-- On one heading, ⋈ is ∩, as Lean equality. -/
theorem join_eq_inter {u v : Unrel} (hs : Heading.Same u.heading v.heading) :
    u.join v = u.inter v := by
  simp only [Unrel.join, Unrel.inter, joinHeading_same hs, Heading.same_ok.mpr hs, bind,
    Except.bind, pure, Except.pure]

/-- σ is ⋈ with an atom: `σ_p u` is `u ⋈ ⟨heading, p⟩`, as Lean equality, when no attribute is
named twice. -/
theorem select_eq_join {p : Term} {u w : Unrel} (hn : u.heading.attrs.Nodup)
    (h : u.select p = .ok w) : u.join ⟨u.heading, p⟩ = .ok w := by
  obtain ⟨hh, ht⟩ := select_heading h
  have hs : Heading.Same u.heading u.heading :=
    ⟨rfl, fun q hq => mem_lookup hn hq⟩
  simp only [Unrel.join, joinHeading_same hs, bind, Except.bind, pure, Except.pure]
  cases w; simp only at hh ht; subst hh ht; rfl

theorem join_idem {u w : Unrel} (hn : u.heading.attrs.Nodup) (h : u.join u = .ok w) :
    Same w u := fun t => by
  have hs : Heading.Same u.heading u.heading := ⟨rfl, fun q hq => mem_lookup hn hq⟩
  have hw : w.heading = u.heading := by
    have := (join_heading h).1; rw [joinHeading_same hs] at this; exact (Except.ok.inj this).symm
  rw [join_holds' h, hw, and_self]; rfl

/-- DEE is an identity of ⋈. -/
theorem join_dee {u w : Unrel} (hn : u.heading.attrs.Nodup) (h : u.join dee = .ok w) :
    Same w u := fun t => by
  have hj := (join_heading h).1
  have hnil : (dee.heading).attrs.Nodup := List.nodup_nil
  have hf : t.Fits w.heading ↔ t.Fits u.heading := fits_congr
    (fun a => ((Finrel.joinHeading_spec hj hn hnil).2.1 a).trans
      ⟨fun h => h.elim id (fun h' => by simp [dee, omega, Heading.attrs] at h'), Or.inl⟩)
    (fun a x => (joinHeading_domOK hj hn hnil a x).trans
      ⟨(·.1), fun h => ⟨h, fun d hd => by simp [dee, omega] at hd⟩⟩)
  rw [join_holds' h, hf]
  simp only [dee, omega_term_holds, and_true]; rfl

/-- ⋈ with an empty relation, of any heading, holds nothing. -/
theorem join_empty {u w : Unrel} {hd : Heading} (h : u.join (empty hd) = .ok w) (t : Tuple) :
    ¬ w.Holds t := fun hw => by
  have := ((join_holds' h t).mp hw).2.2; rw [empty_term_holds] at this; cases this

theorem empty_join {u w : Unrel} {hd : Heading} (h : (empty hd).join u = .ok w) (t : Tuple) :
    ¬ w.Holds t := fun hw => by
  have := ((join_holds' h t).mp hw).2.1; rw [empty_term_holds] at this; cases this

/-- r ⋈ ⊤ is r, on one heading. -/
theorem join_top {u w : Unrel} (hn : u.heading.attrs.Nodup) (h : u.join (omega u.heading) = .ok w) :
    Same w u := fun t => by
  have hs : Heading.Same u.heading (omega u.heading).heading := ⟨rfl, fun q hq => mem_lookup hn hq⟩
  have hw : w.heading = u.heading := by
    have := (join_heading h).1; rw [joinHeading_same hs] at this; exact (Except.ok.inj this).symm
  rw [join_holds' h, hw]; simp only [omega_term_holds, and_true]; rfl

/-- ⋈ distributes over ∪. -/
theorem join_union {u v x vx uv ux w w' : Unrel} (hu : u.WF) (hv : v.WF) (hx : x.WF)
    (tu : u.Total) (tv : v.Total) (tx : x.Total)
    (h₁ : v.union x = .ok vx) (h₂ : u.join vx = .ok w) (h₃ : u.join v = .ok uv)
    (h₄ : u.join x = .ok ux) (h₅ : uv.union ux = .ok w') : Same w w' := fun t => by
  obtain ⟨hs, hvh, hvt⟩ := Unrel.union_heading h₁
  have j2 := (join_heading h₂).1; have j3 := (join_heading h₃).1; have j4 := (join_heading h₄).1
  rw [hvh] at j2
  rw [join_holds' h₂, union_holds h₅ (join_total h₃ hu hv tu tv) (join_total h₄ hu hx tu tx),
    join_holds' h₃, join_holds' h₄, hvt, holds_or2]
  have e1 : w.heading = uv.heading := by rw [j3] at j2; exact (Except.ok.inj j2).symm
  have hxv : ∀ y : Tuple, y.Fits ux.heading ↔ y.Fits uv.heading := fun y => fits_congr
    (fun a => ((Finrel.joinHeading_spec j4 hu.nodup hx.nodup).2.1 a).trans
      ((or_congr Iff.rfl (hs.attrs a).symm).trans
        ((Finrel.joinHeading_spec j3 hu.nodup hv.nodup).2.1 a).symm))
    (fun a z => (joinHeading_domOK j4 hu.nodup hx.nodup a z).trans
      ((and_congr Iff.rfl (by unfold DomOK; rw [hs.lookup a])).trans
        (joinHeading_domOK j3 hu.nodup hv.nodup a z).symm))
  rw [e1, hxv]
  constructor
  · rintro ⟨f, ha, p, q, hp, hq, e⟩
    cases p
    · cases q
      · cases e
      · exact Or.inr ⟨f, ha, hq⟩
    · exact Or.inl ⟨f, ha, hp⟩
  · rintro (⟨f, ha, hp⟩ | ⟨f, ha, hq⟩)
    · obtain ⟨c, hc⟩ := tx _ (by
        rw [← hxv] at f
        exact fits_restrict_right j4 hu.nodup hx.nodup f)
      rw [hx.holds_restrict] at hc
      exact ⟨f, ha, true, c, hp, hc, rfl⟩
    · obtain ⟨c, hc⟩ := tv _ (fits_restrict_right j3 hu.nodup hv.nodup f)
      rw [hv.holds_restrict] at hc
      exact ⟨f, ha, c, true, hc, hq, by simp⟩

/-! ## σ -/

theorem select_comm {p q : Term} {u uq up w w' : Unrel} (h₁ : u.select q = .ok uq)
    (h₂ : uq.select p = .ok w) (h₃ : u.select p = .ok up) (h₄ : up.select q = .ok w') :
    Same w w' := fun t => by
  rw [select_holds h₂, select_holds h₁, select_holds h₄, select_holds h₃, and_assoc, and_assoc,
    and_comm (a := q.holds t = .ok true)]

theorem select_idem {p : Term} {u up w : Unrel} (h₁ : u.select p = .ok up)
    (h₂ : up.select p = .ok w) : Same w up := fun t => by
  rw [select_holds h₂, select_holds h₁, and_assoc, and_self]

theorem select_union {p : Term} {u v x w w' up vp : Unrel} (tu : u.Total) (tv : v.Total)
    (hp : ∀ t, t.Fits u.heading → ∃ b, p.holds t = .ok b)
    (h₁ : u.union v = .ok x) (h₂ : x.select p = .ok w) (h₃ : u.select p = .ok up)
    (h₄ : v.select p = .ok vp) (h₅ : up.union vp = .ok w') : Same w w' := fun t => by
  have hs := (Unrel.union_heading h₁).1
  have hpv : ∀ t, t.Fits v.heading → ∃ b, p.holds t = .ok b := fun t f => hp t (hs.fits.mpr f)
  rw [select_holds h₂, union_holds h₁ tu tv, union_holds h₅ (select_total h₃ tu hp)
    (select_total h₄ tv hpv), select_holds h₃, select_holds h₄, or_and_right]

theorem select_diff {p : Term} {u v d w w' up : Unrel} (tv : v.Total)
    (h₁ : u.diff v = .ok d) (h₂ : d.select p = .ok w) (h₃ : u.select p = .ok up)
    (h₄ : up.diff v = .ok w') : Same w w' := fun t => by
  rw [select_holds h₂, diff_holds h₁ tv, diff_holds h₄ tv, select_holds h₃, and_assoc, and_assoc,
    and_comm (a := ¬ v.Holds t)]

/-! ## ρ -/

/-- ρ distributes over ∪. -/
theorem rename_union {ren : List (String × String)} {u v x w ρu ρv w' : Unrel}
    (hu : u.WF) (hv : v.WF) (tu : u.Total) (tv : v.Total)
    (h₁ : u.union v = .ok x) (h₂ : x.rename ren = .ok w) (h₃ : u.rename ren = .ok ρu)
    (h₄ : v.rename ren = .ok ρv) (h₅ : ρu.union ρv = .ok w') : Same w w' := fun t => by
  have hx := union_wf h₁ hu hv
  obtain ⟨hs, hxh, _⟩ := Unrel.union_heading h₁
  have hρs := (Unrel.union_heading h₅).1
  rw [union_holds h₅ (rename_total h₃ hu tu) (rename_total h₄ hv tv)]
  by_cases f : t.Fits w.heading
  · obtain ⟨s, fs, rfl⟩ := rename_onto h₂ hx f
    rw [hxh] at fs
    rw [rename_holds h₂ hx (hxh ▸ fs), union_holds h₁ tu tv, rename_holds h₃ hu fs,
      rename_holds h₄ hv (hs.fits.mp fs)]
  · have hw : w.heading = ρu.heading := by
      rw [(rename_eq h₂).2, (rename_eq h₃).2, hxh]
    constructor
    · intro h; exact absurd h.1 f
    · rintro (h | h)
      · exact absurd (hw ▸ h.1) f
      · exact absurd (hw ▸ hρs.fits.mpr h.1) f

/-! ## π -/

/-- π distributes over ∪, when every operation succeeds. -/
theorem project_union {as : List String} {u v x w pu pv w' : Unrel} (hu : u.WF) (hv : v.WF)
    (tu : u.Total) (tv : v.Total) (h₁ : u.union v = .ok x) (h₂ : x.project as = .ok w)
    (h₃ : u.project as = .ok pu) (h₄ : v.project as = .ok pv) (h₅ : pu.union pv = .ok w') :
    Same w w' := fun t => by
  have sx := project_sound h₂ (union_wf h₁ hu hv) (union_total h₁ tu tv)
  have su := project_sound h₃ hu tu
  have sv := project_sound h₄ hv tv
  rw [sx.2.2, union_holds h₅ su.2.1 sv.2.1, su.2.2, sv.2.2]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rcases (union_holds h₁ tu tv s).mp hs with h | h
    · exact Or.inl ⟨s, h, rfl⟩
    · exact Or.inr ⟨s, h, rfl⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact ⟨s, (union_holds h₁ tu tv s).mpr (Or.inl hs), rfl⟩
    · exact ⟨s, (union_holds h₁ tu tv s).mpr (Or.inr hs), rfl⟩

/-! ## Finite relations into unrestricted ones -/

theorem toUnrel_union {r s q : Finrel} (hr : r.WF) (hs : s.WF) (hm : r.heading.Unmixed)
    (hms : s.heading.Unmixed) (h : r.union s = .ok q) {w : Unrel}
    (h' : r.toUnrel.union s.toUnrel = .ok w) : Same q.toUnrel w := fun t => by
  have hq := Finrel.union_wf h hr hs
  have hqm : q.heading.Unmixed := by rw [Rasso.union_heading h]; exact hm
  rw [Finrel.toUnrel_holds hq hqm, Finrel.mem_union h,
    union_holds h' (Finrel.toUnrel_total hr hm) (Finrel.toUnrel_total hs hms),
    Finrel.toUnrel_holds hr hm, Finrel.toUnrel_holds hs hms]

theorem toUnrel_diff {r s q : Finrel} (hr : r.WF) (hs : s.WF) (hm : r.heading.Unmixed)
    (hms : s.heading.Unmixed) (h : r.diff s = .ok q) {w : Unrel}
    (h' : r.toUnrel.diff s.toUnrel = .ok w) : Same q.toUnrel w := fun t => by
  have hq := Finrel.diff_wf h hr
  have hqm : q.heading.Unmixed := by rw [Rasso.diff_heading h]; exact hm
  rw [Finrel.toUnrel_holds hq hqm, Finrel.mem_diff h, diff_holds h' (Finrel.toUnrel_total hs hms),
    Finrel.toUnrel_holds hr hm, Finrel.toUnrel_holds hs hms]

end UnrelLaws
end Rasso
