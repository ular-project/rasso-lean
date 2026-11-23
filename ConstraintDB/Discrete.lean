import ConstraintDB.Algebra

/-!
# Where projection breaks: order constraints over `Int`

The same constraint language (`<`, `≤`, `=` between attributes and constants) over a
*discrete* order behaves differently under projection.

* `elim_wrong_over_int`: the elimination step that is correct over a dense order
  (`elim_spec`) is wrong over `Int`: eliminating `z` from `x < z ∧ z < y` gives
  `x < y`, but no integer lies strictly between 0 and 1.
* `int_not_closed`: worse, no generalized relation of order constraints over `Int`
  represents `∃ z. x < z ∧ z < y` at all. Far above every constant, a quantifier-free
  order constraint cannot tell `y = x + 1` from `y = x + 2`. So the class of order
  constraints over `Int` is **not closed under projection**, while over a dense order
  it is (`CAlg.closed_form`).

This answers, for one pair of classes, which constraint languages admit projection.
Over `Int`, the projection of the example is `x + 1 < y`, which no order constraint can
write; closure needs a larger constraint language.
-/

namespace ConstraintDB

open Lean (Name)

private def x : Name := `x
private def y : Name := `y
private def z : Name := `z

/-- The elimination step is wrong over `Int`. -/
theorem elim_wrong_over_int :
    ∃ (g : GTuple (Atom Int)) (v : Val Int),
      GRel.Sat (elim z g) v ∧ ¬ ∃ d, GTuple.Sat g (v.upd z d) := by
  refine ⟨[⟨.lt, .var x, .var z⟩, ⟨.lt, .var z, .var y⟩], fun n => if n = y then 1 else 0, ?_, ?_⟩
  · refine ⟨[⟨.lt, .var x, .var y⟩], ?_, ?_⟩
    · show _ ∈ elim z _
      decide
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst ha
      show ((fun n => if n = y then (1 : Int) else 0) x) < (fun n => if n = y then (1 : Int) else 0) y
      simp only [show x ≠ y by decide, ↓reduceIte]; decide
  · rintro ⟨d, hd⟩
    have h₁ := hd _ (List.mem_cons_self ..)
    have h₂ := hd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only [sat_def, Cmp.holds, Term.val, Val.upd, show x ≠ z by decide, show y ≠ z by decide,
      show x ≠ y by decide, ↓reduceIte] at h₁ h₂
    omega

/-! ## No generalized relation over `Int` represents `∃ z. x < z < y` -/

/-- The constants of a term, atom, tuple, relation. -/
def Term.consts {D : Type} : Term D → List D
  | .var _ => []
  | .const c => [c]

def Atom.consts {D : Type} (a : Atom D) : List D := a.l.consts ++ a.r.consts

def GRel.consts {D : Type} (r : GRel (Atom D)) : List D := r.flatMap (·.flatMap Atom.consts)

/-- A bound above every constant (and above 0). -/
def bigInt (cs : List Int) : Int := 1 + (cs.map Int.natAbs).sum

theorem lt_bigInt {cs : List Int} {c : Int} (h : c ∈ cs) : c < bigInt cs := by
  unfold bigInt
  have : c.natAbs ≤ (cs.map Int.natAbs).sum := by
    induction cs with
    | nil => simp at h
    | cons d ds ih =>
      simp only [List.mem_cons] at h
      simp only [List.map_cons, List.sum_cons]
      rcases h with rfl | h
      · omega
      · have := ih h; omega
  omega

theorem zero_lt_bigInt (cs : List Int) : 0 < bigInt cs := by
  unfold bigInt; omega

/-- The point with `x = N`, `y = N + k`, every other name 0. -/
def pt (N k : Int) : Val Int := fun n => if n = y then N + k else if n = x then N else 0

/-- Far above all constants, raising `y` from `N + 1` to `N + 2` changes no atom. -/
theorem sat_pt_iff {N : Int} (a : Atom Int) (hN : ∀ c ∈ a.consts, c < N) (h0 : 0 < N) :
    Constraint.sat a (pt N 1) ↔ Constraint.sat a (pt N 2) := by
  obtain ⟨cmp, l, r⟩ := a
  simp only [Atom.consts, Term.consts, List.mem_append] at hN
  rw [sat_def, sat_def]
  cases l <;> cases r <;> cases cmp <;>
    simp only [Term.val, pt, Cmp.holds, List.not_mem_nil, false_or, or_false, List.mem_singleton,
      forall_eq, forall_eq_or_imp] at hN ⊢ <;>
    (repeat' split) <;> constructor <;> intro <;> omega

theorem int_not_closed :
    ¬ ∃ r : GRel (Atom Int), ∀ v, GRel.Sat r v ↔ ∃ d, v x < d ∧ d < v y := by
  rintro ⟨r, hr⟩
  let N := bigInt r.consts
  have hN : ∀ g ∈ r, ∀ a ∈ g, ∀ c ∈ a.consts, c < N := fun g hg a ha c hc =>
    lt_bigInt (List.mem_flatMap.2 ⟨g, hg, List.mem_flatMap.2 ⟨a, ha, hc⟩⟩)
  have h0 : 0 < N := zero_lt_bigInt _
  have same : GRel.Sat r (pt N 1) ↔ GRel.Sat r (pt N 2) := by
    simp only [GRel.Sat, GTuple.Sat]
    constructor
    · rintro ⟨g, hg, hs⟩
      exact ⟨g, hg, fun a ha => (sat_pt_iff a (hN g hg a ha) h0).1 (hs a ha)⟩
    · rintro ⟨g, hg, hs⟩
      exact ⟨g, hg, fun a ha => (sat_pt_iff a (hN g hg a ha) h0).2 (hs a ha)⟩
  have hx : ∀ k, pt N k x = N := fun k => by simp [pt, show x ≠ y by decide]
  have hy : ∀ k, pt N k y = N + k := fun k => by simp [pt]
  have two : GRel.Sat r (pt N 2) := (hr _).2 ⟨N + 1, by rw [hx]; omega, by rw [hy]; omega⟩
  obtain ⟨d, h₁, h₂⟩ := (hr _).1 (same.2 two)
  rw [hx] at h₁; rw [hy] at h₂
  omega

end ConstraintDB
