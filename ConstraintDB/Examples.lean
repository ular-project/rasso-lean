import ConstraintDB.Discrete

/-!
# Examples over the rationals

Lean's `Rat` is a dense linear order without endpoints, so the Goldin–Kanellakis
algebra and its closed-form theorem apply to it.
-/

namespace ConstraintDB

open Lean (Name)

instance : DenseOrder Rat where
  lt_irrefl a := by grind
  lt_trans := by grind
  lt_trichotomy a b := by grind
  dense {a b} h := ⟨(a + b) / 2, by grind, by grind⟩
  no_max a := ⟨a + 1, by grind⟩
  no_min a := ⟨a - 1, by grind⟩
  inhabited := 0

section
open CAlg

/-- `x < z ∧ z < y`. -/
private def between : CAlg Rat := .rel [[⟨.lt, .var `x, .var `z⟩, ⟨.lt, .var `z, .var `y⟩]]

/-- Projecting `z` away from `x < z < y` gives `x < y`. -/
example : (CAlg.project [`z] between).toGRel = [[⟨.lt, .var `x, .var `y⟩]] := by decide

/-- Lower and upper bounds that meet only non-strictly: `x ≤ z ∧ z ≤ 3` projects to `x ≤ 3`. -/
example : (CAlg.project (D := Rat) [`z]
    (.rel [[⟨.le, .var `x, .var `z⟩, ⟨.le, .var `z, .const (3 : Rat)⟩]])).toGRel =
    [[⟨.le, .var `x, .const 3⟩]] := by decide

/-- A definition `z = y` is substituted. -/
example : (CAlg.project (D := Rat) [`z]
    (.rel [[⟨.lt, .var `x, .var `z⟩, ⟨.eq, .var `z, .var `y⟩]])).toGRel =
    [[⟨.lt, .var `x, .var `y⟩, ⟨.eq, .var `y, .var `y⟩]] := by decide

/-- Over `Rat` the meaning of the projection is `∃ z. x < z < y`, by the closed-form
theorem; at `x = 0`, `y = 1` the witness is `1/2`. -/
example : (CAlg.project [`z] between).eval (fun n => if n = `y then 1 else 0) :=
  (closed_form _ _).1 (by
    rw [show (CAlg.project [`z] between).toGRel = [[⟨.lt, .var `x, .var `y⟩]] by decide]
    refine ⟨_, List.mem_singleton_self _, fun a ha => ?_⟩
    simp only [List.mem_singleton] at ha; subst ha
    show ((if (`x : Name) = `y then 1 else 0 : Rat)) < (if (`y : Name) = `y then 1 else 0 : Rat)
    decide)

end

end ConstraintDB
