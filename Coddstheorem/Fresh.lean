import Coddstheorem.Schema

/-!
# Codd's theorem for Rasso: fresh variable names

The algebra-to-calculus translation binds a variable for each attribute that π drops.
It names it `fresh k a = "%" ++ a ++ "%" ++ "#…#"` (`k` copies of `#`): the attribute's
own name, marked with `%`, and the depth `k` of the π in the expression. Two facts make
these names safe:

* no Rasso name (`isAttribute`) is a fresh name, since a Rasso name has no `%`;
* `fresh k a = fresh j b` only when `k = j` and `a = b` (for Rasso names `a`, `b`).
-/

namespace Coddstheorem

open Rasso

/-- The variable π binds for the dropped attribute `a` at depth `k`. -/
def fresh (k : Nat) (a : String) : String :=
  "%" ++ a ++ "%" ++ String.ofList (List.replicate k '#')

theorem fresh_toList (k : Nat) (a : String) :
    (fresh k a).toList = '%' :: (a.toList ++ '%' :: List.replicate k '#') := by
  simp [fresh]

/-- A Rasso name has no `%` in it. -/
theorem no_pct_of_isAttribute {s : String} (h : isAttribute s = true) : '%' ∉ s.toList := by
  intro hm
  unfold isAttribute at h
  split at h
  · rename_i e; rw [e] at hm; cases hm
  · rename_i c cs e
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    rw [e] at hm
    cases hm with
    | head => have := h.1.1; revert this; decide
    | tail _ hm' => have := h.1.2 '%' hm'; revert this; decide

theorem isAttribute_ne_fresh {s : String} (h : isAttribute s = true) (k : Nat) (a : String) :
    s ≠ fresh k a := by
  intro e
  apply no_pct_of_isAttribute h
  rw [e, fresh_toList]; exact List.mem_cons_self

theorem split_pct : ∀ {a b x y : List Char}, '%' ∉ a → '%' ∉ b →
    a ++ '%' :: x = b ++ '%' :: y → a = b ∧ x = y
  | [], [], _, _, _, _, h => by simpa using h
  | [], c :: b, _, _, _, hb, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hb
  | c :: a, [], _, _, ha, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) ha
  | c :: a, d :: b, _, _, ha, hb, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨e1, e2⟩ := split_pct (fun m => ha (List.mem_cons_of_mem _ m))
      (fun m => hb (List.mem_cons_of_mem _ m)) h
    exact ⟨by rw [e1], e2⟩

theorem fresh_inj {k j : Nat} {a b : String} (ha : isAttribute a = true)
    (hb : isAttribute b = true) (h : fresh k a = fresh j b) : k = j ∧ a = b := by
  have h' := congrArg String.toList h
  rw [fresh_toList, fresh_toList, List.cons.injEq] at h'
  obtain ⟨e1, e2⟩ := split_pct (no_pct_of_isAttribute ha) (no_pct_of_isAttribute hb) h'.2
  refine ⟨?_, String.toList_inj.mp e1⟩
  have := congrArg List.length e2
  simpa using this

end Coddstheorem
