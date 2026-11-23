import ConstraintDB.Projection

/-!
# The Goldin–Kanellakis constraint algebra (dense order)

Goldin and Kanellakis (GK; Constraints 1996, §3.3) give a relational algebra on
generalized relations of dense order constraints, with the operators projection,
selection, natural join, union, difference and renaming, and show (their Theorem 2)
that it is in closed form: every query maps generalized relations to a generalized
relation that represents the query's answer on the unrestricted relations. They state
(§3) that the algebra's equivalence with the calculus follows from this. That
equivalence is not formalised here.

Here:

* `CAlg D` is the syntax of algebra expressions.
* `CAlg.eval` is the meaning on unrestricted relations (sets of valuations): join is
  `∧`, union `∨`, difference `∧ ¬`, selection `∧` with a constraint, renaming
  substitutes names, projection is `∃`.
* `CAlg.toGRel` computes a generalized relation (in disjunctive normal form) for every
  expression, operator by operator, as the algebra does.
* `closed_form` proves that the computed generalized relation represents the
  expression's meaning, for every dense order `D`.

Where this differs from Rasso:

* Rasso's unrestricted relation is a heading and a term, never put into a normal form,
  and its projection removes an attribute only when a class accepts it. Here every
  intermediate result is a generalized relation in DNF, and projection is an
  operator.

Conventions:

* **No attribute bookkeeping.** Expressions are not indexed by their attribute sets;
  a relation constrains only the names it mentions. Union and difference of
  relations over different attributes are therefore allowed, with the valuation
  meaning. GK require the same attributes.
* **Projection away.** `project zs e` removes the names `zs` (π onto the rest).
* **Renaming** `rename ρ e` gives attribute `n` of `e` the new name `ρ n`; its meaning
  at a valuation `v` is `e` at `v ∘ ρ`.
* **Difference** is computed by complementing in DNF (`GRel.diff`), not by GK's tuple
  difference (§3.3); the represented relation is the same, the size may differ.
-/

namespace ConstraintDB

open Lean (Name)

/-- Constraint algebra expressions over domain `D`. -/
inductive CAlg (D : Type) where
  /-- A stored generalized relation. -/
  | rel : GRel (Atom D) → CAlg D
  /-- σ: keep the points satisfying an atomic constraint. -/
  | select : Atom D → CAlg D → CAlg D
  /-- ⋈: natural join. -/
  | join : CAlg D → CAlg D → CAlg D
  /-- ∪ -/
  | union : CAlg D → CAlg D → CAlg D
  /-- − -/
  | diff : CAlg D → CAlg D → CAlg D
  /-- ρ: attribute `n` is renamed `ρ n`. -/
  | rename : (Name → Name) → CAlg D → CAlg D
  /-- π: remove the listed attributes. -/
  | project : List Name → CAlg D → CAlg D

namespace CAlg

variable {D : Type}

/-- The unrestricted relation an expression denotes. -/
def eval [LT D] : CAlg D → Val D → Prop
  | rel r, v => GRel.Sat r v
  | select a e, v => Constraint.sat a v ∧ e.eval v
  | join e₁ e₂, v => e₁.eval v ∧ e₂.eval v
  | union e₁ e₂, v => e₁.eval v ∨ e₂.eval v
  | diff e₁ e₂, v => e₁.eval v ∧ ¬ e₂.eval v
  | rename ρ e, v => e.eval (v ∘ ρ)
  | project zs e, v => existsAll zs e.eval v

/-- Rename every atom of a generalized relation. -/
def renameGRel (ρ : Name → Name) (r : GRel (Atom D)) : GRel (Atom D) :=
  r.map (·.map (Atom.rename ρ))

theorem sat_renameGRel [LT D] (ρ : Name → Name) (r : GRel (Atom D)) (v : Val D) :
    GRel.Sat (renameGRel ρ r) v ↔ GRel.Sat r (v ∘ ρ) := by
  simp only [GRel.Sat, GTuple.Sat, renameGRel, List.mem_map]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, hs⟩
    exact ⟨g, hg, fun a ha => (sat_rename ρ a v).1 (hs _ (List.mem_map.2 ⟨a, ha, rfl⟩))⟩
  · rintro ⟨g, hg, hs⟩
    refine ⟨_, ⟨g, hg, rfl⟩, fun x hx => ?_⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact (sat_rename ρ a v).2 (hs a ha)

/-- The generalized relation computed for an expression, operator by operator. -/
def toGRel [DenseOrder D] : CAlg D → GRel (Atom D)
  | rel r => r
  | select a e => GRel.inter [[a]] e.toGRel
  | join e₁ e₂ => GRel.inter e₁.toGRel e₂.toGRel
  | union e₁ e₂ => GRel.union e₁.toGRel e₂.toGRel
  | diff e₁ e₂ => GRel.diff e₁.toGRel e₂.toGRel
  | rename ρ e => renameGRel ρ e.toGRel
  | project zs e => GRel.elimAll zs e.toGRel

theorem existsAll_congr [LT D] {U V : Val D → Prop} (h : ∀ v, U v ↔ V v) :
    (zs : List Name) → (v : Val D) → (existsAll zs U v ↔ existsAll zs V v)
  | [], v => h v
  | z :: zs, v => by
    simp only [existsAll]
    exact ⟨fun ⟨d, hd⟩ => ⟨d, (existsAll_congr h zs _).1 hd⟩,
      fun ⟨d, hd⟩ => ⟨d, (existsAll_congr h zs _).2 hd⟩⟩

/-- **Closed form** (GK Theorem 2, for this formulation): the generalized relation
computed for an expression represents the expression's meaning. -/
theorem closed_form [DenseOrder D] : (e : CAlg D) → (v : Val D) →
    (GRel.Sat e.toGRel v ↔ e.eval v)
  | rel r, v => Iff.rfl
  | select a e, v => by
    simp only [toGRel, eval, GRel.sat_inter, closed_form e v]
    simp [GRel.Sat, GTuple.Sat]
  | join e₁ e₂, v => by simp only [toGRel, eval, GRel.sat_inter, closed_form e₁ v, closed_form e₂ v]
  | union e₁ e₂, v => by simp only [toGRel, eval, GRel.sat_union, closed_form e₁ v, closed_form e₂ v]
  | diff e₁ e₂, v => by simp only [toGRel, eval, GRel.sat_diff, closed_form e₁ v, closed_form e₂ v]
  | rename ρ e, v => by simp only [toGRel, eval, sat_renameGRel, closed_form e]
  | project zs e, v => by
    simp only [toGRel, eval, GRel.sat_elimAll]
    exact existsAll_congr (closed_form e) zs v

/-- Every algebra expression denotes a represented unrestricted relation. -/
theorem represented [DenseOrder D] (e : CAlg D) : Represented (Atom D) e.eval :=
  ⟨e.toGRel, closed_form e⟩

end CAlg

end ConstraintDB
