/-!
# Generalized tuples and generalized relations (KKR, generic part)

This library formalises parts of the constraint databases of Kanellakis, Kuper and
Revesz, *Constraint Query Languages* (KKR), and the constraint algebra of Goldin and
Kanellakis for dense order, so that they can be compared fairly with this project's
universe. This file is KKR's generic part: it fixes neither the domain nor the
constraint class.

Sources:

* P. C. Kanellakis, G. M. Kuper, P. Z. Revesz, *Constraint Query Languages*,
  J. Computer and System Sciences 51(1):26–52 (1995), doi:10.1006/jcss.1995.1051.
  The definitions below are those of §1.1–§1.2.

KKR, Definition 1.3:

1. A *generalized k-tuple* over variables x₁…x_k is a finite conjunction
   φ₁ ∧ … ∧ φ_N of constraints from a fixed class.
2. A *generalized relation* of arity k is a finite set of generalized k-tuples over
   the same variables.
3. Its formula is the disjunction of its tuples' formulas.
4. A *generalized database* is a finite set of generalized relations.

KKR, Definition 1.4: a generalized relation *represents* an **unrestricted relation**,
the possibly infinite set of points that satisfies its formula. KKR §1.2 uses the
term "unrestricted relation" for finite or infinite sets of points, which is the same
term as this project's `Unrel`.

Design principles, not themselves expressible in Lean:

* **Isolation.** Everything in this library lives in the `ConstraintDB` namespace and the `ConstraintDB` Lake
  library. Only `ConstraintDB/RassoEmbedding.lean` imports `Rasso`, and `Rasso` never
  imports this library; CI checks this.
* **A separate universe.** This library's universe is not Rasso's. Generalized relations
  are in disjunctive normal form (Rasso's unrestricted relations need no normal form),
  the domain is a single dense order, and projection is an operator. Only
  `ConstraintDB/RassoEmbedding.lean` states theorems about Rasso.
* **Algebra first.** The formalisation follows Goldin and
  Kanellakis's constraint algebra (`ConstraintDB/Algebra.lean`) rather than the KKR calculus.

Conventions:

* **Abstract constraint classes.** In this file a constraint class is a type `A` of
  atomic constraints with a satisfaction relation `Constraint.sat : A → P → Prop` on
  a type `P` of points. `ConstraintDB/Dense.lean` instantiates it: points are valuations of
  attribute names, atoms are dense order comparisons.
* **Finite sets are lists.** "Finite conjunction" and "finite set" are modelled as
  `List`; order and repeats do not affect the meaning (`GRel.Sat`).
* **Closed form** (KKR §1.1: "the output of any query program applied to any input
  generalized relations must be [a] generalized relation") is modelled per operation
  on unrestricted relations: an operation is closed when its result on represented
  relations is again represented (`ClosedBinary`), and for the algebra as a whole in
  `ConstraintDB/Algebra.lean` (`CAlg.closed_form`).
-/

namespace ConstraintDB

/-- A constraint class: atomic constraints `A`, interpreted at points `P`. -/
class Constraint (A : Type) (P : outParam Type) where
  sat : A → P → Prop

/-- KKR Definition 1.3(1): a generalized tuple, a finite conjunction of constraints. -/
abbrev GTuple (A : Type) := List A

/-- KKR Definition 1.3(2): a generalized relation, a finite set of generalized tuples. -/
abbrev GRel (A : Type) := List (GTuple A)

variable {A P : Type} [Constraint A P]

/-- The point satisfies every constraint of the conjunction. -/
def GTuple.Sat (g : GTuple A) (p : P) : Prop := ∀ a ∈ g, Constraint.sat a p

/-- KKR Definition 1.3(3) and 1.4: the unrestricted relation a generalized relation
represents, as a predicate on points (the disjunction of its tuples). -/
def GRel.Sat (r : GRel A) (p : P) : Prop := ∃ g ∈ r, GTuple.Sat g p

/-- An unrestricted relation (a set of points) is *represented* in the class when some
generalized relation denotes exactly it. -/
def Represented (A : Type) {P : Type} [Constraint A P] (U : P → Prop) : Prop :=
  ∃ r : GRel A, ∀ p, GRel.Sat r p ↔ U p

namespace GRel

/-- The empty generalized relation: no points. -/
def bot : GRel A := []

/-- The relation with one empty conjunction: every point. -/
def top : GRel A := [[]]

/-- Union: the disjunction of both. -/
def union (r s : GRel A) : GRel A := r ++ s

/-- Intersection: pairwise conjunctions, distributing `∧` over `∨`. -/
def inter (r s : GRel A) : GRel A := r.flatMap fun g => s.map fun g' => g ++ g'

theorem sat_bot (p : P) : ¬ GRel.Sat (bot : GRel A) p := by
  simp [GRel.Sat, bot]

theorem sat_top (p : P) : GRel.Sat (top : GRel A) p := by
  refine ⟨[], by simp [top], ?_⟩
  intro a ha; simp at ha

theorem sat_union {r s : GRel A} {p : P} : GRel.Sat (union r s) p ↔ GRel.Sat r p ∨ GRel.Sat s p := by
  simp only [GRel.Sat, union, List.mem_append]
  constructor
  · rintro ⟨g, hg | hg, hs⟩
    · exact .inl ⟨g, hg, hs⟩
    · exact .inr ⟨g, hg, hs⟩
  · rintro (⟨g, hg, hs⟩ | ⟨g, hg, hs⟩)
    · exact ⟨g, .inl hg, hs⟩
    · exact ⟨g, .inr hg, hs⟩

theorem gtuple_sat_append {g g' : GTuple A} {p : P} :
    GTuple.Sat (g ++ g') p ↔ GTuple.Sat g p ∧ GTuple.Sat g' p := by
  simp only [GTuple.Sat, List.mem_append]
  constructor
  · intro h; exact ⟨fun a ha => h a (.inl ha), fun a ha => h a (.inr ha)⟩
  · rintro ⟨h₁, h₂⟩ a (ha | ha)
    · exact h₁ a ha
    · exact h₂ a ha

theorem sat_inter {r s : GRel A} {p : P} : GRel.Sat (inter r s) p ↔ GRel.Sat r p ∧ GRel.Sat s p := by
  simp only [GRel.Sat, inter, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨g, hg, g', hg', rfl⟩, hs⟩
    obtain ⟨h₁, h₂⟩ := gtuple_sat_append.1 hs
    exact ⟨⟨g, hg, h₁⟩, ⟨g', hg', h₂⟩⟩
  · rintro ⟨⟨g, hg, h₁⟩, ⟨g', hg', h₂⟩⟩
    exact ⟨g ++ g', ⟨g, hg, g', hg', rfl⟩, gtuple_sat_append.2 ⟨h₁, h₂⟩⟩

end GRel

/-! ## Negation and difference

KKR's classes are closed under complement of an atomic constraint as a finite
disjunction of conjunctions (for example ¬(x < y) is y ≤ x; ¬(x = y) over an order is
x < y ∨ y < x). A class with this property has generalized relations closed under
complement and difference. -/

/-- The negation of every atom is represented, as a generalized relation. -/
class NegDNF (A : Type) (P : outParam Type) [Constraint A P] where
  neg : A → GRel A
  sat_neg : ∀ (a : A) (p : P), GRel.Sat (neg a) p ↔ ¬ Constraint.sat a p

namespace GRel

variable [NegDNF A P]

/-- The negation of a conjunction: the union of the atoms' negations. -/
def negTuple (g : GTuple A) : GRel A := g.flatMap fun a => NegDNF.neg (P := P) a

/-- Complement: the conjunction, over the tuples, of their negations. -/
def compl : GRel A → GRel A
  | [] => top
  | g :: r => inter (negTuple g) (compl r)

/-- Difference: `r` and not `s`. -/
def diff (r s : GRel A) : GRel A := inter r (compl s)

theorem sat_negTuple {g : GTuple A} {p : P} : GRel.Sat (negTuple g) p ↔ ¬ GTuple.Sat g p := by
  simp only [GRel.Sat, negTuple, List.mem_flatMap, GTuple.Sat]
  constructor
  · rintro ⟨c, ⟨a, ha, hc⟩, hs⟩ hall
    exact (NegDNF.sat_neg a p).1 ⟨c, hc, hs⟩ (hall a ha)
  · intro hn
    have : ∃ a ∈ g, ¬ Constraint.sat a p :=
      Classical.byContradiction fun h => hn fun a ha =>
        Classical.byContradiction fun ha' => h ⟨a, ha, ha'⟩
    obtain ⟨a, ha, hna⟩ := this
    obtain ⟨c, hc, hs⟩ := (NegDNF.sat_neg a p).2 hna
    exact ⟨c, ⟨a, ha, hc⟩, hs⟩

theorem sat_compl : (r : GRel A) → (p : P) → (GRel.Sat (compl r) p ↔ ¬ GRel.Sat r p)
  | [], p => by
    simp only [compl]
    constructor
    · rintro _ ⟨_, h, _⟩; exact nomatch h
    · intro _; exact sat_top p
  | g :: r, p => by
    simp only [compl]
    rw [sat_inter, sat_negTuple, sat_compl r p]
    simp only [GRel.Sat, List.mem_cons]
    constructor
    · rintro ⟨h₁, h₂⟩ ⟨g', hg' | hg', hs⟩
      · subst hg'; exact h₁ hs
      · exact h₂ ⟨g', hg', hs⟩
    · intro h
      exact ⟨fun hs => h ⟨g, .inl rfl, hs⟩, fun ⟨g', hg', hs⟩ => h ⟨g', .inr hg', hs⟩⟩

theorem sat_diff {r s : GRel A} {p : P} : GRel.Sat (diff r s) p ↔ GRel.Sat r p ∧ ¬ GRel.Sat s p := by
  rw [diff, sat_inter, sat_compl]

end GRel

/-! ## Closed form

KKR §1.1: a query language has *closed form* when every query maps generalized
relations to a generalized relation. Here it is stated per operation on unrestricted
relations (predicates on points). -/

/-- A binary operation on unrestricted relations (of one point type) is closed in class `A`. -/
def ClosedBinary (A : Type) {P : Type} [Constraint A P]
    (op : (P → Prop) → (P → Prop) → (P → Prop)) : Prop :=
  ∀ r s : GRel A, Represented A (op (GRel.Sat r) (GRel.Sat s))

theorem closed_union : ClosedBinary A (fun U V p => U p ∨ V p) :=
  fun r s => ⟨GRel.union r s, fun _ => GRel.sat_union⟩

theorem closed_inter : ClosedBinary A (fun U V p => U p ∧ V p) :=
  fun r s => ⟨GRel.inter r s, fun _ => GRel.sat_inter⟩

theorem closed_diff [NegDNF A P] : ClosedBinary A (fun U V p => U p ∧ ¬ V p) :=
  fun r s => ⟨GRel.diff r s, fun _ => GRel.sat_diff⟩

end ConstraintDB
