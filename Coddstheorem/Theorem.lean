import Coddstheorem.AlgebraToCalculus
import Coddstheorem.CalculusToAlgebra

/-!
# Codd's theorem for Rasso (theorem C)

In plain words: over a schema whose attributes all have one domain `D`, three ways of
asking a question define the same queries. This is the Equivalence Theorem of Codd
(1972) and of Abiteboul, Hull and Vianu (1995, Theorem 5.3.10), here for the calculus
with order comparisons:

1. the algebra: Rasso's σ, π, ρ, ⋈, ∪, −, ×, ∩ and constant relations (`CRA`), run by
   Rasso's own evaluator;
2. the calculus under **active-domain** semantics: quantifiers range over the values in
   the database and in the query;
3. the **domain-independent** calculus under the natural reading: quantifiers range over
   any domain that holds the active domain, everything included, and the answers do not
   depend on which.

"Define the same queries" is stated with a *query meaning* `F : Env → Tuple → Prop`
(on each database, which tuples are answers) and an output heading `as`: a meaning is
definable in a language when some well-typed query of it has heading `as` and gives
exactly `F` on every database of the schema.

Theorem C is A and B put together:

* algebra → domain-independent calculus: `CRA.toCalc` (theorem A);
* domain-independent → active-domain: take the active domain as the domain;
* active-domain → algebra: `Query.toRA` (theorem B).

## Assumptions

* One domain `D` for the whole schema, with `DomOK D` (no int or rat beside a float, so Rasso's
  `=` never refuses); the schema is well formed (`Schema.WF`).
* The calculus side is `Query.WT`: atoms as the schema has them, output attributes
  distinct Rasso names, free variables among the output variables, and **constants in
  `D`**. The last is needed: `{x | x = 1.5}` is domain independent, but with `D = int` no
  algebra query can hold `1.5`, because Rasso's ω refuses it.
* The algebra side is well typed (`CRA.check S D e = some as`). Its answers are those of
  Rasso's evaluator with no targets; theorem A shows it never refuses on a conforming
  database, so `CRA.answers` hides no refusal.
-/

namespace Coddstheorem

open Rasso

/-- The tuples Rasso's evaluator gives for `e` on `env` (none, if it refuses). -/
def CRA.answers (D : Domain) (env : Env) (e : CRA) (t : Tuple) : Prop :=
  ∃ r, Expr.eval env [] (e.toExpr D) = .ok (.finrel r) ∧ t ∈ r.tuples

/-- `F` is the meaning of a well-typed algebra query with attributes `as`: on every
database of the schema, Rasso's evaluator runs it without refusing and gives a relation
with heading `as` (each attribute with domain `D`, up to order) whose tuples are `F`. -/
def AlgDefinable (S : Schema) (D : Domain) (as : List String) (F : Env → Tuple → Prop) : Prop :=
  ∃ e : CRA, e.check S D = some as ∧
    ∀ env, Conforms S D env → ∃ r, Expr.eval env [] (e.toExpr D) = .ok (.finrel r) ∧
      (∀ a, r.heading.lookup a = (headerOf D as).lookup a) ∧ ∀ t, F env t ↔ t ∈ r.tuples

/-- `F` is the meaning of a well-typed calculus query with heading `as`, under
active-domain semantics. -/
def ActiveDefinable (S : Schema) (D : Domain) (as : List String) (F : Env → Tuple → Prop) :
    Prop :=
  ∃ q : Query, q.WT S D ∧ q.out.map (·.1) = as ∧
    ∀ env, Conforms S D env → ∀ t, F env t ↔ q.answers (· ∈ q.adom S env) S env t

/-- `F` is the meaning of a well-typed, domain-independent calculus query with heading
`as`, under any domain holding the active domain (the unbounded one included). -/
def DIDefinable (S : Schema) (D : Domain) (as : List String) (F : Env → Tuple → Prop) : Prop :=
  ∃ q : Query, q.WT S D ∧ q.out.map (·.1) = as ∧ q.DomainIndependent S D ∧
    ∀ env, Conforms S D env → ∀ dom : Value → Prop, (∀ v ∈ q.adom S env, dom v) →
      ∀ t, F env t ↔ q.answers dom S env t

section TheoremC

variable {S : Schema} {D : Domain}

theorem toCalc_heading {e : CRA} {as : List String} (he : e.check S D = some as) :
    (e.toCalc S D).out.map (·.1) = as := by
  simp [CRA.toCalc, he, List.map_map, Function.comp_def]

/-- Theorem A, restated: a well-typed algebra query's answers are those of a well-typed,
domain-independent calculus query with the same heading, under any domain holding the
active domain. -/
theorem alg_to_di (hS : S.WF) (hD : DomOK D = true) {as : List String} {F : Env → Tuple → Prop}
    (h : AlgDefinable S D as F) : DIDefinable S D as F := by
  obtain ⟨e, he, hF⟩ := h
  refine ⟨e.toCalc S D, toCalc_WT hS he, toCalc_heading he, toCalc_domainIndependent hS hD he,
    fun env henv dom hdom t => ?_⟩
  obtain ⟨r, hev, -, -, hr⟩ := algebra_to_calculus hS hD he henv
  obtain ⟨r', hev', -, hF'⟩ := hF env henv
  rw [hev] at hev'
  cases hev'
  rw [hF' t, hr dom hdom t]

/-- Domain independent gives active domain: take the active domain as the domain. -/
theorem di_to_active {as : List String} {F : Env → Tuple → Prop} (h : DIDefinable S D as F) :
    ActiveDefinable S D as F := by
  obtain ⟨q, hq, hh, -, hF⟩ := h
  exact ⟨q, hq, hh, fun env henv => hF env henv _ fun _ hv => hv⟩

/-- Theorem B, restated: an active-domain calculus query's answers are those of a
well-typed algebra query with the same heading. -/
theorem active_to_alg (hS : S.WF) (hD : DomOK D = true) {as : List String}
    {F : Env → Tuple → Prop} (h : ActiveDefinable S D as F) : AlgDefinable S D as F := by
  obtain ⟨q, hq, hh, hF⟩ := h
  obtain ⟨hc, hev⟩ := calculus_to_algebra hS hD hq
  refine ⟨q.toRA S, hh ▸ hc, fun env henv => ?_⟩
  obtain ⟨r, he, -, hh', hr⟩ := hev env henv
  exact ⟨r, he, hh ▸ hh', fun t => (hF env henv t).trans (hr t).symm⟩

/-- **Codd's theorem** (theorem C). Over a well-formed schema with one domain `D`
(`DomOK D`), a query meaning with output heading `as` is definable in the algebra iff it
is definable in the active-domain calculus, iff it is definable in the domain-independent
calculus. -/
theorem codd (hS : S.WF) (hD : DomOK D = true) (as : List String) (F : Env → Tuple → Prop) :
    (AlgDefinable S D as F ↔ ActiveDefinable S D as F) ∧
    (ActiveDefinable S D as F ↔ DIDefinable S D as F) :=
  ⟨⟨fun h => di_to_active (alg_to_di hS hD h), active_to_alg hS hD⟩,
   ⟨fun h => alg_to_di hS hD (active_to_alg hS hD h), di_to_active⟩⟩

/-- Every well-typed algebra query is domain independent: its answers are those of
`e.toCalc`, a domain-independent query, under every domain holding the active domain
(the unbounded one included). -/
theorem algebra_domainIndependent (hS : S.WF) (hD : DomOK D = true) {e : CRA}
    {as : List String} (he : e.check S D = some as) :
    (e.toCalc S D).DomainIndependent S D ∧
    ∀ env, Conforms S D env → ∀ dom : Value → Prop, (∀ v ∈ (e.toCalc S D).adom S env, dom v) →
      ∀ t, CRA.answers D env e t ↔ (e.toCalc S D).answers dom S env t := by
  exact ⟨toCalc_domainIndependent hS hD he, fun env henv dom hdom t => by
    obtain ⟨r, hev, -, -, hr⟩ := algebra_to_calculus hS hD he henv
    rw [← hr dom hdom t]
    constructor
    · rintro ⟨r', hev', ht⟩; rw [hev] at hev'; cases hev'; exact ht
    · exact fun ht => ⟨r, hev, ht⟩⟩

/-- For a domain-independent calculus query, `toRA` gives its natural answers: those
under any domain holding the active domain, the unbounded one included. -/
theorem toRA_natural (hS : S.WF) (hD : DomOK D = true) {q : Query} (hq : q.WT S D)
    (hdi : q.DomainIndependent S D) (env : Env) (henv : Conforms S D env)
    (dom : Value → Prop) (hdom : ∀ v ∈ q.adom S env, dom v) (t : Tuple) :
    CRA.answers D env (q.toRA S) t ↔ q.answers dom S env t := by
  obtain ⟨-, hev⟩ := calculus_to_algebra hS hD hq
  obtain ⟨r, he, -, -, hr⟩ := hev env henv
  rw [hdi env henv dom hdom t, ← hr t]
  constructor
  · rintro ⟨r', he', ht⟩; rw [he] at he'; cases he'; exact ht
  · exact fun ht => ⟨r, he, ht⟩

end TheoremC

end Coddstheorem
