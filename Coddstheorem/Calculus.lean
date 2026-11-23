import Coddstheorem.Schema

/-!
# Codd's theorem for Rasso: the relational calculus

The **domain relational calculus** (Codd 1972; Abiteboul, Hull and Vianu 1995, §5.3),
with order comparisons added to its equality atoms. Variables stand for values.

In plain words:

* A **formula** is built from atoms `R(x₁, …, xₙ)` ("the stored relation `R` has a tuple
  whose attributes, in the schema's order, hold the values of `x₁, …, xₙ`"), `x = y`,
  `x = c` (a constant), the order comparisons `x < y`, `x < c` (and `<=`, `>`, `>=`), with `not`, `and`, `or`, `∃ x`, `∀ x`.
* **Satisfaction** `Sat dom S env φ ρ` reads `φ` on the database `env` with the
  assignment `ρ` (a value for each variable), the quantifiers ranging over `dom`. `dom` is
  any set of values (a predicate), so one definition gives every semantics: the
  active-domain semantics (`dom` = the active domain), the natural one (`dom` = every
  value), and everything between.
* A **query** has an output heading, (attribute, variable) pairs, and a formula. Its
  **answers** are the tuples whose attribute `a` holds the value of its variable, for an
  assignment that satisfies the formula, each output variable's value in `dom`.
* A query is **domain independent** when, on every database, its answers are the same
  under every domain that contains the active domain.
* `Query.answersList` lists the answers when the domain is a list, and
  `mem_answersList` proves the list is exactly `Query.answers`, so the examples check
  the real meaning.

Conventions:

* Positional atoms in the schema's attribute order.
* No true or false: `∀ z. z = z` and `¬ ∀ z. z = z` are true and false on every
  domain, the empty one included.
* A query's output is a heading of (attribute, variable) pairs, attributes distinct; a
  variable may stand for two attributes. Only the output variables' values
  are constrained to `dom`: the assignment is a total function, and only the free
  variables matter (`Sat_congr`).
* Equality is equality of Rasso values (`=` on `Value`), not Rasso's `=` operator,
  which refuses an int or a rat against a float; `DomOK` makes the two agree on the values a query
  meets. The order comparisons are read by Rasso's own value order
  (`Cmp.holds`, from `Value.cmp`), which never refuses. It puts ints and floats together
  as numbers, so `x <= y ∧ y <= x` need not give `x = y` (int 1 and float 1.0); each atom
  is read on its own, so nothing relies on that.
-/

namespace Coddstheorem

open Rasso

/-- Formulas of the domain relational calculus. -/
inductive Formula where
  /-- `R(x₁, …, xₙ)`, positional in the schema's attribute order. -/
  | rel (R : String) (xs : List String)
  | eqv (x y : String)
  | eqc (x : String) (c : Value)
  /-- `x < y` (and `<=`, `>`, `>=`), read by Rasso's value order. -/
  | cmpv (o : Cmp) (x y : String)
  /-- `x < c` (and `<=`, `>`, `>=`); `c < x` is written `x > c`. -/
  | cmpc (o : Cmp) (x : String) (c : Value)
  | not (φ : Formula)
  | and (φ ψ : Formula)
  | or (φ ψ : Formula)
  | ex (x : String) (φ : Formula)
  | all (x : String) (φ : Formula)
  deriving Repr, Inhabited, DecidableEq

/-- Update an assignment at one variable. -/
def upd (ρ : String → Value) (x : String) (a : Value) : String → Value :=
  fun y => if y = x then a else ρ y

@[simp] theorem upd_same (ρ : String → Value) (x : String) (a : Value) : upd ρ x a x = a := by
  simp [upd]

theorem upd_other {ρ : String → Value} {x y : String} {a : Value} (h : y ≠ x) :
    upd ρ x a y = ρ y := by
  simp [upd, h]

namespace Formula

/-- Free variables (repeats allowed; only membership matters). -/
def fv : Formula → List String
  | rel _ xs => xs
  | eqv x y | cmpv _ x y => [x, y]
  | eqc x _ | cmpc _ x _ => [x]
  | not φ => φ.fv
  | and φ ψ => φ.fv ++ ψ.fv
  | or φ ψ => φ.fv ++ ψ.fv
  | ex x φ => φ.fv.filter (· != x)
  | all x φ => φ.fv.filter (· != x)

/-- The constants. -/
def consts : Formula → List Value
  | rel _ _ | eqv _ _ | cmpv _ _ _ => []
  | eqc _ c | cmpc _ _ c => [c]
  | not φ | ex _ φ | all _ φ => φ.consts
  | and φ ψ | or φ ψ => φ.consts ++ ψ.consts

/-- Well typed for a schema: every atom names a stored relation, with its arity. -/
def WT (S : Schema) : Formula → Bool
  | rel R xs => (S.lookup R).isSome && xs.length == (S.attrsOf R).length
  | eqv _ _ | eqc _ _ | cmpv _ _ _ | cmpc _ _ _ => true
  | not φ | ex _ φ | all _ φ => φ.WT S
  | and φ ψ | or φ ψ => φ.WT S && ψ.WT S

/-- The atom `R(xs)` holds under `ρ`: some stored tuple has, at the schema's `i`-th
attribute, the value of the `i`-th variable. -/
def AtomHolds (S : Schema) (env : Env) (R : String) (xs : List String)
    (ρ : String → Value) : Prop :=
  ∃ t ∈ tuplesOf env R, ∀ p ∈ (S.attrsOf R).zip xs, t.get? p.1 = some (ρ p.2)

instance (S : Schema) (env : Env) (R : String) (xs : List String) (ρ : String → Value) :
    Decidable (AtomHolds S env R xs ρ) :=
  inferInstanceAs (Decidable (∃ t ∈ _, _))

/-- Satisfaction, with the quantifiers ranging over `dom`. -/
def Sat (dom : Value → Prop) (S : Schema) (env : Env) : Formula → (String → Value) → Prop
  | rel R xs, ρ => AtomHolds S env R xs ρ
  | eqv x y, ρ => ρ x = ρ y
  | eqc x c, ρ => ρ x = c
  | cmpv o x y, ρ => o.holds (ρ x) (ρ y) = true
  | cmpc o x c, ρ => o.holds (ρ x) c = true
  | not φ, ρ => ¬ Sat dom S env φ ρ
  | and φ ψ, ρ => Sat dom S env φ ρ ∧ Sat dom S env ψ ρ
  | or φ ψ, ρ => Sat dom S env φ ρ ∨ Sat dom S env ψ ρ
  | ex x φ, ρ => ∃ a, dom a ∧ Sat dom S env φ (upd ρ x a)
  | all x φ, ρ => ∀ a, dom a → Sat dom S env φ (upd ρ x a)

/-- Satisfaction is decidable when the domain is a finite list. -/
instance decSat (l : List Value) (S : Schema) (env : Env) :
    (φ : Formula) → (ρ : String → Value) → Decidable (Sat (· ∈ l) S env φ ρ)
  | rel _ _, _ => inferInstanceAs (Decidable (AtomHolds ..))
  | eqv _ _, _ => inferInstanceAs (Decidable (_ = _))
  | eqc _ _, _ => inferInstanceAs (Decidable (_ = _))
  | cmpv _ _ _, _ => inferInstanceAs (Decidable (_ = _))
  | cmpc _ _ _, _ => inferInstanceAs (Decidable (_ = _))
  | not φ, ρ => @instDecidableNot _ (decSat l S env φ ρ)
  | and φ ψ, ρ => @instDecidableAnd _ _ (decSat l S env φ ρ) (decSat l S env ψ ρ)
  | or φ ψ, ρ => @instDecidableOr _ _ (decSat l S env φ ρ) (decSat l S env ψ ρ)
  | ex x φ, ρ =>
    have : ∀ a, Decidable (Sat (· ∈ l) S env φ (upd ρ x a)) := fun _ => decSat l S env φ _
    decidable_of_iff (∃ a ∈ l, Sat (· ∈ l) S env φ (upd ρ x a)) (by simp [Sat])
  | all x φ, ρ =>
    have : ∀ a, Decidable (Sat (· ∈ l) S env φ (upd ρ x a)) := fun _ => decSat l S env φ _
    decidable_of_iff (∀ a ∈ l, Sat (· ∈ l) S env φ (upd ρ x a)) (by simp [Sat])

/-- Updating two assignments that agree off `x` keeps them agreeing on a quantified
formula's body. -/
theorem upd_agree {ρ ρ' : String → Value} {x : String} {a : Value} {xs : List String}
    (h : ∀ y ∈ xs.filter (· != x), ρ y = ρ' y) : ∀ y ∈ xs, upd ρ x a y = upd ρ' x a y := by
  intro y hy
  if hyx : y = x then
    subst hyx; rw [upd_same, upd_same]
  else
    rw [upd_other hyx, upd_other hyx]
    exact h y (List.mem_filter.mpr ⟨hy, bne_iff_ne.mpr hyx⟩)

/-- Satisfaction depends only on the free variables. -/
theorem Sat_congr {dom : Value → Prop} {S : Schema} {env : Env} :
    (φ : Formula) → {ρ ρ' : String → Value} → (∀ x ∈ φ.fv, ρ x = ρ' x) →
      (Sat dom S env φ ρ ↔ Sat dom S env φ ρ')
  | rel R xs, ρ, ρ', h => by
    simp only [Sat, AtomHolds]
    constructor
    · rintro ⟨t, ht, hp⟩
      exact ⟨t, ht, fun p hp' => (hp p hp').trans (by rw [h p.2 (List.of_mem_zip hp').2])⟩
    · rintro ⟨t, ht, hp⟩
      exact ⟨t, ht, fun p hp' => (hp p hp').trans (by rw [h p.2 (List.of_mem_zip hp').2])⟩
  | eqv x y, ρ, ρ', h => by
    simp only [Sat]
    rw [h x (by simp [fv]), h y (by simp [fv])]
  | eqc x c, ρ, ρ', h => by
    simp only [Sat]
    rw [h x (by simp [fv])]
  | cmpv o x y, ρ, ρ', h => by
    simp only [Sat]
    rw [h x (by simp [fv]), h y (by simp [fv])]
  | cmpc o x c, ρ, ρ', h => by
    simp only [Sat]
    rw [h x (by simp [fv])]
  | not φ, ρ, ρ', h => by simp only [Sat]; rw [Sat_congr φ h]
  | and φ ψ, ρ, ρ', h => by
    simp only [Sat]
    rw [Sat_congr φ (fun x hx => h x (List.mem_append_left _ hx)),
        Sat_congr ψ (fun x hx => h x (List.mem_append_right _ hx))]
  | or φ ψ, ρ, ρ', h => by
    simp only [Sat]
    rw [Sat_congr φ (fun x hx => h x (List.mem_append_left _ hx)),
        Sat_congr ψ (fun x hx => h x (List.mem_append_right _ hx))]
  | ex x φ, ρ, ρ', h => by
    have e : ∀ a, (Sat dom S env φ (upd ρ x a) ↔ Sat dom S env φ (upd ρ' x a)) := fun _ =>
      Sat_congr φ (upd_agree h)
    simp only [Sat]
    exact ⟨fun ⟨a, ha, s⟩ => ⟨a, ha, (e a).mp s⟩, fun ⟨a, ha, s⟩ => ⟨a, ha, (e a).mpr s⟩⟩
  | all x φ, ρ, ρ', h => by
    have e : ∀ a, (Sat dom S env φ (upd ρ x a) ↔ Sat dom S env φ (upd ρ' x a)) := fun _ =>
      Sat_congr φ (upd_agree h)
    simp only [Sat]
    exact ⟨fun s a ha => (e a).mp (s a ha), fun s a ha => (e a).mpr (s a ha)⟩

end Formula

/-- A calculus query: an output heading of (attribute, variable) pairs, and a formula. -/
structure Query where
  out : List (String × String)
  body : Formula
  deriving Repr, Inhabited

namespace Query

open Formula

/-- The output variables. -/
def vars (q : Query) : List String := q.out.map (·.2)

/-- The tuple an assignment gives: attribute `a` holds the value of its variable, sorted
by attribute as Rasso keeps tuples. -/
def tupleOf (q : Query) (ρ : String → Value) : Tuple :=
  Tuple.ofPairs (q.out.map fun p => (p.1, ρ p.2))

/-- The answers of `q` on `env`, the quantifiers ranging over `dom`. -/
def answers (dom : Value → Prop) (S : Schema) (env : Env) (q : Query) (t : Tuple) : Prop :=
  ∃ ρ : String → Value, (∀ x ∈ q.vars, dom (ρ x)) ∧ t = q.tupleOf ρ ∧ Sat dom S env q.body ρ

/-- Well typed: atoms as the schema has them, constants in `D`, output attributes
distinct Rasso names, free variables among the output variables. -/
def WT (S : Schema) (D : Domain) (q : Query) : Prop :=
  q.body.WT S = true ∧ (∀ c ∈ q.body.consts, D.mem c = true) ∧
  (q.out.map (·.1)).Nodup ∧ (∀ p ∈ q.out, isAttribute p.1 = true) ∧
  ∀ x ∈ q.body.fv, x ∈ q.vars

instance (S : Schema) (D : Domain) (q : Query) : Decidable (q.WT S D) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The active domain of a query on a database: the stored values and the constants. -/
def adom (S : Schema) (env : Env) (q : Query) : List Value :=
  Coddstheorem.adom S env ++ q.body.consts

/-- Domain independence (Abiteboul, Hull and Vianu 1995, Definition 5.3.7): on every
database, the answers under any domain containing the active domain are the
active-domain answers. This is their definition, since they read a query under any
domain d as under d together with the active domain. Undecidable in general (their
Corollary 6.3.2); this is the semantic definition. -/
def DomainIndependent (S : Schema) (D : Domain) (q : Query) : Prop :=
  ∀ env, Conforms S D env → ∀ dom : Value → Prop, (∀ v ∈ q.adom S env, dom v) →
    ∀ t, q.answers dom S env t ↔ q.answers (· ∈ q.adom S env) S env t

/-! ## Listing the answers over a list domain -/

/-- Every way of picking one item of `l` for each of `n` places. -/
def picks (l : List Value) : Nat → List (List Value)
  | 0 => [[]]
  | n + 1 => l.flatMap fun v => (picks l n).map (v :: ·)

theorem mem_picks {l : List Value} : ∀ {n : Nat} {vs : List Value},
    vs ∈ picks l n ↔ vs.length = n ∧ ∀ v ∈ vs, v ∈ l
  | 0, vs => by cases vs <;> simp [picks]
  | n + 1, [] => by simp [picks]
  | n + 1, v :: vs => by
    simp only [picks, List.mem_flatMap, List.mem_map, List.cons.injEq, List.length_cons,
      Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨w, hw, us, hus, rfl, rfl⟩
      exact ⟨(mem_picks.mp hus).1, hw, (mem_picks.mp hus).2⟩
    · rintro ⟨hl, hv, hvs⟩
      exact ⟨v, hv, vs, mem_picks.mpr ⟨hl, hvs⟩, rfl, rfl⟩

/-- The assignment that gives the `i`-th variable the `i`-th value (others: a default). -/
def asg (xs : List String) (vs : List Value) : String → Value :=
  fun x => ((xs.zip vs).lookup x).getD (.bool false)

theorem asg_self {xs : List String} {ρ : String → Value} :
    ∀ {x : String}, x ∈ xs → asg xs (xs.map ρ) x = ρ x := by
  induction xs with
  | nil => intro x h; cases h
  | cons y ys ih =>
    intro x hx
    simp only [asg, List.map_cons, List.zip_cons_cons, List.lookup_cons]
    by_cases e : x = y
    · subst e; simp
    · have : (x == y) = false := by simp [e]
      rw [this]
      exact ih (List.mem_of_ne_of_mem e hx)

theorem asg_mem {xs : List String} {vs : List Value} {l : List Value}
    (hl : vs.length = xs.length) (hv : ∀ v ∈ vs, v ∈ l) : ∀ x ∈ xs, asg xs vs x ∈ l := by
  induction xs generalizing vs with
  | nil => intro x h; cases h
  | cons y ys ih =>
    cases vs with
    | nil => simp at hl
    | cons w ws =>
      intro x hx
      simp only [asg, List.zip_cons_cons, List.lookup_cons]
      by_cases e : x = y
      · subst e; simpa using hv w (by simp)
      · have : (x == y) = false := by simp [e]
        rw [this]
        exact ih (by simpa using hl) (fun v h => hv v (by simp [h])) x
          (List.mem_of_ne_of_mem e hx)

/-- The answers over the list domain `l`: every assignment of values of `l` to the output
variables, kept when the formula holds. -/
def answersList (l : List Value) (S : Schema) (env : Env) (q : Query) : List Tuple :=
  ((picks l q.vars.length).filter fun vs => decide (Sat (· ∈ l) S env q.body (asg q.vars vs))).map
    fun vs => q.tupleOf (asg q.vars vs)

theorem tupleOf_congr (q : Query) {ρ ρ' : String → Value} (h : ∀ x ∈ q.vars, ρ x = ρ' x) :
    q.tupleOf ρ = q.tupleOf ρ' := by
  unfold tupleOf
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [h p.2 (List.mem_map_of_mem hp)]

/-- `answersList` is exactly `answers` over its list domain (for a well-typed query). -/
theorem mem_answersList {l : List Value} {S : Schema} {env : Env} {q : Query}
    (hfv : ∀ x ∈ q.body.fv, x ∈ q.vars) (t : Tuple) :
    t ∈ q.answersList l S env ↔ q.answers (· ∈ l) S env t := by
  simp only [answersList, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨vs, ⟨hvs, hs⟩, rfl⟩
    obtain ⟨hl, hv⟩ := mem_picks.mp hvs
    exact ⟨asg q.vars vs, asg_mem hl hv, rfl, hs⟩
  · rintro ⟨ρ, hρ, rfl, hs⟩
    refine ⟨q.vars.map ρ, ⟨mem_picks.mpr ⟨by simp, ?_⟩, ?_⟩, ?_⟩
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact hρ x hx
    · exact (Sat_congr q.body fun x hx => asg_self (hfv x hx)).mpr hs
    · exact q.tupleOf_congr fun x hx => asg_self hx

end Query

end Coddstheorem
