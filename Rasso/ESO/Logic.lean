import Rasso.Value

/-!
# ESO, the logic side: structures, first-order formulas, ESO sentences

This is the logic that the ESO
theorems talk about (Fagin: over finite structures, existential second-order logic
defines exactly the NP properties).

In plain words:

* A **structure** `A` is a finite universe of values and, for each relation symbol, a
  finite list of tuples. A graph is a structure: the universe is its vertices, and one
  symbol `E` holds its edges.
* A **first-order formula** talks about elements: `E(x, y)`, `x = y`, `not`, `and`, `or`,
  `∃ x`, `∀ x`. The quantifiers range over the universe.
* An **ESO sentence** `∃ R₁ … Rₘ. φ` first guesses some relations (the second-order
  variables, each with an arity), and then checks the first-order formula `φ`.
  "The graph is 3-colourable" is `∃ Red Green Blue. φ`, with `φ` saying every vertex has
  a colour and no edge joins two vertices of one colour.
* `Sentence.Holds A ψ` is "some guess makes `φ` true on `A`".

Nothing here mentions relational algebra. `Rasso.ESO.ToProgram` builds a
Rasso program from a sentence and a structure.

Design principles, not themselves expressible in Lean:

* The goal: over finite structures, the properties decided by a fixed multi solution set of
  selection on Boolean function spaces ("does it have a candidate?") are exactly the ESO-definable ones
  (`Rasso.ESO.BoolSelection`). Full Rasso says more than ESO; this is about a fragment.
* Quantifiers are not in the term language of solution sets. Second-order ∃ comes from
  the multi solution set itself (its members range over all candidate relations);
  first-order ∃ is projection and ∀ is difference against the domain, as in Codd's
  theorem.
* Inspiration: Cadoli and Mancini, NP-Alg (TPLP 2006): "Guess Q ⊆ DOM^k; FAIL = ∅".

Conventions:

* **Elements are Rasso values** (`Value`), used only through equality. Rasso has
  one universe of values, so a structure may use ints,
  symbols or strings as its elements. (A universe that mixes ints and floats is legal
  here, but Rasso's `=` refuses to compare an int with a float, so the program `Rasso.ESO.ToProgram`
  builds would be refused on it. The examples use one kind.)
* **Names are strings.** Relation symbols, second-order variables and first-order
  variables are all `String`s, as attribute and statement names are in Rasso.
* **A structure** gives every symbol a list of tuples (most symbols get `[]`). Arity is
  not checked by the logic: an atom just asks whether a tuple is in a list. `Str.WF`
  says every tuple's entries are in the universe.
* **The universe may be empty.** Nothing here needs it to be non-empty.
* **Assignments** are total functions `String → Value`; only the free variables matter
  (`FO.Sat_congr`).
* **Second-order variables are a separate sort** (`gvar`), interpreted by a guess
  `G : String → List (List Value)`. A sentence lists its second-order variables with their
  arities (`ar`); a guess fits when the guess for each listed name is a set of tuples of
  that arity over the universe, and every unlisted name is guessed empty. If a name is
  listed twice, the first listing counts (`List.lookup`); `Sentence.problem` flags it.
* **Equality is a logical symbol**, compared by `=` on values.
* **No `Classical.choice` in this file.** The proofs case-split with `if h : y = x` (a
  decidable test) rather than `by_cases`. The headline theorems of the ESO proof do use
  `Classical.choice`, through core Lean's lemmas about `String`.
-/

namespace Rasso.ESO

open Rasso

/-- A finite relational structure with elements in `Value`. -/
structure Str where
  univ : List Value
  rel : String → List (List Value)

/-- Every tuple of every relation draws its entries from the universe. -/
def Str.WF (A : Str) : Prop := ∀ i, ∀ t ∈ A.rel i, ∀ a ∈ t, a ∈ A.univ

/-- A structure from a universe and a list of named relations (symbols not listed hold
nothing). -/
def Str.ofList (univ : List Value) (rels : List (String × List (List Value))) : Str :=
  ⟨univ, fun i => (rels.lookup i).getD []⟩

/-- A guess: one finite relation per second-order variable. -/
abbrev Guess := String → List (List Value)

/-- Guess `G` fits arities `ar` over `A`: the guess for a listed name is a set of tuples
of its arity over the universe, and the guess for an unlisted name is empty. -/
def Guess.Fits (A : Str) (ar : List (String × Nat)) (G : Guess) : Prop :=
  ∀ j, ∀ t ∈ G j, ∃ k, ar.lookup j = some k ∧ t.length = k ∧ ∀ a ∈ t, a ∈ A.univ

/-- First-order formulas over input symbols (`rel`) and second-order variables
(`gvar`). -/
inductive FO where
  | rel (i : String) (args : List String)
  | gvar (j : String) (args : List String)
  | eq (x y : String)
  | not (φ : FO)
  | and (φ ψ : FO)
  | or (φ ψ : FO)
  | ex (x : String) (φ : FO)
  | all (x : String) (φ : FO)
  deriving Repr, Inhabited

/-- Update an assignment at one variable. -/
def upd (ρ : String → Value) (x : String) (a : Value) : String → Value :=
  fun y => if y = x then a else ρ y

@[simp] theorem upd_same (ρ : String → Value) (x : String) (a : Value) : upd ρ x a x = a := by
  simp [upd]

theorem upd_other {ρ : String → Value} {x y : String} {a : Value} (h : y ≠ x) :
    upd ρ x a y = ρ y := by
  simp [upd, h]

namespace FO

/-- Free variables (repeats allowed; only membership matters). -/
def fv : FO → List String
  | rel _ args => args
  | gvar _ args => args
  | eq x y => [x, y]
  | not φ => φ.fv
  | and φ ψ => φ.fv ++ ψ.fv
  | or φ ψ => φ.fv ++ ψ.fv
  | ex x φ => φ.fv.filter (· != x)
  | all x φ => φ.fv.filter (· != x)

/-- Satisfaction, with first-order quantifiers ranging over the universe. -/
def Sat (A : Str) (G : Guess) : FO → (String → Value) → Prop
  | rel i args, ρ => args.map ρ ∈ A.rel i
  | gvar j args, ρ => args.map ρ ∈ G j
  | eq x y, ρ => ρ x = ρ y
  | not φ, ρ => ¬ Sat A G φ ρ
  | and φ ψ, ρ => Sat A G φ ρ ∧ Sat A G ψ ρ
  | or φ ψ, ρ => Sat A G φ ρ ∨ Sat A G ψ ρ
  | ex x φ, ρ => ∃ a ∈ A.univ, Sat A G φ (upd ρ x a)
  | all x φ, ρ => ∀ a ∈ A.univ, Sat A G φ (upd ρ x a)

/-- Satisfaction is decidable (the universe is a finite list). -/
instance decSat (A : Str) (G : Guess) :
    (φ : FO) → (ρ : String → Value) → Decidable (Sat A G φ ρ)
  | rel _ _, _ => inferInstanceAs (Decidable (_ ∈ _))
  | gvar _ _, _ => inferInstanceAs (Decidable (_ ∈ _))
  | eq _ _, _ => inferInstanceAs (Decidable (_ = _))
  | not φ, ρ => @instDecidableNot _ (decSat A G φ ρ)
  | and φ ψ, ρ => @instDecidableAnd _ _ (decSat A G φ ρ) (decSat A G ψ ρ)
  | or φ ψ, ρ => @instDecidableOr _ _ (decSat A G φ ρ) (decSat A G ψ ρ)
  | ex x φ, ρ =>
    have : ∀ a, Decidable (Sat A G φ (upd ρ x a)) := fun _ => decSat A G φ _
    inferInstanceAs (Decidable (∃ a ∈ A.univ, _))
  | all x φ, ρ =>
    have : ∀ a, Decidable (Sat A G φ (upd ρ x a)) := fun _ => decSat A G φ _
    inferInstanceAs (Decidable (∀ a ∈ A.univ, _))

theorem map_congr {xs : List String} {ρ ρ' : String → Value} (h : ∀ x ∈ xs, ρ x = ρ' x) :
    xs.map ρ = xs.map ρ' := List.map_congr_left h

/-- Updating two assignments that agree off `x` keeps them agreeing, on the variables
of a quantified formula's body. -/
theorem upd_agree {ρ ρ' : String → Value} {x : String} {a : Value} {xs : List String}
    (h : ∀ y ∈ xs.filter (· != x), ρ y = ρ' y) : ∀ y ∈ xs, upd ρ x a y = upd ρ' x a y := by
  intro y hy
  if hyx : y = x then
    subst hyx; rw [upd_same, upd_same]
  else
    rw [upd_other hyx, upd_other hyx]
    exact h y (List.mem_filter.mpr ⟨hy, bne_iff_ne.mpr hyx⟩)

/-- Satisfaction depends only on the free variables. -/
theorem Sat_congr {A : Str} {G : Guess} :
    (φ : FO) → {ρ ρ' : String → Value} → (∀ x ∈ φ.fv, ρ x = ρ' x) →
      (Sat A G φ ρ ↔ Sat A G φ ρ')
  | rel i args, ρ, ρ', h => by simp only [Sat]; rw [map_congr (xs := args) h]
  | gvar j args, ρ, ρ', h => by simp only [Sat]; rw [map_congr (xs := args) h]
  | eq x y, ρ, ρ', h => by
    simp only [Sat]
    rw [h x (List.mem_cons_self ..), h y (List.mem_cons_of_mem _ (List.mem_cons_self ..))]
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
    have e : ∀ a, (Sat A G φ (upd ρ x a) ↔ Sat A G φ (upd ρ' x a)) := fun _ =>
      Sat_congr φ (upd_agree h)
    simp only [Sat]
    exact ⟨fun ⟨a, ha, s⟩ => ⟨a, ha, (e a).mp s⟩, fun ⟨a, ha, s⟩ => ⟨a, ha, (e a).mpr s⟩⟩
  | all x φ, ρ, ρ', h => by
    have e : ∀ a, (Sat A G φ (upd ρ x a) ↔ Sat A G φ (upd ρ' x a)) := fun _ =>
      Sat_congr φ (upd_agree h)
    simp only [Sat]
    exact ⟨fun s a ha => (e a).mp (s a ha), fun s a ha => (e a).mpr (s a ha)⟩

end FO

/-- An ESO sentence `∃ R₁ … Rₘ. φ`: the second-order variables with their arities, and a
first-order formula with no free first-order variables. `closed` is a `Bool` test, so
that `rfl` (or `by decide`) proves it for a written sentence. -/
structure Sentence where
  ar : List (String × Nat)
  φ : FO
  closed : φ.fv.isEmpty = true

/-- `A ⊨ ∃ R̄. φ`: some fitting guess satisfies `φ`. (The assignment is irrelevant since
`φ` is closed (`Sentence.sat_any`); `fun _ => default` is a fixed choice.) -/
def Sentence.Holds (A : Str) (ψ : Sentence) : Prop :=
  ∃ G : Guess, G.Fits A ψ.ar ∧ ψ.φ.Sat A G (fun _ => default)

theorem Sentence.sat_any {A : Str} {G : Guess} (ψ : Sentence) (ρ ρ' : String → Value) :
    ψ.φ.Sat A G ρ ↔ ψ.φ.Sat A G ρ' :=
  FO.Sat_congr ψ.φ fun x hx => by
    have := ψ.closed
    rw [List.isEmpty_iff] at this
    rw [this] at hx; cases hx

end Rasso.ESO
