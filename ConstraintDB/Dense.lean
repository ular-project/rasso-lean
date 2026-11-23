import ConstraintDB.Generalized

/-!
# Dense order constraints (KKR Definition 1.2(2); Goldin–Kanellakis §3)

KKR's dense order class: constraints `x θ y` and `x θ c` between variables and
constants, over a countably infinite dense linear order without endpoints (for
example the rationals). Goldin and Kanellakis build their constraint algebra for
exactly this class.

Sources:

* Kanellakis, Kuper, Revesz, *Constraint Query Languages*, J. Computer and System
  Sciences 51(1):26–52 (1995): the class is Definition 1.2(2).
* Goldin, Kanellakis, *Constraint Query Algebras*, Constraints 1:45–83 (1996),
  doi:10.1007/BF00143878: the algebra is §3, "A Dense Order Constraint Algebra".

Attribute names are `Lean.Name`.

Where KKR differs from Rasso:

* **One domain.** KKR has one domain `D` for every variable; Rasso gives each attribute
  its own domain. `D` is a parameter here with the axioms of a dense linear order
  without endpoints (`DenseOrder`). Lean's `Rat` is an instance
  (`ConstraintDB/Examples.lean`).
* **Points are valuations.** A point is a valuation `Name → D`. A generalized
  relation over attributes X constrains only the names in X; the natural join of two
  relations is then the conjunction of their constraints, and projection is `∃`
  over the dropped names. (Rasso instead gives a tuple a value for each attribute of its
  heading.)

Conventions:

* **Comparisons.** θ ranges over `<`, `≤` and `=`, where `a ≤ b` means `a < b ∨ a = b`.
  KKR's Definition 1.2(2) also takes the negations `≠`, `>`, `≥`. They are not needed:
  `>` and `≥` are `<` and `≤` with the sides swapped, and ¬(a = b) is a < b ∨ b < a in a
  linear order, so the class is closed under negation as it stands (`instance : NegDNF`).
-/

namespace ConstraintDB

open Lean (Name)

/-- A dense linear order without endpoints, given by its strict order. -/
class DenseOrder (D : Type) extends LT D where
  lt_irrefl : ∀ a : D, ¬ a < a
  lt_trans : ∀ {a b c : D}, a < b → b < c → a < c
  lt_trichotomy : ∀ a b : D, a < b ∨ a = b ∨ b < a
  dense : ∀ {a b : D}, a < b → ∃ c, a < c ∧ c < b
  no_max : ∀ a : D, ∃ b, a < b
  no_min : ∀ a : D, ∃ b, b < a
  inhabited : D

/-- A valuation: a value for every attribute name. -/
abbrev Val (D : Type) := Name → D

/-- Change one name's value. -/
def Val.upd {D : Type} (v : Val D) (z : Name) (d : D) : Val D :=
  fun n => if n = z then d else v n

/-- A term: an attribute or a constant. -/
inductive Term (D : Type) where
  | var : Name → Term D
  | const : D → Term D
  deriving Repr, DecidableEq

/-- The comparisons. -/
inductive Cmp where
  | lt | le | eq
  deriving DecidableEq, Repr

/-- An atomic constraint `l θ r`. -/
structure Atom (D : Type) where
  cmp : Cmp
  l : Term D
  r : Term D
  deriving Repr, DecidableEq

variable {D : Type}

def Term.val (v : Val D) : Term D → D
  | .var n => v n
  | .const c => c

/-- `a < b` if `strict`, else `a ≤ b` (that is, `a < b ∨ a = b`). -/
def ltb [LT D] (strict : Bool) (a b : D) : Prop := if strict then a < b else a < b ∨ a = b

def Cmp.holds [LT D] : Cmp → D → D → Prop
  | .lt, a, b => a < b
  | .le, a, b => a < b ∨ a = b
  | .eq, a, b => a = b

def Atom.sat [LT D] (a : Atom D) (v : Val D) : Prop := a.cmp.holds (a.l.val v) (a.r.val v)

instance [LT D] : Constraint (Atom D) (Val D) := ⟨Atom.sat⟩

theorem sat_def [LT D] (a : Atom D) (v : Val D) :
    Constraint.sat a v ↔ a.cmp.holds (a.l.val v) (a.r.val v) := Iff.rfl

/-! ## Order facts -/

section Facts
variable [DenseOrder D]

theorem lt_asymm {a b : D} (h : a < b) : ¬ b < a := fun h' =>
  DenseOrder.lt_irrefl a (DenseOrder.lt_trans h h')

theorem ltb_of_lt {s : Bool} {a b : D} (h : a < b) : ltb s a b := by
  cases s <;> simp [ltb, h]

theorem lt_of_ltb_lt {s : Bool} {a b c : D} (h₁ : ltb s a b) (h₂ : b < c) : a < c := by
  cases s <;> simp only [ltb] at h₁
  · rcases h₁ with h₁ | rfl
    · exact DenseOrder.lt_trans h₁ h₂
    · exact h₂
  · exact DenseOrder.lt_trans h₁ h₂

theorem lt_of_lt_ltb {s : Bool} {a b c : D} (h₁ : a < b) (h₂ : ltb s b c) : a < c := by
  cases s <;> simp only [ltb] at h₂
  · rcases h₂ with h₂ | rfl
    · exact DenseOrder.lt_trans h₁ h₂
    · exact h₁
  · exact DenseOrder.lt_trans h₁ h₂

theorem ltb_trans {s s' : Bool} {a b c : D} (h₁ : ltb s a b) (h₂ : ltb s' b c) :
    ltb (s || s') a c := by
  cases s <;> cases s' <;> simp only [ltb, Bool.or_self, Bool.or_true,
    Bool.or_false, ite_true] at h₁ h₂ ⊢
  · rcases h₁ with h₁ | rfl
    · exact .inl (lt_of_lt_ltb (s := false) h₁ h₂)
    · exact h₂
  · exact lt_of_ltb_lt (s := false) h₁ h₂
  · exact lt_of_lt_ltb (s := false) h₁ h₂
  · exact DenseOrder.lt_trans h₁ h₂

end Facts

/-! ## Negation inside the class -/

instance [DenseOrder D] : NegDNF (Atom D) (Val D) where
  neg a := match a.cmp with
    | .lt => [[⟨.le, a.r, a.l⟩]]
    | .le => [[⟨.lt, a.r, a.l⟩]]
    | .eq => [[⟨.lt, a.l, a.r⟩], [⟨.lt, a.r, a.l⟩]]
  sat_neg a v := by
    obtain ⟨c, l, r⟩ := a
    have tri := DenseOrder.lt_trichotomy (l.val v) (r.val v)
    have irr := DenseOrder.lt_irrefl (l.val v)
    have irr' := DenseOrder.lt_irrefl (r.val v)
    have asy := @lt_asymm D _ (l.val v) (r.val v)
    have asy' := @lt_asymm D _ (r.val v) (l.val v)
    cases c <;> simp only [GRel.Sat, GTuple.Sat, List.mem_cons,
      List.not_mem_nil, or_false, exists_eq_left, forall_eq, exists_eq_or_imp, sat_def,
      Cmp.holds] <;> constructor
    · rintro (h | h)
      · exact asy' h
      · rw [h]; exact irr
    · intro h; rcases tri with h' | h' | h'
      · exact absurd h' h
      · exact .inr h'.symm
      · exact .inl h'
    · intro h; rintro (h' | h')
      · exact asy h' h
      · rw [h'] at h; exact irr' h
    · intro h; rcases tri with h' | h' | h'
      · exact absurd (.inl h') h
      · exact absurd (.inr h') h
      · exact h'
    · rintro (h | h) e
      · rw [e] at h; exact irr' h
      · rw [e] at h; exact irr' h
    · intro h; rcases tri with h' | h' | h'
      · exact .inl h'
      · exact absurd h' h
      · exact .inr h'

/-! ## Renaming -/

def Term.rename (ρ : Name → Name) : Term D → Term D
  | .var n => .var (ρ n)
  | .const c => .const c

def Atom.rename (ρ : Name → Name) (a : Atom D) : Atom D := ⟨a.cmp, a.l.rename ρ, a.r.rename ρ⟩

theorem Term.val_rename (ρ : Name → Name) (v : Val D) (t : Term D) :
    (t.rename ρ).val v = t.val (v ∘ ρ) := by
  cases t <;> rfl

theorem sat_rename [LT D] (ρ : Name → Name) (a : Atom D) (v : Val D) :
    Constraint.sat (a.rename ρ) v ↔ Constraint.sat a (v ∘ ρ) := by
  simp only [sat_def, Atom.rename, Term.val_rename]

/-! ## The names a relation mentions

A relation's truth depends only on the values of the names it mentions. -/

def Term.names : Term D → List Name
  | .var n => [n]
  | .const _ => []

def Atom.names (a : Atom D) : List Name := a.l.names ++ a.r.names

def GRel.names (r : GRel (Atom D)) : List Name := r.flatMap (·.flatMap Atom.names)

theorem Atom.sat_congr [LT D] {a : Atom D} {v w : Val D} (e : ∀ n ∈ a.names, v n = w n) :
    Constraint.sat a v ↔ Constraint.sat a w := by
  obtain ⟨c, l, r⟩ := a
  have hl : l.val v = l.val w := by
    cases l with
    | var n => exact e n (by simp [Atom.names, Term.names])
    | const _ => rfl
  have hr : r.val v = r.val w := by
    cases r with
    | var n => exact e n (by simp [Atom.names, Term.names])
    | const _ => rfl
  rw [sat_def, sat_def]
  simp only [hl, hr]

theorem GRel.sat_congr [LT D] {r : GRel (Atom D)} {v w : Val D}
    (e : ∀ n ∈ r.names, v n = w n) : GRel.Sat r v ↔ GRel.Sat r w := by
  have he : ∀ g ∈ r, ∀ a ∈ g, ∀ n ∈ a.names, v n = w n := fun g hg a ha n hn =>
    e n (List.mem_flatMap.2 ⟨g, hg, List.mem_flatMap.2 ⟨a, ha, hn⟩⟩)
  simp only [GRel.Sat, GTuple.Sat]
  constructor
  · rintro ⟨g, hg, hs⟩
    exact ⟨g, hg, fun a ha => (Atom.sat_congr (he g hg a ha)).1 (hs a ha)⟩
  · rintro ⟨g, hg, hs⟩
    exact ⟨g, hg, fun a ha => (Atom.sat_congr (he g hg a ha)).2 (hs a ha)⟩

end ConstraintDB
