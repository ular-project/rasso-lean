import Rasso.Term

/-!
# Rasso: linear forms

A *linear form* is a sum of rational coefficients times attributes, plus a rational
constant. The linear class reads the comparisons that mention the dropped attribute as
forms, and Fourier–Motzkin works on the forms, not on terms.

This file holds the forms, their operations, and the algebra of their values. Reading a
term as a form, and writing a form back as a term, are in `Rasso.LinElim`.
-/

namespace Rasso

/-- A linear form: `Σ cᵢ · bᵢ + k`. An attribute may appear more than once; its coefficient
is the sum. -/
structure Lin where
  terms : List (String × Rat)
  const : Rat
  deriving Inhabited

namespace Lin

/-- The value of the attribute part, given a value for each attribute. -/
def evalTerms (σ : String → Rat) : List (String × Rat) → Rat
  | [] => 0
  | (b, c) :: r => c * σ b + evalTerms σ r

/-- The value of the form. -/
def eval (σ : String → Rat) (L : Lin) : Rat := evalTerms σ L.terms + L.const

def ofConst (k : Rat) : Lin := ⟨[], k⟩
def ofAttr (b : String) : Lin := ⟨[(b, 1)], 0⟩

def add (L M : Lin) : Lin := ⟨L.terms ++ M.terms, L.const + M.const⟩
def scale (k : Rat) (L : Lin) : Lin := ⟨L.terms.map fun p => (p.1, k * p.2), k * L.const⟩
def neg (L : Lin) : Lin := L.scale (-1)
def sub (L M : Lin) : Lin := L.add M.neg

/-- Does the form read no attribute? -/
def isConst (L : Lin) : Bool := L.terms.isEmpty

/-- The coefficient of `a`. -/
def coeff (a : String) (L : Lin) : Rat :=
  (L.terms.filter (·.1 == a)).foldr (fun p s => p.2 + s) 0

/-- The form without `a`. -/
def drop (a : String) (L : Lin) : Lin := ⟨L.terms.filter (·.1 != a), L.const⟩

/-- The attributes the form names. -/
def attrs (L : Lin) : List String := L.terms.map (·.1)

/-! ## The algebra of values -/

variable (σ : String → Rat)

theorem evalTerms_append (l m : List (String × Rat)) :
    evalTerms σ (l ++ m) = evalTerms σ l + evalTerms σ m := by
  induction l with
  | nil => simp [evalTerms, Rat.zero_add]
  | cons p l ih => obtain ⟨b, c⟩ := p; simp only [List.cons_append, evalTerms, ih]; grind

theorem eval_ofConst (k : Rat) : (ofConst k).eval σ = k := by simp [eval, ofConst, evalTerms, Rat.zero_add]

theorem eval_ofAttr (b : String) : (ofAttr b).eval σ = σ b := by
  simp [eval, ofAttr, evalTerms, Rat.add_zero, Rat.one_mul]

theorem eval_add (L M : Lin) : (L.add M).eval σ = L.eval σ + M.eval σ := by
  simp only [eval, add, evalTerms_append]; grind

theorem eval_scale (k : Rat) (L : Lin) : (L.scale k).eval σ = k * L.eval σ := by
  simp only [eval, scale]
  have : ∀ l : List (String × Rat),
      evalTerms σ (l.map fun p => (p.1, k * p.2)) = k * evalTerms σ l := by
    intro l
    induction l with
    | nil => simp [evalTerms, Rat.mul_zero]
    | cons p l ih => obtain ⟨b, c⟩ := p; simp only [List.map_cons, evalTerms, ih]; grind
  rw [this]; grind

theorem eval_neg (L : Lin) : L.neg.eval σ = - L.eval σ := by
  simp only [neg, eval_scale]; grind

theorem eval_sub (L M : Lin) : (L.sub M).eval σ = L.eval σ - M.eval σ := by
  simp only [sub, eval_add, eval_neg]; grind

/-- A form is its coefficient of `a` times `a`, plus the form without `a`. -/
theorem eval_split (a : String) (L : Lin) :
    L.eval σ = L.coeff a * σ a + (L.drop a).eval σ := by
  simp only [eval, coeff, drop]
  have : ∀ l : List (String × Rat), evalTerms σ l =
      (l.filter (·.1 == a)).foldr (fun p s => p.2 + s) 0 * σ a +
        evalTerms σ (l.filter (·.1 != a)) := by
    intro l
    induction l with
    | nil => simp [evalTerms, Rat.add_zero]
    | cons p l ih =>
      obtain ⟨b, c⟩ := p
      by_cases hb : b = a
      · subst hb; simp only [evalTerms, List.filter_cons, beq_self_eq_true, ↓reduceIte,
          List.foldr_cons, bne_self_eq_false, Bool.false_eq_true, ih]; grind
      · have h1 : (b == a) = false := by simpa using hb
        have h2 : (b != a) = true := by simpa using hb
        simp only [evalTerms, List.filter_cons, h1, h2, Bool.false_eq_true, ↓reduceIte, ih]
        grind
  rw [this]; grind

/-- The value of a form depends only on the attributes it names. -/
theorem evalTerms_congr {σ τ : String → Rat} :
    ∀ (l : List (String × Rat)), (∀ b ∈ l.map (·.1), σ b = τ b) → evalTerms σ l = evalTerms τ l
  | [], _ => rfl
  | (b, c) :: l, h => by
    simp only [evalTerms]
    rw [h b (by simp), evalTerms_congr l (fun x hx => h x (by simp [hx]))]

theorem eval_congr {σ τ : String → Rat} (L : Lin) (h : ∀ b ∈ L.attrs, σ b = τ b) :
    L.eval σ = L.eval τ := by
  simp only [eval]; rw [evalTerms_congr L.terms h]

theorem attrs_drop {a : String} {L : Lin} {b : String} (hb : b ∈ (L.drop a).attrs) :
    b ∈ L.attrs ∧ b ≠ a := by
  simp only [attrs, drop, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq] at hb ⊢
  obtain ⟨p, ⟨hp, hpa⟩, rfl⟩ := hb
  exact ⟨⟨p, hp, rfl⟩, hpa⟩

theorem attrs_add {L M : Lin} {b : String} : b ∈ (L.add M).attrs ↔ b ∈ L.attrs ∨ b ∈ M.attrs := by
  simp [attrs, add]

theorem attrs_scale {k : Rat} {L : Lin} {b : String} : b ∈ (L.scale k).attrs ↔ b ∈ L.attrs := by
  simp [attrs, scale]

theorem attrs_neg {L : Lin} {b : String} : b ∈ L.neg.attrs ↔ b ∈ L.attrs := attrs_scale

theorem attrs_sub {L M : Lin} {b : String} : b ∈ (L.sub M).attrs ↔ b ∈ L.attrs ∨ b ∈ M.attrs := by
  simp [sub, attrs_add, attrs_neg]

end Lin

end Rasso
