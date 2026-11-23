import ConstraintDB.Dense

/-!
# Projection for dense order constraints

Projection is the operator where constraint classes differ. Over a dense order it
maps generalized relations to generalized relations (closed form), and it can be
computed by eliminating one variable at a time.

Goldin and Kanellakis (GK; Constraints 1996, §3.2–§3.3) make projection *syntactic*:
they keep every generalized tuple in a canonical form (each tuple its own tightest
representative, unique by their Theorem 1 and found efficiently, §3.2), and then
projecting a canonical tuple just drops the constraints on the removed variables
(§3.3; its closure is their Lemma 10).

Conventions:

* **Variable elimination instead of canonical form.** Here a variable `z` is
  eliminated from a generalized tuple directly (`elim`), in the manner of
  Fourier–Motzkin elimination for order constraints:
  1. if the tuple contains `z < z`, the tuple is empty;
  2. if it contains `z = t` (t not `z`), substitute `t` for `z` everywhere;
  3. otherwise keep the constraints not mentioning `z`, and for every lower bound
     `l ⋖ z` and upper bound `z ⋖ u` add `l ⋖ u` (strict if either bound is strict).
  This yields the same unrestricted relation as GK's canonicalise-then-drop, by
  `elim_spec`; the syntax may differ from GK's canonical form.
* **Projection away.** Projection is stated as eliminating a list of names
  (`GRel.elimAll`): π_Z of a relation over attributes X eliminates X \ Z.

Step 3 needs density and the absence of endpoints (`interval`). `ConstraintDB/Discrete.lean`
shows that the same elimination is wrong over `Int`.
-/

namespace ConstraintDB

open Lean (Name)

variable {D : Type}

/-! ## Terms and the eliminated variable -/

def Term.isVar (z : Name) : Term D → Bool
  | .var n => decide (n = z)
  | .const _ => false

theorem Term.val_upd_of_not {v : Val D} {z : Name} {d : D} {t : Term D}
    (h : t.isVar z = false) : t.val (v.upd z d) = t.val v := by
  cases t with
  | var n =>
    simp only [Term.isVar, decide_eq_false_iff_not] at h
    simp [Term.val, Val.upd, h]
  | const c => rfl

theorem Term.val_upd_of_isVar {v : Val D} {z : Name} {d : D} {t : Term D}
    (h : t.isVar z = true) : t.val (v.upd z d) = d := by
  cases t with
  | var n =>
    simp only [Term.isVar, decide_eq_true_eq] at h
    simp [Term.val, Val.upd, h]
  | const c => simp [Term.isVar] at h

/-- Replace `z` by `t`. -/
def Term.subst (s : Term D) (z : Name) (t : Term D) : Term D := if s.isVar z then t else s

theorem Term.val_subst (v : Val D) (z : Name) (t s : Term D) :
    (s.subst z t).val v = s.val (v.upd z (t.val v)) := by
  unfold Term.subst
  cases h : s.isVar z
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact (Term.val_upd_of_not h).symm
  · simp only [↓reduceIte]; exact (Term.val_upd_of_isVar h).symm

def Atom.subst (z : Name) (t : Term D) (a : Atom D) : Atom D :=
  ⟨a.cmp, a.l.subst z t, a.r.subst z t⟩

theorem sat_subst [LT D] (z : Name) (t : Term D) (a : Atom D) (v : Val D) :
    Constraint.sat (a.subst z t) v ↔ Constraint.sat a (v.upd z (t.val v)) := by
  simp only [sat_def, Atom.subst, Term.val_subst]

/-! ## How an atom constrains `z` -/

/-- The role of an atom with respect to the variable `z`. -/
inductive Role (D : Type) where
  /-- Does not mention `z`. -/
  | other (a : Atom D)
  /-- `z ≤ z` or `z = z`. -/
  | always
  /-- `z < z`. -/
  | never
  /-- `z = t` or `t = z`. -/
  | defn (t : Term D)
  /-- `t < z` (strict) or `t ≤ z`. -/
  | lower (t : Term D) (strict : Bool)
  /-- `z < t` (strict) or `z ≤ t`. -/
  | upper (t : Term D) (strict : Bool)

def classify (z : Name) (a : Atom D) : Role D :=
  match a.l.isVar z, a.r.isVar z, a.cmp with
  | true, true, .lt => .never
  | true, true, _ => .always
  | true, false, .lt => .upper a.r true
  | true, false, .le => .upper a.r false
  | true, false, .eq => .defn a.r
  | false, true, .lt => .lower a.l true
  | false, true, .le => .lower a.l false
  | false, true, .eq => .defn a.l
  | false, false, _ => .other a

/-- What the role says about the value `d` of `z`, the other names valued by `v`. -/
def Role.holds [LT D] (v : Val D) (d : D) : Role D → Prop
  | .other a => Constraint.sat a v
  | .always => True
  | .never => False
  | .defn t => d = t.val v
  | .lower t s => ltb s (t.val v) d
  | .upper t s => ltb s d (t.val v)

theorem classify_spec [DenseOrder D] (z : Name) (a : Atom D) (v : Val D) (d : D) :
    Constraint.sat a (v.upd z d) ↔ (classify z a).holds v d := by
  obtain ⟨c, l, r⟩ := a
  have irr := DenseOrder.lt_irrefl d
  cases hl : l.isVar z <;> cases hr : r.isVar z
  · rw [sat_def]
    simp only [Term.val_upd_of_not hl, Term.val_upd_of_not hr]
    cases c <;> simp [classify, hl, hr, Role.holds, sat_def]
  · rw [sat_def]
    simp only [Term.val_upd_of_not hl, Term.val_upd_of_isVar hr]
    cases c <;> simp [classify, hl, hr, Role.holds, Cmp.holds, ltb, eq_comm]
  · rw [sat_def]
    simp only [Term.val_upd_of_isVar hl, Term.val_upd_of_not hr]
    cases c <;> simp [classify, hl, hr, Role.holds, Cmp.holds, ltb]
  · rw [sat_def]
    simp only [Term.val_upd_of_isVar hl, Term.val_upd_of_isVar hr]
    cases c <;> simp [classify, hl, hr, Role.holds, Cmp.holds, irr]

/-! ## Bounds: the interval lemma -/

section Interval
variable [DenseOrder D]

theorem lo_exists : (L : List (D × Bool)) → L ≠ [] →
    ∃ b ∈ L, ∀ l ∈ L, ∀ d, ltb b.2 b.1 d → ltb l.2 l.1 d
  | [], h => absurd rfl h
  | [l], _ => ⟨l, by simp, fun l' hl' d hd => by simp at hl'; subst hl'; exact hd⟩
  | l :: l₂ :: L, _ => by
    obtain ⟨b, hb, hdom⟩ := lo_exists (l₂ :: L) (by simp)
    -- `l` dominates `b`, or `b` dominates `l`
    have key : (∀ d, ltb l.2 l.1 d → ltb b.2 b.1 d) ∨ (∀ d, ltb b.2 b.1 d → ltb l.2 l.1 d) := by
      rcases DenseOrder.lt_trichotomy b.1 l.1 with h | h | h
      · exact .inl fun d hd => ltb_of_lt (lt_of_lt_ltb h hd)
      · cases hs : l.2
        · refine .inr fun d hd => ?_
          simp only [ltb, Bool.false_eq_true, ↓reduceIte]
          rw [← h]
          cases hb2 : b.2 <;> simp only [ltb, hb2, Bool.false_eq_true, ↓reduceIte] at hd
          · exact hd
          · exact .inl hd
        · refine .inl fun d hd => ?_
          simp only [ltb, ↓reduceIte] at hd
          rw [h]; exact ltb_of_lt hd
      · exact .inr fun d hd => ltb_of_lt (lt_of_lt_ltb h hd)
    rcases key with k | k
    · refine ⟨l, by simp, fun l' hl' d hd => ?_⟩
      simp only [List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · exact hd
      · exact hdom l' (by simpa using hl') d (k d hd)
    · refine ⟨b, List.mem_cons_of_mem _ hb, fun l' hl' d hd => ?_⟩
      simp only [List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · exact k d hd
      · exact hdom l' (by simpa using hl') d hd

theorem hi_exists : (U : List (D × Bool)) → U ≠ [] →
    ∃ b ∈ U, ∀ u ∈ U, ∀ d, ltb b.2 d b.1 → ltb u.2 d u.1
  | [], h => absurd rfl h
  | [u], _ => ⟨u, by simp, fun u' hu' d hd => by simp at hu'; subst hu'; exact hd⟩
  | u :: u₂ :: U, _ => by
    obtain ⟨b, hb, hdom⟩ := hi_exists (u₂ :: U) (by simp)
    have key : (∀ d, ltb u.2 d u.1 → ltb b.2 d b.1) ∨ (∀ d, ltb b.2 d b.1 → ltb u.2 d u.1) := by
      rcases DenseOrder.lt_trichotomy u.1 b.1 with h | h | h
      · exact .inl fun d hd => ltb_of_lt (lt_of_ltb_lt hd h)
      · cases hs : u.2
        · refine .inr fun d hd => ?_
          simp only [ltb, Bool.false_eq_true, ↓reduceIte]
          rw [h]
          cases hb2 : b.2 <;> simp only [ltb, hb2, Bool.false_eq_true, ↓reduceIte] at hd
          · exact hd
          · exact .inl hd
        · refine .inl fun d hd => ?_
          simp only [ltb, ↓reduceIte] at hd
          rw [← h]; exact ltb_of_lt hd
      · exact .inr fun d hd => ltb_of_lt (lt_of_ltb_lt hd h)
    rcases key with k | k
    · refine ⟨u, by simp, fun u' hu' d hd => ?_⟩
      simp only [List.mem_cons] at hu'
      rcases hu' with rfl | hu'
      · exact hd
      · exact hdom u' (by simpa using hu') d (k d hd)
    · refine ⟨b, List.mem_cons_of_mem _ hb, fun u' hu' d hd => ?_⟩
      simp only [List.mem_cons] at hu'
      rcases hu' with rfl | hu'
      · exact k d hd
      · exact hdom u' (by simpa using hu') d hd

/-- If every lower bound is compatible with every upper bound, some value lies within
all of them. This is where density and the absence of endpoints are used. -/
theorem interval (L U : List (D × Bool)) (h : ∀ l ∈ L, ∀ u ∈ U, ltb (l.2 || u.2) l.1 u.1) :
    ∃ d, (∀ l ∈ L, ltb l.2 l.1 d) ∧ (∀ u ∈ U, ltb u.2 d u.1) := by
  by_cases hL : L = [] <;> by_cases hU : U = []
  · subst hL; subst hU; exact ⟨DenseOrder.inhabited, by simp, by simp⟩
  · subst hL
    obtain ⟨c, _, hc⟩ := hi_exists U hU
    obtain ⟨d, hd⟩ := DenseOrder.no_min c.1
    exact ⟨d, by simp, fun u hu => hc u hu d (ltb_of_lt hd)⟩
  · subst hU
    obtain ⟨b, _, hb⟩ := lo_exists L hL
    obtain ⟨d, hd⟩ := DenseOrder.no_max b.1
    exact ⟨d, fun l hl => hb l hl d (ltb_of_lt hd), by simp⟩
  · obtain ⟨b, hbL, hb⟩ := lo_exists L hL
    obtain ⟨c, hcU, hc⟩ := hi_exists U hU
    have hbc := h b hbL c hcU
    rcases DenseOrder.lt_trichotomy b.1 c.1 with e | e | e
    · obtain ⟨d, h₁, h₂⟩ := DenseOrder.dense e
      exact ⟨d, fun l hl => hb l hl d (ltb_of_lt h₁), fun u hu => hc u hu d (ltb_of_lt h₂)⟩
    · have hs : (b.2 || c.2) = false := by
        cases hs : (b.2 || c.2)
        · rfl
        · simp only [ltb, hs, ↓reduceIte] at hbc
          rw [e] at hbc; exact absurd hbc (DenseOrder.lt_irrefl _)
      simp only [Bool.or_eq_false_iff] at hs
      refine ⟨b.1, fun l hl => hb l hl _ ?_, fun u hu => hc u hu _ ?_⟩
      · simp [ltb, hs.1]
      · simp [ltb, hs.2, e]
    · exfalso
      cases hs : (b.2 || c.2) <;> simp only [ltb, hs, Bool.false_eq_true, ↓reduceIte] at hbc
      · rcases hbc with hbc | hbc
        · exact lt_asymm hbc e
        · rw [hbc] at e; exact DenseOrder.lt_irrefl _ e
      · exact lt_asymm hbc e

end Interval

/-! ## Eliminating one variable from a generalized tuple -/

/-- The first definition `z = t` in the tuple, if any. -/
def findDefn (z : Name) : List (Atom D) → Option (Term D)
  | [] => none
  | a :: g => match classify z a with
    | .defn t => some t
    | _ => findDefn z g

def isNever : Role D → Bool
  | .never => true
  | _ => false

def otherOf : Role D → Option (Atom D)
  | .other a => some a
  | _ => none

def lowerOf : Role D → Option (Term D × Bool)
  | .lower t s => some (t, s)
  | _ => none

def upperOf : Role D → Option (Term D × Bool)
  | .upper t s => some (t, s)
  | _ => none

/-- `l ⋖ u`, strict when `strict`. -/
def bound (strict : Bool) (l u : Term D) : Atom D := ⟨if strict then .lt else .le, l, u⟩

theorem sat_bound [LT D] (s : Bool) (l u : Term D) (v : Val D) :
    Constraint.sat (bound s l u) v ↔ ltb s (l.val v) (u.val v) := by
  cases s <;> rfl

/-- Every lower bound against every upper bound. -/
def pairs (L U : List (Term D × Bool)) : List (Atom D) :=
  L.flatMap fun l => U.map fun u => bound (l.2 || u.2) l.1 u.1

/-- Eliminate `z` from a generalized tuple (see the module comment). -/
def elim (z : Name) (g : GTuple (Atom D)) : GRel (Atom D) :=
  if g.any (fun a => isNever (classify z a)) then [] else
  match findDefn z g with
  | some t => [g.map (Atom.subst z t)]
  | none =>
    [g.filterMap (fun a => otherOf (classify z a)) ++
      pairs (g.filterMap fun a => lowerOf (classify z a)) (g.filterMap fun a => upperOf (classify z a))]

theorem findDefn_some {z : Name} {t : Term D} :
    (g : List (Atom D)) → findDefn z g = some t → ∃ a ∈ g, classify z a = .defn t
  | [], h => nomatch h
  | a :: g, h => by
    simp only [findDefn] at h
    split at h
    · next t' e => cases h; exact ⟨a, by simp, e⟩
    · obtain ⟨b, hb, e⟩ := findDefn_some g h
      exact ⟨b, List.mem_cons_of_mem _ hb, e⟩

theorem findDefn_none {z : Name} :
    (g : List (Atom D)) → findDefn z g = none → ∀ a ∈ g, ∀ t, classify z a ≠ .defn t
  | [], _ => by simp
  | a :: g, h => by
    simp only [findDefn] at h
    split at h
    · nomatch h
    · next hne =>
      intro b hb t e
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hne t e
      · exact findDefn_none g h b hb t e

theorem gtuple_sat_upd_iff [DenseOrder D] (z : Name) (g : GTuple (Atom D)) (v : Val D) (d : D) :
    GTuple.Sat g (v.upd z d) ↔ ∀ a ∈ g, (classify z a).holds v d :=
  ⟨fun h a ha => (classify_spec z a v d).1 (h a ha), fun h a ha => (classify_spec z a v d).2 (h a ha)⟩

/-- Correctness of elimination over a dense order: the result represents `∃ z`. -/
theorem elim_spec [DenseOrder D] (z : Name) (g : GTuple (Atom D)) (v : Val D) :
    GRel.Sat (elim z g) v ↔ ∃ d, GTuple.Sat g (v.upd z d) := by
  simp only [gtuple_sat_upd_iff]
  unfold elim
  split
  · next hn =>
    simp only [List.any_eq_true] at hn
    obtain ⟨a, ha, hna⟩ := hn
    constructor
    · rintro ⟨_, h, _⟩; exact nomatch h
    · rintro ⟨d, hd⟩
      have := hd a ha
      revert this hna
      cases classify z a <;> simp [isNever, Role.holds]
  · next hn =>
    simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hn
    split
    · next t ht =>
      obtain ⟨a₀, ha₀, e₀⟩ := findDefn_some g ht
      simp only [GRel.Sat, List.mem_singleton, exists_eq_left, GTuple.Sat, List.mem_map,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sat_subst]
      constructor
      · intro h; exact ⟨t.val v, fun a ha => (classify_spec z a v _).1 (h a ha)⟩
      · rintro ⟨d, hd⟩ a ha
        have hdef := hd a₀ ha₀
        rw [e₀] at hdef
        simp only [Role.holds] at hdef
        subst hdef
        exact (classify_spec z a v _).2 (hd a ha)
    · next ht =>
      have nodef := findDefn_none g ht
      simp only [GRel.Sat, List.mem_singleton, exists_eq_left, GTuple.Sat, List.mem_append,
        List.mem_filterMap, pairs, List.mem_flatMap, List.mem_map]
      constructor
      · intro h
        obtain ⟨d, hd1, hd2⟩ := interval
          ((g.filterMap fun a => lowerOf (classify z a)).map fun p => (p.1.val v, p.2))
          ((g.filterMap fun a => upperOf (classify z a)).map fun p => (p.1.val v, p.2))
          (by
            simp only [List.mem_map, List.mem_filterMap]
            rintro _ ⟨l, ⟨a, ha, hl⟩, rfl⟩ _ ⟨u, ⟨b, hb, hu⟩, rfl⟩
            exact (sat_bound _ _ _ v).1
              (h _ (.inr ⟨l, ⟨a, ha, hl⟩, ⟨u, ⟨b, hb, hu⟩, rfl⟩⟩)))
        refine ⟨d, fun a ha => ?_⟩
        cases e : classify z a with
        | other b => exact h b (.inl ⟨a, ha, by simp [e, otherOf]⟩)
        | always => trivial
        | never => have := hn a ha; simp [e, isNever] at this
        | defn t => exact absurd e (nodef a ha t)
        | lower t s =>
          exact hd1 _ (List.mem_map.2 ⟨(t, s), List.mem_filterMap.2 ⟨a, ha, by simp [e, lowerOf]⟩, rfl⟩)
        | upper t s =>
          exact hd2 _ (List.mem_map.2 ⟨(t, s), List.mem_filterMap.2 ⟨a, ha, by simp [e, upperOf]⟩, rfl⟩)
      · rintro ⟨d, hd⟩ x hx
        rcases hx with ⟨a, ha, hx⟩ | ⟨l, ⟨a, ha, hl⟩, u, ⟨b, hb, hu⟩, rfl⟩
        · have := hd a ha
          revert hx this
          cases classify z a <;> simp [otherOf, Role.holds]
          rintro rfl h; exact h
        · have h₁ := hd a ha
          have h₂ := hd b hb
          revert hl h₁
          cases classify z a <;> simp only [lowerOf, reduceCtorEq, false_implies]
          intro hl h₁; cases hl
          revert hu h₂
          cases classify z b <;> simp only [upperOf, reduceCtorEq, false_implies]
          intro hu h₂; cases hu
          exact (sat_bound _ _ _ v).2 (ltb_trans h₁ h₂)

/-! ## Eliminating variables from a generalized relation -/

def GRel.elim (z : Name) (r : GRel (Atom D)) : GRel (Atom D) := r.flatMap (ConstraintDB.elim z)

theorem GRel.sat_elim [DenseOrder D] (z : Name) (r : GRel (Atom D)) (v : Val D) :
    GRel.Sat (GRel.elim z r) v ↔ ∃ d, GRel.Sat r (v.upd z d) := by
  simp only [GRel.Sat, GRel.elim, List.mem_flatMap]
  constructor
  · rintro ⟨g', ⟨g, hg, hg'⟩, hs⟩
    obtain ⟨d, hd⟩ := (elim_spec z g v).1 ⟨g', hg', hs⟩
    exact ⟨d, g, hg, hd⟩
  · rintro ⟨d, g, hg, hd⟩
    obtain ⟨g', hg', hs⟩ := (elim_spec z g v).2 ⟨d, hd⟩
    exact ⟨g', ⟨g, hg, hg'⟩, hs⟩

/-- `∃` over a list of names, outermost first. -/
def existsAll [LT D] : List Name → (Val D → Prop) → Val D → Prop
  | [], U, v => U v
  | z :: zs, U, v => ∃ d, existsAll zs U (v.upd z d)

/-- Eliminate a list of names. -/
def GRel.elimAll : List Name → GRel (Atom D) → GRel (Atom D)
  | [], r => r
  | z :: zs, r => GRel.elim z (GRel.elimAll zs r)

theorem GRel.sat_elimAll [DenseOrder D] :
    (zs : List Name) → (r : GRel (Atom D)) → (v : Val D) →
      (GRel.Sat (GRel.elimAll zs r) v ↔ existsAll zs (GRel.Sat r) v)
  | [], r, v => Iff.rfl
  | z :: zs, r, v => by
    simp only [GRel.elimAll, existsAll, GRel.sat_elim]
    exact ⟨fun ⟨d, h⟩ => ⟨d, (GRel.sat_elimAll zs r _).1 h⟩,
      fun ⟨d, h⟩ => ⟨d, (GRel.sat_elimAll zs r _).2 h⟩⟩

end ConstraintDB
