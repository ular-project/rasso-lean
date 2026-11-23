import Rasso.ESO.Guesses
import Rasso.ESO.Meaning

/-!
# ESO: the converse (every BoolSelection query is an ESO sentence)

The forward theorem (`Rasso.ESO.Capture`) says that every ESO sentence is a multi solution
set. This file proves the other direction, for multi solution sets of a fixed shape, the
shape the forward theorem produces: Boolean function spaces under selection. In the
logic's words, the members guess the second-order relations and the condition checks them.

## The fragment, in plain words

A `Query` has two parts:

* **Guesses.** Second-order variables with arities. Each one becomes a member
  ω_sol(univ^k, holds: bool) of the multi solution set, so a candidate gives a set
  of `k`-tuples of the universe (Cadoli and Mancini's "Guess Q ⊆ DOM^k").
* **Checks.** One condition, built with `and`, `or` and `not` from tests "this
  relation has a tuple". Each relation is a relational-algebra expression (`QE`) over:
  - atoms: a symbol of the structure applied to variables (`E(x, y)`), a member applied to
    variables (`R(x)`), and equality of two variables (`x = y`);
  - natural join, union, difference (union and difference need the same variables on
    both sides), and projection (drop one variable).

An expression's
attributes are variables. Each atom is written into the program as Codd's gadget for it
(`compileP`: the data, joined with a copy of the universe for each variable, kept where
the columns equal the variables, projected onto the variables). The rest are Rasso's own
`join`, `union`, `except` and `pi`.

## The result

`Query.form_expresses`: for every well-formed query `Q` there is an ESO sentence
`Q.toSentence w` such that, on every well-formed structure `A`, the multi solution set
`Q.form A` evaluates (it is not refused) and has a candidate exactly when the sentence
holds on `A`. The sentence is read back from the query, the algebra-to-logic half of
Codd's theorem: join is `and`, union is `or`, difference is `and not`, projection is
`∃`, and "has a tuple" is `∃` over the remaining variables.

The proof uses the forward direction's `compile_meaning` for the atoms only (each atom
is the forward translation of an atomic formula) and `eval_esoMsol` and
`eval_nonEmpty` for the members and the condition, proved in other files. No file
in the proof uses `sorry`.

Conventions:

* **The fragment** is atoms, ⋈, ∪, −, π dropping one variable; conditions from "has a
  tuple" with `and`, `or`, `not`.
  σ is not in the fragment: its only use here, equality of variables, is the atom
  `x = y`. Widening the fragment (σ with other tests, γ, extend) is future work.
* **Attributes are variables.** An expression's attributes are `x_v` for its variables
  `v`, all with the universe as their domain, as in the forward construction.
* **Projection of a variable that is not there** changes nothing (and is read back as
  the formula itself, not as `∃`, which would differ on an empty universe).
* The members are the forward construction's (`membersP`), so a query with no
  second-order variables has one unused member, as there.
-/

namespace Rasso.ESO

open Rasso

/-! ## The fragment -/

/-- Relational-algebra expressions over atoms, whose attributes are variables. -/
inductive QE where
  /-- A symbol of the structure applied to variables. -/
  | rel (i : String) (args : List String)
  /-- A member applied to variables. -/
  | member (j : String) (args : List String)
  /-- Equality of two variables. -/
  | eq (x y : String)
  | join (a b : QE)
  | union (a b : QE)
  | diff (a b : QE)
  /-- Drop the variable `x`. -/
  | proj (x : String) (a : QE)
  /-- Every assignment to the variables, minus the expression's. -/
  | not (a : QE)
  deriving Repr, Inhabited

namespace QE

/-- The variables: the attributes of the expression's relation, without repeats. -/
def hdr : QE → List String
  | rel _ args => args.eraseDups
  | member _ args => args.eraseDups
  | eq x y => [x, y].eraseDups
  | join a b => a.hdr ++ b.hdr.filter fun y => !a.hdr.contains y
  | union a _ => a.hdr
  | diff a _ => a.hdr
  | proj x a => a.hdr.filter (· != x)
  | not a => a.hdr

/-- Union and difference combine expressions with the same variables. -/
def WF : QE → Prop
  | join a b => a.WF ∧ b.WF
  | union a b => a.WF ∧ b.WF ∧ ∀ y, y ∈ a.hdr ↔ y ∈ b.hdr
  | diff a b => a.WF ∧ b.WF ∧ ∀ y, y ∈ a.hdr ↔ y ∈ b.hdr
  | proj _ a => a.WF
  | not a => a.WF
  | _ => True

/-- Read an expression back as a formula (Codd's theorem, algebra to logic). -/
def toFO : QE → FO
  | rel i args => .rel i args
  | member j args => .gvar j args
  | eq x y => .eq x y
  | join a b => .and a.toFO b.toFO
  | union a b => .or a.toFO b.toFO
  | diff a b => .and a.toFO (.not b.toFO)
  | proj x a => if a.hdr.contains x then .ex x a.toFO else a.toFO
  | not a => .not a.toFO

/-- The Rasso form of an expression, on structure `A`, with members of arities `ar`. -/
def toExpr (A : Str) (ar : List (String × Nat)) : QE → Expr
  | rel i args => compileP (univLit A) (relLit A) ar (.rel i args)
  | member j args => compileP (univLit A) (relLit A) ar (.gvar j args)
  | eq x y => compileP (univLit A) (relLit A) ar (.eq x y)
  | join a b => .nary .join [a.toExpr A ar, b.toExpr A ar]
  | union a b => .nary .union [a.toExpr A ar, b.toExpr A ar]
  | diff a b => .nary .except [a.toExpr A ar, b.toExpr A ar]
  | proj x a => .project ((a.hdr.filter (· != x)).map varAttr) (a.toExpr A ar)
  | not a => .nary .except [domOfP (univLit A) a.hdr, a.toExpr A ar]

/-- Drop each of some variables in turn. -/
def projs : List String → QE → QE
  | [], e => e
  | x :: xs, e => projs xs (.proj x e)

/-- The expression with all its variables dropped: "has a tuple". -/
def close (e : QE) : QE := projs e.hdr e

end QE

/-- A condition: "has a tuple" tests, combined with `and`, `or`, `not`. -/
inductive QC where
  | some (e : QE)
  | not (c : QC)
  | and (c d : QC)
  | or (c d : QC)
  deriving Repr, Inhabited

namespace QC

def WF : QC → Prop
  | some e => e.WF
  | not c => c.WF
  | and c d => c.WF ∧ d.WF
  | or c d => c.WF ∧ d.WF

def toFO : QC → FO
  | some e => e.close.toFO
  | not c => .not c.toFO
  | and c d => .and c.toFO d.toFO
  | or c d => .or c.toFO d.toFO

def toCond (A : Str) (ar : List (String × Nat)) : QC → Cond
  | some e => nonEmpty (e.close.toExpr A ar)
  | not c => .not (c.toCond A ar)
  | and c d => .and [c.toCond A ar, d.toCond A ar]
  | or c d => .or [c.toCond A ar, d.toCond A ar]

end QC

/-- A BoolSelection query: the arities of its members, and the condition. -/
structure Query where
  ar : List (String × Nat)
  cond : QC
  deriving Repr

def Query.WF (Q : Query) : Prop := Q.cond.WF

/-- The multi solution set of query `Q` on structure `A`. `A` enters only as data. -/
def Query.form (Q : Query) (A : Str) : Expr :=
  .omegaMsol (membersP (univLit A) Q.ar) (some (Q.cond.toCond A Q.ar))

/-! ## Lists, names and headings -/

namespace Converse

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] : (l : List α) → l.eraseDups.Nodup
  | [] => by simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
  | a :: l => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨fun h => ?_, nodup_eraseDups _⟩
    have := (List.mem_filter.mp (List.mem_eraseDups.mp h)).2
    simp at this
termination_by l => l.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem varAttr_inj {a b : String} (h : varAttr a = varAttr b) : a = b :=
  (String.append_right_inj "x_").mp h

theorem mem_map_varAttr {xs : List String} {y : String} :
    varAttr y ∈ xs.map varAttr ↔ y ∈ xs :=
  ⟨fun h => by
    obtain ⟨z, hz, e⟩ := List.mem_map.mp h
    exact varAttr_inj e ▸ hz, fun h => List.mem_map_of_mem h⟩

theorem nodup_map_varAttr : {xs : List String} → xs.Nodup → (xs.map varAttr).Nodup
  | [], _ => List.nodup_nil
  | _ :: _, hn => by
    have ⟨h1, h2⟩ := List.nodup_cons.mp hn
    exact List.nodup_cons.mpr ⟨fun h => h1 (mem_map_varAttr.mp h), nodup_map_varAttr h2⟩

theorem attrs_VH (A : Str) (xs : List String) : (VH A xs).attrs = xs.map varAttr := by
  simp [VH, Heading.attrs, List.map_map, Function.comp_def]

theorem lookup_VH (A : Str) (xs : List String) (a : String) :
    (VH A xs).lookup a = if a ∈ xs.map varAttr then some (DD A) else none := by
  induction xs with
  | nil => simp [VH]
  | cons x xs ih =>
    show List.lookup a ((varAttr x, DD A) :: VH A xs) = _
    unfold List.lookup
    cases h : a == varAttr x
    · have h' : a ≠ varAttr x := by simpa using h
      simp only [ih, List.map_cons, List.mem_cons, h', false_or]
    · have h' : a = varAttr x := by simpa using h
      simp [h']

/-- Two variable headings with the same variables look up alike. -/
theorem lookup_VH_congr (A : Str) {xs ys : List String} (h : ∀ y, y ∈ xs ↔ y ∈ ys) (a : String) :
    (VH A xs).lookup a = (VH A ys).lookup a := by
  rw [lookup_VH, lookup_VH]
  have : a ∈ xs.map varAttr ↔ a ∈ ys.map varAttr := by
    simp only [List.mem_map]
    exact ⟨fun ⟨y, hy, e⟩ => ⟨y, (h y).mp hy, e⟩, fun ⟨y, hy, e⟩ => ⟨y, (h y).mpr hy, e⟩⟩
  by_cases h' : a ∈ xs.map varAttr
  · rw [ite_eq_left h', ite_eq_left (this.mp h')]
  · rw [ite_eq_right h', ite_eq_right (fun h'' => h' (this.mpr h''))]

/-! ## Representations -/

/-- `Rep` depends on the heading only through its look-ups, and on the property only
on tuples that fit. -/
theorem Rep.congr {H K : Heading} {P Q : Tuple → Prop} {r : Finrel} (hr : Rep H P r)
    (hk : ∀ a, H.lookup a = K.lookup a) (hp : ∀ t, t.Fits K → (P t ↔ Q t)) : Rep K Q r where
  wf := hr.wf
  head a := (hr.head a).trans (hk a)
  mem t := by
    rw [hr.mem t]
    constructor
    · rintro ⟨f, h⟩
      have f' := f.congr hk
      exact ⟨f', (hp t f').mp h⟩
    · rintro ⟨f, h⟩
      exact ⟨f.congr fun a => (hk a).symm, (hp t f).mpr h⟩

theorem mem_of_lookup {t : List (String × Value)} {a : String} {v : Value}
    (h : t.lookup a = some v) : (a, v) ∈ t := by
  induction t with
  | nil => cases h
  | cons p t ih =>
    unfold List.lookup at h
    cases e : a == p.1
    · rw [e] at h; exact List.mem_cons_of_mem _ (ih h)
    · rw [e] at h
      cases h
      have : a = p.1 := by simpa using e
      subst this; exact List.mem_cons_self ..

/-- In a tuple that fits the variables `xs`, each variable has a value in the universe. -/
theorem fits_get (A : Str) {xs : List String} {t : Tuple} (f : t.Fits (VH A xs))
    {y : String} (hy : y ∈ xs) : t.get? (varAttr y) = some (asg t y) ∧ asg t y ∈ A.univ := by
  have hin : varAttr y ∈ (VH A xs).attrs := by rw [attrs_VH]; exact mem_map_varAttr.mpr hy
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((f.get?_isSome _).mpr hin)
  have ha : asg t y = v := by simp [asg, hv]
  refine ⟨by rw [hv, ha], ?_⟩
  rw [ha]
  have hp : (varAttr y, v) ∈ t := mem_of_lookup hv
  have hd : (VH A xs).lookup (varAttr y) = some (DD A) := by
    rw [lookup_VH, ite_eq_left (mem_map_varAttr.mpr hy)]
  exact (DD_mem A v).mp (f.dom _ hp _ hd)

theorem asg_restrict {as : List String} {t : Tuple} {y : String} (h : varAttr y ∈ as) :
    asg (t.restrict as) y = asg t y := by
  simp only [asg, get?_restrict, ite_eq_left h]

/-- The tuple that gives the variables `ys` the values of `ρ`. -/
abbrev tupleOf (ys : List String) (ρ : String → Value) : Tuple :=
  Tuple.ofPairs (ys.map fun y => (varAttr y, ρ y))

theorem lookup_map_varAttr {ys : List String} {ρ : String → Value} {y : String} (hy : y ∈ ys) :
    (ys.map fun z => (varAttr z, ρ z)).lookup (varAttr y) = some (ρ y) := by
  induction ys with
  | nil => cases hy
  | cons z zs ih =>
    simp only [List.map_cons]
    unfold List.lookup
    by_cases e : y = z
    · subst e; simp
    · have : (varAttr y == varAttr z) = false := by
        simpa using fun h => e (varAttr_inj h)
      rw [this]
      exact ih ((List.mem_cons.mp hy).resolve_left e)

theorem lookup_map_varAttr_none {ys : List String} {ρ : String → Value} {a : String}
    (ha : a ∉ ys.map varAttr) : (ys.map fun z => (varAttr z, ρ z)).lookup a = none := by
  induction ys with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at ha ⊢
    unfold List.lookup
    have : (a == varAttr z) = false := by simpa using ha.1
    rw [this]; exact ih ha.2

theorem keys_tupleOf {ys : List String} {ρ : String → Value} :
    ((ys.map fun y => (varAttr y, ρ y)).map (·.1)) = ys.map varAttr := by
  simp [List.map_map, Function.comp_def]

theorem sorted_tupleOf {ys : List String} (hn : ys.Nodup) (ρ : String → Value) :
    Tuple.Sorted (tupleOf ys ρ) :=
  Tuple.sorted_ofPairs (by rw [keys_tupleOf]; exact nodup_map_varAttr hn)

theorem get_tupleOf {ys : List String} (hn : ys.Nodup) (ρ : String → Value) {y : String}
    (hy : y ∈ ys) : (tupleOf ys ρ).get? (varAttr y) = some (ρ y) := by
  rw [tupleOf, Tuple.get?_ofPairs (by rw [keys_tupleOf]; exact nodup_map_varAttr hn)]
  exact lookup_map_varAttr hy

theorem get_tupleOf_none {ys : List String} (hn : ys.Nodup) (ρ : String → Value) {a : String}
    (ha : a ∉ ys.map varAttr) : (tupleOf ys ρ).get? a = none := by
  rw [tupleOf, Tuple.get?_ofPairs (by rw [keys_tupleOf]; exact nodup_map_varAttr hn)]
  exact lookup_map_varAttr_none ha

theorem asg_tupleOf {ys : List String} (hn : ys.Nodup) (ρ : String → Value) {y : String}
    (hy : y ∈ ys) : asg (tupleOf ys ρ) y = ρ y := by
  simp only [asg]; rw [get_tupleOf hn ρ hy]; rfl

theorem fits_tupleOf (A : Str) {ys : List String} (hn : ys.Nodup) {ρ : String → Value}
    (hρ : ∀ y ∈ ys, ρ y ∈ A.univ) : (tupleOf ys ρ).Fits (VH A ys) where
  sorted := ofPairs_sorted (by rw [keys_tupleOf]; exact nodup_map_varAttr hn)
  attrs a := by
    rw [tupleOf, attrs_ofPairs, keys_tupleOf, attrs_VH]
  dom p hp d hd := by
    rw [tupleOf, mem_ofPairs] at hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
    rw [lookup_VH, ite_eq_left (mem_map_varAttr.mpr hy)] at hd
    cases hd
    exact (DD_mem A _).mpr (hρ y hy)

/-- Every tuple that fits the variables `ys` is the tuple of its own assignment. -/
theorem eq_tupleOf (A : Str) {ys : List String} (hn : ys.Nodup) {t : Tuple}
    (f : t.Fits (VH A ys)) : t = tupleOf ys (asg t) := by
  apply Tuple.ext_get? f.sorted (sorted_tupleOf hn _)
  intro a
  by_cases ha : a ∈ ys.map varAttr
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
    rw [get_tupleOf hn _ hy, (fits_get A f hy).1]
  · rw [get_tupleOf_none hn _ ha, f.get?_none (by rw [attrs_VH]; exact ha)]

/-- Restricting a tuple of the variables `ys` to all of them changes nothing. -/
theorem restrict_all (A : Str) {ys : List String} {t : Tuple}
    (f : t.Fits (VH A ys)) : t.restrict (ys.map varAttr) = t := by
  apply Tuple.ext_get? (sorted_restrict f.sorted) f.sorted
  intro c
  rw [get?_restrict]
  split
  · rfl
  · rename_i hc; exact (f.get?_none (by rw [attrs_VH]; exact hc)).symm

/-! ## Facts about the read-back -/

theorem mem_hdr_join {a b : QE} {y : String} : y ∈ (QE.join a b).hdr ↔ y ∈ a.hdr ∨ y ∈ b.hdr := by
  simp only [QE.hdr, List.mem_append, List.mem_filter]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact .inl h
    · exact .inr h
  · rintro (h | h)
    · exact .inl h
    · by_cases ha : y ∈ a.hdr
      · exact .inl ha
      · exact .inr ⟨h, by simpa using ha⟩

theorem mem_hdr_proj {x : String} {a : QE} {y : String} :
    y ∈ (QE.proj x a).hdr ↔ y ∈ a.hdr ∧ y ≠ x := by
  simp [QE.hdr, List.mem_filter]

theorem nodup_hdr : (e : QE) → e.hdr.Nodup
  | .rel _ args => nodup_eraseDups args
  | .member _ args => nodup_eraseDups args
  | .eq x y => nodup_eraseDups [x, y]
  | .join a b => by
    simp only [QE.hdr]
    refine List.nodup_append.mpr ⟨nodup_hdr a, (nodup_hdr b).filter _, ?_⟩
    intro y hy z hz e
    subst e
    have := (List.mem_filter.mp hz).2
    simp [hy] at this
  | .union a _ => nodup_hdr a
  | .diff a _ => nodup_hdr a
  | .proj _ a => (nodup_hdr a).filter _
  | .not a => nodup_hdr a

/-- The read-back's free variables are among the expression's variables. -/
theorem fv_toFO : (e : QE) → e.WF → ∀ y ∈ e.toFO.fv, y ∈ e.hdr
  | .rel _ args, _, y, h => List.mem_eraseDups.mpr h
  | .member _ args, _, y, h => List.mem_eraseDups.mpr h
  | .eq x z, _, y, h => List.mem_eraseDups.mpr h
  | .join a b, w, y, h => by
    simp only [QE.toFO, FO.fv, List.mem_append] at h
    exact mem_hdr_join.mpr (h.imp (fv_toFO a w.1 y) (fv_toFO b w.2 y))
  | .union a b, w, y, h => by
    simp only [QE.toFO, FO.fv, List.mem_append] at h
    exact h.elim (fv_toFO a w.1 y) fun h => (w.2.2 y).mpr (fv_toFO b w.2.1 y h)
  | .diff a b, w, y, h => by
    simp only [QE.toFO, FO.fv, List.mem_append] at h
    exact h.elim (fv_toFO a w.1 y) fun h => (w.2.2 y).mpr (fv_toFO b w.2.1 y h)
  | .proj x a, w, y, h => by
    simp only [QE.toFO] at h
    split at h
    · simp only [FO.fv, List.mem_filter] at h
      exact mem_hdr_proj.mpr ⟨fv_toFO a w y h.1, by simpa using h.2⟩
    · rename_i hx
      have hy := fv_toFO a w y h
      exact mem_hdr_proj.mpr ⟨hy, fun e => hx (by subst e; simpa using hy)⟩
  | .not a, w, y, h => fv_toFO a w y h

theorem hdr_projs : (xs : List String) → (e : QE) →
    ∀ y, y ∈ (QE.projs xs e).hdr ↔ y ∈ e.hdr ∧ y ∉ xs
  | [], e, y => by simp [QE.projs]
  | x :: xs, e, y => by
    rw [QE.projs, hdr_projs xs, mem_hdr_proj]
    simp only [List.mem_cons, not_or]
    constructor
    · rintro ⟨⟨h, h1⟩, h2⟩; exact ⟨h, h1, h2⟩
    · rintro ⟨h, h1, h2⟩; exact ⟨⟨h, h1⟩, h2⟩

theorem wf_projs : (xs : List String) → {e : QE} → e.WF → (QE.projs xs e).WF
  | [], _, w => w
  | _ :: xs, _, w => wf_projs xs (e := .proj _ _) w

theorem hdr_close (e : QE) : e.close.hdr = [] := by
  match h : e.close.hdr with
  | [] => rfl
  | y :: _ =>
    have := (hdr_projs e.hdr e y).mp (by rw [QE.close] at h; rw [h]; exact List.mem_cons_self ..)
    exact absurd this.1 this.2

theorem fv_close (e : QE) (w : e.WF) : e.close.toFO.fv = [] := by
  match h : e.close.toFO.fv with
  | [] => rfl
  | y :: _ =>
    have := fv_toFO e.close (wf_projs _ w) y (by rw [h]; exact List.mem_cons_self ..)
    rw [hdr_close] at this; cases this

theorem fv_QC : (c : QC) → c.WF → c.toFO.fv = []
  | .some e, w => fv_close e w
  | .not c, w => by simp only [QC.toFO, FO.fv]; exact fv_QC c w
  | .and c d, w => by simp only [QC.toFO, FO.fv]; rw [fv_QC c w.1, fv_QC d w.2]; rfl
  | .or c d, w => by simp only [QC.toFO, FO.fv]; rw [fv_QC c w.1, fv_QC d w.2]; rfl

/-! ## What an expression evaluates to -/

section Meaning

variable (A : Str) (hA : A.WF) (hC : A.Comparable) (ar : List (String × Nat)) (G : Guess)
  (hG : G.Fits A ar) (E : Env) (hE : GuessEnv A ar G (inCondition E))

/-- The property an expression's relation has: its tuples are the assignments that
satisfy its read-back. -/
abbrev Meant (e : QE) (r : Finrel) : Prop :=
  Rep (VH A e.hdr) (fun t => e.toFO.Sat A G (asg t)) r

/-- Projection: dropping a variable that is there is `∃` over the universe. -/
theorem proj_iff {ys : List String} (hn : ys.Nodup) {x : String} (hx : x ∈ ys) {φ : FO}
    (hfv : ∀ y ∈ φ.fv, y ∈ ys) {t : Tuple} (ft : t.Fits (VH A (ys.filter (· != x)))) :
    (∃ u, u.Fits (VH A ys) ∧ φ.Sat A G (asg u) ∧
        u.restrict ((ys.filter (· != x)).map varAttr) = t) ↔
      ∃ v ∈ A.univ, φ.Sat A G (upd (asg t) x v) := by
  have hmem : ∀ {y}, y ∈ ys → y ≠ x → varAttr y ∈ (ys.filter (· != x)).map varAttr :=
    fun hy hyx => mem_map_varAttr.mpr (List.mem_filter.mpr ⟨hy, by simpa using hyx⟩)
  constructor
  · rintro ⟨u, fu, s, rfl⟩
    refine ⟨asg u x, (fits_get A fu hx).2, (FO.Sat_congr φ fun y hy => ?_).mp s⟩
    if hyx : y = x then
      subst hyx; rw [upd_same]
    else
      rw [upd_other hyx, asg_restrict (hmem (hfv y hy) hyx)]
  · rintro ⟨v, hv, s⟩
    let ρ := upd (asg t) x v
    have hρ : ∀ y ∈ ys, ρ y ∈ A.univ := fun y hy => by
      if hyx : y = x then
        subst hyx; simp only [ρ, upd_same]; exact hv
      else
        simp only [ρ, upd_other hyx]
        exact (fits_get A ft (List.mem_filter.mpr ⟨hy, by simpa using hyx⟩)).2
    refine ⟨tupleOf ys ρ, fits_tupleOf A hn hρ, (FO.Sat_congr φ fun y hy => ?_).mpr s, ?_⟩
    · exact asg_tupleOf hn ρ (hfv y hy)
    · apply Tuple.ext_get? (sorted_restrict (sorted_tupleOf hn ρ)) ft.sorted
      intro a
      rw [get?_restrict]
      split
      · rename_i ha
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
        have ⟨hy1, hy2⟩ := List.mem_filter.mp hy
        have hyx : y ≠ x := by simpa using hy2
        rw [get_tupleOf hn ρ hy1, (fits_get A ft hy).1]
        simp only [ρ, upd_other hyx]
      · rename_i ha
        exact (ft.get?_none (by rw [attrs_VH]; exact ha)).symm

include hA hC hG hE in
/-- **Codd's theorem, algebra to logic.** Each well-formed expression evaluates, and its
relation holds exactly the assignments (over the universe) that satisfy its read-back. -/
theorem eval_QE : (e : QE) → e.WF → ∃ r, Expr.eval (inCondition E) [] (e.toExpr A ar) = .ok (.finrel r) ∧
    Meant A G e r
  | .rel i args, _ => compile_meaning A hA hC ar G hG E hE (.rel i args)
  | .member j args, _ => compile_meaning A hA hC ar G hG E hE (.gvar j args)
  | .eq x y, _ => compile_meaning A hA hC ar G hG E hE (.eq x y)
  | .join a b, w => by
    obtain ⟨r, hr, mr⟩ := eval_QE a w.1
    obtain ⟨s, hs, ms⟩ := eval_QE b w.2
    obtain ⟨q, hq, mq⟩ := rep_join mr ms fun c d e hd he => by
      rw [lookup_VH] at hd he
      split at hd <;> split at he <;> simp_all
    refine ⟨q, eval_join2 hr hs hq, Rep.congr mq (fun c => ?_) fun t ft => ?_⟩
    · rw [lookup_joinH, lookup_VH, lookup_VH, lookup_VH]
      have : c ∈ (QE.join a b).hdr.map varAttr ↔ c ∈ a.hdr.map varAttr ∨ c ∈ b.hdr.map varAttr := by
        simp only [List.mem_map]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact (mem_hdr_join.mp hy).imp (fun h => ⟨y, h, rfl⟩) (fun h => ⟨y, h, rfl⟩)
        · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
          · exact ⟨y, mem_hdr_join.mpr (.inl hy), rfl⟩
          · exact ⟨y, mem_hdr_join.mpr (.inr hy), rfl⟩
      by_cases h1 : c ∈ a.hdr.map varAttr
      · rw [ite_eq_left h1, ite_eq_left (this.mpr (.inl h1))]; rfl
      · rw [ite_eq_right h1]
        by_cases h2 : c ∈ b.hdr.map varAttr
        · rw [ite_eq_left h2, ite_eq_left (this.mpr (.inr h2))]; rfl
        · rw [ite_eq_right h2, ite_eq_right (fun h => (this.mp h).elim h1 h2)]; rfl
    · simp only [QE.toFO, FO.Sat]
      rw [attrs_VH, attrs_VH]
      apply and_congr
      · exact FO.Sat_congr _ fun y hy =>
          asg_restrict (mem_map_varAttr.mpr (fv_toFO a w.1 y hy))
      · exact FO.Sat_congr _ fun y hy =>
          asg_restrict (mem_map_varAttr.mpr (fv_toFO b w.2 y hy))
  | .union a b, w => by
    obtain ⟨r, hr, mr⟩ := eval_QE a w.1
    obtain ⟨s, hs, ms⟩ := eval_QE b w.2.1
    have ms' := Rep.congr ms (K := VH A a.hdr) (lookup_VH_congr A fun y => (w.2.2 y).symm)
      (Q := fun t => b.toFO.Sat A G (asg t)) fun _ _ => Iff.rfl
    obtain ⟨q, hq, mq⟩ := rep_union mr ms'
    exact ⟨q, eval_union2 hr hs hq, mq⟩
  | .diff a b, w => by
    obtain ⟨r, hr, mr⟩ := eval_QE a w.1
    obtain ⟨s, hs, ms⟩ := eval_QE b w.2.1
    have ms' := Rep.congr ms (K := VH A a.hdr) (lookup_VH_congr A fun y => (w.2.2 y).symm)
      (Q := fun t => b.toFO.Sat A G (asg t)) fun _ _ => Iff.rfl
    obtain ⟨q, hq, mq⟩ := rep_diff mr ms'
    exact ⟨q, eval_except2 hr hs hq, mq⟩
  | .proj x a, w => by
    obtain ⟨r, hr, mr⟩ := eval_QE a w
    have hn := nodup_hdr a
    have has : ∀ c ∈ (a.hdr.filter (· != x)).map varAttr, c ∈ (VH A a.hdr).attrs := fun c hc => by
      rw [attrs_VH]
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
      exact List.mem_map_of_mem (List.mem_filter.mp hy).1
    obtain ⟨s, hs, ms⟩ := rep_project mr has (nodup_map_varAttr (hn.filter _))
    refine ⟨s, eval_project hr hs, Rep.congr ms (fun c => ?_) fun t ft => ?_⟩
    · rw [lookup_restrictH, lookup_VH, lookup_VH]
      by_cases hc : c ∈ (a.hdr.filter (· != x)).map varAttr
      · have hc' : c ∈ a.hdr.map varAttr := by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
          exact List.mem_map_of_mem (List.mem_filter.mp hy).1
        rw [ite_eq_left hc, ite_eq_left hc', ite_eq_left (show c ∈ (QE.proj x a).hdr.map varAttr from hc)]
      · rw [ite_eq_right hc, ite_eq_right (show c ∉ (QE.proj x a).hdr.map varAttr from hc)]
    · simp only [QE.toFO]
      split
      · rename_i hx
        exact proj_iff A G hn (List.contains_iff_mem.mp hx) (fv_toFO a w) ft
      · rename_i hx
        have hx : x ∉ a.hdr := fun h => hx (List.contains_iff_mem.mpr h)
        have hfilt : a.hdr.filter (· != x) = a.hdr :=
          List.filter_eq_self.mpr fun y hy => by
            have : y ≠ x := fun e => hx (by rw [← e]; exact hy)
            simpa using this
        have ft' : t.Fits (VH A a.hdr) := by simpa only [QE.hdr, hfilt] using ft
        rw [hfilt]
        constructor
        · rintro ⟨u, fu, su, rfl⟩
          rw [restrict_all A fu]; exact su
        · intro st
          exact ⟨t, ft', st, restrict_all A ft'⟩
  | .not a, w => by
    obtain ⟨r, hr, mr⟩ := eval_QE a w
    obtain ⟨d, hd, md⟩ := repV_domOf A (inCondition E) (nodup_hdr a)
    obtain ⟨q, hq, mq⟩ := repV_diff md mr
    exact ⟨q, eval_except2 hd hr hq, Rep.congr mq (fun _ => rfl) fun t _ => by
      simp only [QE.toFO, FO.Sat]; exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩⟩

/-- A tuple fits the empty heading exactly when it is the empty tuple. -/
theorem fits_nil_iff {t : Tuple} : t.Fits (VH A []) ↔ t = [] := by
  constructor
  · intro f
    match t, f with
    | [], _ => rfl
    | p :: _, f =>
      have := (f.attrs p.1).mp (List.mem_cons_self ..)
      simp [attrs_VH] at this
  · rintro rfl
    exact ⟨List.Pairwise.nil, fun a => by simp [attrs_VH, Tuple.attrs], fun p hp => by cases hp⟩

include hA hC hG hE in
/-- A condition evaluates to the truth of its read-back. -/
theorem eval_QC : (c : QC) → c.WF →
    Cond.eval (inCondition E) [] (c.toCond A ar) = .ok (decide (c.toFO.Sat A G (fun _ => default)))
  | .some e, w => by
    obtain ⟨r, hr, mr⟩ := eval_QE A hA hC ar G hG E hE e.close (wf_projs _ w)
    rw [QC.toCond, eval_nonEmpty hr]
    have h0 : ∀ y, asg ([] : Tuple) y = (fun _ => default) y := fun y => rfl
    have key : (∃ t, t ∈ r.tuples) ↔ e.close.toFO.Sat A G (fun _ => default) := by
      constructor
      · rintro ⟨t, ht⟩
        have ⟨f, s⟩ := (mr.mem t).mp ht
        rw [hdr_close] at f
        rw [(fits_nil_iff A).mp f] at s
        exact (FO.Sat_congr _ fun y _ => h0 y).mp s
      · intro s
        refine ⟨[], (mr.mem []).mpr ⟨?_, (FO.Sat_congr _ fun y _ => h0 y).mpr s⟩⟩
        rw [hdr_close]; exact (fits_nil_iff A).mpr rfl
    simp only [QC.toFO]
    cases h : r.tuples with
    | nil =>
      have : ¬ e.close.toFO.Sat A G (fun _ => default) := fun s => by
        obtain ⟨t, ht⟩ := key.mpr s; rw [h] at ht; cases ht
      simp [this]
    | cons t ts =>
      have : e.close.toFO.Sat A G (fun _ => default) := key.mp ⟨t, by rw [h]; exact List.mem_cons_self ..⟩
      simp [this]
  | .not c, w => by
    simp only [QC.toCond, QC.toFO, FO.Sat]
    rw [Cond.eval, eval_QC c w]
    simp [bind, Except.bind, pure, Except.pure]
  | .and c d, w => by
    simp only [QC.toCond, QC.toFO, FO.Sat]
    rw [Cond.eval]
    simp [List.attach, List.attachWith, List.allM, eval_QC c w.1, eval_QC d w.2, bind,
      Except.bind, pure, Except.pure]
    by_cases h1 : c.toFO.Sat A G (fun _ => default) <;>
      by_cases h2 : d.toFO.Sat A G (fun _ => default) <;> simp [h1, h2]
  | .or c d, w => by
    simp only [QC.toCond, QC.toFO, FO.Sat]
    rw [Cond.eval]
    simp [List.attach, List.attachWith, List.anyM, eval_QC c w.1, eval_QC d w.2, bind,
      Except.bind, pure, Except.pure]
    by_cases h1 : c.toFO.Sat A G (fun _ => default) <;>
      by_cases h2 : d.toFO.Sat A G (fun _ => default) <;> simp [h1, h2]

end Meaning

end Converse

open Converse

/-! ## The converse -/

/-- The ESO sentence of a query: the same second-order variables, and the condition
read back as a formula. -/
def Query.toSentence (Q : Query) (w : Q.WF) : Sentence where
  ar := Q.ar
  φ := Q.cond.toFO
  closed := by rw [fv_QC Q.cond w]; rfl

/-- **The converse (F2).** On every well-formed structure, the multi solution set of
a well-formed BoolSelection query evaluates, and it has a candidate exactly when the
query's ESO sentence holds. -/
theorem Query.form_expresses (Q : Query) (w : Q.WF) (A : Str) (hA : A.WF) (hC : A.Comparable) :
    ∃ m, Expr.eval [] [] (Q.form A) = .ok (.msol m) ∧
      ((∃ db, db ∈ m.candidates) ↔ (Q.toSentence w).Holds A) := by
  obtain ⟨m, hm, hiff⟩ := eval_esoMsol A Q.ar (Q.cond.toCond A Q.ar)
    (fun G => decide (Q.cond.toFO.Sat A G (fun _ => default)))
    (fun G E hG hE => eval_QC A hA hC Q.ar G hG E hE Q.cond w)
  refine ⟨m, hm, hiff.trans ?_⟩
  exact ⟨fun ⟨G, hG, h⟩ => ⟨G, hG, of_decide_eq_true h⟩, fun ⟨G, hG, h⟩ => ⟨G, hG, decide_eq_true h⟩⟩

/-- Every BoolSelection query is defined by an ESO sentence: one sentence for all
well-formed structures. -/
theorem query_definable_in_ESO (Q : Query) (w : Q.WF) :
    ∃ ψ : Sentence, ∀ A : Str, A.WF → A.Comparable →
      ∃ m, Expr.eval [] [] (Q.form A) = .ok (.msol m) ∧ ((∃ db, db ∈ m.candidates) ↔ ψ.Holds A) :=
  ⟨Q.toSentence w, Q.form_expresses w⟩

end Rasso.ESO
