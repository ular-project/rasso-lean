import Rasso.Value

/-!
# Rasso: headings, tuples and finite relations

A finite relation (`Finrel`, Racket's `finrel`) is a heading and a body. The body is a
**quotient**: two lists of tuples with the same members
are the same body, so neither the order a relation was built in nor repeats can be seen.
This follows the way Mathlib builds `Finset` (a quotient of lists), using only core
Lean's `Quotient`.

The one way to look inside a body is `Body.toList`, which gives its tuples without
repeats in a fixed canonical order (the value order of `Rasso.Value`, attribute by
attribute). `Body.toList_eq` is the proof that this is well defined: lists with the same
members give the same canonical list. Every operator is then written on that list and
taken back with `Body.ofList`, so no operator needs a proof of its own to respect the
quotient.

Conventions:

* Attribute names are `String`s (Racket's symbols). They could be wrapped as `Lean.Name`
  later without changing anything here.
* A tuple is a list of (attribute, value) pairs kept sorted by attribute name, so that
  equal tuples are equal lists. Its heading is not part of it, as in Racket (a hash).
* A heading is a list of (attribute, domain) pairs in display order. Column order is a
  matter of display; operators look attributes up by name.
-/

namespace Rasso

/-- A tuple: (attribute, value) pairs, sorted by attribute name, no attribute twice. -/
abbrev Tuple := List (String × Value)

/-- A heading: (attribute, domain) pairs in display order. -/
abbrev Heading := List (String × Domain)

def Heading.attrs (h : Heading) : List String := h.map (·.1)

/-- The same heading: the same attributes, each with the same domain (Racket's
`same-rel-heading!`). ∪, ∩ and − refuse operands whose headings differ, on finite and on
unrestricted relations alike. -/
def Heading.same (who : String) (h k : Heading) : Except String Unit :=
  if h.attrs.mergeSort (· ≤ ·) = k.attrs.mergeSort (· ≤ ·) &&
     h.all (fun (a, d) => k.lookup a == some d) then .ok ()
  else .error s!"{who}: the headings {h.attrs} and {k.attrs} differ"

/-- Headings that share no attribute (Racket's `disjoint-headings!`). × refuses operands
that share one: that is what makes it a product and not a join. -/
def Heading.disjoint (who : String) (h k : Heading) : Except String Unit :=
  let shared := h.attrs.filter k.attrs.contains
  if shared.isEmpty then .ok ()
  else .error s!"{who}: the headings share {shared}; a product's share nothing (a join's may)"

def Tuple.get? (t : Tuple) (a : String) : Option Value := t.lookup a

/-- Build a tuple from pairs in any order (sorted by attribute name). -/
def Tuple.ofPairs (ps : List (String × Value)) : Tuple :=
  ps.mergeSort fun p q => decide (p.1 ≤ q.1)

/-- The tuple restricted to some attributes. -/
def Tuple.restrict (t : Tuple) (as : List String) : Tuple := t.filter fun p => as.contains p.1

/-- Two tuples agree on every attribute they share. -/
def Tuple.agrees (t u : Tuple) : Bool :=
  t.all fun (a, v) => match u.get? a with
    | some w => v == w
    | none => true

/-- The union of two tuples that agree. -/
def Tuple.merge (t u : Tuple) : Tuple :=
  Tuple.ofPairs (t ++ u.filter fun p => (t.get? p.1).isNone)

/-! ## The canonical order on tuples -/

section TupleOrder
attribute [local instance] lexOrd

/-- The canonical order on tuples: attribute by attribute, each pair by its name and then
its value in the canonical value order (`instance : Ord Value`). -/
def Tuple.cmp (t u : Tuple) : Ordering := compare t u

instance : Std.TransCmp Tuple.cmp := by unfold Tuple.cmp; infer_instance
instance : Std.LawfulEqCmp Tuple.cmp := by unfold Tuple.cmp; infer_instance

end TupleOrder

/-- `t` sorts no later than `u`. -/
def Tuple.le (t u : Tuple) : Bool := (Tuple.cmp t u).isLE

theorem Tuple.le_trans {t u w : Tuple} (h₁ : t.le u = true) (h₂ : u.le w = true) :
    t.le w = true :=
  Std.TransCmp.isLE_trans (cmp := Tuple.cmp) h₁ h₂

theorem Tuple.le_total (t u : Tuple) : (t.le u || u.le t) = true := by
  cases h : t.le u
  · have := Std.OrientedCmp.lt_of_not_isLE (cmp := Tuple.cmp) (a := t) (b := u)
      (by simp_all [Tuple.le])
    simp [Tuple.le, this]
  · rfl

theorem Tuple.le_antisymm {t u : Tuple} (h₁ : t.le u = true) (h₂ : u.le t = true) : t = u :=
  Std.LawfulEqCmp.eq_of_compare (cmp := Tuple.cmp)
    (Std.OrientedCmp.isLE_antisymm (cmp := Tuple.cmp) h₁ h₂)

/-! ## Dropping repeats -/

/-- The list without repeats (the last copy of each member is kept). -/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => if a ∈ l then dedup l else a :: dedup l

theorem mem_dedup {α : Type} [DecidableEq α] {x : α} : ∀ {l : List α}, x ∈ dedup l ↔ x ∈ l
  | [] => by simp [dedup]
  | a :: l => by
    unfold dedup
    split
    · rename_i h
      rw [mem_dedup]
      constructor
      · exact List.mem_cons_of_mem a
      · intro hx
        cases List.mem_cons.mp hx with
        | inl e => exact e ▸ h
        | inr e => exact e
    · simp [mem_dedup]

theorem nodup_dedup {α : Type} [DecidableEq α] : ∀ (l : List α), (dedup l).Nodup
  | [] => List.nodup_nil
  | a :: l => by
    unfold dedup
    split
    · exact nodup_dedup l
    · rename_i h
      exact List.nodup_cons.mpr ⟨fun hm => h (mem_dedup.mp hm), nodup_dedup l⟩

/-! ## Bodies -/

/-- Same members. -/
def sameMembers (l l' : List Tuple) : Prop := ∀ x, x ∈ l ↔ x ∈ l'

instance bodySetoid : Setoid (List Tuple) where
  r := sameMembers
  iseqv := {
    refl := fun _ _ => Iff.rfl
    symm := fun h x => (h x).symm
    trans := fun h₁ h₂ x => (h₁ x).trans (h₂ x) }

/-- The body of a finite relation: a finite set of tuples. -/
def Body := Quotient bodySetoid

/-- The canonical list: no repeats, in tuple order. -/
def canon (l : List Tuple) : List Tuple := (dedup l).mergeSort Tuple.le

theorem mem_canon {x : Tuple} {l : List Tuple} : x ∈ canon l ↔ x ∈ l := by
  simp [canon, List.mem_mergeSort, mem_dedup]

/-- Lists with the same members have the same canonical list. -/
theorem canon_eq {l l' : List Tuple} (h : sameMembers l l') : canon l = canon l' := by
  have hp : (dedup l).Perm (dedup l') :=
    (List.perm_ext_iff_of_nodup (nodup_dedup l) (nodup_dedup l')).mpr
      fun x => by rw [mem_dedup, mem_dedup]; exact h x
  apply List.Perm.eq_of_pairwise (le := fun a b => Tuple.le a b = true)
  · exact fun _ _ _ _ h₁ h₂ => Tuple.le_antisymm h₁ h₂
  · exact List.pairwise_mergeSort (le := Tuple.le) (fun _ _ _ h₁ h₂ => Tuple.le_trans h₁ h₂) Tuple.le_total _
  · exact List.pairwise_mergeSort (le := Tuple.le) (fun _ _ _ h₁ h₂ => Tuple.le_trans h₁ h₂) Tuple.le_total _
  · exact ((List.mergeSort_perm _ _).trans hp).trans (List.mergeSort_perm _ _).symm

def Body.ofList (l : List Tuple) : Body := Quotient.mk _ l

/-- The tuples of a body, without repeats, in canonical order. -/
def Body.toList (b : Body) : List Tuple := Quotient.lift canon (fun _ _ h => canon_eq h) b

theorem Body.toList_eq {l l' : List Tuple} (h : sameMembers l l') :
    (Body.ofList l).toList = (Body.ofList l').toList := canon_eq h

theorem Body.mem_toList_ofList {x : Tuple} {l : List Tuple} :
    x ∈ (Body.ofList l).toList ↔ x ∈ l := mem_canon

/-- `toList` loses nothing: a body is determined by its canonical list. -/
theorem Body.ofList_toList (b : Body) : Body.ofList b.toList = b := by
  induction b using Quotient.ind with
  | _ l => exact Quotient.sound fun x => mem_canon

def Body.empty : Body := Body.ofList []
def Body.adjoin (t : Tuple) (b : Body) : Body := Body.ofList (t :: b.toList)
def Body.mem (t : Tuple) (b : Body) : Bool := b.toList.contains t
def Body.size (b : Body) : Nat := b.toList.length

instance : Inhabited Body := ⟨Body.empty⟩

/-! ## Finite relations -/

/-- A finite relation (Racket's `finrel`): a heading and a body. -/
structure Finrel where
  heading : Heading
  body : Body
  deriving Inhabited

namespace Finrel

def tuples (r : Finrel) : List Tuple := r.body.toList
def attrs (r : Finrel) : List String := r.heading.attrs
def domainOf? (r : Finrel) (a : String) : Option Domain := r.heading.lookup a

def ofTuples (h : Heading) (ts : List Tuple) : Finrel := ⟨h, Body.ofList ts⟩

/-- σ: the tuples that pass a test. -/
def select (p : Tuple → Except String Bool) (r : Finrel) : Except String Finrel := do
  let ts ← r.tuples.filterM p
  return ofTuples r.heading ts

/-- π onto some attributes, in the order given. Naming an attribute twice is refused: a heading,
like a map, has no key twice. -/
def project (as : List String) (r : Finrel) : Except String Finrel := do
  if as.eraseDups.length != as.length then throw s!"π: {as} names an attribute twice"
  let h ← as.mapM fun a => match r.domainOf? a with
    | some d => .ok (a, d)
    | none => .error s!"π: no attribute {a} in {r.attrs}"
  return ofTuples h (r.tuples.map (·.restrict as))

/-- The heading of a join: the left heading, then the right's own attributes; a shared
attribute's domain is the intersection (Racket's `join-heading`). -/
def joinHeading (h k : Heading) : Except String Heading := do
  let left ← h.mapM fun (a, d) => match k.lookup a with
    | some e => do return (a, ← d.inter e)
    | none => .ok (a, d)
  return left ++ k.filter fun p => (h.lookup p.1).isNone

/-- ⋈: natural join. -/
def join (r s : Finrel) : Except String Finrel := do
  let h ← joinHeading r.heading s.heading
  let ts := r.tuples.flatMap fun t =>
    (s.tuples.filter fun u => t.agrees u).map fun u => t.merge u
  return ofTuples h ts

/-- The same heading: the same attributes, each with the same domain (Racket's
`headings differ`). -/
def sameHeading (who : String) (r s : Finrel) : Except String Unit :=
  Heading.same who r.heading s.heading

/-- ∪ (same attributes). -/
def union (r s : Finrel) : Except String Finrel := do
  sameHeading "∪" r s
  return ofTuples r.heading (r.tuples ++ s.tuples)

/-- − (same attributes). -/
def diff (r s : Finrel) : Except String Finrel := do
  sameHeading "−" r s
  return ofTuples r.heading (r.tuples.filter fun t => !s.body.mem t)

/-- The new name of an attribute under a renaming (unchanged if not renamed). -/
def renameAttr (ren : List (String × String)) (a : String) : String := (ren.lookup a).getD a

/-- The heading after a renaming. -/
def renameHeading (ren : List (String × String)) (h : Heading) : Heading :=
  h.map fun (a, d) => (renameAttr ren a, d)

/-- A tuple after a renaming. -/
def renameTuple (ren : List (String × String)) (t : Tuple) : Tuple :=
  Tuple.ofPairs (t.map fun (a, v) => (renameAttr ren a, v))

end Finrel

/-- ρ's check, the same on finite and unrestricted relations (Racket's `rename-attrs`):
each renamed attribute is in the heading, and the result names no attribute twice. -/
def Heading.renameCheck (ren : List (String × String)) (h : Heading) : Except String Unit := do
  for (a, _) in ren do
    unless h.attrs.contains a do throw s!"ρ: no attribute {a} to rename in {h.attrs}"
  if (Finrel.renameHeading ren h).attrs.eraseDups.length != h.length then
    throw s!"ρ: the renaming names an attribute twice"


end Rasso
