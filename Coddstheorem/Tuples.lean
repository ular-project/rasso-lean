import Coddstheorem.Schema
import Rasso.Rep

/-!
# Codd's theorem for Rasso: tuples over one domain

Facts about tuples whose
heading gives every attribute the one domain `D`, used by both translations.

* `Match as μ ρ t`: for each attribute `a` of `as`, the tuple `t` holds the value that the
  assignment `ρ` gives the variable `μ a`. This is how a tuple and an assignment of the
  calculus correspond.
* `tupOf as μ ρ`: the one tuple over `as` that matches `ρ`.
-/

set_option linter.deprecated false

namespace Coddstheorem

open Rasso

theorem lookup_headerOf (D : Domain) (as : List String) (a : String) :
    (headerOf D as).lookup a = if a ∈ as then some D else none := by
  induction as with
  | nil => rfl
  | cons b bs ih =>
    simp only [headerOf, List.map_cons, List.lookup_cons, List.mem_cons] at ih ⊢
    by_cases e : a = b
    · subst e; simp
    · have : (a == b) = false := by simp [e]
      rw [this, ih]; simp [e]

theorem attrs_headerOf (D : Domain) (as : List String) : (headerOf D as).attrs = as := by
  simp [headerOf, Heading.attrs, List.map_map, Function.comp_def]

theorem headerOf_congr {D : Domain} {as bs : List String} (h : ∀ a, a ∈ as ↔ a ∈ bs) (a : String) :
    (headerOf D as).lookup a = (headerOf D bs).lookup a := by
  rw [lookup_headerOf, lookup_headerOf]
  by_cases ha : a ∈ as
  · rw [if_pos ha, if_pos ((h a).mp ha)]
  · rw [if_neg ha, if_neg (fun hb => ha ((h a).mpr hb))]

/-- `r`'s heading is `as`, every attribute with domain `D`, up to order. -/
def HeadIs (D : Domain) (as : List String) (h : Heading) : Prop :=
  ∀ a, h.lookup a = (headerOf D as).lookup a

theorem fits_of_mem {D : Domain} {as : List String} {r : Finrel} (hw : r.WF)
    (hh : HeadIs D as r.heading) {t : Tuple} (ht : t ∈ r.tuples) : t.Fits (headerOf D as) :=
  (hw.fits t ht).congr hh

/-- The tuple `t` gives each attribute of `as` the value `ρ` gives its variable. -/
def Match (as : List String) (μ : String → String) (ρ : String → Value) (t : Tuple) : Prop :=
  ∀ a ∈ as, t.get? a = some (ρ (μ a))

/-- The tuple over `as` that matches `ρ`. -/
def tupOf (as : List String) (μ : String → String) (ρ : String → Value) : Tuple :=
  Tuple.ofPairs (as.map fun a => (a, ρ (μ a)))

theorem keys_tupOf (as : List String) (μ : String → String) (ρ : String → Value) :
    ((as.map fun a => (a, ρ (μ a))).map (·.1)) = as := by
  simp [List.map_map, Function.comp_def]

theorem lookup_map_pair {β : Type} (f : String → β) (a : String) :
    ∀ (as : List String), (as.map fun b => (b, f b)).lookup a = if a ∈ as then some (f a) else none
  | [] => rfl
  | b :: bs => by
    simp only [List.map_cons, List.lookup_cons, List.mem_cons]
    by_cases e : a = b
    · subst e; simp
    · have : (a == b) = false := by simp [e]
      rw [this, lookup_map_pair f a bs]; simp [e]

theorem get?_tupOf {as : List String} (hn : as.Nodup) (μ : String → String) (ρ : String → Value)
    (a : String) : (tupOf as μ ρ).get? a = if a ∈ as then some (ρ (μ a)) else none := by
  rw [tupOf, Tuple.get?_ofPairs (by rw [keys_tupOf]; exact hn)]
  exact lookup_map_pair (fun b => ρ (μ b)) a as

theorem match_tupOf {as : List String} (hn : as.Nodup) (μ : String → String) (ρ : String → Value) :
    Match as μ ρ (tupOf as μ ρ) := fun a ha => by rw [get?_tupOf hn, if_pos ha]

theorem sorted_tupOf {as : List String} (hn : as.Nodup) (μ : String → String) (ρ : String → Value) :
    Tuple.Sorted (tupOf as μ ρ) :=
  Tuple.sorted_ofPairs (by rw [keys_tupOf]; exact hn)

/-- A tuple that fits `as` and matches `ρ` is `tupOf as μ ρ`. -/
theorem eq_tupOf {D : Domain} {as : List String} (hn : as.Nodup) {μ : String → String}
    {ρ : String → Value} {t : Tuple} (f : t.Fits (headerOf D as)) (hm : Match as μ ρ t) :
    t = tupOf as μ ρ := by
  apply Tuple.ext_get? f.sorted (sorted_tupOf hn μ ρ)
  intro a
  rw [get?_tupOf hn]
  split
  · rename_i ha; exact hm a ha
  · rename_i ha; exact f.get?_none (by rw [attrs_headerOf]; exact ha)

/-- Two tuples that fit `as` and match one assignment are equal. -/
theorem match_unique {D : Domain} {as : List String} (hn : as.Nodup) {μ : String → String}
    {ρ : String → Value} {t u : Tuple} (ft : t.Fits (headerOf D as)) (fu : u.Fits (headerOf D as))
    (ht : Match as μ ρ t) (hu : Match as μ ρ u) : t = u :=
  (eq_tupOf hn ft ht).trans (eq_tupOf hn fu hu).symm

theorem fits_tupOf {D : Domain} {as : List String} (hn : as.Nodup) {μ : String → String}
    {ρ : String → Value} (hd : ∀ a ∈ as, D.mem (ρ (μ a)) = true) :
    (tupOf as μ ρ).Fits (headerOf D as) where
  sorted := sorted_tupOf hn μ ρ
  attrs a := by rw [tupOf, attrs_ofPairs, keys_tupOf, attrs_headerOf]
  dom p hp d hd' := by
    rw [tupOf, mem_ofPairs] at hp
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
    rw [lookup_headerOf, if_pos hb] at hd'
    cases hd'; exact hd b hb

/-- In a tuple that fits, a pair's value is the tuple's value for that attribute. -/
theorem get?_of_mem {D : Domain} {as : List String} {t : Tuple} (f : t.Fits (headerOf D as))
    {p : String × Value} (hp : p ∈ t) : t.get? p.1 = some p.2 :=
  lookup_of_mem (Tuple.nodup_keys f.sorted) hp

/-- In a tuple that fits, each attribute of `as` has a value, in `D`. -/
theorem get?_fits {D : Domain} {as : List String} {t : Tuple} (f : t.Fits (headerOf D as))
    {a : String} (ha : a ∈ as) : ∃ v, t.get? a = some v ∧ D.mem v = true ∧ (a, v) ∈ t := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((f.get?_isSome a).mpr (by rw [attrs_headerOf]; exact ha))
  have hp : (a, v) ∈ t := lookup_mem hv
  refine ⟨v, hv, f.dom _ hp D (by rw [lookup_headerOf, if_pos ha]), hp⟩

/-- The value an assignment read off a tuple gives. -/
def readAsg (t : Tuple) : String → Value := fun a => (t.get? a).getD (.bool false)

theorem match_readAsg {D : Domain} {as : List String} {t : Tuple} (f : t.Fits (headerOf D as)) :
    Match as id (readAsg t) t := by
  intro a ha
  obtain ⟨v, hv, -⟩ := get?_fits f ha
  simp [readAsg, hv]

end Coddstheorem
