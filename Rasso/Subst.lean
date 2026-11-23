import Rasso.Unrel
import Rasso.Project

/-!
# Rasso: substitution, and setting one attribute of a tuple

Lemmas shared by the classes of `Rasso.Classes`:
`Term.eval_subst` (substitution is evaluation at the updated tuple), `Tuple.get?_set`,
`Tuple.Fits.set`, and restriction.
-/

namespace Rasso

/-! ## Substitution -/

theorem lookup_filter_ne {a b : String} (hb : b ≠ a) :
    ∀ (t : Tuple), (t.filter fun x => !decide (x.1 = a)).lookup b = t.lookup b
  | [] => rfl
  | (c, w) :: t => by
    have ih := lookup_filter_ne hb t
    by_cases hc : c = a
    · subst hc
      have : (b == c) = false := by simp [hb]
      simp [List.lookup, this, ih]
    · simp only [List.filter_cons, hc, decide_false, Bool.not_false, ite_true, List.lookup]
      split <;> simp_all

theorem Tuple.set_keys_nodup {t : Tuple} (ht : Tuple.Sorted t) (a : String) (v : Value) :
    (((a, v) :: t.filter (·.1 ≠ a)).map (·.1)).Nodup := by
  simp only [List.map_cons, List.nodup_cons]
  refine ⟨?_, ?_⟩
  · simp
  · exact (List.filter_sublist.map _).nodup (Tuple.nodup_keys ht)

theorem Tuple.get?_set {t : Tuple} (ht : Tuple.Sorted t) (a b : String) (v : Value) :
    (t.set a v).get? b = if b = a then some v else t.get? b := by
  rw [Tuple.set, Tuple.get?_ofPairs (Tuple.set_keys_nodup ht a v)]
  by_cases h : b = a
  · subst h; simp [List.lookup]
  · have : (b == a) = false := by simp [h]
    simp [List.lookup, this, h, lookup_filter_ne h, Tuple.get?]

/-- Substitution is evaluation at the updated tuple. -/
theorem Term.eval_subst {t : Tuple} (ht : Tuple.Sorted t) {a : String} {τ : Term} {v : Value}
    (hτ : τ.eval t = .ok v) : ∀ (e : Term), (e.subst a τ).eval t = e.eval (t.set a v)
  | .attr b => by
    by_cases h : b = a
    · subst h; simp [Term.subst, Term.eval, hτ, Tuple.get?_set ht]
    · simp [Term.subst, Term.eval, h, Tuple.get?_set ht]
  | .val w => by simp [Term.subst, Term.eval]
  | .call op args => by
    have : (args.attach.map fun ⟨x, _⟩ => x.subst a τ).mapM (Term.eval t) =
        args.mapM (Term.eval (t.set a v)) := by
      rw [List.mapM_map]
      rw [show args.mapM (Term.eval (t.set a v)) =
        args.attach.mapM (fun x => Term.eval (t.set a v) x.1) from by
          conv => lhs; rw [← List.attach_map_subtype_val args]
          rw [List.mapM_map]; rfl]
      exact mapM_congr_ok _ fun ⟨e, he⟩ _ => Term.eval_subst ht hτ e
    simp only [Term.subst, Term.eval, this]

/-- A substituted term reads what the term reads other than `a`, and what `τ` reads. -/
theorem Term.attrs_subst {a : String} {τ : Term} :
    ∀ (e : Term) {x : String}, x ∈ (e.subst a τ).attrs → (x ∈ e.attrs ∧ x ≠ a) ∨ x ∈ τ.attrs
  | .attr b, x, h => by
    unfold Term.subst at h
    split at h
    · exact .inr h
    · rename_i hb
      simp only [Term.attrs, List.mem_singleton] at h ⊢
      exact .inl ⟨h, h ▸ hb⟩
  | .val _, x, h => by simp [Term.subst, Term.attrs] at h
  | .call op args, x, h => by
    simp only [Term.subst, Term.attrs, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, ⟨⟨e, he⟩, _, rfl⟩, hx⟩ := h
    rcases Term.attrs_subst e hx with ⟨h1, h2⟩ | h1
    · exact .inl ⟨by simp only [Term.attrs, List.mem_flatMap]; exact ⟨e, he, h1⟩, h2⟩
    · exact .inr h1

/-! ## Tuples: setting one attribute, restricting -/

/-- A tuple that fits the heading without `a`, with `a` set to a value of its domain,
fits the heading. -/
theorem Tuple.Fits.set {h : Heading} {a : String} {d : Domain} {v : Value} {t : Tuple}
    (f : t.Fits (h.filter (·.1 ≠ a))) (hd : h.lookup a = some d) (hv : d.mem v = true) :
    (t.set a v).Fits h := by
  have hts : Tuple.Sorted t := f.sorted
  refine Tuple.Fits.ofPairs (Tuple.set_keys_nodup hts a v) (fun x => ?_) (fun p hp e he => ?_)
  · have hfa : ∀ y, y ∈ Heading.attrs (h.filter (·.1 ≠ a)) ↔ y ∈ h.attrs ∧ y ≠ a := by
      intro y; simp [Heading.attrs, List.mem_filter]
    simp only [List.map_cons, List.mem_cons, List.mem_map, List.mem_filter]
    constructor
    · rintro (rfl | ⟨q, ⟨hq, hqa⟩, rfl⟩)
      · exact Finrel.mem_attrs_iff.mpr (by rw [hd]; rfl)
      · exact ((hfa q.1).mp ((f.attrs q.1).mp (List.mem_map_of_mem hq))).1
    · intro hx
      by_cases e : x = a
      · exact .inl e
      · obtain ⟨q, hq, hqx⟩ := List.mem_map.mp ((f.attrs x).mpr ((hfa x).mpr ⟨hx, e⟩))
        exact .inr ⟨q, ⟨hq, by simp [hqx, e]⟩, hqx⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · rw [hd] at he; cases he; exact hv
    · have hpa : p.1 ≠ a := by simpa using (List.mem_filter.mp hp).2
      refine f.dom p (List.mem_filter.mp hp).1 e ?_
      rw [lookup_filter_key (c := fun x => decide (x ≠ a)) (by simpa using hpa)]
      exact he

/-- Restricting to a list depends only on which of the tuple's attributes are in it. -/
theorem Tuple.restrict_congr {t : Tuple} {l₁ l₂ : List String}
    (h : ∀ x ∈ t.attrs, x ∈ l₁ ↔ x ∈ l₂) : t.restrict l₁ = t.restrict l₂ := by
  unfold Tuple.restrict
  apply List.filter_congr
  intro p hp
  have := h p.1 (List.mem_map_of_mem hp)
  simp [this]

/-- A tuple restricted to all its heading's attributes is itself. -/
theorem Tuple.Fits.restrict_self {h : Heading} {t : Tuple} (f : t.Fits h) :
    t.restrict h.attrs = t := by
  unfold Tuple.restrict
  apply List.filter_eq_self.mpr
  intro p hp
  simpa [List.contains_iff_mem] using (f.attrs p.1).mp (List.mem_map_of_mem hp)

end Rasso
