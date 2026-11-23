import Rasso.WF

/-!
# Rasso: a finite relation is what empty and adjoin build

The blueprint defines a finite relation by construction (`def:r2-finrel`): over a heading
`H` with no attribute named twice, a finite relation is what *empty* and *adjoin* build,
where adjoin takes a tuple that fits `H`. In Lean, `Finrel` is a heading and a body, and
`Finrel.WF` (`Rasso.WF`) says the heading names no attribute twice and every tuple fits.
This module proves that the two say the same thing.

* `Body.adjoin_idem`, `Body.adjoin_comm`: adjoining a tuple that is already there changes
  nothing, and the order of adjoining does not matter. `Finrel.adjoin_idem` and
  `Finrel.adjoin_comm` are the same for relations.
* `Finrel.Built h r`: `r` is built from the empty relation over `h` by adjoining tuples
  that fit `h`.
* `Finrel.wf_iff_built`: a finite relation is well formed exactly when its heading names
  no attribute twice and it is so built.
* `Finrel.WF.induction`: a property that holds of the empty relation and is kept by
  adjoin holds of every well-formed finite relation. `Finrel.WF.induction_fresh` is the
  same, and its adjoin step may also assume that the tuple is new.
* `Finrel.empty_wf`, `Finrel.adjoin_wf`: empty and adjoin give well-formed relations.
* `Finrel.gamma_spec`, `Finrel.mem_gamma`, `Finrel.gamma_wf`: what γ gives, its tuples,
  and that γ keeps well-formedness.

Conventions:

* The type `Finrel` admits a body whose tuples don't fit the heading. "By construction"
  is the theorem `wf_iff_built`, not a property of the type.
* `gamma_wf` takes as a hypothesis that the values of γ's expression lie in the domain
  `Agg.domain` gives for it, as `extend_wf` does for `Term.domain`. That `Agg.domain` is
  sound is not proved.
-/

namespace Rasso

/-! ## Bodies: the equations of adjoin -/

namespace Body

@[simp] theorem toList_empty : Body.empty.toList = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun t ht => by
    have := (mem_toList_ofList (x := t) (l := [])).mp ht
    cases this

theorem mem_toList_adjoin {t u : Tuple} {b : Body} :
    t ∈ (b.adjoin u).toList ↔ t = u ∨ t ∈ b.toList := by
  simp only [Body.adjoin, mem_toList_ofList, List.mem_cons]

/-- Adjoining a tuple that is already there changes nothing. -/
theorem adjoin_of_mem {t : Tuple} {b : Body} (h : t ∈ b.toList) : b.adjoin t = b :=
  ext fun x => by
    rw [mem_toList_adjoin]
    exact ⟨fun hx => hx.elim (fun e => e ▸ h) id, Or.inr⟩

/-- Adjoining a tuple twice is adjoining it once. -/
theorem adjoin_idem (t : Tuple) (b : Body) : (b.adjoin t).adjoin t = b.adjoin t :=
  adjoin_of_mem (mem_toList_adjoin.mpr (Or.inl rfl))

/-- The order of adjoining does not matter. -/
theorem adjoin_comm (t u : Tuple) (b : Body) :
    (b.adjoin t).adjoin u = (b.adjoin u).adjoin t :=
  ext fun x => by
    simp only [mem_toList_adjoin]
    constructor <;> rintro (h | h | h) <;> simp [h]

/-- A body written as a list is the empty body with the list's tuples adjoined. -/
theorem ofList_cons (t : Tuple) (l : List Tuple) :
    Body.ofList (t :: l) = (Body.ofList l).adjoin t :=
  ext fun x => by
    rw [mem_toList_adjoin, mem_toList_ofList, mem_toList_ofList, List.mem_cons]

theorem ofList_nil : Body.ofList [] = Body.empty := rfl

end Body

/-! ## Relations: empty and adjoin -/

namespace Finrel

/-- The empty relation over a heading. -/
def empty (h : Heading) : Finrel := ⟨h, Body.empty⟩

/-- `r` with the tuple `t` added. The heading is kept. -/
def adjoin (t : Tuple) (r : Finrel) : Finrel := ⟨r.heading, r.body.adjoin t⟩

@[simp] theorem empty_heading (h : Heading) : (empty h).heading = h := rfl

@[simp] theorem adjoin_heading (t : Tuple) (r : Finrel) : (r.adjoin t).heading = r.heading :=
  rfl

@[simp] theorem tuples_empty (h : Heading) : (empty h).tuples = [] := Body.toList_empty

theorem mem_adjoin {t u : Tuple} {r : Finrel} :
    t ∈ (r.adjoin u).tuples ↔ t = u ∨ t ∈ r.tuples := Body.mem_toList_adjoin

/-- Two finite relations with the same heading and the same tuples are equal. -/
theorem ext {r s : Finrel} (hh : r.heading = s.heading)
    (ht : ∀ t, t ∈ r.tuples ↔ t ∈ s.tuples) : r = s := by
  cases r; cases s
  cases hh
  exact congrArg _ (Body.ext ht)

/-- Adjoining a tuple that is already there changes nothing. -/
theorem adjoin_of_mem {t : Tuple} {r : Finrel} (h : t ∈ r.tuples) : r.adjoin t = r := by
  cases r
  exact congrArg _ (Body.adjoin_of_mem h)

/-- Adjoining a tuple twice is adjoining it once. -/
theorem adjoin_idem (t : Tuple) (r : Finrel) : (r.adjoin t).adjoin t = r.adjoin t :=
  congrArg (Finrel.mk r.heading) (Body.adjoin_idem t r.body)

/-- The order of adjoining does not matter. -/
theorem adjoin_comm (t u : Tuple) (r : Finrel) :
    (r.adjoin t).adjoin u = (r.adjoin u).adjoin t :=
  congrArg (Finrel.mk r.heading) (Body.adjoin_comm t u r.body)

/-- The empty relation is `ofTuples` of no tuples. -/
theorem ofTuples_nil (h : Heading) : ofTuples h [] = empty h := rfl

/-- A relation written as a list is the rest of the list with the first tuple adjoined. -/
theorem ofTuples_cons (h : Heading) (t : Tuple) (l : List Tuple) :
    ofTuples h (t :: l) = (ofTuples h l).adjoin t :=
  congrArg (Finrel.mk h) (Body.ofList_cons t l)

/-- A finite relation is `ofTuples` of its heading and its own tuples. -/
theorem ofTuples_tuples (r : Finrel) : ofTuples r.heading r.tuples = r := by
  cases r
  exact congrArg _ (Body.ofList_toList _)

/-! ## Built from empty by adjoin -/

/-- `r` is built over the heading `h`: it is the empty relation over `h`, or a built
relation with a tuple that fits `h` adjoined. This is the blueprint's definition of a
finite relation, for a heading that names no attribute twice. -/
inductive Built (h : Heading) : Finrel → Prop
  | empty : Built h (Finrel.empty h)
  | adjoin {r : Finrel} {t : Tuple} : Built h r → t.Fits h → Built h (r.adjoin t)

theorem Built.heading {h : Heading} {r : Finrel} (b : Built h r) : r.heading = h := by
  induction b with
  | empty => rfl
  | adjoin _ _ ih => exact ih

/-- Every tuple of a built relation fits the heading. -/
theorem Built.fits {h : Heading} {r : Finrel} (b : Built h r) : ∀ t ∈ r.tuples, t.Fits h := by
  induction b with
  | empty => intro t ht; simp at ht
  | adjoin _ f ih =>
    intro t ht
    cases mem_adjoin.mp ht with
    | inl e => exact e ▸ f
    | inr e => exact ih t e

/-- A list of tuples that fit gives a built relation. -/
theorem built_ofTuples {h : Heading} :
    ∀ {l : List Tuple}, (∀ t ∈ l, t.Fits h) → Built h (ofTuples h l)
  | [], _ => Built.empty
  | t :: l, hf => by
    rw [ofTuples_cons]
    exact Built.adjoin (built_ofTuples fun u hu => hf u (List.mem_cons_of_mem _ hu))
      (hf t List.mem_cons_self)

/-- A finite relation whose tuples all fit its heading is built over it. -/
theorem built_of_fits {r : Finrel} (hf : ∀ t ∈ r.tuples, t.Fits r.heading) :
    Built r.heading r := by
  have := built_ofTuples hf
  rwa [ofTuples_tuples] at this

/-- **By construction.** A finite relation is well formed exactly when its heading names
no attribute twice and the relation is built from empty by adjoining tuples that fit. -/
theorem wf_iff_built {r : Finrel} : r.WF ↔ r.heading.attrs.Nodup ∧ Built r.heading r :=
  ⟨fun hr => ⟨hr.nodup, built_of_fits hr.fits⟩, fun ⟨hn, b⟩ => ⟨hn, b.fits⟩⟩

/-- The same, with the heading named: `r` is well formed with heading `h` exactly when
`h` names no attribute twice and `r` is built over `h`. -/
theorem wf_and_heading_iff_built {h : Heading} {r : Finrel} :
    (r.WF ∧ r.heading = h) ↔ h.attrs.Nodup ∧ Built h r := by
  constructor
  · rintro ⟨hr, rfl⟩; exact wf_iff_built.mp hr
  · rintro ⟨hn, b⟩
    have hh := b.heading
    subst hh
    exact ⟨wf_iff_built.mpr ⟨hn, b⟩, rfl⟩

/-! ## Empty and adjoin give well-formed relations -/

theorem empty_wf {h : Heading} (hn : h.attrs.Nodup) : (empty h).WF :=
  ⟨hn, fun t ht => by simp at ht⟩

theorem adjoin_wf {r : Finrel} {t : Tuple} (hr : r.WF) (ht : t.Fits r.heading) :
    (r.adjoin t).WF :=
  ⟨hr.nodup, fun u hu => (mem_adjoin.mp hu).elim (fun e => e ▸ ht) (hr.fits u)⟩

/-- Adjoin gives a well-formed relation only for a tuple that fits. -/
theorem adjoin_wf_iff {r : Finrel} {t : Tuple} (hr : r.WF) :
    (r.adjoin t).WF ↔ t.Fits r.heading :=
  ⟨fun h => h.fits t (mem_adjoin.mpr (Or.inl rfl)), adjoin_wf hr⟩

/-! ## Induction on empty and adjoin -/

/-- Induction over a list of tuples that fit, none twice. -/
private theorem induction_list {h : Heading} {motive : Finrel → Prop}
    (empty : motive (Finrel.empty h))
    (adjoin : ∀ (s : Finrel) (t : Tuple), s.WF → s.heading = h → t.Fits h → t ∉ s.tuples →
      motive s → motive (s.adjoin t))
    (hn : h.attrs.Nodup) :
    ∀ {l : List Tuple}, l.Nodup → (∀ t ∈ l, t.Fits h) → motive (ofTuples h l)
  | [], _, _ => empty
  | t :: l, hl, hf => by
    rw [ofTuples_cons]
    have hl' := List.nodup_cons.mp hl
    have hf' : ∀ u ∈ l, u.Fits h := fun u hu => hf u (List.mem_cons_of_mem _ hu)
    exact adjoin _ t (wf_ofTuples hn hf') rfl (hf t List.mem_cons_self)
      (fun hm => hl'.1 (mem_ofTuples.mp hm)) (induction_list empty adjoin hn hl'.2 hf')

theorem nodup_tuples (r : Finrel) : r.tuples.Nodup := by
  cases r with
  | mk h b =>
    induction b using Quotient.ind with
    | _ l =>
      exact (List.mergeSort_perm (dedup l) Tuple.le).nodup_iff.mpr (nodup_dedup l)

/-- **Induction on empty and adjoin, with a new tuple.** A property that holds of the
empty relation over `r`'s heading, and is kept when a tuple that fits and is not yet in
the relation is adjoined, holds of the well-formed relation `r`. -/
theorem WF.induction_fresh {motive : Finrel → Prop} {r : Finrel} (hr : r.WF)
    (empty : motive (Finrel.empty r.heading))
    (adjoin : ∀ (s : Finrel) (t : Tuple), s.WF → s.heading = r.heading → t.Fits r.heading →
      t ∉ s.tuples → motive s → motive (s.adjoin t)) : motive r := by
  have := induction_list empty adjoin hr.nodup (nodup_tuples r) hr.fits
  rwa [ofTuples_tuples] at this

/-- **Induction on empty and adjoin.** A property that holds of the empty relation over
`r`'s heading, and is kept when a tuple that fits is adjoined, holds of the well-formed
relation `r`. -/
theorem WF.induction {motive : Finrel → Prop} {r : Finrel} (hr : r.WF)
    (empty : motive (Finrel.empty r.heading))
    (adjoin : ∀ (s : Finrel) (t : Tuple), s.WF → s.heading = r.heading → t.Fits r.heading →
      motive s → motive (s.adjoin t)) : motive r :=
  hr.induction_fresh empty fun s t hs hh ht _ => adjoin s t hs hh ht

/-! ## γ keeps well-formedness -/

/-- What γ gives, when it is not refused. -/
theorem gamma_spec {by_ : List String} {ex : Agg} {res : String} {r s : Finrel}
    (h : r.gamma by_ ex res = .ok s) :
    by_.Nodup ∧ res ∉ by_ ∧ ∃ d hd ts, ex.domain r.heading = some d ∧
      Forall2 (fun a p => r.domainOf? a = some p.2 ∧ p.1 = a) by_ hd ∧
      Forall2 (fun k t => ∃ v, ex.eval k (r.tuples.filter fun t => t.restrict by_ == k) = .ok v ∧
        t = Tuple.ofPairs ((res, v) :: k)) (gammaKeys by_ r) ts ∧
      s = ofTuples (hd ++ [(res, d)]) ts := by
  simp only [gamma, bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hn
      split at h
      · cases h
      · rename_i hc
        split at h
        · cases h
        · split at h
          · rename_i d hdm
            split at h
            · cases h
            · rename_i hd he
              split at h
              · cases h
              · rename_i ts hts
                simp only [pure, Except.pure, Except.ok.injEq] at h
                refine ⟨(length_eraseDups_eq by_).mp (by simpa using hn),
                  fun hm => hc (List.contains_iff_mem.mpr hm), d, hd, ts, hdm, ?_, ?_, h.symm⟩
                · exact (mapM_ok.mp he).imp fun a p hp => by
                    cases hx : r.domainOf? a with
                    | none => simp only [hx] at hp; cases hp
                    | some e => simp only [hx] at hp; cases hp; exact ⟨rfl, rfl⟩
                · exact (mapM_ok.mp hts).imp fun k t hp => by
                    split at hp
                    · cases hp
                    · rename_i v hv
                      simp only [pure, Except.pure, Except.ok.injEq] at hp
                      exact ⟨v, hv, hp.symm⟩
          · cases h

/-- The tuples of γ's result: one for each key, the key with the expression's value on
the key's group. -/
theorem mem_gamma {by_ : List String} {ex : Agg} {res : String} {r s : Finrel}
    (h : r.gamma by_ ex res = .ok s) (t : Tuple) :
    t ∈ s.tuples ↔ ∃ k ∈ gammaKeys by_ r, ∃ v,
      ex.eval k (r.tuples.filter fun t => t.restrict by_ == k) = .ok v ∧
        t = Tuple.ofPairs ((res, v) :: k) := by
  obtain ⟨_, _, d, hd, ts, _, _, hts, rfl⟩ := gamma_spec h
  rw [mem_ofTuples]
  constructor
  · intro ht; obtain ⟨k, hk, hr⟩ := hts.mem_right ht; exact ⟨k, hk, hr⟩
  · rintro ⟨k, hk, v, hv, rfl⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := hts.mem_left hk
    rw [hv] at hw; cases hw; exact hy

/-- γ keeps well-formedness, given that the values of its expression lie in the domain
`Agg.domain` gives it (an assumption: the soundness of `Agg.domain` is not proved). -/
theorem gamma_wf {by_ : List String} {ex : Agg} {res : String} {r s : Finrel}
    (h : r.gamma by_ ex res = .ok s) (hr : r.WF)
    (hdom : ∀ d, ex.domain r.heading = some d → ∀ k ∈ gammaKeys by_ r, ∀ v,
      ex.eval k (r.tuples.filter fun t => t.restrict by_ == k) = .ok v → d.mem v = true) :
    s.WF := by
  obtain ⟨hn, hres, d, (hd : Heading), ts, hdm, hhd, hts, rfl⟩ := gamma_spec h
  have hattrs : Heading.attrs hd = by_ := by
    have : ∀ {l : List String} {m : Heading},
        Forall2 (fun a (p : String × Domain) => r.domainOf? a = some p.2 ∧ p.1 = a) l m →
        m.map (·.1) = l := by
      intro l m hf
      induction hf with
      | nil => rfl
      | cons h1 _ ih => simp only [List.map_cons, ih, h1.2]
    exact this hhd
  have hlook : ∀ a e, hd.lookup a = some e → r.heading.lookup a = some e := by
    intro a e hl
    obtain ⟨b, _, hb, hab⟩ := hhd.mem_right (lookup_mem hl)
    subst hab; exact hb
  have hin : ∀ a ∈ by_, a ∈ r.heading.attrs := by
    intro a ha
    obtain ⟨p, _, hp, _⟩ := hhd.mem_left ha
    exact mem_attrs_iff.mpr (by show (r.domainOf? a).isSome = true; rw [hp]; rfl)
  -- each key fits the heading of the grouping attributes
  have hkey : ∀ k ∈ gammaKeys by_ r, k.Fits hd := by
    intro k hk
    unfold gammaKeys at hk
    split at hk
    · rename_i he
      have hb : by_ = [] := List.isEmpty_iff.mp he
      have hk' : k = [] := by simpa using hk
      subst hk'
      refine ⟨List.Pairwise.nil, fun a => ?_, fun p hp => by cases hp⟩
      rw [hattrs, hb]; simp [Tuple.attrs]
    · rw [List.mem_eraseDups, List.mem_map] at hk
      obtain ⟨u, hu, rfl⟩ := hk
      have fu := hr.fits u hu
      refine ⟨fu.sorted.filter _, fun a => ?_,
        fun p hp e he => fu.dom p (List.mem_filter.mp hp).1 e (hlook _ _ he)⟩
      rw [hattrs]
      simp only [Tuple.attrs, Tuple.restrict, List.mem_map, List.mem_filter,
        List.contains_iff_mem]
      constructor
      · rintro ⟨p, ⟨_, hp⟩, rfl⟩; exact hp
      · intro ha
        obtain ⟨p, hp, e⟩ := List.mem_map.mp ((fu.attrs a).mpr (hin a ha))
        exact ⟨p, ⟨hp, e ▸ ha⟩, e⟩
  have hall : Heading.attrs (hd ++ [(res, d)]) = by_ ++ [res] := by
    rw [← hattrs]; simp [Heading.attrs]
  refine wf_ofTuples ?_ fun t ht => ?_
  · rw [hall, List.nodup_append]
    exact ⟨hn, by simp, fun a ha b hb e => by simp at hb; subst hb; subst e; exact hres ha⟩
  · obtain ⟨k, hk, v, hv, rfl⟩ := hts.mem_right ht
    have fk := hkey k hk
    have hresk : res ∉ k.attrs := fun hm => hres (hattrs ▸ (fk.attrs res).mp hm)
    have hkeys : (((res, v) :: k).map (·.1)).Nodup := by
      rw [List.map_cons, List.nodup_cons]
      exact ⟨hresk, fk.nodup⟩
    refine ⟨ofPairs_sorted hkeys, fun a => ?_, fun p hp d' hd' => ?_⟩
    · rw [attrs_ofPairs, hall, List.map_cons, List.mem_cons, List.mem_append]
      have := fk.attrs a
      rw [hattrs] at this
      simp only [Tuple.attrs] at this
      rw [this]
      simp only [List.mem_singleton]
      exact Or.comm
    · rw [mem_ofPairs, List.mem_cons] at hp
      rw [List.lookup_append] at hd'
      cases hp with
      | inl e =>
        subst e
        have : hd.lookup res = none := by
          cases hl : hd.lookup res with
          | none => rfl
          | some _ =>
            exact absurd (List.mem_map_of_mem (f := (·.1)) (lookup_mem hl))
              (fun hm => hres (by rw [← hattrs]; exact hm))
        rw [this] at hd'
        simp [List.lookup] at hd'
        subst hd'
        exact hdom d hdm k hk v hv
      | inr hp =>
        have ha : p.1 ∈ Heading.attrs hd := (fk.attrs p.1).mp (List.mem_map_of_mem (f := (·.1)) hp)
        obtain ⟨d₀, hd₀⟩ := Option.isSome_iff_exists.mp (lookup_isSome_iff_mem ha)
        rw [hd₀] at hd'
        change some d₀ = some d' at hd'
        exact (Option.some.inj hd') ▸ fk.dom p hp d₀ hd₀

/-! ## Examples -/

/-- The type admits a body whose tuple does not fit its heading. Such a value is not well
formed, so it is not a finite relation of the blueprint's definition. -/
example : ¬ (ofTuples [("a", .kind .int)] [[("b", .int 1)]]).WF := fun h => by
  have f := h.fits [("b", .int 1)] (mem_ofTuples.mpr List.mem_cons_self)
  have := (f.attrs "b").mp (by simp [Tuple.attrs])
  simp [Heading.attrs, ofTuples] at this

/-- The same relation, adjoined in two orders and with a repeat. -/
example (h : Heading) (t u : Tuple) :
    (((empty h).adjoin t).adjoin u).adjoin t = ((empty h).adjoin u).adjoin t := by
  rw [adjoin_comm t u, adjoin_idem]

private def gammaExample : Finrel :=
  ofTuples [("a", .kind .int), ("b", .kind .int)]
    [Tuple.ofPairs [("a", .int 1), ("b", .int 5)], Tuple.ofPairs [("a", .int 1), ("b", .int 7)]]

-- γ groups by `a`: one group, of two tuples.
#guard match gammaExample.gamma ["a"] (.agg "count" (.attr "b")) "n" with
  | .ok s => s.tuples == [Tuple.ofPairs [("a", .int 1), ("n", .int 2)]]
  | .error _ => false

-- γ refuses a grouping attribute named twice.
#guard match gammaExample.gamma ["a", "a"] (.agg "count" (.attr "b")) "n" with
  | .ok _ => false
  | .error e => e == "γ: [a, a] names a grouping attribute twice"

end Finrel

end Rasso
