import Rasso.Mem

/-!
# Rasso: well-formed finite relations

A finite relation is **well formed** when its heading names no attribute twice and each
of its tuples *fits* the heading: the tuple has exactly the heading's attributes, sorted
by name with none twice, and each value lies in its attribute's domain. Each operator of
the finite algebra keeps this: from well-formed operands it builds a well-formed result
(when it is not refused).

Nothing in `Finrel` forces well-formedness: a `Finrel` is any heading with any body. It is
a property the evaluator keeps, and these lemmas are the proof that it does, operator by
operator.

Conventions:

* π refuses a list that names an attribute twice, so
  its result never has a repeated attribute.
* extend keeps well-formedness only when the term's values lie in the domain
  `Term.domain` gives for it. That is a property of `Term.domain` (soundness of the term
  typing), not proved here; it is a hypothesis of `extend_wf`.
* γ, empty and adjoin are covered in `Rasso.Built`. The evaluator's ω (rows checked one
  by one) is not covered yet.
-/

namespace Rasso

/-! ## Lists of pairs -/

theorem nodup_map_of_inj {α β : Type} {g : α → β} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, g x = g y → x = y) → (l.map g).Nodup
  | [], _, _ => List.nodup_nil
  | x :: l, hn, hi => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_inj hn.2 fun a ha b hb => hi a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
    obtain ⟨y, hy, e⟩ := List.mem_map.mp hm
    exact hn.1 (hi y (List.mem_cons_of_mem _ hy) x List.mem_cons_self e ▸ hy)

theorem inj_of_nodup_map {α β : Type} {g : α → β} :
    ∀ {l : List α}, (l.map g).Nodup → ∀ x ∈ l, ∀ y ∈ l, g x = g y → x = y
  | [], _, _, h, _, _, _ => by cases h
  | z :: l, hn, x, hx, y, hy, e => by
    rw [List.map_cons, List.nodup_cons] at hn
    cases List.mem_cons.mp hx with
    | inl ex =>
      cases List.mem_cons.mp hy with
      | inl ey => rw [ex, ey]
      | inr ey => subst ex; exact absurd (e ▸ List.mem_map_of_mem ey) hn.1
    | inr ex =>
      cases List.mem_cons.mp hy with
      | inl ey => subst ey; exact absurd (e.symm ▸ List.mem_map_of_mem ex) hn.1
      | inr ey => exact inj_of_nodup_map hn.2 x ex y ey e

theorem lookup_isSome_iff_mem {β : Type} {a : String} {l : List (String × β)}
    (h : a ∈ l.map (·.1)) : (l.lookup a).isSome = true := Finrel.lookup_isSome.mpr h

theorem lookup_mem {β : Type} {a : String} {d : β} :
    ∀ {l : List (String × β)}, l.lookup a = some d → (a, d) ∈ l
  | [], h => by cases h
  | (b, e) :: l, h => by
    simp only [List.lookup] at h
    by_cases hab : a = b
    · subst hab; simp only [beq_self_eq_true] at h; cases h; exact List.mem_cons_self
    · have : (a == b) = false := by simp [hab]
      rw [this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem mem_lookup {β : Type} {a : String} {d : β} :
    ∀ {l : List (String × β)}, (l.map (·.1)).Nodup → (a, d) ∈ l → l.lookup a = some d
  | [], _, h => by cases h
  | (b, e) :: l, hn, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.lookup]
    cases List.mem_cons.mp h with
    | inl e' => cases e'; simp
    | inr e' =>
      have hab : a ≠ b := fun hab => hn.1 (hab ▸ List.mem_map_of_mem (f := (·.1)) e')
      have : (a == b) = false := by simp [hab]
      rw [this]
      exact mem_lookup hn.2 e'

/-! ## Domains -/

theorem Domain.values?_sound {a : Domain} {va : List Value} (h : a.values? = some va)
    {x : Value} (hx : a.mem x = true) : x ∈ va := by
  match a, x with
  | .kind .bool, .bool b =>
    simp only [Domain.values?, Option.some.injEq] at h; subst h; cases b <;> simp
  | .kind .bool, .int _ | .kind .bool, .symbol _ | .kind .bool, .string _ | .kind .bool, .float _
  | .kind .bool, .rat _ _ =>
    simp [Domain.mem, Kind.has] at hx
  | .kind .int, _ | .kind .symbol, _ | .kind .string, _ | .kind .float, _ | .kind .rat, _ =>
    simp [Domain.values?] at h
  | .range lo hi, .int n =>
    simp only [Domain.values?, Option.some.injEq] at h; subst h
    simp only [Domain.mem, Bool.and_eq_true, decide_eq_true_eq] at hx
    simp only [List.mem_map, List.mem_range, Value.int.injEq]
    refine ⟨(n - lo).toNat, by omega, ?_⟩
    rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg (by omega)]; omega
  | .range _ _, .bool _ | .range _ _, .symbol _ | .range _ _, .string _ | .range _ _, .float _
  | .range _ _, .rat _ _ =>
    simp [Domain.mem] at hx
  | .set vs, x =>
    simp only [Domain.values?, Option.some.injEq] at h; subst h
    simp only [Domain.mem, List.contains_iff_mem] at hx
    exact List.mem_mergeSort.mpr hx

theorem Domain.mem_ofValues {vs : List Value} {x : Value} :
    (Domain.ofValues vs).mem x = true ↔ x ∈ vs := by
  simp [Domain.ofValues, Domain.mem, List.mem_mergeSort]

/-- The intersection of two domains holds every value both hold. -/
theorem Domain.inter_sound {a b f : Domain} (h : a.inter b = .ok f) {x : Value}
    (ha : a.mem x = true) (hb : b.mem x = true) : f.mem x = true := by
  unfold Domain.inter at h
  split at h
  · cases h; exact ha
  · split at h
    · rename_i l₁ h₁ l₂ h₂ _
      cases h
      match x with
      | .int n =>
        simp only [Domain.mem, Bool.and_eq_true, decide_eq_true_eq] at ha hb
        have : max l₁ l₂ ≤ min h₁ h₂ := by omega
        simp only [this, ite_true, Domain.mem, Bool.and_eq_true, decide_eq_true_eq]; omega
      | .bool _ | .symbol _ | .string _ | .float _ | .rat _ _ => simp [Domain.mem] at ha
    · cases h; exact hb
    · cases h; exact ha
    · cases h; exact hb
    · cases h; exact ha
    · cases h; exact hb
    · cases h; exact ha
    · split at h
      · rename_i va _ hva
        cases h
        exact Domain.mem_ofValues.mpr (List.mem_filter.mpr ⟨Domain.values?_sound hva ha, hb⟩)
      · rename_i vb hvb _
        cases h
        exact Domain.mem_ofValues.mpr (List.mem_filter.mpr ⟨Domain.values?_sound hvb hb, ha⟩)
      · cases h

/-! ## Tuples that fit a heading -/

/-- The attribute names of a tuple, in its order. -/
def Tuple.attrs (t : Tuple) : List String := t.map (·.1)

/-- A tuple fits a heading: sorted by attribute name with none twice, exactly the
heading's attributes, each value in its attribute's domain. -/
structure Tuple.Fits (h : Heading) (t : Tuple) : Prop where
  sorted : t.Pairwise fun p q => p.1 < q.1
  attrs : ∀ a, a ∈ t.attrs ↔ a ∈ h.attrs
  dom : ∀ p ∈ t, ∀ d, h.lookup p.1 = some d → d.mem p.2 = true

/-- A finite relation is well formed: no attribute twice in its heading, and every tuple
fits the heading. -/
structure Finrel.WF (r : Finrel) : Prop where
  nodup : r.heading.attrs.Nodup
  fits : ∀ t ∈ r.tuples, t.Fits r.heading

theorem Tuple.Fits.nodup {h : Heading} {t : Tuple} (f : t.Fits h) : t.attrs.Nodup :=
  List.nodup_iff_pairwise_ne.mpr (List.pairwise_map.mpr
    (f.sorted.imp fun {a b} (hlt : a.1 < b.1) (e : a.1 = b.1) => String.lt_irrefl b.1 (e ▸ hlt)))

/-- Sorting pairs whose names are all different gives a list sorted strictly. -/
theorem ofPairs_sorted {ps : List (String × Value)} (hn : (ps.map (·.1)).Nodup) :
    (Tuple.ofPairs ps).Pairwise fun p q => p.1 < q.1 := by
  have hs := List.pairwise_mergeSort (le := fun (p q : String × Value) => decide (p.1 ≤ q.1))
    (fun _ _ _ h₁ h₂ => by simp only [decide_eq_true_eq] at *; exact String.le_trans h₁ h₂)
    (fun a b => by simpa using String.le_total a.1 b.1) ps
  have hn' : ((Tuple.ofPairs ps).map (·.1)).Nodup :=
    ((List.mergeSort_perm ps _).map _).nodup_iff.mpr hn
  have hne := List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp hn')
  refine (hs.and hne).imp fun ⟨h1, h2⟩ => ?_
  simp only [decide_eq_true_eq] at h1
  exact String.not_le.mp fun h3 => h2 (String.le_antisymm h1 h3)

@[simp] theorem mem_ofPairs {p : String × Value} {ps : List (String × Value)} :
    p ∈ Tuple.ofPairs ps ↔ p ∈ ps := List.mem_mergeSort

theorem attrs_ofPairs {ps : List (String × Value)} {a : String} :
    a ∈ (Tuple.ofPairs ps).attrs ↔ a ∈ ps.map (·.1) := by
  simp only [Tuple.attrs, List.mem_map, mem_ofPairs]

/-- Fitting depends on the heading only through its attributes and their domains. -/
theorem Tuple.Fits.transfer {h k : Heading} {t : Tuple} (f : t.Fits h)
    (ha : ∀ a, a ∈ h.attrs ↔ a ∈ k.attrs)
    (hd : ∀ a d, k.lookup a = some d → h.lookup a = some d) : t.Fits k :=
  ⟨f.sorted, fun a => (f.attrs a).trans (ha a), fun p hp d hk => f.dom p hp d (hd _ _ hk)⟩

/-! ## Each operator keeps well-formedness -/

namespace Finrel

theorem wf_ofTuples {h : Heading} {ts : List Tuple} (hn : h.attrs.Nodup)
    (hf : ∀ t ∈ ts, t.Fits h) : (ofTuples h ts).WF :=
  ⟨hn, fun t ht => hf t (mem_ofTuples.mp ht)⟩

theorem select_wf {p : Tuple → Except String Bool} {r s : Finrel}
    (h : r.select p = .ok s) (hr : r.WF) : s.WF := by
  have hh := select_heading h
  refine ⟨hh ▸ hr.nodup, fun t ht => hh ▸ hr.fits t ((mem_select h t).mp ht).1⟩

/-- Under `SameHeading r s`, a tuple that fits `s` fits `r`. -/
theorem SameHeading.fits {r s : Finrel} (hs : SameHeading r s) {t : Tuple}
    (f : t.Fits s.heading) : t.Fits r.heading := by
  refine f.transfer (fun a => ?_) (fun a d hk => ?_)
  · have := congrArg (a ∈ ·) hs.1
    simp only [List.mem_mergeSort] at this
    exact (propext_iff.mp this).symm
  · have := hs.2 _ (lookup_mem hk); exact this

theorem union_wf {r s q : Finrel} (h : r.union s = .ok q) (hr : r.WF) (hs : s.WF) : q.WF := by
  have hsh := union_ok.mp ⟨q, h⟩
  simp only [union, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine wf_ofTuples hr.nodup fun t ht => ?_
    cases List.mem_append.mp ht with
    | inl e => exact hr.fits t e
    | inr e => exact hsh.fits (hs.fits t e)

theorem diff_wf {r s q : Finrel} (h : r.diff s = .ok q) (hr : r.WF) : q.WF := by
  simp only [diff, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact wf_ofTuples hr.nodup fun t ht => hr.fits t (List.mem_filter.mp ht).1

theorem inter_wf {r s q : Finrel} (h : r.inter s = .ok q) (hr : r.WF) : q.WF := by
  simp only [Finrel.inter, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact wf_ofTuples hr.nodup fun t ht => hr.fits t (List.mem_filter.mp ht).1

theorem project_spec {as : List String} {r s : Finrel} (h : r.project as = .ok s) :
    (∀ a d, s.heading.lookup a = some d → r.heading.lookup a = some d) ∧
      s = ofTuples s.heading (r.tuples.map (·.restrict as)) := by
  replace h := (project_core h).2
  simp only [projectCore, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i hd he
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨fun a d hl => ?_, rfl⟩
    obtain ⟨b, _, hb⟩ := (mapM_ok.mp he).mem_right (lookup_mem hl)
    cases hb' : r.domainOf? b with
    | none => simp only [hb'] at hb; cases hb
    | some e => simp only [hb', Except.ok.injEq, Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb; exact hb'

theorem project_wf {as : List String} {r s : Finrel} (h : r.project as = .ok s) (hr : r.WF) :
    s.WF := by
  have hattrs := project_heading h
  obtain ⟨hin, hn⟩ := project_ok.mp ⟨s, h⟩
  obtain ⟨hlook, hs⟩ := project_spec h
  refine ⟨hattrs ▸ hn, fun t ht => ?_⟩
  rw [hs, mem_ofTuples, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  have fu := hr.fits u hu
  refine ⟨fu.sorted.filter _, fun a => ?_, fun p hp d hd => fu.dom p (List.mem_filter.mp hp).1 d (hlook _ _ hd)⟩
  rw [hattrs]
  simp only [Tuple.attrs, Tuple.restrict, List.mem_map, List.mem_filter, List.contains_iff_mem]
  constructor
  · rintro ⟨p, ⟨_, hp⟩, rfl⟩; exact hp
  · intro ha
    obtain ⟨p, hp, e⟩ := List.mem_map.mp ((fu.attrs a).mpr (hin a ha))
    exact ⟨p, ⟨hp, e ▸ ha⟩, e⟩

theorem rename_wf {ren : List (String × String)} {r s : Finrel} (h : r.rename ren = .ok s)
    (hr : r.WF) : s.WF := by
  obtain ⟨_, hn, rfl⟩ := rename_eq_ok.mp h
  have hmap : (renameHeading ren r.heading).attrs = r.heading.attrs.map (renameAttr ren) := by
    simp [renameHeading, Heading.attrs]
  have hinj := inj_of_nodup_map (hmap ▸ hn)
  refine wf_ofTuples hn fun t ht => ?_
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have fu := hr.fits u hu
  have hsub : ∀ b ∈ u.attrs, b ∈ r.heading.attrs := fun b hb => (fu.attrs b).mp hb
  have hkeys : ((u.map fun (p : String × Value) => (renameAttr ren p.1, p.2)).map (·.1)) =
      u.attrs.map (renameAttr ren) := by simp [Tuple.attrs]
  refine ⟨ofPairs_sorted (hkeys ▸ nodup_map_of_inj fu.nodup fun x hx y hy e =>
      hinj x (hsub x hx) y (hsub y hy) e), fun a => ?_, fun p hp d hd => ?_⟩
  · rw [renameTuple, attrs_ofPairs, hkeys, hmap, List.mem_map, List.mem_map]
    constructor
    · rintro ⟨b, hb, e⟩; exact ⟨b, hsub b hb, e⟩
    · rintro ⟨b, hb, e⟩; exact ⟨b, (fu.attrs b).mpr hb, e⟩
  · rw [renameTuple, mem_ofPairs, List.mem_map] at hp
    obtain ⟨⟨b, v⟩, hbv, rfl⟩ := hp
    obtain ⟨⟨c, d'⟩, hc, e⟩ := List.mem_map.mp (lookup_mem hd)
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1, rfl⟩ := e
    have hb : b ∈ u.attrs := List.mem_map_of_mem (f := (·.1)) hbv
    have := hinj c (List.mem_map_of_mem (f := (·.1)) hc) b (hsub b hb) e1
    subst this
    exact fu.dom _ hbv _ (mem_lookup hr.nodup hc)

/-- What a join's heading is, when it is defined. -/
theorem joinHeading_spec {h k j : Heading} (hj : joinHeading h k = .ok j) (hh : h.attrs.Nodup)
    (hk : k.attrs.Nodup) :
    j.attrs.Nodup ∧ (∀ a, a ∈ j.attrs ↔ a ∈ h.attrs ∨ a ∈ k.attrs) ∧
      ∀ a f, j.lookup a = some f →
        (∃ d, (a, d) ∈ h ∧ ((k.lookup a = none ∧ f = d) ∨
          ∃ e, k.lookup a = some e ∧ d.inter e = .ok f)) ∨
        (a ∉ h.attrs ∧ k.lookup a = some f) := by
  simp only [joinHeading, bind, Except.bind] at hj
  split at hj
  · cases hj
  · rename_i left he
    simp only [pure, Except.pure, Except.ok.injEq] at hj
    subst hj
    have hf := mapM_ok.mp he
    -- each entry of `left` keeps its attribute
    have hfst : ∀ {l : Heading} {ys : Heading}, Forall2 (fun x y => (match k.lookup x.1 with
        | some e => do return (x.1, ← x.2.inter e)
        | none => .ok (x.1, x.2) : Except String (String × Domain)) = .ok y) l ys →
        ys.map (·.1) = l.map (·.1) := by
      intro l ys hl
      induction hl with
      | nil => rfl
      | @cons x y _ _ h1 _ ih =>
        simp only [List.map_cons, ih, List.cons.injEq, and_true]
        split at h1
        · simp only [bind, Except.bind, pure, Except.pure] at h1
          split at h1
          · cases h1
          · cases h1; rfl
        · cases h1; rfl
    have hla : left.map (·.1) = h.attrs := hfst hf
    have hnot : ∀ b, b ∈ (k.filter fun p => (h.lookup p.1).isNone).map (·.1) → b ∉ h.attrs := by
      intro b hb hbh
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
      have h1 := (List.mem_filter.mp hp).2
      have h2 := lookup_isSome_iff_mem hbh
      cases hl : h.lookup p.1 with
      | none => rw [hl] at h2; cases h2
      | some _ => rw [hl] at h1; cases h1
    have hsub : ((k.filter fun p => (h.lookup p.1).isNone).map (·.1)).Sublist k.attrs :=
      (List.filter_sublist).map _
    refine ⟨?_, fun a => ?_, fun a f hl => ?_⟩
    · show (left ++ _).map (·.1) |>.Nodup
      rw [List.map_append, hla, List.nodup_append]
      exact ⟨hh, hk.sublist hsub, fun a ha b hb e => hnot b hb (e ▸ ha)⟩
    · show a ∈ (left ++ _).map (·.1) ↔ _
      rw [List.map_append, hla, List.mem_append]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (hsub.subset h1)
      · rintro (h1 | h1)
        · exact Or.inl h1
        · by_cases h2 : a ∈ h.attrs
          · exact Or.inl h2
          · refine Or.inr ?_
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h1
            refine List.mem_map_of_mem (List.mem_filter.mpr ⟨hp, ?_⟩)
            cases hl : h.lookup p.1 with
            | none => rfl
            | some _ => exact absurd (lookup_mem hl) fun hm => h2 (List.mem_map_of_mem (f := (·.1)) hm)
    · rw [List.lookup_append] at hl
      cases hll : left.lookup a with
      | some f' =>
        rw [hll] at hl
        change some f' = some f at hl; cases hl
        obtain ⟨⟨b, d⟩, hbd, hg⟩ := hf.mem_right (lookup_mem hll)
        refine Or.inl ⟨d, ?_⟩
        simp only at hg
        split at hg
        · rename_i e he
          simp only [pure, Except.pure] at hg
          split at hg
          · cases hg
          · rename_i f₀ hf₀
            simp only [Except.ok.injEq, Prod.mk.injEq] at hg
            obtain ⟨rfl, rfl⟩ := hg
            exact ⟨hbd, Or.inr ⟨e, he, hf₀⟩⟩
        · rename_i he
          simp only [Except.ok.injEq, Prod.mk.injEq] at hg
          obtain ⟨rfl, rfl⟩ := hg
          exact ⟨hbd, Or.inl ⟨he, rfl⟩⟩
      | none =>
        rw [hll] at hl
        change List.lookup a _ = some f at hl
        have hm := List.mem_filter.mp (lookup_mem hl)
        refine Or.inr ⟨hnot a (List.mem_map_of_mem (f := (·.1)) (lookup_mem hl)),
          mem_lookup hk hm.1⟩

theorem agrees_eq {u v : Tuple} (ha : u.agrees v = true) {a : String} {x y : Value}
    (hx : (a, x) ∈ u) (hy : v.lookup a = some y) : x = y := by
  have := List.all_eq_true.mp ha _ hx
  simp only [Tuple.get?, hy, beq_iff_eq] at this
  exact this

/-- The merge of two agreeing tuples fits the join's heading. -/
theorem merge_fits {h k j : Heading} (hj : joinHeading h k = .ok j) (hh : h.attrs.Nodup)
    (hk : k.attrs.Nodup) {u v : Tuple} (fu : u.Fits h) (fv : v.Fits k)
    (ha : u.agrees v = true) : (u.merge v).Fits j := by
  obtain ⟨_, hjattrs, hjlook⟩ := joinHeading_spec hj hh hk
  have hvf : ∀ p ∈ v.filter (fun p => (u.get? p.1).isNone), p.1 ∉ u.attrs := by
    intro p hp hpu
    have h1 := (List.mem_filter.mp hp).2
    have h2 := lookup_isSome_iff_mem hpu
    simp only [Tuple.get?] at h1
    cases hl : u.lookup p.1 with
    | none => rw [hl] at h2; cases h2
    | some _ => rw [hl] at h1; cases h1
  have hkeys : ((u ++ v.filter fun p => (u.get? p.1).isNone).map (·.1)).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨fu.nodup, fv.nodup.sublist (List.filter_sublist.map _), fun a ha b hb e => ?_⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    exact hvf p hp (e ▸ ha)
  refine ⟨ofPairs_sorted hkeys, fun a => ?_, fun p hp d hd => ?_⟩
  · rw [Tuple.merge, attrs_ofPairs, hjattrs, ← fu.attrs, ← fv.attrs, List.map_append, List.mem_append]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl h1
      · exact Or.inr ((List.filter_sublist.map _).subset h1)
    · rintro (h1 | h1)
      · exact Or.inl h1
      · by_cases h2 : a ∈ u.attrs
        · exact Or.inl h2
        · refine Or.inr ?_
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h1
          refine List.mem_map_of_mem (List.mem_filter.mpr ⟨hp, ?_⟩)
          simp only [Tuple.get?]
          cases hl : u.lookup p.1 with
          | none => rfl
          | some _ => exact absurd (List.mem_map_of_mem (f := (·.1)) (lookup_mem hl)) h2
  · obtain ⟨a, x⟩ := p
    rw [Tuple.merge, mem_ofPairs, List.mem_append] at hp
    rcases hjlook a d hd with ⟨d₀, had, hcase⟩ | ⟨hna, hkd⟩
    · have hd₀ : h.lookup a = some d₀ := mem_lookup hh had
      cases hp with
      | inl hp =>
        have hx := fu.dom _ hp d₀ hd₀
        rcases hcase with ⟨_, rfl⟩ | ⟨e, he, hi⟩
        · exact hx
        · -- `a` is shared: `v` has it too, with the same value
          have hav : a ∈ v.attrs := (fv.attrs a).mpr (List.mem_map_of_mem (f := (·.1)) (lookup_mem he))
          obtain ⟨⟨a', y⟩, hy, rfl⟩ := List.mem_map.mp hav
          have hvy : v.lookup a' = some y := mem_lookup fv.nodup hy
          have := agrees_eq ha hp hvy
          subst this
          exact Domain.inter_sound hi hx (fv.dom _ hy e he)
      | inr hp =>
        exact absurd ((fu.attrs a).mpr (List.mem_map_of_mem (f := (·.1)) had)) (hvf _ hp)
    · cases hp with
      | inl hp => exact absurd ((fu.attrs a).mp (List.mem_map_of_mem (f := (·.1)) hp)) hna
      | inr hp => exact fv.dom _ (List.mem_filter.mp hp).1 d hkd

theorem join_wf {r s q : Finrel} (h : r.join s = .ok q) (hr : r.WF) (hs : s.WF) : q.WF := by
  have hm := mem_join h
  simp only [join, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i j hj
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨(joinHeading_spec hj hr.nodup hs.nodup).1, fun t ht => ?_⟩
    obtain ⟨u, hu, v, hv, ha, rfl⟩ := (hm t).mp ht
    exact merge_fits hj hr.nodup hs.nodup (hr.fits u hu) (hs.fits v hv) ha

/-- × is ⋈ on headings with no attribute in common: every pair of tuples is merged. -/
theorem mem_product {r s q : Finrel} (h : r.join s = .ok q) (hr : r.WF) (hs : s.WF)
    (hd : ∀ a, a ∈ r.attrs → a ∉ s.attrs) (t : Tuple) :
    t ∈ q.tuples ↔ ∃ u ∈ r.tuples, ∃ v ∈ s.tuples, t = u.merge v := by
  rw [mem_join h]
  constructor
  · rintro ⟨u, hu, v, hv, _, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    refine ⟨u, hu, v, hv, List.all_eq_true.mpr fun ⟨a, x⟩ hx => ?_, rfl⟩
    have ha : a ∈ r.attrs := ((hr.fits u hu).attrs a).mp (List.mem_map_of_mem (f := (·.1)) hx)
    cases hl : v.get? a with
    | none => simp only [hl]
    | some _ =>
      exact absurd (((hs.fits v hv).attrs a).mp (List.mem_map_of_mem (f := (·.1)) (lookup_mem hl)))
        (hd a ha)

/-- extend keeps well-formedness, given that the term's values lie in the domain
`Term.domain` gives it (an assumption: the soundness of `Term.domain` is not proved). -/
theorem extend_wf {res : String} {tm : Term} {r s : Finrel} (h : r.extend res tm = .ok s)
    (hr : r.WF)
    (hdom : ∀ d, tm.domain r.heading = some d → ∀ u ∈ r.tuples, ∀ v, tm.eval u = .ok v →
      d.mem v = true) : s.WF := by
  obtain ⟨hres, d, hd, ts, hts, rfl⟩ := extend_eq_ok.mp h
  have hattrs : (r.heading ++ [(res, d)]).attrs = r.heading.attrs ++ [res] := by
    simp [Heading.attrs]
  refine wf_ofTuples ?_ fun t ht => ?_
  · rw [hattrs, List.nodup_append]
    exact ⟨hr.nodup, by simp, fun a ha b hb e => by simp at hb; subst hb; subst e; exact hres ha⟩
  · obtain ⟨u, hu, v, hv, rfl⟩ := hts.mem_right ht
    have fu := hr.fits u hu
    have hkeys : (((res, v) :: u).map (·.1)).Nodup := by
      rw [List.map_cons, List.nodup_cons]
      exact ⟨fun hm => hres ((fu.attrs res).mp hm), fu.nodup⟩
    refine ⟨ofPairs_sorted hkeys, fun a => ?_, fun p hp d' hd' => ?_⟩
    · rw [attrs_ofPairs, hattrs, List.map_cons, List.mem_cons, List.mem_append]
      have := fu.attrs a
      simp only [Tuple.attrs] at this
      rw [this]
      simp only [List.mem_singleton]
      exact Or.comm
    · rw [mem_ofPairs, List.mem_cons] at hp
      rw [List.lookup_append] at hd'
      cases hp with
      | inl e =>
        subst e
        have : r.heading.lookup res = none := by
          cases hl : r.heading.lookup res with
          | none => rfl
          | some _ => exact absurd (List.mem_map_of_mem (f := (·.1)) (lookup_mem hl)) hres
        rw [this] at hd'
        simp [List.lookup] at hd'
        subst hd'
        exact hdom d hd u hu v hv
      | inr hp =>
        have ha : p.1 ∈ r.heading.attrs := (fu.attrs p.1).mp (List.mem_map_of_mem (f := (·.1)) hp)
        obtain ⟨d₀, hd₀⟩ := Option.isSome_iff_exists.mp (lookup_isSome_iff_mem ha)
        rw [hd₀] at hd'
        change some d₀ = some d' at hd'
        exact (Option.some.inj hd') ▸ fu.dom p hp d₀ hd₀

end Finrel

end Rasso
