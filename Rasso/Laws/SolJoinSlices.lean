import Rasso.Laws.SolJoinPicks

/-!
# Rasso: the members of ⋈_sol, as slices

-/

namespace Rasso


/-! ## Tuple facts, by attribute -/

theorem Tuple.sorted_merge {t u : Tuple} (ht : Tuple.Sorted t) (hu : Tuple.Sorted u) :
    Tuple.Sorted (Tuple.merge t u) := by
  apply Tuple.sorted_ofPairs
  rw [List.map_append, List.nodup_append]
  refine ⟨Tuple.nodup_keys ht, (List.filter_sublist.map _).nodup (Tuple.nodup_keys hu), ?_⟩
  intro x hx y hy e
  subst e
  obtain ⟨⟨_, v⟩, hq, rfl⟩ := List.mem_map.mp hx
  obtain ⟨⟨_, w⟩, hq', e⟩ := List.mem_map.mp hy
  simp only at e; subst e
  have hnone := (List.mem_filter.mp hq').2
  have hsome : Tuple.get? t _ = some v := lookup_of_mem (Tuple.nodup_keys ht) hq
  rw [hsome] at hnone; cases hnone

/-- An attribute is in a tuple exactly when the tuple gives it a value. -/
theorem Tuple.mem_keys_iff {t : Tuple} {a : String} :
    a ∈ t.map (·.1) ↔ (Tuple.get? t a).isSome := by
  induction t with
  | nil => simp [Tuple.get?]
  | cons p t ih =>
    obtain ⟨b, v⟩ := p
    by_cases hab : a = b
    · subst hab; simp [Tuple.get?]
    · rw [Tuple.get?, lookup_cons_ne hab]
      simp only [List.map_cons, List.mem_cons, hab, false_or]
      exact ih

/-- `Exactly`, by attribute: the tuple gives a value exactly to the attributes of `as`. -/
theorem Tuple.exactly_iff {as : List String} {t : Tuple} :
    Tuple.Exactly as t ↔ Tuple.Sorted t ∧ ∀ a, (Tuple.get? t a).isSome ↔ a ∈ as := by
  constructor
  · rintro ⟨⟨hs, hover⟩, hall⟩
    refine ⟨hs, fun a => ⟨fun h => ?_, fun h => Tuple.mem_keys_iff.mp (hall a h)⟩⟩
    obtain ⟨q, hq, e⟩ := List.mem_map.mp (Tuple.mem_keys_iff.mpr h)
    exact e ▸ hover q hq
  · rintro ⟨hs, h⟩
    refine ⟨⟨hs, fun q hq => (h q.1).mp (Tuple.mem_keys_iff.mp (List.mem_map_of_mem hq))⟩,
      fun a ha => Tuple.mem_keys_iff.mpr ((h a).mpr ha)⟩

/-- Restricting a merge of a tuple exactly over `D` with a tuple over attributes outside
`D`, to `D`, gives back the first. -/
theorem Tuple.restrict_merge_left {D : List String} {d x : Tuple}
    (hd : Tuple.Exactly D d) (hx : Tuple.Sorted x) :
    (Tuple.merge d x).restrict D = d := by
  have hd' := Tuple.exactly_iff.mp hd
  refine Tuple.ext_get? (sorted_restrict (Tuple.sorted_merge hd'.1 hx)) hd'.1 fun a => ?_
  rw [get?_restrict, Tuple.get?_merge hd'.1 hx]
  by_cases ha : a ∈ D
  · rw [ite_eq_left ha]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((hd'.2 a).mpr ha)
    rw [hv]; rfl
  · rw [ite_eq_right ha]
    cases h : Tuple.get? d a with
    | none => rfl
    | some v => exact absurd ((hd'.2 a).mp (by simp [h])) ha

/-- Restricting a merge of a tuple with no attribute in `X` and a tuple exactly over `X`,
to `X`, gives back the second. -/
theorem Tuple.restrict_merge_right {X : List String} {d x : Tuple}
    (hd : Tuple.Sorted d) (hdx : ∀ a ∈ X, Tuple.get? d a = none) (hx : Tuple.Exactly X x) :
    (Tuple.merge d x).restrict X = x := by
  have hx' := Tuple.exactly_iff.mp hx
  refine Tuple.ext_get? (sorted_restrict (Tuple.sorted_merge hd hx'.1)) hx'.1 fun a => ?_
  rw [get?_restrict, Tuple.get?_merge hd hx'.1]
  by_cases ha : a ∈ X
  · rw [ite_eq_left ha, hdx a ha]; rfl
  · rw [ite_eq_right ha]
    cases h : Tuple.get? x a with
    | none => rfl
    | some v => exact absurd ((hx'.2 a).mp (by simp [h])) ha

namespace SolJoinLaws

/-! ## A well-formed member's decision at a Data tuple -/

theorem decisionAt_graph {s : Sol} {m : Finrel} {f : Tuple → Tuple}
    (hex : ∀ d ∈ s.data.tuples, Tuple.Exactly s.data.attrs d)
    (hf : ∀ d ∈ s.data.tuples, Tuple.Exactly s.decision.attrs (f d))
    (hm : m.body = (graph s.heading s.data.tuples f).body)
    {d : Tuple} (hd : d ∈ s.data.tuples) :
    s.decisionAt m d = some (f d) := by
  have memm : ∀ r, r ∈ m.tuples ↔ ∃ d' ∈ s.data.tuples, r = d'.merge (f d') := by
    intro r
    rw [← mem_graph (h := s.heading)]
    unfold Finrel.tuples; rw [hm]; exact Iff.rfl
  have back : ∀ d' ∈ s.data.tuples, (d'.merge (f d')).restrict s.data.attrs = d' := fun d' hd' =>
    Tuple.restrict_merge_left (hex d' hd') (Tuple.exactly_iff.mp (hf d' hd')).1
  unfold Sol.decisionAt
  cases hfind : m.tuples.find? (fun r => r.restrict s.data.attrs == d) with
  | none =>
    have := List.find?_eq_none.mp hfind (d.merge (f d)) ((memm _).mpr ⟨d, hd, rfl⟩)
    simp [back d hd] at this
  | some r =>
    have hr := List.find?_some hfind
    have hrm := List.mem_of_find?_eq_some hfind
    obtain ⟨d', hd', rfl⟩ := (memm r).mp hrm
    simp only [back d' hd', beq_iff_eq] at hr
    subst hr
    simp only [Option.map_some, Option.some.injEq]
    have hdx : ∀ a ∈ s.decision.attrs, Tuple.get? d' a = none := by
      intro a ha
      apply Tuple.get?_eq_none_of_over (hex d' hd').1
      intro hin
      unfold Sol.decision Heading.attrs at ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      have := (List.mem_filter.mp hp).2
      have hin' : s.data.attrs.contains p.1 = true := List.contains_iff_mem.mpr hin
      rw [hin'] at this; cases this
    exact Tuple.restrict_merge_right (hex d' hd').1.1 hdx (hf d' hd')

/-! ## Attributes -/

theorem mem_decision_attrs {s : Sol} {a : String} :
    a ∈ s.decision.attrs ↔ a ∈ s.heading.attrs ∧ a ∉ s.data.attrs := by
  unfold Sol.decision Heading.attrs
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hc⟩, rfl⟩
    refine ⟨⟨p, hp, rfl⟩, fun hin => ?_⟩
    have : s.data.attrs.contains p.1 = true := List.contains_iff_mem.mpr hin
    rw [this] at hc; cases hc
  · rintro ⟨⟨p, hp, rfl⟩, hn⟩
    refine ⟨p, ⟨hp, ?_⟩, rfl⟩
    cases hc : s.data.attrs.contains p.1 with
    | false => rfl
    | true => exact absurd (List.contains_iff_mem.mp hc) hn

/-- The attributes of a joined heading are those of both, with no hypothesis on repeats. -/
theorem joinHeading_attrs {h k j : Heading} (hj : Finrel.joinHeading h k = .ok j) (a : String) :
    a ∈ j.attrs ↔ a ∈ h.attrs ∨ a ∈ k.attrs := by
  simp only [Finrel.joinHeading, bind, Except.bind] at hj
  split at hj
  · cases hj
  rename_i left he
  simp only [pure, Except.pure, Except.ok.injEq] at hj
  subst hj
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
  have hla : left.map (·.1) = h.attrs := hfst (mapM_ok.mp he)
  unfold Heading.attrs at hla ⊢
  rw [List.map_append, List.mem_append, hla]
  constructor
  · rintro (h1 | h1)
    · exact .inl h1
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h1
      exact .inr (List.mem_map_of_mem (List.mem_filter.mp hp).1)
  · rintro (h1 | h1)
    · exact .inl h1
    · by_cases hh : a ∈ h.map (·.1)
      · exact .inl hh
      · right
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h1
        refine List.mem_map_of_mem (List.mem_filter.mpr ⟨hp, ?_⟩)
        cases hl : h.lookup p.1 with
        | none => rfl
        | some d => exact absurd (List.mem_map_of_mem (f := (·.1)) (lookup_mem hl)) hh

/-! ## Groups -/

theorem lookup_zip_of_mem {β : Type} {k : Tuple} :
    ∀ {gs : List Tuple} {ps : List β}, k ∈ gs → ps.length = gs.length →
      ∃ m, (gs.zip ps).lookup k = some m ∧ m ∈ ps
  | [], _, h, _ => by cases h
  | g :: gs, [], _, e => by cases e
  | g :: gs, p :: ps, h, e => by
    simp only [List.zip_cons_cons, List.lookup]
    by_cases hk : k = g
    · subst hk; exact ⟨p, by simp, List.mem_cons_self⟩
    · have : (k == g) = false := by simp [hk]
      rw [this]
      obtain ⟨m, h1, h2⟩ := lookup_zip_of_mem (List.mem_cons.mp h |>.resolve_left hk)
        (by simpa using e)
      exact ⟨m, h1, List.mem_cons_of_mem _ h2⟩

theorem lookup_zip_mem {β : Type} {k : Tuple} {m : β} :
    ∀ {gs : List Tuple} {ps : List β}, (gs.zip ps).lookup k = some m → (k, m) ∈ gs.zip ps
  | [], _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | g :: gs, p :: ps, h => by
    simp only [List.zip_cons_cons, List.lookup] at h ⊢
    by_cases hk : k = g
    · subst hk; simp at h; subst h; exact List.mem_cons_self
    · have : (k == g) = false := by simp [hk]
      rw [this] at h
      exact List.mem_cons_of_mem _ (lookup_zip_mem h)

/-- Lookups in a list zipped with keys that have no repeats determine the list. -/
theorem eq_of_lookup_zip {β : Type} :
    ∀ {gs : List Tuple} {ps ps' : List β}, gs.Nodup → ps.length = gs.length → ps'.length = gs.length →
      (∀ g ∈ gs, (gs.zip ps).lookup g = (gs.zip ps').lookup g) → ps = ps'
  | [], [], [], _, _, _, _ => rfl
  | g :: gs, p :: ps, p' :: ps', hn, e, e', h => by
    have h0 := h g List.mem_cons_self
    simp only [List.zip_cons_cons, List.lookup, beq_self_eq_true, Option.some.injEq] at h0
    subst h0
    congr 1
    refine eq_of_lookup_zip (List.nodup_cons.mp hn).2 (by simpa using e) (by simpa using e') ?_
    intro g' hg'
    have := h g' (List.mem_cons_of_mem _ hg')
    have hne : (g' == g) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; subst e; exact (List.nodup_cons.mp hn).1 hg'
    simpa [List.zip_cons_cons, List.lookup, hne] using this
  | [], _ :: _, _, _, e, _, _ => by cases e
  | [], [], _ :: _, _, _, e, _ => by cases e
  | _ :: _, [], _, _, e, _, _ => by cases e
  | _ :: _, _ :: _, [], _, _, e, _ => by cases e

/-- `find?` on a key is `lookup`. -/
theorem find?_fst_eq_lookup {β : Type} {k : Tuple} :
    ∀ {l : List (Tuple × β)}, (l.find? (·.1 == k)).map (·.2) = l.lookup k
  | [] => rfl
  | (g, p) :: l => by
    by_cases hk : k = g
    · subst hk; simp [List.lookup]
    · have h1 : (k == g) = false := by simp [hk]
      have h2 : (g == k) = false := by simp [Ne.symm hk]
      simp only [List.find?_cons, h2, List.lookup, h1]
      exact find?_fst_eq_lookup

theorem nodup_joinGroups (J : Finrel) (G : List String) : (joinGroups J G).Nodup := by
  unfold joinGroups
  split
  · simp
  · exact nodup_dedup _

theorem mem_joinGroups {J : Finrel} {G : List String} {t : Tuple} (ht : t ∈ J.tuples) :
    t.restrict G ∈ joinGroups J G := by
  unfold joinGroups
  split
  · rename_i hG
    have : G = [] := List.isEmpty_iff.mp hG
    subst this
    simp [Tuple.restrict]
  · exact mem_dedup.mpr (List.mem_map_of_mem ht)

/-! ## The joined Data's tuples -/

theorem join_heading_attrs {r s q : Finrel} (h : r.join s = .ok q) (a : String) :
    a ∈ q.attrs ↔ a ∈ r.attrs ∨ a ∈ s.attrs := by
  simp only [Finrel.join, bind, Except.bind] at h
  split at h
  · cases h
  rename_i hd hhd
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact joinHeading_attrs hhd a

/-- `Option.or` gives a value exactly when one side does. -/
theorem isSome_or {x y : Option Value} : (x.or y).isSome ↔ x.isSome ∨ y.isSome := by
  cases x <;> cases y <;> simp

/-- A tuple of the joined Data: sorted, with exactly the attributes of both Data, and
its two parts are tuples of the two Data. -/
theorem join_data_tuple {U V W : Sol} (hj : U.join V = .ok W) (MU : U.MembersOk) (MV : V.MembersOk)
    {t : Tuple} (ht : t ∈ W.data.tuples) :
    Tuple.Sorted t ∧ t.restrict U.data.attrs ∈ U.data.tuples ∧ t.restrict V.data.attrs ∈ V.data.tuples ∧
      ∀ a, (Tuple.get? t a).isSome ↔ a ∈ U.data.attrs ∨ a ∈ V.data.attrs := by
  obtain ⟨hJ, -⟩ := join_shape hj
  obtain ⟨du, hdu, dv, hdv, hag, rfl⟩ := (Finrel.mem_join hJ t).mp ht
  have eu := Tuple.exactly_iff.mp (MU.dataExact du hdu)
  have ev := Tuple.exactly_iff.mp (MV.dataExact dv hdv)
  refine ⟨Tuple.sorted_merge eu.1 ev.1, ?_, ?_, ?_⟩
  · rw [Tuple.restrict_merge_left (MU.dataExact du hdu) ev.1]; exact hdu
  · have : (du.merge dv).restrict V.data.attrs = dv := by
      refine Tuple.ext_get? (sorted_restrict (Tuple.sorted_merge eu.1 ev.1)) ev.1 fun a => ?_
      rw [get?_restrict, Tuple.get?_merge eu.1 ev.1]
      by_cases ha : a ∈ V.data.attrs
      · rw [ite_eq_left ha]
        cases hu : Tuple.get? du a with
        | none => rfl
        | some v =>
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((ev.2 a).mpr ha)
          rw [hw, Finrel.agrees_eq hag (lookup_mem hu) hw]; rfl
      · rw [ite_eq_right ha]
        cases hv : Tuple.get? dv a with
        | some w => exact absurd ((ev.2 a).mp (by simp [hv])) ha
        | none =>
          cases hu : Tuple.get? du a with
          | none => rfl
          | some v => rfl
    rw [this]; exact hdv
  · intro a
    rw [Tuple.get?_merge eu.1 ev.1, isSome_or, eu.2 a, ev.2 a]

/-! ## Glued tuples, by attribute -/

section Glued
variable {t x y : Tuple} {Dt Dx Dy : String → Prop}

/-- The value of a glued tuple. -/
theorem get?_glued (ht : Tuple.Sorted t) (hx : Tuple.Sorted x) (hy : Tuple.Sorted y) (a : String) :
    Tuple.get? ((t.merge x).merge y) a = ((Tuple.get? t a).or (Tuple.get? x a)).or (Tuple.get? y a) := by
  rw [Tuple.get?_merge (Tuple.sorted_merge ht hx) hy, Tuple.get?_merge ht hx]

theorem sorted_glued (ht : Tuple.Sorted t) (hx : Tuple.Sorted x) (hy : Tuple.Sorted y) :
    Tuple.Sorted ((t.merge x).merge y) := Tuple.sorted_merge (Tuple.sorted_merge ht hx) hy

/-- Merge is associative. -/
theorem glued_assoc (ht : Tuple.Sorted t) (hx : Tuple.Sorted x) (hy : Tuple.Sorted y) :
    (t.merge x).merge y = t.merge (x.merge y) := by
  refine Tuple.ext_get? (sorted_glued ht hx hy) (Tuple.sorted_merge ht (Tuple.sorted_merge hx hy)) fun a => ?_
  rw [get?_glued ht hx hy, Tuple.get?_merge ht (Tuple.sorted_merge hx hy), Tuple.get?_merge hx hy,
    Option.or_assoc]

/-- Restricting a glued tuple to attributes where only `t` has values. -/
theorem restrict_glued_t {A : List String} (ht : Tuple.Sorted t) (hx : Tuple.Sorted x) (hy : Tuple.Sorted y)
    (hA : ∀ a ∈ A, Tuple.get? x a = none ∧ Tuple.get? y a = none) :
    ((t.merge x).merge y).restrict A = t.restrict A := by
  refine Tuple.ext_get? (sorted_restrict (sorted_glued ht hx hy)) (sorted_restrict ht) fun a => ?_
  rw [get?_restrict, get?_restrict, get?_glued ht hx hy]
  by_cases ha : a ∈ A
  · rw [ite_eq_left ha, ite_eq_left ha, (hA a ha).1, (hA a ha).2, Option.or_none, Option.or_none]
  · rw [ite_eq_right ha, ite_eq_right ha]

/-- Restricting a glued tuple to `D ∪ X`, where `t` has exactly `D` among them and `x` is
exactly `X`, gives `(t.restrict D).merge x`. -/
theorem restrict_glued_left {D X H : List String} (ht : Tuple.Sorted t) (hx : Tuple.Exactly X x)
    (hy : Tuple.Sorted y) (hH : ∀ a, a ∈ H ↔ a ∈ D ∨ a ∈ X)
    (htX : ∀ a ∈ X, Tuple.get? t a = none) (hXD : ∀ a ∈ X, a ∉ D)
    (htD : ∀ a ∈ D, (Tuple.get? t a).isSome) :
    ((t.merge x).merge y).restrict H = (t.restrict D).merge x := by
  have hx' := Tuple.exactly_iff.mp hx
  refine Tuple.ext_get? (sorted_restrict (sorted_glued ht hx'.1 hy))
    (Tuple.sorted_merge (sorted_restrict ht) hx'.1) fun a => ?_
  rw [get?_restrict, get?_glued ht hx'.1 hy, Tuple.get?_merge (sorted_restrict ht) hx'.1, get?_restrict]
  by_cases hX : a ∈ X
  · rw [ite_eq_left ((hH a).mpr (.inr hX)), ite_eq_right (hXD a hX), htX a hX, Option.none_or]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((hx'.2 a).mpr hX)
    rw [hv]; rfl
  · have hxn : Tuple.get? x a = none := by
      cases h : Tuple.get? x a with
      | none => rfl
      | some _ => exact absurd ((hx'.2 a).mp (by simp [h])) hX
    rw [hxn]
    by_cases hD : a ∈ D
    · rw [ite_eq_left ((hH a).mpr (.inl hD)), ite_eq_left hD]
      cases h : Tuple.get? t a with
      | none => have := htD a hD; rw [h] at this; cases this
      | some v => rfl
    · rw [ite_eq_right (fun h => ((hH a).mp h).elim hD hX), ite_eq_right hD]; rfl

/-- Restricting a glued tuple to `D ∪ Y`, where `t` has exactly `D` among them, `y` is
exactly `Y`, and `x` agrees with `y`, gives `(t.restrict D).merge y`. -/
theorem restrict_glued_right {D Y H : List String} (ht : Tuple.Sorted t) (hx : Tuple.Sorted x)
    (hy : Tuple.Exactly Y y) (hH : ∀ a, a ∈ H ↔ a ∈ D ∨ a ∈ Y)
    (htY : ∀ a ∈ Y, Tuple.get? t a = none) (hYD : ∀ a ∈ Y, a ∉ D)
    (hxD : ∀ a ∈ D, Tuple.get? x a = none)
    (hag : ∀ a v w, Tuple.get? x a = some v → Tuple.get? y a = some w → v = w) :
    ((t.merge x).merge y).restrict H = (t.restrict D).merge y := by
  have hy' := Tuple.exactly_iff.mp hy
  refine Tuple.ext_get? (sorted_restrict (sorted_glued ht hx hy'.1))
    (Tuple.sorted_merge (sorted_restrict ht) hy'.1) fun a => ?_
  rw [get?_restrict, get?_glued ht hx hy'.1, Tuple.get?_merge (sorted_restrict ht) hy'.1, get?_restrict]
  by_cases hY : a ∈ Y
  · rw [ite_eq_left ((hH a).mpr (.inr hY)), ite_eq_right (hYD a hY), htY a hY, Option.none_or, Option.none_or]
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp ((hy'.2 a).mpr hY)
    rw [hw]
    cases hxa : Tuple.get? x a with
    | none => rfl
    | some v => rw [hag a v w hxa hw]; rfl
  · have hyn : Tuple.get? y a = none := by
      cases h : Tuple.get? y a with
      | none => rfl
      | some _ => exact absurd ((hy'.2 a).mp (by simp [h])) hY
    rw [hyn, Option.or_none, Option.or_none]
    by_cases hD : a ∈ D
    · rw [ite_eq_left ((hH a).mpr (.inl hD)), ite_eq_left hD, hxD a hD, Option.or_none]
    · rw [ite_eq_right (fun h => ((hH a).mp h).elim hD hY), ite_eq_right hD]

/-- Two tuples that agree give the same value wherever both give one. -/
theorem agrees_get? {x y : Tuple} (h : x.agrees y = true) :
    ∀ a v w, Tuple.get? x a = some v → Tuple.get? y a = some w → v = w :=
  fun _ _ _ hv hw => Finrel.agrees_eq h (lookup_mem hv) hw

end Glued

/-! ## Decisions and groups -/

/-- A decision of a well-formed member is sorted and has values only at Decision attributes. -/
theorem decisionAt_shape {s : Sol} (hs : s.MembersOk) {m : Finrel} (hm : m ∈ s.candidates) {d y : Tuple}
    (h : s.decisionAt m d = some y) :
    Tuple.Sorted y ∧ ∀ a, a ∉ s.decision.attrs → Tuple.get? y a = none := by
  obtain ⟨f, hf, hmb⟩ := hs.graph m hm
  unfold Sol.decisionAt at h
  cases hfind : m.tuples.find? (fun r => r.restrict s.data.attrs == d) with
  | none => simp [hfind] at h
  | some r =>
    simp only [hfind, Option.map_some, Option.some.injEq] at h
    subst h
    have hr : r ∈ (graph s.heading s.data.tuples f).tuples := by
      have := List.mem_of_find?_eq_some hfind
      unfold Finrel.tuples at this; rw [hmb] at this; exact this
    obtain ⟨d', hd', rfl⟩ := (mem_graph _).mp hr
    have hs1 := Tuple.sorted_merge (hs.dataExact d' hd').1.1 (Tuple.exactly_iff.mp (hf d' hd')).1
    refine ⟨sorted_restrict hs1, fun a ha => ?_⟩
    rw [get?_restrict, ite_eq_right ha]

/-- A group of `J` by `G`, when every tuple of `J` is sorted with values at `G`, is exactly
over `G`. -/
theorem group_exactly {J : Finrel} {G : List String}
    (hJ : ∀ t ∈ J.tuples, Tuple.Sorted t ∧ ∀ a ∈ G, (Tuple.get? t a).isSome)
    {g : Tuple} (hg : g ∈ joinGroups J G) : Tuple.Exactly G g := by
  unfold joinGroups at hg
  split at hg
  · rename_i hG
    have : G = [] := List.isEmpty_iff.mp hG
    subst this
    simp only [List.mem_singleton] at hg; subst hg
    exact ⟨⟨List.Pairwise.nil, fun _ h => by cases h⟩, fun _ h => by cases h⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (mem_dedup.mp hg)
    refine Tuple.exactly_iff.mpr ⟨sorted_restrict (hJ t ht).1, fun a => ?_⟩
    rw [get?_restrict]
    by_cases ha : a ∈ G
    · rw [ite_eq_left ha]; exact ⟨fun _ => ha, fun _ => (hJ t ht).2 a ha⟩
    · rw [ite_eq_right ha]; simp [ha]

/-! ## Slices -/

/-- The U-slice of `c` at the U-group `g`: its tuples in the group, each restricted to U's
heading. -/
def sliceU (U V : Sol) (c : Finrel) (g : Tuple) : Body :=
  Body.ofList ((c.tuples.filter fun r => r.restrict (gU U V) == g).map (·.restrict U.heading.attrs))

/-- The V-slice of `c` at the V-group `g`. -/
def sliceV (U V : Sol) (c : Finrel) (g : Tuple) : Body :=
  Body.ofList ((c.tuples.filter fun r => r.restrict (gV U V) == g).map (·.restrict V.heading.attrs))

theorem mem_slice {c : Finrel} {G H : List String} {g r : Tuple} :
    r ∈ (Body.ofList ((c.tuples.filter fun r => r.restrict G == g).map (·.restrict H))).toList ↔
      ∃ c' ∈ c.tuples, c'.restrict G = g ∧ r = c'.restrict H := by
  rw [Body.mem_toList_ofList, List.mem_map]
  simp only [List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨c', ⟨h1, h2⟩, rfl⟩; exact ⟨c', h1, h2, rfl⟩
  · rintro ⟨c', h1, h2, rfl⟩; exact ⟨c', ⟨h1, h2⟩, rfl⟩

theorem mem_glue {U V : Sol} {J : Finrel} {h : Heading} {ps : List Finrel} {vs : List (Tuple × Finrel)}
    {r : Tuple} : r ∈ (glue U V J h ps vs).tuples ↔ ∃ t ∈ J.tuples, r =
      (t.merge ((pdU U V J ps t).getD [])).merge
        (((vs.find? (·.1 == t.restrict (gV U V))).bind fun p => pdV1 V p.2 t).getD []) := by
  unfold glue
  rw [Finrel.mem_ofTuples, List.mem_map]
  exact ⟨fun ⟨t, ht, e⟩ => ⟨t, ht, e.symm⟩, fun ⟨t, ht, e⟩ => ⟨t, ht, e.symm⟩⟩

/-- The V decision a glued tuple takes is sorted and has values only at V's Decision. -/
theorem glue_y_shape {U V : Sol} (MV : V.MembersOk) {vs : List (Tuple × Finrel)}
    (hvs : ∀ p ∈ vs, p.2 ∈ V.candidates) (t : Tuple) :
    Tuple.Sorted ((((vs.find? (·.1 == t.restrict (gV U V))).bind fun p => pdV1 V p.2 t).getD [])) ∧
      ∀ a, a ∉ V.decision.attrs →
        Tuple.get? (((vs.find? (·.1 == t.restrict (gV U V))).bind fun p => pdV1 V p.2 t).getD []) a = none := by
  cases hf : vs.find? (·.1 == t.restrict (gV U V)) with
  | none => exact ⟨List.Pairwise.nil, fun _ _ => rfl⟩
  | some p =>
    simp only [Option.bind_some]
    cases hd : pdV1 V p.2 t with
    | none => exact ⟨List.Pairwise.nil, fun _ _ => rfl⟩
    | some y =>
      exact decisionAt_shape MV (hvs p (List.mem_of_find?_eq_some hf)) hd

/-- **A glued member's U-slices are its U-picks.** -/
theorem slice_glue_U {U V W : Sol} (hj : U.join V = .ok W) (MU : U.MembersOk) (MV : V.MembersOk)
    {ps : List Finrel} {vs : List (Tuple × Finrel)}
    (hps : ps.length = (joinGroups W.data (gU U V)).length) (hpm : ∀ m ∈ ps, m ∈ U.candidates)
    (hvs : ∀ p ∈ vs, p.2 ∈ V.candidates)
    {g : Tuple} {m : Finrel} (hg : g ∈ joinGroups W.data (gU U V))
    (hm : ((joinGroups W.data (gU U V)).zip ps).lookup g = some m) :
    sliceU U V (glue U V W.data W.heading ps vs) g = m.body := by
  obtain ⟨q1, q2⟩ := join_q2 hj
  obtain ⟨-, w3U, -⟩ := join_w3 hj
  have hmU : m ∈ U.candidates := hpm m (List.of_mem_zip (lookup_zip_mem hm)).2
  obtain ⟨f, hf, hmb⟩ := MU.graph m hmU
  -- attribute facts
  have hUx : ∀ a ∈ U.decision.attrs, a ∉ U.data.attrs := fun a ha => (mem_decision_attrs.mp ha).2
  have hVx : ∀ a ∈ V.decision.attrs, a ∉ V.data.attrs := fun a ha => (mem_decision_attrs.mp ha).2
  have hgU : ∀ a ∈ gU U V, a ∈ V.data.attrs ∧ a ∉ U.data.attrs := by
    intro a ha
    obtain ⟨h1, h2⟩ := List.mem_filter.mp ha
    refine ⟨h1, fun hin => ?_⟩
    rw [List.contains_iff_mem.mpr hin] at h2; cases h2
  have hUh : ∀ a, a ∈ U.heading.attrs ↔ a ∈ U.data.attrs ∨ a ∈ U.decision.attrs := by
    intro a
    constructor
    · intro ha
      by_cases hd : a ∈ U.data.attrs
      · exact .inl hd
      · exact .inr (mem_decision_attrs.mpr ⟨ha, hd⟩)
    · rintro (ha | ha)
      · exact MU.dataAttrs a ha
      · exact (mem_decision_attrs.mp ha).1
  -- the glued tuple at a J tuple of the group
  have key : ∀ t ∈ W.data.tuples, ∀ m' : Finrel,
      ((joinGroups W.data (gU U V)).zip ps).lookup (t.restrict (gU U V)) = some m' →
      ∀ f' : Tuple → Tuple, (∀ d ∈ U.data.tuples, Tuple.Exactly U.decision.attrs (f' d)) →
      m'.body = (graph U.heading U.data.tuples f').body →
      let r := (t.merge ((pdU U V W.data ps t).getD [])).merge
        (((vs.find? (·.1 == t.restrict (gV U V))).bind fun p => pdV1 V p.2 t).getD [])
      r.restrict (gU U V) = t.restrict (gU U V) ∧
        r.restrict U.heading.attrs = (t.restrict U.data.attrs).merge (f' (t.restrict U.data.attrs)) := by
    intro t ht m' hl f' hf' hmb'
    obtain ⟨hts, htu, -, hkeys⟩ := join_data_tuple hj MU MV ht
    have hx : pdU U V W.data ps t = some (f' (t.restrict U.data.attrs)) := by
      simp only [pdU, hl, Option.bind_some]
      exact decisionAt_graph MU.dataExact hf' hmb' htu
    rw [hx, Option.getD_some]
    obtain ⟨hys, hyn⟩ := glue_y_shape (U := U) MV hvs t
    have hxe := hf' _ htu
    have hxs := (Tuple.exactly_iff.mp hxe).1
    have hxn : ∀ a, a ∉ U.decision.attrs → Tuple.get? (f' (t.restrict U.data.attrs)) a = none := by
      intro a ha
      cases h : Tuple.get? (f' (t.restrict U.data.attrs)) a with
      | none => rfl
      | some _ => exact absurd ((Tuple.exactly_iff.mp hxe).2 a |>.mp (by simp [h])) ha
    refine ⟨restrict_glued_t hts hxs hys fun a ha => ⟨hxn a ?_, hyn a ?_⟩, ?_⟩
    · exact fun hx' => q2 a (hgU a ha).1 hx'
    · exact fun hy' => hVx a hy' (hgU a ha).1
    · refine restrict_glued_left hts hxe hys hUh ?_ hUx ?_
      · intro a ha
        cases h : Tuple.get? t a with
        | none => rfl
        | some _ =>
          rcases (hkeys a).mp (by simp [h]) with h1 | h1
          · exact absurd h1 (hUx a ha)
          · exact absurd ha (q2 a h1)
      · intro a ha; exact (hkeys a).mpr (.inl ha)
  apply Body.ext
  intro r
  unfold sliceU
  rw [mem_slice]
  have memb : ∀ (m' : Finrel) (f' : Tuple → Tuple), m'.body = (graph U.heading U.data.tuples f').body →
      ∀ r, r ∈ m'.body.toList ↔ ∃ d ∈ U.data.tuples, r = d.merge (f' d) := by
    intro m' f' hmb' r
    rw [hmb']; exact mem_graph (h := U.heading) r
  constructor
  · rintro ⟨c', hc', hcg, rfl⟩
    obtain ⟨t, ht, rfl⟩ := mem_glue.mp hc'
    obtain ⟨-, htu, -, -⟩ := join_data_tuple hj MU MV ht
    obtain ⟨m', hl, hm'⟩ := lookup_zip_of_mem (mem_joinGroups (G := gU U V) ht) hps
    obtain ⟨f', hf', hmb'⟩ := MU.graph m' (hpm m' hm')
    have hk := key t ht m' hl f' hf' hmb'
    simp only at hk hcg
    rw [hk.1] at hcg
    rw [hcg, hm] at hl
    cases hl
    rw [hk.2, memb m f' hmb']
    exact ⟨_, htu, rfl⟩
  · intro hr
    obtain ⟨d, hd, rfl⟩ := (memb m f hmb r).mp hr
    -- the J tuple `d.merge g`
    have hJs : ∀ t ∈ W.data.tuples, Tuple.Sorted t ∧ ∀ a ∈ gU U V, (Tuple.get? t a).isSome := by
      intro t ht
      obtain ⟨hts, -, -, hkeys⟩ := join_data_tuple hj MU MV ht
      exact ⟨hts, fun a ha => (hkeys a).mpr (.inr (hgU a ha).1)⟩
    have hge := group_exactly hJs hg
    have hde := MU.dataExact d hd
    have htJ : d.merge g ∈ W.data.tuples := by
      have := w3U g hg d hd
      unfold Body.mem at this
      exact List.contains_iff_mem.mp this
    have e1 : (d.merge g).restrict (gU U V) = g :=
      Tuple.restrict_merge_right hde.1.1 (fun a ha =>
        Tuple.get?_eq_none_of_over hde.1 (hgU a ha).2) hge
    have e2 : (d.merge g).restrict U.data.attrs = d :=
      Tuple.restrict_merge_left hde (Tuple.exactly_iff.mp hge).1
    have hl : ((joinGroups W.data (gU U V)).zip ps).lookup ((d.merge g).restrict (gU U V)) = some m := by
      rw [e1]; exact hm
    have hk := key _ htJ m hl f hf hmb
    simp only at hk
    refine ⟨_, mem_glue.mpr ⟨_, htJ, rfl⟩, by rw [hk.1, e1], ?_⟩
    rw [hk.2, e2]

/-- The U decision a glued tuple takes, when it has one, is sorted and has values only at
U's Decision. -/
theorem pdU_shape {U V : Sol} (MU : U.MembersOk) {J : Finrel} {ps : List Finrel}
    (hpm : ∀ m ∈ ps, m ∈ U.candidates) {t x : Tuple} (h : pdU U V J ps t = some x) :
    Tuple.Sorted x ∧ ∀ a, a ∉ U.decision.attrs → Tuple.get? x a = none := by
  unfold pdU at h
  cases hl : ((joinGroups J (gU U V)).zip ps).lookup (t.restrict (gU U V)) with
  | none => rw [hl] at h; cases h
  | some m =>
    rw [hl, Option.bind_some] at h
    exact decisionAt_shape MU (hpm m (List.of_mem_zip (lookup_zip_mem hl)).2) h

/-- **A glued member's V-slices are its V-picks.** -/
theorem slice_glue_V {U V W : Sol} (hj : U.join V = .ok W) (MU : U.MembersOk) (MV : V.MembersOk)
    {ps qs : List Finrel} (hpm : ∀ m ∈ ps, m ∈ U.candidates)
    (hqs : qs.length = (joinGroups W.data (gV U V)).length) (hqm : ∀ q ∈ qs, q ∈ V.candidates)
    (hag : ∀ p ∈ (joinGroups W.data (gV U V)).zip qs, ∀ t ∈ W.data.tuples,
      t.restrict (gV U V) = p.1 → agreeAt U V W.data ps p.2 t = true)
    {g : Tuple} {q : Finrel} (hg : g ∈ joinGroups W.data (gV U V))
    (hq : ((joinGroups W.data (gV U V)).zip qs).lookup g = some q) :
    sliceV U V (glue U V W.data W.heading ps ((joinGroups W.data (gV U V)).zip qs)) g = q.body := by
  obtain ⟨q1, q2⟩ := join_q2 hj
  obtain ⟨-, -, w3V⟩ := join_w3 hj
  have hqV : q ∈ V.candidates := hqm q (List.of_mem_zip (lookup_zip_mem hq)).2
  obtain ⟨f, hf, hqb⟩ := MV.graph q hqV
  have hUx : ∀ a ∈ U.decision.attrs, a ∉ U.data.attrs := fun a ha => (mem_decision_attrs.mp ha).2
  have hVx : ∀ a ∈ V.decision.attrs, a ∉ V.data.attrs := fun a ha => (mem_decision_attrs.mp ha).2
  have hgV : ∀ a ∈ gV U V, a ∈ U.data.attrs ∧ a ∉ V.data.attrs := by
    intro a ha
    obtain ⟨h1, h2⟩ := List.mem_filter.mp ha
    refine ⟨h1, fun hin => ?_⟩
    rw [List.contains_iff_mem.mpr hin] at h2; cases h2
  have hVh : ∀ a, a ∈ V.heading.attrs ↔ a ∈ V.data.attrs ∨ a ∈ V.decision.attrs := by
    intro a
    constructor
    · intro ha
      by_cases hd : a ∈ V.data.attrs
      · exact .inl hd
      · exact .inr (mem_decision_attrs.mpr ⟨ha, hd⟩)
    · rintro (ha | ha)
      · exact MV.dataAttrs a ha
      · exact (mem_decision_attrs.mp ha).1
  have key : ∀ t ∈ W.data.tuples, ∀ q' : Finrel,
      ((joinGroups W.data (gV U V)).zip qs).lookup (t.restrict (gV U V)) = some q' →
      ∀ f' : Tuple → Tuple, (∀ d ∈ V.data.tuples, Tuple.Exactly V.decision.attrs (f' d)) →
      q'.body = (graph V.heading V.data.tuples f').body →
      let r := (t.merge ((pdU U V W.data ps t).getD [])).merge
        ((((joinGroups W.data (gV U V)).zip qs).find? (·.1 == t.restrict (gV U V)) |>.bind
          fun p => pdV1 V p.2 t).getD [])
      r.restrict (gV U V) = t.restrict (gV U V) ∧
        r.restrict V.heading.attrs = (t.restrict V.data.attrs).merge (f' (t.restrict V.data.attrs)) := by
    intro t ht q' hl f' hf' hqb'
    obtain ⟨hts, -, htv, hkeys⟩ := join_data_tuple hj MU MV ht
    have hy : pdV1 V q' t = some (f' (t.restrict V.data.attrs)) :=
      decisionAt_graph MV.dataExact hf' hqb' htv
    have hfind : ((((joinGroups W.data (gV U V)).zip qs).find? (·.1 == t.restrict (gV U V))).bind
        fun p => pdV1 V p.2 t) = some (f' (t.restrict V.data.attrs)) := by
      have e := find?_fst_eq_lookup (l := (joinGroups W.data (gV U V)).zip qs) (k := t.restrict (gV U V))
      rw [hl] at e
      cases hf2 : ((joinGroups W.data (gV U V)).zip qs).find? (·.1 == t.restrict (gV U V)) with
      | none => rw [hf2] at e; cases e
      | some p =>
        rw [hf2] at e
        simp only [Option.map_some, Option.some.injEq] at e
        rw [Option.bind_some, e, hy]
    rw [hfind, Option.getD_some]
    -- the agreement at t
    have ha := hag (t.restrict (gV U V), q') (lookup_zip_mem hl) t ht rfl
    unfold agreeAt at ha
    rw [hy] at ha
    cases hx : pdU U V W.data ps t with
    | none => rw [hx] at ha; cases ha
    | some x =>
      rw [hx] at ha
      simp only at ha
      rw [Option.getD_some]
      obtain ⟨hxs, hxn⟩ := pdU_shape MU hpm hx
      have hye := hf' _ htv
      have hys := (Tuple.exactly_iff.mp hye).1
      have hyn : ∀ a, a ∉ V.decision.attrs → Tuple.get? (f' (t.restrict V.data.attrs)) a = none := by
        intro a ha'
        cases h : Tuple.get? (f' (t.restrict V.data.attrs)) a with
        | none => rfl
        | some _ => exact absurd ((Tuple.exactly_iff.mp hye).2 a |>.mp (by simp [h])) ha'
      refine ⟨restrict_glued_t hts hxs hys fun a ha' => ⟨hxn a ?_, hyn a ?_⟩, ?_⟩
      · exact fun hx' => hUx a hx' (hgV a ha').1
      · exact fun hy' => q1 a (hgV a ha').1 hy'
      · refine restrict_glued_right hts hxs hye hVh ?_ hVx ?_ (agrees_get? ha)
        · intro a ha'
          cases h : Tuple.get? t a with
          | none => rfl
          | some _ =>
            rcases (hkeys a).mp (by simp [h]) with h1 | h1
            · exact absurd ha' (q1 a h1)
            · exact absurd h1 (hVx a ha')
        · intro a ha'
          exact hxn a (fun hx' => q2 a ha' hx')
  apply Body.ext
  intro r
  unfold sliceV
  rw [mem_slice]
  have memb : ∀ (q' : Finrel) (f' : Tuple → Tuple), q'.body = (graph V.heading V.data.tuples f').body →
      ∀ r, r ∈ q'.body.toList ↔ ∃ d ∈ V.data.tuples, r = d.merge (f' d) := by
    intro q' f' hqb' r
    rw [hqb']; exact mem_graph (h := V.heading) r
  constructor
  · rintro ⟨c', hc', hcg, rfl⟩
    obtain ⟨t, ht, rfl⟩ := mem_glue.mp hc'
    obtain ⟨-, -, htv, -⟩ := join_data_tuple hj MU MV ht
    obtain ⟨q', hl, hq'⟩ := lookup_zip_of_mem (mem_joinGroups (G := gV U V) ht) hqs
    obtain ⟨f', hf', hqb'⟩ := MV.graph q' (hqm q' hq')
    have hk := key t ht q' hl f' hf' hqb'
    simp only at hk hcg
    rw [hk.1] at hcg
    rw [hcg, hq] at hl
    cases hl
    rw [hk.2, memb q f' hqb']
    exact ⟨_, htv, rfl⟩
  · intro hr
    obtain ⟨d, hd, rfl⟩ := (memb q f hqb r).mp hr
    have hJs : ∀ t ∈ W.data.tuples, Tuple.Sorted t ∧ ∀ a ∈ gV U V, (Tuple.get? t a).isSome := by
      intro t ht
      obtain ⟨hts, -, -, hkeys⟩ := join_data_tuple hj MU MV ht
      exact ⟨hts, fun a ha => (hkeys a).mpr (.inl (hgV a ha).1)⟩
    have hge := group_exactly hJs hg
    have hde := MV.dataExact d hd
    have htJ : d.merge g ∈ W.data.tuples := by
      have := w3V g hg d hd
      unfold Body.mem at this
      exact List.contains_iff_mem.mp this
    have e1 : (d.merge g).restrict (gV U V) = g :=
      Tuple.restrict_merge_right hde.1.1 (fun a ha =>
        Tuple.get?_eq_none_of_over hde.1 (hgV a ha).2) hge
    have e2 : (d.merge g).restrict V.data.attrs = d :=
      Tuple.restrict_merge_left hde (Tuple.exactly_iff.mp hge).1
    have hl : ((joinGroups W.data (gV U V)).zip qs).lookup ((d.merge g).restrict (gV U V)) = some q := by
      rw [e1]; exact hq
    have hk := key _ htJ q hl f hf hqb
    simp only at hk
    refine ⟨_, mem_glue.mpr ⟨_, htJ, rfl⟩, by rw [hk.1, e1], ?_⟩
    rw [hk.2, e2]

/-! ## Membership, "→" -/

/-- **Membership, "→".** Each U-slice of a member of U ⋈_sol V is a member of U, and each
V-slice a member of V (by body). -/
theorem mem_join_sound {U V W : Sol} (hj : U.join V = .ok W) (MU : U.MembersOk) (MV : V.MembersOk)
    {c : Finrel} (hc : c ∈ W.candidates) :
    (∀ g ∈ joinGroups W.data (gU U V), ∃ m ∈ U.candidates, m.body = sliceU U V c g) ∧
    (∀ g ∈ joinGroups W.data (gV U V), ∃ q ∈ V.candidates, q.body = sliceV U V c g) := by
  obtain ⟨ps, qs, h1, h2, h3, h4, rfl⟩ := (mem_join_picks hj).mp hc
  have hqm : ∀ q ∈ qs, q ∈ V.candidates := (zip_snd_forall (P := (· ∈ V.candidates)) h3).mp fun p hp => (h4 p hp).1
  have hvs : ∀ p ∈ (joinGroups W.data (gV U V)).zip qs, p.2 ∈ V.candidates := fun p hp => (h4 p hp).1
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨m, hl, hm⟩ := lookup_zip_of_mem hg h1
    exact ⟨m, h2 m hm, (slice_glue_U hj MU MV h1 h2 hvs hg hl).symm⟩
  · obtain ⟨q, hl, hq⟩ := lookup_zip_of_mem hg h3
    exact ⟨q, hqm q hq, (slice_glue_V hj MU MV h2 h3 hqm (fun p hp => (h4 p hp).2) hg hl).symm⟩

/-! ## ⋈_sol keeps `MembersOk` -/

theorem join_membersOk {U V W : Sol} (hj : U.join V = .ok W) (MU : U.MembersOk) (MV : V.MembersOk) :
    W.MembersOk := by
  obtain ⟨hJ, dec, hdec, hh⟩ := join_shape hj
  obtain ⟨q1, q2⟩ := join_q2 hj
  have hUx : ∀ a ∈ U.decision.attrs, a ∉ U.data.attrs := fun a ha => (mem_decision_attrs.mp ha).2
  have hVx : ∀ a ∈ V.decision.attrs, a ∉ V.data.attrs := fun a ha => (mem_decision_attrs.mp ha).2
  have hJa : ∀ a, a ∈ W.data.attrs ↔ a ∈ U.data.attrs ∨ a ∈ V.data.attrs := join_heading_attrs hJ
  have hWx : ∀ a, a ∈ W.decision.attrs ↔ a ∈ U.decision.attrs ∨ a ∈ V.decision.attrs := by
    intro a
    rw [mem_decision_attrs, hh, attrs_append, List.mem_append, joinHeading_attrs hdec]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact h1
    · intro h1
      refine ⟨.inr h1, fun h2 => ?_⟩
      rcases (hJa a).mp h2 with h3 | h3 <;> rcases h1 with h4 | h4
      · exact hUx a h4 h3
      · exact q1 a h3 h4
      · exact q2 a h3 h4
      · exact hVx a h4 h3
  refine ⟨fun a ha => ?_, fun t ht => ?_, fun c hc => ?_⟩
  · rw [hh, attrs_append]; exact List.mem_append_left _ ha
  · obtain ⟨hts, -, -, hkeys⟩ := join_data_tuple hj MU MV ht
    exact Tuple.exactly_iff.mpr ⟨hts, fun a => by rw [hkeys, hJa]⟩
  · obtain ⟨ps, qs, h1, h2, h3, h4, rfl⟩ := (mem_join_picks hj).mp hc
    have hqm : ∀ q ∈ qs, q ∈ V.candidates :=
      (zip_snd_forall (P := (· ∈ V.candidates)) h3).mp fun p hp => (h4 p hp).1
    let xs (t : Tuple) := (pdU U V W.data ps t).getD []
    let ys (t : Tuple) := ((((joinGroups W.data (gV U V)).zip qs).find? (·.1 == t.restrict (gV U V))).bind
      fun p => pdV1 V p.2 t).getD []
    refine ⟨fun t => (xs t).merge (ys t), fun t ht => ?_, ?_⟩
    · -- the decisions at a J tuple exist and are exact
      obtain ⟨hts, htu, htv, -⟩ := join_data_tuple hj MU MV ht
      obtain ⟨m, hl, hm⟩ := lookup_zip_of_mem (mem_joinGroups (G := gU U V) ht) h1
      obtain ⟨f, hf, hmb⟩ := MU.graph m (h2 m hm)
      have hx : xs t = f (t.restrict U.data.attrs) := by
        show (pdU U V W.data ps t).getD [] = _
        simp only [pdU, hl, Option.bind_some, decisionAt_graph MU.dataExact hf hmb htu, Option.getD_some]
      obtain ⟨q, hl', hq⟩ := lookup_zip_of_mem (mem_joinGroups (G := gV U V) ht) h3
      obtain ⟨f', hf', hqb⟩ := MV.graph q (hqm q hq)
      have hy : ys t = f' (t.restrict V.data.attrs) := by
        show ((((joinGroups W.data (gV U V)).zip qs).find? (·.1 == t.restrict (gV U V))).bind
          fun p => pdV1 V p.2 t).getD [] = _
        have e := find?_fst_eq_lookup (l := (joinGroups W.data (gV U V)).zip qs) (k := t.restrict (gV U V))
        rw [hl'] at e
        cases hf2 : ((joinGroups W.data (gV U V)).zip qs).find? (·.1 == t.restrict (gV U V)) with
        | none => rw [hf2] at e; cases e
        | some p =>
          rw [hf2] at e
          simp only [Option.map_some, Option.some.injEq] at e
          rw [Option.bind_some, e]
          simp only [pdV1, decisionAt_graph MV.dataExact hf' hqb htv, Option.getD_some]
      show Tuple.Exactly W.decision.attrs ((xs t).merge (ys t))
      rw [hx, hy]
      have ex := Tuple.exactly_iff.mp (hf _ htu)
      have ey := Tuple.exactly_iff.mp (hf' _ htv)
      refine Tuple.exactly_iff.mpr ⟨Tuple.sorted_merge ex.1 ey.1, fun a => ?_⟩
      rw [Tuple.get?_merge ex.1 ey.1, isSome_or, ex.2 a, ey.2 a, hWx]
    · -- the glued list is the graph's list
      unfold glue graph
      congr 2
      apply List.map_congr_left
      intro t ht
      obtain ⟨hts, -, -, -⟩ := join_data_tuple hj MU MV ht
      have hxs : Tuple.Sorted (xs t) := by
        show Tuple.Sorted ((pdU U V W.data ps t).getD [])
        cases hx : pdU U V W.data ps t with
        | none => exact List.Pairwise.nil
        | some x => exact (pdU_shape MU h2 hx).1
      have hys : Tuple.Sorted (ys t) := (glue_y_shape (U := U) MV (fun p hp => (h4 p hp).1) t).1
      exact glued_assoc hts hxs hys

/-! ## No member twice -/

theorem nodup_of_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun ha => h.1 (List.mem_map_of_mem ha), nodup_of_map h.2⟩

theorem inj_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => by cases hx
  | a :: l, h, x, hx, y, hy, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with hxa | hx' <;> rcases List.mem_cons.mp hy with hya | hy'
    · rw [hxa, hya]
    · subst hxa; exact absurd (e ▸ List.mem_map_of_mem hy') h.1
    · subst hya; exact absurd (e.symm ▸ List.mem_map_of_mem hx') h.1
    · exact inj_of_nodup_map h.2 x hx' y hy' e

/-- A list of pairs, each block tagged with its own first component, has no repeats when
the tags have none and each block has none. -/
theorem nodup_flatMap_tag {α β : Type} {g : α → List β} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, (g a).Nodup) → (l.flatMap fun a => (g a).map (a, ·)).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hn, hg => by
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨?_, nodup_flatMap_tag (List.nodup_cons.mp hn).2 fun b hb => hg b (List.mem_cons_of_mem _ hb), ?_⟩
    · exact nodup_map_on (fun x _ y _ e => by simpa using e) (hg a List.mem_cons_self)
    · intro x hx y hy e
      subst e
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx
      obtain ⟨b, hb, hy'⟩ := List.mem_flatMap.mp hy
      obtain ⟨_, -, e⟩ := List.mem_map.mp hy'
      simp only [Prod.mk.injEq] at e
      exact (List.nodup_cons.mp hn).1 (e.1 ▸ hb)

theorem sliceU_congr {U V : Sol} {c c' : Finrel} (e : c.body = c'.body) {g : Tuple} :
    sliceU U V c g = sliceU U V c' g := by
  unfold sliceU Finrel.tuples; rw [e]

theorem sliceV_congr {U V : Sol} {c c' : Finrel} (e : c.body = c'.body) {g : Tuple} :
    sliceV U V c g = sliceV U V c' g := by
  unfold sliceV Finrel.tuples; rw [e]

/-- ⋈_sol's members, indexed by their pick pairs. -/
theorem join_candidates_pairs {U V W : Sol} (hj : U.join V = .ok W) :
    W.candidates = (((choices ((joinGroups W.data (gU U V)).map fun _ => U.candidates)).flatMap fun ps =>
      (choices ((joinGroups W.data (gV U V)).map (agreeingV U V W.data ps))).map (ps, ·)).map
      fun pq => glue U V W.data W.heading pq.1 ((joinGroups W.data (gV U V)).zip pq.2)) := by
  rw [join_candidates_picks hj, List.map_flatMap]
  congr 1
  funext ps
  rw [okOptions, choices_tag, List.map_map, List.map_map]
  rfl

/-- **No member twice.** If the members of U, and of V, have no body twice, neither do
the members of U ⋈_sol V. -/
theorem nodup_join {U V W : Sol} (hj : U.join V = .ok W) (MU : U.MembersOk) (MV : V.MembersOk)
    (hU : (U.candidates.map (·.body)).Nodup) (hV : (V.candidates.map (·.body)).Nodup) :
    (W.candidates.map (·.body)).Nodup := by
  rw [join_candidates_pairs hj, List.map_map]
  have hUn : U.candidates.Nodup := nodup_of_map hU
  have hVn : V.candidates.Nodup := nodup_of_map hV
  -- what a pair in the list satisfies
  have facts : ∀ pq ∈ ((choices ((joinGroups W.data (gU U V)).map fun _ => U.candidates)).flatMap fun ps =>
      (choices ((joinGroups W.data (gV U V)).map (agreeingV U V W.data ps))).map (ps, ·)),
      pq.1.length = (joinGroups W.data (gU U V)).length ∧ (∀ m ∈ pq.1, m ∈ U.candidates) ∧
      pq.2.length = (joinGroups W.data (gV U V)).length ∧ (∀ q ∈ pq.2, q ∈ V.candidates) ∧
      (∀ p ∈ (joinGroups W.data (gV U V)).zip pq.2, ∀ t ∈ W.data.tuples,
        t.restrict (gV U V) = p.1 → agreeAt U V W.data pq.1 p.2 t = true) := by
    intro pq hpq
    obtain ⟨ps, hps, hpq'⟩ := List.mem_flatMap.mp hpq
    obtain ⟨qs, hqs, rfl⟩ := List.mem_map.mp hpq'
    obtain ⟨h1, h2⟩ := picks_replicate.mp (mem_choices.mp hps)
    obtain ⟨h3, h4⟩ := picks_map_iff.mp (mem_choices.mp hqs)
    refine ⟨h1, h2, h3, ?_, fun p hp => (mem_agreeingV.mp (h4 p hp)).2⟩
    exact (zip_snd_forall (P := (· ∈ V.candidates)) h3).mp fun p hp => (mem_agreeingV.mp (h4 p hp)).1
  refine nodup_map_on ?_ ?_
  · intro pq hpq pq' hpq' e
    obtain ⟨a1, a2, a3, a4, a5⟩ := facts pq hpq
    obtain ⟨b1, b2, b3, b4, b5⟩ := facts pq' hpq'
    have hvs : ∀ qs : List Finrel, (∀ q ∈ qs, q ∈ V.candidates) →
        ∀ p ∈ (joinGroups W.data (gV U V)).zip qs, p.2 ∈ V.candidates :=
      fun qs h p hp => h p.2 (List.of_mem_zip hp).2
    simp only [Function.comp_def] at e
    have eU : pq.1 = pq'.1 := by
      refine eq_of_lookup_zip (nodup_joinGroups _ _) a1 b1 fun g hg => ?_
      obtain ⟨m, hl, hm⟩ := lookup_zip_of_mem hg a1
      obtain ⟨m', hl', hm'⟩ := lookup_zip_of_mem hg b1
      have s1 := slice_glue_U hj MU MV a1 a2 (hvs _ a4) hg hl
      have s2 := slice_glue_U hj MU MV b1 b2 (hvs _ b4) hg hl'
      rw [sliceU_congr e] at s1
      rw [hl, hl', inj_of_nodup_map hU m (a2 m hm) m' (b2 m' hm') (s1.symm.trans s2)]
    have eV : pq.2 = pq'.2 := by
      refine eq_of_lookup_zip (nodup_joinGroups _ _) a3 b3 fun g hg => ?_
      obtain ⟨q, hl, hq⟩ := lookup_zip_of_mem hg a3
      obtain ⟨q', hl', hq'⟩ := lookup_zip_of_mem hg b3
      have s1 := slice_glue_V hj MU MV a2 a3 a4 a5 hg hl
      have s2 := slice_glue_V hj MU MV b2 b3 b4 b5 hg hl'
      rw [sliceV_congr e] at s1
      rw [hl, hl', inj_of_nodup_map hV q (a4 q hq) q' (b4 q' hq') (s1.symm.trans s2)]
    exact Prod.ext eU eV
  · refine nodup_flatMap_tag (nodup_choices ?_) fun ps _ => nodup_choices ?_
    · intro xs hxs
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hxs
      exact hUn
    · intro xs hxs
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp hxs
      exact hVn.filter _

end SolJoinLaws

end Rasso
