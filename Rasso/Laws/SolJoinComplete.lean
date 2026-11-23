import Rasso.Laws.SolJoinSlices

/-!
# Rasso: membership of ⋈_sol, "←"

-/

namespace Rasso

namespace SolJoinLaws

/-- A tuple of the joined Data is fixed by its U-Data part and its U-group. -/
theorem join_tuple_eq {U V W : Sol} (hj : U.join V = .ok W) (MU : U.MembersOk) (MV : V.MembersOk)
    {t t' : Tuple} (ht : t ∈ W.data.tuples) (ht' : t' ∈ W.data.tuples)
    (hd : t.restrict U.data.attrs = t'.restrict U.data.attrs)
    (hg : t.restrict (gU U V) = t'.restrict (gU U V)) : t = t' := by
  obtain ⟨hs, -, -, hk⟩ := join_data_tuple hj MU MV ht
  obtain ⟨hs', -, -, hk'⟩ := join_data_tuple hj MU MV ht'
  refine Tuple.ext_get? hs hs' fun a => ?_
  by_cases hu : a ∈ U.data.attrs
  · have := congrArg (Tuple.get? · a) hd
    simpa [get?_restrict, hu] using this
  · by_cases hv : a ∈ V.data.attrs
    · have hga : a ∈ gU U V := List.mem_filter.mpr ⟨hv, by simp [hu]⟩
      have := congrArg (Tuple.get? · a) hg
      simpa [get?_restrict, hga] using this
    · have h1 : Tuple.get? t a = none := by
        cases h : Tuple.get? t a with
        | none => rfl
        | some _ => exact ((hk a).mp (by simp [h])).elim (fun x => absurd x hu) (fun x => absurd x hv)
      have h2 : Tuple.get? t' a = none := by
        cases h : Tuple.get? t' a with
        | none => rfl
        | some _ => exact ((hk' a).mp (by simp [h])).elim (fun x => absurd x hu) (fun x => absurd x hv)
      rw [h1, h2]

/-- A tuple of the joined Data is fixed by its V-Data part and its V-group. -/
theorem join_tuple_eq_V {U V W : Sol} (hj : U.join V = .ok W) (MU : U.MembersOk) (MV : V.MembersOk)
    {t t' : Tuple} (ht : t ∈ W.data.tuples) (ht' : t' ∈ W.data.tuples)
    (hd : t.restrict V.data.attrs = t'.restrict V.data.attrs)
    (hg : t.restrict (gV U V) = t'.restrict (gV U V)) : t = t' := by
  obtain ⟨hs, -, -, hk⟩ := join_data_tuple hj MU MV ht
  obtain ⟨hs', -, -, hk'⟩ := join_data_tuple hj MU MV ht'
  refine Tuple.ext_get? hs hs' fun a => ?_
  by_cases hv : a ∈ V.data.attrs
  · have := congrArg (Tuple.get? · a) hd
    simpa [get?_restrict, hv] using this
  · by_cases hu : a ∈ U.data.attrs
    · have hga : a ∈ gV U V := List.mem_filter.mpr ⟨hu, by simp [hv]⟩
      have := congrArg (Tuple.get? · a) hg
      simpa [get?_restrict, hga] using this
    · have h1 : Tuple.get? t a = none := by
        cases h : Tuple.get? t a with
        | none => rfl
        | some _ => exact ((hk a).mp (by simp [h])).elim (fun x => absurd x hu) (fun x => absurd x hv)
      have h2 : Tuple.get? t' a = none := by
        cases h : Tuple.get? t' a with
        | none => rfl
        | some _ => exact ((hk' a).mp (by simp [h])).elim (fun x => absurd x hu) (fun x => absurd x hv)
      rw [h1, h2]

/-- W's Decision attributes are U's and V's. -/
theorem decision_join_attrs {U V W : Sol} (hj : U.join V = .ok W) (a : String) :
    a ∈ W.decision.attrs ↔ a ∈ U.decision.attrs ∨ a ∈ V.decision.attrs := by
  obtain ⟨hJ, dec, hdec, hh⟩ := join_shape hj
  obtain ⟨q1, q2⟩ := join_q2 hj
  have hUx : ∀ a ∈ U.decision.attrs, a ∉ U.data.attrs := fun a ha => (mem_decision_attrs.mp ha).2
  have hVx : ∀ a ∈ V.decision.attrs, a ∉ V.data.attrs := fun a ha => (mem_decision_attrs.mp ha).2
  have hJa : ∀ a, a ∈ W.data.attrs ↔ a ∈ U.data.attrs ∨ a ∈ V.data.attrs := join_heading_attrs hJ
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

/-- Restricting a merge to attributes the right part does not have. -/
theorem restrict_merge_of_none {A : List String} {t x : Tuple} (ht : Tuple.Sorted t) (hx : Tuple.Sorted x)
    (hA : ∀ a ∈ A, Tuple.get? x a = none) : (t.merge x).restrict A = t.restrict A := by
  refine Tuple.ext_get? (sorted_restrict (Tuple.sorted_merge ht hx)) (sorted_restrict ht) fun a => ?_
  rw [get?_restrict, get?_restrict, Tuple.get?_merge ht hx]
  by_cases ha : a ∈ A
  · rw [ite_eq_left ha, ite_eq_left ha, hA a ha, Option.or_none]
  · rw [ite_eq_right ha, ite_eq_right ha]

/-- The restriction of an exact tuple to a sub-list of its attributes is exact over it. -/
theorem exactly_restrict {X Y : List String} {x : Tuple} (hx : Tuple.Exactly X x)
    (hYX : ∀ a ∈ Y, a ∈ X) : Tuple.Exactly Y (x.restrict Y) := by
  have hx' := Tuple.exactly_iff.mp hx
  refine Tuple.exactly_iff.mpr ⟨sorted_restrict hx'.1, fun a => ?_⟩
  rw [get?_restrict]
  by_cases ha : a ∈ Y
  · rw [ite_eq_left ha]; exact ⟨fun _ => ha, fun _ => (hx'.2 a).mpr (hYX a ha)⟩
  · rw [ite_eq_right ha]; simp [ha]

/-- Two tuples agree when they give the same value wherever both give one. -/
theorem agrees_of_get? {x y : Tuple} (hx : Tuple.Sorted x)
    (h : ∀ a v w, Tuple.get? x a = some v → Tuple.get? y a = some w → v = w) : x.agrees y = true := by
  unfold Tuple.agrees
  rw [List.all_eq_true]
  rintro ⟨a, v⟩ hav
  have hv : Tuple.get? x a = some v := lookup_of_mem (Tuple.nodup_keys hx) hav
  simp only
  cases hw : Tuple.get? y a with
  | none => rfl
  | some w => simp [h a v w hv hw]

theorem lookup_zip_map {β : Type} (φ : Tuple → β) {g : Tuple} :
    ∀ {gs : List Tuple}, g ∈ gs → (gs.zip (gs.map φ)).lookup g = some (φ g)
  | [], h => by cases h
  | g' :: gs, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.lookup]
    by_cases e : g = g'
    · subst e; simp
    · have : (g == g') = false := by simp [e]
      rw [this]
      exact lookup_zip_map φ (List.mem_cons.mp h |>.resolve_left e)

theorem mem_zip_map {β : Type} (φ : Tuple → β) {p : Tuple × β} :
    ∀ {gs : List Tuple}, p ∈ gs.zip (gs.map φ) → p.1 ∈ gs ∧ p.2 = φ p.1
  | [], h => by cases h
  | g :: gs, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨List.mem_cons_self, rfl⟩
    · obtain ⟨h1, h2⟩ := mem_zip_map φ h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

section Complete
variable {U V W : Sol} (hj : U.join V = .ok W) (MU : U.MembersOk) (MV : V.MembersOk)
  {F : Tuple → Tuple} (hF : ∀ t ∈ W.data.tuples, Tuple.Exactly W.decision.attrs (F t))
include hj MU MV hF

/-- A member of U whose body is a U-slice of `F`'s graph takes `F`'s U decisions. -/
theorem decisionAt_of_sliceU {m : Finrel} (hm : m ∈ U.candidates)
    {g : Tuple} (hs : m.body = sliceU U V (graph W.heading W.data.tuples F) g)
    {t : Tuple} (ht : t ∈ W.data.tuples) (htg : t.restrict (gU U V) = g) :
    U.decisionAt m (t.restrict U.data.attrs) = some ((F t).restrict U.decision.attrs) := by
  obtain ⟨q1, q2⟩ := join_q2 hj
  obtain ⟨f, hf, hmb⟩ := MU.graph m hm
  obtain ⟨-, htu, -, -⟩ := join_data_tuple hj MU MV ht
  rw [decisionAt_graph MU.dataExact hf hmb htu]
  congr 1
  -- d.merge (f d) is in the slice
  have hin : (t.restrict U.data.attrs).merge (f (t.restrict U.data.attrs)) ∈ m.body.toList := by
    rw [hmb]; exact (mem_graph (h := U.heading) _).mpr ⟨_, htu, rfl⟩
  rw [hs] at hin
  unfold sliceU at hin
  rw [mem_slice] at hin
  obtain ⟨c'', hc'', hcg, he⟩ := hin
  obtain ⟨t', ht', rfl⟩ := (mem_graph _).mp hc''
  obtain ⟨hts', htu', -, hk'⟩ := join_data_tuple hj MU MV ht'
  have hWx := decision_join_attrs hj
  have hFe := Tuple.exactly_iff.mp (hF t' ht')
  have hFn : ∀ a, a ∉ W.decision.attrs → Tuple.get? (F t') a = none := by
    intro a ha
    cases h : Tuple.get? (F t') a with
    | none => rfl
    | some _ => exact absurd ((hFe.2 a).mp (by simp [h])) ha
  have hUx : ∀ a ∈ U.decision.attrs, a ∉ U.data.attrs := fun a ha => (mem_decision_attrs.mp ha).2
  have hVx : ∀ a ∈ V.decision.attrs, a ∉ V.data.attrs := fun a ha => (mem_decision_attrs.mp ha).2
  have hgU : ∀ a ∈ gU U V, a ∈ V.data.attrs ∧ a ∉ U.data.attrs := by
    intro a ha
    obtain ⟨h1, h2⟩ := List.mem_filter.mp ha
    refine ⟨h1, fun hin => ?_⟩
    rw [List.contains_iff_mem.mpr hin] at h2; cases h2
  -- the group of t' is g
  have hg' : t'.restrict (gU U V) = g := by
    rw [← hcg, restrict_merge_of_none hts' hFe.1]
    intro a ha
    apply hFn
    intro hw
    rcases (hWx a).mp hw with h | h
    · exact q2 a (hgU a ha).1 h
    · exact hVx a h (hgU a ha).1
  -- the slice tuple is (t'|Ud).merge ((F t')|Ux)
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
  have hxe : Tuple.Exactly U.decision.attrs ((F t').restrict U.decision.attrs) :=
    exactly_restrict (hF t' ht') fun a ha => (hWx a).mpr (.inl ha)
  have hslice : (t'.merge (F t')).restrict U.heading.attrs =
      (t'.restrict U.data.attrs).merge ((F t').restrict U.decision.attrs) := by
    have hxs := (Tuple.exactly_iff.mp hxe).1
    refine Tuple.ext_get? (sorted_restrict (Tuple.sorted_merge hts' hFe.1))
      (Tuple.sorted_merge (sorted_restrict hts') hxs) fun a => ?_
    rw [get?_restrict, Tuple.get?_merge hts' hFe.1, Tuple.get?_merge (sorted_restrict hts') hxs,
      get?_restrict, get?_restrict]
    by_cases hd : a ∈ U.data.attrs
    · have hFa : Tuple.get? (F t') a = none := hFn a fun hw => by
        rcases (hWx a).mp hw with h | h
        · exact hUx a h hd
        · exact q1 a hd h
      rw [ite_eq_left ((hUh a).mpr (.inl hd)), ite_eq_left hd, ite_eq_right (fun h => hUx a h hd), hFa]
    · by_cases hx : a ∈ U.decision.attrs
      · have hta : Tuple.get? t' a = none := by
          cases h : Tuple.get? t' a with
          | none => rfl
          | some _ =>
            rcases (hk' a).mp (by simp [h]) with h1 | h1
            · exact absurd h1 hd
            · exact absurd hx (q2 a h1)
        rw [ite_eq_left ((hUh a).mpr (.inr hx)), ite_eq_right hd, ite_eq_left hx, hta]
      · rw [ite_eq_right (fun h => ((hUh a).mp h).elim hd hx), ite_eq_right hd, ite_eq_right hx]; rfl
  rw [hslice] at he
  have hde := MU.dataExact _ htu'
  have hde0 := MU.dataExact _ htu
  have e1 : ((t.restrict U.data.attrs).merge (f (t.restrict U.data.attrs))).restrict U.data.attrs =
      ((t'.restrict U.data.attrs).merge ((F t').restrict U.decision.attrs)).restrict U.data.attrs := by
    rw [he]
  rw [Tuple.restrict_merge_left hde0 (Tuple.exactly_iff.mp (hf _ htu)).1,
    Tuple.restrict_merge_left hde (Tuple.exactly_iff.mp hxe).1] at e1
  have htt : t = t' := join_tuple_eq hj MU MV ht ht' e1 (htg.trans hg'.symm)
  subst htt
  have hnone : ∀ (d : Tuple), Tuple.Exactly U.data.attrs d → ∀ a ∈ U.decision.attrs, Tuple.get? d a = none :=
    fun d hd a ha => Tuple.get?_eq_none_of_over hd.1 (hUx a ha)
  have e2 : ((t.restrict U.data.attrs).merge (f (t.restrict U.data.attrs))).restrict U.decision.attrs =
      ((t.restrict U.data.attrs).merge ((F t).restrict U.decision.attrs)).restrict U.decision.attrs := by
    rw [he]
  rw [Tuple.restrict_merge_right hde0.1.1 (hnone _ hde0) (hf _ htu),
    Tuple.restrict_merge_right hde.1.1 (hnone _ hde) hxe] at e2
  exact e2

/-- A member of V whose body is a V-slice of `F`'s graph takes `F`'s V decisions. -/
theorem decisionAt_of_sliceV {m : Finrel} (hm : m ∈ V.candidates)
    {g : Tuple} (hs : m.body = sliceV U V (graph W.heading W.data.tuples F) g)
    {t : Tuple} (ht : t ∈ W.data.tuples) (htg : t.restrict (gV U V) = g) :
    V.decisionAt m (t.restrict V.data.attrs) = some ((F t).restrict V.decision.attrs) := by
  obtain ⟨q1, q2⟩ := join_q2 hj
  obtain ⟨f, hf, hmb⟩ := MV.graph m hm
  obtain ⟨-, -, htu, -⟩ := join_data_tuple hj MU MV ht
  rw [decisionAt_graph MV.dataExact hf hmb htu]
  congr 1
  -- d.merge (f d) is in the slice
  have hin : (t.restrict V.data.attrs).merge (f (t.restrict V.data.attrs)) ∈ m.body.toList := by
    rw [hmb]; exact (mem_graph (h := V.heading) _).mpr ⟨_, htu, rfl⟩
  rw [hs] at hin
  unfold sliceV at hin
  rw [mem_slice] at hin
  obtain ⟨c'', hc'', hcg, he⟩ := hin
  obtain ⟨t', ht', rfl⟩ := (mem_graph _).mp hc''
  obtain ⟨hts', -, htu', hk'⟩ := join_data_tuple hj MU MV ht'
  have hWx := decision_join_attrs hj
  have hFe := Tuple.exactly_iff.mp (hF t' ht')
  have hFn : ∀ a, a ∉ W.decision.attrs → Tuple.get? (F t') a = none := by
    intro a ha
    cases h : Tuple.get? (F t') a with
    | none => rfl
    | some _ => exact absurd ((hFe.2 a).mp (by simp [h])) ha
  have hVx : ∀ a ∈ V.decision.attrs, a ∉ V.data.attrs := fun a ha => (mem_decision_attrs.mp ha).2
  have hUx : ∀ a ∈ U.decision.attrs, a ∉ U.data.attrs := fun a ha => (mem_decision_attrs.mp ha).2
  have hgV : ∀ a ∈ gV U V, a ∈ U.data.attrs ∧ a ∉ V.data.attrs := by
    intro a ha
    obtain ⟨h1, h2⟩ := List.mem_filter.mp ha
    refine ⟨h1, fun hin => ?_⟩
    rw [List.contains_iff_mem.mpr hin] at h2; cases h2
  -- the group of t' is g
  have hg' : t'.restrict (gV U V) = g := by
    rw [← hcg, restrict_merge_of_none hts' hFe.1]
    intro a ha
    apply hFn
    intro hw
    rcases (hWx a).mp hw with h | h
    · exact hUx a h (hgV a ha).1
    · exact q1 a (hgV a ha).1 h
  -- the slice tuple is (t'|Ud).merge ((F t')|Ux)
  have hUh : ∀ a, a ∈ V.heading.attrs ↔ a ∈ V.data.attrs ∨ a ∈ V.decision.attrs := by
    intro a
    constructor
    · intro ha
      by_cases hd : a ∈ V.data.attrs
      · exact .inl hd
      · exact .inr (mem_decision_attrs.mpr ⟨ha, hd⟩)
    · rintro (ha | ha)
      · exact MV.dataAttrs a ha
      · exact (mem_decision_attrs.mp ha).1
  have hxe : Tuple.Exactly V.decision.attrs ((F t').restrict V.decision.attrs) :=
    exactly_restrict (hF t' ht') fun a ha => (hWx a).mpr (.inr ha)
  have hslice : (t'.merge (F t')).restrict V.heading.attrs =
      (t'.restrict V.data.attrs).merge ((F t').restrict V.decision.attrs) := by
    have hxs := (Tuple.exactly_iff.mp hxe).1
    refine Tuple.ext_get? (sorted_restrict (Tuple.sorted_merge hts' hFe.1))
      (Tuple.sorted_merge (sorted_restrict hts') hxs) fun a => ?_
    rw [get?_restrict, Tuple.get?_merge hts' hFe.1, Tuple.get?_merge (sorted_restrict hts') hxs,
      get?_restrict, get?_restrict]
    by_cases hd : a ∈ V.data.attrs
    · have hFa : Tuple.get? (F t') a = none := hFn a fun hw => by
        rcases (hWx a).mp hw with h | h
        · exact q2 a hd h
        · exact hVx a h hd
      rw [ite_eq_left ((hUh a).mpr (.inl hd)), ite_eq_left hd, ite_eq_right (fun h => hVx a h hd), hFa]
    · by_cases hx : a ∈ V.decision.attrs
      · have hta : Tuple.get? t' a = none := by
          cases h : Tuple.get? t' a with
          | none => rfl
          | some _ =>
            rcases (hk' a).mp (by simp [h]) with h1 | h1
            · exact absurd hx (q1 a h1)
            · exact absurd h1 hd
        rw [ite_eq_left ((hUh a).mpr (.inr hx)), ite_eq_right hd, ite_eq_left hx, hta]
      · rw [ite_eq_right (fun h => ((hUh a).mp h).elim hd hx), ite_eq_right hd, ite_eq_right hx]; rfl
  rw [hslice] at he
  have hde := MV.dataExact _ htu'
  have hde0 := MV.dataExact _ htu
  have e1 : ((t.restrict V.data.attrs).merge (f (t.restrict V.data.attrs))).restrict V.data.attrs =
      ((t'.restrict V.data.attrs).merge ((F t').restrict V.decision.attrs)).restrict V.data.attrs := by
    rw [he]
  rw [Tuple.restrict_merge_left hde0 (Tuple.exactly_iff.mp (hf _ htu)).1,
    Tuple.restrict_merge_left hde (Tuple.exactly_iff.mp hxe).1] at e1
  have htt : t = t' := join_tuple_eq_V hj MU MV ht ht' e1 (htg.trans hg'.symm)
  subst htt
  have hnone : ∀ (d : Tuple), Tuple.Exactly V.data.attrs d → ∀ a ∈ V.decision.attrs, Tuple.get? d a = none :=
    fun d hd a ha => Tuple.get?_eq_none_of_over hd.1 (hVx a ha)
  have e2 : ((t.restrict V.data.attrs).merge (f (t.restrict V.data.attrs))).restrict V.decision.attrs =
      ((t.restrict V.data.attrs).merge ((F t).restrict V.decision.attrs)).restrict V.decision.attrs := by
    rw [he]
  rw [Tuple.restrict_merge_right hde0.1.1 (hnone _ hde0) (hf _ htu),
    Tuple.restrict_merge_right hde.1.1 (hnone _ hde) hxe] at e2
  exact e2

/-- **Membership, "←".** A function on the joined Data whose values have exactly W's
Decision attributes, and whose U-slices and V-slices are members of U and V (by body),
is a member of U ⋈_sol V (by body). -/
theorem mem_join_complete
    (hU : ∀ g ∈ joinGroups W.data (gU U V), ∃ m ∈ U.candidates,
      m.body = sliceU U V (graph W.heading W.data.tuples F) g)
    (hV : ∀ g ∈ joinGroups W.data (gV U V), ∃ q ∈ V.candidates,
      q.body = sliceV U V (graph W.heading W.data.tuples F) g) :
    ∃ c ∈ W.candidates, c.body = (graph W.heading W.data.tuples F).body := by
  classical
  let c' := graph W.heading W.data.tuples F
  let φU : Tuple → Finrel := fun g =>
    if h : ∃ m ∈ U.candidates, m.body = sliceU U V c' g then Classical.choose h else default
  let φV : Tuple → Finrel := fun g =>
    if h : ∃ q ∈ V.candidates, q.body = sliceV U V c' g then Classical.choose h else default
  have specU : ∀ g ∈ joinGroups W.data (gU U V), φU g ∈ U.candidates ∧ (φU g).body = sliceU U V c' g := by
    intro g hg
    have h : ∃ m ∈ U.candidates, m.body = sliceU U V c' g := hU g hg
    simp only [φU]; rw [dite_eq_left h]
    exact Classical.choose_spec h
  have specV : ∀ g ∈ joinGroups W.data (gV U V), φV g ∈ V.candidates ∧ (φV g).body = sliceV U V c' g := by
    intro g hg
    have h : ∃ q ∈ V.candidates, q.body = sliceV U V c' g := hV g hg
    simp only [φV]; rw [dite_eq_left h]
    exact Classical.choose_spec h
  let ps := (joinGroups W.data (gU U V)).map φU
  let qs := (joinGroups W.data (gV U V)).map φV
  -- the pure decisions at a J tuple
  have hx : ∀ t ∈ W.data.tuples, pdU U V W.data ps t = some ((F t).restrict U.decision.attrs) := by
    intro t ht
    have hg := mem_joinGroups (G := gU U V) ht
    simp only [pdU, ps, lookup_zip_map φU hg, Option.bind_some]
    exact decisionAt_of_sliceU hj MU MV hF (specU _ hg).1 (specU _ hg).2 ht rfl
  have hy : ∀ t ∈ W.data.tuples, ∀ q, ((joinGroups W.data (gV U V)).zip qs).lookup (t.restrict (gV U V)) = some q →
      pdV1 V q t = some ((F t).restrict V.decision.attrs) := by
    intro t ht q hl
    have hg := mem_joinGroups (G := gV U V) ht
    rw [lookup_zip_map φV hg] at hl
    cases hl
    exact decisionAt_of_sliceV hj MU MV hF (specV _ hg).1 (specV _ hg).2 ht rfl
  have hWx := decision_join_attrs hj
  have hag : ∀ t ∈ W.data.tuples,
      ((F t).restrict U.decision.attrs).agrees ((F t).restrict V.decision.attrs) = true := by
    intro t ht
    have hs := (Tuple.exactly_iff.mp (hF t ht)).1
    refine agrees_of_get? (sorted_restrict hs) fun a v w h1 h2 => ?_
    rw [get?_restrict] at h1 h2
    split at h1
    · split at h2
      · rw [h1] at h2; cases h2; rfl
      · cases h2
    · cases h1
  refine ⟨glue U V W.data W.heading ps ((joinGroups W.data (gV U V)).zip qs), ?_, ?_⟩
  · refine (mem_join_picks hj).mpr ⟨ps, qs, by simp [ps], ?_, by simp [qs], ?_, rfl⟩
    · intro m hm
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
      exact (specU g hg).1
    · intro p hp
      obtain ⟨hp1, hp2⟩ := mem_zip_map φV hp
      refine ⟨hp2 ▸ (specV _ hp1).1, fun t ht htg => ?_⟩
      have hl : ((joinGroups W.data (gV U V)).zip qs).lookup (t.restrict (gV U V)) = some p.2 := by
        rw [htg, hp2]; exact lookup_zip_map φV hp1
      unfold agreeAt
      rw [hx t ht, hy t ht p.2 hl]
      exact hag t ht
  · unfold glue graph
    congr 2
    apply List.map_congr_left
    intro t ht
    have hts := (join_data_tuple hj MU MV ht).1
    have hFe := Tuple.exactly_iff.mp (hF t ht)
    have hfind : ((((joinGroups W.data (gV U V)).zip qs).find? (·.1 == t.restrict (gV U V))).bind
        fun p => pdV1 V p.2 t) = some ((F t).restrict V.decision.attrs) := by
      have e := find?_fst_eq_lookup (l := (joinGroups W.data (gV U V)).zip qs) (k := t.restrict (gV U V))
      have hg := mem_joinGroups (G := gV U V) ht
      have hl : ((joinGroups W.data (gV U V)).zip qs).lookup (t.restrict (gV U V)) = some (φV (t.restrict (gV U V))) :=
        lookup_zip_map φV hg
      rw [hl] at e
      cases hf2 : ((joinGroups W.data (gV U V)).zip qs).find? (·.1 == t.restrict (gV U V)) with
      | none => rw [hf2] at e; cases e
      | some p =>
        rw [hf2] at e
        simp only [Option.map_some, Option.some.injEq] at e
        rw [Option.bind_some, e]
        exact hy t ht _ hl
    rw [hx t ht, hfind, Option.getD_some, Option.getD_some]
    refine Tuple.ext_get? (sorted_glued hts (sorted_restrict hFe.1) (sorted_restrict hFe.1))
      (Tuple.sorted_merge hts hFe.1) fun a => ?_
    rw [get?_glued hts (sorted_restrict hFe.1) (sorted_restrict hFe.1), Tuple.get?_merge hts hFe.1,
      get?_restrict, get?_restrict]
    cases Tuple.get? t a with
    | some v => rfl
    | none =>
      simp only [Option.none_or]
      by_cases hu : a ∈ U.decision.attrs
      · rw [ite_eq_left hu]
        cases Tuple.get? (F t) a with
        | none => split <;> rfl
        | some v => rfl
      · rw [ite_eq_right hu, Option.none_or]
        by_cases hv : a ∈ V.decision.attrs
        · rw [ite_eq_left hv]
        · rw [ite_eq_right hv]
          cases h : Tuple.get? (F t) a with
          | none => rfl
          | some _ =>
            exact ((hWx a).mp ((hFe.2 a).mp (by simp [h]))).elim (fun x => absurd x hu) (fun x => absurd x hv)

/-- **Membership.** A function on the joined Data, with values exactly over W's Decision,
is a member of U ⋈_sol V (by body) exactly when each of its U-slices is a member of U and
each of its V-slices a member of V (by body). -/
theorem mem_join :
    (∃ c ∈ W.candidates, c.body = (graph W.heading W.data.tuples F).body) ↔
      (∀ g ∈ joinGroups W.data (gU U V), ∃ m ∈ U.candidates,
        m.body = sliceU U V (graph W.heading W.data.tuples F) g) ∧
      (∀ g ∈ joinGroups W.data (gV U V), ∃ q ∈ V.candidates,
        q.body = sliceV U V (graph W.heading W.data.tuples F) g) := by
  constructor
  · rintro ⟨c, hc, hb⟩
    obtain ⟨h1, h2⟩ := mem_join_sound hj MU MV hc
    exact ⟨fun g hg => by rw [← sliceU_congr hb]; exact h1 g hg,
      fun g hg => by rw [← sliceV_congr hb]; exact h2 g hg⟩
  · rintro ⟨h1, h2⟩
    exact mem_join_complete hj MU MV hF h1 h2

end Complete

end SolJoinLaws
end Rasso
