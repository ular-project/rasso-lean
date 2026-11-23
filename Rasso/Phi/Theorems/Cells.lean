import Rasso.Phi.Theorems.Square

/-!
# φ's theorems: completeness of the cells (C)

For φ's result `F` on a solution set `ω_sol[Data, Decision]` filtered by conditions: the
assignments that give every cell a value in its domain, and on which the Decision's term
holds on every copy, are mapped by `substitute F` onto the candidates of `ω_sol[Data,
Decision]` (`omegaSolCandidates`), and two assignments over exactly the cells give the same
candidate only if they are equal.
-/

namespace Rasso.Phi

open Rasso

variable {nm : String → Nat → String}

/-- The converse of `Domain.values?_sound`: a listed value is in the domain. -/
theorem Domain.values?_complete {d : Domain} {vs : List Value} (h : d.values? = some vs)
    {v : Value} (hv : v ∈ vs) : d.mem v = true := by
  match d with
  | .kind .bool =>
    simp only [Domain.values?, Option.some.injEq] at h; subst h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> rfl
  | .kind .int | .kind .symbol | .kind .string | .kind .float | .kind .rat =>
    simp [Domain.values?] at h
  | .range lo hi =>
    simp only [Domain.values?, Option.some.injEq] at h; subst h
    simp only [List.mem_map, List.mem_range] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    simp only [Domain.mem, Bool.and_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast]
    omega
  | .set ws =>
    simp only [Domain.values?, Option.some.injEq] at h; subst h
    simp only [Domain.mem, List.contains_iff_mem]
    exact List.mem_mergeSort.mp hv

/-! ## The copy number of a Data tuple -/

theorem find_fst {α β : Type} [DecidableEq α] {t : α} {i : β} : ∀ {L : List (α × β)},
    (L.map Prod.fst).Nodup → (t, i) ∈ L → L.find? (fun p => decide (p.1 = t)) = some (t, i)
  | [], _, h => by simp at h
  | (t', i') :: L, hn, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp h with e | h
    · cases e; simp
    · have : t' ≠ t := fun e => hn.1 ⟨(t, i), h, e.symm⟩
      simp only [List.find?_cons, this, decide_false]
      exact find_fst hn.2 h

/-- The copy number φ gave the Data tuple `t` (0 if none). -/
def copyOf (rows : List Tuple) (t : Tuple) : Nat :=
  (((rows.zip (phiIdx rows.length)).find? fun p => decide (p.1 = t)).map (·.2)).getD 0

theorem copyOf_eq {rows : List Tuple} (hn : rows.Nodup) {t : Tuple} {i : Nat}
    (h : (t, i) ∈ rows.zip (phiIdx rows.length)) : copyOf rows t = i := by
  have hm : ((rows.zip (phiIdx rows.length)).map Prod.fst).Nodup := by
    rw [List.map_fst_zip (by simp [phiIdx])]; exact hn
  simp [copyOf, find_fst hm h]

theorem exists_copy {rows : List Tuple} {t : Tuple} (ht : t ∈ rows) :
    ∃ i, (t, i) ∈ rows.zip (phiIdx rows.length) := by
  have : t ∈ (rows.zip (phiIdx rows.length)).map Prod.fst := by
    rw [List.map_fst_zip (by simp [phiIdx])]; exact ht
  obtain ⟨⟨t', i⟩, h, rfl⟩ := List.mem_map.mp this
  exact ⟨i, h⟩

/-! ## The candidate as a graph -/

theorem nodup_split {dh uh : Heading} (hnd : (dh ++ uh).attrs.Nodup) :
    dh.attrs.Nodup ∧ uh.attrs.Nodup ∧ ∀ a ∈ dh.attrs, a ∉ uh.attrs := by
  simp only [Heading.attrs, List.map_append] at hnd
  obtain ⟨h1, h2, h3⟩ := List.nodup_append.mp hnd
  exact ⟨h1, h2, fun a ha hb => h3 a ha a hb rfl⟩

theorem substRow_merge {dh uh : Heading} (hnd : (dh ++ uh).attrs.Nodup) {x t : Tuple} {i : Nat}
    (hfit : t = fitTuple dh t) :
    substRow x (dPart dh t ++ uPart nm uh i) = t.merge (decOf nm x uh i) := by
  obtain ⟨hdn, hun, hdis⟩ := nodup_split hnd
  have hk : (((dPart dh t ++ uPart nm uh i).map fun p => (p.1, substVal x p.2)).map (·.1)).Nodup := by
    rw [List.map_map]; simpa [Function.comp_def, ← row_keys (nm := nm) dh uh t i] using hnd
  have hdk : ((dh.map fun p => (p.1, (t.get? p.1).getD default)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def, Heading.attrs] using hdn
  have hdec : ((uh.map fun q => (q.1, (x.get? (nm q.1 i)).getD default)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def, Heading.attrs] using hun
  -- `t`'s pairs are its Data pairs
  have htm : ∀ p, p ∈ t ↔ p ∈ dh.map fun q => (q.1, (t.get? q.1).getD default) := by
    intro p
    conv => lhs; rw [hfit]
    simp only [fitTuple, mem_ofPairs]
  have hkey : ∀ p ∈ t, p.1 ∈ dh.attrs := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((htm p).mp hp)
    exact List.mem_map_of_mem hq
  have hdecm : ∀ p, p ∈ decOf nm x uh i ↔ p ∈ uh.map fun q => (q.1, (x.get? (nm q.1 i)).getD default) := by
    intro p; simp [decOf]
  have hmk : ((t ++ (decOf nm x uh i).filter fun p => (t.get? p.1).isNone).map (·.1)).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [hfit]; exact ((List.mergeSort_perm _ _).map _).nodup_iff.mpr hdk
    · apply List.Nodup.sublist (List.filter_sublist.map _)
      exact ((List.mergeSort_perm _ _).map _).nodup_iff.mpr hdec
    · intro a ha b hb e
      subst e
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      obtain ⟨q, hq, e⟩ := List.mem_map.mp hb
      have hq' := (hdecm q).mp (List.mem_filter.mp hq).1
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq'
      exact hdis _ (hkey p hp) (e ▸ List.mem_map_of_mem hr)
  rw [Tuple.merge, substRow]
  apply ofPairs_eq hk hmk
  intro ⟨a, v⟩
  simp only [List.mem_append, List.mem_map, dPart, uPart, List.mem_filter, htm, hdecm]
  constructor
  · rintro ⟨q, hq | hq, e⟩
    · obtain ⟨r, hr, rfl⟩ := hq
      exact .inl ⟨r, hr, e⟩
    · obtain ⟨r, hr, rfl⟩ := hq
      refine .inr ⟨⟨r, hr, e⟩, ?_⟩
      simp only [Prod.mk.injEq] at e
      rw [← e.1]
      cases hg : t.get? r.1 with
      | none => rfl
      | some w =>
        exact absurd (hkey _ (lookup_some_mem hg)) (fun h => hdis _ h (List.mem_map_of_mem hr))
  · rintro (⟨r, hr, e⟩ | ⟨⟨r, hr, e⟩, -⟩)
    · exact ⟨_, .inl ⟨r, hr, rfl⟩, e⟩
    · exact ⟨_, .inr ⟨r, hr, rfl⟩, e⟩

theorem ofTuples_congr {h : Heading} {l l' : List Tuple} (hm : ∀ t, t ∈ l ↔ t ∈ l') :
    Finrel.ofTuples h l = Finrel.ofTuples h l' := by
  unfold Finrel.ofTuples
  congr 1
  exact Body.ext fun t => by rw [Body.mem_toList_ofList, Body.mem_toList_ofList, hm]

theorem over_fit {dh : Heading} (hn : dh.attrs.Nodup) {t : Tuple} (ht : t = fitTuple dh t) :
    Tuple.Over dh.attrs t := by
  have hk : ((dh.map fun p => (p.1, (t.get? p.1).getD default)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def, Heading.attrs] using hn
  rw [ht]
  refine ⟨Tuple.sorted_ofPairs hk, fun q hq => ?_⟩
  simp only [fitTuple, mem_ofPairs, List.mem_map] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  exact List.mem_map_of_mem hr

theorem over_decOf {uh : Heading} (hn : uh.attrs.Nodup) (x : Tuple) (i : Nat) :
    Tuple.Over uh.attrs (decOf nm x uh i) := by
  have hk : ((uh.map fun q => (q.1, (x.get? (nm q.1 i)).getD default)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def, Heading.attrs] using hn
  refine ⟨Tuple.sorted_ofPairs hk, fun q hq => ?_⟩
  simp only [decOf, mem_ofPairs, List.mem_map] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  exact List.mem_map_of_mem hr

theorem mem_rows {data : Finrel} {t : Tuple} : t ∈ phiRows data ↔ t ∈ data.tuples := List.mem_mergeSort

theorem rows_nodup (data : Finrel) : (phiRows data).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finrel.nodup_tuples data)

/-- `substitute F x` is the graph of the function that sends each Data tuple to its copy's
Decision tuple under `x`. -/
theorem substitute_graph {p : Program} {ch : Chain} {F : Flat} (R : PhiOfRun nm p ch F) (x : Tuple) :
    substitute F x = graph F.heading R.data.tuples
      (fun t => decOf nm x R.u.heading (copyOf (phiRows R.data) t)) := by
  obtain ⟨data, u, picks, kinds, conds, hom, hnd, hfit, hcn, hkinds, hattrs, hconds, rfl⟩ := R
  dsimp only
  rw [substitute_eq, graph]
  apply ofTuples_congr
  intro m
  simp only [List.mem_map]
  constructor
  · rintro ⟨row, hr, rfl⟩
    obtain ⟨t, i, hti, rfl⟩ := mem_phiSymI.mp hr
    have ht := mem_rows.mp (List.of_mem_zip hti).1
    refine ⟨t, ht, ?_⟩
    rw [substRow_merge hnd (hfit t ht), copyOf_eq (rows_nodup data) hti]
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨i, hti⟩ := exists_copy (mem_rows.mpr ht)
    refine ⟨_, mem_phiSymI.mpr ⟨t, i, hti, rfl⟩, ?_⟩
    rw [substRow_merge hnd (hfit t ht), copyOf_eq (rows_nodup data) hti]

theorem picks_spec {p : Program} {ch : Chain} {data : Finrel} {u : Unrel} {picks : List Tuple}
    (hom : omegaOf p ch = .ok (data, u, picks)) :
    ∃ as, Unrel.assignments u.heading = .ok as ∧ ∀ t, t ∈ picks ↔ t ∈ as ∧ u.term.holds t = .ok true := by
  obtain ⟨_, _, _, _, _, hpicks⟩ := omegaOf_spec hom
  cases ha : Unrel.assignments u.heading with
  | error e => simp [Unrel.tuples, ha, bind, Except.bind] at hpicks
  | ok as =>
    simp only [Unrel.tuples, ha, bind, Except.bind] at hpicks
    exact ⟨as, rfl, mem_filterM hpicks⟩

theorem idx_copy {rows : List Tuple} {i : Nat} (hi : i ∈ phiIdx rows.length) :
    ∃ t, (t, i) ∈ rows.zip (phiIdx rows.length) := by
  have hs : i ∈ (rows.zip (phiIdx rows.length)).map Prod.snd := by
    rw [List.map_snd_zip (by simp [phiIdx])]; exact hi
  obtain ⟨⟨t, i'⟩, hti, rfl⟩ := List.mem_map.mp hs
  exact ⟨t, hti⟩

/-- **Theorem C, into (as an iff).** For an assignment that gives every cell a value in its
domain, the candidate it gives is one of ω_sol's exactly when the Decision's term holds on
every copy. -/
theorem phi_cells_into {p : Program} {ch : Chain} {F : Flat} (R : PhiOfRun nm p ch F) {x : Tuple}
    (hx : FitsCells F.cells x) :
    substitute F x ∈ omegaSolCandidates F.heading R.data.tuples R.picks ↔
      ∀ i ∈ phiIdx (phiRows R.data).length, R.u.term.holds (decOf nm x R.u.heading i) = .ok true := by
  have hg := substitute_graph R x
  obtain ⟨data, u, picks, kinds, conds, hom, hnd, hfit, hcn, hkinds, hattrs, hconds, rfl⟩ := R
  dsimp only at hg hx ⊢
  obtain ⟨hdn, hun, hdis⟩ := nodup_split hnd
  obtain ⟨as, has, hpk⟩ := picks_spec hom
  rw [hg, mem_omegaSolCandidates (Finrel.nodup_tuples data)]
  constructor
  · rintro ⟨g, hgp, e⟩ i hi
    have hfg := graph_inj hdis (fun t ht => over_fit hdn (hfit t ht))
      (fun t _ => over_decOf hun x _)
      (fun t ht => by
        obtain ⟨ps, hps, e⟩ := (Unrel.mem_assignments has _).mp ((hpk _).mp (hgp t ht)).1
        rw [e]; exact hps.over hun) e
    obtain ⟨t, hti⟩ := idx_copy hi
    have ht := mem_rows.mp (List.of_mem_zip hti).1
    have := hfg t ht
    rw [copyOf_eq (rows_nodup data) hti] at this
    rw [this]
    exact ((hpk _).mp (hgp t ht)).2
  · intro hall
    refine ⟨_, fun t ht => ?_, rfl⟩
    obtain ⟨i, hti⟩ := exists_copy (mem_rows.mpr ht)
    rw [copyOf_eq (rows_nodup data) hti]
    have hi := (List.of_mem_zip hti).2
    exact (hpk _).mpr ⟨decOf_mem hun hcn hkinds hx hi has, hall i hi⟩

theorem of_mem_phiCells {uh : Heading} {n : Nat} {c : String} {d : Domain} (h : (c, d) ∈ phiCells nm uh n) :
    ∃ a i, (a, d) ∈ uh ∧ i ∈ phiIdx n ∧ c = nm a i := by
  simp only [phiCells, List.mem_flatMap, List.mem_map] at h
  obtain ⟨i, hi, ⟨a, d'⟩, ha, e⟩ := h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨a, i, ha, hi, rfl⟩

theorem get_none_of_over {as : List String} {t : Tuple} (ht : Tuple.Over as t) {a : String}
    (ha : a ∉ as) : t.get? a = none := by
  cases hg : t.get? a with
  | none => rfl
  | some v => exact absurd (ht.2 _ (lookup_some_mem hg)) ha

theorem fits_mem {h : Heading} {ps : List (String × Value)} (hf : Fits h ps) {a : String} {d : Domain}
    (ha : (a, d) ∈ h) : ∃ vs v, d.values? = some vs ∧ v ∈ vs ∧ (a, v) ∈ ps := by
  induction hf with
  | nil => simp at ha
  | cons hvs hv _ ih =>
    rcases List.mem_cons.mp ha with e | ha
    · cases e; exact ⟨_, _, hvs, hv, List.mem_cons_self⟩
    · obtain ⟨vs, v, h1, h2, h3⟩ := ih ha
      exact ⟨vs, v, h1, h2, List.mem_cons_of_mem _ h3⟩

/-- A pick gives each Decision attribute a value from its domain. -/
theorem pick_get {uh : Heading} (hun : uh.attrs.Nodup) {as : List Tuple}
    (has : Unrel.assignments uh = .ok as) {t : Tuple} (ht : t ∈ as) {a : String} {d : Domain}
    (ha : (a, d) ∈ uh) : ∃ v, t.get? a = some v ∧ d.mem v = true := by
  obtain ⟨ps, hps, rfl⟩ := (Unrel.mem_assignments has t).mp ht
  obtain ⟨vs, v, h1, h2, h3⟩ := fits_mem hps ha
  have hk : (ps.reverse.map (·.1)).Nodup := by
    rw [List.map_reverse, hps.keys]; exact (List.reverse_perm _).nodup_iff.mpr hun
  refine ⟨v, ?_, Domain.values?_complete h1 h2⟩
  rw [Tuple.get?_ofPairs hk]
  exact lookup_of_mem_nodup hk (List.mem_reverse.mpr h3)

theorem graph_congr {h : Heading} {rows : List Tuple} {f g : Tuple → Tuple} (e : ∀ t ∈ rows, f t = g t) :
    graph h rows f = graph h rows g := by
  unfold graph
  rw [List.map_congr_left fun t ht => by rw [e t ht]]

/-- **Theorem C, onto.** Every candidate of ω_sol is the candidate of some assignment over
exactly the cells that gives every cell a value in its domain. -/
theorem phi_cells_onto {p : Program} {ch : Chain} {F : Flat} (R : PhiOfRun nm p ch F) {c : Finrel}
    (hc : c ∈ omegaSolCandidates F.heading R.data.tuples R.picks) :
    ∃ x, FitsCells F.cells x ∧ Tuple.Over F.cells.attrs x ∧ substitute F x = c := by
  have hg := substitute_graph R
  obtain ⟨data, u, picks, kinds, conds, hom, hnd, hfit, hcn, hkinds, hattrs, hconds, rfl⟩ := R
  dsimp only at hg hc ⊢
  obtain ⟨hdn, hun, hdis⟩ := nodup_split hnd
  obtain ⟨as, has, hpk⟩ := picks_spec hom
  obtain ⟨f, hfp, rfl⟩ := (mem_omegaSolCandidates (Finrel.nodup_tuples data) c).mp hc
  let rows := phiRows data
  let xs : List (String × Value) := (rows.zip (phiIdx rows.length)).flatMap fun ti =>
    u.heading.map fun q => (nm q.1 ti.2, ((f ti.1).get? q.1).getD default)
  have hkeys : xs.map (·.1) = (phiCells nm u.heading rows.length).attrs := by
    simp only [xs, phiCells, Heading.attrs, List.map_flatMap, List.map_map, Function.comp_def]
    rw [← List.flatMap_map (f := Prod.snd) (g := fun i => u.heading.map fun q => nm q.1 i)]
    rw [List.map_snd_zip (by simp [phiIdx])]
  have hxk : (xs.map (·.1)).Nodup := by rw [hkeys]; exact hcn
  have hxget : ∀ t i, (t, i) ∈ rows.zip (phiIdx rows.length) → ∀ q ∈ u.heading,
      (Tuple.ofPairs xs).get? (nm q.1 i) = some (((f t).get? q.1).getD default) := by
    intro t i hti q hq
    rw [Tuple.get?_ofPairs hxk]
    apply lookup_of_mem_nodup hxk
    simp only [xs, List.mem_flatMap, List.mem_map]
    exact ⟨(t, i), hti, q, hq, rfl⟩
  have hfit_t : ∀ t ∈ data.tuples, ∀ q ∈ u.heading, ∃ v, (f t).get? q.1 = some v ∧ q.2.mem v = true :=
    fun t ht q hq => pick_get hun has ((hpk _).mp (hfp t ht)).1 (show (q.1, q.2) ∈ u.heading from hq)
  refine ⟨Tuple.ofPairs xs, ?_, ⟨Tuple.sorted_ofPairs hxk, fun q hq => ?_⟩, ?_⟩
  · intro c d hcd
    obtain ⟨a, i, ha, hi, rfl⟩ := of_mem_phiCells (lookup_some_mem hcd)
    obtain ⟨t, hti⟩ := idx_copy hi
    have ht := mem_rows.mp (List.of_mem_zip hti).1
    obtain ⟨v, hv, hm⟩ := hfit_t t ht (a, d) ha
    refine ⟨v, ?_, hm⟩
    rw [hxget t i hti (a, d) ha, hv]; rfl
  · rw [← hkeys]
    exact List.mem_map_of_mem (mem_ofPairs.mp hq)
  · rw [hg]
    apply graph_congr
    intro t ht
    obtain ⟨i, hti⟩ := exists_copy (mem_rows.mpr ht)
    rw [copyOf_eq (rows_nodup data) hti]
    have hft := (Unrel.mem_assignments has _).mp ((hpk _).mp (hfp t ht)).1
    obtain ⟨ps, hps, hfe⟩ := hft
    have hov : Tuple.Over u.heading.attrs (f t) := by rw [hfe]; exact hps.over hun
    apply Tuple.ext_get? (over_decOf hun _ i).1 hov.1
    intro a
    by_cases ha : a ∈ u.heading.attrs
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      rw [decOf_get hun (show (q.1, q.2) ∈ u.heading from hq), hxget t i hti q hq]
      obtain ⟨v, hv, _⟩ := hfit_t t ht q hq
      rw [hv]; rfl
    · rw [get_none_of_over (over_decOf hun _ i) ha, get_none_of_over hov ha]

/-- Two assignments that give every cell a value in its domain and give the same candidate
agree on every cell. -/
theorem phi_cells_agree {p : Program} {ch : Chain} {F : Flat} (R : PhiOfRun nm p ch F) {x y : Tuple}
    (hx : FitsCells F.cells x) (hy : FitsCells F.cells y)
    (e : substitute F x = substitute F y) : ∀ c ∈ F.cells.attrs, x.get? c = y.get? c := by
  have hgx := substitute_graph R x
  have hgy := substitute_graph R y
  obtain ⟨data, u, picks, kinds, conds, hom, hnd, hfit, hcn, hkinds, hattrs, hconds, rfl⟩ := R
  dsimp only at hgx hgy hx hy e ⊢
  obtain ⟨hdn, hun, hdis⟩ := nodup_split hnd
  rw [hgx, hgy] at e
  have hfg := graph_inj hdis (fun t ht => over_fit hdn (hfit t ht))
    (fun t _ => over_decOf hun x _) (fun t _ => over_decOf hun y _) e
  intro c hc
  obtain ⟨⟨c', d⟩, hcd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨a, i, ha, hi, rfl⟩ := of_mem_phiCells hcd
  obtain ⟨t, hti⟩ := idx_copy hi
  have ht := mem_rows.mp (List.of_mem_zip hti).1
  have he := hfg t ht
  rw [copyOf_eq (rows_nodup data) hti] at he
  have h1 := decOf_get (nm := nm) (x := x) (i := i) hun ha
  have h2 := decOf_get (nm := nm) (x := y) (i := i) hun ha
  rw [he, h2] at h1
  obtain ⟨v, hv, _⟩ := hx _ _ (lookup_of_mem_nodup hcn hcd)
  obtain ⟨w, hw, _⟩ := hy _ _ (lookup_of_mem_nodup hcn hcd)
  rw [hv, hw] at h1 ⊢
  simp only [Option.getD_some, Option.some.injEq] at h1
  rw [h1]

/-- **Theorem C, one to one.** Two assignments over exactly the cells that give every cell a
value in its domain and give the same candidate are equal. -/
theorem phi_cells_inj {p : Program} {ch : Chain} {F : Flat} (R : PhiOfRun nm p ch F) {x y : Tuple}
    (hx : FitsCells F.cells x) (hy : FitsCells F.cells y)
    (hox : Tuple.Over F.cells.attrs x) (hoy : Tuple.Over F.cells.attrs y)
    (e : substitute F x = substitute F y) : x = y := by
  apply Tuple.ext_get? hox.1 hoy.1
  intro c
  by_cases hc : c ∈ F.cells.attrs
  · exact phi_cells_agree R hx hy e c hc
  · rw [get_none_of_over hox hc, get_none_of_over hoy hc]

/-- The candidate an assignment gives reads only the cells. -/
theorem substitute_congr {p : Program} {ch : Chain} {F : Flat} (R : PhiOfRun nm p ch F) {x y : Tuple}
    (h : ∀ c ∈ F.cells.attrs, x.get? c = y.get? c) : substitute F x = substitute F y := by
  rw [substitute_graph R x, substitute_graph R y]
  obtain ⟨data, u, picks, kinds, conds, hom, hnd, hfit, hcn, hkinds, hattrs, hconds, rfl⟩ := R
  dsimp only at h ⊢
  apply graph_congr
  intro t ht
  obtain ⟨i, hti⟩ := exists_copy (mem_rows.mpr ht)
  rw [copyOf_eq (rows_nodup data) hti]
  have hi := (List.of_mem_zip hti).2
  unfold decOf
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [h _ (List.mem_map_of_mem (mem_phiCells (nm := nm) (n := (phiRows data).length) hi
    (show (q.1, q.2) ∈ u.heading from hq)))]

/-- **Theorem C** in one statement, from `phi p k = .ok F`: `data`, `u` and `picks` are the
Data, the Decision and the Decision's tuples of the solution set's `ω_sol` (`omegaOf`). -/
theorem phi_cells {p : Program} {k : Nat} {F : Flat} (h : phi p k = .ok F) :
    ∃ ch data u picks, statementChain p k = some ch ∧ omegaOf p ch = .ok (data, u, picks) ∧
      (∀ x, FitsCells F.cells x →
        (substitute F x ∈ omegaSolCandidates F.heading data.tuples picks ↔
          ∀ i ∈ phiIdx (phiRows data).length, u.term.holds (decOf cellName x u.heading i) = .ok true)) ∧
      (∀ c ∈ omegaSolCandidates F.heading data.tuples picks,
        ∃ x, FitsCells F.cells x ∧ Tuple.Over F.cells.attrs x ∧ substitute F x = c) ∧
      (∀ x y, FitsCells F.cells x → FitsCells F.cells y → Tuple.Over F.cells.attrs x →
        Tuple.Over F.cells.attrs y → substitute F x = substitute F y → x = y) := by
  obtain ⟨R⟩ := phi_spec h
  exact ⟨R.ch, R.data, R.u, R.picks, R.hch, R.hom, fun x hx => phi_cells_into R.toOf hx,
    fun c hc => phi_cells_onto R.toOf hc, fun x y hx hy hox hoy e => phi_cells_inj R.toOf hx hy hox hoy e⟩

end Rasso.Phi
