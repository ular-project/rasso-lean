import Rasso.Laws.SolJoinSlices

/-!
# Rasso: ρ_sol keeps well-formed members

-/

namespace Rasso


open Finrel SolJoinLaws

/-! ## Renaming tuples, by attribute -/

section RenameTuple
variable {ren : List (String × String)} {A : List String}

/-- `renameAttr` is one-to-one on `A`. -/
def RenInj (ren : List (String × String)) (A : List String) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, renameAttr ren a = renameAttr ren b → a = b

theorem renameTuple_keys_nodup {t : Tuple} (ht : Tuple.Sorted t) (hA : ∀ q ∈ t, q.1 ∈ A)
    (hi : RenInj ren A) : ((t.map fun (p : String × Value) => (renameAttr ren p.1, p.2)).map (·.1)).Nodup := by
  rw [List.map_map]
  have hn := Tuple.nodup_keys ht
  refine nodup_map_on (l := t) (fun x hx y hy e => ?_) (nodup_of_map hn)
  have := hi x.1 (hA x hx) y.1 (hA y hy) e
  -- two pairs of a sorted tuple with one attribute are one pair
  have e2 := inj_of_nodup_map hn x hx y hy this
  exact e2

theorem sorted_renameTuple {t : Tuple} (ht : Tuple.Sorted t) (hA : ∀ q ∈ t, q.1 ∈ A)
    (hi : RenInj ren A) : Tuple.Sorted (renameTuple ren t) :=
  Tuple.sorted_ofPairs (renameTuple_keys_nodup ht hA hi)

theorem lookup_rename_map {a : String} (hi : RenInj ren A) (ha : a ∈ A) :
    ∀ {t : Tuple}, (∀ q ∈ t, q.1 ∈ A) →
      (t.map fun (p : String × Value) => (renameAttr ren p.1, p.2)).lookup (renameAttr ren a) = t.lookup a
  | [], _ => rfl
  | (b, v) :: t, hA => by
    simp only [List.map_cons, List.lookup]
    by_cases hab : a = b
    · subst hab; simp
    · have h1 : (renameAttr ren a == renameAttr ren b) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun e => hab (hi a ha b (hA (b, v) List.mem_cons_self) e)
      have h2 : (a == b) = false := by simp [hab]
      rw [h1, h2]
      exact lookup_rename_map hi ha fun q hq => hA q (List.mem_cons_of_mem _ hq)

theorem lookup_rename_map_none {b : String} :
    ∀ {t : Tuple}, (∀ q ∈ t, renameAttr ren q.1 ≠ b) →
      (t.map fun (p : String × Value) => (renameAttr ren p.1, p.2)).lookup b = none
  | [], _ => rfl
  | (c, v) :: t, h => by
    simp only [List.map_cons, List.lookup]
    have : (b == renameAttr ren c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun e => h (c, v) List.mem_cons_self e.symm
    rw [this]
    exact lookup_rename_map_none fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- The value of a renamed tuple at a renamed attribute. -/
theorem renTuple_get? {t : Tuple} (ht : Tuple.Sorted t) (hA : ∀ q ∈ t, q.1 ∈ A)
    (hi : RenInj ren A) {a : String} (ha : a ∈ A) :
    Tuple.get? (renameTuple ren t) (renameAttr ren a) = Tuple.get? t a := by
  unfold renameTuple
  rw [Tuple.get?_ofPairs (renameTuple_keys_nodup ht hA hi)]
  exact lookup_rename_map hi ha hA

/-- A renamed tuple has no value at a name that is no renamed attribute of `A`. -/
theorem renTuple_get?_none {t : Tuple} (ht : Tuple.Sorted t) (hA : ∀ q ∈ t, q.1 ∈ A)
    (hi : RenInj ren A) {b : String} (hb : ∀ a ∈ A, renameAttr ren a ≠ b) :
    Tuple.get? (renameTuple ren t) b = none := by
  unfold renameTuple
  rw [Tuple.get?_ofPairs (renameTuple_keys_nodup ht hA hi)]
  exact lookup_rename_map_none fun q hq => hb q.1 (hA q hq)

/-- Renaming is one-to-one on sorted tuples over `A`. -/
theorem renameTuple_inj {t u : Tuple} (ht : Tuple.Sorted t) (hu : Tuple.Sorted u)
    (htA : ∀ q ∈ t, q.1 ∈ A) (huA : ∀ q ∈ u, q.1 ∈ A) (hi : RenInj ren A)
    (e : renameTuple ren t = renameTuple ren u) : t = u := by
  refine Tuple.ext_get? ht hu fun a => ?_
  by_cases ha : a ∈ A
  · rw [← renTuple_get? ht htA hi ha, ← renTuple_get? hu huA hi ha, e]
  · rw [Tuple.get?_eq_none_of_over ⟨ht, htA⟩ ha, Tuple.get?_eq_none_of_over ⟨hu, huA⟩ ha]

theorem keys_merge {t u : Tuple} (ht : Tuple.Sorted t) (hu : Tuple.Sorted u)
    (htA : ∀ q ∈ t, q.1 ∈ A) (huA : ∀ q ∈ u, q.1 ∈ A) : ∀ q ∈ t.merge u, q.1 ∈ A := by
  intro q hq
  have hs := Tuple.sorted_merge ht hu
  have hv : Tuple.get? (t.merge u) q.1 = some q.2 := lookup_of_mem (Tuple.nodup_keys hs) hq
  rw [Tuple.get?_merge ht hu] at hv
  cases h1 : Tuple.get? t q.1 with
  | some v => exact htA (q.1, v) (lookup_mem (l := t) h1)
  | none =>
    rw [h1, Option.none_or] at hv
    exact huA (q.1, q.2) (lookup_mem (l := u) hv)

/-- Renaming a merge is merging the renamed parts. -/
theorem renameTuple_merge {t u : Tuple} (ht : Tuple.Sorted t) (hu : Tuple.Sorted u)
    (htA : ∀ q ∈ t, q.1 ∈ A) (huA : ∀ q ∈ u, q.1 ∈ A) (hi : RenInj ren A) :
    renameTuple ren (t.merge u) = (renameTuple ren t).merge (renameTuple ren u) := by
  have hs := Tuple.sorted_merge ht hu
  have hmA := keys_merge ht hu htA huA
  have hrt := sorted_renameTuple ht htA hi
  have hru := sorted_renameTuple hu huA hi
  refine Tuple.ext_get? (sorted_renameTuple hs hmA hi) (Tuple.sorted_merge hrt hru) fun b => ?_
  rw [Tuple.get?_merge hrt hru]
  by_cases hb : ∃ a ∈ A, renameAttr ren a = b
  · obtain ⟨a, ha, rfl⟩ := hb
    rw [renTuple_get? hs hmA hi ha, renTuple_get? ht htA hi ha, renTuple_get? hu huA hi ha,
      Tuple.get?_merge ht hu]
  · have hb' : ∀ a ∈ A, renameAttr ren a ≠ b := fun a ha e => hb ⟨a, ha, e⟩
    rw [renTuple_get?_none hs hmA hi hb', renTuple_get?_none ht htA hi hb',
      renTuple_get?_none hu huA hi hb']
    rfl

end RenameTuple

namespace SolJoinLaws

/-- **ρ_sol keeps `MembersOk`.** -/
theorem rename_membersOk {ren : List (String × String)} {s s' : Sol} (hρ : s.rename ren = .ok s')
    (hs : s.MembersOk) : s'.MembersOk := by
  classical
  obtain ⟨⟨-, hnd⟩, -⟩ := rename_ok.mp ⟨s', hρ⟩
  obtain ⟨hd, hh, hc⟩ := rename_eq hρ
  obtain ⟨-, -, hd'⟩ := Finrel.rename_eq_ok.mp hd
  let ren' := ren.filter fun p => s.data.attrs.contains p.1
  -- renaming is one-to-one on the heading
  have hmap : (renameHeading ren s.heading).attrs = s.heading.attrs.map (renameAttr ren) := by
    simp [renameHeading, Heading.attrs, List.map_map, Function.comp_def]
  have hi : RenInj ren s.heading.attrs := by
    intro a ha b hb e
    rw [hmap] at hnd
    exact inj_of_nodup_map hnd a ha b hb e
  have hUd : ∀ a ∈ s.data.attrs, a ∈ s.heading.attrs := hs.dataAttrs
  -- the Data's renaming agrees with `ren` on the Data
  have hagree : ∀ a ∈ s.data.attrs, renameAttr ren' a = renameAttr ren a := by
    intro a ha
    unfold renameAttr
    rw [lookup_filter_key (c := fun x => s.data.attrs.contains x) (List.contains_iff_mem.mpr ha)]
  have hkeysD : ∀ d ∈ s.data.tuples, ∀ q ∈ d, q.1 ∈ s.data.attrs := fun d hd' => (hs.dataExact d hd').1.2
  have hren' : ∀ d ∈ s.data.tuples, renameTuple ren' d = renameTuple ren d := by
    intro d hd0
    unfold renameTuple
    congr 1
    apply List.map_congr_left
    intro q hq
    obtain ⟨a, v⟩ := q
    show (renameAttr ren' a, v) = (renameAttr ren a, v)
    rw [hagree a (hkeysD d hd0 (a, v) hq)]
  have hdataAttrs : ∀ b, b ∈ s'.data.attrs ↔ ∃ a ∈ s.data.attrs, renameAttr ren a = b := by
    intro b
    rw [hd']
    show b ∈ (renameHeading ren' s.data.heading).attrs ↔ _
    simp only [renameHeading, Heading.attrs, List.map_map, Function.comp_def, List.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have ha : p.1 ∈ s.data.attrs := List.mem_map_of_mem hp
      exact ⟨p.1, ha, (hagree p.1 ha).symm⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact ⟨p, hp, hagree p.1 ha⟩
  have hdataT : ∀ t, t ∈ s'.data.tuples ↔ ∃ d ∈ s.data.tuples, t = renameTuple ren d := by
    intro t
    rw [hd', Finrel.mem_ofTuples, List.mem_map]
    constructor
    · rintro ⟨d, hd0, rfl⟩; exact ⟨d, hd0, hren' d hd0⟩
    · rintro ⟨d, hd0, rfl⟩; exact ⟨d, hd0, hren' d hd0⟩
  have hheadAttrs : ∀ b, b ∈ s'.heading.attrs ↔ ∃ a ∈ s.heading.attrs, renameAttr ren a = b := by
    intro b
    rw [hh, hmap, List.mem_map]
  -- the renamed Decision
  have hdec : ∀ a ∈ s.heading.attrs, renameAttr ren a ∈ s'.decision.attrs ↔ a ∈ s.decision.attrs := by
    intro a ha
    rw [mem_decision_attrs, mem_decision_attrs, hheadAttrs, hdataAttrs]
    constructor
    · rintro ⟨-, hn⟩
      exact ⟨ha, fun had => hn ⟨a, had, rfl⟩⟩
    · rintro ⟨-, hn⟩
      refine ⟨⟨a, ha, rfl⟩, ?_⟩
      rintro ⟨a', ha', e⟩
      exact hn (hi a' (hUd a' ha') a ha e ▸ ha')
  have hdecImg : ∀ b ∈ s'.decision.attrs, ∃ a ∈ s.heading.attrs, renameAttr ren a = b := by
    intro b hb
    exact (hheadAttrs b).mp (mem_decision_attrs.mp hb).1
  -- tuples over the heading
  have hdH : ∀ d ∈ s.data.tuples, Tuple.Sorted d ∧ ∀ q ∈ d, q.1 ∈ s.heading.attrs :=
    fun d hd0 => ⟨(hs.dataExact d hd0).1.1, fun q hq => hUd _ (hkeysD d hd0 q hq)⟩
  refine ⟨fun b hb => ?_, fun t ht => ?_, fun c' hc' => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (hdataAttrs b).mp hb
    exact (hheadAttrs _).mpr ⟨a, hUd a ha, rfl⟩
  · obtain ⟨d, hd0, rfl⟩ := (hdataT t).mp ht
    have he := Tuple.exactly_iff.mp (hs.dataExact d hd0)
    refine Tuple.exactly_iff.mpr ⟨sorted_renameTuple (hdH d hd0).1 (hdH d hd0).2 hi, fun b => ?_⟩
    by_cases hb : ∃ a ∈ s.heading.attrs, renameAttr ren a = b
    · obtain ⟨a, ha, rfl⟩ := hb
      rw [renTuple_get? (hdH d hd0).1 (hdH d hd0).2 hi ha, he.2 a, hdataAttrs]
      constructor
      · intro had; exact ⟨a, had, rfl⟩
      · rintro ⟨a', ha', e⟩; exact hi a' (hUd a' ha') a ha e ▸ ha'
    · have hb' : ∀ a ∈ s.heading.attrs, renameAttr ren a ≠ b := fun a ha e => hb ⟨a, ha, e⟩
      rw [renTuple_get?_none (hdH d hd0).1 (hdH d hd0).2 hi hb']
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      rw [hdataAttrs]
      rintro ⟨a, ha, e⟩
      exact hb ⟨a, hUd a ha, e⟩
  · rw [hc] at hc'
    obtain ⟨c, hcc, rfl⟩ := List.mem_map.mp hc'
    obtain ⟨f, hf, hmb⟩ := hs.graph c hcc
    have hfH : ∀ d ∈ s.data.tuples, Tuple.Sorted (f d) ∧ ∀ q ∈ f d, q.1 ∈ s.heading.attrs := by
      intro d hd0
      have he := hf d hd0
      exact ⟨he.1.1, fun q hq => (mem_decision_attrs.mp (he.1.2 q hq)).1⟩
    let f' : Tuple → Tuple := fun d' =>
      if h : ∃ d ∈ s.data.tuples, renameTuple ren d = d' then renameTuple ren (f (Classical.choose h)) else []
    have hf' : ∀ d ∈ s.data.tuples, f' (renameTuple ren d) = renameTuple ren (f d) := by
      intro d hd0
      have h : ∃ d0 ∈ s.data.tuples, renameTuple ren d0 = renameTuple ren d := ⟨d, hd0, rfl⟩
      simp only [f']
      rw [dite_eq_left h]
      obtain ⟨h1, h2⟩ := Classical.choose_spec h
      rw [renameTuple_inj (hdH _ h1).1 (hdH d hd0).1 (hdH _ h1).2 (hdH d hd0).2 hi h2]
    refine ⟨f', fun t ht => ?_, ?_⟩
    · obtain ⟨d, hd0, rfl⟩ := (hdataT t).mp ht
      rw [hf' d hd0]
      have he := Tuple.exactly_iff.mp (hf d hd0)
      refine Tuple.exactly_iff.mpr ⟨sorted_renameTuple (hfH d hd0).1 (hfH d hd0).2 hi, fun b => ?_⟩
      by_cases hb : ∃ a ∈ s.heading.attrs, renameAttr ren a = b
      · obtain ⟨a, ha, rfl⟩ := hb
        rw [renTuple_get? (hfH d hd0).1 (hfH d hd0).2 hi ha, he.2 a, hdec a ha]
      · have hb' : ∀ a ∈ s.heading.attrs, renameAttr ren a ≠ b := fun a ha e => hb ⟨a, ha, e⟩
        rw [renTuple_get?_none (hfH d hd0).1 (hfH d hd0).2 hi hb']
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
        intro hbd
        exact hb (hdecImg b hbd)
    · apply Body.ext
      intro r
      show r ∈ (renameMember ren s.heading c).tuples ↔ r ∈ (graph s'.heading s'.data.tuples f').tuples
      rw [mem_renameMember, mem_graph]
      constructor
      · rintro ⟨u, hu, rfl⟩
        rw [Finrel.mem_ofTuples] at hu
        have hu' : u ∈ (graph s.heading s.data.tuples f).tuples := by
          unfold Finrel.tuples at hu; rw [hmb] at hu; exact hu
        obtain ⟨d, hd0, rfl⟩ := (mem_graph _).mp hu'
        refine ⟨renameTuple ren d, (hdataT _).mpr ⟨d, hd0, rfl⟩, ?_⟩
        rw [hf' d hd0, renameTuple_merge (hdH d hd0).1 (hfH d hd0).1 (hdH d hd0).2 (hfH d hd0).2 hi]
      · rintro ⟨t, ht, rfl⟩
        obtain ⟨d, hd0, rfl⟩ := (hdataT t).mp ht
        refine ⟨d.merge (f d), ?_, ?_⟩
        · rw [Finrel.mem_ofTuples]
          have : d.merge (f d) ∈ (graph s.heading s.data.tuples f).tuples := (mem_graph _).mpr ⟨d, hd0, rfl⟩
          show d.merge (f d) ∈ c.body.toList
          rw [hmb]; exact this
        · rw [hf' d hd0, renameTuple_merge (hdH d hd0).1 (hfH d hd0).1 (hdH d hd0).2 (hfH d hd0).2 hi]

/-- An n-ary ⋈_sol, as a left fold, keeps `MembersOk`. -/
theorem foldlM_join_membersOk :
    ∀ (ws : List Sol) {s r : Sol}, s.MembersOk → (∀ w ∈ ws, w.MembersOk) →
      ws.foldlM (fun acc w => acc.join w) s = .ok r → r.MembersOk
  | [], s, r, hs, _, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hs
  | w :: ws, s, r, hs, hw, h => by
    rw [List.foldlM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i s1 h1
    exact foldlM_join_membersOk ws (join_membersOk h1 hs (hw w List.mem_cons_self))
      (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) h

end SolJoinLaws

end Rasso
