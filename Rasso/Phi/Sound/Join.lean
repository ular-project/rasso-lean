import Rasso.Phi.Sound.Rel

/-!
# φ soundness: natural join

`sJoin_sound`: if `R` denotes `r` and `S` denotes `s`, the symbolic join denotes `r ⋈ s`.
The present rows of the symbolic join are, in order, the merges of each present left row
with each present right row it agrees with: the list Lean's `Finrel.join` builds, before
it is made a set.
-/

namespace Rasso.Phi

open Rasso

/-! ## Lookups -/

theorem lookup_map_keyed {β γ : Type} (g : String → β → γ) : ∀ (l : List (String × β)) (a : String),
    (l.map fun p => (p.1, g p.1 p.2)).lookup a = (l.lookup a).map (g a)
  | [], _ => rfl
  | (b, e) :: l, a => by
    by_cases hab : a = b
    · subst hab; simp [List.lookup]
    · have : (a == b) = false := by simpa using hab
      simp only [List.map_cons, List.lookup, this]
      exact lookup_map_keyed g l a

theorem lookup_filter_key {β : Type} (P : String → Bool) : ∀ (l : List (String × β)) (a : String),
    (l.filter fun p => P p.1).lookup a = if P a then l.lookup a else none
  | [], _ => by simp
  | (b, e) :: l, a => by
    by_cases hab : a = b
    · subst hab
      by_cases hp : P a <;> simp [hp, List.lookup, lookup_filter_key P l a]
    · have : (a == b) = false := by simpa using hab
      rw [List.filter_cons]
      split
      · simp only [List.lookup, this]; exact lookup_filter_key P l a
      · simp only [List.lookup, this]; exact lookup_filter_key P l a

/-- The attributes of an instantiated row: those of the row. -/
def AttrsOf (A : List String) (u : Tuple) : Prop :=
  Tuple.Sorted u ∧ ∀ a, (u.get? a).isSome = true ↔ a ∈ A

theorem attrsOf_inst {x : Tuple} {row : SRow} {u : Tuple} (hu : RowInst x row u) (hs : Tuple.Sorted u) :
    AttrsOf (row.map (·.1)) u := by
  refine ⟨hs, fun a => ?_⟩
  rcases hu a with ⟨h1, h2⟩ | ⟨s, v, h1, _, h3⟩
  · rw [h2]
    constructor
    · intro h; cases h
    · intro ha; have := lookup_isSome_iff_mem ha; rw [h1] at this; cases this
  · rw [h3]
    exact ⟨fun _ => List.mem_map_of_mem (f := (·.1)) (lookup_mem h1), fun _ => rfl⟩

/-- A row whose terms all evaluate instantiates to the sorted tuple of their values. -/
theorem rowInst_ofEval {x : Tuple} {row : SRow} (hn : (row.map (·.1)).Nodup)
    (he : ∀ p ∈ row, ∃ v, p.2.eval x = .ok v) :
    ∃ w, RowInst x row w ∧ Tuple.Sorted w := by
  let g : String → Term → Value := fun _ s => match s.eval x with
    | .ok v => v
    | .error _ => default
  let ps := row.map fun p => (p.1, g p.1 p.2)
  have hk : (ps.map (·.1)).Nodup := by simpa [ps, List.map_map, Function.comp_def] using hn
  refine ⟨Tuple.ofPairs ps, fun a => ?_, Tuple.sorted_ofPairs hk⟩
  rw [Tuple.get?_ofPairs hk, lookup_map_keyed g row a]
  cases hl : row.lookup a with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some s =>
    obtain ⟨v, hv⟩ := he _ (lookup_mem hl)
    refine Or.inr ⟨s, v, rfl, hv, ?_⟩
    simp only [Option.map_some, g, hv]

/-! ## Merges -/

theorem merge_keys_nodup {t u : Tuple} (ht : Tuple.Sorted t) (hu : Tuple.Sorted u) :
    ((t ++ u.filter fun p => (Tuple.get? t p.1).isNone).map (·.1)).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨Tuple.nodup_keys ht, (List.filter_sublist.map _).nodup (Tuple.nodup_keys hu), ?_⟩
  intro a ha b hb e
  subst e
  obtain ⟨⟨_, v⟩, hq, rfl⟩ := List.mem_map.mp ha
  obtain ⟨⟨_, w⟩, hq', e⟩ := List.mem_map.mp hb
  simp only at e; subst e
  have hnone := (List.mem_filter.mp hq').2
  have hsome : Tuple.get? t _ = some v := lookup_of_mem (Tuple.nodup_keys ht) hq
  rw [hsome] at hnone; cases hnone

theorem merge_sorted {t u : Tuple} (ht : Tuple.Sorted t) (hu : Tuple.Sorted u) :
    Tuple.Sorted (t.merge u) := Tuple.sorted_ofPairs (merge_keys_nodup ht hu)

/-- Agreeing tuples over `A` and `B` agree on `A ∩ B`, and conversely. -/
theorem agrees_iff {A B : List String} {u v : Tuple} (hu : AttrsOf A u) (hv : AttrsOf B v) :
    u.agrees v = true ↔ ∀ c, c ∈ A → c ∈ B → u.get? c = v.get? c := by
  constructor
  · intro h c hcA hcB
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((hu.2 c).mpr hcA)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((hv.2 c).mpr hcB)
    have := Finrel.agrees_eq h (lookup_mem hx) hy
    rw [hx, hy, this]
  · intro h
    refine List.all_eq_true.mpr fun ⟨a, x⟩ hx => ?_
    have hux : u.get? a = some x := lookup_of_mem (Tuple.nodup_keys hu.1) hx
    cases hva : v.get? a with
    | none => simp [hva]
    | some y =>
      have := h a ((hu.2 a).mp (by rw [hux]; rfl)) ((hv.2 a).mp (by rw [hva]; rfl))
      rw [hux, hva] at this; cases this; simp [hva]

/-- A merge of agreeing tuples gives back both. -/
theorem merge_inj {A B : List String} {u u' v v' : Tuple} (hu : AttrsOf A u) (hu' : AttrsOf A u')
    (hv : AttrsOf B v) (hv' : AttrsOf B v') (ha : u.agrees v = true) (ha' : u'.agrees v' = true)
    (h : u.merge v = u'.merge v') : u = u' ∧ v = v' := by
  have hg : ∀ a, (u.get? a).or (v.get? a) = (u'.get? a).or (v'.get? a) := fun a => by
    rw [← Tuple.get?_merge hu.1 hv.1, ← Tuple.get?_merge hu'.1 hv'.1, h]
  have hnone : ∀ {w : Tuple} {C : List String}, AttrsOf C w → ∀ a, a ∉ C → w.get? a = Option.none :=
    fun hw a ha => by
      cases hx : Tuple.get? _ a with
      | none => rfl
      | some _ => exact absurd ((hw.2 a).mp (by rw [hx]; rfl)) ha
  have hu_eq : u = u' := Tuple.ext_get? hu.1 hu'.1 fun a => by
    by_cases haA : a ∈ A
    · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((hu.2 a).mpr haA)
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((hu'.2 a).mpr haA)
      have := hg a; rw [hx, hy] at this; simp at this; rw [hx, hy, this]
    · rw [hnone hu a haA, hnone hu' a haA]
  subst hu_eq
  refine ⟨rfl, Tuple.ext_get? hv.1 hv'.1 fun a => ?_⟩
  by_cases haB : a ∈ B
  · by_cases haA : a ∈ A
    · rw [← (agrees_iff hu hv).mp ha a haA haB, ← (agrees_iff hu hv').mp ha' a haA haB]
    · have := hg a; rwa [hnone hu a haA, Option.none_or, Option.none_or] at this
  · rw [hnone hv a haB, hnone hv' a haB]

/-! ## Lists -/

theorem nodup_flatMap {α β : Type} {f : α → List β} : ∀ {l : List α},
    (∀ a ∈ l, (f a).Nodup) → l.Pairwise (fun a b => ∀ x ∈ f a, x ∉ f b) → (l.flatMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h1, h2 => by
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨h1 a List.mem_cons_self, nodup_flatMap (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
      (List.pairwise_cons.mp h2).2, fun x hx y hy e => ?_⟩
    subst e
    obtain ⟨b, hb, hyb⟩ := List.mem_flatMap.mp hy
    exact (List.pairwise_cons.mp h2).1 b hb x hx hyb

/-! ## One pair of rows -/

theorem eq_val_of_applyOp {v w r : Value} (h : applyOp "=" [v, w] = .ok r) : r = .bool (v == w) := by
  simp only [applyOp] at h
  split at h <;> first
    | (simp [throw, throwThe, MonadExceptOf.throw] at h; done)
    | (simp [pure, Except.pure] at h; exact h.symm)

theorem sJoinEqs_sound {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {a b : SRow} {ua ub : Tuple}
    (hua : RowInst x a ua) (hub : RowInst x b ub) : ∀ (cs : List String),
    (∀ c ∈ cs, c ∈ a.map (·.1) ∧ c ∈ b.map (·.1)) → ∀ {ok : Bool} {es : List Term},
    sJoinEqs ks a b cs = .ok (ok, es) →
    ∃ bs : List Bool, es.mapM (Term.eval x) = .ok (bs.map .bool) ∧
      ((ok && bs.all id) = true ↔ ∀ c ∈ cs, ua.get? c = ub.get? c)
  | [], _, ok, es, h => by
    rw [sJoinEqs] at h; cases h; exact ⟨[], rfl, by simp⟩
  | c :: cs, hk, ok, es, h => by
    obtain ⟨hca, hcb⟩ := hk c List.mem_cons_self
    obtain ⟨ta, hta⟩ := Option.isSome_iff_exists.mp (lookup_isSome_iff_mem hca)
    obtain ⟨tb, htb⟩ := Option.isSome_iff_exists.mp (lookup_isSome_iff_mem hcb)
    obtain ⟨va, hva, hua'⟩ := hua.some hta
    obtain ⟨vb, hvb, hub'⟩ := hub.some htb
    -- the head attribute: whether it matches, and its equality terms
    have hhead : ∀ {ok1 : Bool} {es1 : List Term},
        (match a.lookup c, b.lookup c with
          | some (.val x), some (.val y) => .ok (x == y, [])
          | some x, some y => do return (true, [← mk ks "=" [x, y]])
          | _, _ => .ok (false, []) : Except String (Bool × List Term)) = .ok (ok1, es1) →
        ∃ bs1 : List Bool, es1.mapM (Term.eval x) = .ok (bs1.map .bool) ∧
          ((ok1 && bs1.all id) = true ↔ va = vb) := by
      intro ok1 es1 e
      rw [hta, htb] at e
      split at e
      · rename_i x' y' e1 e2
        cases e1; cases e2; cases e
        simp [Term.eval] at hva hvb; subst hva; subst hvb
        exact ⟨[], rfl, by simp⟩
      · rename_i x' y' _ e1 e2
        cases e1; cases e2
        simp only [bind, Except.bind, pure, Except.pure] at e
        split at e
        · cases e
        · rename_i t ht
          cases e
          have := mk_eq ht; subst this
          obtain ⟨w, hw⟩ := mk_sound hx ht
          obtain ⟨ws, hws, hap⟩ := eval_call_ok hw
          simp only [List.mapM_cons, List.mapM_nil, hva, hvb, bind, Except.bind, pure, Except.pure] at hws
          cases hws
          have := eq_val_of_applyOp hap; subst this
          exact ⟨[va == vb], by simp [List.mapM_cons, hw, bind, Except.bind, pure, Except.pure], by simp⟩
      · rename_i hne; exact (hne _ _ rfl rfl).elim
    rw [sJoinEqs] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    rename_i p1 hp1
    obtain ⟨ok1, es1⟩ := p1
    split at h
    · cases h
    rename_i p2 hp2
    obtain ⟨ok2, es2⟩ := p2
    cases h
    obtain ⟨bs1, hes1, hiff1⟩ := hhead hp1
    obtain ⟨bs2, hes2, hiff2⟩ :=
      sJoinEqs_sound hx hua hub cs (fun c hc => hk c (List.mem_cons_of_mem _ hc)) hp2
    refine ⟨bs1 ++ bs2, ?_, ?_⟩
    · rw [List.mapM_append, hes1, hes2]; simp [bind, Except.bind, pure, Except.pure]
    · rw [List.forall_mem_cons, hua', hub', ← hiff2]
      simp only [Option.some.injEq, ← hiff1, List.all_append, Bool.and_eq_true]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
      · rintro ⟨⟨h1, h3⟩, h2, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem lookup_map_fst {β : Type} {F : String × β → String × β} (hF : ∀ q, (F q).1 = q.1) :
    ∀ (l : List (String × β)) (a : String), (l.map F).lookup a = (l.lookup a).map fun t => (F (a, t)).2
  | [], _ => rfl
  | (b, e) :: l, a => by
    have hb := hF (b, e)
    simp only at hb
    by_cases hab : a = b
    · subst hab
      simp only [List.map_cons, List.lookup]
      rw [show F (a, e) = ((F (a, e)).1, (F (a, e)).2) from rfl, hb]
      simp
    · have : (a == b) = false := by simpa using hab
      have : (a == (F (b, e)).1) = false := by rw [hb]; exact this
      simp only [List.map_cons, List.lookup, this, ‹(a == b) = false›]
      exact lookup_map_fst hF l a

theorem map_fst_comp {β : Type} {F : String × β → String × β} (hF : ∀ q, (F q).1 = q.1)
    (l : List (String × β)) : List.map ((fun x => x.fst) ∘ F) l = l.map (·.1) :=
  List.map_congr_left fun q _ => hF q

theorem mem_keys_iff_lookup {β : Type} {l : List (String × β)} {a : String} :
    a ∈ l.map (·.1) ↔ ∃ t, l.lookup a = some t := by
  constructor
  · intro h; exact Option.isSome_iff_exists.mp (lookup_isSome_iff_mem h)
  · rintro ⟨t, ht⟩; exact List.mem_map_of_mem (f := (·.1)) (lookup_mem ht)

/-- The attributes a join's row has: the left's, then the right's own. -/
def joinAttrs (RA SA : List String) : List String :=
  RA ++ SA.filter fun c => !(RA.filter SA.contains).contains c

theorem contains_false {l : List String} {a : String} : l.contains a = false ↔ a ∉ l := by
  rw [← List.contains_iff_mem]; simp

theorem joinAttrs_nodup {RA SA : List String} (hRn : RA.Nodup) (hSn : SA.Nodup) :
    (joinAttrs RA SA).Nodup := by
  unfold joinAttrs
  refine List.nodup_append.mpr ⟨hRn, hSn.filter _, fun a ha b hb e => ?_⟩
  subst e
  have := List.mem_filter.mp hb
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact contains_false.mp this.2 (List.mem_filter.mpr ⟨ha, by simpa using this.1⟩)

/-- The row of a joined pair instantiates; when the pair agrees, to the merge. -/
theorem joinRow_inst {x : Tuple} {RA SA : List String} (hRn : RA.Nodup) (hSn : SA.Nodup)
    {ra rb : SRow} {ua ub : Tuple} (hia : RowInst x ra ua) (hib : RowInst x rb ub)
    (hka : ra.map (·.1) = RA) (hkb : rb.map (·.1) = SA) (hA : AttrsOf RA ua) (hB : AttrsOf SA ub)
    (F : String × Term → String × Term) (hF1 : ∀ q, (F q).1 = q.1)
    (hF2 : ∀ c t, (F (c, t)).2 = t ∨
      (c ∈ RA.filter SA.contains ∧ ∃ y, rb.lookup c = some (.val y) ∧ (F (c, t)).2 = .val y)) :
    ∃ w, RowInst x (ra.map F ++ rb.filter fun q => !(RA.filter SA.contains).contains q.1) w ∧
      Tuple.Sorted w ∧ (ua.agrees ub = true → w = ua.merge ub) := by
  let shared := RA.filter SA.contains
  have hkeys : (ra.map F ++ rb.filter fun q => !shared.contains q.1).map (·.1) = joinAttrs RA SA := by
    have : (rb.filter fun q => !shared.contains q.1).map (·.1) =
        (rb.map (·.1)).filter (fun c => !shared.contains c) := by rw [List.filter_map]; rfl
    rw [List.map_append, List.map_map, map_fst_comp hF1, hka, this, hkb]; rfl
  have hnra : (ra.map (·.1)).Nodup := hka ▸ hRn
  have hnrb : (rb.map (·.1)).Nodup := hkb ▸ hSn
  have hevA : ∀ q ∈ ra, ∃ v, q.2.eval x = .ok v := fun q hq => by
    obtain ⟨v, hv, _⟩ := hia.some (mem_lookup hnra hq); exact ⟨v, hv⟩
  have hevB : ∀ q ∈ rb, ∃ v, q.2.eval x = .ok v := fun q hq => by
    obtain ⟨v, hv, _⟩ := hib.some (mem_lookup hnrb hq); exact ⟨v, hv⟩
  obtain ⟨w, hw, hws⟩ := rowInst_ofEval (hkeys ▸ joinAttrs_nodup hRn hSn) (fun p hp => by
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨⟨c, t⟩, hq, rfl⟩ := List.mem_map.mp hp
      rcases hF2 c t with e | ⟨_, y, _, e⟩
      · rw [e]; exact hevA _ hq
      · rw [e]; exact ⟨y, by simp [Term.eval]⟩
    · exact hevB p (List.mem_filter.mp hp).1)
  refine ⟨w, hw, hws, fun hag => Tuple.ext_get? hws (merge_sorted hA.1 hB.1) fun a => ?_⟩
  rw [Tuple.get?_merge hA.1 hB.1]
  have hnoneA : ra.lookup a = Option.none → ua.get? a = Option.none := hia.none
  have hnoneB : rb.lookup a = Option.none → ub.get? a = Option.none := hib.none
  have hlookA : (ra.map F).lookup a = (ra.lookup a).map fun t => (F (a, t)).2 := lookup_map_fst hF1 ra a
  have hlookB := lookup_filter_key (fun c => !shared.contains c) rb a
  rcases hw a with ⟨h1, h2⟩ | ⟨s, v, h1, h2, h3⟩
  · rw [h2]
    rw [List.lookup_append] at h1
    cases hra : ra.lookup a with
    | some t => rw [hlookA, hra] at h1; simp at h1
    | none =>
      rw [hlookA, hra] at h1
      simp only [Option.map_none, Option.none_or] at h1
      have haA : a ∉ RA := fun haA => by
        rw [← hka] at haA; obtain ⟨t, ht⟩ := mem_keys_iff_lookup.mp haA; rw [hra] at ht; cases ht
      have hsh : shared.contains a = false := by
        exact contains_false.mpr fun hm => haA (List.mem_filter.mp hm).1
      rw [hlookB] at h1
      simp only [hsh, Bool.not_false, ↓reduceIte] at h1
      rw [hnoneA hra, hnoneB h1]; rfl
  · rw [h3]
    rw [List.lookup_append] at h1
    cases hra : ra.lookup a with
    | some t =>
      rw [hlookA, hra] at h1
      simp only [Option.map_some, Option.some_or, Option.some.injEq] at h1
      obtain ⟨va, hva, hua⟩ := hia.some hra
      rw [hua]; simp only [Option.some_or]
      rcases hF2 a t with e | ⟨hsh, y, hy, e⟩
      · rw [e] at h1; subst h1; rw [h2] at hva; cases hva; rfl
      · rw [e] at h1; subst h1
        simp [Term.eval] at h2; subst h2
        obtain ⟨vb, hvb, hub⟩ := hib.some hy
        simp [Term.eval] at hvb; subst hvb
        have hm := List.mem_filter.mp hsh
        have := (agrees_iff hA hB).mp hag a hm.1 (by simpa using hm.2)
        rw [hua, hub] at this; cases this; rfl
    | none =>
      rw [hlookA, hra] at h1
      simp only [Option.map_none, Option.none_or] at h1
      have haA : a ∉ RA := fun haA => by
        rw [← hka] at haA; obtain ⟨t, ht⟩ := mem_keys_iff_lookup.mp haA; rw [hra] at ht; cases ht
      have hsh : shared.contains a = false := by
        exact contains_false.mpr fun hm => haA (List.mem_filter.mp hm).1
      rw [hlookB] at h1
      simp only [hsh, Bool.not_false, ↓reduceIte] at h1
      obtain ⟨vb, hvb, hub⟩ := hib.some h1
      rw [h2] at hvb; cases hvb
      rw [hnoneA hra, hub]; rfl

theorem joinPair_exists {x : Tuple} {RA SA : List String} (hRn : RA.Nodup) (hSn : SA.Nodup)
    {ra rb : SRow} {ua ub : Tuple} (hia : RowInst x ra ua) (hib : RowInst x rb ub)
    (hka : ra.map (·.1) = RA) (hkb : rb.map (·.1) = SA) (hA : AttrsOf RA ua) (hB : AttrsOf SA ub)
    {g : Term} {ba bb : Bool} (hge : g.eval x = .ok (.bool (ba && bb && ua.agrees ub)))
    (F : String × Term → String × Term) (hF1 : ∀ q, (F q).1 = q.1)
    (hF2 : ∀ c t, (F (c, t)).2 = t ∨
      (c ∈ RA.filter SA.contains ∧ ∃ y, rb.lookup c = some (.val y) ∧ (F (c, t)).2 = .val y)) :
    ∃ w b, GroupInst x (ra.map F ++ rb.filter fun q => !(RA.filter SA.contains).contains q.1, g) (w, b) ∧
      Tuple.Sorted w ∧ b = (ba && bb && ua.agrees ub) ∧ (b = true → w = ua.merge ub) := by
  obtain ⟨w, hw, hws, hwm⟩ := joinRow_inst hRn hSn hia hib hka hkb hA hB F hF1 hF2
  exact ⟨w, ba && bb && ua.agrees ub, ⟨hw, hge⟩, hws, rfl,
    fun hb => hwm (by simp only [Bool.and_eq_true] at hb; exact hb.2)⟩

theorem sJoinPair_sound {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {RA SA : List String}
    (hRn : RA.Nodup) (hSn : SA.Nodup) {ra rb : SRow × Term} {ua ub : Tuple × Bool}
    (hia : GroupInst x ra ua) (hib : GroupInst x rb ub) (hka : ra.1.map (·.1) = RA)
    (hkb : rb.1.map (·.1) = SA) (hsa : Tuple.Sorted ua.1) (hsb : Tuple.Sorted ub.1)
    {p : Option (SRow × Term)} (h : sJoinPair ks (RA.filter SA.contains) ra rb = .ok p) :
    match p with
    | none => ua.1.agrees ub.1 = false
    | some rg => rg.1.map (·.1) = joinAttrs RA SA ∧ ∃ w b, GroupInst x rg (w, b) ∧ Tuple.Sorted w ∧
        b = (ua.2 && ub.2 && ua.1.agrees ub.1) ∧ (b = true → w = ua.1.merge ub.1) := by
  have hA := attrsOf_inst hia.1 hsa
  have hB := attrsOf_inst hib.1 hsb
  rw [hka] at hA; rw [hkb] at hB
  have hagree : ua.1.agrees ub.1 = true ↔ ∀ c ∈ RA.filter SA.contains, ua.1.get? c = ub.1.get? c := by
    rw [agrees_iff hA hB]
    constructor
    · intro h c hc
      have := List.mem_filter.mp hc
      exact h c this.1 (by simpa using this.2)
    · intro h c hcA hcB; exact h c (List.mem_filter.mpr ⟨hcA, by simpa using hcB⟩)
  unfold sJoinPair at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i q hq
  obtain ⟨ok, eqs⟩ := q
  obtain ⟨bs, hbs, hiff⟩ := sJoinEqs_sound hx hia.1 hib.1 _ (fun c hc => by
    have := List.mem_filter.mp hc
    exact ⟨hka ▸ this.1, hkb ▸ (by simpa using this.2)⟩) hq
  simp only at h
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases h
    cases hag : ua.1.agrees ub.1
    · rfl
    · have := hiff.mpr (hagree.mp hag); simp at this
  | true =>
  have hok : true = true := rfl
  simp only [↓reduceIte] at h
  split at h
  · cases h
  rename_i g hg
  cases h
  have hbs_ag : bs.all id = ua.1.agrees ub.1 := by
    cases h1 : bs.all id <;> cases h2 : ua.1.agrees ub.1 <;> try rfl
    · have := hiff.mpr (hagree.mp h2); simp [h1] at this
    · have := hagree.mpr (hiff.mp (by simp [h1])); rw [h2] at this; cases this
  have hge : g.eval x = .ok (.bool (ua.2 && ub.2 && ua.1.agrees ub.1)) := by
    rw [sApply_sound hg x]
    simp only [List.mapM_cons, hia.2, hib.2, hbs, bind, Except.bind, pure, Except.pure]
    simp only [applyOp, bind, Except.bind, pure, Except.pure]
    rw [show (Value.bool ua.2 :: Value.bool ub.2 :: bs.map Value.bool) = (ua.2 :: ub.2 :: bs).map Value.bool
      from rfl, mapM_asBool_bools]
    simp [hbs_ag, Bool.and_assoc]
  refine ⟨?_, ?_⟩
  · simp only [List.map_append, List.map_map]
    rw [map_fst_comp, hka, joinAttrs]
    · rw [← hkb, List.filter_map]; rfl
    · intro q
      split
      · split <;> rfl
      · rfl
  exact joinPair_exists hRn hSn hia.1 hib.1 hka hkb hA hB hge _
    (fun q => by
      split
      · split <;> rfl
      · rfl)
    (fun c t => by
      simp only
      split
      · rename_i hsh
        split
        · rename_i y hy
          exact Or.inr ⟨List.contains_iff_mem.mp hsh, y, hy, rfl⟩
        · exact Or.inl rfl
      · exact Or.inl rfl)

/-! ## All pairs -/

@[simp] theorem presentT_cons_true (u : Tuple) (l : List (Tuple × Bool)) :
    presentT ((u, true) :: l) = u :: presentT l := rfl

@[simp] theorem presentT_cons_false (u : Tuple) (l : List (Tuple × Bool)) :
    presentT ((u, false) :: l) = presentT l := rfl

/-- What a left tuple contributes against a right tuple. -/
def joinOne (ba : Bool) (ua ub : Tuple) : Option Tuple :=
  if ba && ua.agrees ub then some (ua.merge ub) else none

theorem sJoinWith_sound {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {RA SA : List String}
    (hRn : RA.Nodup) (hSn : SA.Nodup) {ra : SRow × Term} {ua : Tuple × Bool}
    (hia : GroupInst x ra ua) (hka : ra.1.map (·.1) = RA) (hsa : Tuple.Sorted ua.1) :
    ∀ {srows : List (SRow × Term)} {sInsts : List (Tuple × Bool)},
    Pw (fun rb ub => GroupInst x rb ub ∧ rb.1.map (·.1) = SA ∧ Tuple.Sorted ub.1) srows sInsts →
    ∀ {out : List (SRow × Term)}, sJoinWith ks (RA.filter SA.contains) ra srows = .ok out →
    ∃ outI, Pw (GroupInst x) out outI ∧ (∀ rg ∈ out, rg.1.map (·.1) = joinAttrs RA SA) ∧
      (∀ ub ∈ outI, Tuple.Sorted ub.1) ∧
      presentT outI = (presentT sInsts).filterMap (joinOne ua.2 ua.1)
  | [], [], .nil, out, h => by
    rw [sJoinWith] at h; cases h; exact ⟨[], .nil, by simp, by simp, rfl⟩
  | rb :: srows, ub :: sInsts, .cons ⟨hib, hkb, hsb⟩ hl, out, h => by
    rw [sJoinWith] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    rename_i p hp
    split at h
    · cases h
    rename_i rest hrest
    cases h
    obtain ⟨restI, hpw, hk, hs, hpres⟩ := sJoinWith_sound hx hRn hSn hia hka hsa hl hrest
    have hpair := sJoinPair_sound hx hRn hSn hia hib hka hkb hsa hsb hp
    have hone : (presentT (ub :: sInsts)).filterMap (joinOne ua.2 ua.1) =
        (if ub.2 && ua.2 && ua.1.agrees ub.1 then [ua.1.merge ub.1] else []) ++
          (presentT sInsts).filterMap (joinOne ua.2 ua.1) := by
      obtain ⟨u, b⟩ := ub
      cases b
      · rw [presentT_cons_false]; simp
      · rw [presentT_cons_true, List.filterMap_cons]
        unfold joinOne
        cases hc : (ua.2 && ua.1.agrees u) <;> simp [hc]
    cases p with
    | none =>
      simp only at hpair
      refine ⟨restI, hpw, hk, hs, ?_⟩
      rw [hone, hpres, hpair]; simp
    | some rg =>
      obtain ⟨hkr, w, b, hgi, hws, hb, hwm⟩ := hpair
      refine ⟨(w, b) :: restI, .cons hgi hpw, ?_, ?_, ?_⟩
      · intro rg' hrg'
        rcases List.mem_cons.mp hrg' with rfl | hm
        · exact hkr
        · exact hk rg' hm
      · intro ub' hub'
        rcases List.mem_cons.mp hub' with rfl | hm
        · exact hws
        · exact hs ub' hm
      · rw [hone, ← hpres]
        cases hbv : b
        · have : (ub.2 && ua.2 && ua.1.agrees ub.1) = false := by
            rw [hb] at hbv; cases h1 : ub.2 <;> cases h2 : ua.2 <;> simp_all
          simp [presentT, this]
        · have : (ub.2 && ua.2 && ua.1.agrees ub.1) = true := by
            rw [hb] at hbv; cases h1 : ub.2 <;> cases h2 : ua.2 <;> simp_all
          rw [hwm hbv]; simp [presentT, this]

theorem Pw.append {α β : Type} {R : α → β → Prop} : ∀ {l l' : List α} {m m' : List β},
    Pw R l m → Pw R l' m' → Pw R (l ++ l') (m ++ m')
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons h hl, h' => .cons h (Pw.append hl h')

theorem presentT_append (l l' : List (Tuple × Bool)) : presentT (l ++ l') = presentT l ++ presentT l' := by
  simp [presentT, List.filterMap_append]

theorem filterMap_joinOne_false (ua : Tuple) (l : List Tuple) : l.filterMap (joinOne false ua) = [] := by
  induction l with
  | nil => rfl
  | cons u l ih => simp [joinOne, ih]

theorem sJoinRows_sound {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {RA SA : List String}
    (hRn : RA.Nodup) (hSn : SA.Nodup) {srows : List (SRow × Term)} {sInsts : List (Tuple × Bool)}
    (hS : Pw (fun rb ub => GroupInst x rb ub ∧ rb.1.map (·.1) = SA ∧ Tuple.Sorted ub.1) srows sInsts) :
    ∀ {rrows : List (SRow × Term)} {rInsts : List (Tuple × Bool)},
    Pw (fun ra ua => GroupInst x ra ua ∧ ra.1.map (·.1) = RA ∧ Tuple.Sorted ua.1) rrows rInsts →
    ∀ {out : List (SRow × Term)}, sJoinRows ks (RA.filter SA.contains) srows rrows = .ok out →
    ∃ outI, Pw (GroupInst x) out outI ∧ (∀ rg ∈ out, rg.1.map (·.1) = joinAttrs RA SA) ∧
      (∀ ub ∈ outI, Tuple.Sorted ub.1) ∧
      presentT outI = (presentT rInsts).flatMap fun ua => (presentT sInsts).filterMap (joinOne true ua)
  | [], [], .nil, out, h => by
    rw [sJoinRows] at h; cases h; exact ⟨[], .nil, by simp, by simp, rfl⟩
  | ra :: rrows, ua :: rInsts, .cons ⟨hia, hka, hsa⟩ hl, out, h => by
    rw [sJoinRows] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    rename_i here hhere
    split at h
    · cases h
    rename_i rest hrest
    cases h
    obtain ⟨hI, hpw1, hk1, hs1, hp1⟩ := sJoinWith_sound hx hRn hSn hia hka hsa hS hhere
    obtain ⟨rI, hpw2, hk2, hs2, hp2⟩ := sJoinRows_sound hx hRn hSn hS hl hrest
    refine ⟨hI ++ rI, Pw.append hpw1 hpw2, ?_, ?_, ?_⟩
    · intro rg hrg
      rcases List.mem_append.mp hrg with hm | hm
      · exact hk1 rg hm
      · exact hk2 rg hm
    · intro ub hub
      rcases List.mem_append.mp hub with hm | hm
      · exact hs1 ub hm
      · exact hs2 ub hm
    · rw [presentT_append, hp1, hp2]
      obtain ⟨u, b⟩ := ua
      cases b
      · simp [filterMap_joinOne_false]
      · simp

/-! ## The join -/

theorem nodup_filterMap_inj {α β : Type} {f : α → Option β} : ∀ {l : List α},
    (∀ a a' b, a ∈ l → a' ∈ l → f a = some b → f a' = some b → a = a') → l.Nodup →
    (l.filterMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hinj, hn => by
    have hn' := List.nodup_cons.mp hn
    have ih := nodup_filterMap_inj (fun a a' b ha ha' => hinj a a' b (List.mem_cons_of_mem _ ha)
      (List.mem_cons_of_mem _ ha')) hn'.2
    rw [List.filterMap_cons]
    cases hfa : f a with
    | none => exact ih
    | some b =>
      refine List.nodup_cons.mpr ⟨fun hb => ?_, ih⟩
      obtain ⟨a', ha', hfa'⟩ := List.mem_filterMap.mp hb
      have := hinj a a' b List.mem_cons_self (List.mem_cons_of_mem _ ha') hfa hfa'
      subst this; exact hn'.1 ha'


theorem Pw.map_fst' {β γ : Type} {R : String × β → String × γ → Prop} :
    ∀ {l : List (String × β)} {m : List (String × γ)}, Pw R l m → (∀ a b, R a b → b.1 = a.1) →
      m.map (·.1) = l.map (·.1)
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons h hl, hf => by
    simp only [List.map_cons, hf _ _ h, Pw.map_fst' hl hf]

theorem joinHeading_attrs {h k j : Heading} (hj : Finrel.joinHeading h k = .ok j) :
    j.attrs = joinAttrs h.attrs k.attrs := by
  simp only [Finrel.joinHeading, bind, Except.bind, pure, Except.pure] at hj
  split at hj
  · cases hj
  rename_i left hleft
  cases hj
  have hl : Heading.attrs left = h.attrs := by
    unfold Heading.attrs
    refine Pw.map_fst' (mapM_pw hleft) fun a b e => ?_
    try simp only at e
    split at e
    · split at e
      · cases e
      · cases e; rfl
    · cases e; rfl
  unfold joinAttrs
  rw [show Heading.attrs (left ++ k.filter fun p => (h.lookup p.1).isNone) =
    Heading.attrs left ++ k.attrs.filter fun c => (h.lookup c).isNone by
      simp [Heading.attrs, List.filter_map, Function.comp_def], hl]
  congr 1
  apply List.filter_congr
  intro c hc
  have hiff : (h.lookup c).isSome = true ↔ c ∈ h.attrs := Finrel.lookup_isSome
  cases h1 : (h.lookup c).isSome
  · have hnm : c ∉ h.attrs := fun hm => by rw [hiff.mpr hm] at h1; cases h1
    have hcf : (h.attrs.filter k.attrs.contains).contains c = false :=
      contains_false.mpr fun hm => hnm (List.mem_filter.mp hm).1
    have h2 : h.lookup c = Option.none := by
      cases h3 : h.lookup c with
      | none => rfl
      | some _ => rw [h3] at h1; cases h1
    rw [hcf, h2]; rfl
  · have hm := hiff.mp h1
    have hct : (h.attrs.filter k.attrs.contains).contains c = true :=
      List.contains_iff_mem.mpr (List.mem_filter.mpr ⟨hm, List.contains_iff_mem.mpr hc⟩)
    obtain ⟨v, h2⟩ := Option.isSome_iff_exists.mp h1
    rw [hct, h2]; rfl

theorem sJoin_sound {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {R S J : SRel} {r s : Finrel}
    (hR : Denotes x R r) (hS : Denotes x S s) (h : sJoin ks R S = .ok J) :
    ∃ q, r.join s = .ok q ∧ Denotes x J q := by
  obtain ⟨rI, hpr, hsr, hndr, hmr⟩ := hR.inst
  obtain ⟨sI, hps, hss, hnds, hms⟩ := hS.inst
  simp only [sJoin, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i hd hhd
  split at h
  · cases h
  rename_i out hout
  cases h
  have hR' := Pw.mono_mem hpr hR.attrs hsr
  have hS' := Pw.mono_mem hps hS.attrs hss
  obtain ⟨outI, hpw, hk, hso, hpres⟩ := sJoinRows_sound hx hR.nodup hS.nodup
    (Pw.imp (fun _ _ h => ⟨h.1, h.2.1, h.2.2⟩) hS') (Pw.imp (fun _ _ h => ⟨h.1, h.2.1, h.2.2⟩) hR') hout
  have hj : Finrel.joinHeading r.heading s.heading = .ok hd := by rw [← hR.heading, ← hS.heading]; exact hhd
  have hjoin : r.join s = .ok (Finrel.ofTuples hd (r.tuples.flatMap fun t =>
      (s.tuples.filter fun u => t.agrees u).map fun u => t.merge u)) := by
    simp [Finrel.join, hj, bind, Except.bind, pure, Except.pure]
  -- the present tuples' attributes
  have hattR : ∀ u ∈ presentT rI, AttrsOf R.heading.attrs u := by
    intro u hu
    obtain ⟨ra, hra, hgi, hka, hsa⟩ := Pw.mem_right hR' (mem_presentT.mp hu)
    have := attrsOf_inst hgi.1 hsa; rwa [hka] at this
  have hattS : ∀ u ∈ presentT sI, AttrsOf S.heading.attrs u := by
    intro u hu
    obtain ⟨rb, hrb, hgi, hkb, hsb⟩ := Pw.mem_right hS' (mem_presentT.mp hu)
    have := attrsOf_inst hgi.1 hsb; rwa [hkb] at this
  refine ⟨_, hjoin, ⟨rfl, ?_, ?_, outI, hpw, hso, ?_, ?_⟩⟩
  · exact (Finrel.joinHeading_spec hhd hR.nodup hS.nodup).1
  · intro rg hrg; rw [hk rg hrg, joinHeading_attrs hhd]
  · rw [hpres]
    refine nodup_flatMap (fun ua hua => ?_) ?_
    · refine nodup_filterMap_inj (fun ub ub' w hub hub' e e' => ?_) hnds
      simp only [joinOne, Bool.true_and] at e e'
      split at e
      · split at e'
        · rename_i h1 h2
          simp only [Option.some.injEq] at e e'
          exact (merge_inj (hattR ua hua) (hattR ua hua) (hattS ub hub) (hattS ub' hub') h1 h2
            (e.trans e'.symm)).2
        · cases e'
      · cases e
    · refine List.Pairwise.imp_of_mem ?_ hndr
      intro ua ua' hua hua' hne w hw hw'
      obtain ⟨ub, hub, e⟩ := List.mem_filterMap.mp hw
      obtain ⟨ub', hub', e'⟩ := List.mem_filterMap.mp hw'
      simp only [joinOne, Bool.true_and] at e e'
      split at e
      · split at e'
        · rename_i h1 h2
          simp only [Option.some.injEq] at e e'
          exact hne (merge_inj (hattR ua hua) (hattR ua' hua') (hattS ub hub) (hattS ub' hub') h1 h2
            (e.trans e'.symm)).1
        · cases e'
      · cases e
  · intro t
    rw [hpres, Finrel.mem_ofTuples]
    simp only [List.mem_flatMap, List.mem_filterMap, List.mem_map, List.mem_filter, hmr, hms,
      joinOne, Bool.true_and]
    constructor
    · rintro ⟨ua, hua, ub, hub, e⟩
      split at e
      · rename_i ha; cases e; exact ⟨ua, hua, ub, ⟨hub, ha⟩, rfl⟩
      · cases e
    · rintro ⟨ua, hua, ub, ⟨hub, ha⟩, rfl⟩
      exact ⟨ua, hua, ub, hub, by simp [ha]⟩

end Rasso.Phi
