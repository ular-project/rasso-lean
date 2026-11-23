import Rasso.Phi.Sound.Agg

/-!
# φ soundness: the order of a group does not matter

φ lists a group's rows in its own order; Lean's evaluator lists the group's tuples in the
canonical order. The two lists hold the same tuples (5c shows it), so the aggregates must
not depend on the order. `aggregate_perm`: an aggregate that gives a value on one order
gives the same value on any other. `sum` by commutativity, `bool_and`/`bool_or`/`count`
plainly, `all_different` because "no duplicate" does not depend on the order, and `min`/`max`
because `Value.cmp` ties only equal values when there is no float (φ has none).
-/

namespace Rasso.Phi

open Rasso

/-! ## `mapM` over a permutation -/

theorem mapM_cons_ok {α β ε : Type} {f : α → Except ε β} {a : α} {l : List α} {vs : List β}
    (h : (a :: l).mapM f = .ok vs) : ∃ b bs, f a = .ok b ∧ l.mapM f = .ok bs ∧ vs = b :: bs := by
  simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i b hb
    split at h
    · cases h
    · rename_i bs hbs
      cases h; exact ⟨b, bs, hb, hbs, rfl⟩

theorem mapM_cons_of {α β ε : Type} {f : α → Except ε β} {a : α} {l : List α} {b : β} {bs : List β}
    (hb : f a = .ok b) (hbs : l.mapM f = .ok bs) : (a :: l).mapM f = .ok (b :: bs) := by
  simp [List.mapM_cons, hb, hbs, bind, Except.bind, pure, Except.pure]

theorem mapM_perm {α β ε : Type} {f : α → Except ε β} {l l' : List α} (p : l.Perm l') :
    ∀ {vs : List β}, l.mapM f = .ok vs → ∃ vs', l'.mapM f = .ok vs' ∧ vs.Perm vs' := by
  induction p with
  | nil => intro vs h; cases h; exact ⟨[], rfl, .nil⟩
  | cons x _ ih =>
    intro vs h
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_ok h
    obtain ⟨bs', h', hp⟩ := ih hbs
    exact ⟨b :: bs', mapM_cons_of hb h', hp.cons b⟩
  | swap x y l =>
    intro vs h
    obtain ⟨c, cs, hc, hcs, rfl⟩ := mapM_cons_ok h
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_ok hcs
    exact ⟨b :: c :: bs, mapM_cons_of hb (mapM_cons_of hc hbs), .swap b c bs⟩
  | trans _ _ ih1 ih2 =>
    intro vs h
    obtain ⟨vs1, h1, p1⟩ := ih1 h
    obtain ⟨vs2, h2, p2⟩ := ih2 h1
    exact ⟨vs2, h2, p1.trans p2⟩

theorem mapM_cons_some {α β : Type} {f : α → Option β} {a : α} {l : List α} {vs : List β}
    (h : (a :: l).mapM f = some vs) : ∃ b bs, f a = some b ∧ l.mapM f = some bs ∧ vs = b :: bs := by
  rw [List.mapM_cons] at h
  cases hb : f a with
  | none => simp [hb] at h
  | some b =>
    cases hbs : l.mapM f with
    | none => simp [hb, hbs] at h
    | some bs => simp [hb, hbs] at h; exact ⟨b, bs, rfl, rfl, h.symm⟩

theorem mapM_cons_of_some {α β : Type} {f : α → Option β} {a : α} {l : List α} {b : β} {bs : List β}
    (hb : f a = some b) (hbs : l.mapM f = some bs) : (a :: l).mapM f = some (b :: bs) := by
  simp [List.mapM_cons, hb, hbs]

/-- The same for `Option` (`allInts`). -/
theorem mapM_perm_opt {α β : Type} {f : α → Option β} {l l' : List α} (p : l.Perm l') :
    ∀ {vs : List β}, l.mapM f = some vs → ∃ vs', l'.mapM f = some vs' ∧ vs.Perm vs' := by
  induction p with
  | nil => intro vs h; cases h; exact ⟨[], rfl, .nil⟩
  | cons x _ ih =>
    intro vs h
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_some h
    obtain ⟨bs', h', hp⟩ := ih hbs
    exact ⟨b :: bs', mapM_cons_of_some hb h', hp.cons b⟩
  | swap x y l =>
    intro vs h
    obtain ⟨c, cs, hc, hcs, rfl⟩ := mapM_cons_some h
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_some hcs
    exact ⟨b :: c :: bs, mapM_cons_of_some hb (mapM_cons_of_some hc hbs), .swap b c bs⟩
  | trans _ _ ih1 ih2 =>
    intro vs h
    obtain ⟨vs1, h1, p1⟩ := ih1 h
    obtain ⟨vs2, h2, p2⟩ := ih2 h1
    exact ⟨vs2, h2, p1.trans p2⟩

theorem mapM_none_perm_opt {α β : Type} {f : α → Option β} {l l' : List α} (p : l.Perm l')
    (h : l.mapM f = none) : l'.mapM f = none := by
  cases h' : l'.mapM f with
  | none => rfl
  | some vs =>
    obtain ⟨_, h2, _⟩ := mapM_perm_opt p.symm h'
    rw [h] at h2; cases h2

/-! ## `all`, `any`, sums -/

theorem perm_all {l l' : List Bool} (p : l.Perm l') : l.all id = l'.all id := by
  cases h : l.all id <;> cases h' : l'.all id <;> try rfl
  · rw [List.all_eq_true] at h'
    have : l.all id = true := List.all_eq_true.mpr fun b hb => h' b (p.mem_iff.mp hb)
    rw [h] at this; cases this
  · rw [List.all_eq_true] at h
    have : l'.all id = true := List.all_eq_true.mpr fun b hb => h b (p.mem_iff.mpr hb)
    rw [h'] at this; cases this

theorem perm_any {l l' : List Bool} (p : l.Perm l') : l.any id = l'.any id := by
  cases h : l.any id <;> cases h' : l'.any id <;> try rfl
  · rw [List.any_eq_true] at h'
    obtain ⟨b, hb, hb'⟩ := h'
    have : l.any id = true := List.any_eq_true.mpr ⟨b, p.mem_iff.mpr hb, hb'⟩
    rw [h] at this; cases this
  · rw [List.any_eq_true] at h
    obtain ⟨b, hb, hb'⟩ := h
    have : l'.any id = true := List.any_eq_true.mpr ⟨b, p.mem_iff.mp hb, hb'⟩
    rw [h'] at this; cases this

theorem perm_sum_int {l l' : List Int} (p : l.Perm l') :
    l.foldl (· + ·) 0 = l'.foldl (· + ·) 0 :=
  p.foldl_eq' (fun x _ y _ z => by rw [Int.add_assoc, Int.add_assoc, Int.add_comm x]) 0

theorem perm_sum_rat {l l' : List Rat} (p : l.Perm l') :
    l.foldl (· + ·) 0 = l'.foldl (· + ·) 0 :=
  p.foldl_eq' (fun x _ y _ z => by rw [Rat.add_assoc, Rat.add_assoc, Rat.add_comm x]) 0

theorem arith_sum_perm {who : String} {vs vs' : List Value} (p : vs.Perm vs') {w : Value}
    (h : arith who (·.foldl (· + ·) 0) (·.foldl (· + ·) 0) vs = .ok w) :
    arith who (·.foldl (· + ·) 0) (·.foldl (· + ·) 0) vs' = .ok w := by
  unfold arith at h ⊢
  cases h1 : allInts vs with
  | some ns =>
    have h1' := h1; unfold allInts at h1'
    obtain ⟨ns', h2, pn⟩ := mapM_perm_opt p h1'
    have h2' : allInts vs' = some ns' := h2
    simp only [h2', h1, pure, Except.pure] at h ⊢
    rw [← perm_sum_int pn]; exact h
  | none =>
    have h1' := h1; unfold allInts at h1'
    have h2 : allInts vs' = none := mapM_none_perm_opt p h1'
    simp only [h2, h1, bind, Except.bind, pure, Except.pure] at h ⊢
    split at h
    · cases h
    · rename_i qs hqs
      obtain ⟨qs', hqs', pq⟩ := mapM_perm p hqs
      rw [hqs']; simp only
      rw [← perm_sum_rat pq]; exact h

/-! ## `all_different`: no duplicate -/

theorem length_eraseDups_le {α : Type} [BEq α] [LawfulBEq α] : ∀ (l : List α), l.eraseDups.length ≤ l.length
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    have := length_eraseDups_le (as.filter fun b => !b == a)
    have := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons]; omega
termination_by l => l.length
decreasing_by simp only [List.length_cons]; have := List.length_filter_le (fun b => !b == a) as; omega

theorem eraseDups_length_iff {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), l.eraseDups.length = l.length ↔ l.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons, List.nodup_cons]
    have ih := eraseDups_length_iff (as.filter fun b => !b == a)
    have h1 := length_eraseDups_le (as.filter fun b => !b == a)
    have h2 := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons, Nat.add_right_cancel_iff]
    constructor
    · intro h
      have hf : (as.filter fun b => !b == a).length = as.length := by omega
      have hf' := List.length_filter_eq_length_iff.mp hf
      have hfa : as.filter (fun b => !b == a) = as := List.filter_eq_self.mpr hf'
      refine ⟨fun ha => ?_, ?_⟩
      · have := hf' a ha; simp at this
      · rw [← hfa]; exact ih.mp (by omega)
    · rintro ⟨ha, hn⟩
      have hfa : as.filter (fun b => !b == a) = as := List.filter_eq_self.mpr fun b hb => by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
        rintro rfl; exact ha hb
      rw [hfa] at ih ⊢; exact ih.mpr hn
termination_by l => l.length
decreasing_by simp only [List.length_cons]; have := List.length_filter_le (fun b => !b == a) as; omega

theorem all_different_perm {vs vs' : List Value} (p : vs.Perm vs') :
    (vs.eraseDups.length == vs.length) = (vs'.eraseDups.length == vs'.length) := by
  have h1 := eraseDups_length_iff vs
  have h2 := eraseDups_length_iff vs'
  have h3 := p.nodup_iff
  cases hv : (vs.eraseDups.length == vs.length) <;> cases hv' : (vs'.eraseDups.length == vs'.length) <;>
    simp_all

/-! ## `min` and `max` -/

theorem cmp_self (v : Value) : Value.cmp v v = .eq := by
  have := Std.OrientedCmp.eq_swap (cmp := Value.cmp) (a := v) (b := v)
  cases h : Value.cmp v v <;> simp_all [Ordering.swap]

/-- Ties under `Value.cmp` are equal values, when neither is a float. -/
theorem cmp_eq_of_notFloat {v w : Value} (hv : v.isFloat = false) (hw : w.isFloat = false)
    (h : Value.cmp v w = .eq) : v = w := by
  unfold Value.cmp at h
  rw [compareLex_eq_eq, compareLex_eq_eq] at h
  obtain ⟨_, h2, h3⟩ := h
  have e2 : v.num? = w.num? := Std.LawfulEqCmp.eq_of_compare (cmp := compare) h2
  have e3 : v.nonNumKey = w.nonNumKey := Std.LawfulEqCmp.eq_of_compare (cmp := compare) h3
  cases v <;> cases w <;> simp_all [Value.isFloat, Value.num?, Value.exact?, Value.nonNumKey]
  all_goals first
    | (have hk := Value.key_inj e3; simp_all)
    | (subst e2; exact (‹Rat.den _ ≠ 1›) rfl)

theorem cmp_ne_trans {o : Ordering} (ho : o ≠ .eq) {a b c : Value}
    (h1 : Value.cmp a b ≠ o) (h2 : Value.cmp b c ≠ o) : Value.cmp a c ≠ o := by
  cases o
  · have g1 : (Value.cmp a b).isGE := by cases h : Value.cmp a b <;> simp_all [Ordering.isGE]
    have g2 : (Value.cmp b c).isGE := by cases h : Value.cmp b c <;> simp_all [Ordering.isGE]
    have := Std.TransCmp.isGE_trans g1 g2
    intro h; rw [h] at this; simp [Ordering.isGE] at this
  · exact absurd rfl ho
  · have g1 : (Value.cmp a b).isLE := by cases h : Value.cmp a b <;> simp_all [Ordering.isLE]
    have g2 : (Value.cmp b c).isLE := by cases h : Value.cmp b c <;> simp_all [Ordering.isLE]
    have := Std.TransCmp.isLE_trans g1 g2
    intro h; rw [h] at this; simp [Ordering.isLE] at this

theorem cmp_swap_ne {o : Ordering} (ho : o ≠ .eq) {a b : Value} (h : Value.cmp a b = o) :
    Value.cmp b a ≠ o := by
  rw [Std.OrientedCmp.eq_swap (cmp := Value.cmp), h]
  cases o <;> simp_all [Ordering.swap]

/-- `min`'s and `max`'s fold (`o` is `.lt` for `min`, `.gt` for `max`): its result is one of
the values, and no value is beyond it. -/
theorem foldl_pick_spec {o : Ordering} (ho : o ≠ .eq) : ∀ (ws : List Value) (v : Value),
    (ws.foldl (fun m w => if Value.cmp w m == o then w else m) v = v ∨
      ws.foldl (fun m w => if Value.cmp w m == o then w else m) v ∈ ws) ∧
    ∀ y ∈ v :: ws, Value.cmp y (ws.foldl (fun m w => if Value.cmp w m == o then w else m) v) ≠ o
  | [], v => by
    refine ⟨Or.inl rfl, fun y hy => ?_⟩
    simp at hy; subst hy; simp only [List.foldl_nil]; rw [cmp_self]; exact fun h => ho h.symm
  | w :: ws, v => by
    simp only [List.foldl_cons]
    generalize hm : (if Value.cmp w v == o then w else v) = m
    obtain ⟨ih1, ih2⟩ := foldl_pick_spec ho ws m
    have hmv : m = v ∨ m = w := by
      rw [← hm]; split <;> simp
    have hy : ∀ y, y = v ∨ y = w → Value.cmp y m ≠ o := by
      intro y hy'
      rw [← hm]
      split
      · rename_i hc
        have hc : Value.cmp w v = o := by simpa using hc
        rcases hy' with rfl | rfl
        · exact cmp_swap_ne ho hc
        · rw [cmp_self]; exact fun h => ho h.symm
      · rename_i hc
        have hc : Value.cmp w v ≠ o := by simpa using hc
        rcases hy' with rfl | rfl
        · rw [cmp_self]; exact fun h => ho h.symm
        · exact hc
    refine ⟨?_, fun y hy' => ?_⟩
    · rcases ih1 with h | h
      · rw [h]; rcases hmv with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by simp [h'])
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · simp only [List.mem_cons] at hy'
      rcases hy' with rfl | rfl | h
      · exact cmp_ne_trans ho (hy _ (Or.inl rfl)) (ih2 m (by simp))
      · exact cmp_ne_trans ho (hy _ (Or.inr rfl)) (ih2 m (by simp))
      · exact ih2 y (List.mem_cons_of_mem _ h)

theorem pick_perm {o : Ordering} (ho : o ≠ .eq) {v v' : Value} {ws ws' : List Value}
    (p : (v :: ws).Perm (v' :: ws')) (hf : ∀ u ∈ v :: ws, u.isFloat = false) :
    ws.foldl (fun m w => if Value.cmp w m == o then w else m) v =
      ws'.foldl (fun m w => if Value.cmp w m == o then w else m) v' := by
  obtain ⟨m1, s1⟩ := foldl_pick_spec ho ws v
  obtain ⟨m2, s2⟩ := foldl_pick_spec ho ws' v'
  generalize ws.foldl (fun m w => if Value.cmp w m == o then w else m) v = r at m1 s1
  generalize ws'.foldl (fun m w => if Value.cmp w m == o then w else m) v' = r' at m2 s2
  have hr : r ∈ v :: ws := by rcases m1 with rfl | h <;> simp_all
  have hr' : r' ∈ v :: ws := p.mem_iff.mpr (by rcases m2 with rfl | h <;> simp_all)
  have a1 := s1 r' hr'
  have a2 := s2 r (p.mem_iff.mp hr)
  apply cmp_eq_of_notFloat (hf r hr) (hf r' hr')
  rw [Std.OrientedCmp.eq_swap (cmp := Value.cmp)] at a1
  cases h : Value.cmp r r' <;> cases o <;> simp_all [Ordering.swap]

/-! ## Aggregates -/

/-- An aggregate that gives a value gives the same value on any order of its operands
(`min` and `max` when there is no float). -/
theorem aggregate_perm {op : String} {vs vs' : List Value} (p : vs.Perm vs')
    (hf : aggName op = "min" ∨ aggName op = "max" → ∀ v ∈ vs, v.isFloat = false) {w : Value}
    (h : aggregate op vs = .ok w) : aggregate op vs' = .ok w := by
  unfold aggregate at h ⊢
  split at h
  all_goals first
    | (simp [throw, throwThe, MonadExceptOf.throw] at h; done)
    | (rename_i hop; simp only [hop]; rw [← p.length_eq]; exact h)
    | (rename_i hop; simp only [hop]; exact arith_sum_perm p h)
    | (rename_i hop; simp only [hop]
       simp only [bind, Except.bind, pure, Except.pure] at h ⊢
       split at h
       · cases h
       · rename_i u hu; rw [arith_sum_perm p hu]; exact h)
    | (rename_i hop; simp only [hop]
       simp only [bind, Except.bind, pure, Except.pure] at h ⊢
       split at h
       · cases h
       · rename_i bs hbs
         obtain ⟨bs', h', pb⟩ := mapM_perm p hbs
         rw [h']; simp only; rw [← perm_all pb]; exact h)
    | (rename_i hop; simp only [hop]
       simp only [bind, Except.bind, pure, Except.pure] at h ⊢
       split at h
       · cases h
       · rename_i bs hbs
         obtain ⟨bs', h', pb⟩ := mapM_perm p hbs
         rw [h']; simp only; rw [← perm_any pb]; exact h)
    | (rename_i hop; simp only [hop]; rw [← all_different_perm p]; exact h)
    | (rename_i v ws hop
       cases vs' with
       | nil => exact absurd p.length_eq (by simp)
       | cons v' ws' =>
         simp only [hop]
         first
           | (rw [← pick_perm (o := .lt) (by decide) p (hf (.inl hop))]; exact h)
           | (rw [← pick_perm (o := .gt) (by decide) p (hf (.inr hop))]; exact h))

end Rasso.Phi
