import Rasso.Phi.Sound.Join

/-!
# φ soundness: γ

`sGamma_sound`: if `R` denotes `r`, the symbolic γ denotes `Finrel.gamma`'s result, which
does not refuse. The symbolic side groups by decided keys (every row's key is decided, or φ
refuses); a key whose rows are all absent gives a row whose guard is false. The present
rows of a group are, as a set, the concrete group, so the aggregate agrees (5b).
-/

namespace Rasso.Phi

open Rasso

/-! ## Built terms evaluate -/

theorem sApply_ok {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {op : String} {args : List Term}
    {s : Term} (h : sApply ks op args = .ok s) : ∃ w, s.eval x = .ok w := by
  unfold sApply at h
  split at h
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i v _; cases h; exact ⟨v, by simp [Term.eval]⟩
  · exact mk_sound hx h

theorem mapM_mk_ok {x : Tuple} {α : Type} {f : α → Except String Term}
    (hf : ∀ a s, f a = .ok s → ∃ w, s.eval x = .ok w) :
    ∀ {l : List α} {ss : List Term}, l.mapM f = .ok ss → ∀ s ∈ ss, ∃ w, s.eval x = .ok w
  | [], ss, h => by simp [pure, Except.pure] at h; subst h; simp
  | a :: l, ss, h => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_ok h
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hf a s hb
    · exact mapM_mk_ok hf hbs s hs

theorem sAgg_ok {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {op : String} {vs gs : List Term}
    {s : Term} (h : sAgg ks op vs gs = .ok s) : ∃ w, s.eval x = .ok w := by
  unfold sAgg at h
  dsimp only at h
  split at h
  · split at h
    · cases h; exact ⟨Value.int vs.length, by simp [Term.eval]⟩
    · simp only [bind, Except.bind] at h
      split at h
      · cases h
      · exact mk_sound hx h
  all_goals try (simp only [bind, Except.bind] at h; split at h; · cases h
                 exact mk_sound hx h)
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (first | exact mk_sound hx h | (cases h; done) | split at h)

theorem sAggEval_ok {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {key : SRow} {keyT : Tuple}
    (hkey : RowInst x key keyT) {group : List (SRow × Term)} :
    ∀ (e : Agg) {s : Term}, sAggEval ks key group e = .ok s → ∃ w, s.eval x = .ok w
  | .agg op t, s, h => by
    rw [sAggEval] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · exact sAgg_ok hx h
  | .attr a, s, h => by
    rw [sAggEval] at h
    split at h
    · rename_i t ht; cases h
      obtain ⟨v, hv, _⟩ := hkey.some ht
      exact ⟨v, hv⟩
    · cases h
  | .val v, s, h => by
    rw [sAggEval] at h; cases h; exact ⟨v, by simp [Term.eval]⟩
  | .call op args, s, h => by
    rw [sAggEval] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · exact sApply_ok hx h
  | .hasSubset r, s, h => by
    cases r with
    | omegaRows hd rows =>
      rw [sAggEval] at h
      simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      repeat' (first | exact mk_sound hx h | (cases h; done) | split at h)
    | _ => rw [sAggEval] at h <;> first | cases h | (intro _ _ hr; cases hr)

/-! ## Lists -/

theorem forIn_yield {α : Type} {f : α → PUnit → Except String (ForInStep PUnit)} :
    ∀ {l : List α}, (∀ a ∈ l, f a PUnit.unit = .ok (.yield PUnit.unit)) →
      forIn l PUnit.unit f = .ok PUnit.unit
  | [], _ => rfl
  | a :: l, h => by
    rw [List.forIn_cons, h a List.mem_cons_self]
    exact forIn_yield fun b hb => h b (List.mem_cons_of_mem _ hb)

theorem forIn_of_ok {α : Type} {f : α → PUnit → Except String (ForInStep PUnit)}
    (hf : ∀ a, (∃ e, f a PUnit.unit = .error e) ∨ f a PUnit.unit = .ok (.yield PUnit.unit)) :
    ∀ {l : List α} {u : PUnit}, forIn l PUnit.unit f = .ok u →
      ∀ a ∈ l, f a PUnit.unit = .ok (.yield PUnit.unit)
  | [], _, _ => by simp
  | a :: l, u, h => by
    rw [List.forIn_cons] at h
    rcases hf a with ⟨e, he⟩ | hy
    · rw [he] at h; cases h
    · rw [hy] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hy
      · exact forIn_of_ok hf h b hb

theorem nodup_eraseDups_le {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons, List.nodup_cons]
    have hl := List.length_filter_le (fun b => !b == a) as
    simp only [List.length_cons] at h
    refine ⟨fun hm => ?_, nodup_eraseDups_le n _ (by omega)⟩
    have := List.mem_eraseDups.mp hm
    simp at this

theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup :=
  nodup_eraseDups_le _ l (Nat.le_refl _)

theorem mapM_exists {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ b, f a = .ok b) → ∃ bs, l.mapM f = .ok bs
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨bs, hbs⟩ := mapM_exists (l := l) fun c hc => h c (List.mem_cons_of_mem _ hc)
    exact ⟨b :: bs, by simp [List.mapM_cons, hb, hbs, bind, Except.bind, pure, Except.pure]⟩

theorem mapM_ok_of {α β ε : Type} {f g : α → Except ε β} :
    ∀ {l : List α} {bs : List β}, l.mapM g = .ok bs → (∀ a b, g a = .ok b → f a = .ok b) →
      l.mapM f = .ok bs
  | [], bs, h, _ => h
  | a :: l, bs, h, hfg => by
    obtain ⟨b, bs', hb, hbs, rfl⟩ := mapM_cons_ok h
    simp [List.mapM_cons, hfg a b hb, mapM_ok_of hbs hfg, bind, Except.bind, pure, Except.pure]

theorem mapM_err {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {e : ε}, l.mapM f = .error e → ∃ a ∈ l, ∀ b, f a ≠ .ok b
  | [], e, h => by simp [pure, Except.pure] at h
  | a :: l, e, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · exact ⟨a, List.mem_cons_self, fun b hb => by simp_all⟩
    · split at h
      · rename_i e' he
        obtain ⟨c, hc, hn⟩ := mapM_err he
        exact ⟨c, List.mem_cons_of_mem _ hc, hn⟩
      · cases h

theorem Pw.comp {α β γ : Type} {A : α → β → Prop} {B : α → γ → Prop} :
    ∀ {l : List α} {m : List β} {n : List γ}, Pw A l m → Pw B l n →
      Pw (fun b c => ∃ a, A a b ∧ B a c) m n
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h1 hl, .cons h2 hn => .cons ⟨_, h1, h2⟩ (Pw.comp hl hn)

theorem Pw.filter_both {α β : Type} {P : α → β → Prop} {p : α → Bool} {q : β → Bool}
    (hpq : ∀ a b, P a b → p a = q b) :
    ∀ {l : List α} {m : List β}, Pw P l m → Pw P (l.filter p) (m.filter q)
  | [], [], .nil => .nil
  | a :: _, b :: _, .cons h hl => by
    simp only [List.filter_cons, hpq a b h]
    split
    · exact .cons h (Pw.filter_both hpq hl)
    · exact Pw.filter_both hpq hl

theorem Pw.map_left {α β γ : Type} {R : β → γ → Prop} {F : α → β} :
    ∀ {l : List α} {m : List γ}, Pw (fun a c => R (F a) c) l m → Pw R (l.map F) m
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hl => .cons h (Pw.map_left hl)

theorem presentT_filter (q : Tuple → Bool) : ∀ (l : List (Tuple × Bool)),
    presentT (l.filter fun ub => q ub.1) = (presentT l).filter q
  | [] => rfl
  | (u, b) :: l => by
    have ih := presentT_filter q l
    cases hq : q u <;> cases b <;> simp_all [presentT]

theorem presentT_nodup_of_pw {α : Type} {Q : α → Tuple × Bool → Prop}
    (hinj : ∀ a a' u, Q a (u, true) → Q a' (u, true) → a = a') :
    ∀ {l : List α} {m : List (Tuple × Bool)}, Pw Q l m → l.Nodup → (presentT m).Nodup
  | [], [], .nil, _ => List.nodup_nil
  | a :: l, (u, b) :: m, .cons h hl, hn => by
    have hn' := List.nodup_cons.mp hn
    have ih := presentT_nodup_of_pw hinj hl hn'.2
    cases b
    · simpa [presentT] using ih
    · simp only [presentT, List.filterMap_cons, ite_true] at ih ⊢
      refine List.nodup_cons.mpr ⟨fun hu => ?_, ih⟩
      obtain ⟨a', ha', hq⟩ := Pw.mem_right hl (mem_presentT.mp hu)
      exact hn'.1 (hinj a a' u h hq ▸ ha')

theorem any_snd_iff (l : List (Tuple × Bool)) : l.any (·.2) = true ↔ ∃ t, t ∈ presentT l := by
  simp only [List.any_eq_true, mem_presentT]
  constructor
  · rintro ⟨⟨u, b⟩, hm, hb⟩; simp at hb; subst hb; exact ⟨u, hm⟩
  · rintro ⟨u, hm⟩; exact ⟨(u, true), hm, rfl⟩

/-! ## Keys -/

theorem keys_spec {f : String → Except String (String × Value)} {row : SRow}
    (hf : ∀ a p, f a = .ok p → p.1 = a ∧ row.lookup a = some (.val p.2)) :
    ∀ {l : List String} {k : List (String × Value)}, l.mapM f = .ok k →
      k.map (·.1) = l ∧ ∀ p ∈ k, row.lookup p.1 = some (.val p.2)
  | [], k, h => by simp [pure, Except.pure] at h; subst h; simp
  | a :: l, k, h => by
    obtain ⟨p, ps, hp, hps, rfl⟩ := mapM_cons_ok h
    obtain ⟨h1, h2⟩ := hf a p hp
    obtain ⟨ih1, ih2⟩ := keys_spec hf hps
    refine ⟨by simp [h1, ih1], fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [h1]; exact h2
    · exact ih2 q hq

/-- The key of a tuple: its values of `by_`, in that order. -/
def keyOfT (by_ : List String) (u : Tuple) : List (String × Value) :=
  by_.map fun a => (a, (u.get? a).getD default)

theorem key_eq_keyOfT {u : Tuple} : ∀ {k : List (String × Value)},
    (∀ p ∈ k, u.get? p.1 = some p.2) → k = keyOfT (k.map (·.1)) u
  | [], _ => rfl
  | (a, v) :: k, h => by
    have ha := h (a, v) List.mem_cons_self
    have ih := key_eq_keyOfT (k := k) fun p hp => h p (List.mem_cons_of_mem _ hp)
    simp only [keyOfT, List.map_cons] at ih ⊢
    rw [← ih]; simp [ha]

theorem lookup_none_of_not_mem {β : Type} {a : String} {l : List (String × β)}
    (h : a ∉ l.map (·.1)) : l.lookup a = Option.none := by
  cases hl : l.lookup a with
  | none => rfl
  | some _ => exact absurd (List.mem_map_of_mem (f := (·.1)) (lookup_mem hl)) h

theorem ofPairs_key {u : Tuple} {k : List (String × Value)} (hu : Tuple.Sorted u)
    (hn : (k.map (·.1)).Nodup) (hk : ∀ p ∈ k, u.get? p.1 = some p.2) :
    Tuple.ofPairs k = u.restrict (k.map (·.1)) := by
  refine Tuple.ext_get? (Tuple.sorted_ofPairs hn) (hu.sublist List.filter_sublist) fun a => ?_
  rw [Tuple.get?_ofPairs hn]
  unfold Tuple.restrict Tuple.get?
  rw [lookup_filter_key]
  by_cases ha : a ∈ k.map (·.1)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    rw [lookup_of_mem hn hp]
    simp only [List.contains_iff_mem.mpr ha, ↓reduceIte]
    exact (hk p hp).symm
  · rw [lookup_none_of_not_mem ha, contains_false.mpr ha]; rfl

theorem rowInst_key {x : Tuple} {k : List (String × Value)} (hn : (k.map (·.1)).Nodup) :
    RowInst x (k.map fun p => (p.1, Term.val p.2)) (Tuple.ofPairs k) := by
  intro a
  have e := lookup_map_keyed (fun _ v => Term.val v) k a
  try simp only at e
  rw [e, Tuple.get?_ofPairs hn]
  cases k.lookup a with
  | none => exact .inl ⟨rfl, rfl⟩
  | some v => exact .inr ⟨.val v, v, rfl, by simp [Term.eval], rfl⟩

theorem keyOfT_map (by_ : List String) (u : Tuple) : (keyOfT by_ u).map (·.1) = by_ := by
  simp [keyOfT, Function.comp_def]

theorem keyOfT_iff {A by_ : List String} {t : Tuple} (ht : AttrsOf A t) (hsub : ∀ a ∈ by_, a ∈ A)
    {k : List (String × Value)} (hk : k.map (·.1) = by_) (hn : by_.Nodup) :
    keyOfT by_ t = k ↔ t.restrict by_ = Tuple.ofPairs k := by
  constructor
  · rintro rfl
    have hget : ∀ p ∈ keyOfT by_ t, t.get? p.1 = some p.2 := by
      intro p hp
      simp only [keyOfT, List.mem_map] at hp
      obtain ⟨a, ha, rfl⟩ := hp
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((ht.2 a).mpr (hsub a ha))
      simp [hv]
    have := ofPairs_key ht.1 (by rw [keyOfT_map]; exact hn) hget
    rw [keyOfT_map] at this
    exact this.symm
  · intro e
    have hnk : (k.map (·.1)).Nodup := hk ▸ hn
    have hget : ∀ p ∈ k, t.get? p.1 = some p.2 := by
      intro p hp
      have h1 : (t.restrict by_).get? p.1 = some p.2 := by
        rw [e, Tuple.get?_ofPairs hnk]; exact lookup_of_mem hnk hp
      have hpb : p.1 ∈ by_ := hk ▸ List.mem_map_of_mem hp
      unfold Tuple.restrict Tuple.get? at h1
      rw [lookup_filter_key] at h1
      simp only [List.contains_iff_mem.mpr hpb, ↓reduceIte] at h1
      exact h1
    have := key_eq_keyOfT hget
    rw [hk] at this
    exact this.symm

theorem Pw.refl' {α : Type} : ∀ (l : List α), Pw (fun a b => b = a) l l
  | [] => .nil
  | _ :: l => .cons rfl (Pw.refl' l)

theorem pw_fst {β : Type} : ∀ {l : List String} {m : List (String × β)},
    Pw (fun a b => b.1 = a) l m → m.map (·.1) = l
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hl => by simp [h, pw_fst hl]

/-- A group's guard: whether some row of the group is present. -/
theorem guard_or {ks : Kinds} {x : Tuple} {grp : List (SRow × Term)} {ins : List (Tuple × Bool)}
    (hG : Pw (GroupInst x) grp ins) {g : Term} (h : sApply ks "or" (grp.map (·.2)) = .ok g) :
    g.eval x = .ok (.bool (ins.any (·.2))) := by
  have hm : ∀ {grp : List (SRow × Term)} {ins : List (Tuple × Bool)}, Pw (GroupInst x) grp ins →
      (grp.map (·.2)).mapM (Term.eval x) = .ok ((ins.map (·.2)).map .bool) := by
    intro grp ins hG
    induction hG with
    | nil => rfl
    | cons h _ ih =>
      simp only [List.map_cons, List.mapM_cons, h.2, ih, bind, Except.bind, pure, Except.pure]
  rw [sApply_sound h x, hm hG]
  simp only [bind, Except.bind]
  have := applyOp_andor_bools false (ins.map (·.2))
  simp only [opName, boolSem, Bool.false_eq_true, ↓reduceIte] at this
  rw [this]
  simp [List.any_map, Function.comp_def]

/-- One γ group: the symbolic group's present rows are the concrete group, and the
expression agrees. -/
theorem gamma_group {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {by_ : List String} {ex : Agg}
    {keyed : List (List (String × Value) × SRow × Term)} {insts : List (Tuple × Bool)} {r : Finrel}
    (hKI : Pw (fun kr ub => GroupInst x kr.2 ub ∧ kr.1 = keyOfT by_ ub.1) keyed insts)
    (hnd : (presentT insts).Nodup) (hmem : ∀ t, t ∈ presentT insts ↔ t ∈ r.tuples)
    (hkiff : ∀ t ∈ r.tuples, ∀ k : List (String × Value), k.map (·.1) = by_ →
      (keyOfT by_ t = k ↔ t.restrict by_ = Tuple.ofPairs k))
    {k : List (String × Value)} (hk : k.map (·.1) = by_) (hn : by_.Nodup) {s : Term}
    (hs : sAggEval ks (k.map fun p => (p.1, Term.val p.2))
      ((keyed.filter fun kr => kr.1 == k).map fun kr => (kr.2.1, kr.2.2)) ex = .ok s) :
    ∃ w, s.eval x = .ok w ∧
      Agg.eval (Tuple.ofPairs k) (r.tuples.filter fun t => t.restrict by_ == Tuple.ofPairs k) ex = .ok w ∧
      Pw (GroupInst x) ((keyed.filter fun kr => kr.1 == k).map fun kr => (kr.2.1, kr.2.2))
        (insts.filter fun ub => keyOfT by_ ub.1 == k) ∧
      ∀ t, t ∈ presentT (insts.filter fun ub => keyOfT by_ ub.1 == k) ↔
        t ∈ r.tuples ∧ keyOfT by_ t = k := by
  have hnk : (k.map (·.1)).Nodup := hk ▸ hn
  have hG : Pw (GroupInst x) ((keyed.filter fun kr => kr.1 == k).map fun kr => (kr.2.1, kr.2.2))
      (insts.filter fun ub => keyOfT by_ ub.1 == k) := by
    refine Pw.map_left (Pw.imp (fun kr ub h => h.1) (Pw.filter_both (fun kr ub h => ?_) hKI))
    rw [h.2]
  have hpres : ∀ t, t ∈ presentT (insts.filter fun ub => keyOfT by_ ub.1 == k) ↔
      t ∈ r.tuples ∧ keyOfT by_ t = k := by
    intro t
    rw [presentT_filter (fun u => keyOfT by_ u == k), List.mem_filter, hmem]
    simp
  obtain ⟨w, hw⟩ := sAggEval_ok hx (rowInst_key (x := x) hnk) ex hs
  have hperm : (presentT (insts.filter fun ub => keyOfT by_ ub.1 == k)).Perm
      (r.tuples.filter fun t => t.restrict by_ == Tuple.ofPairs k) := by
    rw [List.perm_ext_iff_of_nodup]
    · intro t
      rw [hpres, List.mem_filter]
      constructor
      · rintro ⟨ht, e⟩; exact ⟨ht, by simpa using (hkiff t ht k hk).mp e⟩
      · rintro ⟨ht, e⟩; exact ⟨ht, (hkiff t ht k hk).mpr (by simpa using e)⟩
    · rw [presentT_filter (fun u => keyOfT by_ u == k)]
      exact hnd.sublist List.filter_sublist
    · exact (Finrel.nodup_tuples r).sublist List.filter_sublist
  exact ⟨w, hw, sAggEval_sound hx (rowInst_key hnk) hG hperm ex hs hw, hG, hpres⟩

/-! ## γ -/

theorem sGamma_sound {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {by_ : List String} {ex : Agg}
    {res : String} {R G : SRel} {r : Finrel}
    (hR : Denotes x R r) (h : sGamma ks by_ ex res R = .ok G) :
    ∃ g, r.gamma by_ ex res = .ok g ∧ Denotes x G g := by
  obtain ⟨insts, hpw, hsorted, hnd, hmem⟩ := hR.inst
  have hdom : r.domainOf? = fun a => List.lookup a R.heading := by
    funext a; simp [Finrel.domainOf?, hR.heading]
  unfold sGamma at h
  unfold Finrel.gamma
  rw [hdom, ← hR.heading]
  simp only [bind, Except.bind] at h ⊢
  split at h
  · cases h
  rename_i u hfor
  have hby : ∀ a ∈ by_, (R.heading.lookup a).isNone = false := by
    have := forIn_of_ok (fun a => by
      cases hl : (R.heading.lookup a).isNone
      · exact .inr (by simp [pure, Except.pure])
      · exact .inl ⟨_, by simp only [↓reduceIte]; rfl⟩) hfor
    intro a ha
    have h1 := this a ha
    cases hl : (R.heading.lookup a).isNone
    · rfl
    · simp [hl, throw, throwThe, MonadExceptOf.throw] at h1
  rw [forIn_yield (fun a ha => by simp [hby a ha, pure, Except.pure])]
  cases hc : by_.contains res
  case true => simp only [hc, ↓reduceIte, throw, throwThe, MonadExceptOf.throw] at h; cases h
  cases hdup : (by_.eraseDups.length != by_.length)
  case true =>
    simp only [hc, hdup, Bool.false_eq_true, ↓reduceIte, throw, throwThe, MonadExceptOf.throw] at h
    cases h
  simp only [hc, hdup, Bool.false_eq_true, ↓reduceIte] at h ⊢
  split at h
  · cases h
  cases hd : ex.domain R.heading
  case none =>
    simp only [hd, throw, throwThe, MonadExceptOf.throw] at h
    cases h
  rename_i d
  simp only [hd] at h ⊢
  split at h
  · cases h
  rename_i hh hhh
  rw [mapM_ok_of hhh (fun a p e => by
    split at e
    · cases e; rename_i heq; simp [heq]
    · cases e)]
  simp only
  split at h
  · cases h
  rename_i keyed hkeyed
  split at h
  · cases h
  rename_i out hout
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  -- the checks
  have hbn : by_.Nodup := (eraseDups_length_iff by_).mp (by simpa using hdup)
  have hres : res ∉ by_ := by simpa using hc
  have hsub : ∀ a ∈ by_, a ∈ R.heading.attrs := fun a ha =>
    Finrel.lookup_isSome.mp (by simpa using hby a ha)
  have hhb : hh.map (·.1) = by_ :=
    pw_fst (Pw.imp (fun a p e => by
      revert e; split
      · intro e; cases e; rfl
      · intro e; cases e) (mapM_pw hhh))
  -- each row's key
  have hkpw : Pw (fun rg kr => kr.2 = rg ∧ kr.1.map (·.1) = by_ ∧
      ∀ p ∈ kr.1, rg.1.lookup p.1 = some (.val p.2)) R.rows keyed := by
    refine Pw.imp (fun rg kr e => ?_) (mapM_pw hkeyed)
    split at e
    · cases e
    · rename_i k hk
      cases e
      obtain ⟨h1, h2⟩ := keys_spec (fun a p e => by
        revert e; split
        · intro e; cases e; rename_i heq; exact ⟨rfl, heq⟩
        · intro e; cases e
        · intro e; cases e) hk
      exact ⟨rfl, h1, h2⟩
  have hR' := Pw.mono_mem hpw hR.attrs hsorted
  have hKI0 := Pw.comp hkpw hR'
  have hKI : Pw (fun kr ub => GroupInst x kr.2 ub ∧ kr.1 = keyOfT by_ ub.1) keyed insts := by
    refine Pw.imp (fun kr ub ⟨rg, ⟨e1, e2, e3⟩, hgi, _, _⟩ => ?_) hKI0
    subst e1
    refine ⟨hgi, ?_⟩
    have hget : ∀ p ∈ kr.1, ub.1.get? p.1 = some p.2 := by
      intro p hp
      obtain ⟨v, hv, hg⟩ := hgi.1.some (e3 p hp)
      simp [Term.eval] at hv; subst hv; exact hg
    have := key_eq_keyOfT hget
    rwa [e2] at this
  have hattR : ∀ t ∈ r.tuples, AttrsOf R.heading.attrs t := by
    intro t ht
    obtain ⟨rg, hrg, hgi, hka, hsa⟩ := Pw.mem_right hR' (mem_presentT.mp ((hmem t).mpr ht))
    have := attrsOf_inst hgi.1 hsa; rwa [hka] at this
  have hkiff : ∀ t ∈ r.tuples, ∀ k : List (String × Value), k.map (·.1) = by_ →
      (keyOfT by_ t = k ↔ t.restrict by_ = Tuple.ofPairs k) :=
    fun t ht k hk => keyOfT_iff (hattR t ht) hsub hk hbn
  -- the symbolic keys
  generalize hkP : (if by_.isEmpty = true then [[]] else (List.map (fun x => x.fst) keyed).eraseDups)
    = keysP at hout
  have hkeys : ∀ k ∈ keysP, k.map (·.1) = by_ := by
    intro k hk
    rw [← hkP] at hk
    split at hk
    · rename_i he
      simp at hk he; subst hk; simp [he]
    · obtain ⟨kr, hkr, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hk)
      obtain ⟨rg, _, _, h2, _⟩ := Pw.mem_right hkpw hkr
      exact h2
  have hkPn : keysP.Nodup := by
    rw [← hkP]; split
    · simp
    · exact nodup_eraseDups _
  have hnone : ∀ k ∈ keysP, (Tuple.ofPairs k).get? res = Option.none := by
    intro k hk
    have hn : (k.map (·.1)).Nodup := (hkeys k hk) ▸ hbn
    rw [Tuple.get?_ofPairs hn]
    exact lookup_none_of_not_mem (by rw [hkeys k hk]; exact hres)
  -- each group's row and its instance
  let U : List (String × Value) → Tuple × Bool → Prop := fun k ub =>
    ∃ w, ub.1 = Tuple.ofPairs ((res, w) :: Tuple.ofPairs k) ∧
      Agg.eval (Tuple.ofPairs k) (r.tuples.filter fun t => t.restrict by_ == Tuple.ofPairs k) ex = .ok w ∧
      (ub.2 = true ↔ (by_ = [] ∨ ∃ t, t ∈ r.tuples ∧ keyOfT by_ t = k))
  obtain ⟨outI, hT, hU⟩ := Pw.build
    (T := fun row ub => GroupInst x row ub ∧ Tuple.Sorted ub.1 ∧ row.1.map (·.1) = by_ ++ [res])
    (U := U)
    (fun k row k' ⟨e, hk, _⟩ hk' => by
      subst k'
      have hkb := hkeys k hk
      have hnk : (k.map (·.1)).Nodup := hkb ▸ hbn
      try simp only at e
      split at e
      · cases e
      rename_i s hs
      obtain ⟨w, hw, hagg, hG, hpres⟩ := gamma_group hx hKI hnd hmem hkiff hkb hbn hs
      have hresk : res ∉ (k.map fun p => (p.1, Term.val p.2)).map (·.1) := by
        simp only [List.map_map]; rw [show ((·.1) ∘ fun p : String × Value => (p.1, Term.val p.2))
          = (·.1) from rfl, hkb]; exact hres
      have hri := rowInst_append_one (rowInst_key (x := x) hnk) hresk hw (Tuple.sorted_ofPairs hnk)
      have hso : Tuple.Sorted (Tuple.ofPairs ((res, w) :: Tuple.ofPairs k)) := by
        refine Tuple.sorted_ofPairs (List.nodup_cons.mpr ⟨not_mem_keys_of_get? (hnone k hk),
          Tuple.nodup_keys (Tuple.sorted_ofPairs hnk)⟩)
      have hattr : ((k.map fun p => (p.1, Term.val p.2)) ++ [(res, s)]).map (·.1) = by_ ++ [res] := by
        simp [Function.comp_def]; exact hkb
      split at e
      · rename_i hemp
        simp only [pure, Except.pure, Except.ok.injEq] at e
        subst e
        have hb : by_ = [] := by simpa using hemp
        refine ⟨(Tuple.ofPairs ((res, w) :: Tuple.ofPairs k), true), ⟨⟨hri, by simp [tt, Term.eval]⟩, hso, hattr⟩,
          w, rfl, hagg, by simp [hb]⟩
      · rename_i hemp
        try simp only at e
        split at e
        · cases e
        rename_i g hg
        simp only [pure, Except.pure, Except.ok.injEq] at e
        subst e
        have hb : by_ ≠ [] := by simpa using hemp
        have hge := guard_or hG hg
        refine ⟨(Tuple.ofPairs ((res, w) :: Tuple.ofPairs k), _), ⟨⟨hri, hge⟩, hso, hattr⟩,
          w, rfl, hagg, ?_⟩
        simp only [hb, false_or]
        rw [any_snd_iff]
        constructor
        · rintro ⟨t, ht⟩; exact ⟨t, (hpres t).mp ht⟩
        · rintro ⟨t, ht⟩; exact ⟨t, (hpres t).mpr ht⟩)
    (Pw.mono_mem (Q := fun _ => True) (mapM_pw hout) (fun k hk => hk) (fun _ _ => trivial))
    (Pw.refl' keysP)
  -- the concrete keys, against the symbolic ones
  have hof0 : Tuple.ofPairs [] = [] := by simp [Tuple.ofPairs]
  have hF : ∀ kF ∈ (if by_.isEmpty = true then [[]] else (r.tuples.map (·.restrict by_)).eraseDups),
      ∃ k ∈ keysP, kF = Tuple.ofPairs k ∧ (by_ = [] ∨ ∃ t, t ∈ r.tuples ∧ keyOfT by_ t = k) := by
    intro kF hkF
    split at hkF
    · rename_i he
      have hb : by_ = [] := by simpa using he
      simp at hkF; subst hkF
      refine ⟨[], ?_, hof0.symm, .inl hb⟩
      rw [← hkP]; simp [he]
    · rename_i he
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hkF)
      obtain ⟨kr, hkr, _, hkt⟩ := Pw.mem_right hKI (mem_presentT.mp ((hmem t).mpr ht))
      refine ⟨keyOfT by_ t, ?_, (hkiff t ht _ (keyOfT_map by_ t)).mp rfl, .inr ⟨t, ht, rfl⟩⟩
      rw [← hkP]; simp only [he, Bool.false_eq_true, ↓reduceIte]
      exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨kr, hkr, hkt⟩)
  have hP : ∀ k ∈ keysP, (by_ = [] ∨ ∃ t, t ∈ r.tuples ∧ keyOfT by_ t = k) →
      Tuple.ofPairs k ∈ (if by_.isEmpty = true then [[]] else (r.tuples.map (·.restrict by_)).eraseDups) := by
    intro k hk hc
    by_cases hb : by_ = []
    · have : k = [] := by
        have := hkeys k hk; rw [hb] at this; exact List.map_eq_nil_iff.mp this
      subst this; subst hb; simp [hof0]
    · obtain ⟨t, ht, hkt⟩ := hc.resolve_left hb
      have hbe : by_.isEmpty = false := by simpa using hb
      simp only [hbe, Bool.false_eq_true, ↓reduceIte]
      exact List.mem_eraseDups.mpr (List.mem_map.mpr ⟨t, ht,
        ((hkiff t ht k (hkeys k hk)).mp hkt)⟩)
  split
  · rename_i e he
    exfalso
    obtain ⟨kF, hkF, hne⟩ := mapM_err he
    obtain ⟨k, hk, rfl, hc⟩ := hF kF hkF
    obtain ⟨ub, _, w, _, hagg, _⟩ := Pw.mem_left hU hk
    exact hne (Tuple.ofPairs ((res, w) :: Tuple.ofPairs k)) (by simp [hagg, pure, Except.pure])
  rename_i ts hts
  refine ⟨_, rfl, ⟨rfl, ?_, ?_, outI, Pw.imp (fun _ _ h => h.1) hT, fun ub hub => ?_, ?_, ?_⟩⟩
  · simp only [Heading.attrs, List.map_append, List.map_cons, List.map_nil]
    rw [show hh.map (·.1) = by_ from hhb]
    exact List.nodup_append.mpr ⟨hbn, by simp, by simpa using fun a ha (e : a = res) => hres (e ▸ ha)⟩
  · intro rg hrg
    obtain ⟨ub, _, _, _, h3⟩ := Pw.mem_left hT hrg
    rw [h3]; simp [Heading.attrs, hhb]
  · obtain ⟨rg, _, _, h2, _⟩ := Pw.mem_right hT hub
    exact h2
  · have hkk : ∀ k ∈ keysP, k = keyOfT by_ (Tuple.ofPairs k) := by
      intro k hk
      have hnk : (k.map (·.1)).Nodup := (hkeys k hk) ▸ hbn
      have := key_eq_keyOfT (u := Tuple.ofPairs k) fun p hp => by
        rw [Tuple.get?_ofPairs hnk]; exact lookup_of_mem hnk hp
      rwa [hkeys k hk] at this
    refine presentT_nodup_of_pw (fun k k' u ⟨⟨w, e, _⟩, hk, _⟩ ⟨⟨w', e', _⟩, hk', _⟩ => ?_)
      (Pw.mono_mem (P := (· ∈ keysP)) (Q := fun _ => True) hU (fun k hk => hk) (fun _ _ => trivial)) hkPn
    have hnk : (k.map (·.1)).Nodup := (hkeys k hk) ▸ hbn
    have hnk' : (k'.map (·.1)).Nodup := (hkeys k' hk') ▸ hbn
    have := ofPairs_cons_inj (Tuple.sorted_ofPairs hnk) (Tuple.sorted_ofPairs hnk') (hnone k hk)
      (hnone k' hk') (e.symm.trans e')
    rw [hkk k hk, hkk k' hk', this]
  · intro t
    rw [Finrel.mem_ofTuples, mem_presentT]
    have hpts := mapM_pw hts
    constructor
    · intro ht
      obtain ⟨k, hk, w, e, hagg, hc⟩ := Pw.mem_right hU ht
      have hkF := hP k hk (hc.mp rfl)
      obtain ⟨t', ht', ef⟩ := Pw.mem_left hpts hkF
      simp only [hagg, pure, Except.pure, Except.ok.injEq] at ef
      simp only at e
      rw [e, ef]; exact ht'
    · intro ht
      obtain ⟨kF, hkF, ef⟩ := Pw.mem_right hpts ht
      obtain ⟨k, hk, rfl, hc⟩ := hF kF hkF
      obtain ⟨ub, hub, w, e, hagg, hb⟩ := Pw.mem_left hU hk
      simp only [hagg, pure, Except.pure, Except.ok.injEq] at ef
      have : ub = (t, true) := by
        rcases ub with ⟨u, b⟩
        simp only at e hb
        rw [e, ← ef, hb.mpr hc]
      rw [← this]; exact hub
