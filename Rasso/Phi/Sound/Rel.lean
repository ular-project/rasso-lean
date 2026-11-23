import Rasso.Phi.Sound.Group
import Rasso.FSpace

/-!
# φ soundness: relations

A symbolic relation `R` **denotes** a finite relation `r` under an assignment `x`
(`Denotes x R r`): the same heading, with no attribute twice; every
row has the heading's attributes; every row instantiates to a well-formed tuple and every
guard to a bool; the present rows give the tuples of `r`, each once.

Then: a literal relation denotes itself (`ofFinrel_denotes`); extend, join and γ keep the
denotation (`sExtend_sound`, `sJoin_sound`, `sGamma_sound`).
-/

namespace Rasso.Phi

open Rasso

/-- `R` denotes `r` under `x` . -/
structure Denotes (x : Tuple) (R : SRel) (r : Finrel) : Prop where
  heading : R.heading = r.heading
  nodup : R.heading.attrs.Nodup
  attrs : ∀ rg ∈ R.rows, rg.1.map (·.1) = R.heading.attrs
  inst : ∃ insts : List (Tuple × Bool), Pw (GroupInst x) R.rows insts ∧
    (∀ ub ∈ insts, Tuple.Sorted ub.1) ∧ (presentT insts).Nodup ∧
    ∀ t, t ∈ presentT insts ↔ t ∈ r.tuples

/-! ## Small facts -/

theorem Pw.of_map {α γ δ : Type} {R : γ → δ → Prop} {f : α → γ} {g : α → δ} :
    ∀ {l : List α}, (∀ a ∈ l, R (f a) (g a)) → Pw R (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (Pw.of_map fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem lookup_map_key {β γ : Type} (F : String → γ) : ∀ (h : List (String × β)) (b : String),
    (h.map fun p => (p.1, F p.1)).lookup b = if b ∈ h.map (·.1) then some (F b) else none
  | [], b => by simp
  | (a, _) :: h, b => by
    by_cases hab : b = a
    · subst hab; simp
    · have : (b == a) = false := by simpa using hab
      rw [List.map_cons, List.lookup_cons, this, lookup_map_key F h b]
      simp only [List.map_cons, List.mem_cons, hab, false_or]

theorem nodup_of_eraseDups {l : List String} (h : ¬ (l.eraseDups.length != l.length) = true) :
    l.Nodup := by
  rw [← eraseDups_length_iff]; simpa using h

theorem presentT_map_true (ts : List Tuple) : presentT (ts.map (·, true)) = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [presentT, List.map_cons, List.filterMap_cons, ite_true] at ih ⊢; rw [ih]

/-! ## A literal relation -/

theorem fit_get? {h : Heading} (hn : h.attrs.Nodup) {t : Tuple} (ht : t = fitTuple h t) (a : String) :
    t.get? a = if a ∈ h.attrs then some ((t.get? a).getD default) else none := by
  have hk : ((h.map fun p => (p.1, (t.get? p.1).getD default)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def, Heading.attrs] using hn
  conv => lhs; rw [ht]
  unfold fitTuple
  rw [Tuple.get?_ofPairs hk, lookup_map_key (fun a => (t.get? a).getD default) h a]
  rfl

theorem ofFinrel_denotes {r : Finrel} {R : SRel} (h : ofFinrel r = .ok R) (x : Tuple) :
    Denotes x R r := by
  simp only [ofFinrel, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hn
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hfit
  cases h
  have hn : r.heading.attrs.Nodup := nodup_of_eraseDups (by simpa [Heading.attrs] using hn)
  have hfit : ∀ t ∈ r.tuples, t = fitTuple r.heading t := by simpa using hfit
  refine ⟨rfl, hn, ?_, r.tuples.map (·, true), ?_, ?_, ?_, ?_⟩
  · intro rg hrg
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hrg
    simp [Heading.attrs, List.map_map, Function.comp_def]
  · refine Pw.of_map fun t ht => ⟨fun a => ?_, by simp [tt, Term.eval]⟩
    have hg := fit_get? hn (hfit t ht) a
    have hl := lookup_map_key (fun a => Term.val ((t.get? a).getD default)) r.heading a
    simp only at hl ⊢
    by_cases ha : a ∈ r.heading.attrs
    · have ha' : a ∈ r.heading.map (·.1) := ha
      simp only [ha, ↓reduceIte] at hg
      simp only [ha', ↓reduceIte] at hl
      exact Or.inr ⟨_, _, hl, by simp [Term.eval], hg⟩
    · have ha' : a ∉ r.heading.map (·.1) := ha
      simp only [ha, ↓reduceIte] at hg
      simp only [ha', ↓reduceIte] at hl
      exact Or.inl ⟨hl, hg⟩
  · intro ub hub
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hub
    rw [hfit t ht]
    exact Tuple.sorted_ofPairs (by simpa [List.map_map, Function.comp_def, Heading.attrs] using hn)
  · rw [presentT_map_true]; exact Finrel.nodup_tuples r
  · intro t; rw [presentT_map_true]

/-! ## Lists in step -/

theorem Pw.of_forall2 {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {m : List β},
    Forall2 R l m → Pw R l m
  | _, _, .nil => .nil
  | _, _, .cons h hl => .cons h (Pw.of_forall2 hl)

theorem Pw.mem_left {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {m : List β},
    Pw R l m → ∀ {a}, a ∈ l → ∃ b ∈ m, R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons h1 h2, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self, h1⟩
    · obtain ⟨b, hb, hr⟩ := Pw.mem_left h2 h; exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem Pw.mem_right {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {m : List β},
    Pw R l m → ∀ {b}, b ∈ m → ∃ a ∈ l, R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons h1 h2, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self, h1⟩
    · obtain ⟨a, ha, hr⟩ := Pw.mem_right h2 h; exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- Build a third list in step with two lists that are in step with a first. -/
theorem Pw.build {α β γ δ : Type} {R : α → β → Prop} {S : α → γ → Prop} {T : β → δ → Prop}
    {U : γ → δ → Prop} (h : ∀ a b c, R a b → S a c → ∃ d, T b d ∧ U c d) :
    ∀ {l : List α} {m : List β} {n : List γ}, Pw R l m → Pw S l n →
      ∃ o, Pw T m o ∧ Pw U n o
  | [], [], [], .nil, .nil => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, _ :: _, .cons h1 hl, .cons h2 hn => by
    obtain ⟨d, ht, hu⟩ := h _ _ _ h1 h2
    obtain ⟨o, hto, huo⟩ := Pw.build h hl hn
    exact ⟨d :: o, .cons ht hto, .cons hu huo⟩

theorem Pw.mono_mem {α β : Type} {R : α → β → Prop} {P : α → Prop} {Q : β → Prop} :
    ∀ {l : List α} {m : List β}, Pw R l m → (∀ a ∈ l, P a) → (∀ b ∈ m, Q b) →
      Pw (fun a b => R a b ∧ P a ∧ Q b) l m
  | [], [], .nil, _, _ => .nil
  | _ :: _, _ :: _, .cons h hl, hp, hq =>
    .cons ⟨h, hp _ List.mem_cons_self, hq _ List.mem_cons_self⟩
      (Pw.mono_mem hl (fun a ha => hp a (List.mem_cons_of_mem _ ha))
        (fun b hb => hq b (List.mem_cons_of_mem _ hb)))

theorem mapM_pw {α β ε : Type} {f : α → Except ε β} {l : List α} {m : List β}
    (h : l.mapM f = .ok m) : Pw (fun a b => f a = .ok b) l m :=
  Pw.of_forall2 (mapM_ok.mp h)

theorem mem_presentT {t : Tuple} {insts : List (Tuple × Bool)} :
    t ∈ presentT insts ↔ (t, true) ∈ insts := by
  simp only [presentT, List.mem_filterMap]
  constructor
  · rintro ⟨⟨u, b⟩, hm, he⟩
    cases b <;> simp at he
    subst he; exact hm
  · intro hm; exact ⟨(t, true), hm, by simp⟩

/-- Present rows that change in step keep their presence. -/
theorem presentT_pw {P : Tuple → Tuple → Prop} : ∀ {insts insts' : List (Tuple × Bool)},
    Pw (fun ub ub' => ub'.2 = ub.2 ∧ P ub.1 ub'.1) insts insts' →
    Pw P (presentT insts) (presentT insts')
  | [], [], .nil => .nil
  | (u, b) :: _, (u', b') :: _, .cons ⟨hb, hp⟩ hl => by
    have ih := presentT_pw hl
    simp only at hb hp
    subst hb
    cases b' with
    | false => simpa [presentT] using ih
    | true => simp only [presentT, List.filterMap_cons, ite_true] at ih ⊢; exact .cons hp ih

/-- In-step lists under an injective relation keep "no repeats". -/
theorem Pw.nodup {α β : Type} {P : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Pw P l m →
      (∀ a c b, a ∈ l → c ∈ l → P a b → P c b → a = c) → l.Nodup → m.Nodup
  | [], [], .nil, _, _ => List.nodup_nil
  | a :: l, b :: m, .cons hab hl, hinj, hn => by
    have hn' := List.nodup_cons.mp hn
    refine List.nodup_cons.mpr ⟨fun hb => ?_, Pw.nodup hl
      (fun a c b ha hc => hinj a c b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hc)) hn'.2⟩
    obtain ⟨c, hc, hcb⟩ := Pw.mem_right hl hb
    have := hinj a c b List.mem_cons_self (List.mem_cons_of_mem _ hc) hab hcb
    subst this; exact hn'.1 hc

/-! ## Rows -/

/-- A row instantiates to a tuple without the attributes the row lacks. -/
theorem rowInst_get?_none {x : Tuple} {row : SRow} {u : Tuple} (hu : RowInst x row u) {a : String}
    (ha : a ∉ row.map (·.1)) : u.get? a = Option.none := by
  apply hu.none
  cases h : row.lookup a with
  | none => rfl
  | some t => exact absurd (List.mem_map_of_mem (f := (·.1)) (lookup_mem h)) ha

theorem not_mem_keys_of_get? {u : Tuple} {a : String} (h : u.get? a = Option.none) :
    a ∉ u.map (·.1) := by
  intro hm
  have := lookup_isSome_iff_mem hm
  simp only [Tuple.get?] at h; rw [h] at this; cases this

theorem rowInst_append_one {x : Tuple} {row : SRow} {u : Tuple} (hu : RowInst x row u)
    {res : String} (hres : res ∉ row.map (·.1)) {s : Term} {v : Value} (hs : s.eval x = .ok v)
    (hsort : Tuple.Sorted u) :
    RowInst x (row ++ [(res, s)]) (Tuple.ofPairs ((res, v) :: u)) := by
  have hnone := rowInst_get?_none hu hres
  have hk : (((res, v) :: u).map (·.1)).Nodup :=
    List.nodup_cons.mpr ⟨not_mem_keys_of_get? hnone, Tuple.nodup_keys hsort⟩
  intro a
  rw [Tuple.get?_ofPairs hk]
  by_cases har : a = res
  · subst har
    have hrl : row.lookup a = Option.none := by
      cases h : row.lookup a with
      | none => rfl
      | some t => exact absurd (List.mem_map_of_mem (f := (·.1)) (lookup_mem h)) hres
    have hL : (row ++ [(a, s)]).lookup a = some s := by
      rw [List.lookup_append, hrl]; simp [List.lookup]
    have hR : ((a, v) :: u).lookup a = some v := by simp [List.lookup]
    rw [hL, hR]
    exact Or.inr ⟨s, v, rfl, hs, rfl⟩
  · have hne : (a == res) = false := by simpa using har
    have hL : (row ++ [(res, s)]).lookup a = row.lookup a := by
      rw [List.lookup_append]
      cases row.lookup a with
      | none => simp [List.lookup, hne]
      | some _ => rfl
    have hR : ((res, v) :: u).lookup a = u.lookup a := by simp [List.lookup, hne]
    rw [hL, hR]
    exact hu a

theorem ofPairs_cons_inj {res : String} {v w : Value} {u u' : Tuple} (hu : Tuple.Sorted u)
    (hu' : Tuple.Sorted u') (hn : u.get? res = none) (hn' : u'.get? res = none)
    (h : Tuple.ofPairs ((res, v) :: u) = Tuple.ofPairs ((res, w) :: u')) : u = u' := by
  have hk : (((res, v) :: u).map (·.1)).Nodup :=
    List.nodup_cons.mpr ⟨not_mem_keys_of_get? hn, Tuple.nodup_keys hu⟩
  have hk' : (((res, w) :: u').map (·.1)).Nodup :=
    List.nodup_cons.mpr ⟨not_mem_keys_of_get? hn', Tuple.nodup_keys hu'⟩
  refine Tuple.ext_get? hu hu' fun a => ?_
  by_cases har : a = res
  · subst har; rw [hn, hn']
  · have e := congrArg (Tuple.get? · a) h
    simp only [Tuple.get?_ofPairs hk, Tuple.get?_ofPairs hk'] at e
    have : (a == res) = false := by simpa using har
    simpa [List.lookup, this, Tuple.get?] using e

/-! ## extend -/

theorem sExtend_sound {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {res : String} {t : Term}
    {R R' : SRel} {r : Finrel} (hR : Denotes x R r) (h : sExtend ks res t R = .ok R') :
    ∃ r', r.extend res t = .ok r' ∧ Denotes x R' r' := by
  obtain ⟨insts, hpw, hsorted, hnd, hmem⟩ := hR.inst
  unfold sExtend at h
  by_cases hres : res ∈ R.heading.attrs
  · simp [hres, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  cases hdom : t.domain R.heading with
  | none => simp [hres, hdom, throw, throwThe, MonadExceptOf.throw] at h
  | some d =>
  simp only [List.contains_iff_mem, hres, hdom, ↓reduceIte, bind, Except.bind,
    pure, Except.pure] at h
  split at h
  · cases h
  rename_i rows' hrows'
  cases h
  have hres' : res ∉ R.heading.attrs := hres
  have hstep : Pw (fun rg rg' => ∃ s, sEval ks rg.1 t = .ok s ∧ rg' = (rg.1 ++ [(res, s)], rg.2))
      R.rows rows' := by
    refine Pw.imp (fun rg rg' e => ?_) (mapM_pw hrows')
    try simp only at e
    split at e
    · cases e
    · rename_i s hs; cases e; exact ⟨s, hs, rfl⟩
  have hpw' := Pw.mono_mem hpw (fun rg hrg => hR.attrs rg hrg) hsorted
  let P : Tuple → Tuple → Prop := fun u u' => Tuple.Sorted u ∧ u.get? res = Option.none ∧
    ∃ v, t.eval u = .ok v ∧ u' = Tuple.ofPairs ((res, v) :: u)
  obtain ⟨insts', hT, hU⟩ := Pw.build (T := GroupInst x)
    (U := fun ub ub' => ub'.2 = ub.2 ∧ P ub.1 ub'.1)
    (fun rg rg' ub hrr ⟨hgi, hka, hso⟩ => by
      obtain ⟨s, hs, rfl⟩ := hrr
      obtain ⟨v, hv⟩ := sEval_ok hx hgi.1 t hs
      have hvu : t.eval ub.1 = .ok v := by rw [← sEval_sound hgi.1 t hs]; exact hv
      have hresk : res ∉ rg.1.map (·.1) := by rw [hka]; exact hres'
      exact ⟨(Tuple.ofPairs ((res, v) :: ub.1), ub.2),
        ⟨rowInst_append_one hgi.1 hresk hv hso, hgi.2⟩,
        rfl, hso, rowInst_get?_none hgi.1 hresk, v, hvu, rfl⟩) hstep hpw'
  have hP := presentT_pw hU
  -- the concrete side
  have hall : ∀ u ∈ r.tuples, ∃ t', ∃ v, t.eval u = .ok v ∧ t' = Tuple.ofPairs ((res, v) :: u) := by
    intro u hu
    obtain ⟨u', _, hPu⟩ := Pw.mem_left hP ((hmem u).mpr hu)
    obtain ⟨_, _, v, hv, _⟩ := hPu
    exact ⟨_, v, hv, rfl⟩
  obtain ⟨ts, hts⟩ := Forall2.of_forall hall
  have hext : r.extend res t = .ok (Finrel.ofTuples (r.heading ++ [(res, d)]) ts) :=
    Finrel.extend_eq_ok.mpr ⟨by rw [Finrel.attrs, ← hR.heading]; exact hres',
      d, by rw [← hR.heading]; exact hdom, ts, hts.imp fun u t' ⟨v, hv, e⟩ => ⟨v, hv, e⟩, rfl⟩
  refine ⟨_, hext, ⟨by simp [hR.heading, Finrel.ofTuples], ?_, ?_, insts', hT, ?_, ?_, ?_⟩⟩
  · simp only [Heading.attrs, List.map_append, List.map_cons, List.map_nil]
    exact List.nodup_append.mpr ⟨hR.nodup, by simp, fun a ha b hb e => by
      simp at hb; subst hb; subst e; exact hres' ha⟩
  · intro rg' hrg'
    obtain ⟨rg, hrg, s, _, rfl⟩ := Pw.mem_right hstep hrg'
    simp [hR.attrs rg hrg, Heading.attrs]
  · intro ub' hub'
    obtain ⟨ub, _, _, hso, hn, v, _, he⟩ := Pw.mem_right hU hub'
    rw [he]
    exact Tuple.sorted_ofPairs (List.nodup_cons.mpr ⟨not_mem_keys_of_get? hn, Tuple.nodup_keys hso⟩)
  · refine Pw.nodup hP (fun a c b _ _ ha hc => ?_) hnd
    obtain ⟨hsa, hna, va, _, ea⟩ := ha
    obtain ⟨hsc, hnc, vc, _, ec⟩ := hc
    exact ofPairs_cons_inj hsa hsc hna hnc (ea.symm.trans ec)
  · intro t'
    rw [Finrel.mem_ofTuples]
    constructor
    · intro ht'
      obtain ⟨u, hu, _, _, v, hv, rfl⟩ := Pw.mem_right hP ht'
      obtain ⟨t'', ht'', v', hv', rfl⟩ := hts.mem_left ((hmem u).mp hu)
      rw [hv] at hv'; cases hv'; exact ht''
    · intro ht'
      obtain ⟨u, hu, v, hv, rfl⟩ := hts.mem_right ht'
      obtain ⟨t'', ht'', _, _, v', hv', rfl⟩ := Pw.mem_left hP ((hmem u).mpr hu)
      rw [hv] at hv'; cases hv'; exact ht''

end Rasso.Phi
