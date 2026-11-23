import Rasso.Eval

/-!
# Rasso: membership lemmas

What the operators of the finite algebra and the solution sets compute, stated as
membership. Each lemma about an operator that can refuse takes the operator's success
(`= .ok s`) as a hypothesis, and says which tuples `s` has.

Conventions:

* Membership is stated for `Finrel.tuples` (the canonical list), so it holds whatever
  order the operator built its list in.
* A refused operation says nothing here. When an operator is not refused is not stated here.
-/

namespace Rasso

/-! ## Bodies -/

namespace Body

theorem mem_iff {t : Tuple} {b : Body} : b.mem t = true ↔ t ∈ b.toList := by
  simp [Body.mem]

@[simp] theorem mem_ofList {t : Tuple} {l : List Tuple} :
    (Body.ofList l).mem t = true ↔ t ∈ l := by
  rw [mem_iff, mem_toList_ofList]

@[simp] theorem not_mem_empty (t : Tuple) : Body.empty.mem t = false := by
  have h : ¬ (Body.empty.mem t = true) := by simp [Body.empty]
  simpa using h

@[simp] theorem mem_adjoin {t u : Tuple} {b : Body} :
    (b.adjoin u).mem t = true ↔ t = u ∨ b.mem t = true := by
  simp only [Body.adjoin, mem_iff, mem_toList_ofList, List.mem_cons]

/-- Two bodies with the same members are equal: the body is a set. -/
theorem ext {b c : Body} (h : ∀ t, t ∈ b.toList ↔ t ∈ c.toList) : b = c := by
  rw [← ofList_toList b, ← ofList_toList c]
  exact Quotient.sound h

end Body

/-! ## Monadic filtering in `Except` -/

theorem filterAuxM_mem {p : Tuple → Except String Bool} :
    ∀ {l acc res : List Tuple}, List.filterAuxM p l acc = .ok res →
      ∀ x, x ∈ res ↔ x ∈ acc ∨ (x ∈ l ∧ p x = .ok true)
  | [], acc, res, h, x => by
    simp only [List.filterAuxM, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | y :: l, acc, res, h, x => by
    simp only [List.filterAuxM, bind, Except.bind] at h
    cases hy : p y with
    | error e => rw [hy] at h; cases h
    | ok b =>
      rw [hy] at h
      have ih := filterAuxM_mem h x
      rw [ih]
      cases b <;> simp only [Bool.cond_false, Bool.cond_true, List.mem_cons] <;> constructor
      · rintro (h1 | ⟨h2, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨Or.inr h2, h3⟩
      · rintro (h1 | ⟨h2 | h2, h3⟩)
        · exact Or.inl h1
        · subst h2; rw [hy] at h3; cases h3
        · exact Or.inr ⟨h2, h3⟩
      · rintro ((h1 | h1) | ⟨h2, h3⟩)
        · subst h1; exact Or.inr ⟨Or.inl rfl, hy⟩
        · exact Or.inl h1
        · exact Or.inr ⟨Or.inr h2, h3⟩
      · rintro (h1 | ⟨h2 | h2, h3⟩)
        · exact Or.inl (Or.inr h1)
        · exact Or.inl (Or.inl h2)
        · exact Or.inr ⟨h2, h3⟩

theorem filterM_mem {p : Tuple → Except String Bool} {l res : List Tuple}
    (h : l.filterM p = .ok res) (x : Tuple) : x ∈ res ↔ x ∈ l ∧ p x = .ok true := by
  simp only [List.filterM, bind, Except.bind] at h
  cases ha : List.filterAuxM p l [] with
  | error e => rw [ha] at h; cases h
  | ok r =>
    rw [ha] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [List.mem_reverse, filterAuxM_mem ha x]
    simp

/-! ## Dropping repeats -/

theorem length_eraseDups_le {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), l.eraseDups.length ≤ l.length
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons, List.length_cons, List.length_cons]
    have := length_eraseDups_le (as.filter fun b => !b == a)
    have := List.length_filter_le (fun b => !b == a) as
    omega
termination_by l => l.length
decreasing_by simp only [List.length_cons]; have := List.length_filter_le (fun b => !b == a) as; omega

/-- `eraseDups` drops nothing exactly when there is nothing to drop. -/
theorem length_eraseDups_eq {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), l.eraseDups.length = l.length ↔ l.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons, List.length_cons, List.length_cons, List.nodup_cons]
    have h1 := length_eraseDups_le (as.filter fun b => !b == a)
    have h2 := List.length_filter_le (fun b => !b == a) as
    have ih := length_eraseDups_eq (as.filter fun b => !b == a)
    constructor
    · intro h
      have hf : (as.filter fun b => !b == a).length = as.length := by omega
      have hall := List.length_filter_eq_length_iff.mp hf
      refine ⟨fun ha => by simpa using hall a ha, ?_⟩
      have : as.filter (fun b => !b == a) = as := List.filter_eq_self.mpr hall
      rw [← this]; exact ih.mp (by omega)
    · rintro ⟨ha, hn⟩
      have : as.filter (fun b => !b == a) = as := List.filter_eq_self.mpr fun b hb => by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
        exact fun e => ha (e ▸ hb)
      rw [this] at ih ⊢
      rw [ih.mpr hn]
termination_by l => l.length
decreasing_by simp only [List.length_cons]; omega

/-! ## The finite algebra -/

namespace Finrel

@[simp] theorem mem_ofTuples {h : Heading} {ts : List Tuple} {t : Tuple} :
    t ∈ (ofTuples h ts).tuples ↔ t ∈ ts := Body.mem_toList_ofList

theorem mem_select {p : Tuple → Except String Bool} {r s : Finrel}
    (h : r.select p = .ok s) (t : Tuple) :
    t ∈ s.tuples ↔ t ∈ r.tuples ∧ p t = .ok true := by
  simp only [select, bind, Except.bind] at h
  cases hf : r.tuples.filterM p with
  | error e => rw [hf] at h; cases h
  | ok ts =>
    rw [hf] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [mem_ofTuples, filterM_mem hf]

theorem select_heading {p : Tuple → Except String Bool} {r s : Finrel}
    (h : r.select p = .ok s) : s.heading = r.heading := by
  simp only [select, bind, Except.bind] at h
  cases hf : r.tuples.filterM p with
  | error e => rw [hf] at h; cases h
  | ok ts =>
    rw [hf] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl

/-- π once its names are known to differ: what `project` does after that check. -/
def projectCore (as : List String) (r : Finrel) : Except String Finrel := do
  let h ← as.mapM fun a => match r.domainOf? a with
    | some d => .ok (a, d)
    | none => .error s!"π: no attribute {a} in {r.attrs}"
  return ofTuples h (r.tuples.map (·.restrict as))

theorem project_eq (as : List String) (r : Finrel) :
    r.project as = if as.eraseDups.length != as.length
      then .error s!"π: {as} names an attribute twice" else projectCore as r := by
  unfold project projectCore
  split <;> rfl

theorem project_core {as : List String} {r s : Finrel} (h : r.project as = .ok s) :
    as.Nodup ∧ projectCore as r = .ok s := by
  rw [project_eq] at h
  split at h
  · cases h
  · rename_i hn
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hn
    exact ⟨(length_eraseDups_eq as).mp hn, h⟩

theorem mem_project {as : List String} {r s : Finrel}
    (h : r.project as = .ok s) (t : Tuple) :
    t ∈ s.tuples ↔ ∃ u ∈ r.tuples, t = u.restrict as := by
  replace h := (project_core h).2
  simp only [projectCore, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [mem_ofTuples, List.mem_map]
    exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩, fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩⟩

theorem mem_join {r s q : Finrel} (h : r.join s = .ok q) (t : Tuple) :
    t ∈ q.tuples ↔ ∃ u ∈ r.tuples, ∃ v ∈ s.tuples, u.agrees v = true ∧ t = u.merge v := by
  simp only [join, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [mem_ofTuples, List.mem_flatMap, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨u, hu, v, ⟨hv, ha⟩, e⟩; exact ⟨u, hu, v, hv, ha, e.symm⟩
    · rintro ⟨u, hu, v, hv, ha, e⟩; exact ⟨u, hu, v, ⟨hv, ha⟩, e.symm⟩

theorem mem_union {r s q : Finrel} (h : r.union s = .ok q) (t : Tuple) :
    t ∈ q.tuples ↔ t ∈ r.tuples ∨ t ∈ s.tuples := by
  simp only [union, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp

theorem mem_diff {r s q : Finrel} (h : r.diff s = .ok q) (t : Tuple) :
    t ∈ q.tuples ↔ t ∈ r.tuples ∧ t ∉ s.tuples := by
  simp only [diff, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [mem_ofTuples, List.mem_filter]
    simp only [Bool.not_eq_true', tuples]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h3 => by rw [← Body.mem_iff] at h3; rw [h3] at h2; cases h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      cases h3 : s.body.mem t
      · rfl
      · exact absurd (Body.mem_iff.mp h3) h2

end Finrel

/-! ## Choices: one item from each list -/

/-- `Picks l xss`: `l` takes one item from each list of `xss`, in order. -/
inductive Picks {α : Type} : List α → List (List α) → Prop
  | nil : Picks [] []
  | cons {x : α} {xs : List α} {l : List α} {xss : List (List α)} :
      x ∈ xs → Picks l xss → Picks (x :: l) (xs :: xss)

theorem mem_choices {α : Type} : ∀ {xss : List (List α)} {l : List α},
    l ∈ choices xss ↔ Picks l xss
  | [], l => by
    simp only [choices, List.mem_singleton]
    constructor
    · rintro rfl; exact .nil
    · intro h; cases h; rfl
  | xs :: xss, l => by
    simp only [choices, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨x, hx, l', hl', rfl⟩
      exact .cons hx (mem_choices.mp hl')
    · intro h
      cases h with
      | cons hx hp => exact ⟨_, hx, _, mem_choices.mpr hp, rfl⟩

/-- There are as many choices as the product of the lists' lengths (|X|^|D| when every
list is X). -/
theorem length_choices {α : Type} : ∀ (xss : List (List α)),
    (choices xss).length = (xss.map List.length).foldr (· * ·) 1
  | [] => rfl
  | xs :: xss => by
    simp only [choices, List.length_flatMap, List.length_map, length_choices xss,
      List.map_cons, List.foldr_cons]
    induction xs with
    | nil => simp
    | cons _ _ ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-! ## Except helpers

Small facts about `mapM`, `filterM` and checking loops in the `Except` monad, used to say
when an operator is refused. `Forall2 R l ys` says `ys` is `l` with each item replaced by
one `R` relates it to (Mathlib's `List.Forall₂`, which core Lean lacks).
-/


inductive Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 R [] []
  | cons {x : α} {y : β} {xs : List α} {ys : List β} :
      R x y → Forall2 R xs ys → Forall2 R (x :: xs) (y :: ys)

theorem mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = .ok ys ↔ Forall2 (fun x y => f x = .ok y) l ys
  | [], ys => by
    rw [List.mapM_nil]
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; rfl
  | x :: l, ys => by
    rw [List.mapM_cons]
    cases hx : f x with
    | error e =>
      constructor
      · intro h; cases h
      · intro h
        cases h with
        | cons h1 _ => rw [hx] at h1; cases h1
    | ok y =>
      cases hl : l.mapM f with
      | error e =>
        constructor
        · intro h; simp only [bind, Except.bind] at h; cases h
        · intro h
          cases h with
          | cons _ h2 => have := mapM_ok.mpr h2; rw [hl] at this; cases this
      | ok zs =>
        have ih := (mapM_ok (l := l) (ys := zs)).mp hl
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
        constructor
        · rintro rfl; exact .cons hx ih
        · intro h
          cases h with
          | cons h1 h2 =>
            rw [hx] at h1; cases h1
            have := mapM_ok.mpr h2; rw [hl] at this; cases this; rfl

theorem Forall2.mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {ys : List β}, Forall2 R l ys → ∀ {y}, y ∈ ys → ∃ x ∈ l, R x y
  | _, _, .nil, _, h => by cases h
  | _, _, .cons h1 h2, _, h => by
    cases List.mem_cons.mp h with
    | inl e => subst e; exact ⟨_, List.mem_cons_self, h1⟩
    | inr e => obtain ⟨x, hx, r⟩ := h2.mem_right e; exact ⟨x, List.mem_cons_of_mem _ hx, r⟩

theorem Forall2.mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {ys : List β}, Forall2 R l ys → ∀ {x}, x ∈ l → ∃ y ∈ ys, R x y
  | _, _, .nil, _, h => by cases h
  | _, _, .cons h1 h2, _, h => by
    cases List.mem_cons.mp h with
    | inl e => subst e; exact ⟨_, List.mem_cons_self, h1⟩
    | inr e => obtain ⟨y, hy, r⟩ := h2.mem_left e; exact ⟨y, List.mem_cons_of_mem _ hy, r⟩

theorem Forall2.imp {α β : Type} {R S : α → β → Prop} (f : ∀ x y, R x y → S x y) :
    ∀ {l : List α} {ys : List β}, Forall2 R l ys → Forall2 S l ys
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => .cons (f _ _ h1) (h2.imp f)

/-- When `R` relates each item to at most one result, the results are determined. -/
theorem Forall2.unique {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {ys zs : List β}, Forall2 R l ys → Forall2 R l zs →
      (∀ x y z, R x y → R x z → y = z) → ys = zs
  | _, _, _, .nil, .nil, _ => rfl
  | _, _, _, .cons h1 h2, .cons h3 h4, hf => by rw [hf _ _ _ h1 h3, h2.unique h4 hf]

theorem Forall2.of_forall {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α}, (∀ x ∈ l, ∃ y, R x y) → ∃ ys, Forall2 R l ys
  | [], _ => ⟨[], .nil⟩
  | x :: l, h => by
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys⟩ := Forall2.of_forall (l := l) fun z hz => h z (List.mem_cons_of_mem _ hz)
    exact ⟨y :: ys, .cons hy hys⟩

/-- `mapM` succeeds exactly when `f` succeeds on every item. -/
theorem mapM_ok_iff {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α}, (∃ ys, l.mapM f = .ok ys) ↔ ∀ x ∈ l, ∃ y, f x = .ok y
  | [] => ⟨fun _ _ h => (by cases h), fun _ => ⟨[], rfl⟩⟩
  | x :: l => by
    constructor
    · rintro ⟨ys, h⟩ z hz
      obtain ⟨y, _, r⟩ := (mapM_ok.mp h).mem_left hz
      exact ⟨y, r⟩
    · intro h
      obtain ⟨y, hy⟩ := h x List.mem_cons_self
      obtain ⟨ys, hys⟩ := (mapM_ok_iff (l := l)).mpr fun z hz => h z (List.mem_cons_of_mem _ hz)
      exact ⟨y :: ys, mapM_ok.mpr (.cons hy (mapM_ok.mp hys))⟩

theorem filterAuxM_ok {p : Tuple → Except String Bool} :
    ∀ {l acc : List Tuple}, (∃ res, List.filterAuxM p l acc = .ok res) ↔ ∀ x ∈ l, ∃ b, p x = .ok b
  | [], acc => ⟨fun _ _ h => (by cases h), fun _ => ⟨_, rfl⟩⟩
  | y :: l, acc => by
    simp only [List.filterAuxM, bind, Except.bind]
    cases hy : p y with
    | error e =>
      constructor
      · intro ⟨_, h⟩; cases h
      · intro h; obtain ⟨b, hb⟩ := h y List.mem_cons_self; rw [hy] at hb; cases hb
    | ok b =>
      simp only
      rw [filterAuxM_ok]
      constructor
      · intro h x hx
        cases List.mem_cons.mp hx with
        | inl e => subst e; exact ⟨b, hy⟩
        | inr e => exact h x e
      · intro h x hx; exact h x (List.mem_cons_of_mem _ hx)

theorem filterM_ok {p : Tuple → Except String Bool} {l : List Tuple} :
    (∃ res, l.filterM p = .ok res) ↔ ∀ x ∈ l, ∃ b, p x = .ok b := by
  rw [← filterAuxM_ok (acc := [])]
  simp only [List.filterM, bind, Except.bind]
  cases List.filterAuxM p l [] with
  | error e => exact ⟨fun ⟨_, h⟩ => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | ok r => exact ⟨fun _ => ⟨r, rfl⟩, fun _ => ⟨_, rfl⟩⟩
/-- A loop that only checks each item: it succeeds exactly when every check passes. -/
theorem forIn_check {α : Type} (c : α → Bool) (msg : α → String) :
    ∀ (l : List α), (forIn (m := Except String) l PUnit.unit fun x _ =>
      if c x = true then pure (ForInStep.yield PUnit.unit)
      else do throw (msg x); pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit ↔
      ∀ x ∈ l, c x = true
  | [] => by simp [forIn, pure, Except.pure]
  | x :: l => by
    rw [List.forIn_cons]
    have ih := forIn_check c msg l
    by_cases hx : c x = true
    · simp only [hx, ite_true, pure, Except.pure, bind, Except.bind] at ih ⊢
      rw [ih]
      constructor
      · intro h y hy
        cases List.mem_cons.mp hy with
        | inl e => exact e ▸ hx
        | inr e => exact h y e
      · intro h y hy; exact h y (List.mem_cons_of_mem _ hy)
    · simp only [hx, Bool.false_eq_true, ite_false, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw]
      constructor
      · intro h; cases h
      · intro h; exact absurd (h x List.mem_cons_self) hx
/-! ## The finite algebra, continued

ρ, ∩ and extend, and when each operator is not refused. `(∃ s, op = .ok s) ↔ …` is
read "the operator is not refused exactly when …".
-/

namespace Finrel

theorem _root_.Rasso.Heading.renameCheck_ok {ren : List (String × String)} {h : Heading} :
    Heading.renameCheck ren h = .ok () ↔
      (∀ p ∈ ren, p.1 ∈ h.attrs) ∧ (renameHeading ren h).attrs.Nodup := by
  have hc := forIn_check (fun (x : String × String) => h.attrs.contains x.1)
    (fun x => toString "ρ: no attribute " ++ toString x.fst ++ toString " to rename in " ++ toString h.attrs) ren
  simp only [Heading.renameCheck, bind, Except.bind] at hc ⊢
  split
  · rename_i e he
    rw [he] at hc
    simp only [reduceCtorEq, false_iff] at hc
    simp only [reduceCtorEq, false_iff]
    intro ⟨h1, _⟩
    exact hc fun x hx => List.contains_iff_mem.mpr (h1 x hx)
  · rename_i u hu
    rw [hu] at hc
    have h1 := hc.mp rfl
    have h1' : ∀ p ∈ ren, p.1 ∈ h.attrs := fun p hp => List.contains_iff_mem.mp (h1 p hp)
    have hn := length_eraseDups_eq (renameHeading ren h).attrs
    have hl : (renameHeading ren h).attrs.length = h.length := by
      simp [renameHeading, Heading.attrs]
    rw [hl] at hn
    split
    · rename_i hne
      simp only [bne_iff_ne, ne_eq] at hne
      simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff]
      intro ⟨_, hnd⟩
      exact hne (hn.mpr hnd)
    · rename_i hne
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
      simp only [pure, Except.pure, true_iff]
      exact ⟨h1', hn.mp hne⟩

theorem rename_eq_ok {ren : List (String × String)} {r s : Finrel} :
    r.rename ren = .ok s ↔
      (∀ p ∈ ren, p.1 ∈ r.attrs) ∧ (renameHeading ren r.heading).attrs.Nodup ∧
      s = ofTuples (renameHeading ren r.heading) (r.tuples.map (renameTuple ren)) := by
  simp only [Finrel.rename, bind, Except.bind]
  split
  · rename_i e he
    simp only [reduceCtorEq, false_iff]
    intro ⟨h1, h2, _⟩
    rw [Heading.renameCheck_ok.mpr ⟨h1, h2⟩] at he; cases he
  · rename_i u hu
    obtain ⟨h1, h2⟩ := Heading.renameCheck_ok.mp hu
    simp only [pure, Except.pure, Except.ok.injEq]
    exact ⟨fun e => ⟨h1, h2, e.symm⟩, fun ⟨_, _, e⟩ => e.symm⟩

theorem rename_ok {ren : List (String × String)} {r : Finrel} :
    (∃ s, r.rename ren = .ok s) ↔
      (∀ p ∈ ren, p.1 ∈ r.attrs) ∧ (renameHeading ren r.heading).attrs.Nodup := by
  constructor
  · rintro ⟨s, h⟩; obtain ⟨h1, h2, _⟩ := rename_eq_ok.mp h; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨_, rename_eq_ok.mpr ⟨h1, h2, rfl⟩⟩

theorem mem_rename {ren : List (String × String)} {r s : Finrel}
    (h : r.rename ren = .ok s) (t : Tuple) :
    t ∈ s.tuples ↔ ∃ u ∈ r.tuples, t = renameTuple ren u := by
  obtain ⟨_, _, rfl⟩ := rename_eq_ok.mp h
  rw [mem_ofTuples, List.mem_map]
  exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩, fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩⟩

theorem rename_heading {ren : List (String × String)} {r s : Finrel}
    (h : r.rename ren = .ok s) : s.heading = renameHeading ren r.heading := by
  obtain ⟨_, _, rfl⟩ := rename_eq_ok.mp h; rfl

/-! ### When the operators are not refused -/

theorem select_ok {p : Tuple → Except String Bool} {r : Finrel} :
    (∃ s, r.select p = .ok s) ↔ ∀ t ∈ r.tuples, ∃ b, p t = .ok b := by
  rw [← filterM_ok]
  simp only [select, bind, Except.bind]
  cases r.tuples.filterM p with
  | error e => exact ⟨fun ⟨_, h⟩ => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | ok ts => exact ⟨fun _ => ⟨ts, rfl⟩, fun _ => ⟨_, rfl⟩⟩

theorem lookup_isSome {β : Type} {a : String} :
    ∀ {l : List (String × β)}, (l.lookup a).isSome ↔ a ∈ l.map (·.1)
  | [] => by simp [List.lookup]
  | (b, x) :: l => by
    simp only [List.lookup, List.map_cons, List.mem_cons]
    by_cases e : a = b
    · subst e; simp
    · have : (a == b) = false := by simp [e]
      rw [this]; simp only [lookup_isSome, e, false_or]

theorem mem_attrs_iff {h : Heading} {a : String} : a ∈ h.attrs ↔ (h.lookup a).isSome := by
  rw [lookup_isSome]; rfl

theorem mapM_error {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {e : ε}, l.mapM f = .error e → ∃ x ∈ l, ∀ y, f x ≠ .ok y
  | [], e, h => by cases h
  | x :: l, e, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e' => exact ⟨x, List.mem_cons_self, fun y hy => by rw [hx] at hy; cases hy⟩
    | ok y =>
      cases hl : l.mapM f with
      | error e' =>
        obtain ⟨z, hz, hf⟩ := mapM_error hl
        exact ⟨z, List.mem_cons_of_mem _ hz, hf⟩
      | ok zs => simp only [hx, hl, bind, Except.bind, pure, Except.pure] at h; cases h

theorem projectCore_ok {as : List String} {r : Finrel} :
    (∃ s, projectCore as r = .ok s) ↔ ∀ a ∈ as, a ∈ r.attrs := by
  simp only [projectCore, bind, Except.bind]
  split
  · rename_i e he
    obtain ⟨x, hx, hf⟩ := mapM_error he
    constructor
    · rintro ⟨_, h⟩; cases h
    · intro h
      have hs := mem_attrs_iff.mp (h x hx)
      rw [← domainOf?] at hs
      cases hd : r.domainOf? x with
      | none => rw [hd] at hs; cases hs
      | some d => exact absurd (by simp only [hd]) (hf (x, d))
  · rename_i hd he
    refine ⟨fun _ a ha => ?_, fun _ => ⟨_, rfl⟩⟩
    obtain ⟨y, _, hy⟩ := (mapM_ok.mp he).mem_left ha
    rw [attrs, mem_attrs_iff, ← domainOf?]
    cases hd : r.domainOf? a with
    | none => simp only [hd] at hy; cases hy
    | some d => rfl

/-- π is not refused exactly when it names attributes of `R`, none twice. -/
theorem project_ok {as : List String} {r : Finrel} :
    (∃ s, r.project as = .ok s) ↔ (∀ a ∈ as, a ∈ r.attrs) ∧ as.Nodup := by
  constructor
  · rintro ⟨s, h⟩
    obtain ⟨hn, hc⟩ := project_core h
    exact ⟨projectCore_ok.mp ⟨s, hc⟩, hn⟩
  · rintro ⟨ha, hn⟩
    obtain ⟨s, hs⟩ := projectCore_ok.mpr ha
    refine ⟨s, ?_⟩
    rw [project_eq]
    have : as.eraseDups.length = as.length := (length_eraseDups_eq as).mpr hn
    simp only [this, bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact hs

theorem project_heading {as : List String} {r s : Finrel} (h : r.project as = .ok s) :
    s.heading.attrs = as := by
  replace h := (project_core h).2
  simp only [projectCore, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i hd he
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    show hd.map (·.1) = as
    have := mapM_ok.mp he
    clear he
    induction this with
    | nil => rfl
    | @cons x y _ _ h1 _ ih =>
      simp only [List.map_cons, ih]
      cases hx : r.domainOf? x with
      | none => rw [hx] at h1; cases h1
      | some d => rw [hx] at h1; cases h1; rfl

/-- The condition `Finrel.sameHeading` checks: the same attributes, each with the same
domain. -/
def SameHeading (r s : Finrel) : Prop :=
  r.attrs.mergeSort (· ≤ ·) = s.attrs.mergeSort (· ≤ ·) ∧
    ∀ p ∈ r.heading, s.domainOf? p.1 = some p.2

theorem sameHeading_ok {who : String} {r s : Finrel} :
    r.sameHeading who s = .ok () ↔ SameHeading r s := by
  unfold sameHeading Heading.same SameHeading
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hc
    exact ⟨fun _ => ⟨hc.1, fun p hp => hc.2 p hp⟩, fun _ => rfl⟩
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hc
    exact ⟨fun h => (by cases h), fun ⟨h1, h2⟩ => absurd ⟨h1, fun p hp => h2 p hp⟩ hc⟩

theorem union_ok {r s : Finrel} : (∃ q, r.union s = .ok q) ↔ SameHeading r s := by
  rw [← sameHeading_ok (who := "∪")]
  simp only [union, bind, Except.bind]
  cases r.sameHeading "∪" s with
  | error e => exact ⟨fun ⟨_, h⟩ => (by cases h), fun h => (by cases h)⟩
  | ok u => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩

theorem diff_ok {r s : Finrel} : (∃ q, r.diff s = .ok q) ↔ SameHeading r s := by
  rw [← sameHeading_ok (who := "−")]
  simp only [diff, bind, Except.bind]
  cases r.sameHeading "−" s with
  | error e => exact ⟨fun ⟨_, h⟩ => (by cases h), fun h => (by cases h)⟩
  | ok u => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩

theorem inter_ok {r s : Finrel} : (∃ q, r.inter s = .ok q) ↔ SameHeading r s := by
  rw [← sameHeading_ok (who := "∩")]
  simp only [Finrel.inter, bind, Except.bind]
  cases r.sameHeading "∩" s with
  | error e => exact ⟨fun ⟨_, h⟩ => (by cases h), fun h => (by cases h)⟩
  | ok u => exact ⟨fun _ => rfl, fun _ => ⟨_, rfl⟩⟩

theorem mem_inter {r s q : Finrel} (h : r.inter s = .ok q) (t : Tuple) :
    t ∈ q.tuples ↔ t ∈ r.tuples ∧ t ∈ s.tuples := by
  simp only [Finrel.inter, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [mem_ofTuples, List.mem_filter, Body.mem_iff]; rfl

/-- The heading of a join is defined exactly when every shared attribute's two domains
can be intersected. -/
theorem joinHeading_ok {h k : Heading} :
    (∃ j, joinHeading h k = .ok j) ↔
      ∀ p ∈ h, ∀ e, k.lookup p.1 = some e → ∃ f, p.2.inter e = .ok f := by
  simp only [joinHeading, bind, Except.bind]
  split
  · rename_i err he
    obtain ⟨⟨a, d⟩, hx, hf⟩ := mapM_error he
    constructor
    · rintro ⟨_, h⟩; cases h
    · intro hall
      cases hk : k.lookup a with
      | none => exact absurd (by simp only [hk]) (hf (a, d))
      | some e =>
        obtain ⟨f, hf'⟩ := hall (a, d) hx e hk
        exact absurd (by simp only [hk, hf', pure, Except.pure]) (hf (a, f))
  · rename_i hd he
    refine ⟨fun _ p hp e hk => ?_, fun _ => ⟨_, rfl⟩⟩
    obtain ⟨y, _, hy⟩ := (mapM_ok.mp he).mem_left hp
    obtain ⟨a, d⟩ := p
    simp only [hk] at hy
    cases hi : d.inter e with
    | error _ => simp only [hi] at hy; cases hy
    | ok f => exact ⟨f, rfl⟩

theorem join_ok {r s : Finrel} :
    (∃ q, r.join s = .ok q) ↔ ∃ j, joinHeading r.heading s.heading = .ok j := by
  simp only [join, bind, Except.bind]
  cases joinHeading r.heading s.heading with
  | error e => exact ⟨fun ⟨_, h⟩ => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | ok u => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩

theorem extend_eq_ok {res : String} {tm : Term} {r s : Finrel} :
    r.extend res tm = .ok s ↔ res ∉ r.attrs ∧ ∃ d, tm.domain r.heading = some d ∧
      ∃ ts, Forall2 (fun u t => ∃ v, tm.eval u = .ok v ∧ t = Tuple.ofPairs ((res, v) :: u))
        r.tuples ts ∧ s = ofTuples (r.heading ++ [(res, d)]) ts := by
  simp only [Finrel.extend, bind, Except.bind]
  split
  · rename_i hc
    simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff]
    intro ⟨h, _⟩; exact h (List.contains_iff_mem.mp hc)
  · rename_i hc
    have hc' : res ∉ r.attrs := fun h => hc (List.contains_iff_mem.mpr h)
    split
    · rename_i d hd
      split
      · rename_i e he
        simp only [reduceCtorEq, false_iff]
        intro ⟨_, d', hd', ts, hts, _⟩
        obtain ⟨u, hu, hf⟩ := mapM_error he
        obtain ⟨t', _, v, hv, rfl⟩ := hts.mem_left hu
        exact hf (Tuple.ofPairs ((res, v) :: u)) (by simp only [hv, pure, Except.pure])
      · rename_i ts he
        simp only [pure, Except.pure, Except.ok.injEq]
        have hts := (mapM_ok.mp he).imp fun u y h => by
          split at h
          · cases h
          · rename_i v hv
            simp only [pure, Except.pure, Except.ok.injEq] at h
            exact (⟨v, hv, h.symm⟩ : ∃ v, tm.eval u = .ok v ∧ y = Tuple.ofPairs ((res, v) :: u))
        constructor
        · rintro rfl; exact ⟨hc', d, hd, ts, hts, rfl⟩
        · rintro ⟨_, d', hd', ts', hts', rfl⟩
          rw [hd] at hd'; cases hd'
          rw [hts.unique hts' fun u y z ⟨v, hv, hy⟩ ⟨w, hw, hz⟩ => by
            rw [hv] at hw; cases hw; rw [hy, hz]]
    · rename_i hd
      simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff]
      intro ⟨_, d, hd', _⟩
      exact hd d hd'

theorem extend_ok {res : String} {tm : Term} {r : Finrel} :
    (∃ s, r.extend res tm = .ok s) ↔ res ∉ r.attrs ∧ (tm.domain r.heading).isSome ∧
      ∀ u ∈ r.tuples, ∃ v, tm.eval u = .ok v := by
  constructor
  · rintro ⟨s, h⟩
    obtain ⟨h1, d, hd, ts, hts, _⟩ := extend_eq_ok.mp h
    refine ⟨h1, by rw [hd]; rfl, fun u hu => ?_⟩
    obtain ⟨_, _, v, hv, _⟩ := hts.mem_left hu
    exact ⟨v, hv⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h2
    have : ∃ ts, Forall2 (fun u t => ∃ v, tm.eval u = .ok v ∧ t = Tuple.ofPairs ((res, v) :: u))
        r.tuples ts := Forall2.of_forall fun u hu => by
      obtain ⟨v, hv⟩ := h3 u hu; exact ⟨_, v, hv, rfl⟩
    obtain ⟨ts, hts⟩ := this
    exact ⟨_, extend_eq_ok.mpr ⟨h1, d, hd, ts, hts, rfl⟩⟩

theorem mem_extend {res : String} {tm : Term} {r s : Finrel}
    (h : r.extend res tm = .ok s) (t : Tuple) :
    t ∈ s.tuples ↔ ∃ u ∈ r.tuples, ∃ v, tm.eval u = .ok v ∧ t = Tuple.ofPairs ((res, v) :: u) := by
  obtain ⟨_, d, _, ts, hts, rfl⟩ := extend_eq_ok.mp h
  rw [mem_ofTuples]
  constructor
  · intro ht; obtain ⟨u, hu, hr⟩ := hts.mem_right ht; exact ⟨u, hu, hr⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := hts.mem_left hu
    rw [hv] at hw; cases hw; exact hy

end Finrel

/-- `Heading.scoped` passes exactly when the term reads only attributes of the heading. -/
theorem Heading.scoped_ok {who : String} {h : Heading} {p : Term} :
    Heading.scoped who h p = .ok () ↔ ∀ a ∈ p.attrs, a ∈ h.attrs := by
  unfold Heading.scoped
  simp only
  split
  · rename_i hc
    rw [List.isEmpty_iff, List.filter_eq_nil_iff] at hc
    refine ⟨fun _ a ha => ?_, fun _ => rfl⟩
    have := hc a ha
    simpa using this
  · rename_i hc
    refine ⟨fun h => (by cases h), fun hall => absurd ?_ hc⟩
    rw [List.isEmpty_iff, List.filter_eq_nil_iff]
    intro a ha; simp [hall a ha]

/-! ## `has_subset` -/

/-- `has_subset` in γ's expression, on an evaluated relation (a literal): every row
matches some tuple of the group on the literal's attributes. -/
theorem Agg.eval_hasSubset_lit (key : Tuple) (group : List Tuple) (h : List (String × DomExpr))
    (rows : List (List Value)) :
    Agg.eval key group (.hasSubset (.omegaRows h rows)) =
      .ok (.bool (rows.all fun row => group.any fun t =>
        (h.zip row).all fun ((a, _), v) => t.get? a == some v)) := by
  simp [Agg.eval]

/-- `has_subset` as a condition: with the candidate bound and the relation evaluated
(as a leaf) to `req`, it gives whether every tuple of `req` is a tuple of the
candidate. -/
theorem Cond.eval_hasSubset {env : Env} {tg : List Expr} {r : Expr} {cand req : Finrel}
    (hc : env.lookup candidateName = some (.finrel cand))
    (hr : Expr.eval (leafEnv env) [] r = .ok (.finrel req)) :
    Cond.eval env tg (.hasSubset r) = .ok (req.tuples.all fun t => cand.tuples.contains t) := by
  rw [Cond.eval, hc]
  simp [bind, Except.bind, hr, Val.asFinrel, pure, Except.pure]

/-- The meaning of `has_subset` as a condition: it holds exactly when every tuple of the
relation is a tuple of the candidate. -/
theorem Cond.eval_hasSubset_iff {env : Env} {tg : List Expr} {r : Expr} {cand req : Finrel}
    (hc : env.lookup candidateName = some (.finrel cand))
    (hr : Expr.eval (leafEnv env) [] r = .ok (.finrel req)) :
    Cond.eval env tg (.hasSubset r) = .ok true ↔ ∀ t ∈ req.tuples, t ∈ cand.tuples := by
  rw [Cond.eval_hasSubset hc hr]
  simp

end Rasso
