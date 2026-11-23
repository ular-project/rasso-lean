import Rasso.Laws.Sol

/-!
# Rasso: the laws of ρ and ⋈ on solution sets

The rows are those of ⋈_sol and ρ_sol in the laws appendix of the Rasso blueprint.
-/

namespace Rasso
namespace SolJoinLaws

open Finrel

/-! ## ρ on solution sets -/

/-- The renamed member: the member's tuples, read over the solution set's heading, renamed. -/
def renameMember (ren : List (String × String)) (h : Heading) (c : Finrel) : Finrel :=
  ofTuples (renameHeading ren h) ((ofTuples h c.tuples).tuples.map (renameTuple ren))

/-- ρ_sol is refused exactly when ρ is refused on the heading or on the Data. -/
theorem rename_ok {ren : List (String × String)} {s : Sol} :
    (∃ s', s.rename ren = .ok s') ↔
      ((∀ p ∈ ren, p.1 ∈ s.heading.attrs) ∧ (renameHeading ren s.heading).attrs.Nodup) ∧
      (∃ d, s.data.rename (ren.filter fun p => s.data.attrs.contains p.1) = .ok d) := by
  have hm : ∀ c : Finrel, (∃ c', (ofTuples s.heading c.tuples).rename ren = .ok c') ↔
      (∀ p ∈ ren, p.1 ∈ s.heading.attrs) ∧ (renameHeading ren s.heading).attrs.Nodup :=
    fun c => Finrel.rename_ok
  have hh : (∃ c', (ofTuples s.heading []).rename ren = .ok c') ↔
      (∀ p ∈ ren, p.1 ∈ s.heading.attrs) ∧ (renameHeading ren s.heading).attrs.Nodup :=
    Finrel.rename_ok
  simp only [Sol.rename, bind, Except.bind]
  constructor
  · intro ⟨s', h⟩
    split at h
    · cases h
    · rename_i x hx
      refine ⟨hh.mp ⟨_, hx⟩, ?_⟩
      split at h
      · cases h
      · rename_i d hd; exact ⟨d, hd⟩
  · intro ⟨h1, d, hd⟩
    obtain ⟨x, hx⟩ := hh.mpr h1
    rw [hx]; simp only [hd]
    obtain ⟨cs, hcs⟩ := (mapM_ok_iff (l := s.candidates)
      (f := fun c => (ofTuples s.heading c.tuples).rename ren)).mpr fun c _ => (hm c).mpr h1
    rw [hcs]
    exact ⟨_, rfl⟩

/-- The members of ρ(U) are U's members renamed, one for one and in order; the Data is
ρ of U's Data and the heading is U's heading renamed. -/
theorem rename_eq {ren : List (String × String)} {s s' : Sol} (h : s.rename ren = .ok s') :
    s.data.rename (ren.filter fun p => s.data.attrs.contains p.1) = .ok s'.data ∧
    s'.heading = renameHeading ren s.heading ∧
    s'.candidates = s.candidates.map (renameMember ren s.heading) := by
  simp only [Sol.rename, bind, Except.bind] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i d hd
  split at h
  · cases h
  rename_i cs hcs
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨hd, rfl, ?_⟩
  have h2 := mapM_ok.mp hcs
  clear hcs
  generalize s.candidates = l at h2 ⊢
  induction h2 with
  | nil => rfl
  | cons hx _ ih =>
    rename_i c c' _ _
    obtain ⟨_, _, e⟩ := Finrel.rename_eq_ok.mp hx
    simp only at ih
    simp only [List.map_cons, renameMember, e, ih]
    rfl

/-- ρ_sol keeps the number of members. -/
theorem rename_length {ren : List (String × String)} {s s' : Sol} (h : s.rename ren = .ok s') :
    s'.candidates.length = s.candidates.length := by
  rw [(rename_eq h).2.2, List.length_map]

/-- A tuple of a renamed member is a tuple of the member, renamed. -/
theorem mem_renameMember {ren : List (String × String)} {h : Heading} {c : Finrel} {t : Tuple} :
    t ∈ (renameMember ren h c).tuples ↔ ∃ u ∈ (ofTuples h c.tuples).tuples, t = renameTuple ren u := by
  rw [renameMember, mem_ofTuples, List.mem_map]
  exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩, fun ⟨u, hu, e⟩ => ⟨u, hu, e.symm⟩⟩

/-- ρ with the empty renaming keeps each member's body, given that each member is
well formed over the heading. -/
theorem rename_nil_members {s s' : Sol} (h : s.rename [] = .ok s')
    (hwf : ∀ c ∈ s.candidates, (ofTuples s.heading c.tuples).WF) :
    s'.candidates.map (·.body) = s.candidates.map fun c => (ofTuples s.heading c.tuples).body := by
  obtain ⟨⟨h1, h2⟩, _⟩ := rename_ok.mp ⟨s', h⟩
  rw [(rename_eq h).2.2, List.map_map]
  apply List.map_congr_left
  intro c hc
  have hr : (ofTuples s.heading c.tuples).rename [] = .ok (renameMember [] s.heading c) :=
    Finrel.rename_eq_ok.mpr ⟨h1, h2, rfl⟩
  exact FinrelLaws.rename_nil (hwf c hc) hr

/-! ## ⋈ on solution sets: its shape -/

/-- When ⋈_sol succeeds, its Data is the join of the two Data, and its heading is that
Data's heading followed by the join of the two Decision headings. -/
theorem join_shape {U V W : Sol} (h : U.join V = .ok W) :
    U.data.join V.data = .ok W.data ∧
    ∃ dec, joinHeading U.decision V.decision = .ok dec ∧ W.heading = W.data.heading ++ dec := by
  unfold Sol.join at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i J hJ
  split at h
  · cases h
  rename_i dec hdec
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨hJ, dec, hdec, rfl⟩

/-- A checking loop: if it succeeds and its step never stops early, every step succeeded. -/
theorem forIn_steps_ok {α : Type} (f : α → PUnit → Except String (ForInStep PUnit))
    (hf : ∀ x u r, f x u = .ok r → r = .yield PUnit.unit) :
    ∀ (l : List α), forIn l PUnit.unit f = .ok PUnit.unit →
      ∀ x ∈ l, f x PUnit.unit = .ok (.yield PUnit.unit)
  | [], _ => by simp
  | y :: l, h => by
    rw [List.forIn_cons] at h
    cases hy : f y PUnit.unit with
    | error e => simp [hy, bind, Except.bind] at h
    | ok r =>
      have hr := hf _ _ _ hy
      subst hr
      simp only [hy, bind, Except.bind] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hy
      · exact forIn_steps_ok f hf l h x hx

/-- The Data/decision clash: ⋈_sol refuses when an attribute is Data in one operand and decided in the other. -/
theorem join_refuses_data_decision {U V : Sol} {a : String}
    (ha : (a ∈ U.data.attrs ∧ a ∈ V.decision.attrs) ∨ (a ∈ V.data.attrs ∧ a ∈ U.decision.attrs)) :
    ∀ W, U.join V ≠ .ok W := by
  intro W h
  unfold Sol.join at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i u hq
  cases u
  have hall := forIn_steps_ok _ (by
    intro x u r hr
    split at hr
    · cases hr
    · simp only [pure, Except.pure, Except.ok.injEq] at hr; exact hr.symm) _ hq
  have inner : ∀ x ∈ [(U, V, "left", "right"), (V, U, "right", "left")],
      ∀ b ∈ x.1.data.attrs, x.2.1.decision.attrs.contains b = false := by
    intro x hm b hb
    have hx := hall x hm
    split at hx
    · cases hx
    rename_i u hin
    cases u
    have := forIn_steps_ok _ (by
      intro y u r hr
      split at hr
      · simp [throw, throwThe, MonadExceptOf.throw] at hr
      · simp only [pure, Except.pure, Except.ok.injEq] at hr; exact hr.symm) _ hin b hb
    split at this
    · simp [throw, throwThe, MonadExceptOf.throw] at this
    · rename_i hc; simpa using hc
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := inner (U, V, "left", "right") (by simp) a h1
    simp at this; exact this h2
  · have := inner (V, U, "right", "left") (by simp) a h1
    simp at this; exact this h2

/-! ## The members of ⋈_sol: the loop as a definition, and the count

`joinLoop` is `Sol.join`'s member-building loop, copied verbatim; `join_candidates_eq` says
`Sol.join`'s members are what it gives. -/

/-- The member-building loop of `Sol.join`, copied verbatim. -/
def joinLoop (U V : Sol) (J : Finrel) (h : Heading) : Except String (List Finrel) := do
  let gU := V.data.attrs.filter fun a => !U.data.attrs.contains a
  let gV := U.data.attrs.filter fun a => !V.data.attrs.contains a
  let gsU := joinGroups J gU
  let gsV := joinGroups J gV
  let decU (picks : List (Tuple × Finrel)) (t : Tuple) : Except String Tuple :=
    match picks.lookup (t.restrict gU) with
    | none => throw "join_sol: internal: no group"
    | some m => match U.decisionAt m (t.restrict U.data.attrs) with
      | some x => pure x
      | none => throw "join_sol: internal: a member has no tuple for a data tuple"
  let decV (m : Finrel) (t : Tuple) : Except String Tuple :=
    match V.decisionAt m (t.restrict V.data.attrs) with
    | some x => pure x
    | none => throw "join_sol: internal: a member has no tuple for a data tuple"
  let mut cands : List Finrel := []
  for ps in choices (gsU.map fun _ => U.candidates) do
    let picks := gsU.zip ps
    let mut options : List (List (Tuple × Finrel)) := []
    for g in gsV do
      let ts := J.tuples.filter fun t => t.restrict gV == g
      let ok ← V.candidates.filterM fun m => ts.allM fun t => do
        return (← decU picks t).agrees (← decV m t)
      options := options ++ [ok.map (g, ·)]
    for vs in choices options do
      let ts ← J.tuples.mapM fun t => do
        let some (_, m) := vs.find? (·.1 == t.restrict gV)
          | throw "join_sol: internal: no group"
        return (t.merge (← decU picks t)).merge (← decV m t)
      cands := cands ++ [Finrel.ofTuples h ts]
  return cands

theorem join_candidates_eq {U V W : Sol} (hj : U.join V = .ok W) :
    joinLoop U V W.data W.heading = .ok W.candidates := by
  unfold Sol.join at hj
  simp only [bind, Except.bind] at hj
  split at hj
  · cases hj
  split at hj
  · cases hj
  rename_i J hJ
  split at hj
  · cases hj
  rename_i dec hdec
  split at hj
  · cases hj
  split at hj
  · cases hj
  split at hj
  · cases hj
  rename_i cs hcs
  simp only [pure, Except.pure, Except.ok.injEq] at hj
  subst hj
  show joinLoop U V J (J.heading ++ dec) = .ok cs
  unfold joinLoop
  simp only [bind, Except.bind]
  first | (rw [hcs]; rfl) | (simp only [hcs]; rfl) | (erw [hcs]; rfl)

/-- An appending loop: if it succeeds and each step appends a piece with property `P`,
the result is the initial list followed by the pieces, one per item. -/
theorem forIn_append_ok {α β : Type} (f : α → List β → Except String (ForInStep (List β)))
    (P : α → List β → Prop)
    (hf : ∀ x b r, f x b = .ok r → ∃ d, r = .yield (b ++ d) ∧ P x d) :
    ∀ (l : List α) (init res : List β), forIn l init f = .ok res →
      ∃ ds : List (List β), Forall2 P l ds ∧ res = init ++ ds.flatten
  | [], init, res, h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨[], .nil, by simp [h]⟩
  | y :: l, init, res, h => by
    rw [List.forIn_cons] at h
    cases hy : f y init with
    | error e => simp [hy, bind, Except.bind] at h
    | ok r =>
      obtain ⟨d, rfl, hd⟩ := hf _ _ _ hy
      simp only [hy, bind, Except.bind] at h
      obtain ⟨ds, h2, e⟩ := forIn_append_ok f P hf l _ _ h
      exact ⟨d :: ds, .cons hd h2, by simp [e]⟩

theorem Forall2_length_flatten {α β : Type} {P : α → List β → Prop} {k : Nat}
    (hk : ∀ x d, P x d → d.length = k) :
    ∀ {l : List α} {ds : List (List β)}, Forall2 P l ds → ds.flatten.length = l.length * k
  | _, _, .nil => by simp
  | _, _, .cons h1 h2 => by
    rw [List.flatten_cons, List.length_append, Forall2_length_flatten hk h2, hk _ _ h1,
      List.length_cons, Nat.succ_mul, Nat.add_comm]


theorem mem_restrict_attr {t : Tuple} {as : List String} {p : String × Value}
    (h : p ∈ t.restrict as) : p.1 ∈ as := by
  unfold Tuple.restrict at h
  exact List.contains_iff_mem.mp (List.mem_filter.mp h).2

theorem get?_restrict_none {u : Tuple} {as : List String} {a : String} (ha : a ∉ as) :
    (u.restrict as).get? a = none := by
  unfold Tuple.get?
  exact lookup_eq_none fun q hq e => ha (e ▸ mem_restrict_attr hq)

theorem agrees_disjoint {t u : Tuple} {as bs : List String} (hd : ∀ a ∈ as, a ∉ bs) :
    (t.restrict as).agrees (u.restrict bs) = true := by
  unfold Tuple.agrees
  rw [List.all_eq_true]
  intro ⟨a, v⟩ hm
  have ha := mem_restrict_attr hm
  simp only [get?_restrict_none (hd a ha)]


theorem Forall2_eq_map {α β : Type} {F : α → β} :
    ∀ {l : List α} {ds : List β}, Forall2 (fun x d => d = F x) l ds → ds = l.map F
  | _, _, .nil => rfl
  | _, _, .cons h1 h2 => by rw [h1, Forall2_eq_map h2]; rfl

theorem flatten_map_singleton {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map fun x => [f x]).flatten = l.map f
  | [] => rfl
  | _ :: l => by simp [flatten_map_singleton f l]

theorem filterM_all_true {α : Type} {p : α → Except String Bool}
    (hp : ∀ x c, p x = .ok c → c = true) {l r : List α} (h : l.filterM p = .ok r) : r = l := by
  obtain ⟨hs, he⟩ := filterM_ok_iff.mp h
  rw [he]
  apply List.filter_eq_self.mpr
  intro x hx
  have := hs x hx
  cases hpx : p x with
  | error e => rw [hpx] at this; exact this.elim
  | ok c => rw [hp x c hpx]; rfl

theorem allM_true {α : Type} {f : α → Except String Bool}
    (hf : ∀ x c, f x = .ok c → c = true) :
    ∀ {l : List α} {b : Bool}, l.allM f = .ok b → b = true
  | [], b, h => by simp [List.allM, pure, Except.pure] at h; exact h
  | x :: l, b, h => by
    simp only [List.allM, bind, Except.bind] at h
    cases hx : f x with
    | error e => simp [hx] at h
    | ok c =>
      rw [hx] at h
      simp only at h
      rw [hf x c hx] at h
      exact allM_true hf h

theorem foldr_mul_const {α : Type} (k : Nat) :
    ∀ (l : List α), (l.map fun _ => k).foldr (· * ·) 1 = k ^ l.length
  | [] => rfl
  | _ :: l => by
    simp only [List.map_cons, List.foldr_cons, foldr_mul_const k l, List.length_cons, Nat.pow_succ,
      Nat.mul_comm]

theorem decisionAt_some {s : Sol} {m : Finrel} {d x : Tuple} (h : s.decisionAt m d = some x) :
    ∃ y : Tuple, x = y.restrict s.decision.attrs := by
  unfold Sol.decisionAt at h
  cases hf : m.tuples.find? (fun r => r.restrict s.data.attrs == d) with
  | none => simp [hf] at h
  | some y => simp only [hf, Option.map_some, Option.some.injEq] at h; exact ⟨y, h.symm⟩

theorem length_joinLoop {U V : Sol} {J : Finrel} {h : Heading} {cs : List Finrel}
    (hl : joinLoop U V J h = .ok cs)
    (hd : ∀ a ∈ U.decision.attrs, a ∉ V.decision.attrs) :
    cs.length = U.candidates.length ^ (joinGroups J (V.data.attrs.filter fun a => !U.data.attrs.contains a)).length *
      V.candidates.length ^ (joinGroups J (U.data.attrs.filter fun a => !V.data.attrs.contains a)).length := by
  unfold joinLoop at hl
  simp only [bind, Except.bind] at hl
  split at hl
  · cases hl
  rename_i v hv
  simp only [pure, Except.pure, Except.ok.injEq] at hl
  subst hl
  -- the number of V-choices for each U-pick
  have key := forIn_append_ok _ (fun (_ : List Finrel) (d : List Finrel) => d.length = V.candidates.length ^
        (joinGroups J (U.data.attrs.filter fun a => !V.data.attrs.contains a)).length) ?_ _ _ _ hv
  · obtain ⟨ds, h2, e⟩ := key
    rw [e, List.nil_append, Forall2_length_flatten (fun _ _ h => h) h2, length_choices,
      List.map_map]
    have : (List.length ∘ fun (_ : Tuple) => U.candidates) = fun _ => U.candidates.length := rfl
    rw [this, foldr_mul_const]
  · intro ps acc r hr
    split at hr
    · cases hr
    rename_i options hopt
    split at hr
    · cases hr
    rename_i w hw
    simp only [pure, Except.pure, Except.ok.injEq] at hr
    subst hr
    -- the options: every member of V, for each V-group
    have ko := forIn_append_ok _ (fun (g : Tuple) (d : List (List (Tuple × Finrel))) =>
      d = [V.candidates.map (g, ·)]) ?_ _ _ _ hopt
    · obtain ⟨ds, h2, e⟩ := ko
      rw [List.nil_append, Forall2_eq_map h2] at e
      have kw := forIn_append_ok _ (fun (_ : List (Tuple × Finrel)) (d : List Finrel) => d.length = 1)
        ?_ _ _ _ hw
      · obtain ⟨ds', h3, e'⟩ := kw
        refine ⟨ds'.flatten, by rw [e'], ?_⟩
        rw [Forall2_length_flatten (fun _ _ h => h) h3, Nat.mul_one, length_choices, e,
          flatten_map_singleton, List.map_map]
        have : (List.length ∘ fun (g : Tuple) => V.candidates.map (g, ·)) = fun _ => V.candidates.length := by
          funext g; simp
        rw [this, foldr_mul_const]
      · intro vs acc' r' hr'
        split at hr'
        · cases hr'
        simp only [pure, Except.pure, Except.ok.injEq] at hr'
        exact ⟨_, hr'.symm, rfl⟩
    · intro g acc' r' hr'
      split at hr'
      · cases hr'
      rename_i okl hok
      simp only [pure, Except.pure, Except.ok.injEq] at hr'
      refine ⟨_, hr'.symm, ?_⟩
      have : okl = V.candidates := by
        refine filterM_all_true ?_ hok
        intro m b ht
        refine allM_true ?_ ht
        intro t c hc
        split at hc
        · cases hc
        rename_i x hx
        split at hc
        · cases hc
        rename_i y hy
        simp only [pure, Except.pure, Except.ok.injEq] at hc
        subst hc
        have hx' : ∃ x' : Tuple, x = x'.restrict U.decision.attrs := by
          split at hx
          · cases hx
          split at hx
          · rename_i z hz
            simp only [pure, Except.pure, Except.ok.injEq] at hx
            subst hx; exact decisionAt_some hz
          · cases hx
        have hy' : ∃ y' : Tuple, y = y'.restrict V.decision.attrs := by
          split at hy
          · rename_i z hz
            simp only [pure, Except.pure, Except.ok.injEq] at hy
            subst hy; exact decisionAt_some hz
          · cases hy
        obtain ⟨x', rfl⟩ := hx'
        obtain ⟨y', rfl⟩ := hy'
        exact agrees_disjoint hd
      rw [this]


/-- **Count.** When ⋈_sol succeeds and the two Decisions share no attribute, it has
|U|^{g_U} · |V|^{g_V} members, with `g` the number of groups `joinGroups` gives (one
when the other side adds no Data attribute, even for empty data). -/
theorem length_join {U V W : Sol} (hj : U.join V = .ok W)
    (hd : ∀ a ∈ U.decision.attrs, a ∉ V.decision.attrs) :
    W.candidates.length =
      U.candidates.length ^ (joinGroups W.data (V.data.attrs.filter fun a => !U.data.attrs.contains a)).length *
      V.candidates.length ^ (joinGroups W.data (U.data.attrs.filter fun a => !V.data.attrs.contains a)).length :=
  length_joinLoop (join_candidates_eq hj) hd

end SolJoinLaws
end Rasso
