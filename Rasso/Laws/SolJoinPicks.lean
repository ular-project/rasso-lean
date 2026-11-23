import Rasso.Laws.SolJoinMembers

/-!
# Rasso: the members of ⋈_sol, as picks

-/

namespace Rasso
namespace SolJoinLaws

/-- The attributes V adds to U's Data: U's groups are by these. -/
abbrev gU (U V : Sol) : List String := V.data.attrs.filter fun a => !U.data.attrs.contains a
/-- The attributes U adds to V's Data. -/
abbrev gV (U V : Sol) : List String := U.data.attrs.filter fun a => !V.data.attrs.contains a

/-! ## The whole-Data check read back from success -/

theorem checkWhole_ok {J : Finrel} {A : Sol} {G : List String} {a b : String}
    (h : checkWhole J A G a b = .ok ()) :
    (J.tuples = [] → A.data.tuples = []) ∧
      ∀ g ∈ joinGroups J G, ∀ d ∈ A.data.tuples, J.body.mem (d.merge g) = true := by
  unfold checkWhole at h
  by_cases hJ : J.tuples.isEmpty = true
  · simp only [hJ, ite_true, bind, Except.bind] at h
    rcases hA : A.data.tuples with _ | ⟨d, tl⟩
    · refine ⟨fun _ => rfl, fun g _ d hd => ?_⟩
      cases hd
    · rw [hA] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp only [hJ, Bool.false_eq_true, ite_false, bind, Except.bind] at h
    refine ⟨fun h0 => absurd (by simp [h0]) hJ, ?_⟩
    split at h
    · cases h
    rename_i u hl
    cases u
    have hall := forIn_steps_ok _ (by
      intro x u r hr
      split at hr
      · cases hr
      · simp only [pure, Except.pure, Except.ok.injEq] at hr; exact hr.symm) _ hl
    intro g hg d hd
    have hx := hall g hg
    split at hx
    · cases hx
    rename_i u hin
    cases u
    have := forIn_steps_ok _ (by
      intro y u r hr
      split at hr
      · simp only [pure, Except.pure, Except.ok.injEq] at hr; exact hr.symm
      · split at hr
        · cases hr
        · simp only [pure, Except.pure, Except.ok.injEq] at hr; exact hr.symm) _ hin d hd
    split at this
    · assumption
    · split at this
      · cases this
      · rename_i hthr
        simp [throw, throwThe, MonadExceptOf.throw] at hthr

/-- The whole-Data check, read back: when ⋈_sol succeeds, both sides' Data are whole in every group of the
joined Data. -/
theorem join_whole {U V W : Sol} (hj : U.join V = .ok W) :
    checkWhole W.data U (V.data.attrs.filter fun a => !U.data.attrs.contains a) "left" "right" = .ok () ∧
    checkWhole W.data V (U.data.attrs.filter fun a => !V.data.attrs.contains a) "right" "left" = .ok () := by
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
  rename_i u1 h1
  split at hj
  · cases hj
  rename_i u2 h2
  split at hj
  · cases hj
  simp only [pure, Except.pure, Except.ok.injEq] at hj
  subst hj
  cases u1; cases u2
  exact ⟨h1, h2⟩

/-- The Data/decision clash, read back: when ⋈_sol succeeds, no attribute is Data on one side and decided on
the other. -/
theorem join_q2 {U V W : Sol} (hj : U.join V = .ok W) :
    (∀ a ∈ U.data.attrs, a ∉ V.decision.attrs) ∧ (∀ a ∈ V.data.attrs, a ∉ U.decision.attrs) :=
  ⟨fun _a h1 h2 => join_refuses_data_decision (.inl ⟨h1, h2⟩) W hj,
   fun _a h1 h2 => join_refuses_data_decision (.inr ⟨h1, h2⟩) W hj⟩

/-- The whole-Data check as a fact about the joined Data: every group of it holds each side's Data whole,
and if it is empty, so are both Data. -/
theorem join_w3 {U V W : Sol} (hj : U.join V = .ok W) :
    (W.data.tuples = [] → U.data.tuples = [] ∧ V.data.tuples = []) ∧
    (∀ g ∈ joinGroups W.data (gU U V), ∀ d ∈ U.data.tuples, W.data.body.mem (d.merge g) = true) ∧
    (∀ g ∈ joinGroups W.data (gV U V), ∀ d ∈ V.data.tuples, W.data.body.mem (d.merge g) = true) := by
  obtain ⟨h1, h2⟩ := join_whole hj
  obtain ⟨a1, b1⟩ := checkWhole_ok h1
  obtain ⟨a2, b2⟩ := checkWhole_ok h2
  exact ⟨fun e => ⟨a1 e, a2 e⟩, b1, b2⟩

/-! ## The loop's pieces, as pure functions -/


/-- The decision of the U member picked for `t`'s group, at `t`'s U-Data part. -/
def pdU (U V : Sol) (J : Finrel) (ps : List Finrel) (t : Tuple) : Option Tuple :=
  (((joinGroups J (gU U V)).zip ps).lookup (t.restrict (gU U V))).bind
    fun m => U.decisionAt m (t.restrict U.data.attrs)

/-- The decision of the V member `m` at `t`'s V-Data part. -/
def pdV1 (V : Sol) (m : Finrel) (t : Tuple) : Option Tuple :=
  V.decisionAt m (t.restrict V.data.attrs)

/-- The U-pick's and the V member's decisions both exist at `t` and agree. -/
def agreeAt (U V : Sol) (J : Finrel) (ps : List Finrel) (m : Finrel) (t : Tuple) : Bool :=
  match pdU U V J ps t, pdV1 V m t with
  | some x, some y => x.agrees y
  | _, _ => false

/-- The members of V that agree with the U-pick on every tuple of the V-group `g`. -/
def agreeingV (U V : Sol) (J : Finrel) (ps : List Finrel) (g : Tuple) : List Finrel :=
  V.candidates.filter fun m => (J.tuples.filter fun t => t.restrict (gV U V) == g).all (agreeAt U V J ps m)

/-- For each V-group, its agreeing members, tagged with the group. -/
def okOptions (U V : Sol) (J : Finrel) (ps : List Finrel) : List (List (Tuple × Finrel)) :=
  (joinGroups J (gV U V)).map fun g => (agreeingV U V J ps g).map (g, ·)

/-- One glued member: each tuple of `J` merged with its U and V decisions. -/
def glue (U V : Sol) (J : Finrel) (h : Heading) (ps : List Finrel) (vs : List (Tuple × Finrel)) : Finrel :=
  Finrel.ofTuples h (J.tuples.map fun t =>
    (t.merge ((pdU U V J ps t).getD [])).merge
      (((vs.find? (·.1 == t.restrict (gV U V))).bind fun p => pdV1 V p.2 t).getD []))

/-! ## Monadic lemmas -/

/-- A successful `allM` is the pure `all`, when each successful step is the pure test. -/
theorem allM_ok_all {α : Type} {f : α → Except String Bool} {q : α → Bool}
    (hf : ∀ x c, f x = .ok c → c = q x) :
    ∀ {l : List α} {b : Bool}, l.allM f = .ok b → b = l.all q
  | [], b, h => by simp [List.allM, pure, Except.pure] at h; simp [h]
  | x :: l, b, h => by
    simp only [List.allM, bind, Except.bind] at h
    cases hx : f x with
    | error e => simp [hx] at h
    | ok c =>
      rw [hx] at h
      simp only at h
      have hc := hf x c hx
      cases c with
      | false =>
        simp [pure, Except.pure] at h
        subst h; simp only [List.all_cons, ← hc, Bool.false_and]
      | true => simp only [List.all_cons, ← hc, Bool.true_and]; exact allM_ok_all hf h

/-- A successful `mapM` is the pure `map`, when each successful step is the pure value. -/
theorem mapM_ok_map {α β : Type} {f : α → Except String β} {g : α → β}
    (hf : ∀ x y, f x = .ok y → y = g x) :
    ∀ {l : List α} {ys : List β}, l.mapM f = .ok ys → ys = l.map g
  | [], ys, h => by simp [List.mapM_nil, pure, Except.pure] at h; simp [h]
  | x :: l, ys, h => by
    rw [List.mapM_cons] at h
    simp only [bind, Except.bind] at h
    cases hx : f x with
    | error e => simp [hx] at h
    | ok y =>
      rw [hx] at h
      simp only at h
      cases hl : l.mapM f with
      | error e => simp [hl] at h
      | ok zs =>
        rw [hl] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [← h, hf x y hx, mapM_ok_map hf hl]; rfl

/-- A check that succeeds passes exactly when its value is `true`. -/
theorem passed_eq {e : Except String Bool} {b : Bool} (h : ∀ c, e = .ok c → c = b) :
    Succeeds e → passed e = b := by
  cases e with
  | error _ => intro h'; exact h'.elim
  | ok c => intro _; rw [h c rfl]; cases b <;> rfl

/-! ## The loop's result, as a list -/

theorem joinLoop_picks {U V : Sol} {J : Finrel} {h : Heading} {cs : List Finrel}
    (hl : joinLoop U V J h = .ok cs) :
    cs = (choices ((joinGroups J (gU U V)).map fun _ => U.candidates)).flatMap
      fun ps => (choices (okOptions U V J ps)).map (glue U V J h ps) := by
  unfold joinLoop at hl
  simp only [bind, Except.bind] at hl
  split at hl
  · cases hl
  rename_i v hv
  simp only [pure, Except.pure, Except.ok.injEq] at hl
  subst hl
  have key := forIn_append_ok _ (fun (ps : List Finrel) (d : List Finrel) =>
      d = (choices (okOptions U V J ps)).map (glue U V J h ps)) ?_ _ _ _ hv
  · obtain ⟨ds, h2, e⟩ := key
    rw [e, List.nil_append, Forall2_eq_map h2, List.flatMap]
  · intro ps acc r hr
    split at hr
    · cases hr
    rename_i options hopt
    split at hr
    · cases hr
    rename_i w hw
    simp only [pure, Except.pure, Except.ok.injEq] at hr
    subst hr
    -- the decisions the loop computes are the pure ones
    have hU : ∀ (t x : Tuple), (match List.lookup (t.restrict (gU U V)) ((joinGroups J (gU U V)).zip ps) with
        | none => (throw "join_sol: internal: no group" : Except String Tuple)
        | some m => match U.decisionAt m (t.restrict U.data.attrs) with
          | some x => pure x
          | none => throw "join_sol: internal: a member has no tuple for a data tuple") = .ok x →
        pdU U V J ps t = some x := by
      intro t x hx
      split at hx
      · cases hx
      rename_i m hm
      split at hx
      · rename_i z hz
        simp only [pure, Except.pure, Except.ok.injEq] at hx
        subst hx
        simp only [pdU, hm, Option.bind_some, hz]
      · cases hx
    have hV : ∀ (m : Finrel) (t y : Tuple), (match V.decisionAt m (t.restrict V.data.attrs) with
          | some x => (pure x : Except String Tuple)
          | none => throw "join_sol: internal: a member has no tuple for a data tuple") = .ok y →
        pdV1 V m t = some y := by
      intro m t y hy
      split at hy
      · rename_i z hz
        simp only [pure, Except.pure, Except.ok.injEq] at hy
        subst hy; exact hz
      · cases hy
    have ko := forIn_append_ok _ (fun (g : Tuple) (d : List (List (Tuple × Finrel))) =>
      d = [(agreeingV U V J ps g).map (g, ·)]) ?_ _ _ _ hopt
    · obtain ⟨ds, h2, e⟩ := ko
      rw [List.nil_append, Forall2_eq_map h2, flatten_map_singleton] at e
      have kw := forIn_append_ok _ (fun (vs : List (Tuple × Finrel)) (d : List Finrel) =>
        d = [glue U V J h ps vs]) ?_ _ _ _ hw
      · obtain ⟨ds', h3, e'⟩ := kw
        refine ⟨ds'.flatten, by rw [e'], ?_⟩
        rw [Forall2_eq_map h3, flatten_map_singleton, e]
        rfl
      · intro vs acc' r' hr'
        split at hr'
        · cases hr'
        rename_i ts hts
        simp only [pure, Except.pure, Except.ok.injEq] at hr'
        refine ⟨_, hr'.symm, ?_⟩
        rw [mapM_ok_map ?_ hts]
        · rfl
        intro t y hy
        split at hy
        · rename_i fst m hfind
          split at hy
          · cases hy
          rename_i x hx
          split at hy
          · cases hy
          rename_i z hz
          simp only [pure, Except.pure, Except.ok.injEq] at hy
          subst hy
          simp only [hfind, Option.bind_some, hU t x hx, hV m t z hz, Option.getD_some]
        · cases hy
    · intro g acc' r' hr'
      split at hr'
      · cases hr'
      rename_i okl hok
      simp only [pure, Except.pure, Except.ok.injEq] at hr'
      refine ⟨_, hr'.symm, ?_⟩
      obtain ⟨hs, he⟩ := filterM_ok_iff.mp hok
      rw [he]
      congr 2
      unfold agreeingV
      apply List.filter_congr
      intro m hm
      have hsm := hs m hm
      revert hsm
      refine passed_eq (fun c hc => allM_ok_all ?_ hc)
      intro t c hc
      split at hc
      · cases hc
      rename_i x hx
      split at hc
      · cases hc
      rename_i y hy
      simp only [pure, Except.pure, Except.ok.injEq] at hc
      subst hc
      simp only [agreeAt, hU t x hx, hV m t y hy]

/-- **⋈_sol's members, as a list.** When ⋈_sol succeeds, its members are, for each
U-pick (one member of U per U-group) and each choice of agreeing V members (one per
V-group), the glued member. -/
theorem join_candidates_picks {U V W : Sol} (hj : U.join V = .ok W) :
    W.candidates = (choices ((joinGroups W.data (gU U V)).map fun _ => U.candidates)).flatMap
      fun ps => (choices (okOptions U V W.data ps)).map (glue U V W.data W.heading ps) :=
  joinLoop_picks (join_candidates_eq hj)

/-- Choosing from tagged lists is choosing and then tagging. -/
theorem choices_tag {α β : Type} (L : α → List β) :
    ∀ gs : List α, choices (gs.map fun g => (L g).map (g, ·)) = (choices (gs.map L)).map (gs.zip ·)
  | [] => rfl
  | g :: gs => by
    simp only [List.map_cons, choices, choices_tag L gs, List.flatMap_map, List.map_flatMap,
      List.map_map]
    rfl

theorem picks_map_iff {α β : Type} {L : α → List β} :
    ∀ {gs : List α} {qs : List β},
      Picks qs (gs.map L) ↔ qs.length = gs.length ∧ ∀ p ∈ gs.zip qs, p.2 ∈ L p.1
  | [], qs => by
    simp only [List.map_nil, List.length_nil, List.zip_nil_left, List.not_mem_nil, false_implies,
      implies_true, and_true]
    constructor
    · intro h; cases h; rfl
    · intro h; rw [List.length_eq_zero_iff.mp h]; exact .nil
  | g :: gs, [] => by
    simp only [List.map_cons, List.length_nil, List.length_cons]
    constructor
    · intro h; cases h
    · rintro ⟨h, -⟩; cases h
  | g :: gs, q :: qs => by
    simp only [List.map_cons, List.length_cons, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp,
      Nat.add_right_cancel_iff]
    constructor
    · intro h
      cases h with
      | cons h1 h2 =>
        obtain ⟨e, h3⟩ := picks_map_iff.mp h2
        exact ⟨e, h1, h3⟩
    · rintro ⟨e, h1, h3⟩
      exact .cons h1 (picks_map_iff.mpr ⟨e, h3⟩)

theorem zip_snd_forall {α β : Type} {gs : List α} {ps : List β} {P : β → Prop}
    (h : ps.length = gs.length) : (∀ p ∈ gs.zip ps, P p.2) ↔ ∀ m ∈ ps, P m := by
  have e : (gs.zip ps).map Prod.snd = ps := List.map_snd_zip (by omega)
  constructor
  · intro hp m hm
    rw [← e] at hm
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hm
    exact hp p hp'
  · intro hm p hp
    exact hm _ (e ▸ List.mem_map_of_mem hp)

theorem mem_agreeingV {U V : Sol} {J : Finrel} {ps : List Finrel} {g : Tuple} {m : Finrel} :
    m ∈ agreeingV U V J ps g ↔ m ∈ V.candidates ∧
      ∀ t ∈ J.tuples, t.restrict (gV U V) = g → agreeAt U V J ps m t = true := by
  simp only [agreeingV, List.mem_filter, List.all_eq_true, List.mem_filter, beq_iff_eq, and_imp]

/-- **⋈_sol's members, as picks.** A member of U ⋈_sol V is a U-pick `ps` (a member of U for
each U-group) and a V-pick `qs` (a member of V for each V-group, agreeing with the U-pick at
every tuple of its group), glued. -/
theorem mem_join_picks {U V W : Sol} (hj : U.join V = .ok W) {c : Finrel} :
    c ∈ W.candidates ↔ ∃ ps qs : List Finrel,
      ps.length = (joinGroups W.data (gU U V)).length ∧ (∀ m ∈ ps, m ∈ U.candidates) ∧
      qs.length = (joinGroups W.data (gV U V)).length ∧
      (∀ p ∈ (joinGroups W.data (gV U V)).zip qs, p.2 ∈ V.candidates ∧
        ∀ t ∈ W.data.tuples, t.restrict (gV U V) = p.1 → agreeAt U V W.data ps p.2 t = true) ∧
      c = glue U V W.data W.heading ps ((joinGroups W.data (gV U V)).zip qs) := by
  rw [join_candidates_picks hj, List.mem_flatMap]
  simp only [okOptions, choices_tag, List.map_map, List.mem_map, mem_choices, picks_map_iff,
    mem_agreeingV, Function.comp_def]
  constructor
  · rintro ⟨ps, ⟨h1, h2⟩, qs, ⟨h3, h4⟩, rfl⟩
    exact ⟨ps, qs, h1, (zip_snd_forall h1).mp h2, h3, h4, rfl⟩
  · rintro ⟨ps, qs, h1, h2, h3, h4, rfl⟩
    exact ⟨ps, ⟨h1, (zip_snd_forall h1).mpr h2⟩, qs, ⟨h3, h4⟩, rfl⟩

end SolJoinLaws
end Rasso
