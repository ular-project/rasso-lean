import Rasso.Classes

/-!
# Rasso: the dense-order class as a global class

A relation is in the dense class when it is well formed, every domain of its heading is
the rat kind, and its term is *dense-shaped*: `and`, `or`, `not` with one operand, Boolean
constants, and comparisons `= < <= > >=` of two operands, each an attribute or an exact
number. Such a term never refuses on a fitting tuple, so the relation is total. σ with a
dense-shaped term, ⋈, ∪, ∩, −, ρ and π keep the class, and π never refuses a relation in
it except for its two checks on the attribute list.
-/

namespace Rasso

open Dense
open NF (attrs_sub_call bv bv_eq foldr_conj_all)

/-- An operand of a dense-shaped comparison: an attribute, or an exact number. -/
def Atomic (o : Term) : Prop := (∃ b, o = .attr b) ∨ ∃ v, o = .val v ∧ v.exact?.isSome

/-- A term of the dense-order class's global shape. -/
inductive DenseShaped : Term → Prop
  | const (b : Bool) : DenseShaped (.val (.bool b))
  | and {es : List Term} : (∀ e ∈ es, DenseShaped e) → DenseShaped (.call "and" es)
  | or {es : List Term} : (∀ e ∈ es, DenseShaped e) → DenseShaped (.call "or" es)
  | not {e : Term} : DenseShaped e → DenseShaped (.call "not" [e])
  | cmp {op : String} {r : XRel} {l r' : Term} : XRel.ofOp op = some r → Atomic l → Atomic r' →
      DenseShaped (.call op [l, r'])

/-- Every domain of the heading is the rat kind. -/
def Heading.AllRat (h : Heading) : Prop := ∀ p ∈ h, p.2 = .kind .rat

/-- A relation in the dense class. -/
structure DenseClass (u : Unrel) : Prop where
  wf : u.WF
  rat : u.heading.AllRat
  shaped : DenseShaped u.term

/-! ## A dense-shaped term never refuses -/

theorem Heading.AllRat.lookup {h : Heading} (hr : h.AllRat) {a : String} {d : Domain}
    (hd : h.lookup a = some d) : d = .kind .rat := hr _ (lookup_mem hd)

/-- An atomic operand that reads only the heading is an exact number on a fitting tuple. -/
theorem atomic_eval {h : Heading} (hr : h.AllRat) {t : Tuple} (f : t.Fits h) {o : Term}
    (ho : Atomic o) (hR : ∀ x ∈ o.attrs, x ∈ h.attrs) :
    ∃ v q, o.eval t = .ok v ∧ v.exact? = some q := by
  rcases ho with ⟨b, rfl⟩ | ⟨v, rfl, hv⟩
  · have hb : b ∈ h.attrs := hR b (by simp [Term.attrs])
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((f.get?_isSome b).mpr hb)
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp hb)
    have hmem := f.dom (b, v) (lookup_mem hv) d hd
    rw [hr.lookup hd] at hmem
    obtain ⟨q, hq⟩ := rat_has (by simpa [Domain.mem] using hmem)
    exact ⟨v, q, by simp [Term.eval, hv], hq⟩
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hv
    exact ⟨v, q, by simp [Term.eval], hq⟩

theorem DenseShaped.total {h : Heading} (hr : h.AllRat) {t : Tuple} (f : t.Fits h) :
    ∀ {e : Term}, DenseShaped e → (∀ x ∈ e.attrs, x ∈ h.attrs) → ∃ b, e.holds t = .ok b := by
  intro e he
  induction he with
  | const b => intro _; exact ⟨b, Term.holds_ok.mpr (by simp [Term.eval])⟩
  | @and es _ ih =>
    intro hR
    have hg : ∀ x ∈ es, x.holds t = .ok (bv t x) := fun x hx => by
      obtain ⟨b, hb⟩ := ih x hx (attrs_sub_call hx hR); rw [hb, bv_eq hb]
    exact ⟨_, holds_andN hg⟩
  | @or es _ ih =>
    intro hR
    have hg : ∀ x ∈ es, x.holds t = .ok (bv t x) := fun x hx => by
      obtain ⟨b, hb⟩ := ih x hx (attrs_sub_call hx hR); rw [hb, bv_eq hb]
    exact ⟨_, holds_orN hg⟩
  | @not e _ ih =>
    intro hR
    obtain ⟨b, hb⟩ := ih (attrs_sub_call List.mem_cons_self hR)
    exact ⟨!b, holds_not1.mpr ⟨b, hb, rfl⟩⟩
  | @cmp op r l r' hop hl hr' =>
    intro hR
    have hop := XRel.ofOp_some hop
    subst hop
    obtain ⟨v, q, hv, hq⟩ := atomic_eval hr f hl (attrs_sub_call List.mem_cons_self hR)
    obtain ⟨w, q', hw, hq'⟩ := atomic_eval hr f hr'
      (attrs_sub_call (List.mem_cons_of_mem _ List.mem_cons_self) hR)
    exact ⟨_, holds_cmp r hv hq hw hq'⟩

theorem DenseClass.total {u : Unrel} (hu : DenseClass u) : u.Total :=
  fun _ f => hu.shaped.total hu.rat f hu.wf.reads

/-! ## σ, ∪, ∩, −, ⋈ and ρ keep the class -/

theorem shaped_pair {op : String} {x y : Term} (hop : op = "and" ∨ op = "or")
    (hx : DenseShaped x) (hy : DenseShaped y) : DenseShaped (.call op [x, y]) := by
  have : ∀ e ∈ [x, y], DenseShaped e := by
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> assumption
  rcases hop with rfl | rfl
  · exact .and this
  · exact .or this

theorem DenseClass.select {u w : Unrel} {p : Term} (hu : DenseClass u) (hp : DenseShaped p)
    (h : u.select p = .ok w) : DenseClass w := by
  obtain ⟨hh, ht⟩ := Unrel.select_heading h
  exact ⟨Unrel.select_wf h hu.wf, hh ▸ hu.rat, ht ▸ shaped_pair (.inl rfl) hu.shaped hp⟩

theorem DenseClass.union {u v w : Unrel} (hu : DenseClass u) (hv : DenseClass v)
    (h : u.union v = .ok w) : DenseClass w := by
  obtain ⟨_, hh, ht⟩ := Unrel.union_heading h
  exact ⟨Unrel.union_wf h hu.wf hv.wf, hh ▸ hu.rat, ht ▸ shaped_pair (.inr rfl) hu.shaped hv.shaped⟩

theorem DenseClass.inter {u v w : Unrel} (hu : DenseClass u) (hv : DenseClass v)
    (h : u.inter v = .ok w) : DenseClass w := by
  obtain ⟨_, hh, ht⟩ := Unrel.inter_heading h
  exact ⟨Unrel.inter_wf h hu.wf hv.wf, hh ▸ hu.rat, ht ▸ shaped_pair (.inl rfl) hu.shaped hv.shaped⟩

theorem DenseClass.diff {u v w : Unrel} (hu : DenseClass u) (hv : DenseClass v)
    (h : u.diff v = .ok w) : DenseClass w := by
  obtain ⟨_, hh, ht⟩ := Unrel.diff_heading h
  exact ⟨Unrel.diff_wf h hu.wf hv.wf, hh ▸ hu.rat,
    ht ▸ shaped_pair (.inl rfl) hu.shaped (.not hv.shaped)⟩

theorem DenseClass.join {u v w : Unrel} (hu : DenseClass u) (hv : DenseClass v)
    (h : u.join v = .ok w) : DenseClass w := by
  have hw := Unrel.join_wf h hu.wf hv.wf
  obtain ⟨hj, ht⟩ := Unrel.join_heading h
  refine ⟨hw, fun p hp => ?_, ht ▸ shaped_pair (.inl rfl) hu.shaped hv.shaped⟩
  obtain ⟨_, _, hl⟩ := Finrel.joinHeading_spec hj hu.wf.nodup hv.wf.nodup
  rcases hl p.1 p.2 (mem_lookup hw.nodup hp) with
    ⟨d, hd, (⟨_, e⟩ | ⟨e, he, hi⟩)⟩ | ⟨_, hk⟩
  · rw [e]; exact hu.rat _ hd
  · have h1 : d = .kind .rat := hu.rat _ hd
    have h2 : e = .kind .rat := hv.rat.lookup he
    subst h1; subst h2
    simp [Domain.inter] at hi
    exact hi.symm
  · exact hv.rat.lookup hk

theorem DenseShaped.rename (ren : List (String × String)) :
    ∀ {e : Term}, DenseShaped e → DenseShaped (e.rename ren) := by
  intro e he
  induction he with
  | const b => simp only [Term.rename]; exact .const b
  | @and es _ ih =>
    simp only [Term.rename]
    exact .and fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact ih y hy
  | @or es _ ih =>
    simp only [Term.rename]
    exact .or fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact ih y hy
  | @not e _ ih => simp only [Term.rename, List.map_cons, List.map_nil]; exact .not ih
  | @cmp op r l r' hop hl hr =>
    simp only [Term.rename, List.map_cons, List.map_nil]
    have hat : ∀ {o : Term}, Atomic o → Atomic (o.rename ren) := by
      rintro o (⟨b, rfl⟩ | ⟨v, rfl, hv⟩)
      · exact .inl ⟨Finrel.renameAttr ren b, by simp [Term.rename]⟩
      · exact .inr ⟨v, by simp [Term.rename], hv⟩
    exact .cmp hop (hat hl) (hat hr)

theorem DenseClass.rename {u w : Unrel} {ren : List (String × String)} (hu : DenseClass u)
    (h : u.rename ren = .ok w) : DenseClass w := by
  have hw := Unrel.rename_wf h hu.wf
  obtain ⟨_, rfl⟩ := Unrel.rename_eq h
  refine ⟨hw, fun p hp => ?_, hu.shaped.rename ren⟩
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hu.rat q hq

/-! ## π keeps the class -/

theorem XRel.ofOp_op (r : XRel) : XRel.ofOp r.op = some r := by
  cases r <;> simp [XRel.ofOp, XRel.op]

/-- In a heading of rat attributes, a dense-shaped term is accepted for every attribute. -/
theorem DenseShaped.denseIn {h : Heading} (hr : h.AllRat) (a : String) :
    ∀ {e : Term}, DenseShaped e → (∀ x ∈ e.attrs, x ∈ h.attrs) → DenseIn h a e := by
  intro e he
  induction he with
  | const b => intro _; exact .opq (by simp [Term.attrs])
  | @and es _ ih => intro hR; exact .and fun x hx => ih x hx (attrs_sub_call hx hR)
  | @or es _ ih => intro hR; exact .or fun x hx => ih x hx (attrs_sub_call hx hR)
  | @not e _ ih => intro hR; exact .not (ih (attrs_sub_call List.mem_cons_self hR))
  | @cmp op r l r' hop hl hr' =>
    intro hR
    have hop' : ∀ {o : Term}, Atomic o → (∀ x ∈ o.attrs, x ∈ h.attrs) → operand? h a o = true := by
      rintro o (⟨b, rfl⟩ | ⟨v, rfl, hv⟩) hRo
      · by_cases hb : b = a
        · subst hb; simp [operand?, isAttr]
        · have hbm : b ∈ h.attrs := hRo b (by simp [Term.attrs])
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp hbm)
          rw [hr.lookup hd] at hd
          simp [operand?, isAttr, numOperand?, hb, hd, Domain.numeric]
      · simp [operand?, isAttr, numOperand?, hv]
    exact .cmp hop (hop' hl (attrs_sub_call List.mem_cons_self hR))
      (hop' hr' (attrs_sub_call (List.mem_cons_of_mem _ List.mem_cons_self) hR))

/-- A literal whose opaque part has the shape `Sh` and whose comparison's operand has the
shape `At` (shared with the linear class's closure, `Rasso.LinClosure`). -/
def LitShapedG (Sh At : Term → Prop) : Lit → Prop
  | .opq _ e => Sh e
  | .atom x => At x.2
  | .const _ => True

/-- What the normal form of a dense-shaped term holds. -/
abbrev LitShaped : Lit → Prop := LitShapedG DenseShaped Atomic

theorem dnf_shaped (a : String) :
    ∀ {e : Term}, DenseShaped e → ∀ (p : Bool), ∀ c ∈ dnf a p e, ∀ l ∈ c, LitShaped l := by
  have opq : ∀ {e : Term} (p : Bool), DenseShaped e → a ∉ e.attrs →
      ∀ c ∈ dnf a p e, ∀ l ∈ c, LitShaped l := by
    intro e p he hna c hc l hl
    rw [dnf, NF.dnf_opq hna] at hc
    simp only [List.mem_singleton] at hc; subst hc
    simp only [List.mem_singleton] at hl; subst hl
    exact he
  intro e he
  induction he with
  | const b => intro p; exact opq p (.const b) (by simp [Term.attrs])
  | @and es hes ih =>
    intro p
    by_cases hca : a ∈ (Term.call "and" es).attrs
    case neg => exact opq p (.and hes) hca
    rw [dnf, NF.dnf_and hca]
    cases p
    · intro c hc l hl
      obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
      exact ih y hy false c hc l hl
    · exact foldr_conj_all es fun y hy => ih y hy true
  | @or es hes ih =>
    intro p
    by_cases hca : a ∈ (Term.call "or" es).attrs
    case neg => exact opq p (.or hes) hca
    rw [dnf, NF.dnf_or hca]
    cases p
    · exact foldr_conj_all es fun y hy => ih y hy false
    · intro c hc l hl
      obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
      exact ih y hy true c hc l hl
  | @not e he ih =>
    intro p
    by_cases hca : a ∈ (Term.call "not" [e]).attrs
    case neg => exact opq p (.not he) hca
    rw [dnf, NF.dnf_not hca]
    exact ih (!p)
  | @cmp op r l' r' hop hl hr =>
    intro p
    by_cases hca : a ∈ (Term.call op [l', r']).attrs
    case neg => exact opq p (.cmp hop hl hr) hca
    obtain ⟨h1, h2, h3⟩ := XRel.ofOp_ne hop
    rw [dnf, NF.dnf_leaf h1 h2 h3 hca, leaf_cmp hop]
    intro c hc l hl'
    unfold atom at hc
    by_cases il : isAttr a l' = true
    · by_cases ir : isAttr a r' = true
      · simp only [il, ir, ↓reduceIte, List.mem_singleton] at hc; subst hc
        simp only [List.mem_singleton] at hl'; subst hl'; trivial
      · simp only [il, ir, ↓reduceIte, Bool.false_eq_true] at hc
        obtain ⟨s', _, rfl⟩ := List.mem_map.mp hc
        simp only [List.mem_singleton] at hl'; subst hl'; exact hr
    · simp only [il, ↓reduceIte, Bool.false_eq_true] at hc
      obtain ⟨s', _, rfl⟩ := List.mem_map.mp hc
      simp only [List.mem_singleton] at hl'; subst hl'; exact hl

/-- Fourier's step keeps comparisons of operands of shape `At`. -/
theorem xpart_shaped {Sh At : Term → Prop}
    (hcmp : ∀ (r : XRel) {l r' : Term}, At l → At r' → Sh (.call r.op [l, r']))
    {xs : List (XRel × Term)} (hat : ∀ {r : XRel} {τ : Term}, (r, τ) ∈ xs → At τ) :
    ∀ e ∈ xpart xs, Sh e := by
  intro e he
  unfold xpart at he
  split at he
  · rename_i r₀ τ₀ hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    exact hcmp p.1 (hat (List.mem_of_find?_eq_some hf)) (hat hp)
  · obtain ⟨lo, hlo, he⟩ := List.mem_flatMap.mp he
    obtain ⟨up, hup, rfl⟩ := List.mem_map.mp he
    rw [op_ltle]
    have hl : At lo.1 := by
      rcases mem_lows.mp hlo with ⟨_, hm⟩ | ⟨_, hm⟩ <;> exact hat hm
    have hu : At up.1 := by
      rcases mem_ups.mp hup with ⟨_, hm⟩ | ⟨_, hm⟩ <;> exact hat hm
    exact hcmp _ hl hu

/-- One `and` with `x` removed keeps a shape `Sh` that holds the Boolean constants, `not`, and
comparisons of operands of shape `At`. -/
theorem elimConj_shapedG {Sh At : Term → Prop} (hconst : ∀ b, Sh (.val (.bool b)))
    (hnot : ∀ {e}, Sh e → Sh (.call "not" [e]))
    (hcmp : ∀ (r : XRel) {l r' : Term}, At l → At r' → Sh (.call r.op [l, r']))
    {c : List Lit} (hc : ∀ l ∈ c, LitShapedG Sh At l) :
    ∀ e ∈ elimConj c, Sh e := by
  intro e he
  simp only [elimConj, NF.elimConj] at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨l, hl, he⟩ := List.mem_filterMap.mp he
    have hs := hc l hl
    cases l with
    | opq p e' =>
      simp only [NF.Lit.rest, Option.some.injEq] at he; subst he
      cases p
      · exact hnot hs
      · exact hs
    | const b =>
      simp only [NF.Lit.rest, Option.some.injEq] at he; subst he; exact hconst b
    | atom _ => simp [NF.Lit.rest] at he
  · have hat : ∀ {r : XRel} {τ : Term}, (r, τ) ∈ c.filterMap NF.Lit.atom? → At τ :=
      fun hm => hc _ (NF.mem_atoms.mp hm)
    exact xpart_shaped hcmp hat e he

theorem elimConj_shaped {c : List Lit} (hc : ∀ l ∈ c, LitShaped l) :
    ∀ e ∈ elimConj c, DenseShaped e :=
  elimConj_shapedG .const .not (fun r _ _ hl hr => .cmp (XRel.ofOp_op r) hl hr) hc

theorem elim_shaped (a : String) {e : Term} (he : DenseShaped e) : DenseShaped (elim a e) := by
  unfold elim NF.elim
  refine .or fun x hx => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact .and (elimConj_shaped (dnf_shaped a he true c hc))

theorem DenseClass.accepts {u : Unrel} (hu : DenseClass u) {a : String}
    (ha : a ∈ u.heading.attrs) : Class.Accepts .dense u a := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp ha)
  have := hu.rat.lookup hd
  subst this
  exact ⟨hd, hu.shaped.denseIn hu.rat a hu.wf.reads⟩

theorem DenseClass.firstIn {u : Unrel} (hu : DenseClass u) {a : String}
    (ha : a ∈ u.heading.attrs) : Class.FirstIn Class.all u a .dense := by
  have hnf : ¬ Class.Accepts .finite u a := by
    rintro ⟨d, vs, hd, hvs⟩
    rw [hu.rat.lookup hd] at hvs
    simp [Domain.values?] at hvs
  exact .inr ⟨hnf, .inl ⟨hu.accepts ha, rfl⟩⟩

theorem DenseClass.dropOne {u : Unrel} (hu : DenseClass u) {a : String}
    (ha : a ∈ u.heading.attrs) : DenseClass (u.dropOne a .dense) := by
  obtain ⟨hw, _⟩ := dropOne_wf (hu.accepts ha) hu.wf hu.total
  exact ⟨hw, fun p hp => hu.rat p (List.mem_filter.mp hp).1, elim_shaped a hu.shaped⟩

theorem DenseClass.eliminate : ∀ {u : Unrel} {l : List String}, DenseClass u → l.Nodup →
    (∀ x ∈ l, x ∈ u.heading.attrs) →
    AllAccepted u l ∧ ∀ w, u.eliminate l = .ok w → DenseClass w
  | u, [], hu, _, _ => by
    refine ⟨trivial, fun w h => ?_⟩
    simp only [Unrel.eliminate, Except.ok.injEq] at h; subst h; exact hu
  | u, a :: rest, hu, hn, hl => by
    have ha := hl a List.mem_cons_self
    have hrest : ∀ x ∈ rest, x ∈ (u.dropOne a .dense).heading.attrs := fun x hx =>
      dropOne_attrs.mpr ⟨hl x (List.mem_cons_of_mem _ hx),
        fun e => (List.nodup_cons.mp hn).1 (e ▸ hx)⟩
    obtain ⟨hacc, hel⟩ := DenseClass.eliminate (hu.dropOne ha) (List.nodup_cons.mp hn).2 hrest
    refine ⟨⟨.dense, hu.firstIn ha, hacc⟩, fun w h => ?_⟩
    have hr : recognise u a = .ok .dense := recognise_ok_iff.mpr (hu.firstIn ha)
    simp only [Unrel.eliminate, hr, bind, Except.bind] at h
    exact hel w h

theorem dropOrder_sub {h : Heading} {as : List String} :
    ∀ x ∈ dropOrder h as, x ∈ h.attrs := fun _ hx => (mem_dropOrder.mp hx).1

/-- π never refuses a relation in the dense class, except for its checks on the list. -/
theorem DenseClass.project_ok {u : Unrel} {as : List String} (hu : DenseClass u)
    (hn : as.Nodup) (hin : ∀ a ∈ as, a ∈ u.heading.attrs) : ∃ w, u.project as = .ok w :=
  project_ok_iff.mpr ⟨hn, hin,
    (DenseClass.eliminate hu (dropOrder_nodup hu.wf.nodup) dropOrder_sub).1⟩

theorem DenseClass.project {u w : Unrel} {as : List String} (hu : DenseClass u)
    (h : u.project as = .ok w) : DenseClass w := by
  obtain ⟨hw, _, _⟩ := project_sound h hu.wf hu.total
  have hpk := project_pick h
  refine ⟨hw, fun p hp => ?_, ?_⟩
  · exact hu.rat.lookup (Heading.pick_lookup hpk p.1 p.2 (mem_lookup hw.nodup hp))
  · rw [project_eq] at h
    split at h
    · cases h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i w' hw'
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ((DenseClass.eliminate hu (dropOrder_nodup hu.wf.nodup) dropOrder_sub).2 w' hw').shaped

end Rasso
