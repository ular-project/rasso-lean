import Rasso.DenseClosure

/-!
# Rasso: the equality class as a global class

For `k` the symbol, string or int kind, a relation is in the equality class over `k` when it is
well formed, every domain of its heading is the whole `k` kind, and its term is
*equality-shaped*: `and`, `or`, `not` with one operand, Boolean constants, and `=` of two
operands, each an attribute or a value of `k`. Such a term never refuses on a fitting tuple,
so the relation is total. σ with an equality-shaped term, ⋈, ∪, ∩, −, ρ and π keep the class,
and π never refuses a relation in it except for its two checks on the attribute list.

Over rat, dense order comes first and takes these terms; an
equality-shaped term over rat is dense-shaped, so the dense class (`DenseClass`) covers it.
-/

namespace Rasso

open Equality
open NF (attrs_sub_call bv bv_eq foldr_conj_all)

/-- An operand of an equality-shaped `=`: an attribute, or a value of `k`. -/
def EqAtomic (k : Kind) (o : Term) : Prop := (∃ b, o = .attr b) ∨ ∃ v, o = .val v ∧ k.has v = true

/-- A term of the equality class's global shape over `k`. -/
inductive EqShaped (k : Kind) : Term → Prop
  | const (b : Bool) : EqShaped k (.val (.bool b))
  | and {es : List Term} : (∀ e ∈ es, EqShaped k e) → EqShaped k (.call "and" es)
  | or {es : List Term} : (∀ e ∈ es, EqShaped k e) → EqShaped k (.call "or" es)
  | not {e : Term} : EqShaped k e → EqShaped k (.call "not" [e])
  | eq {l r : Term} : EqAtomic k l → EqAtomic k r → EqShaped k (.call "=" [l, r])

/-- Every domain of the heading is the whole `k` kind. -/
def Heading.AllKind (k : Kind) (h : Heading) : Prop := ∀ p ∈ h, p.2 = .kind k

/-- A relation in the equality class over `k`. -/
structure EqClass (k : Kind) (u : Unrel) : Prop where
  wf : u.WF
  kind : u.heading.AllKind k
  shaped : EqShaped k u.term

/-! ## An equality-shaped term never refuses -/

theorem Heading.AllKind.lookup {k : Kind} {h : Heading} (hr : h.AllKind k) {a : String}
    {d : Domain} (hd : h.lookup a = some d) : d = .kind k := hr _ (lookup_mem hd)

/-- An atomic operand that reads only the heading is a value of `k` on a fitting tuple. -/
theorem eqAtomic_eval {k : Kind} {h : Heading} (hr : h.AllKind k) {t : Tuple} (f : t.Fits h)
    {o : Term} (ho : EqAtomic k o) (hR : ∀ x ∈ o.attrs, x ∈ h.attrs) :
    ∃ v, o.eval t = .ok v ∧ (Domain.kind k).mem v = true := by
  rcases ho with ⟨b, rfl⟩ | ⟨v, rfl, hv⟩
  · have hb : b ∈ h.attrs := hR b (by simp [Term.attrs])
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((f.get?_isSome b).mpr hb)
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp hb)
    have hmem := f.dom (b, v) (lookup_mem hv) d hd
    rw [hr.lookup hd] at hmem
    exact ⟨v, by simp [Term.eval, hv], hmem⟩
  · exact ⟨v, by simp [Term.eval], hv⟩

theorem EqShaped.total {k : Kind} (hk : infinite? (.kind k) = true) {h : Heading}
    (hr : h.AllKind k) {t : Tuple} (f : t.Fits h) :
    ∀ {e : Term}, EqShaped k e → (∀ x ∈ e.attrs, x ∈ h.attrs) → ∃ b, e.holds t = .ok b := by
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
  | @eq l r hl hr' =>
    intro hR
    obtain ⟨v, hv, hmv⟩ := eqAtomic_eval hr f hl (attrs_sub_call List.mem_cons_self hR)
    obtain ⟨w, hw, hmw⟩ := eqAtomic_eval hr f hr'
      (attrs_sub_call (List.mem_cons_of_mem _ List.mem_cons_self) hR)
    exact ⟨_, holds_eq hk hv hmv hw hmw⟩

theorem EqClass.total {k : Kind} (hk : infinite? (.kind k) = true) {u : Unrel}
    (hu : EqClass k u) : u.Total :=
  fun _ f => hu.shaped.total hk hu.kind f hu.wf.reads

/-! ## σ, ∪, ∩, −, ⋈ and ρ keep the class -/

theorem eqShaped_pair {k : Kind} {op : String} {x y : Term} (hop : op = "and" ∨ op = "or")
    (hx : EqShaped k x) (hy : EqShaped k y) : EqShaped k (.call op [x, y]) := by
  have : ∀ e ∈ [x, y], EqShaped k e := by
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> assumption
  rcases hop with rfl | rfl
  · exact .and this
  · exact .or this

variable {k : Kind}

theorem EqClass.select {u w : Unrel} {p : Term} (hu : EqClass k u) (hp : EqShaped k p)
    (h : u.select p = .ok w) : EqClass k w := by
  obtain ⟨hh, ht⟩ := Unrel.select_heading h
  exact ⟨Unrel.select_wf h hu.wf, hh ▸ hu.kind, ht ▸ eqShaped_pair (.inl rfl) hu.shaped hp⟩

theorem EqClass.union {u v w : Unrel} (hu : EqClass k u) (hv : EqClass k v)
    (h : u.union v = .ok w) : EqClass k w := by
  obtain ⟨_, hh, ht⟩ := Unrel.union_heading h
  exact ⟨Unrel.union_wf h hu.wf hv.wf, hh ▸ hu.kind,
    ht ▸ eqShaped_pair (.inr rfl) hu.shaped hv.shaped⟩

theorem EqClass.inter {u v w : Unrel} (hu : EqClass k u) (hv : EqClass k v)
    (h : u.inter v = .ok w) : EqClass k w := by
  obtain ⟨_, hh, ht⟩ := Unrel.inter_heading h
  exact ⟨Unrel.inter_wf h hu.wf hv.wf, hh ▸ hu.kind,
    ht ▸ eqShaped_pair (.inl rfl) hu.shaped hv.shaped⟩

theorem EqClass.diff {u v w : Unrel} (hu : EqClass k u) (hv : EqClass k v)
    (h : u.diff v = .ok w) : EqClass k w := by
  obtain ⟨_, hh, ht⟩ := Unrel.diff_heading h
  exact ⟨Unrel.diff_wf h hu.wf hv.wf, hh ▸ hu.kind,
    ht ▸ eqShaped_pair (.inl rfl) hu.shaped (.not hv.shaped)⟩

theorem EqClass.join {u v w : Unrel} (hu : EqClass k u) (hv : EqClass k v)
    (h : u.join v = .ok w) : EqClass k w := by
  have hw := Unrel.join_wf h hu.wf hv.wf
  obtain ⟨hj, ht⟩ := Unrel.join_heading h
  refine ⟨hw, fun p hp => ?_, ht ▸ eqShaped_pair (.inl rfl) hu.shaped hv.shaped⟩
  obtain ⟨_, _, hl⟩ := Finrel.joinHeading_spec hj hu.wf.nodup hv.wf.nodup
  rcases hl p.1 p.2 (mem_lookup hw.nodup hp) with
    ⟨d, hd, (⟨_, e⟩ | ⟨e, he, hi⟩)⟩ | ⟨_, hk⟩
  · rw [e]; exact hu.kind _ hd
  · have h1 : d = .kind k := hu.kind _ hd
    have h2 : e = .kind k := hv.kind.lookup he
    subst h1; subst h2
    simp [Domain.inter] at hi
    exact hi.symm
  · exact hv.kind.lookup hk

theorem EqShaped.rename (ren : List (String × String)) :
    ∀ {e : Term}, EqShaped k e → EqShaped k (e.rename ren) := by
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
  | @eq l r hl hr =>
    simp only [Term.rename, List.map_cons, List.map_nil]
    have hat : ∀ {o : Term}, EqAtomic k o → EqAtomic k (o.rename ren) := by
      rintro o (⟨b, rfl⟩ | ⟨v, rfl, hv⟩)
      · exact .inl ⟨Finrel.renameAttr ren b, by simp [Term.rename]⟩
      · exact .inr ⟨v, by simp [Term.rename], hv⟩
    exact .eq (hat hl) (hat hr)

theorem EqClass.rename {u w : Unrel} {ren : List (String × String)} (hu : EqClass k u)
    (h : u.rename ren = .ok w) : EqClass k w := by
  have hw := Unrel.rename_wf h hu.wf
  obtain ⟨_, rfl⟩ := Unrel.rename_eq h
  refine ⟨hw, fun p hp => ?_, hu.shaped.rename ren⟩
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hu.kind q hq

/-! ## π keeps the class -/

/-- In a heading of `k` attributes, an equality-shaped term is accepted for every attribute. -/
theorem EqShaped.eqIn {h : Heading} (hr : h.AllKind k) (a : String) :
    ∀ {e : Term}, EqShaped k e → (∀ x ∈ e.attrs, x ∈ h.attrs) → EqIn h a (.kind k) e := by
  intro e he
  induction he with
  | const b => intro _; exact .opq (by simp [Term.attrs])
  | @and es _ ih => intro hR; exact .and fun x hx => ih x hx (attrs_sub_call hx hR)
  | @or es _ ih => intro hR; exact .or fun x hx => ih x hx (attrs_sub_call hx hR)
  | @not e _ ih => intro hR; exact .not (ih (attrs_sub_call List.mem_cons_self hR))
  | @eq l r hl hr' =>
    intro hR
    have hop' : ∀ {o : Term}, EqAtomic k o → (∀ x ∈ o.attrs, x ∈ h.attrs) →
        operand? h a (.kind k) o = true := by
      rintro o (⟨b, rfl⟩ | ⟨v, rfl, hv⟩) hRo
      · by_cases hb : b = a
        · subst hb; simp [operand?, isAttr]
        · have hbm : b ∈ h.attrs := hRo b (by simp [Term.attrs])
          obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp hbm)
          rw [hr.lookup hd] at hd
          simp [operand?, isAttr, inDom, hb, hd, Domain.subset?]
      · simp [operand?, isAttr, inDom, Domain.mem, hv]
    exact .leaf (by decide) (by decide) (by decide)
      ⟨rfl, l, r, rfl, hop' hl (attrs_sub_call List.mem_cons_self hR),
        hop' hr' (attrs_sub_call (List.mem_cons_of_mem _ List.mem_cons_self) hR)⟩

/-- What the normal form of an equality-shaped term holds. -/
def EqLitShaped (k : Kind) : Equality.Lit → Prop
  | .opq _ e => EqShaped k e
  | .atom x => EqAtomic k x.2
  | .const _ => True

theorem eq_dnf_shaped (a : String) :
    ∀ {e : Term}, EqShaped k e → ∀ (p : Bool), ∀ c ∈ NF.dnf (leaf a) a p e, ∀ l ∈ c,
      EqLitShaped k l := by
  have opq : ∀ {e : Term} (p : Bool), EqShaped k e → a ∉ e.attrs →
      ∀ c ∈ NF.dnf (leaf a) a p e, ∀ l ∈ c, EqLitShaped k l := by
    intro e p he hna c hc l hl
    rw [NF.dnf_opq hna] at hc
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
    rw [NF.dnf_and hca]
    cases p
    · intro c hc l hl
      obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
      exact ih y hy false c hc l hl
    · exact foldr_conj_all es fun y hy => ih y hy true
  | @or es hes ih =>
    intro p
    by_cases hca : a ∈ (Term.call "or" es).attrs
    case neg => exact opq p (.or hes) hca
    rw [NF.dnf_or hca]
    cases p
    · exact foldr_conj_all es fun y hy => ih y hy false
    · intro c hc l hl
      obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
      exact ih y hy true c hc l hl
  | @not e he ih =>
    intro p
    by_cases hca : a ∈ (Term.call "not" [e]).attrs
    case neg => exact opq p (.not he) hca
    rw [NF.dnf_not hca]
    exact ih (!p)
  | @eq l' r' hl hr =>
    intro p
    by_cases hca : a ∈ (Term.call "=" [l', r']).attrs
    case neg => exact opq p (.eq hl hr) hca
    rw [NF.dnf_leaf (by decide) (by decide) (by decide) hca, leaf_eq]
    intro c hc l hl'
    by_cases il : isAttr a l' = true
    · by_cases ir : isAttr a r' = true
      · simp only [il, ir, ↓reduceIte, List.mem_singleton] at hc; subst hc
        simp only [List.mem_singleton] at hl'; subst hl'; trivial
      · simp only [il, ir, ↓reduceIte, Bool.false_eq_true, List.mem_singleton] at hc; subst hc
        simp only [List.mem_singleton] at hl'; subst hl'; exact hr
    · simp only [il, ↓reduceIte, Bool.false_eq_true, List.mem_singleton] at hc; subst hc
      simp only [List.mem_singleton] at hl'; subst hl'; exact hl

theorem eq_elimConj_shaped {c : List Equality.Lit} (hc : ∀ l ∈ c, EqLitShaped k l) :
    ∀ e ∈ NF.elimConj xpart c, EqShaped k e := by
  intro e he
  simp only [NF.elimConj] at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨l, hl, he⟩ := List.mem_filterMap.mp he
    have hs := hc l hl
    cases l with
    | opq p e' =>
      simp only [NF.Lit.rest, Option.some.injEq] at he; subst he
      cases p
      · exact .not hs
      · exact hs
    | const b =>
      simp only [NF.Lit.rest, Option.some.injEq] at he; subst he; exact .const b
    | atom _ => simp [NF.Lit.rest] at he
  · have hat : ∀ {x : Bool × Term}, x ∈ c.filterMap NF.Lit.atom? → EqAtomic k x.2 :=
      fun hm => hc _ (NF.mem_atoms.mp hm)
    unfold xpart at he
    split at he
    · rename_i b₀ τ₀ hf
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      have h₀ : EqAtomic k τ₀ := hat (List.mem_of_find?_eq_some hf)
      cases q.1
      · exact .not (.eq h₀ (hat hq))
      · exact .eq h₀ (hat hq)
    · cases he

theorem eq_elim_shaped (a : String) {e : Term} (he : EqShaped k e) : EqShaped k (elim a e) := by
  unfold elim NF.elim
  refine .or fun x hx => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact .and (eq_elimConj_shaped (eq_dnf_shaped a he true c hc))

variable (hk : infinite? (.kind k) = true)
include hk

theorem EqClass.accepts {u : Unrel} (hu : EqClass k u) {a : String}
    (ha : a ∈ u.heading.attrs) : Class.Accepts .equality u a := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp ha)
  have := hu.kind.lookup hd
  subst this
  exact ⟨_, hd, hk, hu.shaped.eqIn hu.kind a hu.wf.reads⟩

theorem EqClass.firstIn {u : Unrel} (hu : EqClass k u) {a : String}
    (ha : a ∈ u.heading.attrs) : Class.FirstIn Class.all u a .equality := by
  have hk' : k = .symbol ∨ k = .string ∨ k = .int := by
    cases k <;> simp_all [infinite?]
  have hnf : ¬ Class.Accepts .finite u a := by
    rintro ⟨d, vs, hd, hvs⟩
    rw [hu.kind.lookup hd] at hvs
    rcases hk' with rfl | rfl | rfl <;> simp [Domain.values?] at hvs
  have hnd : ¬ Class.Accepts .dense u a := by
    rintro ⟨hd, _⟩
    obtain ⟨d, hd'⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp ha)
    rw [hd', hu.kind.lookup hd'] at hd
    rcases hk' with rfl | rfl | rfl <;> simp at hd
  exact .inr ⟨hnf, .inr ⟨hnd, .inl ⟨hu.accepts hk ha, rfl⟩⟩⟩

theorem EqClass.dropOne {u : Unrel} (hu : EqClass k u) {a : String}
    (ha : a ∈ u.heading.attrs) : EqClass k (u.dropOne a .equality) := by
  obtain ⟨hw, _⟩ := dropOne_wf (hu.accepts hk ha) hu.wf (hu.total hk)
  exact ⟨hw, fun p hp => hu.kind p (List.mem_filter.mp hp).1, eq_elim_shaped a hu.shaped⟩

theorem EqClass.eliminate : ∀ {u : Unrel} {l : List String}, EqClass k u → l.Nodup →
    (∀ x ∈ l, x ∈ u.heading.attrs) →
    AllAccepted u l ∧ ∀ w, u.eliminate l = .ok w → EqClass k w
  | u, [], hu, _, _ => by
    refine ⟨trivial, fun w h => ?_⟩
    simp only [Unrel.eliminate, Except.ok.injEq] at h; subst h; exact hu
  | u, a :: rest, hu, hn, hl => by
    have ha := hl a List.mem_cons_self
    have hrest : ∀ x ∈ rest, x ∈ (u.dropOne a .equality).heading.attrs := fun x hx =>
      dropOne_attrs.mpr ⟨hl x (List.mem_cons_of_mem _ hx),
        fun e => (List.nodup_cons.mp hn).1 (e ▸ hx)⟩
    obtain ⟨hacc, hel⟩ := EqClass.eliminate (hu.dropOne hk ha) (List.nodup_cons.mp hn).2 hrest
    refine ⟨⟨.equality, hu.firstIn hk ha, hacc⟩, fun w h => ?_⟩
    have hr : recognise u a = .ok .equality := recognise_ok_iff.mpr (hu.firstIn hk ha)
    simp only [Unrel.eliminate, hr, bind, Except.bind] at h
    exact hel w h

/-- π never refuses a relation in the equality class, except for its checks on the list. -/
theorem EqClass.project_ok {u : Unrel} {as : List String} (hu : EqClass k u)
    (hn : as.Nodup) (hin : ∀ a ∈ as, a ∈ u.heading.attrs) : ∃ w, u.project as = .ok w :=
  project_ok_iff.mpr ⟨hn, hin,
    (EqClass.eliminate hk hu (dropOrder_nodup hu.wf.nodup) dropOrder_sub).1⟩

theorem EqClass.project {u w : Unrel} {as : List String} (hu : EqClass k u)
    (h : u.project as = .ok w) : EqClass k w := by
  obtain ⟨hw, _, _⟩ := project_sound h hu.wf (hu.total hk)
  have hpk := project_pick h
  refine ⟨hw, fun p hp => ?_, ?_⟩
  · exact hu.kind.lookup (Heading.pick_lookup hpk p.1 p.2 (mem_lookup hw.nodup hp))
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
    exact ((EqClass.eliminate hk hu (dropOrder_nodup hu.wf.nodup) dropOrder_sub).2 w' hw').shaped

end Rasso
