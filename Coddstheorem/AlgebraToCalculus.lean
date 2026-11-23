import Coddstheorem.Tests
import Coddstheorem.Fresh
import Rasso.Bridge.Finrel
import Rasso.ESO.Blocks

/-!
# Codd's theorem for Rasso: from the algebra to the calculus (theorem A)

In plain words: each algebra query `e` is translated into a calculus formula `tr e`
(Codd 1972; Abiteboul, Hull and Vianu 1995, Lemma 5.3.11, whose construction this
follows case for case, here for a named algebra with ⋈, ∩ and ρ besides):

* a stored relation is its atom; a constant relation is "one of its rows";
* σ is "and the test"; ⋈, × and ∩ are "and"; ∪ is "or"; − is "and not";
* π is "there is a value for each dropped attribute";
* ρ only changes which variable stands for which attribute.

`algebra_to_calculus` proves that Rasso's evaluator runs a well-typed `e` on any
database of the schema without refusing, and that the relation it gives holds exactly
the answers of `e.toCalc`, whatever domain the quantifiers range over, as long as it
holds the active domain. So the translation is domain independent
(`toCalc_domainIndependent`).

Conventions: those of `Coddstheorem.Schema` and `Coddstheorem.Algebra`, namely one
domain `D` with `DomOK D`, a well-formed schema, a conforming database.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Coddstheorem

open Rasso Formula

/-! ## Formulas built from lists -/

/-- True on every domain, the empty one included: `∀ z. z = z`. -/
def tt : Formula := .all "%" (.eqv "%" "%")
/-- False on every domain. -/
def ff : Formula := .not tt

def conjF : List Formula → Formula
  | [] => tt
  | φ :: φs => .and φ (conjF φs)

def disjF : List Formula → Formula
  | [] => ff
  | φ :: φs => .or φ (disjF φs)

/-- `∃ x₁ … xₙ. φ`. -/
def exs (xs : List String) (φ : Formula) : Formula := xs.foldr .ex φ

/-! ## The translation -/

/-- The variable for attribute `a` inside π at depth `k` that drops `ds`. -/
def projMap (ds : List String) (μ : String → String) (k : Nat) (a : String) : String :=
  if a ∈ ds then fresh k a else μ a

/-- The attributes π drops. -/
def dropped (as bs : List String) : List String := as.filter fun a => !bs.contains a

/-- Codd's translation of the algebra into the calculus. `μ` gives the variable that
stands for each attribute; `k` is the depth, for fresh names. -/
def tr (S : Schema) (D : Domain) : CRA → (String → String) → Nat → Formula
  | .rel n, μ, _ => .rel n ((S.attrsOf n).map μ)
  | .lit as rows, μ, _ => disjF (rows.map fun row => conjF ((as.zip row).map fun p => .eqc (μ p.1) p.2))
  | .sel t e, μ, k => .and (tr S D e μ k) (t.toFormula μ)
  | .proj bs e, μ, k =>
    let ds := dropped ((e.check S D).getD []) bs
    exs (ds.map (fresh k)) (tr S D e (projMap ds μ k) (k + 1))
  | .ren r e, μ, k => tr S D e (fun a => μ (Finrel.renameAttr r a)) k
  | .join e f, μ, k | .prod e f, μ, k | .inter e f, μ, k => .and (tr S D e μ k) (tr S D f μ k)
  | .union e f, μ, k => .or (tr S D e μ k) (tr S D f μ k)
  | .diff e f, μ, k => .and (tr S D e μ k) (.not (tr S D f μ k))

/-- The calculus query of an algebra query: output attribute `a` held by variable `a`. -/
def CRA.toCalc (S : Schema) (D : Domain) (e : CRA) : Query :=
  ⟨((e.check S D).getD []).map fun a => (a, a), tr S D e id 0⟩

/-! ## What the induction carries -/

/-- The relation `r` is what the formula `φ` says, over attributes `as` read through `μ`. -/
structure Inv (dom : Value → Prop) (S : Schema) (D : Domain) (env : Env) (as : List String)
    (μ : String → String) (φ : Formula) (r : Finrel) : Prop where
  wf : r.WF
  head : HeadIs D as r.heading
  sat : ∀ ρ, Sat dom S env φ ρ ↔ ∃ t ∈ r.tuples, Match as μ ρ t
  vals : ∀ t ∈ r.tuples, ∀ p ∈ t, dom p.2

/-- No variable `μ` gives an attribute of `as` is a fresh name of depth `k` or more. -/
def FreshFrom (μ : String → String) (as : List String) (k : Nat) : Prop :=
  ∀ a ∈ as, ∀ j b, k ≤ j → isAttribute b = true → μ a ≠ fresh j b

def InjOn (μ : String → String) (as : List String) : Prop :=
  ∀ a ∈ as, ∀ b ∈ as, μ a = μ b → a = b

/-! ## What `check` guarantees about attributes -/

theorem lookup_schema {S : Schema} {n : String} {as : List String} (h : S.lookup n = some as) :
    (n, as) ∈ S := lookup_mem h

theorem check_attrs {S : Schema} {D : Domain} (hS : S.WF) :
    (e : CRA) → {as : List String} → e.check S D = some as →
      as.Nodup ∧ ∀ a ∈ as, isAttribute a = true
  | .rel n, as, h => by
    simp only [CRA.check] at h
    have hm := lookup_schema h
    obtain ⟨h1, -, h3⟩ := hS.2 _ hm
    exact ⟨h1, h3⟩
  | .lit bs rows, as, h => by
    simp only [CRA.check] at h
    split at h
    · rename_i hc; cases h
      refine ⟨hc.1, fun a ha => ?_⟩
      exact List.all_eq_true.mp hc.2.1 a ha
    · cases h
  | .sel t e, as, h => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at h
    obtain ⟨as', he, h⟩ := h
    split at h
    · cases h; exact check_attrs hS e he
    · cases h
  | .proj bs e, as, h => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at h
    obtain ⟨as', he, h⟩ := h
    split at h
    · rename_i hc; cases h
      refine ⟨hc.1, fun a ha => (check_attrs hS e he).2 a ?_⟩
      exact List.contains_iff_mem.mp (List.all_eq_true.mp hc.2 a ha)
    · cases h
  | .ren r e, as, h => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at h
    obtain ⟨as', he, h⟩ := h
    split at h
    · rename_i hc; cases h
      refine ⟨hc.2.2.2, fun a ha => ?_⟩
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      cases hl : r.lookup b with
      | none => simpa [hl] using (check_attrs hS e he).2 b hb
      | some c =>
        simp only [hl, Option.getD_some]
        exact List.all_eq_true.mp hc.2.2.1 c (List.mem_map.mpr ⟨(b, c), lookup_mem hl, rfl⟩)
    · cases h
  | .join e f, as, h => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at h
    obtain ⟨as', he, bs', hf, h⟩ := h
    cases h
    obtain ⟨n1, a1⟩ := check_attrs hS e he
    obtain ⟨n2, a2⟩ := check_attrs hS f hf
    refine ⟨List.nodup_append.mpr ⟨n1, n2.filter _, ?_⟩, ?_⟩
    · intro x hx y hy exy
      subst exy
      have := (List.mem_filter.mp hy).2
      simp [List.contains_iff_mem, hx] at this
    · intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact a1 a h
      · exact a2 a (List.mem_filter.mp h).1
  | .prod e f, as, h => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at h
    obtain ⟨as', he, bs', hf, h⟩ := h
    split at h
    · rename_i hc; cases h
      obtain ⟨n1, a1⟩ := check_attrs hS e he
      obtain ⟨n2, a2⟩ := check_attrs hS f hf
      refine ⟨List.nodup_append.mpr ⟨n1, n2, ?_⟩, ?_⟩
      · intro x hx y hy exy
        subst exy
        have := List.all_eq_true.mp hc x hy
        simp [List.contains_iff_mem, hx] at this
      · intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact a1 a h
        · exact a2 a h
    · cases h
  | .union e f, as, h | .diff e f, as, h | .inter e f, as, h => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at h
    obtain ⟨as', he, bs', hf, h⟩ := h
    split at h
    · cases h; exact check_attrs hS e he
    · cases h

/-! ## Satisfaction of the built formulas -/

section Sat
variable {dom : Value → Prop} {S : Schema} {env : Env}

theorem sat_tt (ρ : String → Value) : Sat dom S env tt ρ := fun _ _ => rfl

theorem sat_ff (ρ : String → Value) : ¬ Sat dom S env ff ρ := fun h => h (sat_tt ρ)

theorem sat_conjF (ρ : String → Value) :
    (φs : List Formula) → (Sat dom S env (conjF φs) ρ ↔ ∀ φ ∈ φs, Sat dom S env φ ρ)
  | [] => by simp [conjF, sat_tt]
  | φ :: φs => by simp [conjF, Sat, sat_conjF ρ φs]

theorem sat_disjF (ρ : String → Value) :
    (φs : List Formula) → (Sat dom S env (disjF φs) ρ ↔ ∃ φ ∈ φs, Sat dom S env φ ρ)
  | [] => by simp [disjF, sat_ff]
  | φ :: φs => by simp [disjF, Sat, sat_disjF ρ φs]

/-- `∃ x₁ … xₙ. φ` holds when some assignment, with values in `dom` on the `xᵢ` and equal
to `ρ` elsewhere, satisfies `φ`. -/
theorem sat_exs : (xs : List String) → (φ : Formula) → (ρ : String → Value) →
    (Sat dom S env (exs xs φ) ρ ↔
      ∃ ρ', (∀ x ∈ xs, dom (ρ' x)) ∧ (∀ y, y ∉ xs → ρ' y = ρ y) ∧ Sat dom S env φ ρ')
  | [], φ, ρ => by
    simp only [exs, List.foldr_nil, List.not_mem_nil, not_false_eq_true, forall_const,
      List.mem_nil_iff, false_imp_iff, implies_true, true_and]
    constructor
    · intro h; exact ⟨ρ, fun _ => rfl, h⟩
    · rintro ⟨ρ', h, hs⟩
      have : ρ' = ρ := funext h
      exact this ▸ hs
  | x :: xs, φ, ρ => by
    have ih := fun ρ => sat_exs xs φ ρ
    simp only [exs, List.foldr_cons] at ih ⊢
    simp only [Sat]
    constructor
    · rintro ⟨a, ha, h⟩
      obtain ⟨ρ', h1, h2, h3⟩ := (ih _).mp h
      refine ⟨ρ', fun x' hx' => ?_, fun y hy => ?_, h3⟩
      · by_cases hm : x' ∈ xs
        · exact h1 x' hm
        · have : x' = x := by simpa [hm] using hx'
          subst this
          rw [h2 x' hm, upd_same]; exact ha
      · have hy' : y ∉ xs := fun h => hy (List.mem_cons_of_mem _ h)
        rw [h2 y hy', upd_other (fun e => hy (by rw [e]; exact List.mem_cons_self))]
    · rintro ⟨ρ', h1, h2, h3⟩
      refine ⟨ρ' x, h1 x List.mem_cons_self, (ih _).mpr ⟨ρ', fun x' hx' => h1 x' (List.mem_cons_of_mem _ hx'), fun y hy => ?_, h3⟩⟩
      by_cases e : y = x
      · subst e; rw [upd_same]
      · rw [upd_other e]; exact h2 y (by simp [e, hy])

end Sat

/-! ## The induction -/

theorem zip_map_self (μ : String → String) :
    (as : List String) → as.zip (as.map μ) = as.map fun a => (a, μ a)
  | [] => rfl
  | a :: as => by simp [zip_map_self μ as]

theorem tuplesOf_eq {env : Env} {n : String} {r : Finrel} (h : env.lookup n = some (.finrel r)) :
    tuplesOf env n = r.tuples := by
  simp [tuplesOf, h]

theorem mem_adom {S : Schema} {env : Env} {n : String} {as : List String} (hn : (n, as) ∈ S)
    {t : Tuple} (ht : t ∈ tuplesOf env n) {p : String × Value} (hp : p ∈ t) :
    p.2 ∈ adom S env := by
  simp only [adom, List.mem_flatMap, List.mem_map]
  exact ⟨(n, as), hn, t, ht, p, hp, rfl⟩

/-! ## Helpers for the cases -/

theorem eval_prod2 {env : Env} {e₁ e₂ : Expr} {r₁ r₂ s : Finrel}
    (h₁ : Expr.eval env [] e₁ = .ok (.finrel r₁)) (h₂ : Expr.eval env [] e₂ = .ok (.finrel r₂))
    (hs : r₁.join r₂ = .ok s) (hd : ∀ a ∈ r₁.heading.attrs, a ∉ r₂.heading.attrs) :
    Expr.eval env [] (.nary .product [e₁, e₂]) = .ok (.finrel s) := by
  have hdis : Heading.disjoint "×" r₁.heading r₂.heading = .ok () := by
    unfold Heading.disjoint
    have : (r₁.heading.attrs.filter r₂.heading.attrs.contains).isEmpty = true := by
      rw [List.isEmpty_iff, List.filter_eq_nil_iff]
      intro a ha; simpa using hd a ha
    simp [this]
  rw [Expr.eval]
  simp [h₁, h₂, hs, hdis, Finrel.product, bind, Except.bind, Functor.map, Except.map, Val.asFinrel, List.mapM_cons,
    List.foldlM, pure, Except.pure]

theorem eval_inter2 {env : Env} {e₁ e₂ : Expr} {r₁ r₂ s : Finrel}
    (h₁ : Expr.eval env [] e₁ = .ok (.finrel r₁)) (h₂ : Expr.eval env [] e₂ = .ok (.finrel r₂))
    (hs : r₁.inter r₂ = .ok s) :
    Expr.eval env [] (.nary .intersect [e₁, e₂]) = .ok (.finrel s) := by
  rw [Expr.eval]
  simp [h₁, h₂, hs, bind, Except.bind, Functor.map, Except.map, Val.asFinrel, List.mapM_cons,
    List.foldlM, pure, Except.pure]

theorem inter_heading {r s q : Finrel} (h : r.inter s = .ok q) : q.heading = r.heading := by
  simp only [Finrel.inter, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl

theorem Inv.rep {dom : Value → Prop} {S : Schema} {D : Domain} {env : Env} {as : List String}
    {μ : String → String} {φ : Formula} {r : Finrel} (h : Inv dom S D env as μ φ r) :
    Rep (headerOf D as) (· ∈ r.tuples) r where
  wf := h.wf
  head := h.head
  mem _ := ⟨fun ht => ⟨fits_of_mem h.wf h.head ht, ht⟩, fun h => h.2⟩

theorem Inv.fits {dom : Value → Prop} {S : Schema} {D : Domain} {env : Env} {as : List String}
    {μ : String → String} {φ : Formula} {r : Finrel} (h : Inv dom S D env as μ φ r)
    {t : Tuple} (ht : t ∈ r.tuples) : t.Fits (headerOf D as) := fits_of_mem h.wf h.head ht

/-- An `Inv` over one attribute list holds over any list with the same members. -/
theorem Inv.congr {dom : Value → Prop} {S : Schema} {D : Domain} {env : Env} {as bs : List String}
    {μ : String → String} {φ : Formula} {r : Finrel} (h : Inv dom S D env as μ φ r)
    (e : ∀ a, a ∈ as ↔ a ∈ bs) : Inv dom S D env bs μ φ r where
  wf := h.wf
  head a := (h.head a).trans (headerOf_congr e a)
  sat ρ := by
    rw [h.sat ρ]
    exact ⟨fun ⟨t, ht, hm⟩ => ⟨t, ht, fun a ha => hm a ((e a).mpr ha)⟩,
      fun ⟨t, ht, hm⟩ => ⟨t, ht, fun a ha => hm a ((e a).mp ha)⟩⟩
  vals := h.vals

theorem sameSet_of_all {as bs : List String} (h1 : as.all bs.contains = true)
    (h2 : bs.all as.contains = true) (a : String) : a ∈ as ↔ a ∈ bs :=
  ⟨fun h => List.contains_iff_mem.mp (List.all_eq_true.mp h1 a h),
   fun h => List.contains_iff_mem.mp (List.all_eq_true.mp h2 a h)⟩

theorem InjOn.congr {μ : String → String} {as bs : List String} (h : InjOn μ as)
    (e : ∀ a, a ∈ as ↔ a ∈ bs) : InjOn μ bs :=
  fun a ha b hb => h a ((e a).mpr ha) b ((e b).mpr hb)

theorem FreshFrom.congr {μ : String → String} {as bs : List String} {k : Nat} (h : FreshFrom μ as k)
    (e : ∀ a, a ∈ as ↔ a ∈ bs) : FreshFrom μ bs k :=
  fun a ha => h a ((e a).mpr ha)

theorem InjOn.mono {μ : String → String} {as bs : List String} (h : InjOn μ as)
    (e : ∀ a ∈ bs, a ∈ as) : InjOn μ bs :=
  fun a ha b hb => h a (e a ha) b (e b hb)

theorem FreshFrom.mono {μ : String → String} {as bs : List String} {k : Nat} (h : FreshFrom μ as k)
    (e : ∀ a ∈ bs, a ∈ as) : FreshFrom μ bs k :=
  fun a ha => h a (e a ha)

theorem rep_congrH {H K : Heading} {P : Tuple → Prop} {r : Finrel} (hr : Rep H P r)
    (e : ∀ a, H.lookup a = K.lookup a) : Rep K P r where
  wf := hr.wf
  head a := (hr.head a).trans (e a)
  mem t := by
    rw [hr.mem t]
    exact ⟨fun ⟨f, h⟩ => ⟨f.congr e, h⟩, fun ⟨f, h⟩ => ⟨f.congr fun a => (e a).symm, h⟩⟩

/-- The attributes of a join. -/
def joinAttrs (as bs : List String) : List String := as ++ bs.filter fun b => !as.contains b

theorem mem_joinAttrs {as bs : List String} {a : String} :
    a ∈ joinAttrs as bs ↔ a ∈ as ∨ a ∈ bs := by
  simp only [joinAttrs, List.mem_append, List.mem_filter]
  by_cases h : a ∈ as <;> simp [h, List.contains_iff_mem]

/-- A tuple that agrees with a fitting `u` on `u`'s attributes restricts to `u`. -/
theorem restrict_eq_of_agree {D : Domain} {as : List String} {t u : Tuple} (ht : Tuple.Sorted t)
    (fu : u.Fits (headerOf D as)) (h : ∀ a ∈ as, t.get? a = u.get? a) : t.restrict as = u := by
  apply Tuple.ext_get? (sorted_restrict ht) fu.sorted
  intro a
  rw [get?_restrict]
  split
  · rename_i ha; exact h a ha
  · rename_i ha; exact (fu.get?_none (by rw [attrs_headerOf]; exact ha)).symm

theorem inv_join {dom : Value → Prop} {S : Schema} {D : Domain} {env : Env} {as bs : List String}
    {μ : String → String} {φ ψ : Formula} {r s : Finrel}
    (i1 : Inv dom S D env as μ φ r) (i2 : Inv dom S D env bs μ ψ s)
    (hn : (joinAttrs as bs).Nodup) :
    ∃ q, r.join s = .ok q ∧ Inv dom S D env (joinAttrs as bs) μ (.and φ ψ) q := by
  obtain ⟨q, hq, rq⟩ := rep_join i1.rep i2.rep (fun a d e h1 h2 => by
    rw [lookup_headerOf] at h1 h2
    split at h1 <;> split at h2 <;> simp_all)
  have hH : ∀ a, (joinH (headerOf D as) (headerOf D bs)).lookup a = (headerOf D (joinAttrs as bs)).lookup a := by
    intro a
    rw [lookup_joinH, lookup_headerOf, lookup_headerOf, lookup_headerOf]
    by_cases h1 : a ∈ as
    · simp [h1, mem_joinAttrs]
    · by_cases h2 : a ∈ bs <;> simp [h1, h2, mem_joinAttrs]
  have rq' := rep_congrH rq hH
  simp only [attrs_headerOf] at rq'
  refine ⟨q, hq, rq'.wf, rq'.head, fun ρ => ?_, ?_⟩
  · simp only [Sat, i1.sat, i2.sat]
    constructor
    · rintro ⟨⟨u, hu, hmu⟩, ⟨v, hv, hmv⟩⟩
      have fu := i1.fits hu
      have fv := i2.fits hv
      have hval : ∀ a ∈ joinAttrs as bs, D.mem (ρ (μ a)) = true := by
        intro a ha
        rcases mem_joinAttrs.mp ha with h | h
        · obtain ⟨w, hw, dw, -⟩ := get?_fits fu h
          rw [hmu a h] at hw; cases hw; exact dw
        · obtain ⟨w, hw, dw, -⟩ := get?_fits fv h
          rw [hmv a h] at hw; cases hw; exact dw
      refine ⟨tupOf (joinAttrs as bs) μ ρ, (rq'.mem _).mpr ⟨fits_tupOf hn hval, ?_, ?_⟩,
        match_tupOf hn μ ρ⟩
      · rw [restrict_eq_of_agree (sorted_tupOf hn μ ρ) fu fun a ha => by
          rw [get?_tupOf hn, if_pos (mem_joinAttrs.mpr (Or.inl ha)), hmu a ha]]
        exact hu
      · rw [restrict_eq_of_agree (sorted_tupOf hn μ ρ) fv fun a ha => by
          rw [get?_tupOf hn, if_pos (mem_joinAttrs.mpr (Or.inr ha)), hmv a ha]]
        exact hv
    · rintro ⟨t, ht, hm⟩
      obtain ⟨-, h1, h2⟩ := (rq'.mem t).mp ht
      refine ⟨⟨_, h1, fun a ha => ?_⟩, ⟨_, h2, fun a ha => ?_⟩⟩
      · rw [get?_restrict, if_pos ha]; exact hm a (mem_joinAttrs.mpr (Or.inl ha))
      · rw [get?_restrict, if_pos ha]; exact hm a (mem_joinAttrs.mpr (Or.inr ha))
  · intro t ht p hp
    obtain ⟨ft, h1, h2⟩ := (rq'.mem t).mp ht
    have hpa : p.1 ∈ joinAttrs as bs := by
      rw [← attrs_headerOf D (joinAttrs as bs), ← ft.attrs]
      exact List.mem_map_of_mem hp
    rcases mem_joinAttrs.mp hpa with h | h
    · exact i1.vals _ h1 p (mem_restrict.mpr ⟨hp, h⟩)
    · exact i2.vals _ h2 p (mem_restrict.mpr ⟨hp, h⟩)

/-! ### ρ -/

theorem nodup_of_map_fst {β : Type} {l : List (String × β)} (h : (l.map (·.1)).Nodup) : l.Nodup :=
  List.Pairwise.of_map (·.1) (fun _ _ hab e => hab (congrArg (·.1) e)) h

theorem lookup_allD {D : Domain} : ∀ {h : Heading}, (∀ p ∈ h, p.2 = D) →
    ∀ a, h.lookup a = if a ∈ h.map (·.1) then some D else none
  | [], _, a => rfl
  | (b, d) :: h, hd, a => by
    have hd' : d = D := hd (b, d) List.mem_cons_self
    subst hd'
    simp only [List.lookup_cons, List.map_cons, List.mem_cons]
    by_cases e : a = b
    · subst e; simp
    · have : (a == b) = false := by simp [e]
      rw [this, lookup_allD (fun p hp => hd p (List.mem_cons_of_mem _ hp)) a]
      by_cases h2 : a ∈ h.map (·.1) <;> simp [e, h2]

theorem allD_of_headIs {D : Domain} {as : List String} {h : Heading} (hn : (h.map (·.1)).Nodup)
    (hh : HeadIs D as h) : ∀ p ∈ h, p.2 = D := by
  intro p hp
  have := hh p.1
  rw [mem_lookup hn hp, lookup_headerOf] at this
  split at this <;> simp_all

theorem mem_attrs_of_headIs {D : Domain} {as : List String} {h : Heading} (hh : HeadIs D as h)
    (a : String) : a ∈ h.map (·.1) ↔ a ∈ as := by
  rw [← Finrel.lookup_isSome, hh a, lookup_headerOf]
  split <;> simp_all

theorem lookup_map_key {f : String → String} {a : String} :
    ∀ {l : List (String × Value)}, (∀ p ∈ l, f p.1 = f a → p.1 = a) →
      (l.map fun p => (f p.1, p.2)).lookup (f a) = l.lookup a
  | [], _ => rfl
  | (b, v) :: l, h => by
    simp only [List.map_cons, List.lookup_cons]
    by_cases e : a = b
    · subst e; simp
    · have h1 : (f a == f b) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun e' => e (h (b, v) List.mem_cons_self e'.symm).symm
      have h2 : (a == b) = false := by simp [e]
      rw [h1, h2]
      exact lookup_map_key fun p hp => h p (List.mem_cons_of_mem _ hp)

theorem get?_renameTuple {D : Domain} {as : List String} {r : List (String × String)} {u : Tuple}
    (fu : u.Fits (headerOf D as))
    (hinj : ∀ a ∈ as, ∀ b ∈ as, Finrel.renameAttr r a = Finrel.renameAttr r b → a = b)
    {a : String} (ha : a ∈ as) :
    (Finrel.renameTuple r u).get? (Finrel.renameAttr r a) = u.get? a := by
  have hkeys : ∀ p ∈ u, p.1 ∈ as := fun p hp => by
    rw [← attrs_headerOf D as, ← fu.attrs]; exact List.mem_map_of_mem hp
  have hn : ((u.map fun p => (Finrel.renameAttr r p.1, p.2)).map (·.1)).Nodup := by
    rw [List.map_map]
    exact nodup_map_of_inj (nodup_of_map_fst (Tuple.nodup_keys fu.sorted))
      (fun x hx y hy e => by
        have := hinj x.1 (hkeys x hx) y.1 (hkeys y hy) e
        exact inj_of_nodup_map (Tuple.nodup_keys fu.sorted) x hx y hy this)
  rw [Finrel.renameTuple, Tuple.get?_ofPairs hn]
  exact lookup_map_key fun p hp e => hinj p.1 (hkeys p hp) a ha e

theorem inv_rename {dom : Value → Prop} {S : Schema} {D : Domain} {env : Env} {as : List String}
    {μ : String → String} {φ : Formula} {r : Finrel} {ren : List (String × String)}
    (i1 : Inv dom S D env as (fun a => μ (Finrel.renameAttr ren a)) φ r)
    (hsrc : ∀ p ∈ ren, p.1 ∈ as) (_hn : as.Nodup) (hn' : (CRA.renamed ren as).Nodup) :
    ∃ q, r.rename ren = .ok q ∧ Inv dom S D env (CRA.renamed ren as) μ φ q := by
  have hren : CRA.renamed ren as = as.map (Finrel.renameAttr ren) := rfl
  have hinj : ∀ a ∈ as, ∀ b ∈ as, Finrel.renameAttr ren a = Finrel.renameAttr ren b → a = b := by
    rw [hren] at hn'; exact inj_of_nodup_map hn'
  have hattr := mem_attrs_of_headIs i1.head
  obtain ⟨q, hq⟩ := Finrel.rename_ok.mpr ⟨fun p hp => (hattr p.1).mpr (hsrc p hp), by
    simp only [Finrel.renameHeading, Heading.attrs, List.map_map]
    exact nodup_map_of_inj (nodup_of_map_fst i1.wf.nodup) fun x hx y hy e => by
      have hx' := (hattr x.1).mp (List.mem_map_of_mem hx)
      have hy' := (hattr y.1).mp (List.mem_map_of_mem hy)
      exact inj_of_nodup_map i1.wf.nodup x hx y hy (hinj _ hx' _ hy' e)⟩
  have hall := allD_of_headIs i1.wf.nodup i1.head
  have hhead : HeadIs D (CRA.renamed ren as) q.heading := by
    intro b
    rw [Finrel.rename_heading hq, lookup_allD (fun p hp => by
      simp only [Finrel.renameHeading, List.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp; exact hall x hx), lookup_headerOf]
    have : b ∈ (Finrel.renameHeading ren r.heading).map (·.1) ↔ b ∈ CRA.renamed ren as := by
      simp only [Finrel.renameHeading, List.map_map, hren, List.mem_map, Function.comp_def]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x.1, (hattr x.1).mp (List.mem_map_of_mem hx), rfl⟩
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨x, hx, e⟩ := List.mem_map.mp ((hattr a).mpr ha)
        exact ⟨x, hx, by rw [e]⟩
    by_cases hb : b ∈ CRA.renamed ren as
    · rw [if_pos (this.mpr hb), if_pos hb]
    · rw [if_neg (fun h => hb (this.mp h)), if_neg hb]
  refine ⟨q, hq, Finrel.rename_wf hq i1.wf, hhead, fun ρ => ?_, ?_⟩
  · rw [i1.sat]
    constructor
    · rintro ⟨u, hu, hm⟩
      refine ⟨_, (Finrel.mem_rename hq _).mpr ⟨u, hu, rfl⟩, fun b hb => ?_⟩
      rw [hren] at hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      rw [get?_renameTuple (i1.fits hu) hinj ha]; exact hm a ha
    · rintro ⟨t, ht, hm⟩
      obtain ⟨u, hu, rfl⟩ := (Finrel.mem_rename hq _).mp ht
      refine ⟨u, hu, fun a ha => ?_⟩
      rw [← get?_renameTuple (i1.fits hu) hinj ha]
      exact hm _ (by rw [hren]; exact List.mem_map_of_mem ha)
  · intro t ht p hp
    obtain ⟨u, hu, rfl⟩ := (Finrel.mem_rename hq _).mp ht
    rw [Finrel.renameTuple, mem_ofPairs] at hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact i1.vals u hu x hx

/-! ## Constant relations -/

theorem evalHeading_headerOf (env : Env) (D : Domain) :
    ∀ (bs : List String), evalHeading env [] (bs.map (·, toDomExpr D)) = .ok (headerOf D bs)
  | [] => by rw [evalHeading.eq_def]; rfl
  | b :: bs => by
    have ih := evalHeading_headerOf env D bs
    rw [List.map_cons, evalHeading.eq_def]
    simp [ih, dom_eval_toDomExpr, headerOf, bind, Except.bind, pure, Except.pure]

/-- The rows of a constant relation, as tuples. -/
def litTuples (bs : List String) (rows : List (List Value)) : List Tuple :=
  rows.map fun row => Tuple.ofPairs (bs.zip row)

theorem eval_lit {env : Env} {D : Domain} {bs : List String} {rows : List (List Value)}
    (hrows : ∀ row ∈ rows, row.length = bs.length ∧ ∀ v ∈ row, D.mem v = true) :
    Expr.eval env [] (.omegaRows (bs.map (·, toDomExpr D)) rows) =
      .ok (.finrel (Finrel.ofTuples (headerOf D bs) (litTuples bs rows))) := by
  rw [Expr.eval]
  simp only [evalHeading_headerOf, bind, Except.bind]
  have hlen : (headerOf D bs).length = bs.length := by simp [headerOf]
  rw [Rasso.ESO.mapM_eq_map (fun row => Tuple.ofPairs (bs.zip row))]
  · rfl
  intro row hrow
  obtain ⟨hl₀, hu⟩ := hrows row hrow
  have hl : (row.length != List.length (headerOf D bs)) = false := by simp [hlen, hl₀]
  rw [if_neg (by rw [hl]; exact Bool.false_ne_true)]
  rw [Rasso.ESO.forIn_ok_of_all]
  · simp [attrs_headerOf, pure, Except.pure]
  intro x hx
  obtain ⟨⟨c, d⟩, v⟩ := x
  have hd : d = D := by
    have h1 := (List.of_mem_zip hx).1
    simp only [headerOf, List.mem_map] at h1
    obtain ⟨_, _, e⟩ := h1
    cases e; rfl
  have hm : d.mem v = true := by rw [hd]; exact hu v (List.of_mem_zip hx).2
  simp [hm, pure, Except.pure]

theorem keys_zip' {bs : List String} {row : List Value} (hl : row.length = bs.length) :
    (bs.zip row).map (·.1) = bs := List.map_fst_zip (by omega)

theorem fits_litTuple {D : Domain} {bs : List String} (hn : bs.Nodup) {row : List Value}
    (hl : row.length = bs.length) (hu : ∀ v ∈ row, D.mem v = true) :
    (Tuple.ofPairs (bs.zip row)).Fits (headerOf D bs) := by
  have hk := keys_zip' hl
  refine ⟨ofPairs_sorted (by rw [hk]; exact hn), fun a => ?_, fun p hp d hd => ?_⟩
  · rw [attrs_ofPairs, hk, attrs_headerOf]
  · have hp' := mem_ofPairs.mp hp
    have h1 := (List.of_mem_zip hp').1
    rw [lookup_headerOf, if_pos h1] at hd
    cases hd; exact hu _ (List.of_mem_zip hp').2

theorem match_litTuple {bs : List String} (hn : bs.Nodup) {row : List Value}
    (hl : row.length = bs.length) (μ : String → String) (ρ : String → Value) :
    Match bs μ ρ (Tuple.ofPairs (bs.zip row)) ↔ ∀ p ∈ bs.zip row, ρ (μ p.1) = p.2 := by
  have hk := keys_zip' hl
  have hn' : ((bs.zip row).map (·.1)).Nodup := by rw [hk]; exact hn
  simp only [Match, Tuple.get?_ofPairs hn']
  constructor
  · intro h p hp
    have h1 := (List.of_mem_zip hp).1
    have := h p.1 h1
    rw [lookup_of_mem hn' hp] at this
    exact (Option.some.inj this).symm
  · intro h a ha
    have : a ∈ (bs.zip row).map (·.1) := by rw [hk]; exact ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp this
    rw [lookup_of_mem hn' hp, h p hp]

theorem inv_lit {dom : Value → Prop} {S : Schema} {D : Domain} {env : Env} {bs : List String}
    {rows : List (List Value)} {μ : String → String} {k : Nat} (hn : bs.Nodup)
    (hrows : ∀ row ∈ rows, row.length = bs.length ∧ ∀ v ∈ row, D.mem v = true)
    (hc : ∀ c ∈ (CRA.lit bs rows).consts, dom c) :
    Inv dom S D env bs μ (tr S D (.lit bs rows) μ k)
      (Finrel.ofTuples (headerOf D bs) (litTuples bs rows)) := by
  refine ⟨Finrel.wf_ofTuples (by rw [attrs_headerOf]; exact hn) ?_, fun a => rfl, fun ρ => ?_, ?_⟩
  · intro t ht
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp ht
    exact fits_litTuple hn (hrows row hrow).1 (hrows row hrow).2
  · simp only [tr, sat_disjF, List.mem_map, Finrel.mem_ofTuples, litTuples]
    constructor
    · rintro ⟨_, ⟨row, hrow, rfl⟩, hs⟩
      refine ⟨_, ⟨row, hrow, rfl⟩, (match_litTuple hn (hrows row hrow).1 μ ρ).mpr ?_⟩
      intro p hp
      have := (sat_conjF ρ _).mp hs (.eqc (μ p.1) p.2) (List.mem_map_of_mem hp)
      simpa [Sat] using this
    · rintro ⟨_, ⟨row, hrow, rfl⟩, hm⟩
      refine ⟨_, ⟨row, hrow, rfl⟩, (sat_conjF ρ _).mpr ?_⟩
      intro φ hφ
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hφ
      simpa [Sat] using (match_litTuple hn (hrows row hrow).1 μ ρ).mp hm p hp
  · intro t ht p hp
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp (Finrel.mem_ofTuples.mp ht)
    exact hc _ (by
      simp only [CRA.consts, List.mem_flatten]
      exact ⟨row, hrow, (List.of_mem_zip (mem_ofPairs.mp hp)).2⟩)

/-! ## Projection -/

theorem mem_dropped {as bs : List String} {a : String} : a ∈ dropped as bs ↔ a ∈ as ∧ a ∉ bs := by
  simp [dropped, List.contains_iff_mem]

/-- An assignment that gives each fresh name `fresh k d` of `ds` the value `g d`, and
agrees with `ρ` elsewhere. -/
theorem exists_fresh_asg {ds : List String} (hd : ∀ d ∈ ds, isAttribute d = true) (k : Nat)
    (g : String → Value) (ρ : String → Value) :
    ∃ ρ' : String → Value, (∀ d ∈ ds, ρ' (fresh k d) = g d) ∧
      (∀ y, y ∉ ds.map (fresh k) → ρ' y = ρ y) := by
  refine ⟨fun y => match ds.find? (fun d => fresh k d == y) with
    | some d => g d
    | none => ρ y, fun d hd' => ?_, fun y hy => ?_⟩
  · cases hf : ds.find? (fun d' => fresh k d' == fresh k d) with
    | none =>
      exact absurd (List.find?_eq_none.mp hf d hd') (by simp)
    | some d' =>
      simp only [hf]
      have h1 := List.find?_some hf
      have h2 := List.mem_of_find?_eq_some hf
      simp only [beq_iff_eq] at h1
      rw [(fresh_inj (hd d' h2) (hd d hd') h1).2]
  · cases hf : ds.find? (fun d' => fresh k d' == y) with
    | none => simp only [hf]
    | some d' =>
      have h1 := List.find?_some hf
      have h2 := List.mem_of_find?_eq_some hf
      simp only [beq_iff_eq] at h1
      exact absurd (h1 ▸ List.mem_map_of_mem h2) hy

theorem inv_proj {dom : Value → Prop} {S : Schema} {D : Domain} {env : Env}
    {as bs : List String} {μ : String → String} {k : Nat} {φ : Formula} {r : Finrel}
    (hattr : ∀ a ∈ as, isAttribute a = true) (hn : bs.Nodup) (hsub : ∀ b ∈ bs, b ∈ as)
    (hf : FreshFrom μ bs k)
    (i1 : Inv dom S D env as (projMap (dropped as bs) μ k) φ r) :
    ∃ s, r.project bs = .ok s ∧
      Inv dom S D env bs μ (exs ((dropped as bs).map (fresh k)) φ) s := by
  obtain ⟨s, hs, rs⟩ := rep_project i1.rep (fun a ha => by rw [attrs_headerOf]; exact hsub a ha) hn
  have hmem := Finrel.mem_project hs
  -- the variable of a kept attribute is not one of the bound fresh names
  have hkeep : ∀ a ∈ bs, μ a ∉ (dropped as bs).map (fresh k) := by
    intro a ha hm
    obtain ⟨d, hd, e⟩ := List.mem_map.mp hm
    exact hf a ha k d (Nat.le_refl k) (hattr d (mem_dropped.mp hd).1) e.symm
  have hμ : ∀ a ∈ bs, projMap (dropped as bs) μ k a = μ a := fun a ha => by
    simp only [projMap]; rw [if_neg (fun h => (mem_dropped.mp h).2 ha)]
  refine ⟨s, hs, rs.wf, fun a => ?_, fun ρ => ?_, ?_⟩
  · rw [rs.head a, lookup_restrictH, lookup_headerOf, lookup_headerOf]
    by_cases ha : a ∈ bs
    · rw [if_pos ha, if_pos (hsub a ha), if_pos ha]
    · rw [if_neg ha, if_neg ha]
  · rw [sat_exs]
    constructor
    · rintro ⟨ρ', -, hout, hφ⟩
      obtain ⟨u, hu, hm⟩ := (i1.sat ρ').mp hφ
      refine ⟨u.restrict bs, (hmem _).mpr ⟨u, hu, rfl⟩, fun a ha => ?_⟩
      rw [get?_restrict, if_pos ha, hm a (hsub a ha), hμ a ha, hout _ (hkeep a ha)]
    · rintro ⟨t, ht, hm⟩
      obtain ⟨u, hu, rfl⟩ := (hmem t).mp ht
      have fu := i1.fits hu
      obtain ⟨ρ', h1, h2⟩ := exists_fresh_asg (fun d hd => hattr d (mem_dropped.mp hd).1) k
        (readAsg u) ρ
      refine ⟨ρ', fun x hx => ?_, h2, (i1.sat ρ').mpr ⟨u, hu, fun a ha => ?_⟩⟩
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
        obtain ⟨v, hv, -, hp⟩ := get?_fits fu (mem_dropped.mp hd).1
        rw [h1 d hd]; simp only [readAsg, hv, Option.getD_some]
        exact i1.vals u hu _ hp
      · by_cases hb : a ∈ bs
        · rw [hμ a hb, h2 _ (hkeep a hb), ← hm a hb, get?_restrict, if_pos hb]
        · have hd : a ∈ dropped as bs := mem_dropped.mpr ⟨ha, hb⟩
          obtain ⟨v, hv, -⟩ := get?_fits fu ha
          simp only [projMap, if_pos hd]
          rw [h1 a hd]; simp [readAsg, hv]
  · intro t ht p hp
    obtain ⟨u, hu, rfl⟩ := (hmem t).mp ht
    exact i1.vals u hu p (mem_restrict.mp hp).1

/-! ## Free variables, constants and arities of the translation -/

theorem fv_tt : tt.fv = [] := by decide
theorem consts_tt : tt.consts = [] := rfl

theorem fv_conjF : (φs : List Formula) → (conjF φs).fv = φs.flatMap Formula.fv
  | [] => fv_tt
  | φ :: φs => by simp [conjF, Formula.fv, fv_conjF φs]

theorem fv_disjF : (φs : List Formula) → (disjF φs).fv = φs.flatMap Formula.fv
  | [] => by simp [disjF, ff, Formula.fv, fv_tt]
  | φ :: φs => by simp [disjF, Formula.fv, fv_disjF φs]

theorem consts_conjF : (φs : List Formula) → (conjF φs).consts = φs.flatMap Formula.consts
  | [] => consts_tt
  | φ :: φs => by simp [conjF, Formula.consts, consts_conjF φs]

theorem consts_disjF : (φs : List Formula) → (disjF φs).consts = φs.flatMap Formula.consts
  | [] => by simp [disjF, ff, Formula.consts, consts_tt]
  | φ :: φs => by simp [disjF, Formula.consts, consts_disjF φs]

theorem wt_conjF {S : Schema} : (φs : List Formula) → (∀ φ ∈ φs, φ.WT S = true) →
    (conjF φs).WT S = true
  | [], _ => rfl
  | φ :: φs, h => by
    simp only [conjF, Formula.WT, Bool.and_eq_true]
    exact ⟨h φ List.mem_cons_self, wt_conjF φs fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)⟩

theorem wt_disjF {S : Schema} : (φs : List Formula) → (∀ φ ∈ φs, φ.WT S = true) →
    (disjF φs).WT S = true
  | [], _ => rfl
  | φ :: φs, h => by
    simp only [disjF, Formula.WT, Bool.and_eq_true]
    exact ⟨h φ List.mem_cons_self, wt_disjF φs fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)⟩

theorem fv_exs {x : String} {φ : Formula} : (xs : List String) → x ∈ (exs xs φ).fv →
    x ∈ φ.fv ∧ x ∉ xs
  | [], h => ⟨h, by simp⟩
  | y :: ys, h => by
    simp only [exs, List.foldr_cons, Formula.fv, List.mem_filter, bne_iff_ne, ne_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h3, h4⟩ := fv_exs ys h1
    exact ⟨h3, by simp [h2, h4]⟩

theorem consts_exs {φ : Formula} : (xs : List String) → (exs xs φ).consts = φ.consts
  | [] => rfl
  | _ :: ys => by simp only [exs, List.foldr_cons, Formula.consts]; exact consts_exs ys

theorem wt_exs {S : Schema} {φ : Formula} : (xs : List String) → (exs xs φ).WT S = φ.WT S
  | [] => rfl
  | _ :: ys => by simp only [exs, List.foldr_cons, Formula.WT]; exact wt_exs ys

theorem Test.fv_toFormula (μ : String → String) : (t : Test) → (t.toFormula μ).fv = t.attrs.map μ
  | .eqA _ _ | .eqC _ _ | .cmpA _ _ _ | .cmpC _ _ _ => rfl
  | .and s t | .or s t => by simp [Test.toFormula, Formula.fv, Test.attrs, Test.fv_toFormula μ s, Test.fv_toFormula μ t]
  | .not t => by simp [Test.toFormula, Formula.fv, Test.attrs, Test.fv_toFormula μ t]

theorem Test.consts_toFormula (μ : String → String) : (t : Test) → (t.toFormula μ).consts = t.consts
  | .eqA _ _ | .eqC _ _ | .cmpA _ _ _ | .cmpC _ _ _ => rfl
  | .and s t | .or s t => by simp [Test.toFormula, Formula.consts, Test.consts, Test.consts_toFormula μ s, Test.consts_toFormula μ t]
  | .not t => by simp [Test.toFormula, Formula.consts, Test.consts, Test.consts_toFormula μ t]

theorem Test.wt_toFormula {S : Schema} (μ : String → String) : (t : Test) → (t.toFormula μ).WT S = true
  | .eqA _ _ | .eqC _ _ | .cmpA _ _ _ | .cmpC _ _ _ => rfl
  | .and s t | .or s t => by simp [Test.toFormula, Formula.WT, Test.wt_toFormula μ s, Test.wt_toFormula μ t]
  | .not t => by simp [Test.toFormula, Formula.WT, Test.wt_toFormula μ t]

/-- The members of a binary operator's attribute list are those of its operands. -/
theorem check_bin {S : Schema} {D : Domain} {e f g : CRA} {as : List String}
    (hg : g = .join e f ∨ g = .prod e f ∨ g = .union e f ∨ g = .diff e f ∨ g = .inter e f)
    (he : g.check S D = some as) :
    ∃ as' bs', e.check S D = some as' ∧ f.check S D = some bs' ∧
      ∀ a, a ∈ as ↔ a ∈ as' ∨ a ∈ bs' := by
  have same : ∀ {as' bs' : List String}, (as'.all bs'.contains = true ∧ bs'.all as'.contains = true) →
      ∀ a, a ∈ as' ↔ a ∈ as' ∨ a ∈ bs' := fun hs a => by
    have := sameSet_of_all hs.1 hs.2 a
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · exact this.mpr h
  rcases hg with rfl | rfl | rfl | rfl | rfl <;>
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at he <;>
    obtain ⟨as', he1, bs', he2, he⟩ := he
  · cases he; exact ⟨as', bs', he1, he2, fun a => by rw [← joinAttrs, mem_joinAttrs]⟩
  all_goals
    split at he
    · rename_i hs; cases he
      first
        | exact ⟨_, bs', he1, he2, same hs⟩
        | exact ⟨as', bs', he1, he2, fun a => by simp⟩
    · cases he

/-- The five facts, for a binary operator, from its operands'. -/
theorem facts_bin {S : Schema} {D : Domain} {as as' bs' : List String} {μ : String → String}
    {φ ψ Φ : Formula} {ce cf cg : List Value}
    (hm : ∀ a, a ∈ as ↔ a ∈ as' ∨ a ∈ bs')
    (hfv : Φ.fv = φ.fv ++ ψ.fv) (hc : Φ.consts = φ.consts ++ ψ.consts)
    (hwt : Φ.WT S = (φ.WT S && ψ.WT S)) (hcg : cg = ce ++ cf)
    (i : (∀ x ∈ φ.fv, x ∈ as'.map μ) ∧ (∀ c ∈ ce, c ∈ φ.consts) ∧ (∀ c ∈ φ.consts, c ∈ ce) ∧
      (∀ c ∈ ce, D.mem c = true) ∧ φ.WT S = true)
    (j : (∀ x ∈ ψ.fv, x ∈ bs'.map μ) ∧ (∀ c ∈ cf, c ∈ ψ.consts) ∧ (∀ c ∈ ψ.consts, c ∈ cf) ∧
      (∀ c ∈ cf, D.mem c = true) ∧ ψ.WT S = true) :
    (∀ x ∈ Φ.fv, x ∈ as.map μ) ∧ (∀ c ∈ cg, c ∈ Φ.consts) ∧ (∀ c ∈ Φ.consts, c ∈ cg) ∧
      (∀ c ∈ cg, D.mem c = true) ∧ Φ.WT S = true := by
  subst hcg
  obtain ⟨i1, i2, i3, i4, i5⟩ := i
  obtain ⟨j1, j2, j3, j4, j5⟩ := j
  rw [hfv, hc, hwt]
  refine ⟨fun x hx => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, by simp [i5, j5]⟩
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (i1 x hx)
      exact List.mem_map_of_mem ((hm a).mpr (Or.inl ha))
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (j1 x hx)
      exact List.mem_map_of_mem ((hm a).mpr (Or.inr ha))
  · rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ (i2 c hc)
    · exact List.mem_append_right _ (j2 c hc)
  · rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ (i3 c hc)
    · exact List.mem_append_right _ (j3 c hc)
  · rcases List.mem_append.mp hc with hc | hc
    · exact i4 c hc
    · exact j4 c hc

section Facts
variable {S : Schema} {D : Domain}

theorem tr_facts (hS : S.WF) : (e : CRA) → {as : List String} → {μ : String → String} → {k : Nat} →
    e.check S D = some as →
      (∀ x ∈ (tr S D e μ k).fv, x ∈ as.map μ) ∧
      (∀ c ∈ e.consts, c ∈ (tr S D e μ k).consts) ∧
      (∀ c ∈ (tr S D e μ k).consts, c ∈ e.consts) ∧
      (∀ c ∈ e.consts, D.mem c = true) ∧
      (tr S D e μ k).WT S = true
  | .rel n, as, μ, k, he => by
    simp only [CRA.check] at he
    refine ⟨fun x hx => ?_, by simp [CRA.consts], by simp [tr, Formula.consts], by simp [CRA.consts], ?_⟩
    · simpa [tr, Formula.fv, Schema.attrsOf, he] using hx
    · simp [tr, Formula.WT, he]
  | .lit bs rows, as, μ, k, he => by
    simp only [CRA.check] at he
    split at he
    · rename_i hs
      cases he
      have hl : ∀ row ∈ rows, row.length = bs.length := fun row hrow => by
        simpa using List.all_eq_true.mp hs.2.2.1 row hrow
      refine ⟨fun x hx => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, ?_⟩
      · simp only [tr, fv_disjF, fv_conjF, List.mem_flatMap, List.mem_map] at hx
        obtain ⟨_, ⟨row, -, rfl⟩, hx⟩ := hx
        simp only [fv_conjF, List.mem_flatMap, List.mem_map] at hx
        obtain ⟨_, ⟨p, hp, rfl⟩, hx⟩ := hx
        simp only [Formula.fv, List.mem_singleton] at hx
        subst hx
        exact List.mem_map_of_mem (List.of_mem_zip hp).1
      · simp only [CRA.consts, List.mem_flatten] at hc
        obtain ⟨row, hrow, hc⟩ := hc
        have : c ∈ (bs.zip row).map (·.2) := by
          rw [List.map_snd_zip (by rw [hl row hrow]; exact Nat.le_refl _)]; exact hc
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp this
        simp only [tr, consts_disjF, List.mem_flatMap, List.mem_map]
        refine ⟨_, ⟨row, hrow, rfl⟩, ?_⟩
        simp only [consts_conjF, List.mem_flatMap, List.mem_map]
        exact ⟨_, ⟨p, hp, rfl⟩, by simp [Formula.consts]⟩
      · simp only [tr, consts_disjF, consts_conjF, List.mem_flatMap, List.mem_map] at hc
        obtain ⟨_, ⟨row, hrow, rfl⟩, hc⟩ := hc
        simp only [consts_conjF, List.mem_flatMap, List.mem_map] at hc
        obtain ⟨_, ⟨p, hp, rfl⟩, hc⟩ := hc
        simp only [Formula.consts, List.mem_singleton] at hc
        subst hc
        simp only [CRA.consts, List.mem_flatten]
        exact ⟨row, hrow, (List.of_mem_zip hp).2⟩
      · simp only [CRA.consts, List.mem_flatten] at hc
        obtain ⟨row, hrow, hc⟩ := hc
        exact List.all_eq_true.mp (List.all_eq_true.mp hs.2.2.2 row hrow) c hc
      · simp only [tr]
        apply wt_disjF
        intro φ hφ
        obtain ⟨row, -, rfl⟩ := List.mem_map.mp hφ
        apply wt_conjF
        intro ψ hψ
        obtain ⟨p, -, rfl⟩ := List.mem_map.mp hψ
        rfl
    · cases he
  | .sel t e, as, μ, k, he => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at he
    obtain ⟨as', he1, he⟩ := he
    split at he
    · rename_i hs
      cases he
      obtain ⟨i1, i2, i3, i4, i5⟩ := tr_facts hS e (μ := μ) (k := k) he1
      refine ⟨fun x hx => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, ?_⟩
      · simp only [tr, Formula.fv, List.mem_append, Test.fv_toFormula] at hx
        rcases hx with hx | hx
        · exact i1 x hx
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
          exact List.mem_map_of_mem (List.contains_iff_mem.mp (List.all_eq_true.mp hs.1 a ha))
      · simp only [CRA.consts, List.mem_append] at hc
        simp only [tr, Formula.consts, List.mem_append, Test.consts_toFormula]
        rcases hc with hc | hc
        · exact Or.inr hc
        · exact Or.inl (i2 c hc)
      · simp only [tr, Formula.consts, List.mem_append, Test.consts_toFormula] at hc
        simp only [CRA.consts, List.mem_append]
        rcases hc with hc | hc
        · exact Or.inr (i3 c hc)
        · exact Or.inl hc
      · simp only [CRA.consts, List.mem_append] at hc
        rcases hc with hc | hc
        · exact List.all_eq_true.mp hs.2 c hc
        · exact i4 c hc
      · simp [tr, Formula.WT, i5, Test.wt_toFormula]
    · cases he
  | .proj bs e, as, μ, k, he => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at he
    obtain ⟨as', he1, he⟩ := he
    split at he
    · rename_i hs
      cases he
      obtain ⟨i1, i2, i3, i4, i5⟩ :=
        tr_facts hS e (μ := projMap (dropped as' bs) μ k) (k := k + 1) he1
      simp only [tr, he1, Option.getD_some, consts_exs, wt_exs, CRA.consts]
      refine ⟨fun x hx => ?_, i2, i3, i4, i5⟩
      obtain ⟨hx1, hx2⟩ := fv_exs _ hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (i1 x hx1)
      by_cases hd : a ∈ dropped as' bs
      · exact absurd (by simp only [projMap, if_pos hd]; exact List.mem_map_of_mem hd) hx2
      · have hb : a ∈ bs := Classical.byContradiction fun hb => hd (mem_dropped.mpr ⟨ha, hb⟩)
        simp only [projMap, if_neg hd]
        exact List.mem_map_of_mem hb
    · cases he
  | .ren r e, as, μ, k, he => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at he
    obtain ⟨as', he1, he⟩ := he
    split at he
    · cases he
      obtain ⟨i1, i2, i3, i4, i5⟩ :=
        tr_facts hS e (μ := fun a => μ (Finrel.renameAttr r a)) (k := k) he1
      refine ⟨fun x hx => ?_, i2, i3, i4, i5⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (i1 x hx)
      exact List.mem_map_of_mem (List.mem_map_of_mem ha)
    · cases he
  | .join e f, as, μ, k, he => by
    obtain ⟨as', bs', he1, he2, hm⟩ := check_bin (Or.inl rfl) he
    exact facts_bin hm rfl rfl rfl rfl (tr_facts hS e he1) (tr_facts hS f he2)
  | .prod e f, as, μ, k, he => by
    obtain ⟨as', bs', he1, he2, hm⟩ := check_bin (Or.inr (Or.inl rfl)) he
    exact facts_bin hm rfl rfl rfl rfl (tr_facts hS e he1) (tr_facts hS f he2)
  | .union e f, as, μ, k, he => by
    obtain ⟨as', bs', he1, he2, hm⟩ := check_bin (Or.inr (Or.inr (Or.inl rfl))) he
    exact facts_bin hm rfl rfl rfl rfl (tr_facts hS e he1) (tr_facts hS f he2)
  | .diff e f, as, μ, k, he => by
    obtain ⟨as', bs', he1, he2, hm⟩ := check_bin (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) he
    exact facts_bin hm rfl rfl rfl rfl (tr_facts hS e he1) (tr_facts hS f he2)
  | .inter e f, as, μ, k, he => by
    obtain ⟨as', bs', he1, he2, hm⟩ := check_bin (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) he
    exact facts_bin hm rfl rfl rfl rfl (tr_facts hS e he1) (tr_facts hS f he2)

end Facts

section Induction
variable {S : Schema} {D : Domain} {env : Env} {dom : Value → Prop}
  (hS : S.WF) (hD : DomOK D = true) (henv : Conforms S D env) (hdom : ∀ v ∈ adom S env, dom v)
include hS hD henv hdom

theorem tr_spec : (e : CRA) → {as : List String} → {μ : String → String} → {k : Nat} →
    e.check S D = some as → (∀ c ∈ e.consts, dom c) → InjOn μ as → FreshFrom μ as k →
    ∃ r, Expr.eval env [] (e.toExpr D) = .ok (.finrel r) ∧ Inv dom S D env as μ (tr S D e μ k) r
  | .rel n, as, μ, k, he, _, _, _ => by
    simp only [CRA.check] at he
    have hm := lookup_schema he
    obtain ⟨r, hr, hw, hh⟩ := henv _ hm
    refine ⟨r, by simp only [CRA.toExpr]; exact eval_name hr, hw, hh, fun ρ => ?_, ?_⟩
    · simp only [tr, Sat, AtomHolds, Schema.attrsOf, he, Option.getD_some, zip_map_self,
        tuplesOf_eq hr, List.mem_map, forall_exists_index, and_imp, Match]
      constructor
      · rintro ⟨t, ht, h⟩; exact ⟨t, ht, fun a ha => h _ a ha rfl⟩
      · rintro ⟨t, ht, h⟩; exact ⟨t, ht, fun p a ha e => e ▸ h a ha⟩
    · intro t ht p hp
      exact hdom _ (mem_adom hm (by rw [tuplesOf_eq hr]; exact ht) hp)
  | .lit bs rows, as, μ, k, he, hc, hi, hf => by
    simp only [CRA.check] at he
    split at he
    · rename_i hs
      cases he
      have hrows : ∀ row ∈ rows, row.length = bs.length ∧ ∀ v ∈ row, D.mem v = true :=
        fun row hrow => ⟨by simpa using List.all_eq_true.mp hs.2.2.1 row hrow,
          fun v hv => List.all_eq_true.mp (List.all_eq_true.mp hs.2.2.2 row hrow) v hv⟩
      exact ⟨_, by simp only [CRA.toExpr]; exact eval_lit hrows, inv_lit hs.1 hrows hc⟩
    · cases he
  | .sel t e, as, μ, k, he, hc, hi, hf => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at he
    obtain ⟨as', he1, he⟩ := he
    split at he
    · rename_i hs
      cases he
      have ha : ∀ a ∈ t.attrs, a ∈ as := fun a h =>
        List.contains_iff_mem.mp (List.all_eq_true.mp hs.1 a h)
      have hcD : ∀ c ∈ t.consts, D.mem c = true := fun c h => List.all_eq_true.mp hs.2 c h
      have hc1 : ∀ c ∈ e.consts, dom c := fun c h => hc c (by simp [CRA.consts, h])
      obtain ⟨r1, hr1, i1⟩ := tr_spec e he1 hc1 hi hf
      have hev : ∀ u ∈ r1.tuples, Term.holds u t.toTerm = .ok (t.evalOn u) := fun u hu =>
        Test.holds_toTerm hD (i1.fits hu) ha hcD
      obtain ⟨q, hq⟩ := Finrel.select_ok.mpr fun u hu => ⟨_, hev u hu⟩
      have rq := rep_select i1.rep hq
      have hsc : ∀ a ∈ t.toTerm.attrs, a ∈ r1.heading.attrs := fun a h =>
        (attrs_congr i1.head a).mpr (by rw [attrs_headerOf]; exact ha a (Test.attrs_toTerm t a h))
      refine ⟨q, by simp only [CRA.toExpr]; exact eval_select hr1 hq hsc, rq.wf, rq.head, fun ρ => ?_, ?_⟩
      · simp only [tr, Sat, i1.sat]
        constructor
        · rintro ⟨⟨u, hu, hm⟩, ht⟩
          refine ⟨u, (rq.mem u).mpr ⟨i1.fits hu, hu, ?_⟩, hm⟩
          rw [hev u hu, (Test.sat_toFormula hm t ha).mp ht]
        · rintro ⟨u, hu, hm⟩
          obtain ⟨-, hu1, hu2⟩ := (rq.mem u).mp hu
          rw [hev u hu1] at hu2
          exact ⟨⟨u, hu1, hm⟩, (Test.sat_toFormula hm t ha).mpr (Except.ok.inj hu2)⟩
      · intro u hu p hp
        exact i1.vals u ((rq.mem u).mp hu).2.1 p hp
    · cases he
  | .proj bs e, as, μ, k, he, hc, hi, hf => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at he
    obtain ⟨as', he1, he⟩ := he
    split at he
    · rename_i hs
      cases he
      have hattr := (check_attrs hS e he1).2
      have hsub : ∀ b ∈ bs, b ∈ as' := fun b hb =>
        List.contains_iff_mem.mp (List.all_eq_true.mp hs.2 b hb)
      have hkept : ∀ a ∈ as', a ∉ dropped as' bs → a ∈ bs := fun a ha hd =>
        Classical.byContradiction fun hb => hd (mem_dropped.mpr ⟨ha, hb⟩)
      have hi' : InjOn (projMap (dropped as' bs) μ k) as' := by
        intro a ha b hb h
        simp only [projMap] at h
        by_cases da : a ∈ dropped as' bs <;> by_cases db : b ∈ dropped as' bs <;>
          simp only [da, db, if_true, if_false] at h
        · exact (fresh_inj (hattr a ha) (hattr b hb) h).2
        · exact absurd h.symm (hf b (hkept b hb db) k a (Nat.le_refl k) (hattr a ha))
        · exact absurd h (hf a (hkept a ha da) k b (Nat.le_refl k) (hattr b hb))
        · exact hi a (hkept a ha da) b (hkept b hb db) h
      have hf' : FreshFrom (projMap (dropped as' bs) μ k) as' (k + 1) := by
        intro a ha j b hj hb h
        simp only [projMap] at h
        by_cases da : a ∈ dropped as' bs <;> simp only [da, if_true, if_false] at h
        · have := (fresh_inj (hattr a ha) hb h).1; omega
        · exact hf a (hkept a ha da) j b (by omega) hb h
      obtain ⟨r1, hr1, i1⟩ := tr_spec e he1 hc hi' hf'
      obtain ⟨q, hq, iq⟩ := inv_proj hattr hs.1 hsub hf i1
      refine ⟨q, by simp only [CRA.toExpr]; exact eval_project hr1 hq, ?_⟩
      simp only [tr, he1, Option.getD_some]
      exact iq
    · cases he
  | .ren r e, as, μ, k, he, hc, hi, hf => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at he
    obtain ⟨as', he1, he⟩ := he
    split at he
    · rename_i hs
      cases he
      have hn := (check_attrs hS e he1).1
      have hn' := hs.2.2.2
      have hsrc : ∀ p ∈ r, p.1 ∈ as' := fun p hp =>
        List.contains_iff_mem.mp (List.all_eq_true.mp hs.2.1 p.1 (List.mem_map_of_mem hp))
      have hmem : ∀ a ∈ as', Finrel.renameAttr r a ∈ CRA.renamed r as' := fun a ha =>
        List.mem_map_of_mem ha
      have hinj : ∀ a ∈ as', ∀ b ∈ as', Finrel.renameAttr r a = Finrel.renameAttr r b → a = b :=
        inj_of_nodup_map (g := Finrel.renameAttr r) hn'
      obtain ⟨r1, hr1, i1⟩ := tr_spec e he1 hc
        (μ := fun a => μ (Finrel.renameAttr r a))
        (fun a ha b hb h => hinj a ha b hb (hi _ (hmem a ha) _ (hmem b hb) h))
        (fun a ha => hf _ (hmem a ha))
      obtain ⟨q, hq, iq⟩ := inv_rename i1 hsrc hn hn'
      exact ⟨q, by simp only [CRA.toExpr]; exact eval_rename hr1 hq, iq⟩
    · cases he
  | .join e f, as, μ, k, he, hc, hi, hf => by
    have hn := (check_attrs hS _ he).1
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at he
    obtain ⟨as', he1, bs', he2, he⟩ := he
    cases he
    have hc1 : ∀ c ∈ e.consts, dom c := fun c h => hc c (by simp [CRA.consts, h])
    have hc2 : ∀ c ∈ f.consts, dom c := fun c h => hc c (by simp [CRA.consts, h])
    have sub1 : ∀ a ∈ as', a ∈ joinAttrs as' bs' := fun a h => mem_joinAttrs.mpr (Or.inl h)
    have sub2 : ∀ a ∈ bs', a ∈ joinAttrs as' bs' := fun a h => mem_joinAttrs.mpr (Or.inr h)
    obtain ⟨r1, hr1, i1⟩ := tr_spec e he1 hc1 (hi.mono sub1) (hf.mono sub1)
    obtain ⟨r2, hr2, i2⟩ := tr_spec f he2 hc2 (hi.mono sub2) (hf.mono sub2)
    obtain ⟨q, hq, iq⟩ := inv_join i1 i2 hn
    exact ⟨q, by simp only [CRA.toExpr]; exact eval_join2 hr1 hr2 hq, iq⟩
  | .prod e f, as, μ, k, he, hc, hi, hf => by
    have hn := (check_attrs hS _ he).1
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at he
    obtain ⟨as', he1, bs', he2, he⟩ := he
    split at he
    · rename_i hdis
      cases he
      have hset : ∀ a, a ∈ joinAttrs as' bs' ↔ a ∈ as' ++ bs' := fun a => by
        rw [mem_joinAttrs, List.mem_append]
      have hn' : (joinAttrs as' bs').Nodup := by
        have : joinAttrs as' bs' = as' ++ bs' := by
          unfold joinAttrs; congr 1
          apply List.filter_eq_self.mpr
          intro b hb; simpa using List.all_eq_true.mp hdis b hb
        rw [this]; exact hn
      have hc1 : ∀ c ∈ e.consts, dom c := fun c h => hc c (by simp [CRA.consts, h])
      have hc2 : ∀ c ∈ f.consts, dom c := fun c h => hc c (by simp [CRA.consts, h])
      have sub1 : ∀ a ∈ as', a ∈ as' ++ bs' := fun a h => List.mem_append_left _ h
      have sub2 : ∀ a ∈ bs', a ∈ as' ++ bs' := fun a h => List.mem_append_right _ h
      obtain ⟨r1, hr1, i1⟩ := tr_spec e he1 hc1 (hi.mono sub1) (hf.mono sub1)
      obtain ⟨r2, hr2, i2⟩ := tr_spec f he2 hc2 (hi.mono sub2) (hf.mono sub2)
      obtain ⟨q, hq, iq⟩ := inv_join i1 i2 hn'
      have hd : ∀ a ∈ r1.heading.attrs, a ∉ r2.heading.attrs := fun a h1 h2 => by
        rw [attrs_congr i1.head a, attrs_headerOf] at h1
        rw [attrs_congr i2.head a, attrs_headerOf] at h2
        simpa [h1] using List.all_eq_true.mp hdis a h2
      exact ⟨q, by simp only [CRA.toExpr]; exact eval_prod2 hr1 hr2 hq hd, iq.congr hset⟩
    · cases he
  | .union e f, as, μ, k, he, hc, hi, hf => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at he
    obtain ⟨as', he1, bs', he2, he⟩ := he
    split at he
    · rename_i hs
      cases he
      have hset := sameSet_of_all hs.1 hs.2
      have hc1 : ∀ c ∈ e.consts, dom c := fun c h => hc c (by simp [CRA.consts, h])
      have hc2 : ∀ c ∈ f.consts, dom c := fun c h => hc c (by simp [CRA.consts, h])
      obtain ⟨r1, hr1, i1⟩ := tr_spec e he1 hc1 hi hf
      obtain ⟨r2, hr2, i2'⟩ := tr_spec f he2 hc2 (hi.congr hset) (hf.congr hset)
      have i2 := i2'.congr (fun a => (hset a).symm)
      obtain ⟨q, hq, rq⟩ := rep_union i1.rep i2.rep
      refine ⟨q, by simp only [CRA.toExpr]; exact eval_union2 hr1 hr2 hq, rq.wf, rq.head, fun ρ => ?_, ?_⟩
      · simp only [tr, Sat, i1.sat, i2.sat]
        constructor
        · rintro (⟨t, ht, hm⟩ | ⟨t, ht, hm⟩)
          · exact ⟨t, (rq.mem t).mpr ⟨i1.fits ht, Or.inl ht⟩, hm⟩
          · exact ⟨t, (rq.mem t).mpr ⟨i2.fits ht, Or.inr ht⟩, hm⟩
        · rintro ⟨t, ht, hm⟩
          rcases ((rq.mem t).mp ht).2 with h | h
          · exact Or.inl ⟨t, h, hm⟩
          · exact Or.inr ⟨t, h, hm⟩
      · intro t ht p hp
        rcases ((rq.mem t).mp ht).2 with h | h
        · exact i1.vals t h p hp
        · exact i2.vals t h p hp
    · cases he
  | .diff e f, as, μ, k, he, hc, hi, hf => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at he
    obtain ⟨as', he1, bs', he2, he⟩ := he
    split at he
    · rename_i hs
      cases he
      have hset := sameSet_of_all hs.1 hs.2
      have hc1 : ∀ c ∈ e.consts, dom c := fun c h => hc c (by simp [CRA.consts, h])
      have hc2 : ∀ c ∈ f.consts, dom c := fun c h => hc c (by simp [CRA.consts, h])
      obtain ⟨r1, hr1, i1⟩ := tr_spec e he1 hc1 hi hf
      obtain ⟨r2, hr2, i2'⟩ := tr_spec f he2 hc2 (hi.congr hset) (hf.congr hset)
      have i2 := i2'.congr (fun a => (hset a).symm)
      have hn := (check_attrs hS e he1).1
      obtain ⟨q, hq, rq⟩ := rep_diff i1.rep i2.rep
      refine ⟨q, by simp only [CRA.toExpr]; exact eval_except2 hr1 hr2 hq, rq.wf, rq.head, fun ρ => ?_, ?_⟩
      · simp only [tr, Sat, i1.sat, i2.sat]
        constructor
        · rintro ⟨⟨t, ht, hm⟩, hn2⟩
          exact ⟨t, (rq.mem t).mpr ⟨i1.fits ht, ht, fun h2 => hn2 ⟨t, h2, hm⟩⟩, hm⟩
        · rintro ⟨t, ht, hm⟩
          obtain ⟨-, h1, h2⟩ := (rq.mem t).mp ht
          refine ⟨⟨t, h1, hm⟩, fun ⟨u, hu, hmu⟩ => h2 ?_⟩
          rw [match_unique hn (i1.fits h1) (i2.fits hu) hm hmu]; exact hu
      · intro t ht p hp
        exact i1.vals t ((rq.mem t).mp ht).2.1 p hp
    · cases he
  | .inter e f, as, μ, k, he, hc, hi, hf => by
    simp only [CRA.check, bind, Option.bind_eq_some_iff] at he
    obtain ⟨as', he1, bs', he2, he⟩ := he
    split at he
    · rename_i hs
      cases he
      have hset := sameSet_of_all hs.1 hs.2
      have hc1 : ∀ c ∈ e.consts, dom c := fun c h => hc c (by simp [CRA.consts, h])
      have hc2 : ∀ c ∈ f.consts, dom c := fun c h => hc c (by simp [CRA.consts, h])
      obtain ⟨r1, hr1, i1⟩ := tr_spec e he1 hc1 hi hf
      obtain ⟨r2, hr2, i2'⟩ := tr_spec f he2 hc2 (hi.congr hset) (hf.congr hset)
      have i2 := i2'.congr (fun a => (hset a).symm)
      have hn := (check_attrs hS e he1).1
      obtain ⟨q, hq⟩ := Finrel.inter_ok.mpr (sameHeading_of_rep i1.rep i2.rep)
      have hmem := Finrel.mem_inter hq
      refine ⟨q, by simp only [CRA.toExpr]; exact eval_inter2 hr1 hr2 hq, Finrel.inter_wf hq i1.wf,
        fun a => by rw [inter_heading hq]; exact i1.head a, fun ρ => ?_, ?_⟩
      · simp only [tr, Sat, i1.sat, i2.sat]
        constructor
        · rintro ⟨⟨t, ht, hm⟩, ⟨u, hu, hmu⟩⟩
          have : t = u := match_unique hn (i1.fits ht) (i2.fits hu) hm hmu
          subst this
          exact ⟨t, (hmem t).mpr ⟨ht, hu⟩, hm⟩
        · rintro ⟨t, ht, hm⟩
          obtain ⟨h1, h2⟩ := (hmem t).mp ht
          exact ⟨⟨t, h1, hm⟩, ⟨t, h2, hm⟩⟩
      · intro t ht p hp
        exact i1.vals t ((hmem t).mp ht).1 p hp
    · cases he

end Induction

/-! ## Theorem A -/

section TheoremA
variable {S : Schema} {D : Domain} {env : Env} {e : CRA} {as : List String}

theorem toCalc_vars (he : e.check S D = some as) : (e.toCalc S D).vars = as := by
  simp [CRA.toCalc, Query.vars, he, List.map_map, Function.comp_def]

theorem toCalc_tupleOf (he : e.check S D = some as) (ρ : String → Value) :
    (e.toCalc S D).tupleOf ρ = tupOf as id ρ := by
  simp [CRA.toCalc, Query.tupleOf, tupOf, he, List.map_map, Function.comp_def]

/-- **Theorem A** (Codd 1972; Abiteboul, Hull and Vianu 1995, Lemma 5.3.11). A
well-typed algebra query is never refused by Rasso's evaluator on a database of the
schema, and the relation it gives is exactly the set of answers of its translation,
whatever domain the quantifiers range over, as long as it holds the active domain. -/
theorem algebra_to_calculus (hS : S.WF) (hD : DomOK D = true) (he : e.check S D = some as)
    (henv : Conforms S D env) :
    ∃ r, Expr.eval env [] (e.toExpr D) = .ok (.finrel r) ∧ r.WF ∧
      (∀ a, r.heading.lookup a = (headerOf D as).lookup a) ∧
      ∀ dom : Value → Prop, (∀ v ∈ (e.toCalc S D).adom S env, dom v) →
        ∀ t, t ∈ r.tuples ↔ (e.toCalc S D).answers dom S env t := by
  obtain ⟨hn, hattr⟩ := check_attrs hS e he
  have hi : InjOn id as := fun _ _ _ _ h => h
  have hf : FreshFrom id as 0 := fun a ha j b _ _ => isAttribute_ne_fresh (hattr a ha) j b
  obtain ⟨r, hr, i0⟩ := tr_spec (dom := fun _ => True) hS hD henv (fun _ _ => trivial) e he
    (fun _ _ => trivial) hi hf
  refine ⟨r, hr, i0.wf, i0.head, fun dom hdom t => ?_⟩
  have hdom1 : ∀ v ∈ adom S env, dom v := fun v hv => hdom v (List.mem_append_left _ hv)
  have hc : ∀ c ∈ e.consts, dom c := fun c h =>
    hdom c (List.mem_append_right _ ((tr_facts hS e (μ := id) (k := 0) he).2.1 c h))
  obtain ⟨r', hr', i⟩ := tr_spec hS hD henv hdom1 e he hc hi hf
  have : r' = r := by
    rw [hr] at hr'
    cases hr'; rfl
  subst this
  simp only [Query.answers, toCalc_vars he, toCalc_tupleOf he]
  constructor
  · intro ht
    have ft := i.fits ht
    have hm := match_readAsg ft
    refine ⟨readAsg t, fun x hx => ?_, eq_tupOf hn ft hm, (i.sat _).mpr ⟨t, ht, hm⟩⟩
    obtain ⟨v, hv, -, hp⟩ := get?_fits ft hx
    simp only [readAsg, hv, Option.getD_some]
    exact i.vals t ht _ hp
  · rintro ⟨ρ, -, rfl, hs⟩
    obtain ⟨u, hu, hm⟩ := (i.sat ρ).mp hs
    rw [← eq_tupOf hn (i.fits hu) hm]; exact hu

/-- The translation of a well-typed algebra query is a well-typed calculus query. -/
theorem toCalc_WT (hS : S.WF) (he : e.check S D = some as) : (e.toCalc S D).WT S D := by
  obtain ⟨hn, hattr⟩ := check_attrs hS e he
  obtain ⟨f1, -, f3, f4, f5⟩ := tr_facts hS e (μ := id) (k := 0) he
  refine ⟨f5, fun c hc => f4 c (f3 c hc), ?_, ?_, fun x hx => ?_⟩
  · simpa [CRA.toCalc, he, List.map_map, Function.comp_def] using hn
  · intro p hp
    simp only [CRA.toCalc, he, Option.getD_some, List.mem_map] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    exact hattr a ha
  · rw [toCalc_vars he]
    simpa using f1 x hx

/-- The translation is domain independent. -/
theorem toCalc_domainIndependent (hS : S.WF) (hD : DomOK D = true)
    (he : e.check S D = some as) : (e.toCalc S D).DomainIndependent S D := by
  intro env henv dom hdom t
  obtain ⟨r, -, -, -, h⟩ := algebra_to_calculus hS hD he henv
  rw [← h dom hdom, ← h _ (fun _ hv => hv)]

end TheoremA

end Coddstheorem
