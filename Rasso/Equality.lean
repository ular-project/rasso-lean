import Rasso.NormalFormProof
import Rasso.EqElim

/-!
# Rasso: the equality class, proved

The executable part is `Rasso.EqElim`. This module proves that removing an attribute by
equality is sound: the new term holds a tuple exactly when some value of the removed
attribute's domain makes the old term hold. It instantiates the shared normal form's theorem
`NF.elim_sound`, so what is proved here is the class's own part:

* the domains: `Domain.subset?` is sound, and an infinite domain has a value outside any
  finite list (`Equality.fresh`);
* a leaf `x = τ` has a normal form that means it (`leaf_sem`);
* one `and`'s literals on `x` have a value of `x` that meets them all exactly when the terms
  `xpart` gives hold (`xpart_sem`).
-/

namespace Rasso

/-- `Domain.subset?` is sound. -/
theorem Domain.subset?_mem {d e : Domain} (h : d.subset? e = true) {v : Value}
    (hv : d.mem v = true) : e.mem v = true := by
  cases d with
  | kind k' =>
    cases e with
    | kind k =>
      simp only [Domain.subset?, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
      rcases h with rfl | ⟨rfl, rfl⟩
      · exact hv
      · cases v <;> simp_all [Domain.mem, Kind.has]
    | _ => simp [Domain.subset?] at h
  | range lo hi =>
    cases e with
    | kind k =>
      simp only [Domain.subset?, Bool.or_eq_true, beq_iff_eq] at h
      cases v <;> simp [Domain.mem] at hv
      rcases h with rfl | rfl <;> rfl
    | _ => simp [Domain.subset?] at h
  | set vs =>
    cases e with
    | kind k =>
      simp only [Domain.subset?, List.all_eq_true] at h
      exact h v (by simpa [Domain.mem] using hv)
    | _ => simp [Domain.subset?] at h

namespace Equality

/-! ## Fresh values -/

theorem fresh_string (L : List String) : ∃ s : String, s ∉ L := by
  let n := (L.map String.length).foldr max 0 + 1
  refine ⟨String.ofList (List.replicate n 'a'), fun h => ?_⟩
  have hle : ∀ (L : List String), ∀ s ∈ L, s.length ≤ (L.map String.length).foldr max 0 := by
    intro L s hs
    induction L with
    | nil => cases hs
    | cons x L ih =>
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp hs with rfl | hs
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hs) (Nat.le_max_right _ _)
  have := hle L _ h
  simp [n] at this
  omega

theorem fresh_int (L : List Int) : ∃ n : Int, n ∉ L := by
  refine ⟨(L.map Int.natAbs).foldr max 0 + 1, fun h => ?_⟩
  have hle : ∀ (L : List Int), ∀ s ∈ L, s.natAbs ≤ (L.map Int.natAbs).foldr max 0 := by
    intro L s hs
    induction L with
    | nil => cases hs
    | cons x L ih =>
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp hs with rfl | hs
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hs) (Nat.le_max_right _ _)
  have := hle L _ h
  omega

/-- **An infinite domain has a value outside any finite list.** -/
theorem fresh {d : Domain} (hd : infinite? d = true) (L : List Value) :
    ∃ v, d.mem v = true ∧ v ∉ L := by
  obtain ⟨s, hs⟩ := fresh_string (L.filterMap fun | .symbol s => some s | .string s => some s | _ => none)
  obtain ⟨n, hn⟩ := fresh_int (L.filterMap fun | .int n => some n | _ => none)
  match d, hd with
  | .kind .symbol, _ => exact ⟨.symbol s, rfl, fun h => hs (List.mem_filterMap.mpr ⟨_, h, rfl⟩)⟩
  | .kind .string, _ => exact ⟨.string s, rfl, fun h => hs (List.mem_filterMap.mpr ⟨_, h, rfl⟩)⟩
  | .kind .int, _ => exact ⟨.int n, rfl, fun h => hn (List.mem_filterMap.mpr ⟨_, h, rfl⟩)⟩

theorem infinite_kind {d : Domain} (hd : infinite? d = true) : ∃ k, d = .kind k := by
  match d, hd with
  | .kind k, _ => exact ⟨k, rfl⟩

theorem infinite_unmixed {d : Domain} (hd : infinite? d = true) : d.Unmixed := by
  obtain ⟨k, rfl⟩ := infinite_kind hd
  exact Domain.unmixed_kind k

/-! ## Operands -/

/-- The value an operand stands for on a tuple (a default when it refuses). -/
def valOf (t : Tuple) (τ : Term) : Value :=
  match τ.eval t with
  | .ok v => v
  | .error _ => default

theorem not_mem_of_inDom {h : Heading} {a : String} {d : Domain} {τ : Term}
    (hn : inDom h a d τ = true) : a ∉ τ.attrs := by
  cases τ <;> simp_all [inDom, Term.attrs]
  exact fun e => hn.1 e.symm

/-- An operand in `x`'s domain is a value of the domain on a tuple that fits the heading
without `a`. -/
theorem inDom_eval {h : Heading} {a : String} {d : Domain} {τ : Term} {t : Tuple}
    (hn : inDom h a d τ = true) (f : t.Fits (h.filter (·.1 ≠ a))) :
    τ.eval t = .ok (valOf t τ) ∧ d.mem (valOf t τ) = true := by
  cases τ with
  | val v => simpa [Term.eval, valOf, inDom] using hn
  | attr b =>
    simp only [inDom, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
    obtain ⟨hba, hsub⟩ := hn
    obtain ⟨db, hdb, hs⟩ : ∃ db, h.lookup b = some db ∧ db.subset? d = true := by
      cases e : h.lookup b with
      | none => simp [e] at hsub
      | some db => simp only [e] at hsub; exact ⟨db, rfl, hsub⟩
    have hfl : (h.filter (·.1 ≠ a)).lookup b = some db := by
      rw [lookup_filter_key (c := fun x => decide (x ≠ a)) (by simpa using hba)]; exact hdb
    have hin : b ∈ Heading.attrs (h.filter (·.1 ≠ a)) :=
      Finrel.mem_attrs_iff.mpr (by rw [hfl]; rfl)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((f.get?_isSome b).mpr hin)
    have hmem := f.dom (b, v) (lookup_mem hv) db hfl
    have he : (Term.attr b).eval t = .ok v := by simp [Term.eval, hv]
    simp only [valOf, he]
    exact ⟨trivial, Domain.subset?_mem hs hmem⟩
  | _ => simp [inDom] at hn

/-- `=` on two operands with values in an infinite domain. -/
theorem holds_eq {d : Domain} (hd : infinite? d = true) {s : Tuple} {l r : Term} {v w : Value}
    (hl : l.eval s = .ok v) (hv : d.mem v = true) (hr : r.eval s = .ok w) (hw : d.mem w = true) :
    (Term.call "=" [l, r]).holds s = .ok (v == w) := by
  rw [Term.holds_ok]
  simp [Term.eval, hl, hr, bind, Except.bind, applyOp_eq_unmixed (infinite_unmixed hd) hv hw, pure,
    Except.pure]

/-! ## The specification -/

/-- The leaves the class accepts: `l = r`, each operand `x` or in `x`'s domain `d`. -/
def EqOk (h : Heading) (a : String) (d : Domain) (op : String) (es : List Term) : Prop :=
  op = "=" ∧ ∃ l r, es = [l, r] ∧ operand? h a d l = true ∧ operand? h a d r = true

/-- `e` is a term in which every leaf that mentions `a` is `=` with a value of `a`'s domain
`d`, in a Boolean skeleton of `and`, `or` and `not`. A part that does not mention `a` may be
anything. -/
abbrev EqIn (h : Heading) (a : String) (d : Domain) : Term → Prop := NF.In (EqOk h a d) a

/-- A literal `x = τ` (`(true, τ)`) or `not (x = τ)` (`(false, τ)`) is true on `t` when `x`
is `v`. -/
def ESem (t : Tuple) (v : Value) (x : Bool × Term) : Prop := (v == valOf t x.2) = x.1

/-- What the normal form promises of a literal on `x`: its operand is in `x`'s domain, and it
reads only `R`. -/
def EGood (h : Heading) (a : String) (d : Domain) (R : List String) (x : Bool × Term) : Prop :=
  inDom h a d x.2 = true ∧ ∀ y ∈ x.2.attrs, y ∈ R

/-! ## A leaf means its normal form -/

section Leaf

variable {h : Heading} {a : String} {d : Domain} {t : Tuple}

/-- The value of each operand of `=`, with `a` set to `v`. -/
theorem operand_value (ht : Tuple.Sorted t)
    (f : t.Fits (h.filter (·.1 ≠ a))) {v : Value} (hv : d.mem v = true) {o : Term}
    (ho : operand? h a d o = true) :
    ∃ w, o.eval (t.set a v) = .ok w ∧ d.mem w = true ∧
      w = (if isAttr a o then v else valOf t o) := by
  by_cases hi : isAttr a o = true
  · have e := NF.isAttr_iff.mp hi
    subst e
    exact ⟨v, eval_attr_set ht a v, hv, by simp [hi]⟩
  · have hn : inDom h a d o = true := by simpa [operand?, hi] using ho
    obtain ⟨he, hm⟩ := inDom_eval hn f
    refine ⟨valOf t o, ?_, hm, by simp [hi]⟩
    rw [Term.eval_set_of_not_mem ht (not_mem_of_inDom hn)]; exact he

theorem leaf_eq {p : Bool} {l r : Term} :
    leaf a p "=" [l, r] =
      if isAttr a l then (if isAttr a r then [[.const p]] else [[.atom (p, r)]])
      else [[.atom (p, l)]] := by
  simp [leaf]

open NF in
/-- The class's leaf is right: `l = r` that mentions `x`, under a sign, has a normal form that
means it. -/
theorem leaf_sem (hd : infinite? d = true) (ht : Tuple.Sorted t) (f : t.Fits (h.filter (·.1 ≠ a)))
    {v : Value} (hv : d.mem v = true) :
    ∀ {op : String} {es : List Term}, op ≠ "and" → op ≠ "or" → op ≠ "not" → EqOk h a d op es →
      a ∈ (Term.call op es).attrs → ∀ {R : List String}, (∀ x ∈ (Term.call op es).attrs, x ∈ R) →
      ∀ (p b : Bool), (Term.call op es).holds (t.set a v) = .ok b →
      NF.DnfOk (ESem t v) (EGood h a d) a t R p b (leaf a p op es) := by
  intro op es _ _ _ hA hc R hR p b hb
  obtain ⟨rfl, l, r, rfl, hl, hr⟩ := hA
  obtain ⟨wl, hwl, hml, hql⟩ := operand_value ht f hv hl
  obtain ⟨wr, hwr, hmr, hqr⟩ := operand_value ht f hv hr
  rw [holds_eq hd hwl hml hwr hmr] at hb; cases hb
  have hRl : ∀ y ∈ l.attrs, y ∈ R := attrs_sub_call List.mem_cons_self hR
  have hRr : ∀ y ∈ r.attrs, y ∈ R :=
    attrs_sub_call (List.mem_cons_of_mem _ List.mem_cons_self) hR
  rw [leaf_eq]
  by_cases il : isAttr a l = true
  · by_cases ir : isAttr a r = true
    · simp only [il, ir, ↓reduceIte] at hql hqr ⊢
      subst hql hqr
      refine ⟨fun c hc l hl => by simp_all [Lit.Good], ?_⟩
      simp only [List.mem_singleton, exists_eq_left, forall_eq, Lit.Sem, beq_self_eq_true]
      exact eq_comm
    · have hn : inDom h a d r = true := by simpa [operand?, ir] using hr
      simp only [il, ir, ↓reduceIte, Bool.false_eq_true] at hql hqr ⊢
      subst hql hqr
      refine ⟨fun c hc l hl => ?_, ?_⟩
      · simp only [List.mem_singleton] at hc; subst hc
        simp only [List.mem_singleton] at hl; subst hl
        exact ⟨hn, hRr⟩
      · simp only [List.mem_singleton, exists_eq_left, forall_eq, Lit.Sem, ESem]
  · have hn : inDom h a d l = true := by simpa [operand?, il] using hl
    have ir : isAttr a r = true := by
      cases ir : isAttr a r
      case true => rfl
      exfalso
      have hn' : inDom h a d r = true := by simpa [operand?, ir] using hr
      simp only [Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at hc
      rcases hc with hc | hc
      · exact not_mem_of_inDom hn hc
      · exact not_mem_of_inDom hn' hc
    simp only [il, ir, ↓reduceIte, Bool.false_eq_true] at hql hqr ⊢
    subst hql hqr
    refine ⟨fun c hc l hl => ?_, ?_⟩
    · simp only [List.mem_singleton] at hc; subst hc
      simp only [List.mem_singleton] at hl; subst hl
      exact ⟨hn, hRl⟩
    · simp only [List.mem_singleton, exists_eq_left, forall_eq, Lit.Sem, ESem]
      rw [Bool.beq_comm]

end Leaf

/-! ## One `and`: substitute, or a fresh value -/

section Part

variable {h : Heading} {a : String} {d : Domain} {t : Tuple}

/-- `τ₀ = τ` under a sign, as `xpart` writes it. -/
theorem holds_signed (hd : infinite? d = true) {τ₀ τ : Term} {w₀ w : Value}
    (h₀ : τ₀.eval t = .ok w₀) (hm₀ : d.mem w₀ = true) (h₁ : τ.eval t = .ok w)
    (hm₁ : d.mem w = true) (s : Bool) :
    (if s then Term.call "=" [τ₀, τ] else .call "not" [.call "=" [τ₀, τ]]).holds t =
      .ok (if s then (w₀ == w) else !(w₀ == w)) := by
  have he := holds_eq hd h₀ hm₀ h₁ hm₁
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact holds_not1.mpr ⟨_, he, rfl⟩
  · simpa using he

theorem signed_true (s b : Bool) : (if s then b else !b) = true ↔ b = s := by
  cases s <;> cases b <;> simp

/-- **One `and`.** The terms `xpart` gives each hold a Boolean and read only `R`, and all hold
exactly when some value of `x`'s domain meets every literal on `x`. -/
theorem xpart_sem (hd : infinite? d = true) (f : t.Fits (h.filter (·.1 ≠ a))) {R : List String}
    {xs : List (Bool × Term)} (hx : ∀ x ∈ xs, EGood h a d R x) :
    (∀ e ∈ xpart xs, (∃ b, e.holds t = .ok b) ∧ ∀ x ∈ e.attrs, x ∈ R) ∧
      ((∀ e ∈ xpart xs, e.holds t = .ok true) ↔
        ∃ q : {v : Value // d.mem v = true}, ∀ x ∈ xs, ESem t q.1 x) := by
  have hev : ∀ x ∈ xs, x.2.eval t = .ok (valOf t x.2) ∧ d.mem (valOf t x.2) = true :=
    fun x hx' => inDom_eval (hx x hx').1 f
  unfold xpart
  split
  · rename_i b₀ τ₀ hf
    have hm := List.mem_of_find?_eq_some hf
    have hb₀ : b₀ = true := by simpa using List.find?_some hf
    subst hb₀
    have h₀ := hev _ hm
    have hterm : ∀ x ∈ xs, (if x.1 then Term.call "=" [τ₀, x.2]
        else .call "not" [.call "=" [τ₀, x.2]]).holds t =
          .ok (if x.1 then (valOf t τ₀ == valOf t x.2) else !(valOf t τ₀ == valOf t x.2)) :=
      fun x hx' => holds_signed hd h₀.1 h₀.2 (hev x hx').1 (hev x hx').2 x.1
    refine ⟨fun e he => ?_, ?_⟩
    · obtain ⟨x, hx', rfl⟩ := List.mem_map.mp he
      refine ⟨⟨_, hterm x hx'⟩, fun y hy => ?_⟩
      have hR₀ := (hx _ hm).2
      have hR₁ := (hx x hx').2
      cases hs : x.1 <;> simp only [hs, Bool.false_eq_true, ↓reduceIte, Term.attrs,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hy <;>
        rcases hy with hy | hy
      · exact hR₀ y hy
      · exact hR₁ y hy
      · exact hR₀ y hy
      · exact hR₁ y hy
    · simp only [List.mem_map, forall_exists_index, and_imp]
      constructor
      · intro hall
        refine ⟨⟨valOf t τ₀, h₀.2⟩, fun x hx' => ?_⟩
        have := hall _ x hx' rfl
        rw [hterm x hx', Except.ok.injEq, signed_true] at this
        exact this
      · rintro ⟨⟨v, hv⟩, hq⟩ _ x hx' rfl
        have hv₀ : v = valOf t τ₀ := by simpa [ESem] using hq _ hm
        subst hv₀
        rw [hterm x hx', Except.ok.injEq, signed_true]
        exact hq x hx'
  · rename_i hf
    have hneg : ∀ x ∈ xs, x.1 = false := fun x hx' => by
      have := List.find?_eq_none.mp hf x hx'
      simpa using this
    refine ⟨fun e he => absurd he List.not_mem_nil, ?_⟩
    simp only [List.not_mem_nil, false_implies, implies_true, true_iff]
    obtain ⟨v, hv, hvL⟩ := fresh hd (xs.map fun x => valOf t x.2)
    refine ⟨⟨v, hv⟩, fun x hx' => ?_⟩
    simp only [ESem, hneg x hx']
    cases e : (v == valOf t x.2)
    · rfl
    · exact absurd (List.mem_map.mpr ⟨x, hx', (beq_iff_eq.mp e).symm⟩) hvL

end Part

/-! ## What the new term reads -/

open NF in
theorem leaf_attrs {h : Heading} {a : String} {d : Domain} :
    ∀ {op : String} {es : List Term}, EqOk h a d op es → a ∈ (Term.call op es).attrs →
      ∀ (p : Bool), ∀ c ∈ leaf a p op es, ∀ l ∈ c, ∀ x ∈ l.attrs (fun y : Bool × Term => y.2.attrs),
        x ∈ (Term.call op es).attrs ∧ x ≠ a := by
  intro op es hA hca p c hc l hl x hx
  obtain ⟨rfl, l', r', rfl, hl', hr'⟩ := hA
  rw [leaf_eq] at hc
  have hmem : ∀ o, o = l' ∨ o = r' → isAttr a o = false → inDom h a d o = true ∧
      ∀ y ∈ o.attrs, y ∈ (Term.call "=" [l', r']).attrs := by
    rintro o (rfl | rfl) hi
    · exact ⟨by simpa [operand?, hi] using hl', fun y hy => by simp [Term.attrs, hy]⟩
    · exact ⟨by simpa [operand?, hi] using hr', fun y hy => by simp [Term.attrs, hy]⟩
  by_cases il : isAttr a l' = true
  · by_cases ir : isAttr a r' = true
    · simp only [il, ir, ↓reduceIte, List.mem_singleton] at hc; subst hc
      simp only [List.mem_singleton] at hl; subst hl
      simp [NF.Lit.attrs] at hx
    · simp only [il, ir, ↓reduceIte, Bool.false_eq_true, List.mem_singleton] at hc; subst hc
      simp only [List.mem_singleton] at hl; subst hl
      have := hmem r' (.inr rfl) (by simpa using ir)
      exact ⟨this.2 x hx, fun e => not_mem_of_inDom this.1 (e ▸ hx)⟩
  · simp only [il, ↓reduceIte, Bool.false_eq_true, List.mem_singleton] at hc; subst hc
    simp only [List.mem_singleton] at hl; subst hl
    have := hmem l' (.inl rfl) (by simpa using il)
    exact ⟨this.2 x hx, fun e => not_mem_of_inDom this.1 (e ▸ hx)⟩

/-- A term of `xpart` reads only what its literals read. -/
theorem xpart_attrs (xs : List (Bool × Term)) (e : Term) (he : e ∈ xpart xs) :
    ∀ x ∈ e.attrs, ∃ l ∈ xs, x ∈ l.2.attrs := by
  intro x hx
  unfold xpart at he
  split at he
  · rename_i b₀ τ₀ hf
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    have hm := List.mem_of_find?_eq_some hf
    cases hs : q.1 <;> simp only [hs, Bool.false_eq_true, ↓reduceIte, Term.attrs,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx <;>
      rcases hx with hx | hx
    · exact ⟨_, hm, hx⟩
    · exact ⟨q, hq, hx⟩
    · exact ⟨_, hm, hx⟩
    · exact ⟨q, hq, hx⟩
  · cases he

/-! ## The class obligation -/

/-- **Removal by equality is sound.** With `a`'s domain the whole symbol, string or int kind,
and every leaf that mentions `a` an `=` with a value of that domain, the new term reads only
the remaining attributes, never refuses on a fitting tuple, and holds `t` exactly when some
value of `a` makes the old term hold. An instance of `NF.elim_sound`, with the domain's
values as the values of `a`. -/
theorem elim_sound {u : Unrel} {a : String} {d : Domain} (hd : u.heading.lookup a = some d)
    (hinf : infinite? d = true) (hacc : EqIn u.heading a d u.term) (hu : u.WF) (tu : u.Total) :
    let w : Unrel := ⟨u.heading.filter (·.1 ≠ a), elim a u.term⟩
    (∀ x ∈ w.term.attrs, x ∈ w.heading.attrs) ∧ w.Total ∧
      ∀ t, t.Fits w.heading → (w.Holds t ↔ ∃ v, u.Holds (t.set a v)) :=
  have q₀ : {v : Value // d.mem v = true} :=
    ⟨Classical.choose (fresh hinf []), (Classical.choose_spec (fresh hinf [])).1⟩
  NF.elim_sound (at' := fun y : Bool × Term => y.2.attrs) hd Subtype.val (fun q => q.2)
    (fun v hv => ⟨⟨v, hv⟩, rfl⟩) q₀ (fun t q => ESem t q.1) (fun _ => EGood u.heading a d) hacc
    hu tu (fun _ f q => leaf_sem hinf f.sorted f q.2) (fun _ f _ _ hx => xpart_sem hinf f hx)
    leaf_attrs xpart_attrs

/-! ## The test decides the specification -/

theorem leafOk_sound {h : Heading} {a : String} {d : Domain} {op : String} {es : List Term}
    (hok : leafOk h a d op es = true) : EqOk h a d op es := by
  unfold leafOk at hok
  split at hok
  · rename_i hop
    refine ⟨hop, ?_⟩
    split at hok
    · rename_i l r
      simp only [Bool.and_eq_true] at hok
      exact ⟨l, r, rfl, hok.1, hok.2⟩
    · cases hok
  · cases hok

theorem leafOk_complete {h : Heading} {a : String} {d : Domain} {op : String} {es : List Term}
    (hA : EqOk h a d op es) : leafOk h a d op es = true := by
  obtain ⟨rfl, l, r, rfl, hl, hr⟩ := hA
  simp [leafOk, hl, hr]

theorem accepts_iff {h : Heading} {a : String} {d : Domain} {e : Term} :
    accepts? h a d e = true ↔ EqIn h a d e :=
  ⟨fun hacc => NF.accepts_sound (fun _ _ _ => leafOk_sound) e hacc,
   fun he => NF.accepts_complete leafOk_complete he⟩

end Equality

end Rasso
