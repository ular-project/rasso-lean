import Rasso.NormalFormProof
import Rasso.DenseElim

/-!
# Rasso: the dense-order class, proved

The executable part is `Rasso.DenseElim`. This module proves that removing an attribute by
dense order is sound: the new term holds a tuple exactly when some rat value of the removed
attribute makes the old term hold.
-/

namespace Rasso

/-! ## Exact numbers -/

theorem Value.exact?_kindRank {v : Value} {q : Rat} (h : v.exact? = some q) : v.kindRank = 1 := by
  cases v <;> simp_all [Value.exact?, Value.kindRank]

theorem Value.num?_of_exact? {v : Value} {q : Rat} (h : v.exact? = some q) : v.num? = some q := by
  cases v <;> simp_all [Value.exact?, Value.num?]

theorem Value.nonNumKey_of_exact? {v : Value} {q : Rat} (h : v.exact? = some q) :
    v.nonNumKey = [] := by
  simp [Value.nonNumKey, Value.num?_of_exact? h]

/-- On exact numbers, the order a program sees is the order of ℚ. -/
theorem Value.cmp_exact {v w : Value} {q r : Rat} (hv : v.exact? = some q)
    (hw : w.exact? = some r) : Value.cmp v w = compare q r := by
  simp only [Value.cmp, compareLex, compareOn, Value.exact?_kindRank hv,
    Value.exact?_kindRank hw, Value.num?_of_exact? hv, Value.num?_of_exact? hw,
    Value.nonNumKey_of_exact? hv, Value.nonNumKey_of_exact? hw]
  have h1 : compare (1 : Nat) 1 = .eq := Nat.compare_eq_eq.mpr rfl
  have h2 : compare ([] : List Int) [] = .eq := rfl
  have h3 : compare (some q) (some r) = compare q r := rfl
  rw [h1, h2, h3]
  cases compare q r <;> rfl

theorem Rat.compare_lt_iff {q r : Rat} : compare q r = .lt ↔ q < r :=
  compareOfLessAndEq_eq_lt

theorem Rat.compare_eq_iff {q r : Rat} : compare q r = .eq ↔ q = r :=
  compareOfLessAndEq_eq_eq (fun _ => Rat.le_refl) Rat.not_le

theorem Rat.compare_gt_iff {q r : Rat} : compare q r = .gt ↔ r < q := by
  constructor
  · intro h
    have tri : q < r ∨ q = r ∨ r < q := by grind
    rcases tri with hl | he | hg
    · rw [Rat.compare_lt_iff.mpr hl] at h; cases h
    · rw [Rat.compare_eq_iff.mpr he] at h; cases h
    · exact hg
  · intro h
    cases e : compare q r
    · have := Rat.compare_lt_iff.mp e; grind
    · have := Rat.compare_eq_iff.mp e; grind
    · rfl

/-- An exact number is the value of its rational. -/
theorem Value.eq_ofRat {v : Value} {q : Rat} (h : v.exact? = some q) : v = Value.ofRat q := by
  cases v with
  | int n =>
    simp only [Value.exact?, Option.some.injEq] at h
    subst h
    simp [Value.ofRat]
  | rat q' hq =>
    simp only [Value.exact?, Option.some.injEq] at h
    subst h
    simp [Value.ofRat, hq]
  | _ => simp [Value.exact?] at h

namespace Dense

/-- What `q ⋈ r` is on ℚ. -/
def XRel.test : XRel → Rat → Rat → Bool
  | .lt, q, r => decide (q < r)
  | .le, q, r => decide (q ≤ r)
  | .eq, q, r => decide (q = r)
  | .ge, q, r => decide (r ≤ q)
  | .gt, q, r => decide (r < q)

end Dense

open Dense in
/-- A comparison of two exact numbers never refuses; it compares them in ℚ. -/
theorem applyOp_exact (r : XRel) {v w : Value} {q q' : Rat} (hv : v.exact? = some q)
    (hw : w.exact? = some q') : applyOp r.op [v, w] = .ok (.bool (r.test q q')) := by
  have hc := Value.cmp_exact hv hw
  have tri : q < q' ∨ q = q' ∨ q' < q := by grind
  have hcmp : Value.cmp v w = (if q < q' then .lt else if q = q' then .eq else .gt) := by
    rw [hc]
    rcases tri with h | h | h
    · simp [Rat.compare_lt_iff.mpr h, h]
    · subst h; simp [Rat.lt_irrefl]
    · have h1 : ¬ q < q' := by grind
      have h2 : q ≠ q' := by grind
      simp [Rat.compare_gt_iff.mpr h, h1, h2]
  have hbeq : (v == w) = decide (q = q') := by
    rw [Value.eq_ofRat hv, Value.eq_ofRat hw]
    by_cases e : q = q'
    · subst e; simp
    · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
      exact fun h => e (Value.ofRat_inj h)
  cases r
  case eq =>
    simp only [XRel.op, applyOp, XRel.test]
    cases v <;> cases w <;> simp_all [Value.exact?] <;> rfl
  all_goals
    simp only [XRel.op, applyOp, XRel.test, hcmp]
    show Except.ok _ = _
    congr 2
    by_cases h1 : q < q' <;> by_cases h2 : q = q' <;> simp [h1, h2] <;> grind

/-- A value of a domain that holds numbers only is an exact number. -/
theorem Domain.exact_of_numeric {d : Domain} {k : Domain} {v : Value} (hk : d.numeric = some k)
    (hv : d.mem v = true) : v.exact?.isSome := by
  cases d with
  | kind kd =>
    cases kd <;> simp [Domain.numeric] at hk <;>
      cases v <;> simp_all [Domain.mem, Kind.has, Value.exact?]
  | range lo hi => cases v <;> simp_all [Domain.mem, Value.exact?]
  | set vs =>
    simp only [Domain.mem, List.contains_iff_mem] at hv
    simp only [Domain.numeric] at hk
    split at hk
    · rename_i hall
      have := List.all_eq_true.mp hall v hv
      cases v <;> simp_all [Value.exact?]
    · split at hk
      · rename_i _ hall
        exact List.all_eq_true.mp hall v hv
      · cases hk

namespace Dense

/-! ## Order over ℚ: density and no endpoints

Rasso keeps its own copy, so that it stays self-contained. -/

/-- `a < b` when `strict`, else `a ≤ b`. -/
def qltb (strict : Bool) (a b : Rat) : Prop := if strict then a < b else a ≤ b

theorem qltb_of_lt {s : Bool} {a b : Rat} (h : a < b) : qltb s a b := by
  cases s <;> simp only [qltb, Bool.false_eq_true, ↓reduceIte] <;> grind

theorem qlo_exists : (L : List (Rat × Bool)) → L ≠ [] →
    ∃ b ∈ L, ∀ l ∈ L, ∀ d, qltb b.2 b.1 d → qltb l.2 l.1 d
  | [], h => absurd rfl h
  | [l], _ => ⟨l, by simp, fun l' hl' d hd => by simp at hl'; subst hl'; exact hd⟩
  | l :: l₂ :: L, _ => by
    obtain ⟨b, hb, hdom⟩ := qlo_exists (l₂ :: L) (by simp)
    have key : (∀ d, qltb l.2 l.1 d → qltb b.2 b.1 d) ∨ (∀ d, qltb b.2 b.1 d → qltb l.2 l.1 d) := by
      obtain ⟨x, s⟩ := l; obtain ⟨y, t⟩ := b
      have tri : y < x ∨ y = x ∨ x < y := by grind
      rcases tri with e | e | e
      · exact .inl fun d hd => by
          cases s <;> cases t <;> simp only [qltb, Bool.false_eq_true, ↓reduceIte] at hd ⊢ <;> grind
      · cases s
        · exact .inr fun d hd => by
            cases t <;> simp only [qltb, Bool.false_eq_true, ↓reduceIte] at hd ⊢ <;> grind
        · exact .inl fun d hd => by
            cases t <;> simp only [qltb, Bool.false_eq_true, ↓reduceIte] at hd ⊢ <;> grind
      · exact .inr fun d hd => by
          cases s <;> cases t <;> simp only [qltb, Bool.false_eq_true, ↓reduceIte] at hd ⊢ <;> grind
    rcases key with k | k
    · refine ⟨l, by simp, fun l' hl' d hd => ?_⟩
      simp only [List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · exact hd
      · exact hdom l' (by simpa using hl') d (k d hd)
    · refine ⟨b, List.mem_cons_of_mem _ hb, fun l' hl' d hd => ?_⟩
      simp only [List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · exact k d hd
      · exact hdom l' (by simpa using hl') d hd

theorem qhi_exists : (U : List (Rat × Bool)) → U ≠ [] →
    ∃ b ∈ U, ∀ u ∈ U, ∀ d, qltb b.2 d b.1 → qltb u.2 d u.1
  | [], h => absurd rfl h
  | [u], _ => ⟨u, by simp, fun u' hu' d hd => by simp at hu'; subst hu'; exact hd⟩
  | u :: u₂ :: U, _ => by
    obtain ⟨b, hb, hdom⟩ := qhi_exists (u₂ :: U) (by simp)
    have key : (∀ d, qltb u.2 d u.1 → qltb b.2 d b.1) ∨ (∀ d, qltb b.2 d b.1 → qltb u.2 d u.1) := by
      obtain ⟨x, s⟩ := u; obtain ⟨y, t⟩ := b
      have tri : x < y ∨ x = y ∨ y < x := by grind
      rcases tri with e | e | e
      · exact .inl fun d hd => by
          cases s <;> cases t <;> simp only [qltb, Bool.false_eq_true, ↓reduceIte] at hd ⊢ <;> grind
      · cases s
        · exact .inr fun d hd => by
            cases t <;> simp only [qltb, Bool.false_eq_true, ↓reduceIte] at hd ⊢ <;> grind
        · exact .inl fun d hd => by
            cases t <;> simp only [qltb, Bool.false_eq_true, ↓reduceIte] at hd ⊢ <;> grind
      · exact .inr fun d hd => by
          cases s <;> cases t <;> simp only [qltb, Bool.false_eq_true, ↓reduceIte] at hd ⊢ <;> grind
    rcases key with k | k
    · refine ⟨u, by simp, fun u' hu' d hd => ?_⟩
      simp only [List.mem_cons] at hu'
      rcases hu' with rfl | hu'
      · exact hd
      · exact hdom u' (by simpa using hu') d (k d hd)
    · refine ⟨b, List.mem_cons_of_mem _ hb, fun u' hu' d hd => ?_⟩
      simp only [List.mem_cons] at hu'
      rcases hu' with rfl | hu'
      · exact k d hd
      · exact hdom u' (by simpa using hu') d hd

/-- If every lower bound is compatible with every upper bound, some rational lies within
all of them. This is where density and the absence of endpoints are used. -/
theorem qinterval (L U : List (Rat × Bool)) (h : ∀ l ∈ L, ∀ u ∈ U, qltb (l.2 || u.2) l.1 u.1) :
    ∃ d, (∀ l ∈ L, qltb l.2 l.1 d) ∧ (∀ u ∈ U, qltb u.2 d u.1) := by
  by_cases hL : L = [] <;> by_cases hU : U = []
  · subst hL; subst hU; exact ⟨0, by simp, by simp⟩
  · subst hL
    obtain ⟨c, _, hc⟩ := qhi_exists U hU
    exact ⟨c.1 - 1, by simp, fun u hu => hc u hu _ (qltb_of_lt (by grind))⟩
  · subst hU
    obtain ⟨b, _, hb⟩ := qlo_exists L hL
    exact ⟨b.1 + 1, fun l hl => hb l hl _ (qltb_of_lt (by grind)), by simp⟩
  · obtain ⟨b, hbL, hb⟩ := qlo_exists L hL
    obtain ⟨c, hcU, hc⟩ := qhi_exists U hU
    have hbc := h b hbL c hcU
    have tri : b.1 < c.1 ∨ b.1 = c.1 ∨ c.1 < b.1 := by grind
    rcases tri with e | e | e
    · exact ⟨(b.1 + c.1) / 2, fun l hl => hb l hl _ (qltb_of_lt (by grind)),
        fun u hu => hc u hu _ (qltb_of_lt (by grind))⟩
    · have hs : b.2 = false ∧ c.2 = false := by
        cases hb2 : b.2 <;> cases hc2 : c.2 <;>
          simp only [hb2, hc2, qltb, Bool.or_self, Bool.or_true, Bool.or_false,
            Bool.false_eq_true, ↓reduceIte] at hbc ⊢ <;> grind
      refine ⟨b.1, fun l hl => hb l hl _ ?_, fun u hu => hc u hu _ ?_⟩
      · simp [qltb, hs.1]
      · simp only [qltb, hs.2, Bool.false_eq_true, ↓reduceIte]; grind
    · exfalso
      cases hs : (b.2 || c.2) <;> simp only [qltb, hs, Bool.false_eq_true, ↓reduceIte] at hbc <;>
        grind

theorem qltb_trans {s s' : Bool} {a b c : Rat} (h₁ : qltb s a b) (h₂ : qltb s' b c) :
    qltb (s || s') a c := by
  cases s <;> cases s' <;>
    simp only [qltb, Bool.false_eq_true, ↓reduceIte, Bool.or_self, Bool.or_true,
      Bool.or_false] at h₁ h₂ ⊢ <;> grind

end Dense
namespace Dense

set_option linter.unusedSimpArgs false in
theorem XRel.ofOp_some {op : String} {r : XRel} (h : XRel.ofOp op = some r) : op = r.op := by
  unfold XRel.ofOp at h
  by_cases h1 : op = "<"
  · simp [h1] at h; subst h; exact h1
  by_cases h2 : op = "<="
  · simp [h1, h2] at h; subst h; exact h2
  by_cases h3 : op = "="
  · simp [h1, h2, h3] at h; subst h; exact h3
  by_cases h4 : op = ">="
  · simp [h1, h2, h3, h4] at h; subst h; exact h4
  by_cases h5 : op = ">"
  · simp [h1, h2, h3, h4, h5] at h; subst h; exact h5
  simp [h1, h2, h3, h4, h5] at h

theorem XRel.test_refl (r : XRel) (q : Rat) : r.test q q = r.refl := by
  cases r <;> simp [XRel.test, XRel.refl, Rat.lt_irrefl]

theorem XRel.test_flip (r : XRel) (q q' : Rat) : r.flip.test q q' = r.test q' q := by
  cases r <;> simp [XRel.test, XRel.flip, eq_comm]

theorem XRel.test_neg (r : XRel) (q q' : Rat) :
    (∃ s ∈ r.neg, s.test q q' = true) ↔ r.test q q' = false := by
  cases r <;> simp [XRel.test, XRel.neg] <;> grind

/-- The rational an operand stands for on a tuple (0 when it is not a number). -/
def qOf (t : Tuple) (τ : Term) : Rat :=
  match τ.eval t with
  | .ok v => v.exact?.getD 0
  | .error _ => 0

theorem eval_qOf {t : Tuple} {τ : Term} {v : Value} {q : Rat} (he : τ.eval t = .ok v)
    (hq : v.exact? = some q) : qOf t τ = q := by
  simp [qOf, he, hq]

end Dense

open Dense in
/-- A comparison of two operands that are exact numbers. -/
theorem holds_cmp {t : Tuple} (r : XRel) {l r' : Term} {v w : Value} {q q' : Rat}
    (hl : l.eval t = .ok v) (hv : v.exact? = some q) (hr : r'.eval t = .ok w)
    (hw : w.exact? = some q') : (Term.call r.op [l, r']).holds t = .ok (r.test q q') := by
  rw [Term.holds_ok]
  simp [Term.eval, hl, hr, bind, Except.bind, applyOp_exact r hv hw, pure, Except.pure]

namespace Dense

theorem isAttr_iff {a : String} {e : Term} : isAttr a e = true ↔ e = .attr a := by
  cases e <;> simp [isAttr]

theorem not_mem_of_numOperand {h : Heading} {a : String} {τ : Term}
    (hn : numOperand? h a τ = true) : a ∉ τ.attrs := by
  cases τ <;> simp_all [numOperand?, Term.attrs]
  exact fun e => hn.1 e.symm

/-- A number operand is an exact number on a tuple that fits the heading without `a`. -/
theorem numOperand_eval {h : Heading} {a : String} {τ : Term} {t : Tuple}
    (hn : numOperand? h a τ = true) (f : t.Fits (h.filter (·.1 ≠ a))) :
    ∃ v, τ.eval t = .ok v ∧ v.exact? = some (qOf t τ) := by
  cases τ with
  | val v =>
    simp only [numOperand?] at hn
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hn
    have he : (Term.val v).eval t = .ok v := by simp [Term.eval]
    exact ⟨v, he, by rw [hq, eval_qOf he hq]⟩
  | attr b =>
    simp only [numOperand?, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
    obtain ⟨hba, hnum⟩ := hn
    obtain ⟨dm, k, hdm, hk⟩ : ∃ dm k, h.lookup b = some dm ∧ dm.numeric = some k := by
      cases e : h.lookup b with
      | none => simp [e] at hnum
      | some dm =>
        simp only [e, Option.bind_some] at hnum
        obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hnum
        exact ⟨dm, k, rfl, hk⟩
    have hfl : (h.filter (·.1 ≠ a)).lookup b = some dm := by
      rw [lookup_filter_key (c := fun x => decide (x ≠ a)) (by simpa using hba)]; exact hdm
    have hin : b ∈ Heading.attrs (h.filter (·.1 ≠ a)) :=
      Finrel.mem_attrs_iff.mpr (by rw [hfl]; rfl)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((f.get?_isSome b).mpr hin)
    have hmem := f.dom (b, v) (lookup_mem hv) dm hfl
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (Domain.exact_of_numeric hk hmem)
    have he : (Term.attr b).eval t = .ok v := by simp [Term.eval, hv]
    exact ⟨v, he, by rw [hq, eval_qOf he hq]⟩
  | _ => simp [numOperand?] at hn

end Dense

namespace Dense

/-! ## The specification -/

/-- `e` is a term in which every comparison that mentions `a` compares it with a number, in
a Boolean skeleton of `and`, `or` and `not`. A part that does not mention `a` may be
anything. -/
inductive DenseIn (h : Heading) (a : String) : Term → Prop
  | opq {e : Term} : a ∉ e.attrs → DenseIn h a e
  | and {es : List Term} : (∀ e ∈ es, DenseIn h a e) → DenseIn h a (.call "and" es)
  | or {es : List Term} : (∀ e ∈ es, DenseIn h a e) → DenseIn h a (.call "or" es)
  | not {e : Term} : DenseIn h a e → DenseIn h a (.call "not" [e])
  | cmp {op : String} {r : XRel} {l r' : Term} : XRel.ofOp op = some r →
      operand? h a l = true → operand? h a r' = true → DenseIn h a (.call op [l, r'])

/-! ## The class's leaves, for the shared normal form -/

/-- The leaves the class accepts, as `NF.In` sees them: a comparison of two operands, each
`x` or a number. -/
def CmpOk (h : Heading) (a : String) (op : String) (es : List Term) : Prop :=
  ∃ r l r', XRel.ofOp op = some r ∧ es = [l, r'] ∧ operand? h a l = true ∧ operand? h a r' = true

theorem XRel.ofOp_ne {op : String} {r : XRel} (hr : XRel.ofOp op = some r) :
    op ≠ "and" ∧ op ≠ "or" ∧ op ≠ "not" := by
  have := XRel.ofOp_some hr; subst this; cases r <;> simp [XRel.op]

theorem DenseIn.toIn {h : Heading} {a : String} :
    ∀ {e : Term}, DenseIn h a e → NF.In (CmpOk h a) a e := by
  intro e he
  induction he with
  | opq hna => exact .opq hna
  | and _ ih => exact .and ih
  | or _ ih => exact .or ih
  | not _ ih => exact .not ih
  | cmp hr hl hr' =>
    obtain ⟨h1, h2, h3⟩ := XRel.ofOp_ne hr
    exact .leaf h1 h2 h3 ⟨_, _, _, hr, rfl, hl, hr'⟩

theorem DenseIn.ofIn {h : Heading} {a : String} :
    ∀ {e : Term}, NF.In (CmpOk h a) a e → DenseIn h a e := by
  intro e he
  induction he with
  | opq hna => exact .opq hna
  | and _ ih => exact .and ih
  | or _ ih => exact .or ih
  | not _ ih => exact .not ih
  | leaf _ _ _ hA =>
    obtain ⟨r, l, r', hr, rfl, hl, hr'⟩ := hA
    exact .cmp hr hl hr'

theorem leaf_cmp {a : String} {p : Bool} {op : String} {r : XRel} {l r' : Term}
    (hr : XRel.ofOp op = some r) : leaf a p op [l, r'] = atom a p r l r' := by
  simp [leaf, hr]

/-- A comparison literal `x ⋈ τ` is true on `t` when `x` is `d`. -/
def XSem (t : Tuple) (d : Rat) (x : XRel × Term) : Prop := x.1.test d (qOf t x.2) = true

/-- What the normal form promises of a comparison literal: its other operand is a number,
and it reads only `R`. -/
def XGood (h : Heading) (a : String) (R : List String) (x : XRel × Term) : Prop :=
  numOperand? h a x.2 = true ∧ ∀ y ∈ x.2.attrs, y ∈ R

section NormalForm

variable {h : Heading} {a : String} {t : Tuple} {d : Rat}


/-- The value of each operand of a comparison, with `a` set to `d`. -/
theorem operand_value (ht : Tuple.Sorted t) (f : t.Fits (h.filter (·.1 ≠ a))) {o : Term}
    (ho : operand? h a o = true) :
    ∃ v, o.eval (t.set a (Value.ofRat d)) = .ok v ∧
      v.exact? = some (if isAttr a o then d else qOf t o) := by
  by_cases hi : isAttr a o = true
  · have e := isAttr_iff.mp hi
    subst e
    exact ⟨_, eval_attr_set ht a _, by simp [hi, Value.exact?_ofRat]⟩
  · have hn : numOperand? h a o = true := by simpa [operand?, hi] using ho
    obtain ⟨v, hv, hq⟩ := numOperand_eval hn f
    refine ⟨v, ?_, by simp [hi, hq]⟩
    rw [Term.eval_set_of_not_mem ht (not_mem_of_numOperand hn)]; exact hv

open NF in
/-- The class's leaf is right: a comparison that mentions `x`, under a sign, has a normal form
that means it. -/
theorem leaf_sem (ht : Tuple.Sorted t) (f : t.Fits (h.filter (·.1 ≠ a))) :
    ∀ {op : String} {es : List Term}, op ≠ "and" → op ≠ "or" → op ≠ "not" → CmpOk h a op es →
      a ∈ (Term.call op es).attrs → ∀ {R : List String}, (∀ x ∈ (Term.call op es).attrs, x ∈ R) →
      ∀ (p b : Bool), (Term.call op es).holds (t.set a (Value.ofRat d)) = .ok b →
      NF.DnfOk (XSem t d) (XGood h a) a t R p b (leaf a p op es) := by
  intro op es _ _ _ hA hc R hR p b hb
  obtain ⟨r, l, r', hr, rfl, hl, hr'⟩ := hA
  have hop := XRel.ofOp_some hr
  subst hop
  rw [leaf_cmp hr]
  obtain ⟨vl, hvl, hql⟩ := operand_value (d := d) ht f hl
  obtain ⟨vr, hvr, hqr⟩ := operand_value (d := d) ht f hr'
  have hbv := holds_cmp r hvl hql hvr hqr
  rw [hbv] at hb; cases hb
  have hRl : ∀ y ∈ l.attrs, y ∈ R := attrs_sub_call List.mem_cons_self hR
  have hRr : ∀ y ∈ r'.attrs, y ∈ R :=
    attrs_sub_call (List.mem_cons_of_mem _ List.mem_cons_self) hR
  unfold atom
  by_cases il : isAttr a l = true
  · by_cases ir : isAttr a r' = true
    · simp only [il, ir, ↓reduceIte]
      refine ⟨fun c hc l hl => by simp_all [NF.Lit.Good], ?_⟩
      simp only [List.mem_singleton, exists_eq_left, forall_eq, NF.Lit.Sem, XSem, XRel.test_refl,
        beq_iff_eq]
    · have hn : numOperand? h a r' = true := by simpa [operand?, ir] using hr'
      simp only [il, ir, ↓reduceIte, Bool.false_eq_true]
      refine ⟨fun c hc l hl => ?_, ?_⟩
      · obtain ⟨s', _, rfl⟩ := List.mem_map.mp hc
        simp only [List.mem_singleton] at hl; subst hl
        exact ⟨hn, hRr⟩
      · simp only [List.mem_map, NF.Lit.Sem, XSem, XSem]
        constructor
        · rintro ⟨_, ⟨s', hs, rfl⟩, hl⟩
          have := hl _ List.mem_cons_self
          simp only at this
          cases p
          · simp only [Bool.false_eq_true, ↓reduceIte] at hs
            exact (XRel.test_neg r d _).mp ⟨s', hs, this⟩
          · simp only [↓reduceIte, List.mem_singleton] at hs; subst hs; exact this
        · intro hp
          cases p
          · obtain ⟨s', hs, hst⟩ := (XRel.test_neg r d (qOf t r')).mpr hp
            exact ⟨_, ⟨s', by simpa using hs, rfl⟩, by simpa [NF.Lit.Sem, XSem, XSem] using hst⟩
          · exact ⟨_, ⟨r, by simp, rfl⟩, by simpa [NF.Lit.Sem, XSem, XSem] using hp⟩
  · have hn : numOperand? h a l = true := by simpa [operand?, il] using hl
    have ir : isAttr a r' = true := by
      cases ir : isAttr a r'
      case true => rfl
      exfalso
      have hn' : numOperand? h a r' = true := by simpa [operand?, ir] using hr'
      simp only [Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at hc
      rcases hc with hc | hc
      · exact not_mem_of_numOperand hn hc
      · exact not_mem_of_numOperand hn' hc
    simp only [il, ir, ↓reduceIte, Bool.false_eq_true]
    refine ⟨fun c hc l hl => ?_, ?_⟩
    · obtain ⟨s', _, rfl⟩ := List.mem_map.mp hc
      simp only [List.mem_singleton] at hl; subst hl
      exact ⟨hn, hRl⟩
    · simp only [List.mem_map, NF.Lit.Sem, XSem, XSem]
      constructor
      · rintro ⟨_, ⟨s', hs, rfl⟩, hl⟩
        have := hl _ List.mem_cons_self
        simp only [XRel.test_flip] at this
        cases p
        · simp only [Bool.false_eq_true, ↓reduceIte] at hs
          exact (XRel.test_neg r _ d).mp ⟨s', hs, this⟩
        · simp only [↓reduceIte, List.mem_singleton] at hs; subst hs; exact this
      · intro hp
        cases p
        · obtain ⟨s', hs, hst⟩ := (XRel.test_neg r (qOf t l) d).mpr hp
          exact ⟨_, ⟨s', by simpa using hs, rfl⟩, by simpa [NF.Lit.Sem, XSem, XSem, XRel.test_flip] using hst⟩
        · exact ⟨_, ⟨r, by simp, rfl⟩, by simpa [NF.Lit.Sem, XSem, XSem, XRel.test_flip] using hp⟩


/-! ## One conjunction: Fourier's step -/

/-- `τ` is an exact number on `t`. -/
def NumOn (t : Tuple) (τ : Term) : Prop := ∃ v, τ.eval t = .ok v ∧ v.exact? = some (qOf t τ)

theorem holds_xa (r : XRel) {τ₀ τ : Term} (h₀ : NumOn t τ₀) (h₁ : NumOn t τ) :
    (Term.call r.op [τ₀, τ]).holds t = .ok (r.test (qOf t τ₀) (qOf t τ)) := by
  obtain ⟨v₀, hv₀, hq₀⟩ := h₀
  obtain ⟨v₁, hv₁, hq₁⟩ := h₁
  exact holds_cmp r hv₀ hq₀ hv₁ hq₁

/-- A literal that does not mention `x` means the same for every `d`, and its term holds a
Boolean. -/
theorem mem_lows {xs : List (XRel × Term)} {τ : Term} {s : Bool} :
    (τ, s) ∈ lows xs ↔ (s = true ∧ (.gt, τ) ∈ xs) ∨ (s = false ∧ (.ge, τ) ∈ xs) := by
  simp only [lows, List.mem_filterMap]
  constructor
  · rintro ⟨⟨r, τ'⟩, hm, he⟩
    cases r <;> simp at he <;> obtain ⟨rfl, rfl⟩ := he <;> simp [hm]
  · rintro (⟨rfl, hm⟩ | ⟨rfl, hm⟩)
    · exact ⟨_, hm, rfl⟩
    · exact ⟨_, hm, rfl⟩

theorem mem_ups {xs : List (XRel × Term)} {τ : Term} {s : Bool} :
    (τ, s) ∈ ups xs ↔ (s = true ∧ (.lt, τ) ∈ xs) ∨ (s = false ∧ (.le, τ) ∈ xs) := by
  simp only [ups, List.mem_filterMap]
  constructor
  · rintro ⟨⟨r, τ'⟩, hm, he⟩
    cases r <;> simp at he <;> obtain ⟨rfl, rfl⟩ := he <;> simp [hm]
  · rintro (⟨rfl, hm⟩ | ⟨rfl, hm⟩)
    · exact ⟨_, hm, rfl⟩
    · exact ⟨_, hm, rfl⟩

theorem test_qltb (s : Bool) (q q' : Rat) :
    (if s then XRel.lt else XRel.le).test q q' = true ↔ qltb s q q' := by
  cases s <;> simp [XRel.test, qltb]

/-- Without an equality, the comparisons of `x` hold for some `d` exactly when each lower
bound is below each upper bound. -/
theorem fourier (Q : Term → Rat) (xs : List (XRel × Term)) (hne : ∀ p ∈ xs, p.1 ≠ .eq) :
    (∃ d, ∀ p ∈ xs, p.1.test d (Q p.2) = true) ↔
      ∀ l ∈ lows xs, ∀ u ∈ ups xs, qltb (l.2 || u.2) (Q l.1) (Q u.1) := by
  have split : ∀ d, (∀ p ∈ xs, p.1.test d (Q p.2) = true) ↔
      (∀ l ∈ lows xs, qltb l.2 (Q l.1) d) ∧ (∀ u ∈ ups xs, qltb u.2 d (Q u.1)) := by
    intro d
    constructor
    · intro hx
      refine ⟨fun ⟨τ, s⟩ hl => ?_, fun ⟨τ, s⟩ hu => ?_⟩
      · rcases mem_lows.mp hl with ⟨rfl, hm⟩ | ⟨rfl, hm⟩
        · simpa [XRel.test, qltb] using hx _ hm
        · simpa [XRel.test, qltb] using hx _ hm
      · rcases mem_ups.mp hu with ⟨rfl, hm⟩ | ⟨rfl, hm⟩
        · simpa [XRel.test, qltb] using hx _ hm
        · simpa [XRel.test, qltb] using hx _ hm
    · rintro ⟨hL, hU⟩ ⟨r, τ⟩ hm
      cases r
      · simpa [XRel.test, qltb] using hU (τ, true) (mem_ups.mpr (.inl ⟨rfl, hm⟩))
      · simpa [XRel.test, qltb] using hU (τ, false) (mem_ups.mpr (.inr ⟨rfl, hm⟩))
      · exact absurd rfl (hne _ hm)
      · simpa [XRel.test, qltb] using hL (τ, false) (mem_lows.mpr (.inr ⟨rfl, hm⟩))
      · simpa [XRel.test, qltb] using hL (τ, true) (mem_lows.mpr (.inl ⟨rfl, hm⟩))
  simp only [split]
  constructor
  · rintro ⟨d, hL, hU⟩ l hl u hu
    exact qltb_trans (hL l hl) (hU u hu)
  · intro hp
    obtain ⟨d, hL, hU⟩ := qinterval ((lows xs).map fun l => (Q l.1, l.2))
      ((ups xs).map fun u => (Q u.1, u.2)) (by
        simp only [List.mem_map]
        rintro _ ⟨l, hl, rfl⟩ _ ⟨u, hu, rfl⟩
        exact hp l hl u hu)
    exact ⟨d, fun l hl => hL _ (List.mem_map_of_mem hl), fun u hu => hU _ (List.mem_map_of_mem hu)⟩


theorem op_ltle (s : Bool) : (if s then "<" else "<=") = (if s then XRel.lt else XRel.le).op := by
  cases s <;> rfl

/-- Fourier's step on one `and`, for bounds that are exact numbers on `t` (shared with the
linear class, `Rasso.Linear`). -/
theorem xpart_sem_num {R : List String} {xs : List (XRel × Term)}
    (hx : ∀ p ∈ xs, NumOn t p.2 ∧ ∀ x ∈ p.2.attrs, x ∈ R) :
    (∀ e ∈ xpart xs, (∃ b, e.holds t = .ok b) ∧ ∀ x ∈ e.attrs, x ∈ R) ∧
      ((∀ e ∈ xpart xs, e.holds t = .ok true) ↔
        ∃ d, ∀ p ∈ xs, p.1.test d (qOf t p.2) = true) := by
  have attrs2 : ∀ {op : String} {τ₀ τ : Term}, (∀ x ∈ τ₀.attrs, x ∈ R) → (∀ x ∈ τ.attrs, x ∈ R) →
      ∀ x ∈ (Term.call op [τ₀, τ]).attrs, x ∈ R := by
    intro op τ₀ τ h₀ h₁ x hx'
    simp only [Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at hx'
    rcases hx' with hx' | hx'
    · exact h₀ x hx'
    · exact h₁ x hx'
  unfold xpart
  split
  · rename_i r₀ τ₀ hf
    have hm := List.mem_of_find?_eq_some hf
    have hr₀ : r₀ = .eq := by simpa using List.find?_some hf
    subst hr₀
    have h₀ := hx _ hm
    refine ⟨fun e he => ?_, ?_⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      exact ⟨⟨_, holds_xa p.1 h₀.1 (hx _ hp).1⟩, attrs2 h₀.2 (hx _ hp).2⟩
    · simp only [List.mem_map, forall_exists_index, and_imp]
      constructor
      · intro hall
        refine ⟨qOf t τ₀, fun p hp => ?_⟩
        have := hall _ p hp rfl
        rw [holds_xa p.1 h₀.1 (hx _ hp).1, Except.ok.injEq] at this
        exact this
      · rintro ⟨d, hd⟩ _ p hp rfl
        have hd₀ : d = qOf t τ₀ := by simpa [XRel.test] using hd _ hm
        subst hd₀
        rw [holds_xa p.1 h₀.1 (hx _ hp).1, hd _ hp]
  · rename_i hf
    have hne : ∀ p ∈ xs, p.1 ≠ .eq := fun p hp e => by
      have := List.find?_eq_none.mp hf p hp
      simp [e] at this
    have hlo : ∀ l ∈ lows xs, NumOn t l.1 ∧ ∀ x ∈ l.1.attrs, x ∈ R :=
      fun ⟨τ, s⟩ hl => by
        rcases mem_lows.mp hl with ⟨_, hm⟩ | ⟨_, hm⟩ <;> exact hx _ hm
    have hup : ∀ u ∈ ups xs, NumOn t u.1 ∧ ∀ x ∈ u.1.attrs, x ∈ R :=
      fun ⟨τ, s⟩ hu => by
        rcases mem_ups.mp hu with ⟨_, hm⟩ | ⟨_, hm⟩ <;> exact hx _ hm
    have hpair : ∀ l ∈ lows xs, ∀ u ∈ ups xs,
        (Term.call (if l.2 || u.2 then "<" else "<=") [l.1, u.1]).holds t =
          .ok ((if l.2 || u.2 then XRel.lt else XRel.le).test (qOf t l.1) (qOf t u.1)) :=
      fun l hl u hu => by rw [op_ltle]; exact holds_xa _ (hlo l hl).1 (hup u hu).1
    refine ⟨fun e he => ?_, ?_⟩
    · obtain ⟨l, hl, he⟩ := List.mem_flatMap.mp he
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
      exact ⟨⟨_, hpair l hl u hu⟩, attrs2 (hlo l hl).2 (hup u hu).2⟩
    · rw [fourier (qOf t) xs hne]
      constructor
      · intro hall l hl u hu
        have := hall _ (List.mem_flatMap.mpr ⟨l, hl, List.mem_map.mpr ⟨u, hu, rfl⟩⟩)
        rw [hpair l hl u hu, Except.ok.injEq, test_qltb] at this
        exact this
      · intro hall e he
        obtain ⟨l, hl, he⟩ := List.mem_flatMap.mp he
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
        rw [hpair l hl u hu, Except.ok.injEq, test_qltb]
        exact hall l hl u hu

theorem xpart_sem (f : t.Fits (h.filter (·.1 ≠ a))) {R : List String} {xs : List (XRel × Term)}
    (hx : ∀ p ∈ xs, numOperand? h a p.2 = true ∧ ∀ x ∈ p.2.attrs, x ∈ R) :
    (∀ e ∈ xpart xs, (∃ b, e.holds t = .ok b) ∧ ∀ x ∈ e.attrs, x ∈ R) ∧
      ((∀ e ∈ xpart xs, e.holds t = .ok true) ↔
        ∃ d, ∀ p ∈ xs, p.1.test d (qOf t p.2) = true) :=
  xpart_sem_num fun p hp => ⟨numOperand_eval (hx p hp).1 f, (hx p hp).2⟩

end NormalForm

/-! ## What the new term reads -/

open NF in
theorem leaf_attrs {h : Heading} {a : String} :
    ∀ {op : String} {es : List Term}, CmpOk h a op es → a ∈ (Term.call op es).attrs →
      ∀ (p : Bool), ∀ c ∈ leaf a p op es, ∀ l ∈ c, ∀ x ∈ l.attrs (fun y : XRel × Term => y.2.attrs),
        x ∈ (Term.call op es).attrs ∧ x ≠ a := by
  intro op es hA hca p c hc l hl x hx
  obtain ⟨r, l', r', hr, rfl, hl', hr'⟩ := hA
  rw [leaf_cmp hr] at hc
  have hmem : ∀ o, o = l' ∨ o = r' → isAttr a o = false → numOperand? h a o = true ∧
      ∀ y ∈ o.attrs, y ∈ (Term.call op [l', r']).attrs := by
    rintro o (rfl | rfl) hi
    · exact ⟨by simpa [operand?, hi] using hl', fun y hy => by simp [Term.attrs, hy]⟩
    · exact ⟨by simpa [operand?, hi] using hr', fun y hy => by simp [Term.attrs, hy]⟩
  by_cases il : isAttr a l' = true
  · by_cases ir : isAttr a r' = true
    · simp only [atom, il, ir, ↓reduceIte, List.mem_singleton] at hc; subst hc
      simp only [List.mem_singleton] at hl; subst hl
      simp [NF.Lit.attrs] at hx
    · simp only [atom, il, ir, ↓reduceIte, Bool.false_eq_true] at hc
      obtain ⟨s', _, rfl⟩ := List.mem_map.mp hc
      simp only [List.mem_singleton] at hl; subst hl
      have := hmem r' (.inr rfl) (by simpa using ir)
      exact ⟨this.2 x hx, fun e => not_mem_of_numOperand this.1 (e ▸ hx)⟩
  · simp only [atom, il, ↓reduceIte, Bool.false_eq_true] at hc
    obtain ⟨s', _, rfl⟩ := List.mem_map.mp hc
    simp only [List.mem_singleton] at hl; subst hl
    have := hmem l' (.inl rfl) (by simpa using il)
    exact ⟨this.2 x hx, fun e => not_mem_of_numOperand this.1 (e ▸ hx)⟩

/-- A term of `xpart` reads only what its comparisons read. -/
theorem xpart_attrs (xs : List (XRel × Term)) (e : Term) (he : e ∈ xpart xs) :
    ∀ x ∈ e.attrs, ∃ l ∈ xs, x ∈ l.2.attrs := by
  intro x hx
  unfold xpart at he
  split at he
  · rename_i r₀ τ₀ hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    simp only [Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at hx
    rcases hx with hx | hx
    · exact ⟨_, List.mem_of_find?_eq_some hf, hx⟩
    · exact ⟨p, hp, hx⟩
  · obtain ⟨lo, hlo, he⟩ := List.mem_flatMap.mp he
    obtain ⟨up, hup, rfl⟩ := List.mem_map.mp he
    simp only [Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at hx
    rcases hx with hx | hx
    · rcases mem_lows.mp hlo with ⟨_, hm⟩ | ⟨_, hm⟩ <;> exact ⟨_, hm, hx⟩
    · rcases mem_ups.mp hup with ⟨_, hm⟩ | ⟨_, hm⟩ <;> exact ⟨_, hm, hx⟩

/-! ## The class obligation -/

theorem rat_has {v : Value} (h : Kind.has .rat v = true) : ∃ q, v.exact? = some q := by
  cases v <;> simp_all [Kind.has, Value.exact?]

theorem rat_has_ofRat (q : Rat) : Kind.has .rat (Value.ofRat q) = true := by
  unfold Value.ofRat; split <;> rfl

/-- **Removal by dense order is sound.** With `a`'s domain the rat kind and every comparison
that mentions `a` a comparison with a number, the new term reads only the remaining
attributes, never refuses on a fitting tuple, and holds `t` exactly when some value of `a`
makes the old term hold. An instance of `NF.elim_sound`, with the rationals as the values of
`a`. -/
theorem elim_sound {u : Unrel} {a : String} (hd : u.heading.lookup a = some (.kind .rat))
    (hacc : DenseIn u.heading a u.term) (hu : u.WF) (tu : u.Total) :
    let w : Unrel := ⟨u.heading.filter (·.1 ≠ a), elim a u.term⟩
    (∀ x ∈ w.term.attrs, x ∈ w.heading.attrs) ∧ w.Total ∧
      ∀ t, t.Fits w.heading → (w.Holds t ↔ ∃ v, u.Holds (t.set a v)) :=
  NF.elim_sound (at' := fun y : XRel × Term => y.2.attrs) hd Value.ofRat
    (fun q => by simp [Domain.mem, rat_has_ofRat])
    (fun v hv => by
      obtain ⟨q, hq⟩ := rat_has (by simpa [Domain.mem] using hv)
      exact ⟨q, Value.eq_ofRat hq⟩)
    (0 : Rat) (fun t d => XSem t d) (fun _ => XGood u.heading a) hacc.toIn hu tu
    (fun _ f _ => leaf_sem f.sorted f) (fun _ f _ _ hx => xpart_sem f hx) leaf_attrs xpart_attrs

/-! ## The test decides the specification -/

theorem leafOk_sound {h : Heading} {a : String} {op : String} {es : List Term}
    (hok : leafOk h a op es = true) : CmpOk h a op es := by
  unfold leafOk at hok
  split at hok
  · rename_i r l r' hr
    simp only [Bool.and_eq_true] at hok
    exact ⟨r, l, r', hr, rfl, hok.1, hok.2⟩
  · cases hok

theorem leafOk_complete {h : Heading} {a : String} {op : String} {es : List Term}
    (hA : CmpOk h a op es) : leafOk h a op es = true := by
  obtain ⟨r, l, r', hr, rfl, hl, hr'⟩ := hA
  simp [leafOk, hr, hl, hr']

theorem accepts_iff {h : Heading} {a : String} {e : Term} : accepts? h a e = true ↔ DenseIn h a e :=
  ⟨fun hacc => DenseIn.ofIn (NF.accepts_sound (fun _ _ _ => leafOk_sound) e hacc),
   fun he => NF.accepts_complete leafOk_complete he.toIn⟩

end Dense

end Rasso
