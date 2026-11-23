import Coddstheorem.Schema

/-!
# Codd's theorem for Rasso: attribute names for calculus variables

The calculus-to-algebra translation gives each variable `x` an attribute. A variable may
be any string (the fresh `%` names of `Coddstheorem.Fresh` among them), and an attribute must be a Rasso
name (`isAttribute`), so the attribute is an encoding: `enc x` is `v` followed by, for
each character, `_` and its character code in decimal (`x` becomes `v_120`). The
encoding is injective, and its names never clash with the copies `cpy i` (`c_0`, `c_1`,
…) that the output heading uses, which start with `c`.
-/

namespace Coddstheorem

open Rasso

/-- The character codes of a list of characters, each after a `_`. -/
def encL : List Char → List Char
  | [] => []
  | c :: cs => '_' :: (Nat.toDigits 10 c.toNat ++ encL cs)

/-- The attribute that stands for variable `x`. -/
def enc (x : String) : String := String.ofList ('v' :: encL x.toList)

/-- The attribute of the `i`-th output copy. -/
def cpy (i : Nat) : String := "c_" ++ toString i

theorem enc_toList (x : String) : (enc x).toList = 'v' :: encL x.toList := by simp [enc]

/-- `r` is empty or starts with `_`. -/
def HeadUs (r : List Char) : Prop := r = [] ∨ ∃ t, r = '_' :: t

theorem headUs_encL : ∀ cs, HeadUs (encL cs)
  | [] => Or.inl rfl
  | _ :: _ => Or.inr ⟨_, rfl⟩

theorem split_us : ∀ {p q r s : List Char}, '_' ∉ p → '_' ∉ q → HeadUs r → HeadUs s →
    p ++ r = q ++ s → p = q ∧ r = s
  | [], [], _, _, _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], d :: q, r, s, _, hq, hr, _, h => by
    rcases hr with rfl | ⟨t, rfl⟩
    · simp at h
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hq
  | c :: p, [], r, s, hp, _, _, hs, h => by
    rcases hs with rfl | ⟨t, rfl⟩
    · simp at h
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1.symm ▸ List.mem_cons_self) hp
  | c :: p, d :: q, r, s, hp, hq, hr, hs, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨e1, e2⟩ := split_us (fun m => hp (List.mem_cons_of_mem _ m))
      (fun m => hq (List.mem_cons_of_mem _ m)) hr hs h
    exact ⟨by rw [e1], e2⟩

theorem encL_inj : ∀ {a b : List Char}, encL a = encL b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encL] at h
  | _ :: _, [], h => by simp [encL] at h
  | c :: a, d :: b, h => by
    simp only [encL, List.cons.injEq, true_and] at h
    obtain ⟨e1, e2⟩ := split_us Nat.underscore_not_in_toDigits Nat.underscore_not_in_toDigits
      (headUs_encL a) (headUs_encL b) h
    have : c.toNat = d.toNat := by
      have := congrArg (Nat.ofDigitChars 10 · 0) e1
      simpa only [Nat.ofDigitChars_ten_toDigits] using this
    rw [Char.toNat_inj.mp this, encL_inj e2]

theorem enc_inj {x y : String} (h : enc x = enc y) : x = y := by
  have := congrArg String.toList h
  rw [enc_toList, enc_toList, List.cons.injEq] at this
  exact String.toList_inj.mp (encL_inj this.2)

theorem mem_encL : ∀ {cs : List Char} {c : Char}, c ∈ encL cs → c = '_' ∨ c.isDigit = true
  | [], _, h => by simp [encL] at h
  | d :: cs, c, h => by
    simp only [encL, List.mem_cons, List.mem_append] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Nat.isDigit_of_mem_toDigits (by decide) (by decide) h)
    · exact mem_encL h

theorem toNat_lt_of_isDigit {c : Char} (h : c.isDigit = true) : c.toNat < 128 := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  have h2 : c.val.toNat ≤ ('9' : Char).val.toNat := h.2
  exact Nat.lt_of_le_of_lt h2 (by decide)

theorem isAttribute_enc (x : String) : isAttribute (enc x) = true := by
  unfold isAttribute
  rw [enc_toList]
  simp only [Bool.and_eq_true, List.all_cons, List.all_eq_true]
  refine ⟨⟨by decide, fun c hc => ?_⟩, by decide, fun c hc => ?_⟩
  · rcases mem_encL hc with rfl | h
    · decide
    · simp [Char.isAlphanum, h]
  · rcases mem_encL hc with rfl | h
    · decide
    · simpa using toNat_lt_of_isDigit h

theorem enc_ne_cpy (x : String) (i : Nat) : enc x ≠ cpy i := by
  intro h
  have := congrArg String.toList h
  rw [enc_toList] at this
  simp [cpy] at this

theorem cpy_inj {i j : Nat} (h : cpy i = cpy j) : i = j := by
  have := congrArg String.toList h
  simp only [cpy, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr] at this
  have := congrArg (Nat.ofDigitChars 10 · 0) (List.append_cancel_left this)
  simpa only [Nat.ofDigitChars_ten_toDigits] using this

theorem isAttribute_cpy (i : Nat) : isAttribute (cpy i) = true := by
  unfold isAttribute
  have : (cpy i).toList = 'c' :: '_' :: Nat.toDigits 10 i := by
    simp [cpy, Nat.toString_eq_repr, Nat.toList_repr]
  rw [this]
  simp only [Bool.and_eq_true, List.all_cons, List.all_eq_true]
  have hd : ∀ c ∈ Nat.toDigits 10 i, c.isDigit = true := fun c hc =>
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  refine ⟨⟨by decide, by decide, fun c hc => by simp [Char.isAlphanum, hd c hc]⟩, by decide,
    by decide, fun c hc => by simpa using toNat_lt_of_isDigit (hd c hc)⟩

end Coddstheorem
