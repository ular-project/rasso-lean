import Rasso.Phi.Sound.Term
import Rasso.WF

/-!
# φ's soundness: the kind check

An operator whose arguments have the kinds `opKinds` was given does not refuse, and its
value has one of the kinds `opKinds` found (`opKinds_sound`); so a term whose kinds
`termKinds` finds evaluates without refusal on every assignment of the cells within their
domains (`termKinds_sound`, which gives `KindsSound`).
-/

namespace Rasso.Phi

open Rasso

/-- The value has one of the kinds. -/
def KindOk (ks : List VK) (v : Value) : Prop := ∃ k, vkOf v = some k ∧ k ∈ ks

/-- Each value has one of the kinds at its position. -/
def Kinded : List Value → List (List VK) → Prop
  | [], [] => True
  | w :: ws, k :: ks => KindOk k w ∧ Kinded ws ks
  | _, _ => False

theorem Kinded.length : ∀ {ws : List Value} {ks : List (List VK)}, Kinded ws ks → ws.length = ks.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [Kinded.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Kinded.mem : ∀ {ws : List Value} {ks : List (List VK)}, Kinded ws ks →
    ∀ w ∈ ws, ∃ k0 ∈ ks, KindOk k0 w
  | [], [], _, _, hw => by simp at hw
  | w :: ws, k :: ks, h, v, hv => by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨k, by simp, h.1⟩
    · obtain ⟨k0, hk0, hok⟩ := Kinded.mem h.2 v hv
      exact ⟨k0, by simp [hk0], hok⟩
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

theorem Kinded.need {ws : List Value} {ks : List (List VK)} (h : Kinded ws ks) {allowed : List VK}
    (hn : (ks.all fun x => subKinds x allowed) = true) : ∀ w ∈ ws, KindOk allowed w := by
  intro w hw
  obtain ⟨k0, hk0, k, hk, hkk⟩ := h.mem w hw
  have := List.all_eq_true.mp hn k0 hk0
  simp only [subKinds, List.all_eq_true, List.contains_iff_mem] at this
  exact ⟨k, hk, this k hkk⟩

theorem Kinded.all {ws : List Value} {ks : List (List VK)} (h : Kinded ws ks) :
    ∀ w ∈ ws, KindOk ks.flatten.eraseDups w := by
  intro w hw
  obtain ⟨k0, hk0, k, hk, hkk⟩ := h.mem w hw
  exact ⟨k, hk, List.mem_eraseDups.mpr (List.mem_flatten.mpr ⟨k0, hk0, hkk⟩)⟩

/-! ## Values of given kinds -/

theorem asExact_ok {who : String} {w : Value} (h : KindOk numKinds w) : ∃ q, asExact who w = .ok q := by
  obtain ⟨k, hk, hm⟩ := h
  cases w <;> simp [vkOf] at hk <;> subst hk <;> simp [numKinds] at hm <;> simp [asExact]

theorem asBool_ok {w : Value} (h : KindOk [.bool] w) : ∃ b, w = .bool b := by
  obtain ⟨k, hk, hm⟩ := h
  cases w <;> simp [vkOf] at hk <;> subst hk <;> simp at hm
  exact ⟨_, rfl⟩

theorem asInt_ok {w : Value} (h : KindOk [.int] w) : ∃ n, w = .int n := by
  obtain ⟨k, hk, hm⟩ := h
  cases w <;> simp [vkOf] at hk <;> subst hk <;> simp at hm
  exact ⟨_, rfl⟩

theorem bools_of {ws : List Value} (h : ∀ w ∈ ws, KindOk [.bool] w) : ∃ bs : List Bool, ws = bs.map .bool := by
  induction ws with
  | nil => exact ⟨[], rfl⟩
  | cons w ws ih =>
    obtain ⟨b, rfl⟩ := asBool_ok (h w (by simp))
    obtain ⟨bs, rfl⟩ := ih (fun v hv => h v (by simp [hv]))
    exact ⟨b :: bs, rfl⟩

theorem mapM_asExact_ok {who : String} :
    ∀ {ws : List Value}, (∀ w ∈ ws, KindOk numKinds w) → ∃ qs, ws.mapM (asExact who) = .ok qs
  | [], _ => ⟨[], rfl⟩
  | w :: ws, h => by
    obtain ⟨q, hq⟩ := asExact_ok (who := who) (h w (by simp))
    obtain ⟨qs, hqs⟩ := mapM_asExact_ok (who := who) (ws := ws) (fun v hv => h v (by simp [hv]))
    exact ⟨q :: qs, by simp [List.mapM_cons, hq, hqs, bind, Except.bind, pure, Except.pure]⟩

theorem allInts_none {ws : List Value} (h : allInts ws = none) (hk : ∀ w ∈ ws, KindOk numKinds w) :
    ∃ w ∈ ws, vkOf w = some .rat := by
  induction ws with
  | nil => simp [allInts] at h
  | cons w ws ih =>
    obtain ⟨k, hk1, hk2⟩ := hk w (by simp)
    cases w with
    | int n =>
      have : allInts ws = none := by
        cases h' : allInts ws with
        | none => rfl
        | some a =>
          simp only [allInts] at h'
          simp [allInts, List.mapM_cons, h'] at h
      obtain ⟨v, hv, hv'⟩ := ih this (fun v hv => hk v (by simp [hv]))
      exact ⟨v, by simp [hv], hv'⟩
    | rat q hq => exact ⟨.rat q hq, by simp, rfl⟩
    | _ => simp [vkOf] at hk1 <;> subst hk1 <;> simp [numKinds] at hk2

theorem ofRat_kind (q : Rat) : KindOk numKinds (Value.ofRat q) := by
  unfold Value.ofRat; split <;> simp [KindOk, vkOf, numKinds]

/-- Arithmetic on exact numbers does not refuse; its value is an int, or a rat when some
operand is a rat. -/
theorem arith_ok (who : String) (onInt : List Int → Int) (onRat : List Rat → Rat) {ws : List Value}
    (hk : ∀ w ∈ ws, KindOk numKinds w) :
    ∃ v, arith who onInt onRat ws = .ok v ∧
      (KindOk [.int] v ∨ ((∃ w ∈ ws, vkOf w = some .rat) ∧ KindOk numKinds v)) := by
  unfold arith
  cases h : allInts ws with
  | some ns => exact ⟨.int (onInt ns), by simp [pure, Except.pure], Or.inl ⟨.int, rfl, by simp⟩⟩
  | none =>
    obtain ⟨qs, hqs⟩ := mapM_asExact_ok (who := who) hk
    refine ⟨Value.ofRat (onRat qs), by simp [hqs, bind, Except.bind, pure, Except.pure], Or.inr ⟨allInts_none h hk, ofRat_kind _⟩⟩

theorem arith_case {ws : List Value} {ks : List (List VK)} {rk : List VK} (hk : Kinded ws ks)
    (hn : ∀ x ∈ ks, subKinds x numKinds = true)
    (hrat : (∃ l, l ∈ ks ∧ VK.rat ∈ l) → VK.rat ∈ rk) (hint : VK.int ∈ rk)
    (who : String) (onInt : List Int → Int) (onRat : List Rat → Rat) :
    ∃ v, arith who onInt onRat ws = .ok v ∧ KindOk rk v := by
  obtain ⟨v, hv, hor⟩ := arith_ok who onInt onRat (hk.need (List.all_eq_true.mpr hn))
  refine ⟨v, hv, ?_⟩
  rcases hor with ⟨k, hk1, hk2⟩ | ⟨⟨w, hw, hwr⟩, k, hk1, hk2⟩
  · simp at hk2; subst hk2; exact ⟨.int, hk1, hint⟩
  · obtain ⟨k0, hk0, k', hk', hkk'⟩ := hk.mem w hw
    rw [hwr] at hk'; cases hk'
    have hr := hrat ⟨k0, hk0, hkk'⟩
    simp [numKinds] at hk2
    rcases hk2 with rfl | rfl
    · exact ⟨_, hk1, hint⟩
    · exact ⟨_, hk1, hr⟩

theorem foldl_pick_mem (g : Value → Value → Value) (hg : ∀ m w, g m w = w ∨ g m w = m) :
    ∀ (v : Value) (ws : List Value), ws.foldl g v ∈ v :: ws
  | v, [] => by simp
  | v, w :: ws => by
    simp only [List.foldl_cons]
    have := foldl_pick_mem g hg (g v w) ws
    rcases hg v w with h | h <;> rw [h] at this ⊢
    · exact List.mem_cons_of_mem _ this
    · rcases List.mem_cons.mp this with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem foldl_choose_mem (f : Value → Value → Bool) :
    ∀ (v : Value) (ws : List Value), ws.foldl (fun m w => if f w m then w else m) v ∈ v :: ws
  | v, [] => by simp
  | v, w :: ws => by
    simp only [List.foldl_cons]
    have := foldl_choose_mem f (if f w v then w else v) ws
    by_cases hf : f w v = true
    · simp only [hf, ite_true] at this ⊢
      exact List.mem_cons_of_mem _ this
    · simp only [hf, Bool.false_eq_true, ite_false] at this ⊢
      rcases List.mem_cons.mp this with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem ks_length {ws : List Value} {ks : List (List VK)} (hk : Kinded ws ks) {n : Nat}
    (h : ks.length = n) : ws.length = n := by rw [hk.length, h]

theorem KindOk.sub {k allowed : List VK} {v : Value} (h : KindOk k v) (hs : subKinds k allowed = true) :
    KindOk allowed v := by
  obtain ⟨k', h1, h2⟩ := h
  simp only [subKinds, List.all_eq_true, List.contains_iff_mem] at hs
  exact ⟨k', h1, hs k' h2⟩

theorem KindOk.mono {k k' : List VK} {v : Value} (h : KindOk k v) (hs : ∀ x ∈ k, x ∈ k') : KindOk k' v := by
  obtain ⟨x, h1, h2⟩ := h
  exact ⟨x, h1, hs x h2⟩

theorem notFloat {v : Value} {ks : List VK} (h : KindOk ks v) : v.isFloat = false := by
  obtain ⟨k, hk, _⟩ := h; cases v <;> simp [vkOf] at hk <;> rfl

theorem Kinded.two {v w : Value} {ks : List (List VK)} (hk : Kinded [v, w] ks) :
    ∃ k1 k2, KindOk k1 v ∧ KindOk k2 w := by
  match ks, hk with
  | [k1, k2], hk => exact ⟨k1, k2, hk.1, hk.2.1⟩

/-- An operator whose arguments have the kinds `opKinds` was given does not refuse, and its
value has one of the kinds `opKinds` found. -/
theorem opKinds_sound {op : String} {ks : List (List VK)} {ws : List Value} {rk : List VK}
    (hk : Kinded ws ks) (h : opKinds op ks = .ok rk) : ∃ v, applyOp op ws = .ok v ∧ KindOk rk v := by
  rw [opKinds.eq_def] at h
  split at h
  all_goals simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  · by_cases hn : ∀ x ∈ ks, subKinds x numKinds = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)] at h
      simp at h
      subst h
      simp only [applyOp]
      exact arith_case hk hn (fun hr => by split <;> simp_all) (by split <;> simp) _ _ _
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at h
      simp at h
  · by_cases hn : ∀ x ∈ ks, subKinds x numKinds = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)] at h
      simp at h
      subst h
      simp only [applyOp]
      exact arith_case hk hn (fun hr => by split <;> simp_all) (by split <;> simp) _ _ _
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at h
      simp at h
  · by_cases hn : ∀ x ∈ ks, subKinds x numKinds = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)] at h
      simp at h
      subst h
      simp only [applyOp]
      exact arith_case hk hn (fun hr => by split <;> simp_all) (by split <;> simp) _ _ _
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at h
      simp at h
  · -- "-"
    by_cases hl : 1 ≤ ks.length
    · by_cases hn : ∀ x ∈ ks, subKinds x numKinds = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h
        simp only at h
        rw [ite_eq_left_of_eq_true _ _ (eq_true hn)] at h
        simp at h
        subst h
        match ws, ks_length hk rfl with
        | [], h0 => simp at h0; omega
        | [w], _ =>
          simp only [applyOp]
          exact arith_case hk hn (fun hr => by split <;> simp_all) (by split <;> simp) _ _ _
        | w :: w' :: ws', _ =>
          simp only [applyOp]
          exact arith_case hk hn (fun hr => by split <;> simp_all) (by split <;> simp) _ _ _
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h
        simp only at h
        rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at h
        simp at h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h
      simp at h
  · -- "%"
    by_cases hl : ks.length = 2
    · by_cases hn : ∀ x ∈ ks, subKinds x [VK.int] = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp only at h
        rw [ite_eq_left_of_eq_true _ _ (eq_true hn)] at h; simp at h; subst h
        have hw := hk.need (List.all_eq_true.mpr hn)
        match ws, ks_length hk hl with
        | [v, w], _ =>
          obtain ⟨a, rfl⟩ := asInt_ok (hw v (by simp))
          obtain ⟨b, rfl⟩ := asInt_ok (hw w (by simp))
          exact ⟨.int (a % b), by simp [applyOp, asInt, bind, Except.bind, pure, Except.pure], .int, rfl, by simp⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp only at h
        rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at h; simp at h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h; simp at h
  · -- "abs"
    by_cases hl : ks.length = 1
    · by_cases hn : ∀ x ∈ ks, subKinds x [VK.int] = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp only at h
        rw [ite_eq_left_of_eq_true _ _ (eq_true hn)] at h; simp at h; subst h
        have hw := hk.need (List.all_eq_true.mpr hn)
        match ws, ks_length hk hl with
        | [v], _ =>
          obtain ⟨a, rfl⟩ := asInt_ok (hw v (by simp))
          exact ⟨.int a.natAbs, by simp [applyOp, asInt, bind, Except.bind, pure, Except.pure], .int, rfl, by simp⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp only at h
        rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at h; simp at h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h; simp at h
  · -- "min"
    by_cases hl : 1 ≤ ks.length
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp at h; subst h
      match ws, ks_length hk rfl with
      | [], h0 => simp at h0; omega
      | v :: ws', _ =>
        exact ⟨_, rfl, hk.all _ (foldl_pick_mem _ (fun m w => by split <;> simp) v ws')⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h; simp at h
  · -- "max"
    by_cases hl : 1 ≤ ks.length
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp at h; subst h
      match ws, ks_length hk rfl with
      | [], h0 => simp at h0; omega
      | v :: ws', _ =>
        exact ⟨_, rfl, hk.all _ (foldl_pick_mem _ (fun m w => by split <;> simp) v ws')⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h; simp at h
  · -- "all_different"
    subst h
    exact ⟨_, rfl, .bool, rfl, by simp⟩
  · -- "="
    by_cases hl : ks.length = 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp at h
      split at h
      · rename_i hs
        simp at h; subst h
        match ws, ks_length hk hl with
        | [v, w], _ =>
          match ks, hk with
          | [k1, k2], hk =>
            obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩, -⟩ := hk
            cases v <;> cases w <;> simp [vkOf] at ha hb <;> subst ha hb <;> first
              | exact ⟨_, rfl, .bool, rfl, by simp⟩
              | (exfalso; simp_all)
      · simp at h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h; simp at h
  · -- "<"
    by_cases hl : ks.length = 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp at h; subst h
      match ws, ks_length hk hl with
      | [v, w], _ =>
        obtain ⟨_, _, h1, h2⟩ := hk.two
        have f1 := notFloat h1
        have f2 := notFloat h2
        cases v <;> cases w <;> simp [Value.isFloat] at f1 f2 <;>
          exact ⟨_, rfl, .bool, rfl, by simp⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h; simp at h
  · -- "<="
    by_cases hl : ks.length = 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp at h; subst h
      match ws, ks_length hk hl with
      | [v, w], _ =>
        obtain ⟨_, _, h1, h2⟩ := hk.two
        have f1 := notFloat h1
        have f2 := notFloat h2
        cases v <;> cases w <;> simp [Value.isFloat] at f1 f2 <;>
          exact ⟨_, rfl, .bool, rfl, by simp⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h; simp at h
  · -- ">"
    by_cases hl : ks.length = 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp at h; subst h
      match ws, ks_length hk hl with
      | [v, w], _ =>
        obtain ⟨_, _, h1, h2⟩ := hk.two
        have f1 := notFloat h1
        have f2 := notFloat h2
        cases v <;> cases w <;> simp [Value.isFloat] at f1 f2 <;>
          exact ⟨_, rfl, .bool, rfl, by simp⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h; simp at h
  · -- ">="
    by_cases hl : ks.length = 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp at h; subst h
      match ws, ks_length hk hl with
      | [v, w], _ =>
        obtain ⟨_, _, h1, h2⟩ := hk.two
        have f1 := notFloat h1
        have f2 := notFloat h2
        cases v <;> cases w <;> simp [Value.isFloat] at f1 f2 <;>
          exact ⟨_, rfl, .bool, rfl, by simp⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h; simp at h
  · -- "and"
    by_cases hn : ∀ x ∈ ks, subKinds x [VK.bool] = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)] at h; simp at h; subst h
      obtain ⟨bs, rfl⟩ := bools_of (hk.need (List.all_eq_true.mpr hn))
      have := applyOp_andor_bools true bs
      simp only [opName] at this
      exact ⟨_, this, .bool, rfl, by simp⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at h; simp at h
  · -- "or"
    by_cases hn : ∀ x ∈ ks, subKinds x [VK.bool] = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)] at h; simp at h; subst h
      obtain ⟨bs, rfl⟩ := bools_of (hk.need (List.all_eq_true.mpr hn))
      have := applyOp_andor_bools false bs
      simp only [opName] at this
      exact ⟨_, this, .bool, rfl, by simp⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at h; simp at h
  · -- "not"
    by_cases hl : ks.length = 1
    · by_cases hn : ∀ x ∈ ks, subKinds x [VK.bool] = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp only at h
        rw [ite_eq_left_of_eq_true _ _ (eq_true hn)] at h; simp at h; subst h
        have hw := hk.need (List.all_eq_true.mpr hn)
        match ws, ks_length hk hl with
        | [v], _ =>
          obtain ⟨b, rfl⟩ := asBool_ok (hw v (by simp))
          exact ⟨.bool !b, by simp [applyOp, asBool, bind, Except.bind, pure, Except.pure], .bool, rfl, by simp⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h; simp only at h
        rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at h; simp at h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h; simp at h
  · -- "if"
    split at h
    · rename_i c a b
      split at h
      · rename_i hc
        cases h
        match ws, hk with
        | [cv, av, bv], hk =>
          obtain ⟨bc, rfl⟩ := asBool_ok (hk.1.sub hc)
          have ha : KindOk (a ++ b).eraseDups av := hk.2.1.mono (fun k hk => by simp [hk])
          have hb : KindOk (a ++ b).eraseDups bv := hk.2.2.1.mono (fun k hk => by simp [hk])
          refine ⟨if bc then av else bv, rfl, ?_⟩
          cases bc
          · exact hb
          · exact ha
      · cases h
    · cases h

/-! ## Terms -/

theorem kinded_of {x : Tuple} : ∀ {args : List Term} {kss : List (List VK)}, kss.length = args.length →
    (∀ i (hi : i < args.length) (hk : i < kss.length), ∃ v, args[i].eval x = .ok v ∧ KindOk kss[i] v) →
    ∃ ws, args.mapM (Term.eval x) = .ok ws ∧ Kinded ws kss
  | [], [], _, _ => ⟨[], rfl, trivial⟩
  | a :: as, k :: ks, hl, h => by
    obtain ⟨v, hv, hok⟩ := h 0 (by simp) (by simp)
    obtain ⟨ws, hws, hk⟩ := kinded_of (args := as) (kss := ks) (by simpa using hl)
      (fun i hi hk => h (i + 1) (by simpa using hi) (by simpa using hk))
    simp only [List.getElem_cons_zero] at hv hok
    exact ⟨v :: ws, by simp [List.mapM_cons, hv, hws, bind, Except.bind, pure, Except.pure], hok, hk⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem termKinds_sound {kinds : List (String × List VK)} {x : Tuple}
    (hx : ∀ c ks, kinds.lookup c = some ks → ∃ v, x.get? c = some v ∧ KindOk ks v) :
    ∀ (t : Term) {ks : List VK}, termKinds kinds t = .ok ks → ∃ v, t.eval x = .ok v ∧ KindOk ks v
  | .val v, ks, h => by
    rw [termKinds] at h
    split at h
    · rename_i k hk; cases h; exact ⟨v, by simp [Term.eval], k, hk, by simp⟩
    · cases h
  | .attr c, ks, h => by
    rw [termKinds] at h
    split at h
    · rename_i ks' hks; cases h
      obtain ⟨v, hv, hok⟩ := hx c _ hks
      exact ⟨v, by simp [Term.eval, Tuple.get?] at hv ⊢; simp [hv], hok⟩
    · cases h
  | .call op args, ks, h => by
    rw [termKinds] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i kss hkss
      -- each argument evaluates, with a kind
      have hl := mapM_ok_length hkss
      simp only [List.length_attach] at hl
      have hargs := kinded_of (x := x) hl (fun i hi hk => by
        have hg := mapM_ok_get hkss i (by simpa using hi)
        simp only [List.getElem_attach] at hg
        exact termKinds_sound hx args[i] hg)
      obtain ⟨ws, hws, hk⟩ := hargs
      obtain ⟨v, hv, hok⟩ := opKinds_sound hk h
      exact ⟨v, by simp [Term.eval, hws, bind, Except.bind, hv], hok⟩
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  have := List.sizeOf_lt_of_mem (List.getElem_mem hi); omega

/-! ## The cells' kinds -/

theorem mapM_vkOf_mem {v : Value} : ∀ {vs : List Value} {ks : List VK}, vs.mapM vkOf = some ks →
    v ∈ vs → ∃ k, vkOf v = some k ∧ k ∈ ks
  | [], _, _, hv => by simp at hv
  | w :: ws, ks, h, hv => by
    simp only [List.mapM_cons] at h
    cases hw : vkOf w with
    | none => simp [hw] at h
    | some k =>
      cases hws : ws.mapM vkOf with
      | none => simp [hw, hws] at h
      | some ks' =>
        simp [hw, hws] at h; subst h
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨k, hw, by simp⟩
        · obtain ⟨k', h1, h2⟩ := mapM_vkOf_mem hws hv
          exact ⟨k', h1, by simp [h2]⟩

/-- A value in a domain has one of the domain's kinds. -/
theorem domKinds_mem {d : Domain} {ks : List VK} {v : Value} (h : domKinds d = some ks)
    (hv : d.mem v = true) : KindOk ks v := by
  simp only [domKinds, bind, Option.bind] at h
  cases hd : d.values? with
  | none => simp [hd] at h
  | some vs =>
    simp only [hd] at h
    cases hm : vs.mapM vkOf with
    | none => simp [hm] at h
    | some ks' =>
      simp [hm, pure] at h; subst h
      obtain ⟨k, h1, h2⟩ := mapM_vkOf_mem hm (Domain.values?_sound hd hv)
      exact ⟨k, h1, List.mem_eraseDups.mpr h2⟩

theorem cellKinds_lookup : ∀ {cells : Heading} {kinds : List (String × List VK)},
    cellKinds cells = .ok kinds → ∀ {c ks}, kinds.lookup c = some ks →
      ∃ d, cells.lookup c = some d ∧ domKinds d = some ks
  | [], kinds, h, c, ks, hl => by
    simp [cellKinds, List.mapM_nil, pure, Except.pure] at h; subst h; simp at hl
  | (c', d) :: cells, kinds, h, c, ks, hl => by
    simp only [cellKinds, List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i p hp
      split at h
      · cases h
      · rename_i rest hrest
        cases h
        split at hp
        · rename_i ks0 hks0
          cases hp
          by_cases hc : c = c'
          · subst hc; simp at hl; subst hl; exact ⟨d, by simp, hks0⟩
          · have hne : (c == c') = false := by simpa using hc
            simp [List.lookup, hne] at hl ⊢
            exact cellKinds_lookup (cells := cells) hrest hl
        · cases hp

/-- Step 3's `KindsSound`, proved. -/
theorem kindsSound (cells : Heading) (kinds : List (String × List VK)) : KindsSound cells kinds := by
  intro hck t ks x ht hx
  have hx' : ∀ c ks, kinds.lookup c = some ks → ∃ v, x.get? c = some v ∧ KindOk ks v := by
    intro c ks hl
    obtain ⟨d, hd, hdk⟩ := cellKinds_lookup hck hl
    obtain ⟨v, hv, hm⟩ := hx c d hd
    exact ⟨v, hv, domKinds_mem hdk hm⟩
  exact termKinds_sound hx' t ht

end Rasso.Phi
