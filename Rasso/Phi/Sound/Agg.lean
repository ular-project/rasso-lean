import Rasso.Phi.Sound.Kinds

/-!
# φ's soundness: aggregates and `has_subset`

Over symbolic rows that instantiate (`RowInst`) to concrete tuples, what φ builds for `has_subset`
(`sHas`) and for an aggregate over guarded values (`sAgg`) evaluates, wherever it has a
value, to what the evaluator computes over the rows present.
-/

namespace Rasso.Phi

open Rasso

/-! ## `has_subset` -/

/-- The tuple matches every (attribute, value) pair (`has_subset`'s test, `Agg.eval`). -/
def matchesAll (u : Tuple) (ps : List (String × Value)) : Bool :=
  ps.all fun (a, v) => u.get? a == some v

theorem RowInst.some {x : Tuple} {row : SRow} {u : Tuple} (hu : RowInst x row u) {a : String} {t : Term}
    (h : row.lookup a = some t) : ∃ v, t.eval x = .ok v ∧ u.get? a = some v := by
  rcases hu a with ⟨h1, _⟩ | ⟨s, v, h1, h2, h3⟩
  · rw [h] at h1; cases h1
  · rw [h] at h1; cases h1; exact ⟨v, h2, h3⟩

theorem RowInst.none {x : Tuple} {row : SRow} {u : Tuple} (hu : RowInst x row u) {a : String}
    (h : row.lookup a = none) : u.get? a = none := by
  rcases hu a with ⟨_, h2⟩ | ⟨s, v, h1, _, _⟩
  · exact h2
  · rw [h] at h1; cases h1

/-- `=` that has a value is equality of values. -/
theorem eval_eq_call {x : Tuple} {t : Term} {v w : Value}
    (h : (Term.call "=" [t, .val v]).eval x = .ok w) : ∃ tv, t.eval x = .ok tv ∧ w = .bool (tv == v) := by
  obtain ⟨ws, hws, hap⟩ := eval_call_ok h
  simp only [List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure] at hws
  split at hws
  · cases hws
  · rename_i tv htv
    simp [Term.eval] at hws
    subst hws
    refine ⟨tv, htv, ?_⟩
    simp only [applyOp] at hap
    split at hap <;> first | (cases hap; rfl) | cases hap

theorem sHasConds_sound {ks : Kinds} {x : Tuple} {row : SRow} {u : Tuple} (hu : RowInst x row u) :
    ∀ (ps : List (String × Value)) {r : Option (List Term)}, sHasConds ks row ps = .ok r →
      match r with
      | none => matchesAll u ps = false
      | some cs => ∀ ws, cs.mapM (Term.eval x) = .ok ws →
          ∃ bs : List Bool, ws = bs.map .bool ∧ bs.all id = matchesAll u ps
  | [], r, h => by
    simp [sHasConds] at h; subst h
    intro ws hws; simp [List.mapM_nil, pure, Except.pure] at hws; subst hws
    exact ⟨[], rfl, by simp [matchesAll]⟩
  | (a, v) :: ps, r, h => by
    rw [sHasConds] at h
    split at h
    · rename_i w hw
      obtain ⟨v', hv', hg⟩ := hu.some hw
      simp [Term.eval] at hv'; subst hv'
      split at h
      · rename_i hne
        cases h
        simp [matchesAll, hg]
        intro heq; subst heq; simp at hne
      · rename_i heq
        have hwv : w = v := by simpa using heq
        subst hwv
        have := sHasConds_sound hu ps h
        cases r with
        | none => simpa [matchesAll, hg] using this
        | some cs => simpa [matchesAll, hg] using this
    · rename_i t _ hlk
      obtain ⟨tv, htv, hg⟩ := hu.some hlk
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i c hc
        have hc' := mk_eq hc; subst hc'
        split at h
        · cases h
        · rename_i r' hr'
          have ih := sHasConds_sound hu ps hr'
          cases r' with
          | none =>
            simp [pure, Except.pure] at h; subst h
            simp only [matchesAll, List.all_cons, Bool.and_eq_false_iff]
            exact Or.inr (by simpa [matchesAll] using ih)
          | some cs =>
            simp [pure, Except.pure] at h; subst h
            intro ws hws
            simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at hws
            split at hws
            · cases hws
            · rename_i wc hwc
              split at hws
              · cases hws
              · rename_i ws' hws'
                cases hws
                obtain ⟨tv', htv', rfl⟩ := eval_eq_call hwc
                rw [htv] at htv'; cases htv'
                obtain ⟨bs, rfl, hbs⟩ := ih ws' hws'
                refine ⟨(tv == v) :: bs, rfl, ?_⟩
                simp [matchesAll, hg] at hbs ⊢
                rw [hbs]
    · rename_i hn
      cases h
      simp [matchesAll, hu.none hn]

/-- Each symbolic row instantiates to the tuple at its position. -/
def RowsInst (x : Tuple) : List SRow → List Tuple → Prop
  | [], [] => True
  | r :: rs, u :: us => RowInst x r u ∧ RowsInst x rs us
  | _, _ => False

theorem eval_and_ok {x : Tuple} {cs : List Term} {w : Value}
    (h : (Term.call "and" cs).eval x = .ok w) :
    ∃ ws, ∃ bs : List Bool, cs.mapM (Term.eval x) = .ok ws ∧ ws = bs.map .bool ∧ w = .bool (bs.all id) := by
  obtain ⟨ws, hws, hap⟩ := eval_call_ok h
  obtain ⟨bs, rfl, rfl⟩ := applyOp_andor (isAnd := true) (by simpa [opName] using hap)
  exact ⟨_, bs, hws, rfl, by simp [boolSem]⟩

theorem eval_or_ok {x : Tuple} {cs : List Term} {w : Value}
    (h : (Term.call "or" cs).eval x = .ok w) :
    ∃ ws, ∃ bs : List Bool, cs.mapM (Term.eval x) = .ok ws ∧ ws = bs.map .bool ∧ w = .bool (bs.any id) := by
  obtain ⟨ws, hws, hap⟩ := eval_call_ok h
  obtain ⟨bs, rfl, rfl⟩ := applyOp_andor (isAnd := false) (by simpa [opName] using hap)
  exact ⟨_, bs, hws, rfl, by simp [boolSem]⟩

theorem map_bool_inj {bs cs : List Bool} (h : bs.map Value.bool = cs.map Value.bool) : bs = cs := by
  induction bs generalizing cs with
  | nil => cases cs with
    | nil => rfl
    | cons _ _ => simp at h
  | cons b bs ih => cases cs with
    | nil => simp at h
    | cons c cs =>
      simp only [List.map_cons, List.cons.injEq, Value.bool.injEq] at h
      rw [h.1, ih h.2]

theorem sHasAlts_sound {ks : Kinds} {x : Tuple} {ps : List (String × Value)} :
    ∀ {rows : List SRow} {us : List Tuple} {alts : List Term}, RowsInst x rows us →
      sHasAlts ks ps rows = .ok alts → ∀ ws, alts.mapM (Term.eval x) = .ok ws →
        ∃ bs : List Bool, ws = bs.map .bool ∧ bs.any id = us.any (matchesAll · ps)
  | [], [], alts, _, h, ws, hws => by
    simp [sHasAlts] at h; subst h
    simp [List.mapM_nil, pure, Except.pure] at hws; subst hws
    exact ⟨[], rfl, by simp⟩
  | row :: rows, u :: us, alts, hus, h, ws, hws => by
    rw [sHasAlts] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      have hc := sHasConds_sound hus.1 ps hr
      cases r with
      | none =>
        obtain ⟨bs, h1, h2⟩ := sHasAlts_sound hus.2 h ws hws
        exact ⟨bs, h1, by simp [h2, hc]⟩
      | some cs =>
        simp only at h
        split at h
        · cases h
        · rename_i a ha
          split at h
          · cases h
          · rename_i rest hrest
            simp [pure, Except.pure] at h; subst h
            have ha' := mk_eq ha; subst ha'
            simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at hws
            split at hws
            · cases hws
            · rename_i wa hwa
              split at hws
              · cases hws
              · rename_i ws' hws'
                cases hws
                obtain ⟨cws, cbs, hcws, rfl, rfl⟩ := eval_and_ok hwa
                obtain ⟨bs', h1, h2⟩ := hc _ hcws
                have := map_bool_inj h1; subst this
                obtain ⟨bs, rfl, h3⟩ := sHasAlts_sound hus.2 hrest ws' hws'
                exact ⟨cbs.all id :: bs, rfl, by simp [h2, h3]⟩
  | [], _ :: _, _, hus, _, _, _ => hus.elim
  | _ :: _, [], _, hus, _, _, _ => hus.elim

/-- `has_subset`'s term, wherever it has a value, says whether some instantiated row matches
every pair. -/
theorem sHas_sound {ks : Kinds} {x : Tuple} {rows : List SRow} {us : List Tuple}
    {ps : List (String × Value)} {s : Term} {w : Value} (hus : RowsInst x rows us)
    (h : sHas ks rows ps = .ok s) (hw : s.eval x = .ok w) :
    w = .bool (us.any (matchesAll · ps)) := by
  simp only [sHas, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i alts halts
    have := mk_eq h; subst this
    obtain ⟨ws, bs, hws, rfl, rfl⟩ := eval_or_ok hw
    obtain ⟨bs', h1, h2⟩ := sHasAlts_sound hus halts _ hws
    have := map_bool_inj h1; subst this
    rw [h2]

/-! ## Aggregates over guarded values -/

/-- Pointwise relation between two lists. -/
inductive Pw {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Pw R [] []
  | cons {a b l m} : R a b → Pw R l m → Pw R (a :: l) (b :: m)

theorem Pw.eq_map {α β : Type} {F : α → β} : ∀ {l : List α} {m : List β}, Pw (fun a b => b = F a) l m → m = l.map F
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hl => by rw [h, Pw.eq_map hl]; rfl

theorem Pw.imp {α β : Type} {R S : α → β → Prop} (hrs : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {m : List β}, Pw R l m → Pw S l m
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hl => .cons (hrs _ _ h) (Pw.imp hrs hl)

theorem Pw.map_right {α β γ : Type} {R : α → γ → Prop} {F : β → γ} :
    ∀ {l : List α} {m : List β}, Pw R l (m.map F) → Pw (fun a b => R a (F b)) l m
  | [], [], _ => .nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons] at h
    cases h with | cons h hl => exact .cons h (Pw.map_right hl)

/-- `mapM` of a function building terms, then their values: each value is related to its
source by whatever every built term's value is. -/
theorem mapM_terms {α : Type} {x : Tuple} {f : α → Except String Term} {P : α → Value → Prop}
    (hp : ∀ a t w, f a = .ok t → t.eval x = .ok w → P a w) :
    ∀ {l : List α} {ts : List Term} {ws : List Value}, l.mapM f = .ok ts →
      ts.mapM (Term.eval x) = .ok ws → Pw P l ws
  | [], ts, ws, h, hws => by
    simp [List.mapM_nil, pure, Except.pure] at h; subst h
    simp [List.mapM_nil, pure, Except.pure] at hws; subst hws; exact .nil
  | a :: l, ts, ws, h, hws => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i t ht
      split at h
      · cases h
      · rename_i ts' hts'
        cases h
        simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at hws
        split at hws
        · cases hws
        · rename_i w hw
          split at hws
          · cases hws
          · rename_i ws' hws'
            cases hws
            exact .cons (hp a t w ht hw) (mapM_terms hp hts' hws')

theorem isTrue_eval {g : Term} (h : isTrue g = true) (x : Tuple) : g.eval x = .ok (.bool true) := by
  cases g with
  | val v => cases v with
    | bool b => cases b <;> simp_all [isTrue, Term.eval]
    | _ => simp [isTrue] at h
  | _ => simp [isTrue] at h

/-- The values present: those whose guard is true. -/
def present (vals : List (Value × Bool)) : List Value :=
  vals.filterMap fun (v, g) => if g then some v else none

/-- Each (value term, guard term) evaluates to its (value, guard). -/
def PairInst (x : Tuple) (p : Term × Term) (q : Value × Bool) : Prop :=
  p.1.eval x = .ok q.1 ∧ p.2.eval x = .ok (.bool q.2)

theorem eval_if {x : Tuple} {g v z : Term} {w : Value} {gb : Bool} {vv zv : Value}
    (hg : g.eval x = .ok (.bool gb)) (hv : v.eval x = .ok vv) (hz : z.eval x = .ok zv)
    (h : (Term.call "if" [g, v, z]).eval x = .ok w) : w = if gb then vv else zv := by
  rw [eval_call] at h
  simp [List.mapM_cons, hg, hv, hz, bind, Except.bind, pure, Except.pure, applyOp, asBool] at h
  exact h.symm

theorem Pw.combine {α β γ : Type} {R : α → β → Prop} {S : α → γ → Prop} {T : γ → β → Prop}
    (h : ∀ a b c, R a b → S a c → T c b) :
    ∀ {l : List α} {m : List β} {n : List γ}, Pw R l m → Pw S l n → Pw T n m
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h1 hl, .cons h2 hn => .cons (h _ _ _ h1 h2) (Pw.combine h hl hn)

/-! ### Padding with zeros -/

def pad0 (q : Value × Bool) : Value := if q.2 then q.1 else .int 0

theorem allInts_cons {v : Value} {vs : List Value} :
    allInts (v :: vs) = (match v with | .int n => (allInts vs).map (n :: ·) | _ => none) := by
  unfold allInts
  cases v <;> simp only [List.mapM_cons] <;>
    first | rfl | (cases List.mapM (m := Option) (fun | Value.int n => some n | _ => none) vs <;> rfl)

theorem allInts_pad : ∀ (vals : List (Value × Bool)) {ns : List Int}, allInts (vals.map pad0) = some ns →
    ∃ ns', allInts (present vals) = some ns' ∧ ∀ c : Int, ns.foldl (· + ·) c = ns'.foldl (· + ·) c
  | [], ns, h => by simp [allInts, List.mapM_nil] at h; subst h; exact ⟨[], rfl, fun _ => rfl⟩
  | (v, g) :: vals, ns, h => by
    rw [List.map_cons, allInts_cons] at h
    cases g with
    | false =>
      simp only [pad0, Bool.false_eq_true, ite_false] at h
      cases h' : allInts (vals.map pad0) with
      | none => simp [h'] at h
      | some ns0 =>
        simp [h'] at h; subst h
        obtain ⟨ns', h1, h2⟩ := allInts_pad vals h'
        exact ⟨ns', by simpa [present] using h1, fun c => by simp [h2]⟩
    | true =>
      simp only [pad0, ite_true] at h
      cases v with
      | int n =>
        cases h' : allInts (vals.map pad0) with
        | none => simp [h'] at h
        | some ns0 =>
          simp [h'] at h; subst h
          obtain ⟨ns', h1, h2⟩ := allInts_pad vals h'
          refine ⟨n :: ns', ?_, fun c => by simp [h2]⟩
          simp only [present, List.filterMap_cons, ite_true]
          rw [allInts_cons]; simp only [present] at h1; simp [h1]
      | _ => simp at h

theorem allInts_pad_none : ∀ (vals : List (Value × Bool)), allInts (vals.map pad0) = none →
    allInts (present vals) = none
  | [], h => by simp [allInts] at h
  | (v, g) :: vals, h => by
    rw [List.map_cons, allInts_cons] at h
    cases g with
    | false =>
      simp only [pad0, Bool.false_eq_true, ite_false] at h
      have : allInts (vals.map pad0) = none := by
        cases h' : allInts (vals.map pad0) with
        | none => rfl
        | some _ => simp [h'] at h
      simpa [present] using allInts_pad_none vals this
    | true =>
      simp only [pad0, ite_true] at h
      simp only [present, List.filterMap_cons, ite_true]
      rw [allInts_cons]
      cases v with
      | int n =>
        have : allInts (vals.map pad0) = none := by
          cases h' : allInts (vals.map pad0) with
          | none => rfl
          | some _ => simp [h'] at h
        have := allInts_pad_none vals this
        simp only [present] at this; simp [this]
      | _ => rfl

theorem mapM_asExact_pad {who : String} : ∀ (vals : List (Value × Bool)) {qs : List Rat},
    (vals.map pad0).mapM (asExact who) = .ok qs →
    ∃ qs', (present vals).mapM (asExact who) = .ok qs' ∧ ∀ c : Rat, qs.foldl (· + ·) c = qs'.foldl (· + ·) c
  | [], qs, h => by
    simp [List.mapM_nil, pure, Except.pure] at h; subst h; exact ⟨[], rfl, fun _ => rfl⟩
  | (v, g) :: vals, qs, h => by
    simp only [List.map_cons, List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i q hq
      split at h
      · cases h
      · rename_i qs0 hqs0
        cases h
        obtain ⟨qs', h1, h2⟩ := mapM_asExact_pad vals hqs0
        cases g with
        | false =>
          simp [pad0, asExact] at hq; subst hq
          exact ⟨qs', by simpa [present] using h1, fun c => by simp [h2, Rat.add_zero]⟩
        | true =>
          simp only [pad0, ite_true] at hq
          refine ⟨q :: qs', ?_, fun c => by simp [h2]⟩
          simp only [present, List.filterMap_cons, ite_true, List.mapM_cons, hq, bind, Except.bind, pure, Except.pure]
          simp only [present] at h1; rw [h1]

/-- A `sum` padded with zeros where the guard is false is the `sum` of the values present. -/
theorem arith_sum_pad (who : String) (vals : List (Value × Bool)) {w : Value}
    (h : arith who (·.foldl (· + ·) 0) (·.foldl (· + ·) 0) (vals.map pad0) = .ok w) :
    arith who (·.foldl (· + ·) 0) (·.foldl (· + ·) 0) (present vals) = .ok w := by
  unfold arith at h ⊢
  cases h1 : allInts (vals.map pad0) with
  | some ns =>
    obtain ⟨ns', h2, h3⟩ := allInts_pad vals h1
    simp [h1, h2, pure, Except.pure] at h ⊢; rw [← h, h3]
  | none =>
    rw [allInts_pad_none vals h1]
    simp only [h1, bind, Except.bind, pure, Except.pure] at h ⊢
    split at h
    · cases h
    · rename_i qs hqs
      obtain ⟨qs', h2, h3⟩ := mapM_asExact_pad vals hqs
      rw [h2]; simp only; rw [← h3]; exact h

/-! ### The pieces of `sAgg` -/

theorem Pw.length {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {m : List β}, Pw R l m → l.length = m.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ hl => by simp [Pw.length hl]

theorem Pw.split {x : Tuple} : ∀ {vs gs : List Term} {vals : List (Value × Bool)}, vs.length = gs.length →
    Pw (PairInst x) (vs.zip gs) vals →
    Pw (fun v vv => Term.eval x v = .ok vv) vs (vals.map (·.1)) ∧
    Pw (fun g gb => Term.eval x g = .ok (.bool gb)) gs (vals.map (·.2))
  | [], [], [], _, .nil => ⟨.nil, .nil⟩
  | v :: vs, g :: gs, q :: vals, hl, .cons h hp => by
    obtain ⟨h1, h2⟩ := Pw.split (by simpa using hl) hp
    exact ⟨.cons h.1 h1, .cons h.2 h2⟩
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | [], [], _ :: _, _, hp => by cases hp
  | _ :: _, _ :: _, [], _, hp => by cases hp

theorem Pw.forall_mem {α β : Type} {R : α → β → Prop} {P : α → Prop} {Q : β → Prop}
    (h : ∀ a b, R a b → P a → Q b) : ∀ {l : List α} {m : List β}, Pw R l m → (∀ a ∈ l, P a) → ∀ b ∈ m, Q b
  | [], [], .nil, _ => by simp
  | _ :: _, _ :: _, .cons hr hl, hp => by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h _ _ hr (hp _ (by simp))
    · exact Pw.forall_mem h hl (fun a ha => hp a (by simp [ha])) b hb

theorem present_all (vals : List (Value × Bool)) (h : ∀ q ∈ vals, q.2 = true) :
    present vals = vals.map (·.1) := by
  induction vals with
  | nil => rfl
  | cons q vals ih =>
    have hq := h q (by simp)
    simp only [present, List.filterMap_cons, hq, ite_true, List.map_cons]
    simp only [present] at ih; rw [ih (fun r hr => h r (by simp [hr]))]

theorem allInts_ints (ns : List Int) : allInts (ns.map .int) = some ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih => rw [List.map_cons, allInts_cons]; simp [ih]

theorem count_fold : ∀ (vals : List (Value × Bool)) (c : Int),
    (vals.map fun q => if q.2 then (1 : Int) else 0).foldl (· + ·) c = c + (present vals).length
  | [], c => by simp [present]
  | (v, g) :: vals, c => by
    have ih := count_fold vals
    cases g
    · simp only [List.map_cons, List.foldl_cons, present, List.filterMap_cons, Bool.false_eq_true, ite_false]
      simp only [present] at ih; rw [ih]; omega
    · simp only [List.map_cons, List.foldl_cons, present, List.filterMap_cons, ite_true, List.length_cons]
      simp only [present] at ih; rw [ih]; omega

theorem gsAll {x : Tuple} {gs : List Term} {gbs : List Bool}
    (hg : Pw (fun g gb => Term.eval x g = .ok (.bool gb)) gs gbs) (h : gs.all isTrue = true) :
    ∀ gb ∈ gbs, gb = true := by
  refine Pw.forall_mem (P := fun g => isTrue g = true) (fun g gb hgb ht => ?_) hg
    (fun g hg => List.all_eq_true.mp h g hg)
  rw [isTrue_eval ht x] at hgb; cases hgb; rfl

theorem vals_all {vals : List (Value × Bool)} (h : ∀ gb ∈ vals.map (·.2), gb = true) :
    ∀ q ∈ vals, q.2 = true := fun q hq => h q.2 (List.mem_map.mpr ⟨q, hq, rfl⟩)

theorem map_fst_eq {x : Tuple} {vs : List Term} {vvs : List Value}
    (hv : Pw (fun v vv => Term.eval x v = .ok vv) vs vvs) : vs.mapM (Term.eval x) = .ok vvs := by
  induction hv with
  | nil => rfl
  | cons h _ ih => simp [List.mapM_cons, h, ih, bind, Except.bind, pure, Except.pure]

theorem bool_and_vals : ∀ {vals : List (Value × Bool)} {bs : List Bool},
    Pw (fun q b' => ∃ b, q.1 = .bool b ∧ b' = (!q.2 || b)) vals bs →
    ∃ cs, (present vals).mapM (asBool "bool_and") = .ok cs ∧ cs.all id = bs.all id
  | [], [], .nil => ⟨[], rfl, rfl⟩
  | (v, g) :: vals, b' :: bs, .cons ⟨b, h1, h2⟩ hl => by
    obtain ⟨cs, hcs, hall⟩ := bool_and_vals hl
    simp only at h1 h2; subst h1; subst h2
    cases g
    · exact ⟨cs, by simpa [present] using hcs, by simp [hall]⟩
    · refine ⟨b :: cs, ?_, by simp [hall]⟩
      simp only [present, List.filterMap_cons, ite_true, List.mapM_cons, asBool, bind, Except.bind, pure, Except.pure]
      simp only [present] at hcs; rw [hcs]

theorem bool_or_vals : ∀ {vals : List (Value × Bool)} {bs : List Bool},
    Pw (fun q b' => ∃ b, q.1 = .bool b ∧ b' = (q.2 && b)) vals bs →
    ∃ cs, (present vals).mapM (asBool "bool_or") = .ok cs ∧ cs.any id = bs.any id
  | [], [], .nil => ⟨[], rfl, rfl⟩
  | (v, g) :: vals, b' :: bs, .cons ⟨b, h1, h2⟩ hl => by
    obtain ⟨cs, hcs, hany⟩ := bool_or_vals hl
    simp only at h1 h2; subst h1; subst h2
    cases g
    · exact ⟨cs, by simpa [present] using hcs, by simp [hany]⟩
    · refine ⟨b :: cs, ?_, by simp [hany]⟩
      simp only [present, List.filterMap_cons, ite_true, List.mapM_cons, asBool, bind, Except.bind, pure, Except.pure]
      simp only [present] at hcs; rw [hcs]

/-- An aggregate over guarded values, as φ builds it, evaluates wherever it has a value to
the evaluator's aggregate over the values whose guard is true. -/
theorem sAgg_sound {ks : Kinds} {op : String} {vs gs : List Term} {s : Term} {x : Tuple}
    {vals : List (Value × Bool)} {w : Value} (hlen : vs.length = gs.length)
    (hp : Pw (PairInst x) (vs.zip gs) vals) (h : sAgg ks op vs gs = .ok s) (hw : s.eval x = .ok w) :
    aggregate op (present vals) = .ok w := by
  obtain ⟨hv, hg⟩ := Pw.split hlen hp
  unfold sAgg at h
  split at h
  · -- count
    rename_i hop
    simp only at h
    split at h
    · rename_i hall
      simp [pure, Except.pure] at h; subst h
      simp [Term.eval] at hw; subst hw
      rw [present_all vals (vals_all (gsAll hg hall))]
      have := hv.length
      simp [aggregate, hop, pure, Except.pure, this]
    · simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i ts hts
        have := mk_eq h; subst this
        obtain ⟨ws, hws, hap⟩ := eval_call_ok hw
        have hpw := mapM_terms (P := fun g w => ∀ gb, Term.eval x g = .ok (.bool gb) →
            w = .int (if gb then 1 else 0)) (fun g t w ht htw gb hgb => by
              try simp only at ht
              split at ht
              · rename_i hT
                cases ht; rw [isTrue_eval hT x] at hgb; cases hgb
                simp [Term.eval] at htw; simp [htw]
              · have := mk_eq ht; subst this
                rw [eval_if (vv := .int 1) (zv := .int 0) hgb (by simp [Term.eval]) (by simp [Term.eval]) htw]
                cases gb <;> rfl) hts hws
        have hws' := Pw.eq_map (F := fun gb => Value.int (if gb then 1 else 0))
          (Pw.combine (fun g w gb h1 h2 => h1 gb h2) hpw hg)
        subst hws'
        rw [List.map_map] at hap
        have hm : (vals.map ((fun gb => Value.int (if gb then 1 else 0)) ∘ (·.2))) =
            (vals.map fun q => if q.2 then (1 : Int) else 0).map Value.int := by
          simp [List.map_map, Function.comp_def]
        rw [hm] at hap
        simp only [applyOp, arith, allInts_ints, pure, Except.pure] at hap
        cases hap
        simp [aggregate, hop, pure, Except.pure, count_fold]
  · -- sum
    rename_i hop
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i ts hts
      have := mk_eq h; subst this
      obtain ⟨ws, hws, hap⟩ := eval_call_ok hw
      have hpw := mapM_terms (P := fun p w => ∀ q, PairInst x p q → w = pad0 q) (fun p t w ht htw q hq => by
          obtain ⟨v, g⟩ := p
          obtain ⟨q1, q2⟩ := q
          obtain ⟨h1, h2⟩ := hq
          try simp only at ht h1 h2
          split at ht
          · rename_i hT
            cases ht; rw [isTrue_eval hT x] at h2; cases h2
            rw [h1] at htw; cases htw; simp [pad0]
          · have := mk_eq ht; subst this
            rw [eval_if (zv := .int 0) h2 h1 (by simp [Term.eval]) htw]; rfl) hts hws
      have hws' := Pw.eq_map (Pw.combine (fun p w q h1 h2 => h1 q h2) hpw hp)
      subst hws'
      simp only [applyOp] at hap
      have := arith_sum_pad "sum" vals hap
      simp [aggregate, hop, this]
  · -- bool_and
    rename_i hop
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i ts hts
      have := mk_eq h; subst this
      obtain ⟨ws, bs, hws, rfl, rfl⟩ := eval_and_ok hw
      have hpw := mapM_terms (P := fun p w => ∀ q, PairInst x p q → ∀ b', w = .bool b' →
          ∃ b, q.1 = .bool b ∧ b' = (!q.2 || b)) (fun p t w ht htw q hq b' hb' => by
          obtain ⟨v, g⟩ := p
          obtain ⟨q1, q2⟩ := q
          obtain ⟨h1, h2⟩ := hq
          try simp only at ht h1 h2 ⊢
          subst hb'
          split at ht
          · rename_i hT
            cases ht
            rw [isTrue_eval hT x] at h2; cases h2
            rw [h1] at htw; cases htw; exact ⟨b', rfl, by simp⟩
          · try simp only [bind, Except.bind] at ht
            split at ht
            · cases ht
            · rename_i n hn
              have := mk_eq hn; subst this
              have := mk_eq ht; subst this
              obtain ⟨_, bs2, hws2, rfl, hw2⟩ := eval_or_ok htw
              simp [List.mapM_cons, eval_call, h2, h1, bind, Except.bind, pure, Except.pure, applyOp, asBool] at hws2
              match bs2, hws2 with
              | [c1, c2], hws2 =>
                simp at hws2
                obtain ⟨hc1, hc2⟩ := hws2
                cases hw2
                exact ⟨c2, hc2, by simp [hc1]⟩) hts hws
      have hpw2 := Pw.combine (T := fun q (w : Value) => ∀ b', w = .bool b' → ∃ b, q.1 = .bool b ∧ b' = (!q.2 || b))
        (fun p w q h1 h2 => h1 q h2) hpw hp
      have hpw3 := Pw.imp (S := fun q b' => ∃ b, q.1 = .bool b ∧ b' = (!q.2 || b))
        (fun q b' h => h b' rfl) (Pw.map_right hpw2)
      obtain ⟨cs, hcs, hall⟩ := bool_and_vals hpw3
      simp [aggregate, hop, hcs, hall, bind, Except.bind, pure, Except.pure]
  · -- bool_or
    rename_i hop
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i ts hts
      have := mk_eq h; subst this
      obtain ⟨ws, bs, hws, rfl, rfl⟩ := eval_or_ok hw
      have hpw := mapM_terms (P := fun p w => ∀ q, PairInst x p q → ∀ b', w = .bool b' →
          ∃ b, q.1 = .bool b ∧ b' = (q.2 && b)) (fun p t w ht htw q hq b' hb' => by
          obtain ⟨v, g⟩ := p
          obtain ⟨q1, q2⟩ := q
          obtain ⟨h1, h2⟩ := hq
          try simp only at ht h1 h2 ⊢
          subst hb'
          split at ht
          · rename_i hT
            cases ht
            rw [isTrue_eval hT x] at h2; cases h2
            rw [h1] at htw; cases htw; exact ⟨b', rfl, by simp⟩
          · have := mk_eq ht; subst this
            obtain ⟨_, bs2, hws2, rfl, hw2⟩ := eval_and_ok htw
            simp [List.mapM_cons, h2, h1, bind, Except.bind, pure, Except.pure] at hws2
            match bs2, hws2 with
            | [c1, c2], hws2 =>
              simp at hws2
              obtain ⟨hc1, hc2⟩ := hws2
              cases hw2
              exact ⟨c2, hc2, by simp [hc1]⟩) hts hws
      have hpw2 := Pw.combine (T := fun q (w : Value) => ∀ b', w = .bool b' → ∃ b, q.1 = .bool b ∧ b' = (q.2 && b))
        (fun p w q h1 h2 => h1 q h2) hpw hp
      have hpw3 := Pw.imp (S := fun q b' => ∃ b, q.1 = .bool b ∧ b' = (q.2 && b))
        (fun q b' h => h b' rfl) (Pw.map_right hpw2)
      obtain ⟨cs, hcs, hany⟩ := bool_or_vals hpw3
      simp [aggregate, hop, hcs, hany, bind, Except.bind, pure, Except.pure]
  · -- all_different, min, max
    rename_i o _ _ _ _
    simp only at h
    split at h
    · rename_i hall
      rw [present_all vals (vals_all (gsAll hg hall))]
      have hvs := map_fst_eq hv
      split at h
      all_goals first
        | (simp [throw, throwThe, MonadExceptOf.throw] at h; done)
        | skip
      all_goals
        have := mk_eq h; subst this
        obtain ⟨ws, hws, hap⟩ := eval_call_ok hw
        rw [hvs] at hws; cases hws
        revert hap
        cases vals.map (·.1) <;> simp [aggregate, applyOp, *, throw, throwThe, MonadExceptOf.throw]
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

end Rasso.Phi
