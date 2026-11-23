import Rasso.Phi.Phi

/-!
# φ's soundness: terms

-/

namespace Rasso.Phi

open Rasso

/-! ## Lists in `Except` -/

theorem mapM_ok_length {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.length = l.length
  | [], r, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h; simp [mapM_ok_length ‹_›]

/-- Two `mapM`s agree when their functions agree pointwise along two lists. -/
theorem mapM_congr2 {α α' β ε : Type} {f : α → Except ε β} {g : α' → Except ε β} :
    ∀ {l : List α} {l' : List α'}, l.length = l'.length →
      (∀ i (h : i < l.length) (h' : i < l'.length), f l[i] = g l'[i]) →
      l.mapM f = l'.mapM g
  | [], [], _, _ => rfl
  | a :: l, b :: l', hl, h => by
    simp only [List.mapM_cons]
    have h0 : f a = g b := h 0 (by simp) (by simp)
    rw [h0, mapM_congr2 (by simpa using hl) (fun i hi hi' => h (i + 1) (by simpa using hi) (by simpa using hi'))]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem mapM_ok_get {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β} (h : l.mapM f = .ok r) (i : Nat) (hi : i < l.length),
      f l[i] = .ok (r[i]'(by rw [mapM_ok_length h]; exact hi))
  | [], _, _, i, hi => by simp at hi
  | a :: l, r, h, i, hi => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i b hb
      split at h
      · cases h
      · rename_i rs hrs
        cases h
        cases i with
        | zero => simpa using hb
        | succ i => simpa using mapM_ok_get hrs i (by simpa using hi)

/-! ## `mk` and `sApply` -/

theorem mk_eq {ks : Kinds} {op : String} {args : List Term} {t : Term}
    (h : mk ks op args = .ok t) : t = .call op args := by
  simp only [mk, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

theorem decided?_mapM {ss : List Term} {vs : List Value} (h : ss.mapM decided? = some vs) :
    ss = vs.map .val := by
  induction ss generalizing vs with
  | nil => simp at h; subst h; rfl
  | cons s ss ih =>
    simp only [List.mapM_cons] at h
    cases hs : decided? s with
    | none => simp [hs] at h
    | some v =>
      cases hss : ss.mapM decided? with
      | none => simp [hs, hss] at h
      | some ws =>
        simp [hs, hss] at h; subst h
        cases s <;> simp [decided?] at hs
        subst hs; simp [ih hss]

/-- The values of `.val`s. -/
theorem eval_vals (x : Tuple) (vs : List Value) :
    (vs.map Term.val).mapM (Term.eval x) = .ok vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [List.mapM_cons, Term.eval, ih, bind, Except.bind, pure, Except.pure]

/-- `sApply` commutes with evaluation: whatever it builds evaluates, on any assignment, to
`applyOp` on the arguments' values. -/
theorem sApply_sound {ks : Kinds} {op : String} {ss : List Term} {s : Term}
    (h : sApply ks op ss = .ok s) (x : Tuple) :
    s.eval x = (do applyOp op (← ss.mapM (Term.eval x))) := by
  unfold sApply at h
  split at h
  · rename_i vs hvs
    rw [decided?_mapM hvs, eval_vals]
    simp only [bind, Except.bind, pure, Except.pure] at h ⊢
    split at h
    · cases h
    · cases h; rename_i v hv; simp [Term.eval, hv]
  · rw [mk_eq h]; simp [Term.eval]

/-! ## `sEval` -/

/-- A symbolic row instantiates under the assignment `x` to the tuple `u`: each attribute
is in both or neither, and where it is in both, the row's term evaluates to `u`'s value. -/
def RowInst (x : Tuple) (row : SRow) (u : Tuple) : Prop :=
  ∀ a, (row.lookup a = none ∧ u.get? a = none) ∨
    ∃ s v, row.lookup a = some s ∧ s.eval x = .ok v ∧ u.get? a = some v

/-- `sEval` commutes with instantiation. -/
theorem sEval_sound {ks : Kinds} {row : SRow} {x u : Tuple} (hu : RowInst x row u) :
    ∀ (t : Term) {s : Term}, sEval ks row t = .ok s → s.eval x = t.eval u
  | .attr a, s, h => by
    rw [sEval] at h
    rcases hu a with ⟨hr, _⟩ | ⟨s', v, hr, hs, hg⟩
    · simp [hr] at h
    · simp [hr] at h; subst h; simp [Term.eval, hs, hg]
  | .val v, s, h => by rw [sEval] at h; cases h; simp [Term.eval]
  | .call op args, s, h => by
    rw [sEval] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i ss hss
      rw [sApply_sound h x]
      have hl := mapM_ok_length hss
      have : ss.mapM (Term.eval x) = args.mapM (Term.eval u) := by
        apply mapM_congr2 (by simpa using hl)
        intro i hi hi'
        have hg := mapM_ok_get hss i (by simpa using hi')
        simp only [List.getElem_attach] at hg
        exact sEval_sound hu args[i] hg
      rw [this]; simp [Term.eval, bind, Except.bind]
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  have := List.sizeOf_lt_of_mem (List.getElem_mem hi'); omega

/-! ## The simplifier -/

/-- `and` (`isAnd`) or `or` of Booleans. -/
def boolSem (isAnd : Bool) (bs : List Bool) : Bool := if isAnd then bs.all id else bs.any id

def opName (isAnd : Bool) : String := if isAnd then "and" else "or"

theorem boolSem_append (isAnd : Bool) (l m : List Bool) :
    boolSem isAnd (l ++ m) = if isAnd then (boolSem isAnd l && boolSem isAnd m)
      else (boolSem isAnd l || boolSem isAnd m) := by
  cases isAnd <;> simp [boolSem, List.all_append, List.any_append]

theorem boolSem_cons (isAnd b : Bool) (l : List Bool) :
    boolSem isAnd (b :: l) = if isAnd then (b && boolSem isAnd l) else (b || boolSem isAnd l) := by
  cases isAnd <;> simp [boolSem]

theorem mapM_asBool {who : String} :
    ∀ {ws : List Value} {bs : List Bool}, ws.mapM (asBool who) = .ok bs → ws = bs.map .bool
  | [], bs, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; rfl
  | w :: ws, bs, h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i b hb
      split at h
      · cases h
      · rename_i bs' hbs
        cases h
        cases w <;> simp [asBool] at hb
        subst hb; simp [mapM_asBool hbs]

theorem mapM_asBool_bools (who : String) (bs : List Bool) :
    (bs.map Value.bool).mapM (asBool who) = .ok bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.mapM_cons, asBool, ih, bind, Except.bind, pure, Except.pure]

theorem applyOp_andor {isAnd : Bool} {ws : List Value} {v : Value}
    (h : applyOp (opName isAnd) ws = .ok v) :
    ∃ bs, ws = bs.map .bool ∧ v = .bool (boolSem isAnd bs) := by
  cases isAnd
  · have h' : applyOp "or" ws = .ok v := by simpa [opName] using h
    simp only [applyOp, bind, Except.bind, pure, Except.pure] at h'
    split at h'
    · cases h'
    · rename_i bs hbs
      cases h'
      exact ⟨bs, mapM_asBool hbs, by simp [boolSem]⟩
  · have h' : applyOp "and" ws = .ok v := by simpa [opName] using h
    simp only [applyOp, bind, Except.bind, pure, Except.pure] at h'
    split at h'
    · cases h'
    · rename_i bs hbs
      cases h'
      exact ⟨bs, mapM_asBool hbs, by simp [boolSem]⟩

theorem mapM_asBool_comp (who : String) (bs : List Bool) :
    bs.mapM (asBool who ∘ Value.bool) = .ok bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.mapM_cons, asBool, ih, bind, Except.bind, pure, Except.pure]

theorem applyOp_andor_bools (isAnd : Bool) (bs : List Bool) :
    applyOp (opName isAnd) (bs.map .bool) = .ok (.bool (boolSem isAnd bs)) := by
  cases isAnd <;> simp [opName, applyOp, mapM_asBool_comp, boolSem, bind, Except.bind, pure, Except.pure]

theorem eval_call (x : Tuple) (op : String) (args : List Term) :
    (Term.call op args).eval x = (do applyOp op (← args.mapM (Term.eval x))) := by
  simp [Term.eval]

theorem beq_val {s : Term} {v : Value} (h : s.beq (.val v) = true) : s = .val v := by
  cases s <;> simp [Term.beq] at h
  subst h; rfl

/-- One step of `simpFlat`'s flattening. -/
def flatStep (op : String) (ident : Term) (s : Term) : List Term :=
  match s with
  | .call o zs => if o == op then zs else [s]
  | s => if s.beq ident then [] else [s]

theorem simpFlat_eq (op : String) (ident absorb : Term) (ss : List Term) :
    simpFlat op ident absorb ss =
      let ys := ss.flatMap (flatStep op ident)
      if ys.any (·.beq absorb) then absorb
      else match ys with
        | [] => ident
        | [y] => y
        | ys => .call op ys := by
  simp only [simpFlat]
  first
    | rfl
    | (congr 1 <;> (try congr 1) <;> (try congr 1) <;> (try (funext s; cases s <;> rfl)))

/-- Flattening keeps the Boolean meaning. -/
theorem flat_sound (isAnd : Bool) (x : Tuple) :
    ∀ (ss : List Term) (bs : List Bool), ss.mapM (Term.eval x) = .ok (bs.map .bool) →
      ∃ cs, (ss.flatMap (flatStep (opName isAnd) (.val (.bool isAnd)))).mapM (Term.eval x) =
          .ok (cs.map .bool) ∧ boolSem isAnd cs = boolSem isAnd bs
  | [], bs, h => by
    simp [List.mapM_nil, pure, Except.pure] at h
    cases bs with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons _ _ => simp at h
  | s :: ss, bs, h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i w hw
      split at h
      · cases h
      · rename_i ws hws
        cases bs with
        | nil => simp at h
        | cons b bs =>
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨cs, hcs, hsem⟩ := flat_sound isAnd x ss bs hws
          -- the step for s
          have step : ∃ c1, (flatStep (opName isAnd) (.val (.bool isAnd)) s).mapM (Term.eval x) =
              .ok (c1.map .bool) ∧ boolSem isAnd c1 = b := by
            cases s with
            | call o zs =>
              simp only [flatStep]
              by_cases ho : o = opName isAnd
              · subst ho
                simp only [beq_self_eq_true, ite_true]
                rw [eval_call] at hw
                simp only [bind, Except.bind] at hw
                split at hw
                · cases hw
                · rename_i us hus
                  obtain ⟨c1, rfl, hv⟩ := applyOp_andor hw
                  cases hv
                  exact ⟨c1, hus, rfl⟩
              · simp only [show (o == opName isAnd) = false from by simpa using ho]
                refine ⟨[b], ?_, ?_⟩
                · simp [List.mapM_cons, hw, bind, Except.bind, pure, Except.pure]
                · cases isAnd <;> simp [boolSem]
            | _ =>
              simp only [flatStep]
              split
              · rename_i hb
                have := beq_val hb
                cases this
                all_goals
                  have hb' : isAnd = b := by simpa [Term.eval] using hw
                  subst hb'
                  exact ⟨[], rfl, by cases isAnd <;> rfl⟩
              · refine ⟨[b], ?_, ?_⟩
                · simp [List.mapM_cons, hw, bind, Except.bind, pure, Except.pure]
                · cases isAnd <;> simp [boolSem]
          obtain ⟨c1, hc1, hb⟩ := step
          refine ⟨c1 ++ cs, ?_, ?_⟩
          · rw [List.flatMap_cons, List.mapM_append, hc1, hcs]; simp [bind, Except.bind, pure, Except.pure]
          · rw [boolSem_append, boolSem_cons, hb, hsem]

theorem mem_mapM_bool {x : Tuple} {ys : List Term} {cs : List Bool}
    (h : ys.mapM (Term.eval x) = .ok (cs.map .bool)) {y : Term} (hy : y ∈ ys) :
    ∃ c ∈ cs, y.eval x = .ok (.bool c) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have := mapM_ok_get h i hi
  have hl := mapM_ok_length h
  simp at hl
  refine ⟨cs[i]'(by omega), List.getElem_mem _, ?_⟩
  simpa using this

theorem simpFlat_sound (isAnd : Bool) (x : Tuple) (ss : List Term) (bs : List Bool)
    (h : ss.mapM (Term.eval x) = .ok (bs.map .bool)) :
    (simpFlat (opName isAnd) (.val (.bool isAnd)) (.val (.bool !isAnd)) ss).eval x =
      .ok (.bool (boolSem isAnd bs)) := by
  obtain ⟨cs, hcs, hsem⟩ := flat_sound isAnd x ss bs h
  rw [simpFlat_eq, ← hsem]
  simp only
  generalize hys : ss.flatMap (flatStep (opName isAnd) (.val (.bool isAnd))) = ys at hcs
  split
  · rename_i hany
    obtain ⟨y, hy, hb⟩ := List.any_eq_true.mp hany
    have := beq_val hb; subst this
    obtain ⟨c, hc, hyc⟩ := mem_mapM_bool hcs hy
    have hcv : (!isAnd) = c := by simpa [Term.eval] using hyc
    subst hcv
    cases isAnd
    · simp only [boolSem, Term.eval, Bool.not_false, Bool.false_eq_true, ite_false]
      have : cs.any id = true := List.any_eq_true.mpr ⟨true, hc, rfl⟩
      rw [this]
    · simp only [boolSem, Term.eval, Bool.not_true, ite_true]
      have : cs.all id = false := by
        cases h' : cs.all id
        · rfl
        · have := List.all_eq_true.mp h' false hc; simp at this
      rw [this]
  · split
    · cases cs with
      | nil => cases isAnd <;> simp [Term.eval, boolSem]
      | cons _ _ => simp [pure, Except.pure] at hcs
    · cases cs with
      | nil => simp [List.mapM_cons, bind, Except.bind, pure, Except.pure] at hcs; split at hcs <;> simp at hcs
      | cons c cs =>
        rename_i y
        have := mem_mapM_bool hcs (List.mem_singleton.mpr rfl)
        obtain ⟨c', hc', hy⟩ := this
        have hl := mapM_ok_length hcs; simp at hl
        subst hl
        simp at hc'; subst hc'
        rw [hy]; cases isAnd <;> simp [boolSem]
    · rw [eval_call, hcs]; simp [bind, Except.bind, applyOp_andor_bools]

theorem mapM_map_ok {x : Tuple} {f : Term → Term} :
    ∀ {xs : List Term} {ws : List Value}, xs.mapM (Term.eval x) = .ok ws →
      (∀ y ∈ xs, ∀ w, y.eval x = .ok w → (f y).eval x = .ok w) →
      (xs.map f).mapM (Term.eval x) = .ok ws
  | [], ws, h, _ => h
  | y :: xs, ws, h, hf => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i w hw
      split at h
      · cases h
      · rename_i ws' hws
        cases h
        simp only [List.map_cons, List.mapM_cons, bind, Except.bind, pure, Except.pure]
        rw [hf y (by simp) w hw, mapM_map_ok hws (fun z hz => hf z (by simp [hz]))]

theorem eval_call_ok {x : Tuple} {op : String} {xs : List Term} {v : Value}
    (h : (Term.call op xs).eval x = .ok v) :
    ∃ ws, xs.mapM (Term.eval x) = .ok ws ∧ applyOp op ws = .ok v := by
  rw [eval_call] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · exact ⟨_, ‹_›, h⟩

/-- The simplifier keeps a term's value wherever the term has one. -/
theorem simpTerm_sound (x : Tuple) : ∀ (t : Term) {v : Value}, t.eval x = .ok v →
    (simpTerm t).eval x = .ok v
  | .call op xs, v, h => by
    obtain ⟨ws, hws, hap⟩ := eval_call_ok h
    have hmap : (xs.map simpTerm).mapM (Term.eval x) = .ok ws :=
      mapM_map_ok hws (fun y hy w hw => simpTerm_sound x y hw)
    have hatt : (xs.attach.map fun ⟨y, _⟩ => simpTerm y) = xs.map simpTerm := by simp
    by_cases h1 : op = "and"
    · subst h1
      rw [simpTerm.eq_1, hatt]
      obtain ⟨bs, rfl, rfl⟩ := applyOp_andor (isAnd := true) (by simpa [opName] using hap)
      simpa [opName] using simpFlat_sound true x _ bs hmap
    by_cases h2 : op = "or"
    · subst h2
      rw [simpTerm.eq_2, hatt]
      obtain ⟨bs, rfl, rfl⟩ := applyOp_andor (isAnd := false) (by simpa [opName] using hap)
      simpa [opName] using simpFlat_sound false x _ bs hmap
    by_cases h3 : ∃ y, op = "not" ∧ xs = [y]
    · obtain ⟨y, hn, hx⟩ := h3
      have hyx : y ∈ xs := by rw [hx]; exact List.mem_singleton_self y
      have IH := fun w (hw : y.eval x = .ok w) => simpTerm_sound x y hw
      subst hn; subst hx
      rw [simpTerm.eq_3]
      simp only [List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure] at hws
      split at hws
      · cases hws
      · rename_i w hw
        cases hws
        have hy := IH w hw
        simp only [applyOp, bind, Except.bind, pure, Except.pure] at hap
        split at hap
        · cases hap
        · rename_i b hb
          cases hap
          cases w <;> simp [asBool] at hb
          subst hb
          rw [simpNot.eq_def]
          split
          · rename_i b' heq
            rw [heq] at hy; simp [Term.eval] at hy; subst hy; simp [Term.eval]
          · simp [Term.eval, hy, applyOp, asBool, bind, Except.bind, pure, Except.pure]
    · rw [simpTerm.eq_4 op xs h1 h2 (fun y hn hx => h3 ⟨y, hn, hx⟩), hatt, eval_call, hmap]
      simpa [bind, Except.bind] using hap
  | .attr a, v, h => by rw [simpTerm.eq_5 _ (by simp) (by simp) (by simp) (by simp)]; exact h
  | .val w, v, h => by rw [simpTerm.eq_5 _ (by simp) (by simp) (by simp) (by simp)]; exact h
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem hy; omega)
    | omega
    | (have := List.sizeOf_lt_of_mem hyx; omega)

/-! ## The Decision's term over one copy's cells -/

/-- Replacing each attribute of `t` by a term that evaluates under `x` as the attribute does
under `d` gives a term that evaluates under `x` as `t` does under `d`. -/
theorem substAttrs_sound {m : List (String × Term)} {x d : Tuple} :
    ∀ (t : Term), (∀ a ∈ t.attrs, ∃ s, m.lookup a = some s ∧ s.eval x = (Term.attr a).eval d) →
      (substAttrs m t).eval x = t.eval d
  | .attr a, h => by
    obtain ⟨s, hs, he⟩ := h a (by simp [Term.attrs])
    rw [substAttrs, hs]; exact he
  | .val v, _ => by rw [substAttrs] <;> simp [Term.eval]
  | .call op xs, h => by
    rw [substAttrs, eval_call, eval_call]
    have : (xs.attach.map fun ⟨y, _⟩ => substAttrs m y).mapM (Term.eval x) = xs.mapM (Term.eval d) := by
      apply mapM_congr2 (by simp)
      intro i hi hi'
      simp only [List.getElem_map, List.getElem_attach]
      exact substAttrs_sound xs[i] (fun a ha => h a (by
        simp only [Term.attrs, List.mem_flatMap]; exact ⟨xs[i], List.getElem_mem hi', ha⟩))
    rw [this]
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  have := List.sizeOf_lt_of_mem (List.getElem_mem hi'); omega

end Rasso.Phi
