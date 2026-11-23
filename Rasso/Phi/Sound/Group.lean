import Rasso.Phi.Sound.Perm

/-!
# φ soundness: γ's expression on a group

`sAggEval_sound`: γ's expression, built symbolically over a group of rows, has on an
assignment `x` the value Lean's evaluator gives on the group's present tuples, in any order.
The hypotheses are the ones 5c keeps as its invariant: the cells of `x` have their kinds
(`CellsOk`), and each row of the group instantiates to a tuple, its guard to whether the
tuple is present (`GroupInst`).
-/

namespace Rasso.Phi

open Rasso

/-- The cells of `x` have their kinds. -/
def CellsOk (ks : Kinds) (x : Tuple) : Prop :=
  ∀ c k, ks.lookup c = some k → ∃ v, x.get? c = some v ∧ KindOk k v

/-- A row of a group, with its guard, instantiates to a tuple and whether it is present. -/
def GroupInst (x : Tuple) (rg : SRow × Term) (ub : Tuple × Bool) : Prop :=
  RowInst x rg.1 ub.1 ∧ rg.2.eval x = .ok (.bool ub.2)

/-- The tuples of the present rows. -/
def presentT (inst : List (Tuple × Bool)) : List Tuple :=
  inst.filterMap fun (u, b) => if b then some u else none

/-! ## Built terms evaluate -/

theorem termKinds_call (ks : Kinds) (op : String) (args : List Term) :
    termKinds ks (.call op args) = (do opKinds op (← args.mapM (termKinds ks))) := by
  rw [termKinds]
  have : (args.attach.mapM fun ⟨y, _⟩ => termKinds ks y) = args.mapM (termKinds ks) :=
    mapM_congr2 (by simp) (fun i hi hi' => by simp)
  rw [this]

theorem mk_sound {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {op : String} {args : List Term}
    {t : Term} (h : mk ks op args = .ok t) : ∃ v, t.eval x = .ok v := by
  have := mk_eq h; subst this
  simp only [mk, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i kss hkss
    split at h
    · cases h
    · rename_i k hk
      obtain ⟨v, hv, _⟩ := termKinds_sound hx (.call op args) (ks := k)
        (by rw [termKinds_call]; simp [bind, Except.bind, hkss, hk])
      exact ⟨v, hv⟩

theorem mk_args {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {op : String} {args : List Term}
    {t : Term} (h : mk ks op args = .ok t) : ∀ a ∈ args, ∀ v, a.eval x = .ok v → v.isFloat = false := by
  simp only [mk, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i kss hkss
    intro a ha v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hg := mapM_ok_get hkss i hi
    obtain ⟨v', hv', hok⟩ := termKinds_sound hx _ hg
    rw [hv] at hv'; cases hv'
    exact notFloat hok

/-- A term φ computes on a row that instantiates evaluates. -/
theorem sEval_ok {ks : Kinds} {x u : Tuple} (hx : CellsOk ks x) {row : SRow} (hu : RowInst x row u) :
    ∀ (t : Term) {s : Term}, sEval ks row t = .ok s → ∃ v, s.eval x = .ok v
  | .attr a, s, h => by
    rw [sEval] at h
    split at h
    · rename_i t ht; cases h; obtain ⟨v, hv, _⟩ := hu.some ht; exact ⟨v, hv⟩
    · cases h
  | .val v, s, h => by rw [sEval] at h; cases h; exact ⟨v, by simp [Term.eval]⟩
  | .call op args, s, h => by
    rw [sEval] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i ss hss
      unfold sApply at h
      split at h
      · simp only [bind, Except.bind, pure, Except.pure] at h
        split at h
        · cases h
        · rename_i v _; cases h; exact ⟨v, by simp [Term.eval]⟩
      · exact mk_sound hx h

/-! ## A group's values -/

theorem group_vals {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {t : Term} :
    ∀ {group : List (SRow × Term)} {inst : List (Tuple × Bool)} {vs : List Term},
    Pw (GroupInst x) group inst → group.mapM (fun (r, _) => sEval ks r t) = .ok vs →
    ∃ vals, Pw (PairInst x) (vs.zip (group.map (·.2))) vals ∧ vs.length = (group.map (·.2)).length ∧
      (presentT inst).mapM t.eval = .ok (present vals)
  | [], [], vs, .nil, h => by
    simp [List.mapM_nil, pure, Except.pure] at h; subst h
    exact ⟨[], .nil, rfl, rfl⟩
  | (r, g) :: group, (u, b) :: inst, vs, .cons ⟨hu, hg⟩ hp, h => by
    obtain ⟨s0, vs', hs0, hvs', rfl⟩ := mapM_cons_ok h
    obtain ⟨v0, hv0⟩ := sEval_ok hx hu t hs0
    have ht : t.eval u = .ok v0 := by rw [← sEval_sound hu t hs0]; exact hv0
    obtain ⟨vals, hpw, hlen, hm⟩ := group_vals hx hp hvs'
    refine ⟨(v0, b) :: vals, .cons ⟨hv0, hg⟩ hpw, by simpa using hlen, ?_⟩
    cases b
    · simpa [presentT, present] using hm
    · simp only [presentT, present, List.filterMap_cons, ite_true] at hm ⊢
      exact mapM_cons_of ht hm

theorem sAgg_minmax {ks : Kinds} {op : String} {vs gs : List Term} {s : Term}
    (hop : aggName op = "min" ∨ aggName op = "max") (h : sAgg ks op vs gs = .ok s) :
    ∃ o, mk ks o vs = .ok s := by
  rcases hop with hop | hop <;> simp only [sAgg, hop] at h <;> split at h
  all_goals first
    | (rename_i heq; exfalso; revert heq; decide)
    | (split at h <;> first
        | (simp only at h; exact ⟨_, h⟩)
        | (simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h))

theorem present_notFloat {x : Tuple} {vs gs : List Term} {vals : List (Value × Bool)}
    (hp : Pw (PairInst x) (vs.zip gs) vals) (hf : ∀ a ∈ vs, ∀ v, a.eval x = .ok v → v.isFloat = false) :
    ∀ v ∈ present vals, v.isFloat = false := by
  intro v hv
  simp only [present, List.mem_filterMap] at hv
  obtain ⟨q, hq, hqv⟩ := hv
  have := Pw.forall_mem (P := fun p : Term × Term => p.1 ∈ vs) (Q := fun q : Value × Bool => q.1.isFloat = false)
    (fun p q hpq hm => hf p.1 hm q.1 hpq.1) hp (fun p hm => (List.of_mem_zip hm).1) q hq
  obtain ⟨w, b⟩ := q
  cases b <;> simp at hqv
  subst hqv; exact this

/-! ## `has_subset` over a group -/

theorem perm_any_f {α : Type} {f : α → Bool} {l l' : List α} (p : l.Perm l') : l.any f = l'.any f := by
  cases h : l.any f <;> cases h' : l'.any f <;> try rfl
  · rw [List.any_eq_true] at h'
    obtain ⟨b, hb, hb'⟩ := h'
    have : l.any f = true := List.any_eq_true.mpr ⟨b, p.mem_iff.mpr hb, hb'⟩
    rw [h] at this; cases this
  · rw [List.any_eq_true] at h
    obtain ⟨b, hb, hb'⟩ := h
    have : l'.any f = true := List.any_eq_true.mpr ⟨b, p.mem_iff.mp hb, hb'⟩
    rw [h'] at this; cases this

theorem matchesAll_zip {β : Type} (u : Tuple) (h : List (String × β)) (row : List Value) :
    matchesAll u ((h.map (·.1)).zip row) = (h.zip row).all fun ((a, _), v) => u.get? a == some v := by
  induction h generalizing row with
  | nil => simp [matchesAll]
  | cons p h ih =>
    cases row with
    | nil => simp [matchesAll]
    | cons v row =>
      have := ih row
      simp only [matchesAll] at this ⊢
      simp [List.all_cons, this]

theorem rowsInst_of {x : Tuple} : ∀ {group : List (SRow × Term)} {inst : List (Tuple × Bool)},
    Pw (GroupInst x) group inst → RowsInst x (group.map (·.1)) (inst.map (·.1))
  | [], [], .nil => trivial
  | _ :: _, _ :: _, .cons h hp => ⟨h.1, rowsInst_of hp⟩

theorem presentT_all {x : Tuple} : ∀ {group : List (SRow × Term)} {inst : List (Tuple × Bool)},
    Pw (GroupInst x) group inst → group.all (isTrue ·.2) = true → presentT inst = inst.map (·.1)
  | [], [], .nil, _ => rfl
  | (r, g) :: _, (u, b) :: _, .cons ⟨_, hg⟩ hp, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    rw [isTrue_eval hall.1 x] at hg; cases hg
    simp only [presentT, List.filterMap_cons, ite_true, List.map_cons] at ⊢
    exact congrArg _ (presentT_all hp hall.2)

theorem mapM_ok_self {α ε : Type} : ∀ (l : List α), l.mapM (fun a => (Except.ok a : Except ε α)) = .ok l
  | [] => rfl
  | a :: l => by simp [List.mapM_cons, mapM_ok_self l, bind, Except.bind, pure, Except.pure]

theorem hasSubset_sound {ks : Kinds} {x : Tuple} {key : SRow} {keyT : Tuple}
    {group : List (SRow × Term)} {inst : List (Tuple × Bool)}
    (hg : Pw (GroupInst x) group inst) {us : List Tuple} (hus : (presentT inst).Perm us)
    {hd : List (String × DomExpr)} {rows : List (List Value)} {s : Term} {w : Value}
    (h : sAggEval ks key group (.hasSubset (.omegaRows hd rows)) = .ok s) (hw : s.eval x = .ok w) :
    Agg.eval keyT us (.hasSubset (.omegaRows hd rows)) = .ok w := by
    rw [sAggEval] at h
    simp only [bind, Except.bind] at h
    split at h
    · rename_i hall
      split at h
      · cases h
      · rename_i terms hterms
        have := mk_eq h; subst this
        obtain ⟨ws, bs, hws, rfl, rfl⟩ := eval_and_ok hw
        have hpres := presentT_all hg hall
        rw [hpres] at hus
        have hri := rowsInst_of hg
        have hl := mapM_ok_length hterms
        have hl2 := mapM_ok_length hws
        simp only [List.length_map] at hl2
        have hbs : bs = rows.map fun row => (inst.map (·.1)).any (matchesAll · ((hd.map (·.1)).zip row)) := by
          apply List.ext_getElem (by simp; omega)
          intro i hi hi'
          have h1 := mapM_ok_get hterms i (by simp at hi'; exact hi')
          have h2 := mapM_ok_get hws i (by omega)
          simp only [List.getElem_map] at h2
          have := sHas_sound hri h1 h2
          simp at this ⊢; exact this
        subst hbs
        have e : ∀ row, (us.any fun t => (hd.zip row).all fun x => t.get? x.1.fst == some x.snd) =
            (inst.map (·.1)).any (matchesAll · ((hd.map (·.1)).zip row)) := by
          intro row; rw [← perm_any_f hus]; congr 1; funext u; exact (matchesAll_zip u hd row).symm
        simp only [Agg.eval, List.all_map, e]; rfl
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## γ's expression -/

theorem sAggEval_sound {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {key : SRow} {keyT : Tuple}
    (hkey : RowInst x key keyT) {group : List (SRow × Term)} {inst : List (Tuple × Bool)}
    (hg : Pw (GroupInst x) group inst) {us : List Tuple} (hus : (presentT inst).Perm us) :
    ∀ (e : Agg) {s : Term} {w : Value}, sAggEval ks key group e = .ok s → s.eval x = .ok w →
      Agg.eval keyT us e = .ok w
  | .agg op t, s, w, h, hw => by
    rw [sAggEval] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i vs hvs
      obtain ⟨vals, hp, hlen, hm⟩ := group_vals hx hg hvs
      have ha := sAgg_sound hlen hp h hw
      obtain ⟨vs', hm', pv⟩ := mapM_perm hus hm
      simp only [Agg.eval, bind, Except.bind, hm']
      refine aggregate_perm pv (fun hmm => ?_) ha
      obtain ⟨o, ho⟩ := sAgg_minmax hmm h
      exact present_notFloat hp (mk_args hx ho)
  | .attr a, s, w, h, hw => by
    rw [sAggEval] at h
    split at h
    · rename_i t ht; cases h
      obtain ⟨v, hv, hk⟩ := hkey.some ht
      rw [hv] at hw; cases hw
      simp [Agg.eval, hk]
    · cases h
  | .val v, s, w, h, hw => by
    rw [sAggEval] at h; cases h
    simp [Term.eval] at hw; subst hw; simp [Agg.eval]
  | .call op args, s, w, h, hw => by
    rw [sAggEval] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i ss hss
      rw [sApply_sound h x] at hw
      simp only [bind, Except.bind] at hw
      split at hw
      · cases hw
      · rename_i ws hws
        have hl := mapM_ok_length hss
        have hl2 := mapM_ok_length hws
        simp only [List.length_attach] at hl
        have : args.mapM (Agg.eval keyT us) = .ok ws := by
          rw [← mapM_ok_self ws]
          apply mapM_congr2 (by omega)
          intro i hi hi'
          have h1 := mapM_ok_get hss i (by simpa using hi)
          simp only [List.getElem_attach] at h1
          have h2 := mapM_ok_get hws i (by omega)
          exact sAggEval_sound hx hkey hg hus args[i] h1 (by simpa using h2)
        rw [Agg.eval]; simp [bind, Except.bind, this, hw]
  | .hasSubset r, s, w, h, hw => by
    cases r with
    | omegaRows hd rows => exact hasSubset_sound hg hus h hw
    | _ => rw [sAggEval] at h <;> first | cases h | (intro _ _ hr; cases hr)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  have := List.sizeOf_lt_of_mem (List.getElem_mem hi); omega

end Rasso.Phi
