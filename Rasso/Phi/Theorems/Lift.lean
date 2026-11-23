import Rasso.Phi.Theorems.Cells

/-!
# φ's theorems: B lifts to the evaluator (B′)

In the program's environment after the earlier statements, statement `k` evaluates (without
refusal) to a solution set whose candidates are exactly the `substitute F x` on which
`accepts` gives `.ok true`.
-/

namespace Rasso.Phi

open Rasso

variable {nm : String → Nat → String}

/-- The ω_sol part of `Expr.eval` and of `omegaOf`: the Data, the Decision, their check, the
Decision's tuples. -/
def omegaCore (env : Env) (d dec : Expr) : Except String (Finrel × Unrel × List Tuple) := do
  let data ← (← Expr.eval env [] d).asFinrel "ω_sol data"
  let u ← (← Expr.eval env [] dec).asUnrel
  for a in u.heading.attrs do
    if data.attrs.contains a then throw s!"ω_sol: {a} is both a data and a decision attribute"
  let picks ← u.tuples
  return (data, u, picks)

theorem omegaOf_core (p : Program) (ch : Chain) :
    omegaOf p ch = (do let env ← envAt p ch.stmt; omegaCore env ch.data ch.decision) := by
  rfl

theorem eval_omegaSol_core (env : Env) (d dec : Expr) :
    Expr.eval env [] (.omegaSol d dec) = (do
      let (data, u, picks) ← omegaCore env d dec
      return .sol ⟨data, data.heading ++ u.heading,
        omegaSolCandidates (data.heading ++ u.heading) data.tuples picks⟩) := by
  rw [Expr.eval.eq_def]
  simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte, omegaCore, omegaSolCandidates]
  simp only [bind, Except.bind]
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

theorem eval_sigmaSol_eq (env : Env) (c : Cond) (e : Expr) :
    Expr.eval env [] (.sigmaSol c e) = (do
      let s ← (← Expr.eval env [] e).asSol
      c.checkSubsets env s.heading
      let cands ← s.candidates.filterM fun r => c.eval (candEnv env (.finrel r)) [e]
      return .sol { s with candidates := cands }) := by
  rw [Expr.eval.eq_def]
  simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem eval_name_eq (env : Env) (n : String) :
    Expr.eval env [] (.name n) = (match env.lookup n with
      | some v => .ok v
      | none => .error s!"{n} is not defined") := by
  rw [Expr.eval.eq_def]
  simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte]
  cases List.lookup n env <;> rfl

/-! ## What a chain evaluates to -/

/-- Every level of the chain holds on the candidate `c` (a refusal counts as false). -/
def levelsB (p : Program) (ch : Chain) (c : Finrel) : Bool :=
  ch.levels.all fun lv => match envAt p lv.stmt with
    | .ok env => okB (lv.cond.eval (candEnv env (.finrel c)) [lv.marker])
    | .error _ => false

/-- The value `v` is the solution set of the chain `ch`: the candidates of its `ω_sol`, in
order, that every level keeps. -/
def SolSem (p : Program) (ch : Chain) (v : Val) : Prop :=
  ∃ s data u picks, v = .sol s ∧ omegaOf p ch = .ok (data, u, picks) ∧
    s.heading = data.heading ++ u.heading ∧
    s.candidates = (omegaSolCandidates (data.heading ++ u.heading) data.tuples picks).filter (levelsB p ch)

/-- A known chain and a bound value agree: same name, and the value is the chain's. -/
def NameRel (p : Program) (no : String × Option Chain) (nv : String × Val) : Prop :=
  no.1 = nv.1 ∧ ∀ ch, no.2 = some ch → SolSem p ch nv.2

theorem lookup_rel {p : Program} {n : String} {ch : Chain} :
    ∀ {known : List (String × Option Chain)} {env : Env}, Pw (NameRel p) known env →
      known.lookup n = some (some ch) → ∃ v, env.lookup n = some v ∧ SolSem p ch v
  | [], [], .nil, h => by simp at h
  | (n', o) :: known, (n'', v) :: env, .cons ⟨e, hs⟩ hk, h => by
    dsimp only at e hs
    subst e
    by_cases hn : n = n'
    · subst hn
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h ⊢
      exact ⟨v, rfl, hs ch h⟩
    · have hb : (n == n') = false := by simpa using hn
      simp only [List.lookup, hb] at h ⊢
      exact lookup_rel hk h

theorem passed_eq_okB (e : Except String Bool) : passed e = okB e := by
  cases e with
  | error => rfl
  | ok b => cases b <;> rfl

/-- **The chain is what the evaluator evaluates**: a statement `f` at `i` that unfolds to the
chain `ch`, evaluated (successfully) in the environment of the earlier statements, gives
the chain's solution set. -/
theorem sem_of_eval {p : Program} {i : Nat} {env : Env} (henv : envAt p i = .ok env)
    {known : List (String × Option Chain)} (hk : Pw (NameRel p) known env) :
    ∀ {f : Expr} {ch : Chain}, Unfolds known i f ch → ∀ {v : Val}, Expr.eval env [] f = .ok v → SolSem p ch v
  | _, _, .omega d dec, v, hv => by
    rw [eval_omegaSol_core] at hv
    have hom := omegaOf_core p ⟨i, d, dec, []⟩
    simp only [henv, bind, Except.bind] at hom hv
    split at hv
    · cases hv
    rename_i r hr
    obtain ⟨data, u, picks⟩ := r
    simp only [pure, Except.pure, Except.ok.injEq] at hv
    subst hv
    refine ⟨_, data, u, picks, rfl, by rw [hom]; exact hr, rfl, ?_⟩
    symm; exact List.filter_eq_self.mpr fun _ _ => rfl
  | _, _, .sigma c e ch hu _, v, hv => by
    rw [eval_sigmaSol_eq] at hv
    simp only [bind, Except.bind] at hv
    split at hv
    · cases hv
    rename_i ve hve
    obtain ⟨s, data, u, picks, rfl, hom, hh, hc⟩ := sem_of_eval henv hk hu hve
    simp only [Val.asSol] at hv
    split at hv
    · cases hv
    split at hv
    · cases hv
    rename_i cands hcands
    simp only [pure, Except.pure, Except.ok.injEq] at hv
    subst hv
    refine ⟨_, data, u, picks, rfl, hom, hh, ?_⟩
    obtain ⟨_, rfl⟩ := filterM_ok_iff.mp hcands
    dsimp only
    rw [hc, List.filter_filter]
    apply List.filter_congr
    intro r _
    simp only [levelsB, List.all_append, List.all_cons, List.all_nil, Bool.and_true, henv, passed_eq_okB]
    rw [Bool.and_comm]
  | _, _, .name n ch hl, v, hv => by
    rw [eval_name_eq] at hv
    obtain ⟨w, hw, hs⟩ := lookup_rel hk hl
    rw [hw] at hv
    cases hv
    exact hs

/-- **Statement `i` does not refuse**, when its own `ω_sol` (if written here) succeeds and
its own levels pass φ's subset check and evaluate on every candidate of the `ω_sol`. -/
theorem eval_ok_of {p : Program} {i : Nat} {env : Env} (henv : envAt p i = .ok env)
    {known : List (String × Option Chain)} (hk : Pw (NameRel p) known env) :
    ∀ {f : Expr} {ch : Chain}, Unfolds known i f ch →
      (ch.stmt = i → ∃ r, omegaOf p ch = .ok r) →
      (∀ data u picks, omegaOf p ch = .ok (data, u, picks) → ∀ lv ∈ ch.levels, lv.stmt = i →
        lv.cond.checkSubsets env (data.heading ++ u.heading) = .ok () ∧
        ∀ c ∈ omegaSolCandidates (data.heading ++ u.heading) data.tuples picks,
          ∃ b, lv.cond.eval (candEnv env (.finrel c)) [lv.marker] = .ok b) →
      ∃ v, Expr.eval env [] f = .ok v
  | _, _, .omega d dec, hω, _ => by
    obtain ⟨⟨data, u, picks⟩, hr⟩ := hω rfl
    have hom := omegaOf_core p ⟨i, d, dec, []⟩
    simp only [henv, bind, Except.bind] at hom
    rw [hom] at hr
    rw [eval_omegaSol_core, hr]
    exact ⟨_, rfl⟩
  | _, _, .sigma c e ch hu _, hω, hlv => by
    obtain ⟨ve, hve⟩ := eval_ok_of henv hk hu hω (fun data u picks hom lv hlv' hs =>
      hlv data u picks hom lv (List.mem_append_left _ hlv') hs)
    obtain ⟨s, data, u, picks, rfl, hom, hh, hc⟩ := sem_of_eval henv hk hu hve
    obtain ⟨hck, hev⟩ := hlv data u picks hom ⟨i, e, c⟩ (List.mem_append_right _ List.mem_cons_self) rfl
    rw [eval_sigmaSol_eq]
    simp only [hve, Val.asSol, hh, hck, bind, Except.bind]
    have hf : ∃ cands, s.candidates.filterM (fun r => c.eval (candEnv env (.finrel r)) [e]) = .ok cands := by
      refine ⟨_, filterM_ok_iff.mpr ⟨fun r hr => ?_, rfl⟩⟩
      rw [hc] at hr
      obtain ⟨b, hb⟩ := hev r (List.mem_filter.mp hr).1
      simp only [hb, Succeeds]
    obtain ⟨cands, hcands⟩ := hf
    rw [hcands]
    exact ⟨_, rfl⟩
  | _, _, .name n ch hl, _, _ => by
    rw [eval_name_eq]
    obtain ⟨w, hw, _⟩ := lookup_rel hk hl
    rw [hw]
    exact ⟨w, rfl⟩

/-! ## Through the program -/

/-- One step of `programChains`' fold. -/
def knownStep (known : List (String × Option Chain)) (x : (String × Expr) × Nat) :
    List (String × Option Chain) :=
  (x.1.1, chainOf known x.2 x.1.2) :: known

/-- The chains of the first `i` statements, latest first. -/
def knownAt (p : Program) (i : Nat) : List (String × Option Chain) :=
  (p.take i).zipIdx.foldl knownStep []

theorem knownAt_succ {p : Program} {i : Nat} (hi : i < p.length) :
    knownAt p (i + 1) = knownStep (knownAt p i) (p[i], i) := by
  unfold knownAt
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.zipIdx_append,
    List.foldl_append]
  simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]

theorem knownAt_of_le {p : Program} {i : Nat} (hi : p.length ≤ i) : knownAt p (i + 1) = knownAt p i := by
  unfold knownAt
  rw [List.take_of_length_le hi, List.take_of_length_le (by omega)]

theorem programChains_eq (p : Program) : programChains p = (knownAt p p.length).reverse := by
  unfold programChains knownAt
  rw [List.take_length]
  rfl

theorem knownAt_spec (p : Program) : ∀ m (hm : m ≤ p.length), (knownAt p m).length = m ∧
    ∀ k (hk : k < m), (knownAt p m).reverse[k]? =
      some ((p[k]'(Nat.lt_of_lt_of_le hk hm)).1, chainOf (knownAt p k) k (p[k]'(Nat.lt_of_lt_of_le hk hm)).2)
  | 0, _ => ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | m + 1, hm => by
    obtain ⟨hl, hs⟩ := knownAt_spec p m (by omega)
    rw [knownAt_succ (by omega)]
    refine ⟨by simp [knownStep, hl], fun k hk => ?_⟩
    simp only [knownStep, List.reverse_cons]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [List.getElem?_append_left (by simp [hl]; exact hk)]
      exact hs k hk
    · rw [List.getElem?_append_right (by simp [hl])]
      simp [hl]

theorem statementChain_spec {p : Program} {k : Nat} {ch : Chain} (h : statementChain p k = some ch) :
    ∃ hk : k < p.length, chainOf (knownAt p k) k p[k].2 = some ch := by
  obtain ⟨hl, hs⟩ := knownAt_spec p p.length (Nat.le_refl _)
  unfold statementChain at h
  rw [programChains_eq] at h
  have hk : k < p.length := by
    rcases Nat.lt_or_ge k p.length with hk | hk
    · exact hk
    · rw [List.getElem?_eq_none (by simp [hl]; omega)] at h
      cases h
  refine ⟨hk, ?_⟩
  rw [hs k hk] at h
  simpa using h

/-- Every statement that ran is bound to its chain's solution set, when it has a chain. -/
theorem run_rel (p : Program) : ∀ i {env : Env}, runProgram (p.take i) = .ok env →
    Pw (NameRel p) (knownAt p i) env.reverse
  | 0, env, h => by
    simp only [List.take_zero, runProgram, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact .nil
  | i + 1, env, h => by
    by_cases hi : i < p.length
    · rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, runProgram_append] at h
      cases h0 : runProgram (p.take i) with
      | error e => rw [h0] at h; cases h
      | ok env0 =>
        rw [h0] at h
        simp only [Except.bind, List.foldlM_cons, List.foldlM_nil, bind] at h
        cases hv : Expr.eval env0.reverse [] p[i].2 with
        | error e => simp [hv] at h
        | ok v =>
        simp only [hv, pure, Except.pure, Except.ok.injEq] at h
        subst h
        have ih := run_rel p i h0
        have henv : envAt p i = .ok env0.reverse := by simp [envAt, h0, Except.map]
        rw [knownAt_succ hi, List.reverse_append]
        refine .cons ⟨rfl, fun ch hc => ?_⟩ ih
        exact sem_of_eval henv ih ((chainOf_eq_some_iff _ _ _ _).mp hc) hv
    · rw [List.take_of_length_le (by omega)] at h
      rw [knownAt_of_le (by omega)]
      apply run_rel p i
      rw [List.take_of_length_le (by omega)]; exact h

/-! ## Theorem B′ -/

theorem Pw.exists_left {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {m : List β}, Pw R l m →
    ∀ a ∈ l, ∃ b, R a b
  | [], [], .nil, a, ha => by simp at ha
  | _ :: _, b :: _, .cons h hl, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, h⟩
    · exact Pw.exists_left hl a ha

theorem okB_true {e : Except String Bool} : okB e = true ↔ e = .ok true := by
  cases e with
  | error => simp [okB]
  | ok b => cases b <;> simp [okB]

theorem levels_all {p : Program} {c : Finrel} : ∀ {l : List Level} {bs : List Bool},
    Pw (fun (lv : Level) b => ∃ env, envAt p lv.stmt = .ok env ∧
      lv.cond.eval (candEnv env (.finrel c)) [lv.marker] = .ok b) l bs →
    (l.all fun lv => match envAt p lv.stmt with
      | .ok env => okB (lv.cond.eval (candEnv env (.finrel c)) [lv.marker])
      | .error _ => false) = bs.all id
  | [], [], .nil => rfl
  | _ :: _, b :: _, .cons ⟨env, he, hb⟩ hl => by
    have := levels_all hl
    simp only [List.all_cons, he, hb, okB, id] at this ⊢
    rw [this]

/-- **B′ for a chain**: an expression `f` of statement `i` that unfolds to the chain `ch`
whose φ succeeded evaluates, without refusal, in the environment of the earlier statements,
to a solution set with φ's heading, whose candidates are exactly the `substitute F x` on
which `acceptsOf` gives `.ok true`, each given by an assignment over exactly the cells. -/
theorem lift_of_chain {p : Program} {ch : Chain} {F : Flat} (R : PhiOfRun nm p ch F) {i : Nat}
    {env : Env} (henv : envAt p i = .ok env) {known : List (String × Option Chain)}
    (hrel : Pw (NameRel p) known env) {f : Expr} (hu : Unfolds known i f ch) :
    ∃ s : Sol, Expr.eval env [] f = .ok (.sol s) ∧ s.heading = F.heading ∧
      (∀ x, FitsCells F.cells x → (substitute F x ∈ s.candidates ↔ acceptsOf p ch (substitute F x) = .ok true)) ∧
      (∀ c ∈ s.candidates, ∃ x, FitsCells F.cells x ∧ Tuple.Over F.cells.attrs x ∧ substitute F x = c) := by
  have hFh : F.heading = R.data.heading ++ R.u.heading := congrArg Flat.heading R.hF
  have hsame : ∀ {data u picks}, omegaOf p ch = .ok (data, u, picks) →
      data = R.data ∧ u = R.u ∧ picks = R.picks := by
    intro data u picks hom
    rw [R.hom] at hom
    simp only [Except.ok.injEq, Prod.mk.injEq] at hom
    exact ⟨hom.1.symm, hom.2.1.symm, hom.2.2.symm⟩
  obtain ⟨v, hv⟩ := eval_ok_of henv hrel hu (fun _ => ⟨_, R.hom⟩) (by
    intro data u picks hom lv hlv hst
    obtain ⟨rfl, rfl, rfl⟩ := hsame hom
    refine ⟨?_, fun c hc' => ?_⟩
    · obtain ⟨s, env', he, hck, _⟩ := Pw.exists_left R.hconds lv hlv
      rw [hst, henv] at he
      cases he
      exact hck
    · rw [← hFh] at hc'
      obtain ⟨x, hx, _, rfl⟩ := phi_cells_onto R hc'
      obtain ⟨bs, hU, _, _⟩ := square_parts R hx
      obtain ⟨b, env', he, hb⟩ := Pw.exists_left hU lv hlv
      rw [hst, henv] at he
      cases he
      exact ⟨b, hb⟩)
  obtain ⟨s, data, u, picks, rfl, hom, hh, hcs⟩ := sem_of_eval henv hrel hu hv
  obtain ⟨rfl, rfl, rfl⟩ := hsame hom
  refine ⟨s, hv, by rw [hh, hFh], fun x hx => ?_, fun c hc' => ?_⟩
  · obtain ⟨bs, hU, _, hacc⟩ := square_parts R hx
    rw [hcs, List.mem_filter, ← hFh, phi_cells_into R hx, hacc]
    unfold levelsB
    rw [levels_all hU]
    simp only [copiesB, List.all_eq_true, okB_true, Except.ok.injEq, Bool.and_eq_true]
  · rw [hcs, List.mem_filter, ← hFh] at hc'
    exact phi_cells_onto R hc'.1

/-- **Theorem B′** (B lifts to the evaluator). When φ succeeds on statement `k` and the earlier
statements have run, statement `k` evaluates, without refusal, to a
solution set with φ's heading; an assignment that gives every cell a value in its domain
gives one of its candidates exactly when `accepts` gives `.ok true`; and every candidate
is given by such an assignment, over exactly the cells. -/
theorem phi_lift {p : Program} {k : Nat} {F : Flat} (h : phi p k = .ok F) {env : Env}
    (hrun : runProgram (p.take k) = .ok env) :
    ∃ (hk : k < p.length) (s : Sol), Expr.eval env.reverse [] (p[k]'hk).2 = .ok (.sol s) ∧
      s.heading = F.heading ∧
      (∀ x, FitsCells F.cells x → (substitute F x ∈ s.candidates ↔ accepts p k (substitute F x) = .ok true)) ∧
      (∀ c ∈ s.candidates, ∃ x, FitsCells F.cells x ∧ Tuple.Over F.cells.attrs x ∧ substitute F x = c) := by
  obtain ⟨R⟩ := phi_spec h
  obtain ⟨hk, hc⟩ := statementChain_spec R.hch
  have henv : envAt p k = .ok env.reverse := by simp [envAt, hrun, Except.map]
  obtain ⟨s, hv, hh, hin, hon⟩ := lift_of_chain R.toOf henv (run_rel p k hrun)
    ((chainOf_eq_some_iff _ _ _ _).mp hc)
  exact ⟨hk, s, hv, hh, fun x hx => by rw [accepts_of_chain R.hch]; exact hin x hx, hon⟩

end Rasso.Phi
