import Rasso.Phi.Sound.Gamma

/-!
# φ soundness: leaves do not read the candidate

A leaf of a condition (`IsLeaf`: it does not mention the marker and holds no solution-set
form) that does not name the candidate's placeholder evaluates the same whichever
candidate is bound. So φ may evaluate it once, with an empty candidate bound
(`Ctx.condEnv`), and the result is what the concrete evaluator gives for every candidate.
-/

namespace Rasso.Phi

open Rasso

/-- The environment of a condition, with the candidate `v` bound. -/
def candEnv (env : Env) (v : Val) : Env := inCondition ((candidateName, v) :: env)

theorem afterLeaf_cons_ne {n : String} {w : Val} {e : Env} (hn : (n == leafName) = false) :
    afterLeaf ((n, w) :: e) = afterLeaf e := by
  simp only [afterLeaf]
  cases afterLeaf e <;> simp [hn]

theorem leafEnv_candEnv (env : Env) (v v' : Val) : leafEnv (candEnv env v) = leafEnv (candEnv env v') := by
  have h1 : (inConditionName == leafName) = false := by decide
  have h2 : (candidateName == leafName) = false := by decide
  simp only [leafEnv, candEnv, inCondition, afterLeaf_cons_ne h1, afterLeaf_cons_ne h2]
  cases afterLeaf env with
  | some e => rfl
  | none => simp [inConditionName, candidateName]

theorem splice_congr {E E' : Env} (h : leafEnv E = leafEnv E') : ∀ (a : Agg), a.splice E = a.splice E'
  | .hasSubset r => by rw [Agg.splice, Agg.splice, h]
  | .call op args => by
    rw [Agg.splice, Agg.splice]
    have : (args.attach.mapM fun ⟨x, _⟩ => x.splice E) = args.attach.mapM fun ⟨x, _⟩ => x.splice E' := by
      congr 1; funext ⟨x, hx⟩; exact splice_congr h x
    rw [this]
  | .attr _ => by simp [Agg.splice]
  | .val _ => by simp [Agg.splice]
  | .agg _ _ => by simp [Agg.splice]
termination_by a => sizeOf a
decreasing_by
  all_goals simp_wf
  have := List.sizeOf_lt_of_mem hx; omega

theorem exprsAnySub_false {P : Expr → Bool} : ∀ {es : List Expr}, exprsAnySub P es = false →
    ∀ e ∈ es, e.anySub P = false
  | [], _ => by simp
  | e :: es, h => by
    simp only [exprsAnySub, Bool.or_eq_false_iff] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact exprsAnySub_false h.2 x hx

theorem mapM_congr_mem {α β ε : Type} {f g : α → Except ε β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapM_cons, h a List.mem_cons_self,
      mapM_congr_mem (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- The three things a leaf avoids, at one position. -/
structure Avoids (m f : Expr) : Prop where
  cand : f.anySub (·.beq (.name candidateName)) = false
  marker : f.anySub (·.beq m) = false
  sol : f.anySub Expr.isSolForm = false

mutual
theorem eval_cand_irrel (env : Env) (m : Expr) (v v' : Val) :
    ∀ (f : Expr), Avoids m f → Expr.eval (candEnv env v) [m] f = Expr.eval (candEnv env v') [m] f
  | f, ⟨h1, h2, h3⟩ => by
    have htg : [m].any f.beq = false := by
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      have := h2; unfold Expr.anySub at this; split at this <;> simp_all
    rw [Expr.eval.eq_def (candEnv env v) [m] f, Expr.eval.eq_def (candEnv env v') [m] f, htg]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases f with
    | name n =>
      dsimp only
      have hn : n ≠ candidateName := by
        intro e; subst e; simp [Expr.anySub, Expr.beq] at h1
      have hl : ∀ w, (candEnv env w).lookup n =
          if n = inConditionName then some (.db []) else env.lookup n := by
        intro w
        by_cases hc : n = inConditionName
        · subst hc; simp [candEnv, inCondition]
        · have : (n == candidateName) = false := by simpa using hn
          have : (n == inConditionName) = false := by simpa using hc
          simp [candEnv, inCondition, List.lookup, *]
      simp only [hl]
    | omega hd =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [evalHeading_cand_irrel env m v v' hd h1.2 h2.2 h3.2]
    | omegaWhere hd t =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [evalHeading_cand_irrel env m v v' hd h1.2 h2.2 h3.2]
    | omegaRows hd rows =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [evalHeading_cand_irrel env m v v' hd h1.2 h2.2 h3.2]
    | select p e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [eval_cand_irrel env m v v' e ⟨h1.2, h2.2, h3.2⟩]
    | project as e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [eval_cand_irrel env m v v' e ⟨h1.2, h2.2, h3.2⟩]
    | rename ren e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [eval_cand_irrel env m v v' e ⟨h1.2, h2.2, h3.2⟩]
    | nary op es =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      have : es.mapM (Expr.eval (candEnv env v) [m]) = es.mapM (Expr.eval (candEnv env v') [m]) := by
        apply mapM_congr_mem
        intro e he
        exact eval_cand_irrel env m v v' e ⟨exprsAnySub_false h1.2 e he,
          exprsAnySub_false h2.2 e he, exprsAnySub_false h3.2 e he⟩
      simp only [this]
    | gamma by_ ex res e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [eval_cand_irrel env m v v' e ⟨h1.2, h2.2, h3.2⟩,
        splice_congr (leafEnv_candEnv env v v') ex]
      simp [candEnv, inCondition]
    | extend res t e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [eval_cand_irrel env m v v' e ⟨h1.2, h2.2, h3.2⟩]
    | enum c key e =>
      dsimp only
      cases key with
      | none =>
        dsimp only
        simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
        rw [eval_cand_irrel env m v v' e ⟨h1.2, h2.2, h3.2⟩]
      | some k =>
        try dsimp only
        simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
        rw [eval_cand_irrel env m v v' e ⟨h1.2, h2.2, h3.2⟩]
    | forget e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [eval_cand_irrel env m v v' e ⟨h1.2, h2.2, h3.2⟩]
    | lift e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [eval_cand_irrel env m v v' e ⟨h1.2, h2.2, h3.2⟩]
    | flatten rank e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [eval_cand_irrel env m v v' e ⟨h1.2, h2.2, h3.2⟩]
    | flattenMsol rank e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [eval_cand_irrel env m v v' e ⟨h1.2, h2.2, h3.2⟩]
    | dbRef n e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h2 h3
      rw [eval_cand_irrel env m v v' e ⟨h1.2, h2.2, h3.2⟩]
    | omegaSol _ _ => simp [Expr.anySub, Expr.isSolForm] at h3
    | sigmaSol _ _ => simp [Expr.anySub, Expr.isSolForm] at h3
    | enumSol _ k _ => cases k <;> simp [Expr.anySub, Expr.isSolForm] at h3
    | omegaMsol _ c => cases c <;> simp [Expr.anySub, Expr.isSolForm] at h3
    | sigmaMsol _ _ => simp [Expr.anySub, Expr.isSolForm] at h3
    | enumMsol _ k _ => cases k <;> simp [Expr.anySub, Expr.isSolForm] at h3
termination_by f => sizeOf f

theorem evalHeading_cand_irrel (env : Env) (m : Expr) (v v' : Val) :
    ∀ (hd : List (String × DomExpr)),
      headAnySub (·.beq (.name candidateName)) hd = false → headAnySub (·.beq m) hd = false →
      headAnySub Expr.isSolForm hd = false →
      evalHeading (candEnv env v) [m] hd = evalHeading (candEnv env v') [m] hd
  | [], _, _, _ => by rw [evalHeading, evalHeading]
  | (a, d) :: hd, h1, h2, h3 => by
    simp only [headAnySub, Bool.or_eq_false_iff] at h1 h2 h3
    rw [evalHeading, evalHeading, domEval_cand_irrel env m v v' d h1.1 h2.1 h3.1,
      evalHeading_cand_irrel env m v v' hd h1.2 h2.2 h3.2]
termination_by hd => sizeOf hd

theorem domEval_cand_irrel (env : Env) (m : Expr) (v v' : Val) :
    ∀ (d : DomExpr),
      d.anySub (·.beq (.name candidateName)) = false → d.anySub (·.beq m) = false →
      d.anySub Expr.isSolForm = false →
      d.eval (candEnv env v) [m] = d.eval (candEnv env v') [m]
  | .in_ e, h1, h2, h3 => by
    simp only [DomExpr.anySub] at h1 h2 h3
    rw [DomExpr.eval, DomExpr.eval, eval_cand_irrel env m v v' e ⟨h1, h2, h3⟩]
  | .kind _, _, _, _ => by rw [DomExpr.eval, DomExpr.eval]
  | .range _ _, _, _, _ => by rw [DomExpr.eval, DomExpr.eval]
  | .set _, _, _, _ => by rw [DomExpr.eval, DomExpr.eval]
termination_by d => sizeOf d
end

end Rasso.Phi
