import Rasso.Phi.Theorems.Square

/-!
# φ's theorems: the ℰ_sol key (K)

If `phiKey p j = .ok (F, t)` and the assignment `x` gives every
cell a value in its domain, then the term `t` evaluates under `x` to the value that Lean's
evaluator gives as the key of the candidate `substitute F x`, and neither refuses.
-/

namespace Rasso.Phi

open Rasso

variable {nm : String → Nat → String}

/-- **Theorem K.** φ's key term and the evaluator's key agree on every candidate φ can
describe, and neither refuses. -/
theorem phiKey_sound {p : Program} {j : Nat} {F : Flat} {t : Term} (h : phiKey p j = .ok (F, t))
    {x : Tuple} (hx : FitsCells F.cells x) :
    ∃ v, t.eval x = .ok v ∧ keyValue p j (substitute F x) = .ok v := by
  unfold phiKey at h
  unfold keyValue
  cases hk : keyOf p j with
  | none => simp [hk, throw, throwThe, MonadExceptOf.throw] at h
  | some r =>
  obtain ⟨ch, e, key⟩ := r
  simp only [hk, bind, Except.bind] at h ⊢
  split at h
  · cases h
  rename_i F' hF
  split at h
  · cases h
  rename_i env henv
  split at h
  · cases h
  split at h
  · cases h
  rename_i kinds hkinds
  split at h
  · cases h
  rename_i R hR
  obtain ⟨⟨data, u, picks, kinds', conds, hom, hnd, hfit, hcn, hkinds', hattrs, hconds, rfl⟩⟩ :=
    phiOf_spec hF
  split at h
  · rename_i a d row g hh hrows
    cases hg : isTrue g
    · simp [hg, throw, throwThe, MonadExceptOf.throw] at h
    simp only [hg, ↓reduceIte, pure, Except.pure] at h
    cases hv : row.lookup a with
    | none => simp [hv, throw, throwThe, MonadExceptOf.throw] at h
    | some v =>
    simp only [hv, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    dsimp only at hx hkinds hR ⊢
    have hrows' : (phiRows data).Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (Finrel.nodup_tuples data)
    have hfitr : ∀ t ∈ phiRows data, t = fitTuple data.heading t :=
      fun t ht => hfit t (List.mem_mergeSort.mp ht)
    have hden := cand_denotes hnd hfitr hrows' hx
    obtain ⟨r, hre, hD⟩ := sRel_sound_sol (env := env) (m := e) (cellsOk_of_fits hkinds hx) hden key hR
    obtain ⟨insts, hpw, _, hnd', hmem⟩ := hD.inst
    rw [hrows] at hpw
    cases hpw with
    | @cons _ ub _ _ hgi hnil =>
    cases hnil
    have hb : ub.2 = true := by
      have := hgi.2; rw [isTrue_eval hg x] at this
      simp only [Except.ok.injEq, Value.bool.injEq] at this; exact this.symm
    have hts : r.tuples = [ub.1] := by
      apply eq_single_of_nodup (Finrel.nodup_tuples r)
      intro t; rw [← hmem]
      rcases ub with ⟨u, b⟩; simp only at hb; subst hb
      simp [presentT]
    obtain ⟨val, hval, hget⟩ := hgi.1.some hv
    refine ⟨val, simpTerm_sound x v hval, ?_⟩
    have hat : r.attrs = [a] := by simp [Finrel.attrs, ← hD.heading, hh, Heading.attrs]
    rw [substitute_eq]
    simp only [show inCondition ((candidateName, Val.finrel _) :: env) = candEnv env (.finrel _) from rfl]
    simp [hre, scalar, Val.asFinrel, hat, hts, hget, bind, Except.bind, pure, Except.pure]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

end Rasso.Phi
