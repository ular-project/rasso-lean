import Rasso.Phi.Sound.Leaf

/-!
# φ soundness: relational expressions over the candidate

`sRel_sound`: if the symbolic candidate denotes `rc`, the symbolic relation φ builds for a
relational expression denotes what the evaluator gives for it with `rc` bound.
-/

namespace Rasso.Phi

open Rasso

/-- What the concrete environment `E` gives, for φ's reading of a condition in `c` to be
sound under the assignment `x`: the candidate (if any) and each member denote what the
symbolic ones do; `E` is a condition's environment; its leaves evaluate as in `c.condEnv`. -/
structure CtxOk (c : Ctx) (x : Tuple) (E : Env) : Prop where
  cand : ∀ m R, c.cand = some (m, R) → ∃ rc, E.lookup candidateName = some (.finrel rc) ∧ Denotes x R rc
  named : ∀ n R, c.named.lookup n = some R → ∃ r, E.lookup n = some (.finrel r) ∧ Denotes x R r
  cond : E.lookup inConditionName = some (.db [])
  leafEnv : leafEnv c.condEnv = leafEnv E
  leaf : ∀ f, c.isLeaf f = true → f.anySub c.isBound = false → Expr.eval c.condEnv c.tg f = Expr.eval E c.tg f

/-- A leaf: evaluated once, in `c.condEnv`; the same in `E`. -/
theorem sLeaf_sound {c : Ctx} {x : Tuple} {E : Env} (hok : CtxOk c x E) {f : Expr} {R : SRel}
    (h : sLeaf c f = .ok R) : ∃ r, Expr.eval E c.tg f = .ok (.finrel r) ∧ Denotes x R r := by
  unfold sLeaf at h
  split at h
  · rename_i hl
    cases hs : f.anySub c.isBound
    · simp only [hs, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at h
      split at h
      · cases h
      rename_i v hv
      split at h
      · cases h
      rename_i r0 hr0
      rw [hok.leaf f hl hs] at hv
      have : v = .finrel r0 := by
        cases v <;> simp only [Val.asFinrel, Except.ok.injEq] at hr0 <;> first | (subst hr0; rfl) | cases hr0
      subst this
      exact ⟨r0, hv, ofFinrel_denotes h x⟩
    · simp only [hs, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      cases h
  · cases h

theorem join_fold {ks : Kinds} {x : Tuple} (hx : CellsOk ks x) {F : Finrel → Val → Except String Finrel}
    (hF : ∀ acc r, F acc (.finrel r) = acc.join r) :
    ∀ {Rs : List SRel} {rs : List Finrel}, Pw (Denotes x) Rs rs →
    ∀ {R0 : SRel} {r0 : Finrel} {J : SRel}, Denotes x R0 r0 → Rs.foldlM (sJoin ks) R0 = .ok J →
      ∃ q, (rs.map Val.finrel).foldlM F r0 = .ok q ∧ Denotes x J q
  | [], [], .nil, R0, r0, J, h0, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨r0, rfl, h0⟩
  | R :: Rs, r :: rs, .cons hR hRs, R0, r0, J, h0, h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    rename_i R1 hR1
    obtain ⟨q1, hq1, hD1⟩ := sJoin_sound hx h0 hR hR1
    obtain ⟨q, hq, hD⟩ := join_fold hx hF hRs hD1 h
    refine ⟨q, ?_, hD⟩
    simp only [List.map_cons, List.foldlM_cons, hF, hq1, bind, Except.bind]
    exact hq

theorem mapM_of_pw {α β γ ε : Type} {f : α → Except ε γ} {g : β → γ} :
    ∀ {l : List α} {m : List β}, Pw (fun a b => f a = .ok (g b)) l m → l.mapM f = .ok (m.map g)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hl => by
    simp [List.mapM_cons, h, mapM_of_pw hl, bind, Except.bind, pure, Except.pure]

theorem all_map_finrel {p : Val → Bool} (hp : ∀ r, p (.finrel r) = true) (rs : List Finrel) :
    (rs.map Val.finrel).all p = true := by
  simp [List.all_map, hp]

theorem sRel_sound_lt {c : Ctx} {x : Tuple} (hx : CellsOk c.kinds x) {E : Env}
    (hok : CtxOk c x E) (n : Nat) : ∀ (f : Expr), sizeOf f < n → ∀ {R : SRel}, sRel c f = .ok R →
      ∃ r, Expr.eval E c.tg f = .ok (.finrel r) ∧ Denotes x R r := by
  induction n with
  | zero => intro f hf; omega
  | succ n ih =>
    intro f hf R h
    rw [sRel.eq_def] at h
    by_cases hm : c.tg.any f.beq = true
    · simp only [hm, ↓reduceIte] at h
      cases hc : c.cand with
      | none => simp [hc] at h
      | some mR =>
      obtain ⟨m, R0⟩ := mR
      simp only [hc, Except.ok.injEq] at h
      subst h
      obtain ⟨rc, hl, hD⟩ := hok.cand m R0 hc
      refine ⟨rc, ?_, hD⟩
      rw [Expr.eval.eq_def]
      simp only [hm, ↓reduceIte, hl]
    have hm' : c.tg.any f.beq = false := by simpa using hm
    simp only [hm', Bool.false_eq_true, ↓reduceIte] at h
    cases f with
    | name nn =>
      dsimp only at h
      cases hn : c.named.lookup nn with
      | none => simp only [hn] at h; exact sLeaf_sound hok h
      | some R0 =>
        simp only [hn, Except.ok.injEq] at h
        subst h
        obtain ⟨r, hl, hD⟩ := hok.named nn R0 hn
        refine ⟨r, ?_, hD⟩
        rw [Expr.eval.eq_def]
        simp only [hm', Bool.false_eq_true, ↓reduceIte, hl]
    | gamma by_ ex res e =>
      dsimp only at h
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      rename_i Re hRe
      obtain ⟨re, hre, hDe⟩ := ih e (by simp only [Expr.gamma.sizeOf_spec] at hf; omega) hRe
      have hev : ∀ g, re.gamma by_ ex (res.getD gammaDefaultName) = .ok g →
          Expr.eval E c.tg (.gamma by_ ex res e) = .ok (.finrel g) ∨ ex.hasSub = true := by
        intro g hg
        cases hs : ex.hasSub
        · left
          rw [Expr.eval.eq_def]
          simp only [hm', Bool.false_eq_true, ↓reduceIte]
          try dsimp only
          simp [hok.cond, hre, Val.asFinrel, hs, hg, bind, Except.bind, pure, Except.pure]
        · exact .inr rfl
      cases hs : ex.hasSub
      · simp only [hs, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at h
        obtain ⟨g, hg, hDg⟩ := sGamma_sound hx hDe h
        rcases hev g hg with he | he
        · exact ⟨g, he, hDg⟩
        · rw [hs] at he; cases he
      · simp only [hs, ↓reduceIte] at h
        split at h
        · cases h
        rename_i ex' hsp
        split at h
        · cases h
        rename_i u hfor
        simp only [pure, Except.pure] at h
        obtain ⟨g, hg, hDg⟩ := sGamma_sound hx hDe h
        refine ⟨g, ?_, hDg⟩
        have hall : ∀ a ∈ ex'.subsetAttrs, (Re.heading.lookup a).isNone = false := by
          have := forIn_of_ok (fun a => by
            cases hl : (Re.heading.lookup a).isNone
            · exact .inr (by simp [pure, Except.pure])
            · exact .inl ⟨_, by simp only [↓reduceIte]; rfl⟩) hfor
          intro a ha
          have h1 := this a ha
          cases hl : (Re.heading.lookup a).isNone
          · rfl
          · simp [hl, throw, throwThe, MonadExceptOf.throw] at h1
        rw [Expr.eval.eq_def]
        simp only [hm', Bool.false_eq_true, ↓reduceIte]
        try dsimp only
        simp only [hok.cond, Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
          hre, Val.asFinrel, hs, bind, Except.bind]
        rw [← splice_congr hok.leafEnv ex, hsp]
        simp only
        rw [forIn_yield (fun a ha => by
          simp [Finrel.domainOf?, ← hDe.heading, hall a ha, pure, Except.pure])]
        simp [hg, pure, Except.pure]
    | extend res t e =>
      dsimp only at h
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      rename_i Re hRe
      obtain ⟨re, hre, hDe⟩ := ih e (by simp only [Expr.extend.sizeOf_spec] at hf; omega) hRe
      obtain ⟨g, hg, hDg⟩ := sExtend_sound hx hDe h
      refine ⟨g, ?_, hDg⟩
      rw [Expr.eval.eq_def]
      simp only [hm', Bool.false_eq_true, ↓reduceIte]
      try dsimp only
      simp [hre, Val.asFinrel, hg, bind, Except.bind, pure, Except.pure]
    | nary op es =>
      cases op with
      | join =>
        dsimp only at h
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        rename_i Rs hRs
        have hRs' : es.mapM (sRel c) = .ok Rs := by
          rw [← hRs]; exact (mapM_congr2 (by simp) (fun i hi hi' => by simp)).symm
        have hpw : Pw (fun e R => ∃ r, Expr.eval E c.tg e = .ok (.finrel r) ∧
            Denotes x R r) es Rs :=
          Pw.imp (fun e R ⟨he, hmem, _⟩ => ih e (by
            have := List.sizeOf_lt_of_mem hmem; simp only [Expr.nary.sizeOf_spec] at hf; omega) he) (Pw.mono_mem (Q := fun _ => True)
            (mapM_pw hRs') (fun e he => he) (fun _ _ => trivial))
        cases Rs with
        | nil => simp [throw, throwThe, MonadExceptOf.throw] at h
        | cons R0 Rs' =>
          simp only at h
          obtain ⟨rs, hT, hU⟩ := Pw.build (T := Denotes x)
            (U := fun e r => Expr.eval E c.tg e = .ok (.finrel r))
            (fun e R e' ⟨r, h1, h2⟩ he' => by subst he'; exact ⟨r, h2, h1⟩) hpw (Pw.refl' es)
          cases hT with
          | cons hD0 hTs =>
          rename_i r0 rs'
          obtain ⟨q, hq, hDq⟩ := join_fold hx (F := fun acc w => do acc.join (← w.asFinrel "join"))
            (fun acc r => by simp [Val.asFinrel, bind, Except.bind]) hTs hD0 h
          refine ⟨q, ?_, hDq⟩
          have hmm : es.mapM (Expr.eval E c.tg) =
              .ok ((r0 :: rs').map Val.finrel) := mapM_of_pw hU
          rw [Expr.eval.eq_def]
          simp only [hm', Bool.false_eq_true, ↓reduceIte]
          try dsimp only
          simp only [bind, Except.bind] at hq ⊢
          simp only [hmm]
          simp only [Val.asFinrel] at hq
          simp [Val.asFinrel, hq, pure, Except.pure]
      | _ => dsimp only at h; exact sLeaf_sound hok h
    | _ => dsimp only at h; exact sLeaf_sound hok h

theorem sRel_sound {c : Ctx} {x : Tuple} (hx : CellsOk c.kinds x) {E : Env} (hok : CtxOk c x E)
    (f : Expr) {R : SRel} (h : sRel c f = .ok R) :
    ∃ r, Expr.eval E c.tg f = .ok (.finrel r) ∧ Denotes x R r :=
  sRel_sound_lt hx hok (sizeOf f + 1) f (Nat.lt_succ_self _) h

/-! ## A solution set's condition: one candidate, bound with `candEnv` -/

/-- A solution set's condition over the marker `m` and the symbolic candidate `R`. -/
abbrev Ctx.sol (env : Env) (kinds : Kinds) (m : Expr) (R : SRel) : Ctx := ⟨env, kinds, some (m, R), []⟩

theorem lookup_cond (env : Env) (v : Val) :
    (candEnv env v).lookup inConditionName = some (.db []) := by
  simp [candEnv, inCondition]

theorem lookup_cand (env : Env) (v : Val) : (candEnv env v).lookup candidateName = some v := by
  simp [candEnv, inCondition, List.lookup, inConditionName, candidateName]

theorem isBound_sol (env : Env) (kinds : Kinds) (m : Expr) (R : SRel) :
    (Ctx.sol env kinds m R).isBound = fun g => g.beq (.name candidateName) := by
  funext g; simp [Ctx.isBound]

theorem ctxOk_sol {env : Env} {kinds : Kinds} {m : Expr} {R : SRel} {x : Tuple} {rc : Finrel}
    (hc : Denotes x R rc) : CtxOk (Ctx.sol env kinds m R) x (candEnv env (.finrel rc)) where
  cand := by
    intro m' R' h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rc, lookup_cand env _, hc⟩
  named := by intro n R' h; simp at h
  cond := lookup_cond env _
  leafEnv := leafEnv_candEnv env _ _
  leaf := by
    intro f hl hb
    rw [isBound_sol] at hb
    have hav : Avoids m f := by
      simp only [Ctx.isLeaf, Ctx.tg, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true, Bool.not_eq_true'] at hl
      exact ⟨hb, hl.1, hl.2⟩
    exact eval_cand_irrel env m _ (.finrel rc) f hav

/-- `sRel_sound` for a solution set's condition. -/
theorem sRel_sound_sol {env : Env} {kinds : Kinds} {m : Expr} {R : SRel} {x : Tuple}
    (hx : CellsOk kinds x) {rc : Finrel} (hc : Denotes x R rc) (f : Expr) {S : SRel}
    (h : sRel (Ctx.sol env kinds m R) f = .ok S) :
    ∃ r, Expr.eval (candEnv env (.finrel rc)) [m] f = .ok (.finrel r) ∧ Denotes x S r :=
  sRel_sound hx (ctxOk_sol hc) f h

end Rasso.Phi
