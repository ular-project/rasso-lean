import Rasso.Phi.Sound.RelEval

/-!
# φ soundness: conditions

`sCond_sound`: if the symbolic candidate denotes `rc` and all its guards are true, the
Boolean term φ builds for a condition evaluates, under the assignment, to what the
evaluator gives for the condition with `rc` bound. `has_subset` also needs the evaluator's
own check (`Cond.checkSubsets`): the required relation has the candidate's attributes.
-/

namespace Rasso.Phi

open Rasso

theorem allM_pw {α : Type} {f : α → Except String Bool} :
    ∀ {l : List α} {bs : List Bool}, Pw (fun a b => f a = .ok b) l bs → l.allM f = .ok (bs.all id)
  | [], [], .nil => rfl
  | _ :: _, b :: _, .cons h hl => by
    rw [List.allM_cons]
    simp only [h, bind, Except.bind]
    cases b
    · rfl
    · simpa using allM_pw hl

theorem anyM_pw {α : Type} {f : α → Except String Bool} :
    ∀ {l : List α} {bs : List Bool}, Pw (fun a b => f a = .ok b) l bs → l.anyM f = .ok (bs.any id)
  | [], [], .nil => rfl
  | _ :: _, b :: _, .cons h hl => by
    rw [List.anyM_cons]
    simp only [h, bind, Except.bind]
    cases b
    · simpa using anyM_pw hl
    · rfl

theorem forM_ok_mem {α : Type} {f : α → Except String PUnit} :
    ∀ {l : List α}, l.forM f = .ok () → ∀ a ∈ l, f a = .ok ()
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.forM] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i u hu
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hu
    · exact forM_ok_mem h b hb

/-- An `and`/`or` of conditions: each operand's term has the operand's value. -/
theorem andor_terms {x : Tuple} {E : Env} {tg : List Expr} {c : Ctx} {cs : List Cond} {ts : List Term}
    (hts : Pw (fun (a : {x // x ∈ cs}) t => sCond c a.1 = .ok t) cs.attach ts)
    (ih : ∀ a ∈ cs, ∀ {t}, sCond c a = .ok t → ∃ b, t.eval x = .ok (.bool b) ∧ a.eval E tg = .ok b) :
    ∃ bs : List Bool, ts.mapM (Term.eval x) = .ok (bs.map .bool) ∧
      Pw (fun (a : {x // x ∈ cs}) b => a.1.eval E tg = .ok b) cs.attach bs := by
  obtain ⟨bs, hT, hU⟩ := Pw.build (T := fun t b => t.eval x = .ok (.bool b))
    (U := fun (a : {x // x ∈ cs}) b => a.1.eval E tg = .ok b)
    (fun a t a' ht ha' => by
      subst a'
      obtain ⟨b, h1, h2⟩ := ih a.1 a.2 ht
      exact ⟨b, h1, h2⟩) hts (Pw.refl' cs.attach)
  exact ⟨bs, mapM_of_pw hT, hU⟩

theorem eq_single_of_nodup {α : Type} {u : α} : ∀ {l : List α}, l.Nodup → (∀ t, t ∈ [u] ↔ t ∈ l) → l = [u]
  | [], _, h => absurd ((h u).mp List.mem_cons_self) (by simp)
  | t :: l, hn, h => by
    have ht : t = u := by simpa using (h t).mpr List.mem_cons_self
    subst ht
    cases l with
    | nil => rfl
    | cons t' l =>
      have : t' = t := by simpa using (h t').mpr (List.mem_cons_of_mem _ List.mem_cons_self)
      subst this
      exact absurd List.mem_cons_self (List.nodup_cons.mp hn).1

theorem Pw.of_map_left {α β γ : Type} {R : β → γ → Prop} {F : α → β} :
    ∀ {l : List α} {m : List γ}, Pw R (l.map F) m → Pw (fun a c => R (F a) c) l m
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hl => .cons h (Pw.of_map_left hl)

theorem Pw.flip {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Pw R l m → Pw (fun b a => R a b) m l
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hl => .cons h (Pw.flip hl)

theorem leafEnv_candEnv_env (env : Env) (v : Val) : leafEnv (candEnv env v) = leafEnv env := by
  have h1 : (inConditionName == leafName) = false := by decide
  have h2 : (candidateName == leafName) = false := by decide
  simp only [leafEnv, candEnv, inCondition, afterLeaf_cons_ne h1, afterLeaf_cons_ne h2]
  cases afterLeaf env with
  | some e => rfl
  | none => simp [inConditionName, candidateName]

theorem ofFinrel_rows {r : Finrel} {R : SRel} (h : ofFinrel r = .ok R) :
    R.rows = r.tuples.map (fun t => (r.heading.map fun p => (p.1, Term.val ((t.get? p.1).getD default)), tt)) ∧
      r.heading.attrs.Nodup ∧ ∀ t ∈ r.tuples, t = fitTuple r.heading t := by
  simp only [ofFinrel, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hn
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hfit
  cases h
  exact ⟨rfl, nodup_of_eraseDups (by simpa [Heading.attrs] using hn), by simpa using hfit⟩

theorem matchesAll_fit {A : List String} {u t : Tuple} {h : Heading} (hu : AttrsOf A u)
    (hA : ∀ a, a ∈ A ↔ a ∈ h.attrs) (hn : h.attrs.Nodup) (ht : t = fitTuple h t) :
    matchesAll u (h.map fun p => (p.1, (t.get? p.1).getD default)) = true ↔ u = t := by
  have htg := fit_get? hn ht
  have hts : Tuple.Sorted t := by
    rw [ht]; exact Tuple.sorted_ofPairs (by simpa [List.map_map, Function.comp_def, Heading.attrs] using hn)
  simp only [matchesAll, List.all_map, List.all_eq_true, Function.comp_def, beq_iff_eq]
  constructor
  · intro hm
    refine Tuple.ext_get? hu.1 hts fun a => ?_
    by_cases ha : a ∈ h.attrs
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      rw [hm p hp, htg]; simp [ha]
    · rw [htg]; simp only [ha, ↓reduceIte]
      cases hg : u.get? a with
      | none => rfl
      | some _ => exact absurd ((hA a).mp ((hu.2 a).mp (by simp [hg]))) ha
  · rintro rfl p hp
    have ha : p.1 ∈ h.attrs := List.mem_map_of_mem hp
    rw [htg]; simp [ha]

theorem sCond_sound_lt {c : Ctx} {x : Tuple} (hx : CellsOk c.kinds x) {E : Env} (hok : CtxOk c x E)
    (htt : ∀ m R, c.cand = some (m, R) → R.rows.all (isTrue ·.2) = true) (n : Nat) :
    ∀ (cond : Cond), sizeOf cond < n →
      (∀ m R, c.cand = some (m, R) → cond.checkSubsets c.env R.heading = .ok ()) →
      ∀ {s : Term}, sCond c cond = .ok s →
        ∃ b, s.eval x = .ok (.bool b) ∧ Cond.eval E c.tg cond = .ok b := by
  induction n with
  | zero => intro cond hn; omega
  | succ n ih =>
  intro cond hn hck s h
  cases cond with
  | and cs =>
    rw [sCond] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i ts hts
    have := mk_eq h; subst this
    have hck' : ∀ a ∈ cs, ∀ m R, c.cand = some (m, R) → a.checkSubsets c.env R.heading = .ok () := by
      intro a ha m R hc
      have := hck m R hc
      rw [Cond.checkSubsets] at this
      exact forM_ok_mem this ⟨a, ha⟩ (List.mem_attach _ _)
    obtain ⟨bs, hm, hpw⟩ := andor_terms (x := x) (E := E) (tg := c.tg)
      (Pw.imp (fun a t e => e) (mapM_pw hts))
      (fun a ha t ht => ih a (by have := List.sizeOf_lt_of_mem ha; simp only [Cond.and.sizeOf_spec] at hn; omega)
        (hck' a ha) ht)
    refine ⟨bs.all id, ?_, ?_⟩
    · have := applyOp_andor_bools true bs
      simp only [opName, boolSem, ↓reduceIte] at this
      rw [eval_call]; simp [hm, bind, Except.bind, this]
    · rw [Cond.eval]; exact allM_pw hpw
  | or cs =>
    rw [sCond] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i ts hts
    have := mk_eq h; subst this
    have hck' : ∀ a ∈ cs, ∀ m R, c.cand = some (m, R) → a.checkSubsets c.env R.heading = .ok () := by
      intro a ha m R hc
      have := hck m R hc
      rw [Cond.checkSubsets] at this
      exact forM_ok_mem this ⟨a, ha⟩ (List.mem_attach _ _)
    obtain ⟨bs, hm, hpw⟩ := andor_terms (x := x) (E := E) (tg := c.tg)
      (Pw.imp (fun a t e => e) (mapM_pw hts))
      (fun a ha t ht => ih a (by have := List.sizeOf_lt_of_mem ha; simp only [Cond.or.sizeOf_spec] at hn; omega)
        (hck' a ha) ht)
    refine ⟨bs.any id, ?_, ?_⟩
    · have := applyOp_andor_bools false bs
      simp only [opName, boolSem, Bool.false_eq_true, ↓reduceIte] at this
      rw [eval_call]; simp [hm, bind, Except.bind, this]
    · rw [Cond.eval]; exact anyM_pw hpw
  | not d =>
    rw [sCond] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i t ht
    have := mk_eq h; subst this
    obtain ⟨b, hb, hev⟩ := ih d (by simp only [Cond.not.sizeOf_spec] at hn; omega)
      (fun m R hc => by have := hck m R hc; rwa [Cond.checkSubsets] at this) ht
    refine ⟨!b, ?_, ?_⟩
    · rw [eval_call]; simp [hb, bind, Except.bind, applyOp, pure, Except.pure, asBool]
    · rw [Cond.eval]; simp [hev, bind, Except.bind, pure, Except.pure]
  | expr e =>
    rw [sCond] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    rename_i R hR
    obtain ⟨r, hre, hD⟩ := sRel_sound hx hok e hR
    obtain ⟨insts, hpw, _, hnd, hmem⟩ := hD.inst
    split at h
    · rename_i a d row g hh hrows
      rw [hrows] at hpw
      cases hpw with
      | @cons _ ub _ _ hgi hnil =>
      cases hnil
      cases hg : isTrue g
      · simp [hg, throw, throwThe, MonadExceptOf.throw] at h
      simp only [hg, ↓reduceIte, pure, Except.pure] at h
      cases hv : row.lookup a with
      | none => simp [hv, throw, throwThe, MonadExceptOf.throw] at h
      | some v =>
      simp only [hv] at h
      cases hks : termKinds c.kinds v with
      | error e => simp [hks] at h
      | ok ks =>
      simp only [hks] at h
      cases hs : subKinds ks [.bool]
      · simp [hs, throw, throwThe, MonadExceptOf.throw] at h
      simp only [hs, ↓reduceIte, Except.ok.injEq] at h
      subst h
      have hb : ub.2 = true := by
        have := hgi.2; rw [isTrue_eval hg x] at this
        simp only [Except.ok.injEq, Value.bool.injEq] at this; exact this.symm
      have hts : r.tuples = [ub.1] := by
        apply eq_single_of_nodup (Finrel.nodup_tuples r)
        intro t; rw [← hmem]
        rcases ub with ⟨u, b⟩; simp only at hb; subst hb
        simp [presentT]
      obtain ⟨val, hval, hget⟩ := hgi.1.some hv
      obtain ⟨val', hval', hk⟩ := termKinds_sound hx v hks
      rw [hval] at hval'; cases hval'
      obtain ⟨b, rfl⟩ := asBool_ok (hk.sub hs)
      refine ⟨b, hval, ?_⟩
      have hat : r.attrs = [a] := by simp [Finrel.attrs, ← hD.heading, hh, Heading.attrs]
      rw [Cond.eval]
      simp [hre, scalar, Val.asFinrel, hat, hts, hget, asBool, bind, Except.bind, pure, Except.pure]
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | hasSubset r =>
    rw [sCond] at h
    cases hcc : c.cand with
    | none => simp [hcc, throw, throwThe, MonadExceptOf.throw] at h
    | some mR =>
    obtain ⟨m, R⟩ := mR
    obtain ⟨rc, hlc, hc⟩ := hok.cand m R hcc
    have htt := htt m R hcc
    have hck := hck m R hcc
    simp only [hcc, bind, Except.bind] at h
    split at h
    · cases h
    rename_i v0 hv0
    split at h
    · cases h
    rename_i req hreq
    split at h
    · cases h
    rename_i reqS hreqS
    split at h
    · cases h
    rename_i terms hterms
    have := mk_eq h; subst this
    obtain ⟨hrows, hn, hfit⟩ := ofFinrel_rows hreqS
    -- the check: the required relation has the candidate's attributes
    rw [Cond.checkSubsets] at hck
    have hl0 : leafEnv c.condEnv = leafEnv c.env := by
      simp only [Ctx.condEnv, hcc]; exact leafEnv_candEnv_env c.env _
    have hv0E : Expr.eval (leafEnv E) [] r = .ok v0 := by rw [← hok.leafEnv]; exact hv0
    rw [hl0] at hv0
    simp only [hv0, hreq, bind, Except.bind, checkSubsetHeading] at hck
    have hA : ∀ a, a ∈ R.heading.attrs ↔ a ∈ req.heading.attrs := by
      split at hck
      · rename_i hok
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem,
          Finrel.attrs] at hok
        intro a
        exact ⟨hok.2 a, hok.1.2 a⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at hck
    -- the candidate's rows
    obtain ⟨insts, hpw, hsorted, _, hmem⟩ := hc.inst
    have hpres := presentT_all hpw htt
    have hri := rowsInst_of hpw
    have hattr : ∀ u ∈ insts.map (·.1), AttrsOf R.heading.attrs u := by
      intro u hu
      obtain ⟨ub, hub, rfl⟩ := List.mem_map.mp hu
      obtain ⟨rg, hrg, hgi⟩ := Pw.mem_right hpw hub
      have := attrsOf_inst hgi.1 (hsorted ub hub); rwa [hc.attrs rg hrg] at this
    have hany : ∀ t ∈ req.tuples, (insts.map (·.1)).any
        (matchesAll · (req.heading.map fun p => (p.1, (t.get? p.1).getD default))) = rc.tuples.contains t := by
      intro t ht
      rw [Bool.eq_iff_iff, List.any_eq_true, List.contains_iff_mem, ← hmem, hpres]
      constructor
      · rintro ⟨u, hu, hm⟩
        rw [(matchesAll_fit (hattr u hu) hA hn (hfit t ht)).mp hm] at hu; exact hu
      · intro hu
        exact ⟨t, hu, (matchesAll_fit (hattr t hu) hA hn (hfit t ht)).mpr rfl⟩
    rw [hrows] at hterms
    have hpt := Pw.of_map_left (mapM_pw hterms)
    have hev : Pw (fun t term => term.eval x = .ok (.bool (rc.tuples.contains t))) req.tuples terms := by
      refine Pw.imp (fun t term ⟨e, ht, _⟩ => ?_) (Pw.mono_mem (Q := fun _ => True) hpt (fun t ht => ht)
        (fun _ _ => trivial))
      simp only [List.filterMap_map, Function.comp_def, decided?, Option.map_some] at e
      have e' : sHas c.kinds (R.rows.map (·.1))
          (req.heading.map fun p => (p.1, (t.get? p.1).getD default)) = .ok term := by
        rw [← e]; congr 1
        simp
      have hmk : ∃ w, term.eval x = .ok w := by
        simp only [sHas, bind, Except.bind] at e'
        split at e'
        · cases e'
        · exact mk_sound hx e'
      obtain ⟨w, hw⟩ := hmk
      rw [hw, sHas_sound hri e' hw, hany t ht]
    refine ⟨req.tuples.all rc.tuples.contains, ?_, ?_⟩
    · have hm : terms.mapM (Term.eval x) = .ok ((req.tuples.map rc.tuples.contains).map Value.bool) := by
        rw [List.map_map]
        exact mapM_of_pw (g := fun t => Value.bool (rc.tuples.contains t)) (Pw.flip hev)
      have := applyOp_andor_bools true (req.tuples.map rc.tuples.contains)
      simp only [opName, boolSem, ↓reduceIte] at this
      rw [eval_call]; simp only [hm, bind, Except.bind, this]
      simp [List.all_map, Function.comp_def]
      congr 1
    · rw [Cond.eval]
      simp [hlc, hv0E, hreq, bind, Except.bind, pure, Except.pure]
      congr 1

theorem sCond_sound {c : Ctx} {x : Tuple} (hx : CellsOk c.kinds x) {E : Env} (hok : CtxOk c x E)
    (htt : ∀ m R, c.cand = some (m, R) → R.rows.all (isTrue ·.2) = true) (cond : Cond)
    (hck : ∀ m R, c.cand = some (m, R) → cond.checkSubsets c.env R.heading = .ok ()) {s : Term}
    (h : sCond c cond = .ok s) :
    ∃ b, s.eval x = .ok (.bool b) ∧ Cond.eval E c.tg cond = .ok b :=
  sCond_sound_lt hx hok htt (sizeOf cond + 1) cond (Nat.lt_succ_self _) hck h

/-- `sCond_sound` for a solution set's condition. -/
theorem sCond_sound_sol {env : Env} {kinds : Kinds} {m : Expr} {R : SRel} {x : Tuple}
    (hx : CellsOk kinds x) {rc : Finrel} (hc : Denotes x R rc) (htt : R.rows.all (isTrue ·.2) = true)
    (cond : Cond) (hck : cond.checkSubsets env R.heading = .ok ()) {s : Term}
    (h : sCond (Ctx.sol env kinds m R) cond = .ok s) :
    ∃ b, s.eval x = .ok (.bool b) ∧ Cond.eval (candEnv env (.finrel rc)) [m] cond = .ok b :=
  sCond_sound hx (ctxOk_sol hc) (fun m' R' h => by cases h; exact htt) cond
    (fun m' R' h => by cases h; exact hck) h

end Rasso.Phi
