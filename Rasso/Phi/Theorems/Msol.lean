import Rasso.Phi.Theorems.Lift

/-!
# φ's theorems: a multi solution set (theorem M)

If `phiMsol p k = .ok M` and the assignment `x` gives every
cell a value in its domain, then the flat term evaluates under `x` to a bool `b`, and the
reference evaluator `acceptsMsol` gives `.ok b` on the database `msolSubstitute M x`.
-/

namespace Rasso.Phi

open Rasso

/-! ## Leaves do not read the members -/

/-- The environments `E` and `E'` agree on every name `Q` lets a leaf read, on the
condition marker, and on the leaf environment. -/
structure EnvAgree (Q : Expr → Bool) (E E' : Env) : Prop where
  name : ∀ n, Q (.name n) = false → E.lookup n = E'.lookup n
  cond : E.lookup inConditionName = E'.lookup inConditionName
  leaf : leafEnv E = leafEnv E'

mutual
/-- A leaf evaluates the same in two environments that agree on what it reads. -/
theorem eval_env_irrel {Q : Expr → Bool} {E E' : Env} (h : EnvAgree Q E E') :
    ∀ (f : Expr), f.anySub Q = false → f.anySub Expr.isSolForm = false → Expr.eval E [] f = Expr.eval E' [] f
  | f, h1, h3 => by
    rw [Expr.eval.eq_def E [] f, Expr.eval.eq_def E' [] f]
    simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte]
    cases f with
    | name n =>
      dsimp only
      have hq : Q (.name n) = false := by simpa [Expr.anySub] using h1
      rw [h.name n hq]
    | omega hd =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [evalHeading_env_irrel h hd h1.2 h3.2]
    | omegaWhere hd t =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [evalHeading_env_irrel h hd h1.2 h3.2]
    | omegaRows hd rows =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [evalHeading_env_irrel h hd h1.2 h3.2]
    | select p e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [eval_env_irrel h e h1.2 h3.2]
    | project as e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [eval_env_irrel h e h1.2 h3.2]
    | rename ren e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [eval_env_irrel h e h1.2 h3.2]
    | nary op es =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      have : es.mapM (Expr.eval E []) = es.mapM (Expr.eval E' []) := by
        apply mapM_congr_mem
        intro e he
        exact eval_env_irrel h e (exprsAnySub_false h1.2 e he) (exprsAnySub_false h3.2 e he)
      simp only [this]
    | gamma by_ ex res e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [eval_env_irrel h e h1.2 h3.2, splice_congr h.leaf ex, h.cond]
    | extend res t e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [eval_env_irrel h e h1.2 h3.2]
    | enum c key e =>
      dsimp only
      cases key with
      | none =>
        dsimp only
        simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
        rw [eval_env_irrel h e h1.2 h3.2]
      | some k =>
        try dsimp only
        simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
        rw [eval_env_irrel h e h1.2 h3.2]
    | forget e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [eval_env_irrel h e h1.2 h3.2]
    | lift e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [eval_env_irrel h e h1.2 h3.2]
    | flatten rank e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [eval_env_irrel h e h1.2 h3.2]
    | flattenMsol rank e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [eval_env_irrel h e h1.2 h3.2]
    | dbRef n e =>
      dsimp only
      simp only [Expr.anySub, Bool.or_eq_false_iff] at h1 h3
      rw [eval_env_irrel h e h1.2 h3.2]
    | omegaSol _ _ => simp [Expr.anySub, Expr.isSolForm] at h3
    | sigmaSol _ _ => simp [Expr.anySub, Expr.isSolForm] at h3
    | enumSol _ k _ => cases k <;> simp [Expr.anySub, Expr.isSolForm] at h3
    | omegaMsol _ c => cases c <;> simp [Expr.anySub, Expr.isSolForm] at h3
    | sigmaMsol _ _ => simp [Expr.anySub, Expr.isSolForm] at h3
    | enumMsol _ k _ => cases k <;> simp [Expr.anySub, Expr.isSolForm] at h3
termination_by f => sizeOf f

theorem evalHeading_env_irrel {Q : Expr → Bool} {E E' : Env} (h : EnvAgree Q E E') :
    ∀ (hd : List (String × DomExpr)), headAnySub Q hd = false → headAnySub Expr.isSolForm hd = false →
      evalHeading E [] hd = evalHeading E' [] hd
  | [], _, _ => by rw [evalHeading, evalHeading]
  | (a, d) :: hd, h1, h3 => by
    simp only [headAnySub, Bool.or_eq_false_iff] at h1 h3
    rw [evalHeading, evalHeading, domEval_env_irrel h d h1.1 h3.1, evalHeading_env_irrel h hd h1.2 h3.2]
termination_by hd => sizeOf hd

theorem domEval_env_irrel {Q : Expr → Bool} {E E' : Env} (h : EnvAgree Q E E') :
    ∀ (d : DomExpr), d.anySub Q = false → d.anySub Expr.isSolForm = false → d.eval E [] = d.eval E' []
  | .in_ e, h1, h3 => by
    simp only [DomExpr.anySub] at h1 h3
    rw [DomExpr.eval, DomExpr.eval, eval_env_irrel h e h1 h3]
  | .kind _, _, _ => by rw [DomExpr.eval, DomExpr.eval]
  | .range _ _, _, _ => by rw [DomExpr.eval, DomExpr.eval]
  | .set _, _, _ => by rw [DomExpr.eval, DomExpr.eval]
termination_by d => sizeOf d
end

/-! ## The condition's environment: `inCondition (bindDb db env)` -/

theorem lookup_append_left {β : Type} {n : String} {v : β} :
    ∀ {l : List (String × β)} (r : List (String × β)), l.lookup n = some v → (l ++ r).lookup n = some v
  | [], _, h => by simp at h
  | (a, b) :: l, r, h => by
    by_cases hna : n = a
    · subst hna; simpa [List.lookup] using h
    · have : (n == a) = false := by simpa using hna
      simp only [List.cons_append, List.lookup_cons, this] at h ⊢
      exact lookup_append_left r h

theorem lookup_append_right {β : Type} {n : String} :
    ∀ {l : List (String × β)} (r : List (String × β)), l.lookup n = none → (l ++ r).lookup n = r.lookup n
  | [], _, _ => rfl
  | (a, b) :: l, r, h => by
    by_cases hna : n = a
    · subst hna; simp [List.lookup] at h
    · have : (n == a) = false := by simpa using hna
      simp only [List.cons_append, List.lookup_cons, this] at h ⊢
      exact lookup_append_right r h

theorem afterLeaf_bindDb (env : Env) : ∀ (db : Db), (∀ q ∈ db, q.1 ≠ leafName) →
    afterLeaf (bindDb db env) = afterLeaf ((leafName, .db []) :: env)
  | [], _ => rfl
  | (n, r) :: db, h => by
    have hn : (n == leafName) = false := by simpa using h (n, r) List.mem_cons_self
    have ih := afterLeaf_bindDb env db fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [bindDb, List.map_cons, List.cons_append] at ih ⊢
    rw [afterLeaf_cons_ne hn, ih]

theorem afterLeaf_mark_isSome (env : Env) : (afterLeaf ((leafName, .db []) :: env)).isSome = true := by
  simp only [afterLeaf]
  cases afterLeaf env <;> simp

theorem leafEnv_bindDb (env : Env) {db db' : Db} (h : ∀ q ∈ db, q.1 ≠ leafName)
    (h' : ∀ q ∈ db', q.1 ≠ leafName) :
    leafEnv (inCondition (bindDb db env)) = leafEnv (inCondition (bindDb db' env)) := by
  have hc : (inConditionName == leafName) = false := by decide
  simp only [leafEnv, inCondition, afterLeaf_cons_ne hc, afterLeaf_bindDb env db h,
    afterLeaf_bindDb env db' h']
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (afterLeaf_mark_isSome env)
  rw [he]; rfl

theorem lookup_inCondition_bindDb_other {env : Env} {db : Db} {n : String} (hc : n ≠ inConditionName)
    (hn : n ∉ db.map (·.1)) :
    (inCondition (bindDb db env)).lookup n = ((leafName, Val.db []) :: env).lookup n := by
  have : (n == inConditionName) = false := by simpa using hc
  simp only [inCondition, List.lookup_cons, this, bindDb]
  apply lookup_append_right
  apply lookup_none_of_not_mem
  simpa [List.map_map, Function.comp_def] using hn

theorem lookup_inCondition_bindDb_mem {env : Env} {db : Db} {n : String} {r : Finrel}
    (hc : n ≠ inConditionName) (hl : db.lookup n = some r) :
    (inCondition (bindDb db env)).lookup n = some (.finrel r) := by
  have : (n == inConditionName) = false := by simpa using hc
  simp only [inCondition, List.lookup_cons, this, bindDb]
  apply lookup_append_left
  have := lookup_map_snd Val.finrel n db
  simp only [hl, Option.map_some] at this
  exact this

/-- The members' names avoid the evaluator's own bindings. -/
def NamesOk (names : List String) : Prop := ∀ n ∈ names, n ∉ reservedNames

/-- **The msol condition's environment** meets `CtxOk`: each member denotes its candidate,
the members' names are distinct and not reserved. -/
theorem ctxOk_msol {env : Env} {kinds : Kinds} {Fs : List (String × Flat)} {x : Tuple}
    (hok : NamesOk (Fs.map (·.1))) (hden : ∀ q ∈ Fs, Denotes x q.2.sym (substitute q.2 x)) :
    CtxOk ⟨env, kinds, none, Fs.map fun p => (p.1, p.2.sym)⟩ x
      (inCondition (bindDb (Fs.map fun p => (p.1, substitute p.2 x)) env)) := by
  have hres : ∀ n ∈ Fs.map (·.1), n ≠ candidateName ∧ n ≠ leafName ∧ n ≠ inConditionName := by
    intro n hn
    have := hok n hn
    simp only [reservedNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this
  have hdb0 : ∀ q ∈ (Fs.map fun p => (p.1, p.2.sym)).map (fun p => (p.1, Finrel.ofTuples p.2.heading [])),
      q.1 ≠ leafName := by
    intro q hq
    simp only [List.map_map, List.mem_map, Function.comp_def] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    exact (hres a.1 (List.mem_map_of_mem ha)).2.1
  have hdb : ∀ q ∈ Fs.map fun p => (p.1, substitute p.2 x), q.1 ≠ leafName := by
    intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    exact (hres a.1 (List.mem_map_of_mem ha)).2.1
  have hleaf : leafEnv (Ctx.condEnv ⟨env, kinds, none, Fs.map fun p => (p.1, p.2.sym)⟩) =
      leafEnv (inCondition (bindDb (Fs.map fun p => (p.1, substitute p.2 x)) env)) :=
    leafEnv_bindDb env hdb0 hdb
  refine ⟨fun m R h => (by cases h), ?_, (by simp [inCondition]), hleaf, ?_⟩
  · intro n R h
    have h' := h
    rw [lookup_map_snd Flat.sym n Fs] at h'
    cases hF : Fs.lookup n with
    | none => simp [hF] at h'
    | some F =>
    simp only [hF, Option.map_some, Option.some.injEq] at h'
    subst h'
    have hmem := lookup_some_mem hF
    have hn := hres n (List.mem_map_of_mem hmem)
    refine ⟨substitute F x, lookup_inCondition_bindDb_mem hn.2.2 ?_, hden (n, F) hmem⟩
    have := lookup_map_snd (fun F => substitute F x) n Fs
    simpa [hF] using this
  · intro f hl hb
    have hsol : f.anySub Expr.isSolForm = false := by
      simp only [Ctx.isLeaf, Ctx.tg, List.all_nil, Bool.true_and, Bool.not_eq_true'] at hl
      exact hl
    apply eval_env_irrel (Q := Ctx.isBound ⟨env, kinds, none, Fs.map fun p => (p.1, p.2.sym)⟩) _ f hb hsol
    refine ⟨fun n hq => ?_, by simp [Ctx.condEnv, inCondition], hleaf⟩
    simp only [Ctx.isBound, Bool.or_eq_false_iff, List.any_eq_false, List.mem_map] at hq
    have hnm : n ∉ Fs.map (·.1) := by
      intro hn
      obtain ⟨q, hq', rfl⟩ := List.mem_map.mp hn
      have := hq.2 (q.1, q.2.sym) ⟨q, hq', rfl⟩
      simp [Expr.beq] at this
    by_cases hc : n = inConditionName
    · subst hc; simp [Ctx.condEnv, inCondition]
    · simp only [Ctx.condEnv]
      rw [lookup_inCondition_bindDb_other hc (by simpa [List.map_map, Function.comp_def] using hnm),
        lookup_inCondition_bindDb_other hc (by simpa [List.map_map, Function.comp_def] using hnm)]

/-! ## What `phiMsolOf` checks and builds -/

variable {nm : String → Nat → String}

/-- A member's symbolic candidate denotes the candidate an assignment gives. -/
theorem member_denotes {p : Program} {ch : Chain} {F : Flat} (R : PhiOfRun nm p ch F) {x : Tuple}
    (hx : FitsCells F.cells x) : Denotes x F.sym (substitute F x) := by
  obtain ⟨data, u, picks, kinds, conds, hom, hnd, hfit, hcn, hkinds, hattrs, hconds, rfl⟩ := R
  have hrows : (phiRows data).Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (Finrel.nodup_tuples data)
  have hfitr : ∀ t ∈ phiRows data, t = fitTuple data.heading t :=
    fun t ht => hfit t (List.mem_mergeSort.mp ht)
  rw [substitute_eq]
  exact cand_denotes hnd hfitr hrows hx

/-- What `phiMsolOf p mc = .ok M` tells. -/
structure MsolRun (p : Program) (mc : MChain) (M : MFlat) where
  Fs : List (String × Flat)
  kinds : Kinds
  conds : List Term
  hne : mc.members ≠ []
  hI : "I" ∉ mc.members.map (·.1)
  hnames : NamesOk (mc.members.map (·.1))
  hnd : (mc.members.map (·.1)).Nodup
  hFs : Pw (fun (q : String × Chain) (r : String × Flat) => r.1 = q.1 ∧
    phiOf (memberCell q.1) p q.2 = .ok r.2) mc.members Fs
  hcn : Heading.attrs (Fs.flatMap (·.2.cells)) |>.Nodup
  hkinds : cellKinds (Fs.flatMap (·.2.cells)) = .ok kinds
  hconds : Pw (fun (lv : MLevel) s => ∃ env, envAt p lv.stmt = .ok env ∧
    sCond ⟨env, kinds, none, Fs.map fun p => (p.1, p.2.sym)⟩ lv.cond = .ok s) mc.levels conds
  hM : M = ⟨Fs, Fs.flatMap (·.2.cells), simpTerm (.call "and" (Fs.map (·.2.term) ++ conds))⟩

theorem phiMsolOf_spec {p : Program} {mc : MChain} {M : MFlat} (h : phiMsolOf p mc = .ok M) :
    Nonempty (MsolRun p mc M) := by
  unfold phiMsolOf at h
  cases hne : mc.members.isEmpty
  case true => simp only [hne, ↓reduceIte] at h; cases h
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
  cases hI : (mc.members.map (·.1)).contains "I"
  case true => simp only [hI, ↓reduceIte] at h; cases h
  simp only [hI, Bool.false_eq_true, ↓reduceIte] at h
  cases hnd : ((mc.members.map (·.1)).eraseDups.length != (mc.members.map (·.1)).length)
  case true => simp only [hnd, ↓reduceIte] at h; cases h
  simp only [hnd, Bool.false_eq_true, ↓reduceIte] at h
  cases hres : (mc.members.map (·.1)).any reservedNames.contains
  case true => simp only [hres, ↓reduceIte] at h; cases h
  simp only [hres, Bool.false_eq_true, ↓reduceIte] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i Fs hFs
  cases hcn : ((Heading.attrs (Fs.flatMap fun x => x.snd.cells)).eraseDups.length != (Fs.flatMap fun x => x.snd.cells).length)
  case true => simp only [hcn, ↓reduceIte] at h; cases h
  simp only [hcn, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · cases h
  rename_i kinds hkinds
  split at h
  · cases h
  rename_i conds hconds
  simp only [pure, Except.pure, Except.ok.injEq] at h
  refine ⟨⟨Fs, kinds, conds, ?_, by simpa using hI, ?_, nodup_of_eraseDups (by simp only [hnd]; decide), ?_,
    nodup_of_eraseDups (by simp only [Heading.attrs, List.length_map] at hcn ⊢; simp only [hcn]; decide), hkinds, ?_, h.symm⟩⟩

  · intro e; simp [e] at hne
  · intro n hn hr
    have := hres
    simp only [List.any_eq_false] at this
    have h2 := this n hn
    simp [hr] at h2
  · refine Pw.imp (fun q r hq => ?_) (mapM_pw hFs)
    obtain ⟨n, ch⟩ := q
    simp only at hq
    split at hq
    · cases hq
    rename_i F hF
    simp only [pure, Except.pure, Except.ok.injEq] at hq
    subst hq
    exact ⟨rfl, hF⟩
  · refine Pw.imp (fun lv s hs => ?_) (mapM_pw hconds)
    split at hs
    · cases hs
    rename_i env henv
    exact ⟨env, henv, hs⟩

/-! ## Theorem M -/

theorem fits_member {Fs : List (String × Flat)} {x : Tuple}
    (hcn : Heading.attrs (Fs.flatMap (·.2.cells)) |>.Nodup) (hx : FitsCells (Fs.flatMap (·.2.cells)) x)
    {r : String × Flat} (hr : r ∈ Fs) : FitsCells r.2.cells x := by
  intro c d hl
  apply hx
  apply lookup_of_mem_nodup hcn
  exact List.mem_flatMap.mpr ⟨r, hr, lookup_some_mem hl⟩

theorem Pw.map_fst_eq {α β γ : Type} {R : α × β → α × γ → Prop} (hR : ∀ a b, R a b → b.1 = a.1) :
    ∀ {l : List (α × β)} {m : List (α × γ)}, Pw R l m → m.map (·.1) = l.map (·.1)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hl => by simp [hR _ _ h, Pw.map_fst_eq hR hl]

/-- `acceptsMsolOf`, unfolded: each member's bool, then each condition's. -/
theorem acceptsMsolOf_eq {p : Program} {mc : MChain} {db : Db} {bm : List Bool}
    (h1 : Pw (fun (q : String × Chain) b => ∃ r, db.lookup q.1 = some r ∧ acceptsOf p q.2 r = .ok b)
      mc.members bm)
    {bl : List Bool} (h2 : Pw (fun (lv : MLevel) b => ∃ env, envAt p lv.stmt = .ok env ∧
      lv.cond.eval (inCondition (bindDb db env)) [] = .ok b) mc.levels bl) :
    acceptsMsolOf p mc db = .ok (bm.all id && bl.all id) := by
  unfold acceptsMsolOf
  simp only [bind, Except.bind]
  rw [forIn_early (bs := bm) (s1 := (some false, ())) (Pw.imp (fun q b ⟨r, hl, hb⟩ => by
    obtain ⟨n, ch⟩ := q
    simp only at hl hb ⊢
    simp only [hl, hb]; cases b <;> rfl) h1)]
  cases hbm : bm.all id
  · rfl
  · simp only [↓reduceIte]
    rw [forIn_early (bs := bl) (s1 := (some false, ())) (Pw.imp (fun lv b ⟨env, he, hb⟩ => by
      simp only [he, hb]; cases b <;> rfl) h2)]
    cases bl.all id <;> rfl

/-- **Theorem M** for a chain: when φ succeeds, under every assignment that gives each cell a
value in its domain, the flat term and the reference evaluator agree on the database the
assignment gives, and neither refuses. -/
theorem msol_parts {p : Program} {mc : MChain} {M : MFlat} (h : phiMsolOf p mc = .ok M) {x : Tuple}
    (hx : FitsCells M.cells x) :
    ∃ bm bl, Pw (fun (q : String × Chain) b => ∃ r, (msolSubstitute M x).lookup q.1 = some r ∧
        acceptsOf p q.2 r = .ok b) mc.members bm ∧
      Pw (fun (lv : MLevel) b => ∃ env, envAt p lv.stmt = .ok env ∧
        lv.cond.eval (inCondition (bindDb (msolSubstitute M x) env)) [] = .ok b) mc.levels bl ∧
      M.term.eval x = .ok (.bool ((bm ++ bl).all id)) := by
  obtain ⟨R⟩ := phiMsolOf_spec h
  obtain ⟨Fs, kinds, conds, _, _, hnames, hnd, hFs, hcn, hkinds, hconds, rfl⟩ := R
  dsimp only at hx ⊢
  have hfst : Fs.map (·.1) = mc.members.map (·.1) := Pw.map_fst_eq (fun a b h => h.1) hFs
  have hndF : (Fs.map (·.1)).Nodup := by rw [hfst]; exact hnd
  have hxr : ∀ r ∈ Fs, FitsCells r.2.cells x := fun r hr => fits_member hcn hx hr
  have hrun : ∀ r ∈ Fs, ∃ ch, phiOf (memberCell r.1) p ch = .ok r.2 := by
    intro r hr
    obtain ⟨q, _, he, hq⟩ := Pw.mem_right hFs hr
    exact ⟨q.2, by rw [he]; exact hq⟩
  have hden : ∀ r ∈ Fs, Denotes x r.2.sym (substitute r.2 x) := by
    intro r hr
    obtain ⟨ch, hch⟩ := hrun r hr
    obtain ⟨Rr⟩ := phiOf_spec hch
    exact member_denotes Rr (hxr r hr)
  have hlook : ∀ r ∈ Fs, (Fs.map fun p => (p.1, substitute p.2 x)).lookup r.1 = some (substitute r.2 x) := by
    intro r hr
    apply lookup_of_mem_nodup
    · simpa [List.map_map, Function.comp_def] using hndF
    · exact List.mem_map.mpr ⟨r, hr, rfl⟩
  -- the members
  obtain ⟨bm, hTm, hUm⟩ := Pw.build (T := fun (r : String × Flat) b => r.2.term.eval x = .ok (.bool b))
    (U := fun (q : String × Chain) b => ∃ r, (Fs.map fun p => (p.1, substitute p.2 x)).lookup q.1 = some r ∧
      acceptsOf p q.2 r = .ok b)
    (fun q r q' ⟨⟨he, hphi⟩, _, hr⟩ hq' => by
      subst hq'
      obtain ⟨Rr⟩ := phiOf_spec hphi
      obtain ⟨bs, _, ht, ha⟩ := square_parts Rr (hxr r hr)
      exact ⟨_, ht, substitute r.2 x, by rw [← he]; exact hlook r hr, ha⟩)
    (Pw.mono_mem (P := fun _ => True) (Q := fun r => r ∈ Fs) hFs (fun _ _ => trivial) (fun _ h => h))
    (Pw.refl' mc.members)
  -- the conditions
  have hcok : CellsOk kinds x := cellsOk_of_fits hkinds hx
  obtain ⟨bl, hTc, hUc⟩ := Pw.build (T := fun s b => s.eval x = .ok (.bool b))
    (U := fun (lv : MLevel) b => ∃ env, envAt p lv.stmt = .ok env ∧
      lv.cond.eval (inCondition (bindDb (Fs.map fun p => (p.1, substitute p.2 x)) env)) [] = .ok b)
    (fun (lv : MLevel) s (lv' : MLevel) ⟨env, he, hs⟩ e => by
      subst lv'
      have hok := ctxOk_msol (env := env) (kinds := kinds) (Fs := Fs) (x := x)
        (by rw [hfst]; exact hnames) hden
      obtain ⟨b, hb, hc⟩ := sCond_sound hcok hok (fun m R h => by cases h) lv.cond
        (fun m R h => by cases h) hs
      exact ⟨b, hb, env, he, hc⟩) hconds (Pw.refl' mc.levels)
  -- the term
  have hargs := mapM_of_pw (g := Value.bool) (Pw.append (Pw.map_left (F := fun r : String × Flat => r.2.term) hTm) hTc)
  have hand : (Term.call "and" (Fs.map (·.2.term) ++ conds)).eval x = .ok (.bool ((bm ++ bl).all id)) := by
    rw [eval_call, hargs]
    exact applyOp_andor_bools true (bm ++ bl)
  exact ⟨bm, bl, hUm, hUc, simpTerm_sound x _ hand⟩

theorem msol_square_of {p : Program} {mc : MChain} {M : MFlat} (h : phiMsolOf p mc = .ok M) {x : Tuple}
    (hx : FitsCells M.cells x) :
    ∃ b, M.term.eval x = .ok (.bool b) ∧ acceptsMsolOf p mc (msolSubstitute M x) = .ok b := by
  obtain ⟨bm, bl, hUm, hUc, ht⟩ := msol_parts h hx
  refine ⟨(bm ++ bl).all id, ht, ?_⟩
  rw [List.all_append]
  exact acceptsMsolOf_eq hUm hUc

/-- **Theorem M**: when φ succeeds on statement `k`, a multi solution set, under every
assignment that gives each cell a value in its domain, the flat term and the reference
evaluator agree on the database the assignment gives, and neither refuses. -/
theorem msol_square {p : Program} {k : Nat} {M : MFlat} (h : phiMsol p k = .ok M) {x : Tuple}
    (hx : FitsCells M.cells x) :
    ∃ b, M.term.eval x = .ok (.bool b) ∧ acceptsMsol p k (msolSubstitute M x) = .ok b := by
  unfold phiMsol at h
  cases hmc : statementMChain p k with
  | none => simp [hmc, throw, throwThe, MonadExceptOf.throw] at h
  | some mc =>
  simp only [hmc] at h
  obtain ⟨b, h1, h2⟩ := msol_square_of h hx
  exact ⟨b, h1, by simp [acceptsMsol, hmc, h2]⟩

end Rasso.Phi
