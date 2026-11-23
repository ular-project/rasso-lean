import Rasso.Bridge.Sol
import Rasso.Phi.Theorems.Msol

/-!
# φ's theorems: a multi solution set's key, cells and lift

The `ℰ_msol` key as a term over the cells (as theorem K); and
theorem C and B′ for databases (M′): the statement evaluates without refusal, and its
databases are exactly the `msolSubstitute M x` on which `acceptsMsol` gives true, each given
by one assignment over exactly the cells.
-/

namespace Rasso.Phi

open Rasso

/-- What a multi solution set's φ gives a condition over its members: the environment
with the database `msolSubstitute M x` bound meets `CtxOk`. -/
theorem msol_ctxOk {p : Program} {mc : MChain} {M : MFlat} (h : phiMsolOf p mc = .ok M) {x : Tuple}
    (hx : FitsCells M.cells x) (env : Env) (kinds : Kinds) :
    CtxOk ⟨env, kinds, none, M.members.map fun q => (q.1, q.2.sym)⟩ x
      (inCondition (bindDb (msolSubstitute M x) env)) := by
  obtain ⟨R⟩ := phiMsolOf_spec h
  obtain ⟨Fs, kinds', conds, _, _, hnames, hnd, hFs, hcn, hkinds, hconds, rfl⟩ := R
  dsimp only at hx ⊢
  have hfst : Fs.map (·.1) = mc.members.map (·.1) := Pw.map_fst_eq (fun a b h => h.1) hFs
  apply ctxOk_msol (by rw [hfst]; exact hnames)
  intro r hr
  obtain ⟨q, _, he, hq⟩ := Pw.mem_right hFs hr
  obtain ⟨Rr⟩ := phiOf_spec hq
  rw [← he] at Rr
  exact member_denotes Rr (fits_member hcn hx hr)

/-- **Theorem K for databases.** φ's key term and the evaluator's key agree on every database
φ can describe, and neither refuses. -/
theorem phiMsolKey_sound {p : Program} {j : Nat} {M : MFlat} {t : Term} (h : phiMsolKey p j = .ok (M, t))
    {x : Tuple} (hx : FitsCells M.cells x) :
    ∃ v, t.eval x = .ok v ∧ keyValueMsol p j (msolSubstitute M x) = .ok v := by
  unfold phiMsolKey at h
  unfold keyValueMsol
  cases hk : mkeyOf p j with
  | none => simp [hk, throw, throwThe, MonadExceptOf.throw] at h
  | some r =>
  obtain ⟨mc, key⟩ := r
  simp only [hk, bind, Except.bind] at h ⊢
  split at h
  · cases h
  rename_i M' hM
  split at h
  · cases h
  rename_i env henv
  split at h
  · cases h
  rename_i kinds hkinds
  split at h
  · cases h
  rename_i R hR
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
    obtain ⟨r, hre, hD⟩ := sRel_sound (cellsOk_of_fits hkinds hx) (msol_ctxOk hM hx env kinds) key hR
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
    have hre' : Expr.eval (inCondition (bindDb (msolSubstitute M' x) env)) [] key = .ok (.finrel r) := hre
    simp [hre', scalar, Val.asFinrel, hat, hts, hget, bind, Except.bind, pure, Except.pure]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## A chain's candidates, as a list -/

variable {nm : String → Nat → String}

/-- The candidates of the chain `ch` (`SolSem`'s list), or none when its `ω_sol` refuses. -/
def chainCands (p : Program) (ch : Chain) : List Finrel :=
  match omegaOf p ch with
  | .ok (data, u, picks) => (omegaSolCandidates (data.heading ++ u.heading) data.tuples picks).filter (levelsB p ch)
  | .error _ => []

theorem solSem_candidates {p : Program} {ch : Chain} {s : Sol} (h : SolSem p ch (.sol s)) :
    s.candidates = chainCands p ch := by
  obtain ⟨s', data, u, picks, e, hom, _, hc⟩ := h
  cases e
  simp [chainCands, hom, hc]

/-- B for a chain, as membership: the candidate an assignment gives is one of the chain's
exactly when `acceptsOf` gives true. -/
theorem chain_mem_iff {p : Program} {ch : Chain} {F : Flat} (R : PhiOfRun nm p ch F) {x : Tuple}
    (hx : FitsCells F.cells x) :
    substitute F x ∈ chainCands p ch ↔ acceptsOf p ch (substitute F x) = .ok true := by
  have hFh : F.heading = R.data.heading ++ R.u.heading := congrArg Flat.heading R.hF
  obtain ⟨bs, hU, _, hacc⟩ := square_parts R hx
  unfold chainCands
  rw [R.hom]
  dsimp only
  rw [List.mem_filter, ← hFh, phi_cells_into R hx, hacc]
  unfold levelsB
  rw [levels_all hU]
  simp only [copiesB, List.all_eq_true, okB_true, Except.ok.injEq, Bool.and_eq_true]

/-- Every candidate of the chain is the candidate of an assignment over exactly the cells. -/
theorem chain_onto {p : Program} {ch : Chain} {F : Flat} (R : PhiOfRun nm p ch F) {c : Finrel}
    (hc : c ∈ chainCands p ch) :
    ∃ x, FitsCells F.cells x ∧ Tuple.Over F.cells.attrs x ∧ substitute F x = c := by
  have hFh : F.heading = R.data.heading ++ R.u.heading := congrArg Flat.heading R.hF
  unfold chainCands at hc
  rw [R.hom] at hc
  dsimp only at hc
  rw [List.mem_filter, ← hFh] at hc
  exact phi_cells_onto R hc.1

/-! ## Gluing the members' assignments -/

/-- Each member's cells with that member's assignment's values. -/
def gluePairs : List (String × Flat) → List Tuple → List (String × Value)
  | r :: Fs, xr :: xs => r.2.cells.map (fun q => (q.1, (xr.get? q.1).getD default)) ++ gluePairs Fs xs
  | _, _ => []

theorem gluePairs_keys {α : Type} {R : String × Flat → Tuple → Prop} :
    ∀ {Fs : List (String × Flat)} {xs : List Tuple}, Pw R Fs xs →
      (gluePairs Fs xs).map (·.1) = Heading.attrs (Fs.flatMap (·.2.cells))
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ hl => by
    simp [gluePairs, Heading.attrs, gluePairs_keys (α := α) hl, Function.comp_def]

theorem gluePairs_mem {R : String × Flat → Tuple → Prop} :
    ∀ {Fs : List (String × Flat)} {xs : List Tuple}, Pw R Fs xs →
      Pw (fun r xr => R r xr ∧ ∀ c ∈ r.2.cells.attrs, (c, (xr.get? c).getD default) ∈ gluePairs Fs xs) Fs xs
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hl => by
    refine .cons ⟨h, fun c hc => ?_⟩ (Pw.imp (fun r xr ⟨h1, h2⟩ => ⟨h1, fun c hc =>
      List.mem_append_right _ (h2 c hc)⟩) (gluePairs_mem hl))
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
    exact List.mem_append_left _ (List.mem_map.mpr ⟨q, hq, rfl⟩)

/-- Assignments of the members, each fitting its member's cells, glue into one assignment
over exactly the cells of all members that agrees with each on its cells. -/
theorem glue {Fs : List (String × Flat)} {xs : List Tuple}
    (hcn : Heading.attrs (Fs.flatMap (·.2.cells)) |>.Nodup)
    (hp : Pw (fun r xr => FitsCells r.2.cells xr) Fs xs) :
    ∃ x, FitsCells (Fs.flatMap (·.2.cells)) x ∧ Tuple.Over (Heading.attrs (Fs.flatMap (·.2.cells))) x ∧
      Pw (fun r xr => ∀ c ∈ r.2.cells.attrs, x.get? c = xr.get? c) Fs xs := by
  have hk : ((gluePairs Fs xs).map (·.1)).Nodup := by rw [gluePairs_keys (α := Unit) hp]; exact hcn
  refine ⟨Tuple.ofPairs (gluePairs Fs xs), ?_, ⟨Tuple.sorted_ofPairs hk, fun q hq => ?_⟩, ?_⟩
  rotate_left
  · rw [← gluePairs_keys (α := Unit) hp]
    exact List.mem_map_of_mem (mem_ofPairs.mp hq)
  · refine Pw.imp (fun r xr ⟨hf, hm⟩ c hc => ?_) (gluePairs_mem hp)
    rw [Tuple.get?_ofPairs hk, lookup_of_mem_nodup hk (hm c hc)]
    obtain ⟨⟨c', d⟩, hcd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨d', hd'⟩ := lookup_isSome_of_mem hcd
    obtain ⟨v, hv, _⟩ := hf _ _ hd'
    rw [hv]; rfl
  · have hagree := gluePairs_mem hp
    intro c d hl
    have hmem := lookup_some_mem hl
    obtain ⟨r, hr, hcr⟩ := List.mem_flatMap.mp hmem
    obtain ⟨xr, _, ⟨hf, hm⟩⟩ := Pw.mem_left hagree hr
    have hc : c ∈ r.2.cells.attrs := List.mem_map_of_mem hcr
    rw [Tuple.get?_ofPairs hk, lookup_of_mem_nodup hk (hm c hc)]
    have hnr : (r.2.cells.map (·.1)).Nodup := by
      have := hcn
      simp only [Heading.attrs, List.map_flatMap] at this
      rw [List.flatMap_def] at this
      exact List.Nodup.sublist (List.sublist_flatten_of_mem
        (List.mem_map_of_mem (f := fun a : String × Flat => a.2.cells.map (·.1)) hr)) this
    obtain ⟨v, hv, hdv⟩ := hf c d (lookup_of_mem_nodup hnr hcr)
    exact ⟨v, by rw [hv]; rfl, hdv⟩

/-! ## What a multi solution set chain evaluates to -/

/-- The members' part of a database of `mc`: one candidate of each member's chain, in order,
under the member's name. -/
def MPart (p : Program) (mc : MChain) (db : Db) : Prop :=
  Pw (fun (q : String × Chain) (d : String × Finrel) => d.1 = q.1 ∧ d.2 ∈ chainCands p q.2) mc.members db

/-- `db` is a database of the chain `mc`: its members' part, and every condition holds on it. -/
def MMeaning (p : Program) (mc : MChain) (db : Db) : Prop :=
  MPart p mc db ∧ ∀ lv ∈ mc.levels, ∃ env, envAt p lv.stmt = .ok env ∧
    lv.cond.eval (inCondition (bindDb db env)) [] = .ok true

/-- The value `v` is the multi solution set of the chain `mc`. -/
def MSem (p : Program) (mc : MChain) (v : Val) : Prop :=
  ∃ m : Msol, v = .msol m ∧ ∀ db, db ∈ m.candidates ↔ MMeaning p mc db

/-- A known multi solution set chain and a bound value agree. -/
def MNameRel (p : Program) (no : String × Option MChain) (nv : String × Val) : Prop :=
  no.1 = nv.1 ∧ ∀ mc, no.2 = some mc → MSem p mc nv.2

/-- `f`, written at statement `i`, unfolds to the multi solution set chain `mc`. -/
inductive MUnfolds (known : List (String × Option Chain)) (mknown : List (String × Option MChain))
    (i : Nat) : Expr → MChain → Prop
  | omega (ms : List (String × Expr)) (c : Option Cond) (chs : List (String × Chain)) :
      Pw (fun (ne : String × Expr) (nc : String × Chain) => nc.1 = ne.1 ∧ Unfolds known i ne.2 nc.2) ms chs →
      MUnfolds known mknown i (.omegaMsol ms c) ⟨i, chs, c.toList.map (⟨i, ·⟩)⟩
  | sigma (c : Cond) (e : Expr) (mc : MChain) : MUnfolds known mknown i e mc →
      MUnfolds known mknown i (.sigmaMsol c e) { mc with levels := mc.levels ++ [⟨i, c⟩] }
  | name (n : String) (mc : MChain) : mknown.lookup n = some (some mc) →
      MUnfolds known mknown i (.name n) mc

theorem optMapM_pw {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {m : List β}, l.mapM f = some m → Pw (fun a b => f a = some b) l m
  | [], m, h => by simp at h; subst h; exact .nil
  | a :: l, m, h => by
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
    simp only [ha] at h
    cases hl : l.mapM f with
    | none => simp [hl] at h
    | some bs =>
    simp only [hl, pure, Option.some.injEq] at h
    subst h
    exact .cons ha (optMapM_pw hl)

theorem mchainOf_some {known : List (String × Option Chain)} {mknown : List (String × Option MChain)}
    {i : Nat} : ∀ {f : Expr} {mc : MChain}, mchainOf known mknown i f = some mc → MUnfolds known mknown i f mc
  | .omegaMsol ms c, mc, h => by
    simp only [mchainOf, bind, Option.bind] at h
    cases hm : ms.mapM (fun x => (chainOf known i x.2).map (x.1, ·)) with
    | none => simp [hm] at h
    | some chs =>
    simp only [hm, Option.some.injEq] at h
    subst h
    refine .omega ms c chs (Pw.imp (fun ne nc hne => ?_) (optMapM_pw hm))
    cases hc : chainOf known i ne.2 with
    | none => simp [hc] at hne
    | some ch =>
    simp only [hc, Option.map_some, Option.some.injEq] at hne
    subst hne
    exact ⟨rfl, (chainOf_eq_some_iff _ _ _ _).mp hc⟩
  | .sigmaMsol c e, mc, h => by
    simp only [mchainOf] at h
    cases he : mchainOf known mknown i e with
    | none => simp [he] at h
    | some mc' =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst h
    exact .sigma c e mc' (mchainOf_some he)
  | .name n, mc, h => by
    simp only [mchainOf] at h
    cases hl : mknown.lookup n with
    | none => simp [hl] at h
    | some o =>
    simp only [hl, Option.bind_some] at h
    subst h
    exact .name n mc hl
  | .omega _, _, h | .omegaWhere _ _, _, h | .omegaRows _ _, _, h | .select _ _, _, h | .project _ _, _, h
  | .rename _ _, _, h | .nary _ _, _, h | .gamma _ _ _ _, _, h | .extend _ _ _, _, h | .enum _ _ _, _, h
  | .omegaSol _ _, _, h | .sigmaSol _ _, _, h | .enumSol _ _ _, _, h | .enumMsol _ _ _, _, h
  | .flatten _ _, _, h | .flattenMsol _ _, _, h | .dbRef _ _, _, h | .forget _, _, h | .lift _, _, h => by
    simp [mchainOf] at h

theorem candOf_iff {p : Program} {i : Nat} {env : Env} (henv : envAt p i = .ok env)
    {known : List (String × Option Chain)} (hk : Pw (NameRel p) known env) :
    ∀ {ms : List (String × Expr)} {sols : List (String × Sol)} {chs : List (String × Chain)},
      MembersEval env [] ms sols →
      Pw (fun (ne : String × Expr) (nc : String × Chain) => nc.1 = ne.1 ∧ Unfolds known i ne.2 nc.2) ms chs →
      ∀ db, (CandOf sols db ↔ Pw (fun (q : String × Chain) (d : String × Finrel) =>
        d.1 = q.1 ∧ d.2 ∈ chainCands p q.2) chs db)
  | [], [], [], .nil, .nil, db => by
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; exact .nil
  | (n, e) :: ms, (_, s) :: sols, (n', ch) :: chs, .cons _ hs hme, .cons ⟨hn, hu⟩ hpw, db => by
    dsimp only at hn hu
    subst hn
    have hc := solSem_candidates (sem_of_eval henv hk hu hs)
    have ih := candOf_iff henv hk hme hpw
    constructor
    · intro h
      cases h with
      | cons hr hrest =>
        exact .cons ⟨rfl, by rw [← hc]; exact hr⟩ ((ih _).mp hrest)
    · intro h
      cases h with
      | cons hd hrest =>
        rename_i d db'
        obtain ⟨d1, d2⟩ := d
        dsimp only at hd
        obtain ⟨rfl, hd2⟩ := hd
        exact .cons (by rw [hc]; exact hd2) ((ih _).mpr hrest)

theorem lookup_mrel {p : Program} {n : String} {mc : MChain} :
    ∀ {mknown : List (String × Option MChain)} {env : Env}, Pw (MNameRel p) mknown env →
      mknown.lookup n = some (some mc) → ∃ v, env.lookup n = some v ∧ MSem p mc v
  | [], [], .nil, h => by simp at h
  | (n', o) :: mknown, (n'', v) :: env, .cons ⟨e, hs⟩ hk, h => by
    dsimp only at e hs
    subst e
    by_cases hn : n = n'
    · subst hn
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h ⊢
      exact ⟨v, rfl, hs mc h⟩
    · have hb : (n == n') = false := by simpa using hn
      simp only [List.lookup, hb] at h ⊢
      exact lookup_mrel hk h

/-- **The msol chain is what the evaluator evaluates.** -/
theorem sem_of_eval_msol {p : Program} {i : Nat} {env : Env} (henv : envAt p i = .ok env)
    {known : List (String × Option Chain)} (hk : Pw (NameRel p) known env)
    {mknown : List (String × Option MChain)} (hmk : Pw (MNameRel p) mknown env) :
    ∀ {f : Expr} {mc : MChain}, MUnfolds known mknown i f mc → ∀ {v : Val}, Expr.eval env [] f = .ok v →
      MSem p mc v
  | _, _, .omega ms c chs hpw, v, hv => by
    obtain ⟨sols, m, hme, rfl, _, hm⟩ := eval_omegaMsol_meaning (by rfl) hv
    refine ⟨m, rfl, fun db => ?_⟩
    rw [hm db]
    unfold MsolMeaning MMeaning MPart
    rw [candOf_iff henv hk hme hpw db]
    apply and_congr Iff.rfl
    cases c with
    | none => simp [msolConds]
    | some c =>
      simp only [msolConds, List.mem_cons, List.not_mem_nil, or_false, forall_eq, Option.toList_some,
        List.map_cons, List.map_nil, msolTest]
      constructor
      · intro h; exact ⟨env, henv, h⟩
      · rintro ⟨env', he, h⟩; rw [henv] at he; cases he; exact h
  | _, _, .sigma c e mc hu, v, hv => by
    obtain ⟨m0, dbs, he, hf, rfl⟩ := eval_sigmaMsol (by rfl) hv
    obtain ⟨m0', e0, hm0⟩ := sem_of_eval_msol henv hk hmk hu he
    cases e0
    refine ⟨_, rfl, fun db => ?_⟩
    dsimp only
    rw [mem_filterM hf, hm0]
    unfold MMeaning msolTest
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun lv hlv => ?_⟩
      rcases hlv with hlv | rfl
      · exact h2 lv hlv
      · exact ⟨env, henv, h3⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun lv hlv => h2 lv (.inl hlv)⟩, ?_⟩
      obtain ⟨env', he', h3⟩ := h2 ⟨i, c⟩ (.inr rfl)
      rw [henv] at he'; cases he'; exact h3
  | _, _, .name n mc hl, v, hv => by
    rw [eval_name_eq] at hv
    obtain ⟨w, hw, hs⟩ := lookup_mrel hmk hl
    rw [hw] at hv
    cases hv
    exact hs

/-! ## Through the program -/

theorem programChains_take (p : Program) {j : Nat} (hj : j ≤ p.length) :
    ((programChains p).take j).reverse = knownAt p j := by
  rw [← List.reverse_reverse (knownAt p j)]
  congr 1
  obtain ⟨hl, hs⟩ := knownAt_spec p p.length (Nat.le_refl _)
  obtain ⟨hl', hs'⟩ := knownAt_spec p j hj
  rw [programChains_eq]
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_take]
  by_cases hk : k < j
  · simp only [hk, ↓reduceIte]
    rw [hs k (Nat.lt_of_lt_of_le hk hj), hs' k hk]
  · simp only [hk, ↓reduceIte]
    rw [List.getElem?_eq_none (by simp [hl']; omega)]

/-- One step of `programMChains`' fold. -/
def mknownStep (p : Program) (mk : List (String × Option MChain)) (x : (String × Expr) × Nat) :
    List (String × Option MChain) :=
  (x.1.1, mchainOf ((programChains p).take x.2).reverse mk x.2 x.1.2) :: mk

/-- The multi solution set chains of the first `i` statements, latest first. -/
def mknownAt (p : Program) (i : Nat) : List (String × Option MChain) :=
  (p.take i).zipIdx.foldl (mknownStep p) []

theorem mknownAt_succ {p : Program} {i : Nat} (hi : i < p.length) :
    mknownAt p (i + 1) = mknownStep p (mknownAt p i) (p[i], i) := by
  unfold mknownAt
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.zipIdx_append,
    List.foldl_append]
  simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]

theorem mknownAt_of_le {p : Program} {i : Nat} (hi : p.length ≤ i) : mknownAt p (i + 1) = mknownAt p i := by
  unfold mknownAt
  rw [List.take_of_length_le hi, List.take_of_length_le (by omega)]

theorem programMChains_eq (p : Program) : programMChains p = (mknownAt p p.length).reverse := by
  unfold programMChains mknownAt
  rw [List.take_length]
  rfl

theorem mknownAt_spec (p : Program) : ∀ m (hm : m ≤ p.length), (mknownAt p m).length = m ∧
    ∀ k (hk : k < m), (mknownAt p m).reverse[k]? =
      some ((p[k]'(Nat.lt_of_lt_of_le hk hm)).1,
        mchainOf (knownAt p k) (mknownAt p k) k (p[k]'(Nat.lt_of_lt_of_le hk hm)).2)
  | 0, _ => ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | m + 1, hm => by
    obtain ⟨hl, hs⟩ := mknownAt_spec p m (by omega)
    rw [mknownAt_succ (by omega)]
    refine ⟨by simp [mknownStep, hl], fun k hk => ?_⟩
    simp only [mknownStep, List.reverse_cons]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [List.getElem?_append_left (by simp [hl]; exact hk)]
      exact hs k hk
    · rw [List.getElem?_append_right (by simp [hl])]
      simp [hl, programChains_take p (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hm))]

theorem statementMChain_spec {p : Program} {k : Nat} {mc : MChain} (h : statementMChain p k = some mc) :
    ∃ hk : k < p.length, mchainOf (knownAt p k) (mknownAt p k) k p[k].2 = some mc := by
  obtain ⟨hl, hs⟩ := mknownAt_spec p p.length (Nat.le_refl _)
  unfold statementMChain at h
  rw [programMChains_eq] at h
  have hk : k < p.length := by
    rcases Nat.lt_or_ge k p.length with hk | hk
    · exact hk
    · rw [List.getElem?_eq_none (by simp [hl]; omega)] at h
      cases h
  refine ⟨hk, ?_⟩
  rw [hs k hk] at h
  simpa using h

/-- Every statement that ran is bound to its msol chain's value, when it has one. -/
theorem run_mrel (p : Program) : ∀ i {env : Env}, runProgram (p.take i) = .ok env →
    Pw (MNameRel p) (mknownAt p i) env.reverse
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
        have ih := run_mrel p i h0
        have henv : envAt p i = .ok env0.reverse := by simp [envAt, h0, Except.map]
        rw [mknownAt_succ hi, List.reverse_append]
        refine .cons ⟨rfl, fun mc hc => ?_⟩ ih
        simp only at hc
        rw [programChains_take p (Nat.le_of_lt hi)] at hc
        exact sem_of_eval_msol henv (run_rel p i h0) ih (mchainOf_some hc) hv
    · rw [List.take_of_length_le (by omega)] at h
      rw [mknownAt_of_le (by omega)]
      apply run_mrel p i
      rw [List.take_of_length_le (by omega)]; exact h

/-- **An msol statement does not refuse**, when its members evaluate, none is named `I`,
there is at least one, no two have one name, and its own conditions evaluate on every database of members'
candidates. -/
theorem eval_ok_of_msol {p : Program} {i : Nat} {env : Env} (henv : envAt p i = .ok env)
    {known : List (String × Option Chain)} (hk : Pw (NameRel p) known env)
    {mknown : List (String × Option MChain)} (hmk : Pw (MNameRel p) mknown env) :
    ∀ {f : Expr} {mc : MChain}, MUnfolds known mknown i f mc →
      (∀ nc ∈ mc.members, nc.1 ≠ "I" ∧ ∀ e, Unfolds known i e nc.2 → ∃ s, Expr.eval env [] e = .ok (.sol s)) →
      mc.members ≠ [] →
      (mc.members.map (·.1)).Nodup →
      (∀ lv ∈ mc.levels, lv.stmt = i → ∀ db, MPart p mc db →
        ∃ b, lv.cond.eval (inCondition (bindDb db env)) [] = .ok b) →
      ∃ v, Expr.eval env [] f = .ok v
  | _, _, .omega ms c chs hpw, hmem, hne, hnd, hcond => by
    apply eval_omegaMsol_ok (by rfl)
    · intro e; subst e; cases hpw; exact hne rfl
    · have hf : chs.map (·.1) = ms.map (·.1) := Pw.map_fst_eq (fun a b h => h.1) hpw
      rw [← hf]; exact hnd
    · intro ne hne'
      obtain ⟨nc, hnc, he, hu⟩ := Pw.mem_left hpw hne'
      obtain ⟨hI, hev⟩ := hmem nc hnc
      refine ⟨by rw [← he]; simpa using hI, hev ne.2 hu⟩
    · intro sols hme cond hc db hdb
      subst hc
      exact hcond ⟨i, cond⟩ (by simp) rfl db ((candOf_iff henv hk hme hpw db).mp hdb)
  | _, _, .sigma c e mc hu, hmem, hne, hnd, hcond => by
    obtain ⟨v0, hv0⟩ := eval_ok_of_msol henv hk hmk hu hmem hne hnd
      (fun lv hlv hst db hdb => hcond lv (List.mem_append_left _ hlv) hst db hdb)
    obtain ⟨m0, rfl, hm0⟩ := sem_of_eval_msol henv hk hmk hu hv0
    apply eval_sigmaMsol_ok (by rfl) hv0
    intro db hdb
    exact hcond ⟨i, c⟩ (List.mem_append_right _ List.mem_cons_self) rfl db ((hm0 db).mp hdb).1
  | _, _, .name n mc hl, _, _, _, _ => by
    rw [eval_name_eq]
    obtain ⟨w, hw, _⟩ := lookup_mrel hmk hl
    rw [hw]
    exact ⟨w, rfl⟩

/-! ## Theorem M′ -/

theorem Pw.and {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Pw R l m → Pw S l m → Pw (fun a b => R a b ∧ S a b) l m
  | [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, .cons h hl, .cons h' hl' => .cons ⟨h, h'⟩ (Pw.and hl hl')

theorem Pw.to_map_right {α β γ : Type} {R : α → γ → Prop} {F : β → γ} :
    ∀ {l : List α} {m : List β}, Pw (fun a b => R a (F b)) l m → Pw R l (m.map F)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hl => .cons h (Pw.to_map_right hl)

/-- Choose a witness for each related pair. -/
theorem Pw.choose {α β γ : Type} {P : α → β → Prop} {Q : α → β → γ → Prop}
    (h : ∀ a b, P a b → ∃ c, Q a b c) :
    ∀ {l : List α} {m : List β}, Pw P l m →
      ∃ ys : List (β × γ), Pw (fun a y => Q a y.1 y.2) l ys ∧ ys.map (·.1) = m
  | [], [], .nil => ⟨[], .nil, rfl⟩
  | a :: _, b :: _, .cons hab hl => by
    obtain ⟨c, hc⟩ := h a b hab
    obtain ⟨ys, hys, e⟩ := Pw.choose h hl
    exact ⟨(b, c) :: ys, .cons hc hys, by simp [e]⟩

theorem Pw.imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Pw R l m → (∀ a ∈ l, ∀ b, R a b → S a b) → Pw S l m
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h hl, hs => .cons (hs _ List.mem_cons_self _ h)
      (Pw.imp_mem hl fun a ha => hs a (List.mem_cons_of_mem _ ha))

theorem pw_all_iff {α : Type} {P : α → Prop} :
    ∀ {l : List α} {bs : List Bool}, Pw (fun a b => (P a ↔ b = true)) l bs →
      ((∀ a ∈ l, P a) ↔ bs.all id = true)
  | [], [], .nil => by simp
  | _ :: _, _ :: _, .cons h hl => by
    simp only [List.mem_cons, forall_eq_or_imp, List.all_cons, Bool.and_eq_true, id, h, pw_all_iff hl]

/-- A database whose names are the members' names, without repeats: being the members'
part pointwise is the same as each member's name looking up a relation that fits it. -/
theorem pw_lookup_iff {β γ : Type} {C : String × β → γ → Prop} :
    ∀ {ms : List (String × β)} {db : List (String × γ)}, db.map (·.1) = ms.map (·.1) →
      (ms.map (·.1)).Nodup →
      (Pw (fun (q : String × β) (d : String × γ) => d.1 = q.1 ∧ C q d.2) ms db ↔
        ∀ q ∈ ms, ∃ r, db.lookup q.1 = some r ∧ C q r)
  | [], [], _, _ => by simp; exact .nil
  | [], _ :: _, e, _ => by simp at e
  | _ :: _, [], e, _ => by simp at e
  | (n, b) :: ms, (n', r) :: db, e, hnd => by
    simp only [List.map_cons, List.cons.injEq] at e
    obtain ⟨rfl, e⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnd
    have ih := pw_lookup_iff (C := C) e hnd.2
    have hne : ∀ q ∈ ms, (q.1 == n') = false := by
      intro q hq
      simp only [beq_eq_false_iff_ne]
      intro hq1
      apply hnd.1
      rw [← hq1]
      exact List.mem_map_of_mem hq
    constructor
    · intro h
      cases h with
      | cons h1 hl =>
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨r, by simp [List.lookup], h1.2⟩
        · simp only [List.lookup, hne q hq]
          exact ih.mp hl q hq
    · intro h
      refine .cons ⟨rfl, ?_⟩ (ih.mpr fun q hq => ?_)
      · obtain ⟨r', hl, hc⟩ := h (n', b) List.mem_cons_self
        simp [List.lookup] at hl
        subst hl
        exact hc
      · obtain ⟨r', hl, hc⟩ := h q (List.mem_cons_of_mem _ hq)
        simp only [List.lookup, hne q hq] at hl
        exact ⟨r', hl, hc⟩

/-- Every database of the members' candidates is the database of an assignment over exactly
the cells. -/
theorem msol_db_onto {p : Program} {mc : MChain} {M : MFlat} (h : phiMsolOf p mc = .ok M) {db : Db}
    (hdb : MPart p mc db) :
    ∃ x, FitsCells M.cells x ∧ Tuple.Over M.cells.attrs x ∧ msolSubstitute M x = db := by
  obtain ⟨R⟩ := phiMsolOf_spec h
  obtain ⟨Fs, _, _, _, _, _, _, hFs, hcn, _, _, rfl⟩ := R
  obtain ⟨ys, hys, e⟩ := Pw.choose (Q := fun (r : String × Flat) (d : String × Finrel) (xr : Tuple) =>
      (∃ ch, phiOf (memberCell r.1) p ch = .ok r.2) ∧ FitsCells r.2.cells xr ∧ d = (r.1, substitute r.2 xr))
    (fun r d ⟨q, ⟨hr1, hphi⟩, hd1, hd2⟩ => by
      obtain ⟨Rr⟩ := phiOf_spec hphi
      obtain ⟨xr, hxr, _, hs⟩ := chain_onto Rr hd2
      exact ⟨xr, ⟨q.2, by rw [hr1]; exact hphi⟩, hxr, Prod.ext (hd1.trans hr1.symm) hs.symm⟩)
    (Pw.comp hFs hdb)
  obtain ⟨x, hx, hox, hag⟩ := glue hcn (Pw.to_map_right (F := (·.2)) (Pw.imp (fun r y hy => hy.2.1) hys))
  refine ⟨x, hx, hox, ?_⟩
  dsimp only [msolSubstitute]
  rw [← e]
  refine (Pw.eq_map (F := fun r : String × Flat => (r.1, substitute r.2 x)) ?_).symm
  apply Pw.to_map_right
  refine Pw.imp (fun r y ⟨⟨⟨ch, hphi⟩, _, hy⟩, hagr⟩ => ?_) (Pw.and hys (Pw.map_right hag))
  obtain ⟨Rr⟩ := phiOf_spec hphi
  rw [hy, substitute_congr Rr hagr]

/-- B for databases, as membership: an assignment's database is a database of the chain
exactly when `acceptsMsolOf` gives true. -/
theorem msol_meaning_iff {p : Program} {mc : MChain} {M : MFlat} (h : phiMsolOf p mc = .ok M) {x : Tuple}
    (hx : FitsCells M.cells x) :
    MMeaning p mc (msolSubstitute M x) ↔ acceptsMsolOf p mc (msolSubstitute M x) = .ok true := by
  obtain ⟨bm, bl, hUm, hUc, _⟩ := msol_parts h hx
  obtain ⟨R⟩ := phiMsolOf_spec h
  obtain ⟨Fs, _, _, _, _, _, hnd, hFs, hcn, _, _, hM⟩ := R
  have hmem : M.members = Fs := by rw [hM]
  have hcells : M.cells = Fs.flatMap (·.2.cells) := by rw [hM]
  have hfst : Fs.map (·.1) = mc.members.map (·.1) := Pw.map_fst_eq (fun a b h => h.1) hFs
  have hndF : ((Fs.map fun p => (p.1, substitute p.2 x)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def, hfst] using hnd
  have hkeys : (msolSubstitute M x).map (·.1) = mc.members.map (·.1) := by
    simp only [msolSubstitute, hmem, List.map_map, Function.comp_def]
    simpa [Function.comp_def] using hfst
  have hm : Pw (fun (q : String × Chain) b => ((∃ r, (msolSubstitute M x).lookup q.1 = some r ∧
      r ∈ chainCands p q.2) ↔ b = true)) mc.members bm := by
    refine Pw.imp_mem hUm fun q hq b ⟨r, hl, ha⟩ => ?_
    obtain ⟨r', hr', hr1, hphi⟩ := Pw.mem_left hFs hq
    obtain ⟨Rr⟩ := phiOf_spec hphi
    have hxr : FitsCells r'.2.cells x := fits_member hcn (by rw [← hcells]; exact hx) hr'
    have hl' : (msolSubstitute M x).lookup q.1 = some (substitute r'.2 x) := by
      rw [← hr1, msolSubstitute, hmem]
      exact lookup_of_mem_nodup hndF (List.mem_map.mpr ⟨r', hr', rfl⟩)
    rw [hl'] at hl ⊢
    cases hl
    simp only [Option.some.injEq, exists_eq_left']
    rw [chain_mem_iff Rr hxr, ha]
    simp
  have hc : Pw (fun (lv : MLevel) b => ((∃ env, envAt p lv.stmt = .ok env ∧
      lv.cond.eval (inCondition (bindDb (msolSubstitute M x) env)) [] = .ok true) ↔ b = true))
      mc.levels bl := by
    refine Pw.imp (fun lv b ⟨env, he, hb⟩ => ?_) hUc
    constructor
    · rintro ⟨env', he', hb'⟩
      rw [he] at he'
      cases he'
      rw [hb] at hb'
      simpa using hb'
    · rintro rfl
      exact ⟨env, he, hb⟩
  rw [acceptsMsolOf_eq hUm hUc, Except.ok.injEq, Bool.and_eq_true]
  unfold MMeaning MPart
  rw [pw_lookup_iff hkeys hnd]
  exact and_congr (pw_all_iff hm) (pw_all_iff hc)

/-- **Theorem M′** (B′ for databases): when φ succeeds on statement `k` and the statements
before it run, statement `k` evaluates without refusal to a multi solution set; an
assignment's database is one of its databases exactly when `acceptsMsol` gives true; and
every one of its databases is the database of an assignment over exactly the cells. -/
theorem phiMsol_lift {p : Program} {k : Nat} {M : MFlat} (h : phiMsol p k = .ok M) {env : Env}
    (hrun : runProgram (p.take k) = .ok env) :
    ∃ (hk : k < p.length) (m : Msol), Expr.eval env.reverse [] (p[k]'hk).2 = .ok (.msol m) ∧
      (∀ x, FitsCells M.cells x →
        (msolSubstitute M x ∈ m.candidates ↔ acceptsMsol p k (msolSubstitute M x) = .ok true)) ∧
      (∀ db ∈ m.candidates, ∃ x, FitsCells M.cells x ∧ Tuple.Over M.cells.attrs x ∧ msolSubstitute M x = db) := by
  unfold phiMsol at h
  cases hmc : statementMChain p k with
  | none => simp [hmc, throw, throwThe, MonadExceptOf.throw] at h
  | some mc =>
  simp only [hmc] at h
  obtain ⟨hk, hc⟩ := statementMChain_spec hmc
  have henv : envAt p k = .ok env.reverse := by simp [envAt, hrun, Except.map]
  have hu := mchainOf_some hc
  have hrel := run_rel p k hrun
  have hmrel := run_mrel p k hrun
  obtain ⟨R⟩ := phiMsolOf_spec h
  have hmembers : ∀ nc ∈ mc.members, nc.1 ≠ "I" ∧ ∀ e, Unfolds (knownAt p k) k e nc.2 →
      ∃ s, Expr.eval env.reverse [] e = .ok (.sol s) := by
    intro nc hnc
    refine ⟨fun e => R.hI (by rw [← e]; exact List.mem_map_of_mem hnc), fun e he => ?_⟩
    obtain ⟨r, _, _, hphi⟩ := Pw.mem_left R.hFs hnc
    obtain ⟨Rr⟩ := phiOf_spec hphi
    obtain ⟨s, hs, _⟩ := lift_of_chain Rr henv hrel he
    exact ⟨s, hs⟩
  have hlevels : ∀ lv ∈ mc.levels, lv.stmt = k → ∀ db, MPart p mc db →
      ∃ b, lv.cond.eval (inCondition (bindDb db env.reverse)) [] = .ok b := by
    intro lv hlv hst db hdb
    obtain ⟨x, hx, _, rfl⟩ := msol_db_onto h hdb
    obtain ⟨_, _, _, hUc, _⟩ := msol_parts h hx
    obtain ⟨b, env', he, hb⟩ := Pw.exists_left hUc lv hlv
    rw [hst, henv] at he
    cases he
    exact ⟨b, hb⟩
  obtain ⟨v, hv⟩ := eval_ok_of_msol henv hrel hmrel hu hmembers R.hne R.hnd hlevels
  obtain ⟨m, rfl, hm⟩ := sem_of_eval_msol henv hrel hmrel hu hv
  have hacc : ∀ db, acceptsMsol p k db = acceptsMsolOf p mc db := fun db => by simp [acceptsMsol, hmc]
  refine ⟨hk, m, hv, fun x hx => ?_, fun db hdb => msol_db_onto h ((hm db).mp hdb).1⟩
  rw [hm, hacc]
  exact msol_meaning_iff h hx

/-- **Theorem C for databases**: different assignments over exactly the cells give different
databases. -/
theorem msol_cells_inj {p : Program} {mc : MChain} {M : MFlat} (h : phiMsolOf p mc = .ok M) {x y : Tuple}
    (hx : FitsCells M.cells x) (hy : FitsCells M.cells y)
    (hox : Tuple.Over M.cells.attrs x) (hoy : Tuple.Over M.cells.attrs y)
    (e : msolSubstitute M x = msolSubstitute M y) : x = y := by
  obtain ⟨R⟩ := phiMsolOf_spec h
  obtain ⟨Fs, _, _, _, _, _, _, hFs, hcn, _, _, hM⟩ := R
  have hmem : M.members = Fs := by rw [hM]
  have hcells : M.cells = Fs.flatMap (·.2.cells) := by rw [hM]
  rw [hcells] at hx hy hox hoy
  rw [msolSubstitute, msolSubstitute, hmem] at e
  apply Tuple.ext_get? hox.1 hoy.1
  intro c
  by_cases hc : c ∈ Heading.attrs (Fs.flatMap (·.2.cells))
  · obtain ⟨⟨c', d⟩, hcd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨r, hr, hcr⟩ := List.mem_flatMap.mp hcd
    obtain ⟨q, _, _, hphi⟩ := Pw.mem_right hFs hr
    obtain ⟨Rr⟩ := phiOf_spec hphi
    have hs : substitute r.2 x = substitute r.2 y := congrArg Prod.snd (List.map_inj_left.mp e r hr)
    exact phi_cells_agree Rr (fits_member hcn hx hr) (fits_member hcn hy hr) hs c'
      (List.mem_map_of_mem hcr)
  · rw [get_none_of_over hox hc, get_none_of_over hoy hc]

end Rasso.Phi
