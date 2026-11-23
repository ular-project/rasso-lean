import Rasso.Phi.Sound.Cond
import Rasso.Laws

/-!
# φ's theorems: the commuting square (B) and no hidden refusal (D)

If `phi p k = .ok F` and the assignment `x` gives every
cell a value in its domain, then the flat term evaluates under `x` to a bool `b`, and the
reference evaluator `accepts` gives `.ok b` on the candidate `substitute F x`.
-/

namespace Rasso.Phi

open Rasso

variable {nm : String → Nat → String}

/-! ## φ's construction, named -/

/-- The Data tuples in φ's order (Racket's numbering). -/
def phiRows (data : Finrel) : List Tuple := data.tuples.mergeSort fun s t => !tupleLt data.attrs t s

/-- The copy numbers, from 1. -/
def phiIdx (n : Nat) : List Nat := (List.range n).map (· + 1)

/-- The cells of `n` copies of the Decision heading `uh`. -/
def phiCells (nm : String → Nat → String) (uh : Heading) (n : Nat) : Heading :=
  (phiIdx n).flatMap fun i => uh.map fun (a, d) => (nm a i, d)

/-- The symbolic candidate's rows: Data tuple `i`, then its cells. -/
def phiSymI (nm : String → Nat → String) (dh uh : Heading) (rows : List Tuple) : List SRow :=
  (rows.zip (phiIdx rows.length)).map fun (t, i) =>
    dh.map (fun (a, _) => (a, .val ((t.get? a).getD default))) ++
    uh.map fun (a, _) => (a, .attr (nm a i))

/-- The Decision's term on every copy. -/
def phiPTerms (nm : String → Nat → String) (u : Unrel) (n : Nat) : List Term :=
  if isTrue u.term then [] else
  (phiIdx n).map fun i => substAttrs (u.heading.map fun (a, _) => (a, .attr (nm a i))) u.term

/-- What `phiOf nm p ch = .ok F` tells (`PhiRun` without the statement). -/
structure PhiOfRun (nm : String → Nat → String) (p : Program) (ch : Chain) (F : Flat) where
  data : Finrel
  u : Unrel
  picks : List Tuple
  kinds : Kinds
  conds : List Term
  hom : omegaOf p ch = .ok (data, u, picks)
  hnd : (data.heading ++ u.heading).attrs.Nodup
  hfit : ∀ t ∈ data.tuples, t = fitTuple data.heading t
  hcn : (phiCells nm u.heading (phiRows data).length).attrs.Nodup
  hkinds : cellKinds (phiCells nm u.heading (phiRows data).length) = .ok kinds
  hattrs : ∀ a ∈ u.term.attrs, a ∈ u.heading.attrs
  hconds : Pw (fun lv s => ∃ env, envAt p lv.stmt = .ok env ∧
      lv.cond.checkSubsets env (data.heading ++ u.heading) = .ok () ∧
      sCond (Ctx.sol env kinds lv.marker ⟨data.heading ++ u.heading,
        (phiSymI nm data.heading u.heading (phiRows data)).map (·, tt)⟩) lv.cond = .ok s) ch.levels conds
  hF : F = ⟨data.heading ++ u.heading, u.heading, phiSymI nm data.heading u.heading (phiRows data),
    phiCells nm u.heading (phiRows data).length,
    simpTerm (.call "and" (phiPTerms nm u (phiRows data).length ++ conds))⟩

/-- What `phi p k = .ok F` tells: the chain, the ω_sol it read, the checks it ran, and how
it built `F`. -/
structure PhiRun (p : Program) (k : Nat) (F : Flat) where
  ch : Chain
  data : Finrel
  u : Unrel
  picks : List Tuple
  kinds : Kinds
  conds : List Term
  hch : statementChain p k = some ch
  hom : omegaOf p ch = .ok (data, u, picks)
  hnd : (data.heading ++ u.heading).attrs.Nodup
  hfit : ∀ t ∈ data.tuples, t = fitTuple data.heading t
  hcn : (phiCells cellName u.heading (phiRows data).length).attrs.Nodup
  hkinds : cellKinds (phiCells cellName u.heading (phiRows data).length) = .ok kinds
  hattrs : ∀ a ∈ u.term.attrs, a ∈ u.heading.attrs
  hconds : Pw (fun lv s => ∃ env, envAt p lv.stmt = .ok env ∧
      lv.cond.checkSubsets env (data.heading ++ u.heading) = .ok () ∧
      sCond (Ctx.sol env kinds lv.marker ⟨data.heading ++ u.heading,
        (phiSymI cellName data.heading u.heading (phiRows data)).map (·, tt)⟩) lv.cond = .ok s) ch.levels conds
  hF : F = ⟨data.heading ++ u.heading, u.heading, phiSymI cellName data.heading u.heading (phiRows data),
    phiCells cellName u.heading (phiRows data).length,
    simpTerm (.call "and" (phiPTerms cellName u (phiRows data).length ++ conds))⟩

/-- The chain-level facts of a statement's φ. -/
def PhiRun.toOf {p : Program} {k : Nat} {F : Flat} (R : PhiRun p k F) : PhiOfRun cellName p R.ch F :=
  ⟨R.data, R.u, R.picks, R.kinds, R.conds, R.hom, R.hnd, R.hfit, R.hcn, R.hkinds, R.hattrs, R.hconds, R.hF⟩

theorem phiOf_spec {p : Program} {ch : Chain} {F : Flat} (h : phiOf nm p ch = .ok F) :
    Nonempty (PhiOfRun nm p ch F) := by
  unfold phiOf at h
  simp only [bind, Except.bind] at h
  cases hom : omegaOf p ch with
  | error e => simp [hom] at h
  | ok r =>
  obtain ⟨data, u, picks⟩ := r
  simp only [hom] at h
  split at h
  · cases h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hnd
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hfit
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hcn
  split at h
  · cases h
  rename_i kinds hkinds
  split at h
  · cases h
  rename_i _ hattrs
  split at h
  · cases h
  rename_i conds hconds
  simp only [pure, Except.pure, Except.ok.injEq] at h
  refine ⟨⟨data, u, picks, kinds, conds, hom,
    nodup_of_eraseDups (by simpa only [Heading.attrs, List.length_map] using hnd), ?_,
    nodup_of_eraseDups (by simpa only [Heading.attrs, List.length_map, phiCells, phiRows, phiIdx] using hcn),
    hkinds, ?_, ?_, h.symm⟩⟩
  · intro t ht
    have := hfit
    simp only [List.any_eq_true, bne_iff_ne, ne_eq, not_exists, not_and, Decidable.not_not] at this
    exact this t ht
  · intro a ha
    have := forIn_of_ok (fun a => by
      by_cases hc : u.heading.attrs.contains a = true
      · exact .inr (by simp only [hc, ↓reduceIte]; rfl)
      · exact .inl ⟨_, by simp only [hc, Bool.false_eq_true, ↓reduceIte]; rfl⟩) hattrs a ha
    by_cases hc : u.heading.attrs.contains a = true
    · simpa using hc
    · by_cases hm : a ∈ u.heading.attrs
      · exact hm
      · simp [hm, throw, throwThe, MonadExceptOf.throw] at this
  · refine Pw.imp (fun lv s hs => ?_) (mapM_pw hconds)
    split at hs
    · cases hs
    rename_i env henv
    split at hs
    · cases hs
    rename_i v hck
    exact ⟨env, henv, hck, hs⟩

theorem phi_spec {p : Program} {k : Nat} {F : Flat} (h : phi p k = .ok F) : Nonempty (PhiRun p k F) := by
  unfold phi at h
  cases hch : statementChain p k with
  | none => simp [hch, throw, throwThe, MonadExceptOf.throw] at h
  | some ch =>
  simp only [hch] at h
  obtain ⟨R⟩ := phiOf_spec h
  exact ⟨⟨ch, R.data, R.u, R.picks, R.kinds, R.conds, hch, R.hom, R.hnd, R.hfit, R.hcn, R.hkinds,
    R.hattrs, R.hconds, R.hF⟩⟩

/-! ## Small facts on lookups -/

theorem lookup_some_mem {β : Type} {a : String} {b : β} : ∀ {l : List (String × β)},
    l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp at h
  | (c, d) :: l, h => by
    by_cases hac : a = c
    · subst hac; simp [List.lookup] at h; subst h; simp
    · have : (a == c) = false := by simpa using hac
      rw [List.lookup_cons, this] at h
      exact List.mem_cons_of_mem _ (lookup_some_mem h)

theorem lookup_of_mem_nodup {β : Type} {a : String} {b : β} : ∀ {l : List (String × β)},
    (l.map (·.1)).Nodup → (a, b) ∈ l → l.lookup a = some b
  | [], _, h => by simp at h
  | (c, d) :: l, hn, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp h with e | h
    · cases e; simp [List.lookup]
    · have hac : a ≠ c := fun e => hn.1 ⟨(a, b), h, e⟩
      have : (a == c) = false := by simpa using hac
      rw [List.lookup_cons, this]
      exact lookup_of_mem_nodup hn.2 h

theorem lookup_isSome_of_mem {β : Type} {a : String} {b : β} : ∀ {l : List (String × β)},
    (a, b) ∈ l → ∃ b', l.lookup a = some b'
  | [], h => by simp at h
  | (c, d) :: l, h => by
    by_cases hac : a = c
    · subst hac; exact ⟨d, by simp [List.lookup]⟩
    · have : (a == c) = false := by simpa using hac
      rw [List.lookup_cons, this]
      rcases List.mem_cons.mp h with e | h
      · cases e; exact absurd rfl hac
      · exact lookup_isSome_of_mem h

theorem lookup_map_snd {β γ : Type} (g : β → γ) (a : String) : ∀ (l : List (String × β)),
    (l.map fun p => (p.1, g p.2)).lookup a = (l.lookup a).map g
  | [] => rfl
  | (c, d) :: l => by
    by_cases hac : a = c
    · subst hac; simp [List.lookup]
    · have : (a == c) = false := by simpa using hac
      simp only [List.map_cons, List.lookup_cons, this]
      exact lookup_map_snd g a l

/-! ## The candidate an assignment gives -/

/-- A cell's value under `x`, or a known value (`substitute`'s reading of one term). -/
def substVal (x : Tuple) : Term → Value
  | .attr c => (x.get? c).getD default
  | .val v => v
  | _ => default

/-- One row of the symbolic candidate, with `x`'s values. -/
def substRow (x : Tuple) (row : SRow) : Tuple := Tuple.ofPairs (row.map fun p => (p.1, substVal x p.2))

theorem substitute_eq (F : Flat) (x : Tuple) :
    substitute F x = Finrel.ofTuples F.heading (F.symI.map (substRow x)) := by
  rfl

/-- `x` gives every cell a value in its domain. -/
def FitsCells (cells : Heading) (x : Tuple) : Prop :=
  ∀ c d, cells.lookup c = some d → ∃ v, x.get? c = some v ∧ d.mem v = true

theorem rowInst_substRow {x : Tuple} {row : SRow} (hn : (row.map (·.1)).Nodup)
    (hev : ∀ p ∈ row, p.2.eval x = .ok (substVal x p.2)) : RowInst x row (substRow x row) := by
  intro a
  have hk : ((row.map fun p => (p.1, substVal x p.2)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def] using hn
  rw [substRow, Tuple.get?_ofPairs hk, lookup_map_snd (substVal x) a row]
  cases hl : row.lookup a with
  | none => exact .inl ⟨rfl, rfl⟩
  | some s => exact .inr ⟨s, substVal x s, rfl, hev (a, s) (lookup_some_mem hl), rfl⟩

/-! ## The symbolic candidate denotes `substitute F x` -/

/-- The Data part of a symbolic row. -/
def dPart (dh : Heading) (t : Tuple) : SRow := dh.map fun p => (p.1, .val ((t.get? p.1).getD default))

/-- The Decision part of copy `i`. -/
def uPart (nm : String → Nat → String) (uh : Heading) (i : Nat) : SRow := uh.map fun p => (p.1, .attr (nm p.1 i))

theorem phiSymI_eq (dh uh : Heading) (rows : List Tuple) :
    phiSymI nm dh uh rows = (rows.zip (phiIdx rows.length)).map fun ti => dPart dh ti.1 ++ uPart nm uh ti.2 := rfl

theorem mem_phiSymI {dh uh : Heading} {rows : List Tuple} {row : SRow} :
    row ∈ phiSymI nm dh uh rows ↔ ∃ t i, (t, i) ∈ rows.zip (phiIdx rows.length) ∧ row = dPart dh t ++ uPart nm uh i := by
  rw [phiSymI_eq, List.mem_map]
  constructor
  · rintro ⟨⟨t, i⟩, h, rfl⟩; exact ⟨t, i, h, rfl⟩
  · rintro ⟨t, i, h, rfl⟩; exact ⟨(t, i), h, rfl⟩

theorem row_keys (dh uh : Heading) (t : Tuple) (i : Nat) :
    (dPart dh t ++ uPart nm uh i).map (·.1) = (dh ++ uh).attrs := by
  simp [dPart, uPart, Heading.attrs, Function.comp_def]

theorem mem_phiCells {uh : Heading} {n i : Nat} {a : String} {d : Domain} (hi : i ∈ phiIdx n)
    (ha : (a, d) ∈ uh) : (nm a i, d) ∈ phiCells nm uh n := by
  simp only [phiCells, List.mem_flatMap, List.mem_map]
  exact ⟨i, hi, (a, d), ha, rfl⟩

theorem fits_cell {uh : Heading} {n i : Nat} {x : Tuple} (hx : FitsCells (phiCells nm uh n) x)
    {a : String} {d : Domain} (hi : i ∈ phiIdx n) (ha : (a, d) ∈ uh) :
    ∃ v, x.get? (nm a i) = some v := by
  obtain ⟨d', hd'⟩ := lookup_isSome_of_mem (mem_phiCells hi ha)
  obtain ⟨v, hv, _⟩ := hx _ _ hd'
  exact ⟨v, hv⟩

theorem row_eval {dh uh : Heading} {n i : Nat} {x : Tuple} (hx : FitsCells (phiCells nm uh n) x)
    (hi : i ∈ phiIdx n) (t : Tuple) :
    ∀ p ∈ dPart dh t ++ uPart nm uh i, p.2.eval x = .ok (substVal x p.2) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · simp only [dPart, List.mem_map] at hp
    obtain ⟨q, _, rfl⟩ := hp
    simp [Term.eval, substVal]
  · simp only [uPart, List.mem_map] at hp
    obtain ⟨⟨a, d⟩, hq, rfl⟩ := hp
    obtain ⟨v, hv⟩ := fits_cell hx hi hq
    have hv' : x.get? (nm a i) = some v := hv
    simp [Term.eval, substVal, hv']

theorem nodup_map_of_fst {α β γ : Type} {f : α × β → γ} : ∀ {l : List (α × β)},
    (l.map Prod.fst).Nodup → (∀ a ∈ l, ∀ b ∈ l, f a = f b → a.1 = b.1) → (l.map f).Nodup
  | [], _, _ => .nil
  | a :: l, hn, hf => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn ⊢
    refine ⟨fun b hb e => hn.1 b hb (hf b (List.mem_cons_of_mem _ hb) a List.mem_cons_self e), ?_⟩
    exact nodup_map_of_fst hn.2 fun c hc d hd => hf c (List.mem_cons_of_mem _ hc) d (List.mem_cons_of_mem _ hd)

theorem substRow_data {dh uh : Heading} (hnd : (dh ++ uh).attrs.Nodup) {x t : Tuple} {i : Nat}
    {a : String} (ha : a ∈ dh.attrs) :
    (substRow x (dPart dh t ++ uPart nm uh i)).get? a = some ((t.get? a).getD default) := by
  have hk : (((dPart dh t ++ uPart nm uh i).map fun p => (p.1, substVal x p.2)).map (·.1)).Nodup := by
    rw [List.map_map]; simpa [Function.comp_def, ← row_keys (nm := nm) dh uh t i] using hnd
  rw [substRow, Tuple.get?_ofPairs hk]
  apply lookup_of_mem_nodup hk
  simp only [List.mem_map, List.mem_append]
  simp only [Heading.attrs, List.mem_map] at ha
  obtain ⟨q, hq, rfl⟩ := ha
  exact ⟨(q.1, .val ((t.get? q.1).getD default)), .inl (by simp only [dPart, List.mem_map]; exact ⟨q, hq, rfl⟩), rfl⟩

theorem cand_denotes {dh uh : Heading} {rows : List Tuple} {x : Tuple}
    (hnd : (dh ++ uh).attrs.Nodup) (hfit : ∀ t ∈ rows, t = fitTuple dh t) (hrows : rows.Nodup)
    (hx : FitsCells (phiCells nm uh rows.length) x) :
    Denotes x ⟨dh ++ uh, (phiSymI nm dh uh rows).map (·, tt)⟩
      (Finrel.ofTuples (dh ++ uh) ((phiSymI nm dh uh rows).map (substRow x))) := by
  have hrow : ∀ row ∈ phiSymI nm dh uh rows, (row.map (·.1)).Nodup ∧
      ∀ p ∈ row, p.2.eval x = .ok (substVal x p.2) := by
    intro row hr
    obtain ⟨t, i, hti, rfl⟩ := mem_phiSymI.mp hr
    exact ⟨by rw [row_keys]; exact hnd, row_eval hx (List.of_mem_zip hti).2 t⟩
  refine ⟨rfl, hnd, ?_, ?_⟩
  · intro rg hrg
    simp only [List.mem_map] at hrg
    obtain ⟨row, hr, rfl⟩ := hrg
    obtain ⟨t, i, _, rfl⟩ := mem_phiSymI.mp hr
    exact row_keys (nm := nm) dh uh t i
  refine ⟨(phiSymI nm dh uh rows).map fun row => (substRow x row, true), ?_, ?_, ?_, ?_⟩
  · exact Pw.of_map fun row hr => ⟨rowInst_substRow (hrow row hr).1 (hrow row hr).2, isTrue_eval rfl x⟩
  · intro ub hub
    simp only [List.mem_map] at hub
    obtain ⟨row, hr, rfl⟩ := hub
    have hk : ((row.map fun p => (p.1, substVal x p.2)).map (·.1)).Nodup := by
      rw [List.map_map]; simpa [Function.comp_def] using (hrow row hr).1
    exact Tuple.sorted_ofPairs hk
  · have hp : presentT ((phiSymI nm dh uh rows).map fun row => (substRow x row, true)) =
        (phiSymI nm dh uh rows).map (substRow x) := by
      simp [presentT, Function.comp_def]
    rw [hp, phiSymI_eq, List.map_map]
    apply nodup_map_of_fst
    · rw [List.map_fst_zip (by simp [phiIdx])]; exact hrows
    · intro ⟨t, i⟩ hti ⟨t', i'⟩ hti' e
      simp only [Function.comp_apply] at e
      have ht := hfit t (List.of_mem_zip hti).1
      have ht' := hfit t' (List.of_mem_zip hti').1
      show t = t'
      rw [ht, ht']
      simp only [fitTuple]
      apply congrArg Tuple.ofPairs
      apply List.map_congr_left
      intro q hq
      have hqa : q.1 ∈ dh.attrs := List.mem_map_of_mem hq
      have h1 := substRow_data (nm := nm) (x := x) (t := t) (i := i) (uh := uh) hnd hqa
      have h2 := substRow_data (nm := nm) (x := x) (t := t') (i := i') (uh := uh) hnd hqa
      rw [e, h2] at h1
      simp only [Option.some.injEq] at h1
      rw [h1]
  · intro t
    have hp : presentT ((phiSymI nm dh uh rows).map fun row => (substRow x row, true)) =
        (phiSymI nm dh uh rows).map (substRow x) := by
      simp [presentT, Function.comp_def]
    rw [hp, Finrel.mem_ofTuples]

/-! ## The ω_sol φ read -/

theorem omegaOf_spec {p : Program} {ch : Chain} {data : Finrel} {u : Unrel} {picks : List Tuple}
    (h : omegaOf p ch = .ok (data, u, picks)) :
    ∃ env, envAt p ch.stmt = .ok env ∧
      (∃ dv, Expr.eval env [] ch.data = .ok dv ∧ dv.asFinrel "ω_sol data" = .ok data) ∧
      (∃ uv, Expr.eval env [] ch.decision = .ok uv ∧ uv.asUnrel = .ok u) ∧
      (∀ a ∈ u.heading.attrs, ¬ a ∈ data.attrs) ∧ u.tuples = .ok picks := by
  unfold omegaOf at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i env henv
  split at h
  · cases h
  rename_i dv hdv
  split at h
  · cases h
  rename_i data' hdata
  split at h
  · cases h
  rename_i uv huv
  split at h
  · cases h
  rename_i u' hu
  split at h
  · cases h
  rename_i _ hfor
  split at h
  · cases h
  rename_i picks' hpicks
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨env, henv, ⟨dv, hdv, hdata⟩, ⟨uv, huv, hu⟩, ?_, hpicks⟩
  intro a ha hd
  have := forIn_of_ok (fun a => by
    by_cases hc : data'.attrs.contains a = true
    · exact .inl ⟨_, by simp only [hc, ↓reduceIte]; rfl⟩
    · exact .inr (by simp only [hc, Bool.false_eq_true, ↓reduceIte]; rfl)) hfor a ha
  simp [hd, throw, throwThe, MonadExceptOf.throw] at this

/-- The Decision's term ran on every assignment of the Decision's heading without refusal. -/
theorem holds_ok_of_tuples {u : Unrel} {picks : List Tuple} (h : u.tuples = .ok picks) {t : Tuple}
    {as : List Tuple} (has : Unrel.assignments u.heading = .ok as) (ht : t ∈ as) :
    ∃ b, u.term.holds t = .ok b := by
  simp only [Unrel.tuples, has, bind, Except.bind] at h
  have := (filterM_ok_iff.mp h).1 t ht
  revert this
  cases u.term.holds t with
  | ok b => intro; exact ⟨b, rfl⟩
  | error e => intro h; exact h.elim

/-! ## The copies' Decision tuples -/

/-- Copy `i`'s Decision tuple under `x`. -/
def decOf (nm : String → Nat → String) (x : Tuple) (uh : Heading) (i : Nat) : Tuple :=
  Tuple.ofPairs (uh.map fun p => (p.1, (x.get? (nm p.1 i)).getD default))

theorem cellKinds_values {cells : Heading} {kinds : Kinds} (h : cellKinds cells = .ok kinds) :
    ∀ c ∈ cells, ∃ vs, c.2.values? = some vs := by
  intro c hc
  have hpw := mapM_pw h
  obtain ⟨k, hk⟩ : ∃ k, (match domKinds c.2 with
      | some ks => (.ok (c.1, ks) : Except String (String × List VK))
      | none => .error s!"φ: the domain of {c.1} is not finite, or holds a float") = .ok k := by
    clear h
    induction hpw with
    | nil => simp at hc
    | cons hab _ ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨_, hab⟩
      · exact ih hc
  cases hd : domKinds c.2 with
  | none => simp [hd] at hk
  | some ks =>
    simp only [domKinds, bind, Option.bind] at hd
    cases hv : c.2.values? with
    | none => simp [hv] at hd
    | some vs => exact ⟨vs, rfl⟩

theorem fits_map {uh : Heading} {val : String → Value}
    (h : ∀ q ∈ uh, ∃ vs, q.2.values? = some vs ∧ val q.1 ∈ vs) :
    Fits uh (uh.map fun q => (q.1, val q.1)) := by
  induction uh with
  | nil => exact .nil
  | cons q uh ih =>
    obtain ⟨vs, hvs, hv⟩ := h q List.mem_cons_self
    exact .cons hvs hv (ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))

theorem decOf_mem {uh : Heading} {n i : Nat} {x : Tuple} {kinds : Kinds}
    (hun : uh.attrs.Nodup) (hcn : (phiCells nm uh n).attrs.Nodup)
    (hk : cellKinds (phiCells nm uh n) = .ok kinds) (hx : FitsCells (phiCells nm uh n) x)
    (hi : i ∈ phiIdx n) {as : List Tuple} (has : Unrel.assignments uh = .ok as) :
    decOf nm x uh i ∈ as := by
  rw [Unrel.mem_assignments has]
  refine ⟨uh.map fun q => (q.1, (x.get? (nm q.1 i)).getD default), fits_map (val := fun a => (x.get? (nm a i)).getD default) ?_, ?_⟩
  · intro q hq
    have hmem := mem_phiCells (nm := nm) (n := n) hi (show (q.1, q.2) ∈ uh from hq)
    obtain ⟨vs, hvs⟩ := cellKinds_values hk _ hmem
    obtain ⟨v, hv, hm⟩ := hx _ _ (lookup_of_mem_nodup hcn hmem)
    refine ⟨vs, hvs, ?_⟩
    rw [hv]
    exact Domain.values?_sound hvs hm
  · have hk' : ((uh.map fun q => (q.1, (x.get? (nm q.1 i)).getD default)).map (·.1)).Nodup := by
      simpa [List.map_map, Function.comp_def, Heading.attrs] using hun
    apply ofPairs_eq hk' (by rw [List.map_reverse]; exact (List.reverse_perm _).nodup_iff.mpr hk')
    intro q; simp

/-- What `accepts` reads of a candidate tuple, for copy `i`, is copy `i`'s Decision tuple. -/
theorem restrict_substRow {dh uh : Heading} (hnd : (dh ++ uh).attrs.Nodup) (x t : Tuple) (i : Nat) :
    Tuple.ofPairs ((substRow x (dPart dh t ++ uPart nm uh i)).restrict uh.attrs) = decOf nm x uh i := by
  have hk : (((dPart dh t ++ uPart nm uh i).map fun p => (p.1, substVal x p.2)).map (·.1)).Nodup := by
    rw [List.map_map]; simpa [Function.comp_def, ← row_keys (nm := nm) dh uh t i] using hnd
  have hun : uh.attrs.Nodup := by
    simp only [Heading.attrs, List.map_append] at hnd; exact (List.nodup_append.mp hnd).2.1
  have hdis : ∀ a ∈ dh.attrs, a ∉ uh.attrs := by
    intro a ha hb
    simp only [Heading.attrs, List.map_append] at hnd
    exact (List.nodup_append.mp hnd).2.2 a ha a hb rfl
  have hr : (((substRow x (dPart dh t ++ uPart nm uh i)).restrict uh.attrs).map (·.1)).Nodup := by
    unfold Tuple.restrict substRow
    apply List.Nodup.sublist (List.filter_sublist.map _)
    exact ((List.mergeSort_perm _ _).map _).nodup_iff.mpr hk
  have hd : ((uh.map fun q => (q.1, (x.get? (nm q.1 i)).getD default)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def, Heading.attrs] using hun
  unfold decOf
  apply ofPairs_eq hr hd
  intro ⟨a, v⟩
  simp only [Tuple.restrict, substRow, List.mem_filter, mem_ofPairs, List.mem_map, List.mem_append,
    List.contains_iff_mem, dPart, uPart]
  constructor
  · rintro ⟨⟨q, hq, e⟩, hc⟩
    rcases hq with ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
    · simp only [Prod.mk.injEq] at e
      exact absurd (e.1 ▸ hc) (hdis _ (List.mem_map_of_mem hq'))
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨q', hq', rfl⟩
  · rintro ⟨q, hq, e⟩
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨⟨(q.1, .attr (nm q.1 i)), .inr ⟨q, hq, rfl⟩, rfl⟩, List.mem_map_of_mem hq⟩

/-! ## `accepts`, unfolded -/

/-- A `for` loop that stops at the first false step, when every step is `.ok`. -/
theorem forIn_early {α ε σ : Type} {g : α → σ → Except ε (ForInStep σ)} {s0 s1 : σ} :
    ∀ {l : List α} {bs : List Bool},
      Pw (fun a b => g a s0 = .ok (if b then .yield s0 else .done s1)) l bs →
      forIn l s0 g = .ok (if bs.all id then s0 else s1)
  | [], [], .nil => rfl
  | a :: l, b :: bs, .cons hb hl => by
    rw [List.forIn_cons, hb]
    cases b
    · rfl
    · simp only [↓reduceIte, bind, Except.bind, List.all_cons, id, Bool.true_and]
      exact forIn_early hl

theorem acceptsOf_eq {p : Program} {cand : Finrel} {ch : Chain} {d : Finrel} {u : Unrel}
    {pk : List Tuple} (hom : omegaOf p ch = .ok (d, u, pk))
    {bt : List Bool} (h1 : Pw (fun t b => u.term.holds (Tuple.ofPairs (t.restrict u.heading.attrs)) = .ok b)
      cand.tuples bt)
    {bs : List Bool} (h2 : Pw (fun lv b => ∃ env, envAt p lv.stmt = .ok env ∧
      lv.cond.eval (candEnv env (.finrel cand)) [lv.marker] = .ok b) ch.levels bs) :
    acceptsOf p ch cand = .ok (bt.all id && bs.all id) := by
  unfold acceptsOf
  simp only [hom, bind, Except.bind]
  rw [forIn_early (bs := bt) (s1 := (some false, ())) (Pw.imp (fun t b hb => by
    simp only [hb]; cases b <;> rfl) h1)]
  cases hbt : bt.all id
  · rfl
  · simp only [↓reduceIte]
    rw [forIn_early (bs := bs) (s1 := (some false, ())) (Pw.imp (fun lv b ⟨env, he, hb⟩ => by
      simp only [he]; rw [show inCondition ((candidateName, Val.finrel cand) :: env) = candEnv env (.finrel cand)
        from rfl, hb]; cases b <;> rfl) h2)]
    cases bs.all id <;> rfl

theorem accepts_of_chain {p : Program} {k : Nat} {ch : Chain} (hch : statementChain p k = some ch)
    (cand : Finrel) : accepts p k cand = acceptsOf p ch cand := by
  simp [accepts, hch]

/-! ## Theorems B and D -/

theorem cellsOk_of_fits {cells : Heading} {kinds : Kinds} {x : Tuple} (hk : cellKinds cells = .ok kinds)
    (hx : FitsCells cells x) : CellsOk kinds x := by
  intro c ks hl
  obtain ⟨d, hd, hdk⟩ := cellKinds_lookup hk hl
  obtain ⟨v, hv, hm⟩ := hx c d hd
  exact ⟨v, hv, domKinds_mem hdk hm⟩

theorem holds_eval {t : Tuple} {e : Term} {b : Bool} (h : e.holds t = .ok b) : e.eval t = .ok (.bool b) := by
  simp only [Term.holds, bind, Except.bind] at h
  split at h
  · cases h
  rename_i v hv
  cases v <;> simp [asBool] at h
  subst h; exact hv

/-- The value of an `Except` known to succeed. -/
def okB : Except String Bool → Bool
  | .ok b => b
  | .error _ => false

theorem okB_eq {e : Except String Bool} {b : Bool} (h : e = .ok b) : e = .ok (okB e) := by
  subst h; rfl

theorem decOf_get {uh : Heading} (hun : uh.attrs.Nodup) {x : Tuple} {i : Nat} {a : String} {d : Domain}
    (ha : (a, d) ∈ uh) : (decOf nm x uh i).get? a = some ((x.get? (nm a i)).getD default) := by
  have hk : ((uh.map fun q => (q.1, (x.get? (nm q.1 i)).getD default)).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def, Heading.attrs] using hun
  rw [decOf, Tuple.get?_ofPairs hk]
  exact lookup_of_mem_nodup hk (List.mem_map.mpr ⟨(a, d), ha, rfl⟩)

theorem pTerm_eval {uh : Heading} (hun : uh.attrs.Nodup) {n i : Nat} {x : Tuple}
    (hx : FitsCells (phiCells nm uh n) x) (hi : i ∈ phiIdx n) {t : Term}
    (hattrs : ∀ a ∈ t.attrs, a ∈ uh.attrs) :
    (substAttrs (uh.map fun (a, _) => (a, .attr (nm a i))) t).eval x = t.eval (decOf nm x uh i) := by
  apply substAttrs_sound
  intro a ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hattrs a ha)
  have hk : ((uh.map fun (a, _) => (a, Term.attr (nm a i))).map (·.1)).Nodup := by
    simpa [List.map_map, Function.comp_def, Heading.attrs] using hun
  refine ⟨.attr (nm q.1 i), lookup_of_mem_nodup hk (List.mem_map.mpr ⟨q, hq, rfl⟩), ?_⟩
  obtain ⟨v, hv⟩ := fits_cell hx hi (show (q.1, q.2) ∈ uh from hq)
  have hd := decOf_get (nm := nm) (x := x) (i := i) hun (show (q.1, q.2) ∈ uh from hq)
  rw [hv] at hd
  simp only [Term.eval, hv, hd, Option.getD_some]

/-- The bools of the copies: the Decision's term on each copy's Decision tuple. -/
def copiesB (nm : String → Nat → String) (u : Unrel) (n : Nat) (x : Tuple) : Bool :=
  (phiIdx n).all fun i => okB (u.term.holds (decOf nm x u.heading i))

/-- The pieces of the square: the levels' bools `bs` (each level evaluates on `substitute F x`
without refusal), the flat term's value, and `accepts`' value, both `copiesB && bs.all id`. -/
theorem square_parts {p : Program} {ch : Chain} {F : Flat} (R : PhiOfRun nm p ch F) {x : Tuple}
    (hx : FitsCells F.cells x) :
    ∃ bs, Pw (fun (lv : Level) b => ∃ env, envAt p lv.stmt = .ok env ∧
        lv.cond.eval (candEnv env (.finrel (substitute F x))) [lv.marker] = .ok b) ch.levels bs ∧
      F.term.eval x = .ok (.bool (copiesB nm R.u (phiRows R.data).length x && bs.all id)) ∧
      acceptsOf p ch (substitute F x) = .ok (copiesB nm R.u (phiRows R.data).length x && bs.all id) := by
  obtain ⟨data, u, picks, kinds, conds, hom, hnd, hfit, hcn, hkinds, hattrs, hconds, rfl⟩ := R
  dsimp only at hx ⊢
  -- names
  have hrows : (phiRows data).Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (Finrel.nodup_tuples data)
  have hfitr : ∀ t ∈ phiRows data, t = fitTuple data.heading t :=
    fun t ht => hfit t (List.mem_mergeSort.mp ht)
  have hun : u.heading.attrs.Nodup := by
    have := hnd; simp only [Heading.attrs, List.map_append] at this; exact (List.nodup_append.mp this).2.1
  have hcok := cellsOk_of_fits hkinds hx
  have hden := cand_denotes hnd hfitr hrows hx
  rw [substitute_eq]
  dsimp only
  -- the Decision's term on every copy
  obtain ⟨_, _, _, _, _, hpicks⟩ := omegaOf_spec hom
  obtain ⟨as, has⟩ : ∃ as, Unrel.assignments u.heading = .ok as := by
    cases ha : Unrel.assignments u.heading with
    | ok as => exact ⟨as, rfl⟩
    | error e => simp [Unrel.tuples, ha, bind, Except.bind] at hpicks
  have hcopy : ∀ i ∈ phiIdx (phiRows data).length,
      u.term.holds (decOf nm x u.heading i) = .ok (okB (u.term.holds (decOf nm x u.heading i))) := by
    intro i hi
    obtain ⟨b, hb⟩ := holds_ok_of_tuples hpicks has (decOf_mem hun hcn hkinds hx hi has)
    exact okB_eq hb
  -- the conditions
  obtain ⟨bs, hT, hU⟩ := Pw.build (T := fun s b => s.eval x = .ok (.bool b))
    (U := fun (lv : Level) b => ∃ env, envAt p lv.stmt = .ok env ∧
      lv.cond.eval (candEnv env (.finrel (Finrel.ofTuples (data.heading ++ u.heading)
        ((phiSymI nm data.heading u.heading (phiRows data)).map (substRow x))))) [lv.marker] = .ok b)
    (fun (lv : Level) s (lv' : Level) ⟨env, he, hck, hs⟩ e => by
      subst lv'
      obtain ⟨b, hb, hc⟩ := sCond_sound_sol (env := env) (m := lv.marker) hcok hden
        (by simp [List.all_map, isTrue, tt]) lv.cond hck hs
      exact ⟨b, hb, env, he, hc⟩) hconds (Pw.refl' ch.levels)
  -- the copies' bools
  let pb : List Bool := if isTrue u.term then [] else
    (phiIdx (phiRows data).length).map fun i => okB (u.term.holds (decOf nm x u.heading i))
  have hP : Pw (fun t b => t.eval x = .ok (.bool b)) (phiPTerms nm u (phiRows data).length) pb := by
    simp only [phiPTerms, pb]
    split
    · exact .nil
    · exact Pw.of_map fun i hi => by
        rw [pTerm_eval hun hx hi hattrs]; exact holds_eval (hcopy i hi)
  have hargs := mapM_of_pw (g := Value.bool) (Pw.append hP hT)
  have hand : (Term.call "and" (phiPTerms nm u (phiRows data).length ++ conds)).eval x =
      .ok (.bool ((pb ++ bs).all id)) := by
    rw [eval_call, hargs]
    exact applyOp_andor_bools true (pb ++ bs)
  have htt : isTrue u.term = true → ∀ t, u.term.holds t = .ok true := by
    intro ht t
    have : u.term = .val (.bool true) := by
      revert ht; cases u.term <;> simp [isTrue]; rename_i v; cases v <;> simp; rename_i b; cases b <;> simp
    simp [this, Term.holds, Term.eval, asBool, bind, Except.bind]
  have hpb : pb.all id = copiesB nm u (phiRows data).length x := by
    simp only [pb, copiesB]
    split
    · rename_i ht
      show true = _
      symm; rw [List.all_eq_true]; intro i _; simp [htt ht, okB]
    · rw [List.all_map]; rfl
  refine ⟨bs, hU, by rw [simpTerm_sound x _ hand, List.all_append, hpb], ?_⟩
  -- the reference evaluator
  let cand := Finrel.ofTuples (data.heading ++ u.heading)
    ((phiSymI nm data.heading u.heading (phiRows data)).map (substRow x))
  have hmem : ∀ t ∈ cand.tuples, ∃ i ∈ phiIdx (phiRows data).length,
      Tuple.ofPairs (t.restrict u.heading.attrs) = decOf nm x u.heading i := by
    intro t ht
    rw [Finrel.mem_ofTuples, List.mem_map] at ht
    obtain ⟨row, hr, rfl⟩ := ht
    obtain ⟨t', i, hti, rfl⟩ := mem_phiSymI.mp hr
    exact ⟨i, (List.of_mem_zip hti).2, restrict_substRow hnd x t' i⟩
  have h1 : Pw (fun t b => u.term.holds (Tuple.ofPairs (t.restrict u.heading.attrs)) = .ok b) cand.tuples
      (cand.tuples.map fun t => okB (u.term.holds (Tuple.ofPairs (t.restrict u.heading.attrs)))) := by
    have := Pw.of_map (R := fun t b => u.term.holds (Tuple.ofPairs (t.restrict u.heading.attrs)) = .ok b)
      (f := id) (g := fun t => okB (u.term.holds (Tuple.ofPairs (t.restrict u.heading.attrs))))
      (l := cand.tuples) fun t ht => by
        obtain ⟨i, hi, e⟩ := hmem t ht
        simp only [id, e]; exact hcopy i hi
    simpa using this
  rw [acceptsOf_eq hom h1 hU, ← hpb]
  suffices hA : (cand.tuples.map fun t => okB (u.term.holds (Tuple.ofPairs (t.restrict u.heading.attrs)))).all id
      = pb.all id by rw [hA]
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  simp only [List.mem_map, id, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  simp only [pb]
  split
  · rename_i ht
    simp only [List.not_mem_nil, false_implies, implies_true, iff_true]
    intro t _
    simp [htt ht, okB]
  · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · intro hall i hi
      have hs : i ∈ ((phiRows data).zip (phiIdx (phiRows data).length)).map Prod.snd := by
        rw [List.map_snd_zip (by simp [phiIdx])]; exact hi
      obtain ⟨⟨t', i'⟩, hti, rfl⟩ := List.mem_map.mp hs
      have := hall (substRow x (dPart data.heading t' ++ uPart nm u.heading i'))
        (by rw [Finrel.mem_ofTuples]; exact List.mem_map.mpr ⟨_, mem_phiSymI.mpr ⟨t', i', hti, rfl⟩, rfl⟩)
      rwa [restrict_substRow hnd] at this
    · intro hall t ht
      obtain ⟨i, hi, e⟩ := hmem t ht
      rw [e]; exact hall i hi

/-- **Theorem B** (with **D**, its `.ok`): when φ succeeds, under every assignment that gives
each cell a value in its domain, the flat term and the reference evaluator agree on the
candidate the assignment gives, and neither refuses. -/
theorem phi_square {p : Program} {k : Nat} {F : Flat} (h : phi p k = .ok F) {x : Tuple}
    (hx : FitsCells F.cells x) :
    ∃ b, F.term.eval x = .ok (.bool b) ∧ accepts p k (substitute F x) = .ok b := by
  obtain ⟨R⟩ := phi_spec h
  obtain ⟨bs, _, h1, h2⟩ := square_parts R.toOf hx
  exact ⟨_, h1, by rw [accepts_of_chain R.hch]; exact h2⟩

/-- **Theorem D**: when φ succeeds, the reference evaluator does not refuse on any
candidate φ can describe. -/
theorem phi_no_refusal {p : Program} {k : Nat} {F : Flat} (h : phi p k = .ok F) {x : Tuple}
    (hx : FitsCells F.cells x) : ∃ b, accepts p k (substitute F x) = .ok b :=
  let ⟨b, _, hb⟩ := phi_square h hx; ⟨b, hb⟩

end Rasso.Phi
