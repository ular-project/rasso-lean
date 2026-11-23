import Rasso.Eval

/-!
# The φ fragment

φ unrolls a solution set into one relation over cells (`Rasso.Phi.Phi`). This file says, on
forms alone, which solution-set statements φ takes: a Lean port of Racket's grammar of
conditions (`condition?` and `rexp-over?`) and of its leaves (`candidate-leaf`).

Each check is a `Bool` function, with a `Prop` beside it and an `_iff` theorem:

* `Expr.mentions m f`: some sub-form of `f`, anywhere, is `m`. `Expr.hasSolForm f`: `f`
  holds a solution-set or multiple-solution-set form. `IsLeaf m f`: neither.
* `Term.phiOk`, `PhiTerm`: a term φ can read (known operators, no float).
* `Agg.phiOk`, `PhiAgg`: γ's expression, with `has_subset` of a leaf.
* `Expr.phiExpr`, `PhiExpr`: a relational expression over the candidate `m`: `m` itself, a
  leaf, γ, `extend`, or a join.
* `Cond.phiCond`, `PhiCond`: `and`, `or`, `not`, `has_subset` of a leaf, a relational
  expression.
* `chainOf`, `Unfolds`: a statement unfolds, through the names of earlier statements, into
  `σ_sol[cₙ](… σ_sol[c₁](ω_sol[D, Dec]))`, each level with its marker as written and the
  statement that wrote it. `programChains`, `InPhiFragment`.

Refusals that depend on values (a leaf whose value is a solution set, a float in the data,
grouping by a cell, a type error) are not here: they are φ's own (`Rasso.Phi.Phi`).

Conventions:

* The fragment is Racket's grammar, not Lean's evaluator's. Lean's evaluator also accepts
  σ, π, ρ, ∪, ∩ and − over the candidate inside a condition; Racket refuses them, and so
  does φ.
* `mentions` is conservative: a candidate mentioned only inside `has_subset`, where the
  evaluator would not read it as the candidate, still counts.
  That costs acceptance only.
* A leaf holds no solution-set form, even one Racket would evaluate (`ℰ_sol` inside
  `flatten`). A nested solution set binds a candidate of its own, and a nested multi
  solution set's `has_subset` would read the outer candidate (`Eval.lean`, `Cond.eval`);
  leaving them out makes "a leaf does not read the candidate" a plain induction.
* Arity and types are checked by φ's static pass (`Rasso.Phi.Phi`), not here.
-/

namespace Rasso

@[simp] theorem NOp.beq_self (o : NOp) : (o == o) = true := by cases o <;> rfl
@[simp] theorem Order.beq_self (o : Order) : (o == o) = true := by cases o <;> rfl
@[simp] theorem Count.beq_self (c : Count) : (c == c) = true := by
  cases c with
  | all => rfl
  | int k => show (k == k) = true; simp

/-! ## `Expr.beq` is reflexive -/

mutual
theorem Expr.beq_refl : (r : Expr) → r.beq r = true
  | .name _ => by simp [Expr.beq]
  | .omega h => by simp [Expr.beq, headBeq_refl h]
  | .omegaWhere h t => by simp [Expr.beq, headBeq_refl h, Term.beq_refl t]
  | .omegaRows h _ => by simp [Expr.beq, headBeq_refl h]
  | .select t r => by simp [Expr.beq, Term.beq_refl t, Expr.beq_refl r]
  | .project _ r => by simp [Expr.beq, Expr.beq_refl r]
  | .rename _ r => by simp [Expr.beq, Expr.beq_refl r]
  | .nary _ es => by simp [Expr.beq, exprsBeq_refl es]
  | .gamma _ x _ r => by simp [Expr.beq, Agg.beq_refl x, Expr.beq_refl r]
  | .extend _ t r => by simp [Expr.beq, Term.beq_refl t, Expr.beq_refl r]
  | .enum _ none r => by simp [Expr.beq, Expr.beq_refl r]
  | .enum _ (some (_, t)) r => by simp [Expr.beq, Term.beq_refl t, Expr.beq_refl r]
  | .omegaSol a b => by simp [Expr.beq, Expr.beq_refl a, Expr.beq_refl b]
  | .sigmaSol c r => by simp [Expr.beq, Cond.beq_refl c, Expr.beq_refl r]
  | .enumSol _ none r => by simp [Expr.beq, Expr.beq_refl r]
  | .enumSol _ (some (_, k)) r => by simp [Expr.beq, Expr.beq_refl k, Expr.beq_refl r]
  | .omegaMsol ms none => by simp [Expr.beq, membersBeq_refl ms]
  | .omegaMsol ms (some c) => by simp [Expr.beq, membersBeq_refl ms, Cond.beq_refl c]
  | .sigmaMsol c r => by simp [Expr.beq, Cond.beq_refl c, Expr.beq_refl r]
  | .enumMsol _ none r => by simp [Expr.beq, Expr.beq_refl r]
  | .enumMsol _ (some (_, k)) r => by simp [Expr.beq, Expr.beq_refl k, Expr.beq_refl r]
  | .flattenMsol _ r => by simp [Expr.beq, Expr.beq_refl r]
  | .dbRef _ r => by simp [Expr.beq, Expr.beq_refl r]
  | .flatten _ r => by simp [Expr.beq, Expr.beq_refl r]
  | .forget r => by simp [Expr.beq, Expr.beq_refl r]
  | .lift r => by simp [Expr.beq, Expr.beq_refl r]
theorem exprsBeq_refl : (rs : List Expr) → exprsBeq rs rs = true
  | [] => by simp [exprsBeq]
  | r :: rs => by simp [exprsBeq, Expr.beq_refl r, exprsBeq_refl rs]
theorem membersBeq_refl : (ms : List (String × Expr)) → membersBeq ms ms = true
  | [] => by simp [membersBeq]
  | (_, r) :: ms => by simp [membersBeq, Expr.beq_refl r, membersBeq_refl ms]
theorem headBeq_refl : (h : List (String × DomExpr)) → headBeq h h = true
  | [] => by simp [headBeq]
  | (_, d) :: h => by simp [headBeq, DomExpr.beq_refl d, headBeq_refl h]
theorem DomExpr.beq_refl : (d : DomExpr) → d.beq d = true
  | .kind _ => by simp [DomExpr.beq]
  | .range _ _ => by simp [DomExpr.beq]
  | .set _ => by simp [DomExpr.beq]
  | .in_ r => by simp [DomExpr.beq, Expr.beq_refl r]
theorem Term.beq_refl : (t : Term) → t.beq t = true
  | .attr _ => by simp [Term.beq]
  | .val _ => by simp [Term.beq]
  | .call _ xs => by simp [Term.beq, termsBeq_refl xs]
theorem termsBeq_refl : (ts : List Term) → termsBeq ts ts = true
  | [] => by simp [termsBeq]
  | t :: ts => by simp [termsBeq, Term.beq_refl t, termsBeq_refl ts]
theorem Agg.beq_refl : (x : Agg) → x.beq x = true
  | .attr _ => by simp [Agg.beq]
  | .val _ => by simp [Agg.beq]
  | .call _ xs => by simp [Agg.beq, aggsBeq_refl xs]
  | .agg _ t => by simp [Agg.beq, Term.beq_refl t]
  | .hasSubset r => by simp [Agg.beq, Expr.beq_refl r]
theorem aggsBeq_refl : (xs : List Agg) → aggsBeq xs xs = true
  | [] => by simp [aggsBeq]
  | x :: xs => by simp [aggsBeq, Agg.beq_refl x, aggsBeq_refl xs]
theorem Cond.beq_refl : (c : Cond) → c.beq c = true
  | .and cs => by simp [Cond.beq, condsBeq_refl cs]
  | .or cs => by simp [Cond.beq, condsBeq_refl cs]
  | .not c => by simp [Cond.beq, Cond.beq_refl c]
  | .hasSubset r => by simp [Cond.beq, Expr.beq_refl r]
  | .expr r => by simp [Cond.beq, Expr.beq_refl r]
theorem condsBeq_refl : (cs : List Cond) → condsBeq cs cs = true
  | [] => by simp [condsBeq]
  | c :: cs => by simp [condsBeq, Cond.beq_refl c, condsBeq_refl cs]
end

/-! ## Sub-forms

`Expr.anySub P f`: `P` holds of some relation position inside `f`, `f` included, at any
depth and in any syntactic category (domains `in R`, γ's `has_subset`, nested conditions
and keys). -/

mutual
def Expr.anySub (P : Expr → Bool) : Expr → Bool
  | f@(.name _) => P f
  | f@(.omega h) => P f || headAnySub P h
  | f@(.omegaWhere h _) => P f || headAnySub P h
  | f@(.omegaRows h _) => P f || headAnySub P h
  | f@(.select _ r) => P f || r.anySub P
  | f@(.project _ r) => P f || r.anySub P
  | f@(.rename _ r) => P f || r.anySub P
  | f@(.nary _ es) => P f || exprsAnySub P es
  | f@(.gamma _ x _ r) => P f || x.anySub P || r.anySub P
  | f@(.extend _ _ r) => P f || r.anySub P
  | f@(.enum _ _ r) => P f || r.anySub P
  | f@(.omegaSol a b) => P f || a.anySub P || b.anySub P
  | f@(.sigmaSol c r) => P f || c.anySub P || r.anySub P
  | f@(.enumSol _ none r) => P f || r.anySub P
  | f@(.enumSol _ (some (_, k)) r) => P f || k.anySub P || r.anySub P
  | f@(.omegaMsol ms none) => P f || membersAnySub P ms
  | f@(.omegaMsol ms (some c)) => P f || membersAnySub P ms || c.anySub P
  | f@(.sigmaMsol c r) => P f || c.anySub P || r.anySub P
  | f@(.enumMsol _ none r) => P f || r.anySub P
  | f@(.enumMsol _ (some (_, k)) r) => P f || k.anySub P || r.anySub P
  | f@(.flattenMsol _ r) => P f || r.anySub P
  | f@(.dbRef _ r) => P f || r.anySub P
  | f@(.flatten _ r) => P f || r.anySub P
  | f@(.forget r) => P f || r.anySub P
  | f@(.lift r) => P f || r.anySub P
def exprsAnySub (P : Expr → Bool) : List Expr → Bool
  | [] => false
  | r :: rs => r.anySub P || exprsAnySub P rs
def membersAnySub (P : Expr → Bool) : List (String × Expr) → Bool
  | [] => false
  | (_, r) :: ms => r.anySub P || membersAnySub P ms
def headAnySub (P : Expr → Bool) : List (String × DomExpr) → Bool
  | [] => false
  | (_, d) :: h => d.anySub P || headAnySub P h
def DomExpr.anySub (P : Expr → Bool) : DomExpr → Bool
  | .in_ r => r.anySub P
  | _ => false
def Agg.anySub (P : Expr → Bool) : Agg → Bool
  | .call _ xs => aggsAnySub P xs
  | .hasSubset r => r.anySub P
  | _ => false
def aggsAnySub (P : Expr → Bool) : List Agg → Bool
  | [] => false
  | x :: xs => x.anySub P || aggsAnySub P xs
def Cond.anySub (P : Expr → Bool) : Cond → Bool
  | .and cs => condsAnySub P cs
  | .or cs => condsAnySub P cs
  | .not c => c.anySub P
  | .hasSubset r => r.anySub P
  | .expr r => r.anySub P
def condsAnySub (P : Expr → Bool) : List Cond → Bool
  | [] => false
  | c :: cs => c.anySub P || condsAnySub P cs
end

/-- `P` of the form itself implies `anySub P`. -/
theorem Expr.anySub_self {P : Expr → Bool} {f : Expr} (h : P f = true) : f.anySub P = true := by
  unfold Expr.anySub; split <;> simp_all

/-! ## Leaves -/

/-- `m` is a sub-form of `f`, by `Expr.beq` (as the evaluator finds the candidate,
`tg.any f.beq`). -/
def Expr.mentions (f m : Expr) : Bool := f.anySub (·.beq m)

/-- A form that binds a candidate or a database of its own. -/
def Expr.isSolForm : Expr → Bool
  | .omegaSol _ _ | .sigmaSol _ _ | .enumSol _ _ _
  | .omegaMsol _ _ | .sigmaMsol _ _ | .enumMsol _ _ _ => true
  | _ => false

def Expr.hasSolForm (f : Expr) : Bool := f.anySub Expr.isSolForm

/-- A leaf of a condition over the candidate `m`: it does not mention `m` and holds no
solution-set form. φ evaluates it concretely (Racket's `candidate-leaf`). -/
def Expr.isLeaf (f m : Expr) : Bool := !f.mentions m && !f.hasSolForm

def IsLeaf (m f : Expr) : Prop := f.mentions m = false ∧ f.hasSolForm = false

theorem Expr.isLeaf_iff (m f : Expr) : f.isLeaf m = true ↔ IsLeaf m f := by
  simp [Expr.isLeaf, IsLeaf]

instance (m f : Expr) : Decidable (IsLeaf m f) := decidable_of_iff _ (Expr.isLeaf_iff m f)

theorem Expr.mentions_self (m : Expr) : m.mentions m = true :=
  Expr.anySub_self (Expr.beq_refl m)

/-- The candidate is never a leaf. -/
theorem not_isLeaf_self (m : Expr) : ¬ IsLeaf m m := by
  intro h; have := h.1; rw [Expr.mentions_self] at this; cases this

/-! ## Terms and γ's expressions -/

/-- The operators `applyOp` evaluates (`Rasso.Term`). -/
def phiOps : List String :=
  ["+", "-", "*", "%", "abs", "sum", "min", "max", "all_different",
   "=", "<", "<=", ">", ">=", "and", "or", "not"]

/-- The aggregates `aggregate` evaluates, in the `_` spelling (`aggName`). -/
def phiAggs : List String :=
  ["count", "sum", "bool_and", "bool_or", "min", "max", "all_different"]

mutual
/-- A term φ can read: known operators, no float constant. -/
def Term.phiOk : Term → Bool
  | .attr _ => true
  | .val v => !v.isFloat
  | .call op xs => phiOps.contains op && termsPhiOk xs
def termsPhiOk : List Term → Bool
  | [] => true
  | t :: ts => t.phiOk && termsPhiOk ts
end

inductive PhiTerm : Term → Prop
  | attr (a : String) : PhiTerm (.attr a)
  | val (v : Value) : v.isFloat = false → PhiTerm (.val v)
  | call (op : String) (xs : List Term) : op ∈ phiOps → (∀ x ∈ xs, PhiTerm x) →
      PhiTerm (.call op xs)

mutual
theorem Term.phiOk_iff : (t : Term) → (t.phiOk = true ↔ PhiTerm t)
  | .attr a => by simp only [Term.phiOk, true_iff]; exact .attr a
  | .val v => by
    simp only [Term.phiOk, Bool.not_eq_true']
    exact ⟨.val v, fun h => by cases h; assumption⟩
  | .call op xs => by
    simp only [Term.phiOk, Bool.and_eq_true, List.contains_iff_mem, termsPhiOk_iff xs]
    exact ⟨fun ⟨h1, h2⟩ => .call op xs h1 h2, fun h => by cases h; exact ⟨by assumption, by assumption⟩⟩
theorem termsPhiOk_iff : (ts : List Term) → (termsPhiOk ts = true ↔ ∀ x ∈ ts, PhiTerm x)
  | [] => by simp [termsPhiOk]
  | t :: ts => by
    simp only [termsPhiOk, Bool.and_eq_true, Term.phiOk_iff t, termsPhiOk_iff ts,
      List.mem_cons, forall_eq_or_imp]
end

instance : DecidablePred PhiTerm := fun t => decidable_of_iff _ (Term.phiOk_iff t)

mutual
/-- γ's expression over the candidate `m`: scalar parts as terms, known aggregates of
terms, and `has_subset` of a leaf. -/
def Agg.phiOk (m : Expr) : Agg → Bool
  | .attr _ => true
  | .val v => !v.isFloat
  | .call op xs => phiOps.contains op && aggsPhiOk m xs
  | .agg op t => phiAggs.contains (aggName op) && t.phiOk
  | .hasSubset r => r.isLeaf m
def aggsPhiOk (m : Expr) : List Agg → Bool
  | [] => true
  | x :: xs => x.phiOk m && aggsPhiOk m xs
end

inductive PhiAgg (m : Expr) : Agg → Prop
  | attr (a : String) : PhiAgg m (.attr a)
  | val (v : Value) : v.isFloat = false → PhiAgg m (.val v)
  | call (op : String) (xs : List Agg) : op ∈ phiOps → (∀ x ∈ xs, PhiAgg m x) →
      PhiAgg m (.call op xs)
  | agg (op : String) (t : Term) : aggName op ∈ phiAggs → PhiTerm t → PhiAgg m (.agg op t)
  | hasSubset (r : Expr) : IsLeaf m r → PhiAgg m (.hasSubset r)

mutual
theorem Agg.phiOk_iff (m : Expr) : (x : Agg) → (x.phiOk m = true ↔ PhiAgg m x)
  | .attr a => by simp only [Agg.phiOk, true_iff]; exact .attr a
  | .val v => by
    simp only [Agg.phiOk, Bool.not_eq_true']
    exact ⟨.val v, fun h => by cases h; assumption⟩
  | .call op xs => by
    simp only [Agg.phiOk, Bool.and_eq_true, List.contains_iff_mem, aggsPhiOk_iff m xs]
    exact ⟨fun ⟨h1, h2⟩ => .call op xs h1 h2, fun h => by cases h; exact ⟨by assumption, by assumption⟩⟩
  | .agg op t => by
    simp only [Agg.phiOk, Bool.and_eq_true, List.contains_iff_mem, Term.phiOk_iff t]
    exact ⟨fun ⟨h1, h2⟩ => .agg op t h1 h2, fun h => by cases h; exact ⟨by assumption, by assumption⟩⟩
  | .hasSubset r => by
    simp only [Agg.phiOk, Expr.isLeaf_iff]
    exact ⟨.hasSubset r, fun h => by cases h; assumption⟩
theorem aggsPhiOk_iff (m : Expr) : (xs : List Agg) → (aggsPhiOk m xs = true ↔ ∀ x ∈ xs, PhiAgg m x)
  | [] => by simp [aggsPhiOk]
  | x :: xs => by
    simp only [aggsPhiOk, Bool.and_eq_true, Agg.phiOk_iff m x, aggsPhiOk_iff m xs,
      List.mem_cons, forall_eq_or_imp]
end

instance (m : Expr) : DecidablePred (PhiAgg m) := fun x => decidable_of_iff _ (Agg.phiOk_iff m x)

/-! ## Relational expressions over the candidate (Racket's `rexp?`) -/

/-- A relational expression over the candidate `m`: `m` itself, a leaf, γ, `extend`, or a
natural join of one or more. -/
def Expr.phiExpr (f m : Expr) : Bool :=
  f.beq m || f.isLeaf m || match f with
    | .gamma _ x _ e => x.phiOk m && e.phiExpr m
    | .extend _ t e => t.phiOk && e.phiExpr m
    | .nary .join es => !es.isEmpty && es.attach.all fun ⟨e, _⟩ => e.phiExpr m
    | _ => false
termination_by sizeOf f
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)

inductive PhiExpr (m : Expr) : Expr → Prop
  | cand (f : Expr) : f.beq m = true → PhiExpr m f
  | leaf (f : Expr) : IsLeaf m f → PhiExpr m f
  | gamma (by_ : List String) (x : Agg) (res : Option String) (e : Expr) :
      PhiAgg m x → PhiExpr m e → PhiExpr m (.gamma by_ x res e)
  | extend (res : String) (t : Term) (e : Expr) : PhiTerm t → PhiExpr m e → PhiExpr m (.extend res t e)
  | join (es : List Expr) : es ≠ [] → (∀ e ∈ es, PhiExpr m e) → PhiExpr m (.nary .join es)

theorem Expr.phiExpr_sound (m f : Expr) (h : f.phiExpr m = true) : PhiExpr m f := by
  rw [Expr.phiExpr.eq_def] at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact .cand f h
  · exact .leaf f ((Expr.isLeaf_iff m f).1 h)
  · split at h
    · simp only [Bool.and_eq_true] at h
      exact .gamma _ _ _ _ ((Agg.phiOk_iff m _).1 h.1) (Expr.phiExpr_sound m _ h.2)
    · simp only [Bool.and_eq_true] at h
      exact .extend _ _ _ ((Term.phiOk_iff _).1 h.1) (Expr.phiExpr_sound m _ h.2)
    · rename_i es
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at h
      refine .join es h.1 fun e he => Expr.phiExpr_sound m e ?_
      exact h.2 ⟨e, he⟩ (List.mem_attach _ _)
    · cases h
termination_by sizeOf f
decreasing_by
  all_goals simp_wf
  all_goals (try subst_vars)
  all_goals (try have := List.sizeOf_lt_of_mem ‹_ ∈ _›)
  all_goals (try simp)
  all_goals omega

theorem Expr.phiExpr_complete {m f : Expr} (h : PhiExpr m f) : f.phiExpr m = true := by
  induction h with
  | cand f h => rw [Expr.phiExpr.eq_def]; simp [h]
  | leaf f h => rw [Expr.phiExpr.eq_def]; simp [(Expr.isLeaf_iff m f).2 h]
  | gamma by_ x res e hx _ ih =>
    rw [Expr.phiExpr.eq_def]; simp [(Agg.phiOk_iff m x).2 hx, ih]
  | extend res t e ht _ ih =>
    rw [Expr.phiExpr.eq_def]; simp [(Term.phiOk_iff t).2 ht, ih]
  | join es hne _ ih =>
    rw [Expr.phiExpr.eq_def]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true]
    exact .inr ⟨hne, fun ⟨e, he⟩ _ => ih e he⟩

theorem Expr.phiExpr_iff (m f : Expr) : f.phiExpr m = true ↔ PhiExpr m f :=
  ⟨Expr.phiExpr_sound m f, Expr.phiExpr_complete⟩

instance (m : Expr) : DecidablePred (PhiExpr m) := fun f => decidable_of_iff _ (Expr.phiExpr_iff m f)

/-! ## Conditions (Racket's `condition?`, without the internal `holds`, `has`, `each-group`) -/

mutual
def Cond.phiCond (m : Expr) : Cond → Bool
  | .and cs => condsPhiCond m cs
  | .or cs => condsPhiCond m cs
  | .not c => c.phiCond m
  | .hasSubset r => r.isLeaf m
  | .expr e => e.phiExpr m
def condsPhiCond (m : Expr) : List Cond → Bool
  | [] => true
  | c :: cs => c.phiCond m && condsPhiCond m cs
end

inductive PhiCond (m : Expr) : Cond → Prop
  | and (cs : List Cond) : (∀ c ∈ cs, PhiCond m c) → PhiCond m (.and cs)
  | or (cs : List Cond) : (∀ c ∈ cs, PhiCond m c) → PhiCond m (.or cs)
  | not (c : Cond) : PhiCond m c → PhiCond m (.not c)
  | hasSubset (r : Expr) : IsLeaf m r → PhiCond m (.hasSubset r)
  | rel (e : Expr) : PhiExpr m e → PhiCond m (.expr e)

mutual
theorem Cond.phiCond_iff (m : Expr) : (c : Cond) → (c.phiCond m = true ↔ PhiCond m c)
  | .and cs => by
    simp only [Cond.phiCond, condsPhiCond_iff m cs]
    exact ⟨.and cs, fun h => by cases h; assumption⟩
  | .or cs => by
    simp only [Cond.phiCond, condsPhiCond_iff m cs]
    exact ⟨.or cs, fun h => by cases h; assumption⟩
  | .not c => by
    simp only [Cond.phiCond, Cond.phiCond_iff m c]
    exact ⟨.not c, fun h => by cases h; assumption⟩
  | .hasSubset r => by
    simp only [Cond.phiCond, Expr.isLeaf_iff]
    exact ⟨.hasSubset r, fun h => by cases h; assumption⟩
  | .expr e => by
    simp only [Cond.phiCond, Expr.phiExpr_iff]
    exact ⟨.rel e, fun h => by cases h; assumption⟩
theorem condsPhiCond_iff (m : Expr) : (cs : List Cond) → (condsPhiCond m cs = true ↔ ∀ c ∈ cs, PhiCond m c)
  | [] => by simp [condsPhiCond]
  | c :: cs => by
    simp only [condsPhiCond, Bool.and_eq_true, Cond.phiCond_iff m c, condsPhiCond_iff m cs,
      List.mem_cons, forall_eq_or_imp]
end

instance (m : Expr) : DecidablePred (PhiCond m) := fun c => decidable_of_iff _ (Cond.phiCond_iff m c)

/-! ## Leaves are closed under the structure φ reads

A γ, `extend` or join that is a leaf is read as structure (as Racket's `rexp-value`); its
operands are leaves too. -/

theorem IsLeaf.gamma {m : Expr} {b : List String} {x : Agg} {r : Option String} {e : Expr}
    (h : IsLeaf m (.gamma b x r e)) : IsLeaf m e := by
  simp only [IsLeaf, Expr.mentions, Expr.hasSolForm, Expr.anySub, Bool.or_eq_false_iff] at h ⊢
  exact ⟨h.1.2, h.2.2⟩

theorem IsLeaf.extend {m : Expr} {a : String} {t : Term} {e : Expr}
    (h : IsLeaf m (.extend a t e)) : IsLeaf m e := by
  simp only [IsLeaf, Expr.mentions, Expr.hasSolForm, Expr.anySub, Bool.or_eq_false_iff] at h ⊢
  exact ⟨h.1.2, h.2.2⟩

theorem exprsAnySub_eq_false {P : Expr → Bool} :
    ∀ {es : List Expr}, exprsAnySub P es = false → ∀ e ∈ es, e.anySub P = false
  | [], _, _, he => by cases he
  | r :: rs, h, e, he => by
    simp only [exprsAnySub, Bool.or_eq_false_iff] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact exprsAnySub_eq_false h.2 e he

theorem IsLeaf.join {m : Expr} {o : NOp} {es : List Expr}
    (h : IsLeaf m (.nary o es)) : ∀ e ∈ es, IsLeaf m e := by
  simp only [IsLeaf, Expr.mentions, Expr.hasSolForm, Expr.anySub, Bool.or_eq_false_iff] at h
  exact fun e he => ⟨exprsAnySub_eq_false h.1.2 e he, exprsAnySub_eq_false h.2.2 e he⟩

/-! ## Solution sets, through the program -/

namespace Phi

/-- One `σ_sol` level: the statement that wrote it, its operand as written (the marker the
evaluator finds the candidate by), and its condition. -/
structure Level where
  stmt : Nat
  marker : Expr
  cond : Cond

/-- A solution set as φ reads it: `ω_sol[data, decision]`, written at statement `stmt`,
then the `σ_sol` levels from the inside out. -/
structure Chain where
  stmt : Nat
  data : Expr
  decision : Expr
  levels : List Level

/-- The chain of the form `f`, written at statement `i`. `known` holds every earlier
statement, latest first, with `none` for one that has no chain, so a name finds its latest
binding, as the evaluator's environment does (`runProgram`). -/
def chainOf (known : List (String × Option Chain)) (i : Nat) : Expr → Option Chain
  | .omegaSol d dec => some ⟨i, d, dec, []⟩
  | .sigmaSol c e => match chainOf known i e with
    | some ch => if c.phiCond e then some { ch with levels := ch.levels ++ [⟨i, e, c⟩] } else none
    | none => none
  | .name n => (known.lookup n).bind id
  | _ => none

/-- `f`, written at statement `i`, unfolds through the names in `known` into
`σ_sol[cₙ](… σ_sol[c₁](ω_sol[D, Dec]))`, each condition in the fragment over its own
operand. -/
inductive Unfolds (known : List (String × Option Chain)) (i : Nat) : Expr → Chain → Prop
  | omega (d dec : Expr) : Unfolds known i (.omegaSol d dec) ⟨i, d, dec, []⟩
  | sigma (c : Cond) (e : Expr) (ch : Chain) : Unfolds known i e ch → PhiCond e c →
      Unfolds known i (.sigmaSol c e) { ch with levels := ch.levels ++ [⟨i, e, c⟩] }
  | name (n : String) (ch : Chain) : known.lookup n = some (some ch) → Unfolds known i (.name n) ch

theorem chainOf_eq_some_iff (known : List (String × Option Chain)) (i : Nat) (f : Expr) (ch : Chain) :
    chainOf known i f = some ch ↔ Unfolds known i f ch := by
  cases f
  case omegaSol d dec =>
    simp only [chainOf, Option.some.injEq]
    exact ⟨fun h => h ▸ .omega d dec, fun h => by cases h; rfl⟩
  case sigmaSol c e =>
    have ih := chainOf_eq_some_iff known i e
    simp only [chainOf]
    constructor
    · intro h
      split at h
      · rename_i ch' he
        split at h
        · cases h; exact .sigma c e ch' ((ih ch').1 he) ((Cond.phiCond_iff e c).1 ‹_›)
        · cases h
      · cases h
    · intro h
      cases h with
      | sigma _ _ ch' hu hc =>
        rw [(ih ch').2 hu]
        simp [(Cond.phiCond_iff e c).2 hc]
  case name n =>
    simp only [chainOf]
    constructor
    · intro h
      cases hl : known.lookup n with
      | none => rw [hl] at h; cases h
      | some o => rw [hl] at h; cases o with
        | none => cases h
        | some ch' =>
          simp only [Option.bind_some, id, Option.some.injEq] at h
          subst h; exact .name n _ hl
    · intro h; cases h with
      | name _ _ hl => rw [hl]; rfl
  all_goals
    simp only [chainOf, reduceCtorEq, false_iff]
    intro h; cases h
termination_by sizeOf f

/-- The chain of every statement of a program, in order. -/
def programChains (p : Program) : List (String × Option Chain) :=
  (p.zipIdx.foldl (fun known ((n, f), i) => (n, chainOf known i f) :: known) []).reverse

/-- The chain of statement `k` (from 0), if it is in the fragment. -/
def statementChain (p : Program) (k : Nat) : Option Chain :=
  ((programChains p)[k]?).bind (·.2)

/-- Statement `k` of `p` is a solution set φ takes. Decidable: it is computed. -/
def InPhiFragment (p : Program) (k : Nat) : Prop := (statementChain p k).isSome = true

instance (p : Program) (k : Nat) : Decidable (InPhiFragment p k) := by
  unfold InPhiFragment; infer_instance

/-! ## The environment each statement sees -/

/-- The environment statement `i` (from 0) is evaluated in, latest binding first, as
`runProgram` gives it. Leaves, `D` and `Dec` of a level written at statement `i` are
evaluated here. -/
def envAt (p : Program) (i : Nat) : Except String Env := (runProgram (p.take i)).map List.reverse

theorem runProgram_append (p q : Program) :
    runProgram (p ++ q) = (runProgram p).bind fun env =>
      q.foldlM (fun env (n, e) => do return env ++ [(n, ← e.eval env.reverse [])]) env := by
  simp only [runProgram, List.foldlM_append]
  rfl

end Phi

end Rasso
