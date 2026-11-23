import Rasso.Laws.Unrel
import Rasso.Bridge.Sol

/-!
# Rasso: the laws of solution sets and multi solution sets

The laws of solution sets, multi solution sets and the boundary operators, for the
operators current Rasso has. The rows are in the laws appendix of the Rasso blueprint.

How a law is stated:

* **Selections on abstract tests**. σ_sol and σ_msol filter a list of
  candidates (relations, or databases) by a test that can refuse. The laws are proved once,
  for a list of any kind of item, and reach the evaluator through `solTest` and `msolTest`
  (`Rasso/Bridge/Sol.lean`). A written condition names its candidate by repeating its
  operand's form, so a law that swaps two written selections is not literally a law about
  forms.
* **When both sides succeed**, with a separate line on definedness: filtering refuses when
  the test refuses on any item, even one that a later test would drop.
* **Counts** for the exponent laws, from `length_omegaSolCandidates` and `length_omegaMsolDbs`.

Conventions:

* The cascade is stated with `andThen` (the second test runs only when the first passed),
  which is how a written `and` of two conditions evaluates (`Cond.eval`, `List.allM`).
-/

namespace Rasso
namespace SolLaws

/-! ## Selection on any list of candidates -/

section Generic

variable {α : Type}

/-- Run `q`; when it passes, run `p`. -/
def andThen (q p : α → Except String Bool) (x : α) : Except String Bool := do
  if ← q x then p x else pure false

theorem andThen_true {q p : α → Except String Bool} {x : α} :
    andThen q p x = .ok true ↔ q x = .ok true ∧ p x = .ok true := by
  unfold andThen
  cases hq : q x with
  | error e => simp [bind, Except.bind]
  | ok b => cases b <;> simp [bind, Except.bind, pure, Except.pure]

theorem passed_andThen {q p : α → Except String Bool} {x : α} :
    passed (andThen q p x) = (passed (q x) && passed (p x)) := by
  cases h : passed (andThen q p x) with
  | true =>
    obtain ⟨h1, h2⟩ := andThen_true.mp (passed_iff.mp h)
    rw [h1, h2]; rfl
  | false =>
    symm
    cases hq : passed (q x) with
    | false => rfl
    | true =>
      cases hp : passed (p x) with
      | false => rfl
      | true =>
        have := andThen_true.mpr ⟨passed_iff.mp hq, passed_iff.mp hp⟩
        rw [this] at h; cases h

theorem andThen_succeeds {q p : α → Except String Bool} {x : α} :
    Succeeds (andThen q p x) ↔ Succeeds (q x) ∧ (q x = .ok true → Succeeds (p x)) := by
  unfold andThen
  cases hq : q x with
  | error e => simp [bind, Except.bind, Succeeds]
  | ok b =>
    cases b <;> simp [bind, Except.bind, pure, Except.pure, Succeeds]

/-- **What a selection keeps**: the items that pass, in the operand's order. -/
theorem select_eq {p : α → Except String Bool} {l r : List α} (h : l.filterM p = .ok r) :
    r = l.filter fun x => passed (p x) :=
  (filterM_ok_iff.mp h).2

/-- **Definedness**: a selection succeeds exactly when the test is not refused on any
item. -/
theorem select_ok {p : α → Except String Bool} {l : List α} :
    (∃ r, l.filterM p = .ok r) ↔ ∀ x ∈ l, Succeeds (p x) :=
  ⟨fun ⟨_, h⟩ => (filterM_ok_iff.mp h).1, fun h => ⟨_, filterM_ok_iff.mpr ⟨h, rfl⟩⟩⟩

/-- **Commutative**, as lists: when both orders succeed they give the same list. -/
theorem select_comm {p q : α → Except String Bool} {l lq lp s s' : List α}
    (h₁ : l.filterM q = .ok lq) (h₂ : lq.filterM p = .ok s)
    (h₃ : l.filterM p = .ok lp) (h₄ : lp.filterM q = .ok s') : s = s' := by
  rw [select_eq h₂, select_eq h₁, select_eq h₄, select_eq h₃, List.filter_filter,
    List.filter_filter]
  congr 1; funext x; exact Bool.and_comm _ _

/-- **Idempotent**: selecting again keeps everything, and is not refused. -/
theorem select_idem {p : α → Except String Bool} {l r : List α} (h : l.filterM p = .ok r) :
    r.filterM p = .ok r := by
  obtain ⟨hok, rfl⟩ := filterM_ok_iff.mp h
  refine filterM_ok_iff.mpr ⟨fun x hx => hok x (List.mem_filter.mp hx).1, ?_⟩
  rw [List.filter_filter]
  congr 1; funext x; simp

/-- **Cascade**: selecting by `q` and then by `p` succeeds, with result `s`, exactly when
selecting by `andThen q p` does. Both sides refuse together. -/
theorem select_cascade {p q : α → Except String Bool} {l s : List α} :
    (∃ lq, l.filterM q = .ok lq ∧ lq.filterM p = .ok s) ↔ l.filterM (andThen q p) = .ok s := by
  constructor
  · rintro ⟨lq, h₁, h₂⟩
    obtain ⟨hq, rfl⟩ := filterM_ok_iff.mp h₁
    obtain ⟨hp, rfl⟩ := filterM_ok_iff.mp h₂
    refine filterM_ok_iff.mpr ⟨fun x hx => andThen_succeeds.mpr ⟨hq x hx, fun hx' => ?_⟩, ?_⟩
    · exact hp x (List.mem_filter.mpr ⟨hx, by rw [hx']; rfl⟩)
    · rw [List.filter_filter]
      congr 1; funext x; rw [passed_andThen, Bool.and_comm]
  · intro h
    obtain ⟨hqp, rfl⟩ := filterM_ok_iff.mp h
    have hq : ∀ x ∈ l, Succeeds (q x) := fun x hx => (andThen_succeeds.mp (hqp x hx)).1
    refine ⟨_, filterM_ok_iff.mpr ⟨hq, rfl⟩, filterM_ok_iff.mpr ⟨fun x hx => ?_, ?_⟩⟩
    · obtain ⟨hx, hx'⟩ := List.mem_filter.mp hx
      exact (andThen_succeeds.mp (hqp x hx)).2 (passed_iff.mp hx')
    · rw [List.filter_filter]
      congr 1; funext x; rw [passed_andThen, Bool.and_comm]

/-- **Decreasing**: a selection keeps a sublist of its operand. -/
theorem select_sublist {p : α → Except String Bool} {l r : List α}
    (h : l.filterM p = .ok r) : r.Sublist l := by
  rw [select_eq h]; exact List.filter_sublist

/-- A selection adds no repeats. -/
theorem select_nodup {p : α → Except String Bool} {l r : List α}
    (h : l.filterM p = .ok r) (hl : l.Nodup) : r.Nodup :=
  (select_sublist h).nodup hl

/-- **Identity**: the test that always passes keeps everything. -/
theorem select_true (l : List α) : l.filterM (fun _ => (.ok true : Except String Bool)) = .ok l :=
  filterM_ok_iff.mpr ⟨fun _ _ => trivial, (List.filter_eq_self.mpr fun _ _ => rfl).symm⟩

/-- **Zero**: the test that always fails keeps nothing. -/
theorem select_false (l : List α) :
    l.filterM (fun _ => (.ok false : Except String Bool)) = .ok [] :=
  filterM_ok_iff.mpr ⟨fun _ _ => trivial, by simp [passed]⟩

/-- **Commutative up to definedness, one way**: if selecting by `q` then `p` succeeds and
`p` is not refused on any item of the operand, the other order succeeds too. -/
theorem select_comm_ok {p q : α → Except String Bool} {l lq s : List α}
    (h₁ : l.filterM q = .ok lq) (_h₂ : lq.filterM p = .ok s)
    (hp : ∀ x ∈ l, Succeeds (p x)) :
    ∃ lp s', l.filterM p = .ok lp ∧ lp.filterM q = .ok s' := by
  obtain ⟨lp, h₃⟩ := select_ok.mpr hp
  have hq := (filterM_ok_iff.mp h₁).1
  obtain ⟨s', h₄⟩ := select_ok.mpr fun x hx => hq x ((select_sublist h₃).subset hx)
  exact ⟨lp, s', h₃, h₄⟩

end Generic

/-! ## A written `and` is `andThen` -/

/-- A written `and` of two conditions runs the second only when the first passed
(`List.allM` stops at the first `false`), so it is `andThen` of the two. -/
theorem cond_and_two (env : Env) (tg : List Expr) (c d : Cond) :
    Cond.eval env tg (.and [c, d]) =
      andThen (fun _ : Unit => c.eval env tg) (fun _ => d.eval env tg) () := by
  rw [Cond.eval]
  simp only [List.attach, List.attachWith, List.pmap, List.allM, andThen]
  cases hc : c.eval env tg with
  | error e => rfl
  | ok b =>
    cases b with
    | false => rfl
    | true =>
      simp only [bind, Except.bind, ite_true]
      cases d.eval env tg with
      | error e => rfl
      | ok b' => cases b' <;> rfl

/-- So σ_sol by a written `and [c, d]` tests each candidate with `andThen` of the two
tests. -/
theorem solTest_and (env : Env) (tg : List Expr) (c d : Cond) (e : Expr) :
    solTest env tg (.and [c, d]) e = andThen (solTest env tg c e) (solTest env tg d e) := by
  funext r; unfold solTest; rw [cond_and_two]; rfl

theorem msolTest_and (env : Env) (tg : List Expr) (c d : Cond) :
    msolTest env tg (.and [c, d]) = andThen (msolTest env tg c) (msolTest env tg d) := by
  funext db; unfold msolTest; rw [cond_and_two]; rfl

/-! ## σ_sol -/

/-- **σ_sol keeps the data and the heading** and keeps a sublist of the candidates. -/
theorem sigmaSol_keeps {env : Env} {tg : List Expr} {c : Cond} {e : Expr} {v : Val}
    (hnt : tg.any (Expr.sigmaSol c e).beq = false)
    (h : Expr.eval env tg (.sigmaSol c e) = .ok v) :
    ∃ s s', Expr.eval env tg e = .ok (.sol s) ∧ v = .sol s' ∧ s'.data = s.data ∧
      s'.heading = s.heading ∧ s'.candidates.Sublist s.candidates := by
  obtain ⟨s, cands, he, hf, rfl⟩ := eval_sigmaSol hnt h
  exact ⟨s, _, he, rfl, rfl, rfl, select_sublist hf⟩

/-! ## σ_msol: the laws hold of written forms

σ_msol's condition names the members, not its operand's form (`msolTest` evaluates it with
the evaluator's own targets), so swapping two written σ_msol leaves each condition meaning
what it meant. -/

/-- **σ_msol keeps the members** and keeps a sublist of the databases. -/
theorem sigmaMsol_keeps {env : Env} {tg : List Expr} {c : Cond} {e : Expr} {v : Val}
    (hnt : tg.any (Expr.sigmaMsol c e).beq = false)
    (h : Expr.eval env tg (.sigmaMsol c e) = .ok v) :
    ∃ m m', Expr.eval env tg e = .ok (.msol m) ∧ v = .msol m' ∧ m'.members = m.members ∧
      m'.candidates.Sublist m.candidates := by
  obtain ⟨m, dbs, he, hf, rfl⟩ := eval_sigmaMsol hnt h
  exact ⟨m, _, he, rfl, rfl, select_sublist hf⟩

/-- **σ_msol commutes, as written forms**: when both orders evaluate, they give the same
multi solution set. -/
theorem sigmaMsol_comm {env : Env} {tg : List Expr} {c d : Cond} {e : Expr} {v w : Val}
    (hnt₁ : tg.any (Expr.sigmaMsol c (.sigmaMsol d e)).beq = false)
    (hnt₂ : tg.any (Expr.sigmaMsol d e).beq = false)
    (hnt₃ : tg.any (Expr.sigmaMsol d (.sigmaMsol c e)).beq = false)
    (hnt₄ : tg.any (Expr.sigmaMsol c e).beq = false)
    (h₁ : Expr.eval env tg (.sigmaMsol c (.sigmaMsol d e)) = .ok v)
    (h₂ : Expr.eval env tg (.sigmaMsol d (.sigmaMsol c e)) = .ok w) : v = w := by
  obtain ⟨m₁, dbs₁, he₁, hf₁, rfl⟩ := eval_sigmaMsol hnt₁ h₁
  obtain ⟨m₂, dbs₂, he₂, hf₂, rfl⟩ := eval_sigmaMsol hnt₃ h₂
  obtain ⟨m, dd, he, hd, hv⟩ := eval_sigmaMsol hnt₂ he₁
  obtain ⟨m', dc, he', hc, hv'⟩ := eval_sigmaMsol hnt₄ he₂
  injection hv with hv; subst hv
  injection hv' with hv'; subst hv'
  rw [he] at he'; injection he' with he'; injection he' with he'; subst he'
  rw [select_comm hd hf₁ hc hf₂]

/-- **σ_msol is idempotent, as written forms**, and selecting twice is refused exactly when
selecting once is. -/
theorem sigmaMsol_idem {env : Env} {tg : List Expr} {c : Cond} {e : Expr} {v : Val}
    (hnt₁ : tg.any (Expr.sigmaMsol c (.sigmaMsol c e)).beq = false)
    (hnt₂ : tg.any (Expr.sigmaMsol c e).beq = false)
    (h : Expr.eval env tg (.sigmaMsol c e) = .ok v) :
    Expr.eval env tg (.sigmaMsol c (.sigmaMsol c e)) = .ok v := by
  obtain ⟨m, dbs, he, hf, rfl⟩ := eval_sigmaMsol hnt₂ h
  have h₁ := h
  rw [Expr.eval, hnt₁]
  simp only [Bool.false_eq_true, ite_false]
  rw [h₁]
  simp only [bind, Except.bind, Val.asMsol]
  unfold msolTest at hf
  rw [select_idem hf]; rfl

/-- **σ_msol cascades, as written forms**: selecting by `c` and then by `d` gives what
selecting by `and [c, d]` gives, and both are refused together. -/
theorem sigmaMsol_cascade {env : Env} {tg : List Expr} {c d : Cond} {e : Expr} {v : Val}
    (hnt₁ : tg.any (Expr.sigmaMsol d (.sigmaMsol c e)).beq = false)
    (hnt₂ : tg.any (Expr.sigmaMsol c e).beq = false)
    (hnt₃ : tg.any (Expr.sigmaMsol (.and [c, d]) e).beq = false) :
    Expr.eval env tg (.sigmaMsol d (.sigmaMsol c e)) = .ok v ↔
      Expr.eval env tg (.sigmaMsol (.and [c, d]) e) = .ok v := by
  constructor
  · intro h
    obtain ⟨m₁, dbs, he₁, hf₁, rfl⟩ := eval_sigmaMsol hnt₁ h
    obtain ⟨m, dc, he, hc, hv⟩ := eval_sigmaMsol hnt₂ he₁
    injection hv with hv; subst hv
    have hf := select_cascade.mp ⟨dc, hc, hf₁⟩
    rw [← msolTest_and] at hf
    rw [Expr.eval, hnt₃]
    simp only [Bool.false_eq_true, ite_false]
    rw [he]
    simp only [bind, Except.bind, Val.asMsol]
    unfold msolTest at hf
    rw [hf]; rfl
  · intro h
    obtain ⟨m, dbs, he, hf, rfl⟩ := eval_sigmaMsol hnt₃ h
    rw [msolTest_and] at hf
    obtain ⟨lq, h₁, h₂⟩ := select_cascade.mpr hf
    have hin : Expr.eval env tg (.sigmaMsol c e) = .ok (.msol { m with candidates := lq }) := by
      rw [Expr.eval, hnt₂]
      simp only [Bool.false_eq_true, ite_false]
      rw [he]
      simp only [bind, Except.bind, Val.asMsol]
      unfold msolTest at h₁
      rw [h₁]; rfl
    rw [Expr.eval, hnt₁]
    simp only [Bool.false_eq_true, ite_false]
    rw [hin]
    simp only [bind, Except.bind, Val.asMsol]
    unfold msolTest at h₂
    rw [h₂]; rfl

/-- **ω_msol with a condition is σ_msol over ω_msol without one**, as written forms: both
give the same result, and both are refused together. -/
theorem omegaMsol_some {env : Env} {tg : List Expr} {ms : List (String × Expr)} {c : Cond}
    {v : Val}
    (hnt₁ : tg.any (Expr.omegaMsol ms (some c)).beq = false)
    (hnt₂ : tg.any (Expr.sigmaMsol c (.omegaMsol ms none)).beq = false)
    (hnt₃ : tg.any (Expr.omegaMsol ms none).beq = false) :
    Expr.eval env tg (.omegaMsol ms (some c)) = .ok v ↔
      Expr.eval env tg (.sigmaMsol c (.omegaMsol ms none)) = .ok v := by
  have hn : Expr.eval env tg (.omegaMsol ms none) =
      (do
        let sols ← evalMembers env tg ms
        if sols.isEmpty then throw "ω_msol: needs at least one member"
        if (sols.map (·.1)).eraseDups.length != sols.length then throw "ω_msol: two members have one name"
        return .msol ⟨sols.map fun (n, s) => (n, s.heading), omegaMsolDbs sols⟩) := by
    rw [Expr.eval, hnt₃]
    simp only [Bool.false_eq_true, ite_false, evalMsolCond]
    rfl
  have hs : Expr.eval env tg (.omegaMsol ms (some c)) =
      (do
        let sols ← evalMembers env tg ms
        if sols.isEmpty then throw "ω_msol: needs at least one member"
        if (sols.map (·.1)).eraseDups.length != sols.length then throw "ω_msol: two members have one name"
        let dbs ← (omegaMsolDbs sols).filterM (msolTest env tg c)
        return .msol ⟨sols.map fun (n, s) => (n, s.heading), dbs⟩) := by
    rw [Expr.eval, hnt₁]
    simp only [Bool.false_eq_true, ite_false, evalMsolCond]
    rfl
  have hσ : Expr.eval env tg (.sigmaMsol c (.omegaMsol ms none)) =
      (do
        let m ← (← Expr.eval env tg (.omegaMsol ms none)).asMsol
        return .msol { m with candidates := ← m.candidates.filterM (msolTest env tg c) }) := by
    conv => lhs; rw [Expr.eval, hnt₂]
    simp only [Bool.false_eq_true, ite_false]
    rfl
  rw [hs, hσ, hn]
  cases evalMembers env tg ms with
  | error err => simp [bind, Except.bind]
  | ok sols =>
    by_cases he : sols.isEmpty = true
    · simp [bind, Except.bind, he, throw, throwThe, MonadExceptOf.throw]
    · by_cases hd2 : ((sols.map (·.1)).eraseDups.length != sols.length) = true
      · simp [bind, Except.bind, he, hd2, throw, throwThe, MonadExceptOf.throw]
      · simp only [bind, Except.bind, he, hd2, Bool.false_eq_true, ite_false, pure, Except.pure,
          Val.asMsol]

/-! ## ω_sol: the exponent laws as counts -/

/-- **D^∅ = 1**: with no data tuples, the only candidate is the empty relation. -/
theorem omegaSolCandidates_no_rows (h : Heading) (picks : List Tuple) :
    omegaSolCandidates h [] picks = [Finrel.ofTuples h []] := rfl

/-- **0^A = 0**: with a data tuple and no decision tuples there is no candidate. -/
theorem omegaSolCandidates_no_picks (h : Heading) {rows : List Tuple} (hr : rows ≠ []) :
    omegaSolCandidates h rows [] = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [length_omegaSolCandidates]
  cases rows with
  | nil => exact absurd rfl hr
  | cons _ _ => simp

/-- **1^A = 1**: one decision tuple gives one candidate. -/
theorem length_omegaSolCandidates_one (h : Heading) (rows : List Tuple) (p : Tuple) :
    (omegaSolCandidates h rows [p]).length = 1 := by
  rw [length_omegaSolCandidates]; simp

/-- **The sum law, as a count**: X^(A ⊎ B) has |X^A| · |X^B| candidates. -/
theorem length_omegaSolCandidates_append (h hA hB : Heading) (A B picks : List Tuple) :
    (omegaSolCandidates h (A ++ B) picks).length =
      (omegaSolCandidates hA A picks).length * (omegaSolCandidates hB B picks).length := by
  simp only [length_omegaSolCandidates, List.length_append, Nat.pow_add]

/-- **The product law, as a count**: when the decision X × Y has |X| · |Y| tuples,
(X × Y)^A has |X^A| · |Y^A| candidates. -/
theorem length_omegaSolCandidates_product (h hX hY : Heading) (rows XY X Y : List Tuple)
    (hxy : XY.length = X.length * Y.length) :
    (omegaSolCandidates h rows XY).length =
      (omegaSolCandidates hX rows X).length * (omegaSolCandidates hY rows Y).length := by
  simp only [length_omegaSolCandidates, hxy, Nat.mul_pow]

/-- **Currying, as a count**: when A × B has |A| · |B| tuples, X^(A × B) has as many
candidates as there are functions from A to X^B. -/
theorem length_omegaSolCandidates_curry (h hB : Heading) (AB A B picks : List Tuple)
    (hab : AB.length = A.length * B.length) :
    (omegaSolCandidates h AB picks).length = (omegaSolCandidates hB B picks).length ^ A.length := by
  simp only [length_omegaSolCandidates, hab, ← Nat.pow_mul, Nat.mul_comm]

/-! ## ω_sol: the sum law on candidates -/

/-- **The sum law, one way**: a candidate over the data tuples `A ++ B` is, tuple for
tuple, a candidate over `A` together with a candidate over `B`. -/
theorem omegaSolCandidates_append_split {h : Heading} {A B picks : List Tuple}
    (hn : (A ++ B).Nodup) {c : Finrel} (hc : c ∈ omegaSolCandidates h (A ++ B) picks) :
    ∃ ca ∈ omegaSolCandidates h A picks, ∃ cb ∈ omegaSolCandidates h B picks,
      ∀ t, t ∈ c.tuples ↔ t ∈ ca.tuples ∨ t ∈ cb.tuples := by
  obtain ⟨f, hf, rfl⟩ := (mem_omegaSolCandidates hn c).mp hc
  refine ⟨graph h A f, (mem_omegaSolCandidates (List.nodup_append.mp hn).1 _).mpr
      ⟨f, fun t ht => hf t (List.mem_append_left _ ht), rfl⟩,
    graph h B f, (mem_omegaSolCandidates (List.nodup_append.mp hn).2.1 _).mpr
      ⟨f, fun t ht => hf t (List.mem_append_right _ ht), rfl⟩, fun t => ?_⟩
  simp only [mem_graph, List.mem_append]
  constructor
  · rintro ⟨r, hr | hr, e⟩
    · exact .inl ⟨r, hr, e⟩
    · exact .inr ⟨r, hr, e⟩
  · rintro (⟨r, hr, e⟩ | ⟨r, hr, e⟩)
    · exact ⟨r, .inl hr, e⟩
    · exact ⟨r, .inr hr, e⟩

/-- **The sum law, the other way**: a candidate over `A` and one over `B` together make a
candidate over `A ++ B`, when no data tuple is in both. -/
theorem omegaSolCandidates_append_join {h : Heading} {A B picks : List Tuple}
    (hn : (A ++ B).Nodup) {ca cb : Finrel} (ha : ca ∈ omegaSolCandidates h A picks)
    (hb : cb ∈ omegaSolCandidates h B picks) :
    ∃ c ∈ omegaSolCandidates h (A ++ B) picks, ∀ t, t ∈ c.tuples ↔ t ∈ ca.tuples ∨ t ∈ cb.tuples := by
  have hnd := List.nodup_append.mp hn
  obtain ⟨fa, hfa, rfl⟩ := (mem_omegaSolCandidates hnd.1 ca).mp ha
  obtain ⟨fb, hfb, rfl⟩ := (mem_omegaSolCandidates hnd.2.1 cb).mp hb
  let f : Tuple → Tuple := fun t => if t ∈ A then fa t else fb t
  have hfA : ∀ t ∈ A, f t = fa t := fun t ht => by simp [f, ht]
  have hfB : ∀ t ∈ B, f t = fb t := fun t ht =>
    have : t ∉ A := fun hA => hnd.2.2 t hA t ht rfl
    by simp [f, this]
  refine ⟨graph h (A ++ B) f, (mem_omegaSolCandidates hn _).mpr ⟨f, fun t ht => ?_, rfl⟩,
    fun t => ?_⟩
  · rcases List.mem_append.mp ht with ht | ht
    · rw [hfA t ht]; exact hfa t ht
    · rw [hfB t ht]; exact hfb t ht
  simp only [mem_graph, List.mem_append]
  constructor
  · rintro ⟨r, hr | hr, e⟩
    · exact .inl ⟨r, hr, by rw [e, hfA r hr]⟩
    · exact .inr ⟨r, hr, by rw [e, hfB r hr]⟩
  · rintro (⟨r, hr, e⟩ | ⟨r, hr, e⟩)
    · exact ⟨r, .inl hr, by rw [e, hfA r hr]⟩
    · exact ⟨r, .inr hr, by rw [e, hfB r hr]⟩

/-! ## ω_msol -/

/-- **One member**: ω_msol of one member lists that member's candidates, each named. -/
theorem omegaMsolDbs_one (n : String) (s : Sol) :
    omegaMsolDbs [(n, s)] = s.candidates.map fun r => [(n, r)] := by
  simp [omegaMsolDbs, choices, List.flatMap]
  induction s.candidates with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem foldr_mul_perm {l l' : List Nat} (hp : l.Perm l') :
    l.foldr (· * ·) 1 = l'.foldr (· * ·) 1 := by
  induction hp with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap x y l => simp only [List.foldr_cons]; exact Nat.mul_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Reordering the members** does not change how many databases ω_msol forms. -/
theorem length_omegaMsolDbs_perm {sols sols' : List (String × Sol)} (hp : sols.Perm sols') :
    (omegaMsolDbs sols).length = (omegaMsolDbs sols').length := by
  rw [length_omegaMsolDbs, length_omegaMsolDbs]
  exact foldr_mul_perm (hp.map _)

/-! ## The boundary: ℰ, ℰ_sol, ℰ_msol -/

/-- **The prefix law**: with the same keys, ℰ with a smaller count keeps the first items of
ℰ with a larger one. -/
theorem sortTake_prefix {β : Type} {m n : Nat} (hmn : m ≤ n) (dirs : List Order)
    (xs : List (β × List Value)) : sortTake m dirs xs = (sortTake n dirs xs).take m := by
  unfold sortTake
  rw [List.take_take, Nat.min_eq_left hmn]

/-- **ℰ with count 0** keeps nothing. -/
theorem sortTake_zero {β : Type} (dirs : List Order) (xs : List (β × List Value)) :
    sortTake 0 dirs xs = [] := by
  simp [sortTake]

/-- mergeSort sorts when the comparison is transitive and total on the items present. -/
theorem mergeSort_pairwise_on {β : Type} (le : β → β → Bool) (xs : List β)
    (trans : ∀ a ∈ xs, ∀ b ∈ xs, ∀ c ∈ xs, le a b = true → le b c = true → le a c = true)
    (total : ∀ a ∈ xs, ∀ b ∈ xs, (le a b || le b a) = true) :
    (xs.mergeSort le).Pairwise fun a b => le a b = true := by
  have h1 : (xs.attach.mergeSort fun a b => le a.1 b.1).map Subtype.val = xs.mergeSort le := by
    rw [List.map_mergeSort (s := le) (fun _ _ _ _ => rfl), List.attach_map_subtype_val]
  rw [← h1]
  refine List.Pairwise.map _ (fun _ _ h => h) (List.pairwise_mergeSort ?_ ?_ _)
  · exact fun a b c hab hbc => trans a.1 a.2 b.1 b.2 c.1 c.2 hab hbc
  · exact fun a b => total a.1 a.2 b.1 b.2

/-- **In key order**: when the key comparison is transitive and total on the items present,
ℰ returns its items in key order (each item's key is not after the next one's). This says
nothing about which items are kept when there are more than `n`. -/
theorem sortTake_sorted {β : Type} (n : Nat) (dirs : List Order) (xs : List (β × List Value))
    (trans : ∀ a ∈ xs, ∀ b ∈ xs, ∀ c ∈ xs, (cmpKeys dirs a.2 b.2 != .gt) = true →
      (cmpKeys dirs b.2 c.2 != .gt) = true → (cmpKeys dirs a.2 c.2 != .gt) = true)
    (total : ∀ a ∈ xs, ∀ b ∈ xs,
      ((cmpKeys dirs a.2 b.2 != .gt) || (cmpKeys dirs b.2 a.2 != .gt)) = true) :
    (sortTake n dirs xs).Pairwise fun a b => (cmpKeys dirs a.2 b.2 != .gt) = true := by
  unfold sortTake
  exact (mergeSort_pairwise_on _ xs trans total).sublist (List.take_sublist _ _)

/-! ## ℰ of a finite relation, and `forget` -/

/-- The keys ℰ orders by, as the evaluator reads them from the form. -/
def enumKeys (key : Option (Order × Term)) : List (Term × Order) :=
  match key with
  | some (o, .call "list" ks) => ks.map (·, o)
  | some (o, k) => [(k, o)]
  | none => []

/-- The items ℰ sorts: each tuple with its keys. -/
def enumItems (key : Option (Order × Term)) (r : Finrel) :
    Except String (List (Tuple × List Value)) :=
  r.tuples.mapM fun t => do
    return (t, ← (enumKeys key).mapM fun (p : Term × Order) => p.1.eval t)

/-- **ℰ of a finite relation, step by step.** It paired each tuple with its keys and kept
`sortTake` of them. The pairs do not depend on the count. -/
theorem eval_enum_finrel {env : Env} {tg : List Expr} {c : Count} {key : Option (Order × Term)}
    {e : Expr} {r : Finrel} {v : Val} (hnt : tg.any (Expr.enum c key e).beq = false)
    (he : Expr.eval env tg e = .ok (.finrel r)) (h : Expr.eval env tg (.enum c key e) = .ok v) :
    ∃ items, enumItems key r = .ok items ∧
      items.map (·.1) = r.tuples ∧
      v = .tseq r.heading (sortTake c.toNat ((enumKeys key).map (·.2)) items) := by
  rw [Expr.eval.eq_def] at h
  simp only [hnt, Bool.false_eq_true, ite_false, he, bind, Except.bind, Val.asFinrel, pure,
    Except.pure] at h
  split at h
  · cases h
  · rename_i items hi
    simp only [Except.ok.injEq] at h
    refine ⟨items, hi, mapM_fst ?_ hi, h.symm⟩
    intro x y hy
    split at hy
    · cases hy
    · simp only [Except.ok.injEq] at hy; rw [← hy]

/-- **The prefix law for ℰ, as written forms**: ℰ with a smaller count gives the first
items of ℰ with a larger one, on the same operand and keys. -/
theorem enum_prefix {env : Env} {tg : List Expr} {c c' : Count} {key : Option (Order × Term)}
    {e : Expr} {r : Finrel} {h₁ h₂ : Heading} {ts ts' : List (Tuple × List Value)}
    (hnt : tg.any (Expr.enum c key e).beq = false) (hnt' : tg.any (Expr.enum c' key e).beq = false)
    (he : Expr.eval env tg e = .ok (.finrel r)) (hcc : c.toNat ≤ c'.toNat)
    (h : Expr.eval env tg (.enum c key e) = .ok (.tseq h₁ ts))
    (h' : Expr.eval env tg (.enum c' key e) = .ok (.tseq h₂ ts')) :
    ts = ts'.take c.toNat := by
  obtain ⟨items, hi, -, hv⟩ := eval_enum_finrel hnt he h
  obtain ⟨items', hi', -, hv'⟩ := eval_enum_finrel hnt' he h'
  rw [hi] at hi'; injection hi' with hi'; subst hi'
  injection hv with _ hv; injection hv' with _ hv'
  rw [hv, hv', sortTake_prefix hcc]

/-- `forget` of a sequence of tuples, step by step. -/
theorem eval_forget {env : Env} {tg : List Expr} {e : Expr} {h : Heading}
    {ts : List (Tuple × List Value)} (hnt : tg.any (Expr.forget e).beq = false)
    (he : Expr.eval env tg e = .ok (.tseq h ts)) :
    Expr.eval env tg (.forget e) = .ok (.finrel (Finrel.ofTuples h (ts.map (·.1)))) := by
  rw [Expr.eval.eq_def]
  simp only [hnt, Bool.false_eq_true, ite_false, he, bind, Except.bind, pure, Except.pure]

theorem enum_ok_of_forget {env : Env} {tg : List Expr} {e : Expr} {v : Val}
    (hnt : tg.any (Expr.forget e).beq = false) (h : Expr.eval env tg (.forget e) = .ok v) :
    ∃ w, Expr.eval env tg e = .ok w := by
  cases hw : Expr.eval env tg e with
  | ok w => exact ⟨w, rfl⟩
  | error err =>
    rw [Expr.eval.eq_def] at h
    simp only [hnt, Bool.false_eq_true, ite_false, bind, Except.bind, hw] at h
    cases h

/-- **forget ∘ ℰ is decreasing**: whatever the count, every tuple it gives is in the
operand, under the operand's heading. -/
theorem forget_enum_sub {env : Env} {tg : List Expr} {c : Count} {key : Option (Order × Term)}
    {e : Expr} {r : Finrel} {v : Val} (hnt : tg.any (Expr.enum c key e).beq = false)
    (hnt' : tg.any (Expr.forget (.enum c key e)).beq = false)
    (he : Expr.eval env tg e = .ok (.finrel r))
    (h : Expr.eval env tg (.forget (.enum c key e)) = .ok v) :
    ∃ r', v = .finrel r' ∧ r'.heading = r.heading ∧ ∀ t ∈ r'.tuples, t ∈ r.tuples := by
  obtain ⟨w, hw⟩ := enum_ok_of_forget hnt' h
  obtain ⟨items, -, hfst, rfl⟩ := eval_enum_finrel hnt he hw
  rw [eval_forget hnt' hw] at h
  injection h with h; subst h
  refine ⟨_, rfl, rfl, fun t ht => ?_⟩
  rw [Finrel.mem_ofTuples] at ht
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
  rw [← hfst]
  exact List.mem_map_of_mem ((sortTake_spec _ _ _).1 x hx)

/-- **forget ∘ ℰ with a large enough count is the identity on bodies.** -/
theorem forget_enum_all {env : Env} {tg : List Expr} {c : Count} {key : Option (Order × Term)}
    {e : Expr} {r : Finrel} {v : Val} (hnt : tg.any (Expr.enum c key e).beq = false)
    (hnt' : tg.any (Expr.forget (.enum c key e)).beq = false)
    (he : Expr.eval env tg e = .ok (.finrel r)) (hk : r.tuples.length ≤ c.toNat)
    (h : Expr.eval env tg (.forget (.enum c key e)) = .ok v) :
    ∃ r', v = .finrel r' ∧ r'.heading = r.heading ∧ r'.body = r.body := by
  obtain ⟨w, hw⟩ := enum_ok_of_forget hnt' h
  obtain ⟨items, -, hfst, rfl⟩ := eval_enum_finrel hnt he hw
  rw [eval_forget hnt' hw] at h
  injection h with h; subst h
  have hlen : items.length ≤ c.toNat := by rw [← hfst, List.length_map] at hk; exact hk
  have hp := ((sortTake_spec c.toNat ((enumKeys key).map (·.2)) items).2.2 hlen).map (·.1)
  refine ⟨_, rfl, rfl, Finrel.body_eq fun t => ?_⟩
  rw [Finrel.mem_ofTuples, hp.mem_iff, hfst]

end SolLaws
end Rasso
