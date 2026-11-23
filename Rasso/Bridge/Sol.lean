import Rasso.Eval
import Rasso.FSpace

/-!
# Rasso: bridge lemmas for the solution-set forms 

`Rasso.FSpace` proves what the expressions inside `Expr.eval` compute. This file joins
those results to `Expr.eval` itself, which is total. For each solution-set form
there is a "step by step" lemma: when evaluation is not refused, it says what each
sub-evaluation gave and what the value is. A "meaning" lemma then gives the value's
candidates as the set meaning of `Rasso.FSpace`.

* ω_sol: `eval_omegaSol`, `eval_omegaSol_meaning` (candidates = graphs of total functions,
  |X|^|D| of them).
* σ_sol: `eval_sigmaSol`, `eval_sigmaSol_meaning` (adds the condition, `solTest`).
* ℰ_sol: `eval_enumSol`, `eval_enumSol_meaning`; flatten: `eval_flatten_none`,
  `eval_flatten_some`.
* ω_msol: `eval_omegaMsol`, `eval_omegaMsol_meaning`, with `MembersEval` for the members.
* σ_msol: `eval_sigmaMsol`, `eval_sigmaMsol_meaning` (adds `msolTest`).
* ℰ_msol: `eval_enumMsol`, `eval_enumMsol_meaning`; flatten_msol: `eval_flattenMsol`,
  `mem_rankUnion`.
* Not refused, under simple sufficient hypotheses: `eval_omegaSol_ok`,
  `eval_sigmaSol_ok`, `eval_omegaMsol_ok`, `eval_sigmaMsol_ok`, and `Unrel.tuples_ok`
  for listing a decision relation's tuples.

For ℰ the lemmas say only that the sequence holds candidates, how many, and that it holds
all of them when the count allows. Which candidates a smaller count keeps depends on the
keys and is not stated: Rasso states problems; finding optimal solutions is outside the
algebra.

Conventions:

* Each lemma has the hypothesis `tg.any f.beq = false`: the form `f` being evaluated is
  not itself a target (an operand of an enclosing σ_sol or ℰ_sol). At the top level
  `tg = []`, so the hypothesis holds by `rfl`.
* A condition is kept abstract (`solTest`, `msolTest`: the condition evaluated as
  `Expr.eval` does it). What a condition means, including how a target inside it is
  read, is for the bridges of the condition's own forms.
* Axioms: these lemmas show `Classical.choice`, as everything mentioning `Expr.eval`
  or `Domain.values?` does (see `Rasso.FSpace`).
-/

namespace Rasso

/-! ## Small facts about `Except` -/

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {v : β} :
    (x >>= f) = .ok v ↔ ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

theorem Val.asFinrel_ok {who : String} {w : Val} {r : Finrel} :
    w.asFinrel who = .ok r ↔ w = .finrel r := by
  cases w <;> simp [Val.asFinrel]

theorem Val.asSol_ok {w : Val} {s : Sol} : w.asSol = .ok s ↔ w = .sol s := by
  cases w <;> simp [Val.asSol]

theorem Val.asMsol_ok {w : Val} {m : Msol} : w.asMsol = .ok m ↔ w = .msol m := by
  cases w <;> simp [Val.asMsol]

/-- A `for` loop whose body either refuses or goes on, and that was not refused, went
on at every item. -/
theorem forIn_unit_ok {ε α : Type} {F : α → PUnit → Except ε (ForInStep PUnit)}
    (hF : ∀ a, (∃ e, F a () = .error e) ∨ F a () = .ok (.yield ())) :
    ∀ {l : List α}, forIn l () F = .ok () → ∀ a ∈ l, F a () = .ok (.yield ())
  | [], _, a, ha => by cases ha
  | b :: l, h, a, ha => by
    rw [List.forIn_cons] at h
    rcases hF b with ⟨e, he⟩ | hb
    · rw [he] at h; cases h
    · rw [hb] at h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hb
      · exact forIn_unit_ok hF h a ha

/-! ## ω_sol -/

/-- **ω_sol, step by step.** When `Expr.eval` is not refused on ω_sol(d, dec) (and the
form itself is not a target), it evaluated `d` to a finite relation and `dec` to a
relation with no attribute in common, listed the decision tuples, and built the
candidates `omegaSolCandidates`. -/
theorem eval_omegaSol {env : Env} {tg : List Expr} {d dec : Expr} {v : Val}
    (hnt : tg.any (Expr.omegaSol d dec).beq = false)
    (h : Expr.eval env tg (.omegaSol d dec) = .ok v) :
    ∃ data u picks, Expr.eval env tg d = .ok (.finrel data) ∧
      (∃ w, Expr.eval env tg dec = .ok w ∧ w.asUnrel = .ok u) ∧
      (∀ a ∈ u.heading.attrs, a ∉ data.attrs) ∧ u.tuples = .ok picks ∧
      v = .sol ⟨data, data.heading ++ u.heading,
        omegaSolCandidates (data.heading ++ u.heading) data.tuples picks⟩ := by
  rw [Expr.eval, hnt] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨wd, hd, h1⟩ := except_bind_ok.mp h
  obtain ⟨data, hdata, h2⟩ := except_bind_ok.mp h1
  obtain ⟨w, hw, h3⟩ := except_bind_ok.mp h2
  obtain ⟨u, hu, h4⟩ := except_bind_ok.mp h3
  obtain ⟨⟨⟩, hloop, h5⟩ := except_bind_ok.mp h4
  obtain ⟨picks, hpicks, h6⟩ := except_bind_ok.mp h5
  simp only [pure, Except.pure, Except.ok.injEq] at h6
  rw [Val.asFinrel_ok] at hdata
  subst hdata
  refine ⟨data, u, picks, hd, ⟨w, hw, hu⟩, ?_, hpicks, h6.symm⟩
  intro a ha hda
  have := forIn_unit_ok (fun a => by
    by_cases hc : data.attrs.contains a = true
    · left; simp only [hc, ite_true]; exact ⟨_, rfl⟩
    · right; simp only [hc]; rfl) hloop a ha
  have hc : data.attrs.contains a = true := List.contains_iff_mem.mpr hda
  simp only [hc, ite_true] at this
  cases this

/-- **The meaning of ω_sol.** Its candidates are exactly the graphs of the total
functions from the data's tuples to the decision tuples (`SolMeaning` with no
condition), and there are |X|^|D| of them. -/
theorem eval_omegaSol_meaning {env : Env} {tg : List Expr} {d dec : Expr} {v : Val}
    (hnt : tg.any (Expr.omegaSol d dec).beq = false)
    (h : Expr.eval env tg (.omegaSol d dec) = .ok v) :
    ∃ s picks, v = .sol s ∧ (∃ u : Unrel, u.tuples = .ok picks ∧
        s.heading = s.data.heading ++ u.heading ∧ ∀ a ∈ u.heading.attrs, a ∉ s.data.attrs) ∧
      (∀ c, c ∈ s.candidates ↔ SolMeaning s.heading s.data.tuples picks [] c) ∧
      s.candidates.length = picks.length ^ s.data.tuples.length := by
  obtain ⟨data, u, picks, -, -, hdx, hp, rfl⟩ := eval_omegaSol hnt h
  exact ⟨_, picks, rfl, ⟨u, hp, rfl, hdx⟩,
    omegaSolCandidates_meaning (Finrel.nodup_tuples data), length_omegaSolCandidates _ _ _⟩

/-! ## σ_sol -/

/-- The condition of σ_sol as a test on candidates: the condition evaluated with the
candidate bound and the operand as a target, as `Expr.eval` does it. -/
def solTest (env : Env) (tg : List Expr) (c : Cond) (e : Expr) (r : Finrel) :
    Except String Bool :=
  c.eval (inCondition ((candidateName, .finrel r) :: env)) (e :: tg)

/-- **σ_sol, step by step.** It evaluated its operand to a solution set and filtered
its candidates by the condition. -/
theorem eval_sigmaSol {env : Env} {tg : List Expr} {c : Cond} {e : Expr} {v : Val}
    (hnt : tg.any (Expr.sigmaSol c e).beq = false)
    (h : Expr.eval env tg (.sigmaSol c e) = .ok v) :
    ∃ s cands, Expr.eval env tg e = .ok (.sol s) ∧
      s.candidates.filterM (solTest env tg c e) = .ok cands ∧ v = .sol { s with candidates := cands } := by
  rw [Expr.eval, hnt] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨w, hw, h1⟩ := except_bind_ok.mp h
  obtain ⟨s, hs, h2⟩ := except_bind_ok.mp h1
  obtain ⟨_, -, h2⟩ := except_bind_ok.mp h2
  obtain ⟨cands, hc, h3⟩ := except_bind_ok.mp h2
  simp only [pure, Except.pure, Except.ok.injEq] at h3
  rw [Val.asSol_ok] at hs; subst hs
  exact ⟨s, cands, hw, hc, h3.symm⟩

/-- **The meaning of σ_sol.** If the operand's candidates have the set meaning with
conditions `conds`, the result's have it with σ_sol's condition added. The data and the
heading are the operand's. -/
theorem eval_sigmaSol_meaning {env : Env} {tg : List Expr} {c : Cond} {e : Expr} {v : Val}
    (hnt : tg.any (Expr.sigmaSol c e).beq = false)
    (h : Expr.eval env tg (.sigmaSol c e) = .ok v) {s : Sol}
    (he : Expr.eval env tg e = .ok (.sol s)) {picks : List Tuple}
    {conds : List (Finrel → Except String Bool)}
    (hc : ∀ x, x ∈ s.candidates ↔ SolMeaning s.heading s.data.tuples picks conds x) :
    ∃ s', v = .sol s' ∧ s'.data = s.data ∧ s'.heading = s.heading ∧
      ∀ x, x ∈ s'.candidates ↔ SolMeaning s.heading s.data.tuples picks (solTest env tg c e :: conds) x := by
  obtain ⟨s₀, cands, he', hf, rfl⟩ := eval_sigmaSol hnt h
  rw [he] at he'; cases he'
  exact ⟨_, rfl, rfl, rfl, sigmaSol_meaning hc hf⟩

/-! ## ℰ_sol -/

theorem mapM_fst {ε α β : Type} {f : α → Except ε (α × β)} (hf : ∀ x y, f x = .ok y → y.1 = x) :
    ∀ {l : List α} {ys : List (α × β)}, l.mapM f = .ok ys → ys.map (·.1) = l
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | x :: l, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h1⟩ := except_bind_ok.mp h
    obtain ⟨ys', hys, h2⟩ := except_bind_ok.mp h1
    simp only [pure, Except.pure, Except.ok.injEq] at h2
    subst h2
    rw [List.map_cons, hf x y hy, mapM_fst hf hys]

/-- What `sortTake` keeps: at most `n` of the items, each one of them, and all of them
(in some order) when there are no more than `n`. Which ones it keeps when there are more
is a matter of the keys and is not stated here: finding optimal candidates is outside
the algebra. -/
theorem sortTake_spec {α : Type} (n : Nat) (dirs : List Order) (xs : List (α × List Value)) :
    (∀ x ∈ sortTake n dirs xs, x ∈ xs) ∧ (sortTake n dirs xs).length = min n xs.length ∧
      (xs.length ≤ n → (sortTake n dirs xs).Perm xs) := by
  unfold sortTake
  have hp := List.mergeSort_perm xs fun a b => cmpKeys dirs a.2 b.2 != .gt
  refine ⟨fun x hx => hp.mem_iff.mp (List.mem_of_mem_take hx), ?_, fun hle => ?_⟩
  · rw [List.length_take, hp.length_eq]
  · rw [List.take_of_length_le (by rw [hp.length_eq]; exact hle)]; exact hp

/-- **ℰ_sol, step by step.** It evaluated its operand to a solution set, paired each
candidate with its key (if any), and kept `sortTake` of them. -/
theorem eval_enumSol {env : Env} {tg : List Expr} {c : Count} {key : Option (Order × Expr)}
    {e : Expr} {v : Val} (hnt : tg.any (Expr.enumSol c key e).beq = false)
    (h : Expr.eval env tg (.enumSol c key e) = .ok v) :
    ∃ s items, Expr.eval env tg e = .ok (.sol s) ∧ items.map (·.1) = s.candidates ∧
      v = .cseq s.heading (sortTake c.toNat (key.toList.map (·.1)) items) := by
  rw [Expr.eval, hnt] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨w, hw, h1⟩ := except_bind_ok.mp h
  obtain ⟨s, hs, h2⟩ := except_bind_ok.mp h1
  obtain ⟨_, -, h2⟩ := except_bind_ok.mp h2
  obtain ⟨items, hi, h3⟩ := except_bind_ok.mp h2
  simp only [pure, Except.pure, Except.ok.injEq] at h3
  rw [Val.asSol_ok] at hs; subst hs
  refine ⟨s, items, hw, mapM_fst ?_ hi, h3.symm⟩
  intro x y hy
  cases key with
  | none => simp only [pure, Except.pure, Except.ok.injEq] at hy; subst hy; rfl
  | some ok =>
    obtain ⟨o, k⟩ := ok
    obtain ⟨z, -, hz⟩ := except_bind_ok.mp hy
    obtain ⟨z', -, hz'⟩ := except_bind_ok.mp hz
    simp only [pure, Except.pure, Except.ok.injEq] at hz'; subst hz'; rfl

/-- **The meaning of ℰ_sol.** Every relation in the sequence is a candidate of the
solution set; there are min(k, number of candidates) of them; and when k is at least
the number of candidates, the sequence holds all of them. -/
theorem eval_enumSol_meaning {env : Env} {tg : List Expr} {c : Count} {key : Option (Order × Expr)}
    {e : Expr} {v : Val} (hnt : tg.any (Expr.enumSol c key e).beq = false)
    (h : Expr.eval env tg (.enumSol c key e) = .ok v) :
    ∃ s rs, Expr.eval env tg e = .ok (.sol s) ∧ v = .cseq s.heading rs ∧
      (∀ x ∈ rs, x.1 ∈ s.candidates) ∧ rs.length = min c.toNat s.candidates.length ∧
      (s.candidates.length ≤ c.toNat → (rs.map (·.1)).Perm s.candidates) := by
  obtain ⟨s, items, he, hi, rfl⟩ := eval_enumSol hnt h
  obtain ⟨h1, h2, h3⟩ := sortTake_spec c.toNat (key.toList.map (·.1)) items
  have hlen : items.length = s.candidates.length := by rw [← hi, List.length_map]
  refine ⟨s, _, he, rfl, fun x hx => ?_, by rw [h2, hlen], fun hle => ?_⟩
  · rw [← hi]; exact List.mem_map_of_mem (h1 x hx)
  · rw [← hi]; exact (h3 (hlen ▸ hle)).map _

/-! ## flatten -/

/-- **flatten without a rank.** Its operand was an empty sequence (giving no tuples) or
a sequence of one relation (giving that relation's tuples). -/
theorem eval_flatten_none {env : Env} {tg : List Expr} {e : Expr} {v : Val}
    (hnt : tg.any (Expr.flatten none e).beq = false)
    (h : Expr.eval env tg (.flatten none e) = .ok v) :
    ∃ hd rs, Expr.eval env tg e = .ok (.cseq hd rs) ∧
      ((rs = [] ∧ v = .tseq hd []) ∨
       ∃ r ks ts, rs = [(r, ks)] ∧ v = .tseq hd ts ∧ (∀ x ∈ ts, x.2 = []) ∧
         ∀ t, t ∈ ts.map (·.1) ↔ t ∈ r.tuples) := by
  rw [Expr.eval, hnt] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨w, hw, h1⟩ := except_bind_ok.mp h
  cases w with
  | cseq hd rs =>
    refine ⟨hd, rs, hw, ?_⟩
    match rs, h1 with
    | [], h1 =>
      simp only [pure, Except.pure, Except.ok.injEq] at h1
      exact Or.inl ⟨rfl, h1.symm⟩
    | [(r, ks)], h1 =>
      simp only [pure, Except.pure, Except.ok.injEq] at h1
      refine Or.inr ⟨r, ks, _, rfl, h1.symm, ?_, fun t => ?_⟩
      · intro x hx
        obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx; rfl
      · rw [List.map_map]
        simp only [Function.comp_def, List.map_id']
        exact (List.mergeSort_perm _ _).mem_iff
    | _ :: _ :: _, h1 => cases h1
  | _ => cases h1

/-- **flatten with a rank attribute `a`.** `a` is not an attribute of the solution set,
and the tuples are those of the relations in the sequence, each with its place in the
sequence (from 1) as `a`. -/
theorem eval_flatten_some {env : Env} {tg : List Expr} {a : String} {e : Expr} {v : Val}
    (hnt : tg.any (Expr.flatten (some a) e).beq = false)
    (h : Expr.eval env tg (.flatten (some a) e) = .ok v) :
    ∃ hd rs ts, Expr.eval env tg e = .ok (.cseq hd rs) ∧ a ∉ hd.attrs ∧
      v = .tseq (hd ++ [(a, .kind .int)]) ts ∧ (∀ x ∈ ts, x.2 = []) ∧
      ∀ t, t ∈ ts.map (·.1) ↔ ∃ r ks i, ((r, ks), i) ∈ rs.zipIdx 1 ∧
        ∃ u ∈ r.tuples, t = Tuple.ofPairs ((a, .int i) :: u) := by
  rw [Expr.eval, hnt] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨w, hw, h1⟩ := except_bind_ok.mp h
  cases w with
  | cseq hd rs =>
    simp only at h1
    split at h1
    · cases h1
    · rename_i hc
      simp only [pure, Except.pure, Except.ok.injEq] at h1
      refine ⟨hd, rs, _, hw, fun hm => hc (List.contains_iff_mem.mpr hm), h1.symm, ?_, fun t => ?_⟩
      · intro x hx
        obtain ⟨_, -, hx⟩ := List.mem_flatMap.mp hx
        obtain ⟨_, -, rfl⟩ := List.mem_map.mp hx; rfl
      · simp only [List.map_flatMap, List.map_map, Function.comp_def, List.mem_flatMap,
          List.mem_map]
        constructor
        · rintro ⟨⟨⟨r, ks⟩, i⟩, hri, u, hu, rfl⟩
          exact ⟨r, ks, i, hri, u, (List.mergeSort_perm _ _).mem_iff.mp hu, rfl⟩
        · rintro ⟨r, ks, i, hri, u, hu, rfl⟩
          exact ⟨((r, ks), i), hri, u, (List.mergeSort_perm _ _).mem_iff.mpr hu, rfl⟩
  | _ => cases h1

/-! ## ω_msol -/

/-- `MembersEval env tg ms sols`: each member form of `ms` evaluated to the solution set
in the same place of `sols`, under the same name, and no member is named `I`. -/
inductive MembersEval (env : Env) (tg : List Expr) :
    List (String × Expr) → List (String × Sol) → Prop
  | nil : MembersEval env tg [] []
  | cons {n : String} {e : Expr} {s : Sol} {ms : List (String × Expr)} {sols : List (String × Sol)} :
      (n == "I") = false → Expr.eval env tg e = .ok (.sol s) → MembersEval env tg ms sols →
      MembersEval env tg ((n, e) :: ms) ((n, s) :: sols)

theorem evalMembers_ok {env : Env} {tg : List Expr} :
    ∀ {ms : List (String × Expr)} {sols : List (String × Sol)},
      evalMembers env tg ms = .ok sols → MembersEval env tg ms sols
  | [], sols, h => by
    rw [evalMembers] at h; cases h; exact .nil
  | (n, e) :: ms, sols, h => by
    rw [evalMembers] at h
    by_cases hn : (n == "I") = true
    · simp only [hn, ite_true] at h
      obtain ⟨_, h1, -⟩ := except_bind_ok.mp h; cases h1
    · simp only [hn, Bool.false_eq_true, ite_false] at h
      obtain ⟨w, hw, h2⟩ := except_bind_ok.mp h
      obtain ⟨s, hs, h3⟩ := except_bind_ok.mp h2
      obtain ⟨sols', hsols, h4⟩ := except_bind_ok.mp h3
      simp only [pure, Except.pure, Except.ok.injEq] at h4
      rw [Val.asSol_ok] at hs; subst hs; subst h4
      exact .cons (by simpa using hn) hw (evalMembers_ok hsols)

/-- Each evaluated member came from a member form under the same name. With
`eval_omegaSol_meaning`, a member written ω_sol(D, X) has the graphs of the functions
from D's tuples to X's as its candidates. -/
theorem MembersEval.mem {env : Env} {tg : List Expr} {ms : List (String × Expr)}
    {sols : List (String × Sol)} (h : MembersEval env tg ms sols) {n : String} {s : Sol}
    (hs : (n, s) ∈ sols) : ∃ e, (n, e) ∈ ms ∧ Expr.eval env tg e = .ok (.sol s) := by
  induction h with
  | nil => cases hs
  | cons _ he _ ih =>
    rcases List.mem_cons.mp hs with hh | hs
    · cases hh; exact ⟨_, List.mem_cons_self, he⟩
    · obtain ⟨e', he', hev⟩ := ih hs; exact ⟨e', List.mem_cons_of_mem _ he', hev⟩

theorem MembersEval.names {env : Env} {tg : List Expr} {ms : List (String × Expr)}
    {sols : List (String × Sol)} (h : MembersEval env tg ms sols) :
    sols.map (·.1) = ms.map (·.1) := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

/-- The condition of ω_msol (none or one) as tests on databases, as `Expr.eval` runs it:
the condition evaluated with the database's relations bound by their member names. -/
def msolTest (env : Env) (tg : List Expr) (c : Cond) (db : Db) : Except String Bool :=
  c.eval (inCondition (bindDb db env)) tg

def msolConds (env : Env) (tg : List Expr) : Option Cond → List (Db → Except String Bool)
  | none => []
  | some c => [msolTest env tg c]

/-- **ω_msol, step by step.** It evaluated its members to solution sets (at least one),
formed every way to pick one candidate per member, and kept those passing its
condition. -/
theorem eval_omegaMsol {env : Env} {tg : List Expr} {ms : List (String × Expr)}
    {c : Option Cond} {v : Val} (hnt : tg.any (Expr.omegaMsol ms c).beq = false)
    (h : Expr.eval env tg (.omegaMsol ms c) = .ok v) :
    ∃ sols dbs, MembersEval env tg ms sols ∧ sols ≠ [] ∧
      evalMsolCond env tg c (omegaMsolDbs sols) = .ok dbs ∧
      v = .msol ⟨sols.map fun (n, s) => (n, s.heading), dbs⟩ := by
  rw [Expr.eval, hnt] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨sols, hs, h1⟩ := except_bind_ok.mp h
  by_cases he : sols.isEmpty = true
  · simp only [he, ite_true] at h1
    obtain ⟨_, h2, -⟩ := except_bind_ok.mp h1; cases h2
  · simp only [he, Bool.false_eq_true, ite_false] at h1
    by_cases hd2 : ((sols.map (·.1)).eraseDups.length != sols.length) = true
    · simp only [hd2, ite_true] at h1
      obtain ⟨_, h2, -⟩ := except_bind_ok.mp h1; cases h2
    · simp only [hd2, Bool.false_eq_true, ite_false] at h1
      obtain ⟨dbs, hd, h3⟩ := except_bind_ok.mp h1
      simp only [pure, Except.pure, Except.ok.injEq] at h3
      exact ⟨sols, dbs, evalMembers_ok hs, fun e => he (by simp [e]), hd, h3.symm⟩

/-- **The meaning of ω_msol.** A database is a candidate exactly when it binds each
member's name to one of that member's candidates and passes the condition. -/
theorem eval_omegaMsol_meaning {env : Env} {tg : List Expr} {ms : List (String × Expr)}
    {c : Option Cond} {v : Val} (hnt : tg.any (Expr.omegaMsol ms c).beq = false)
    (h : Expr.eval env tg (.omegaMsol ms c) = .ok v) :
    ∃ sols m, MembersEval env tg ms sols ∧ v = .msol m ∧
      m.members = (sols.map fun (n, s) => (n, s.heading)) ∧
      ∀ db, db ∈ m.candidates ↔ MsolMeaning sols (msolConds env tg c) db := by
  obtain ⟨sols, dbs, hm, -, hd, rfl⟩ := eval_omegaMsol hnt h
  refine ⟨sols, _, hm, rfl, rfl, fun db => ?_⟩
  cases c with
  | none =>
    simp only [evalMsolCond, Except.ok.injEq] at hd; subst hd
    exact omegaMsol_meaning_none db
  | some c => simp only [evalMsolCond] at hd; exact omegaMsol_meaning hd db

/-! ## σ_msol -/

/-- **σ_msol, step by step.** -/
theorem eval_sigmaMsol {env : Env} {tg : List Expr} {c : Cond} {e : Expr} {v : Val}
    (hnt : tg.any (Expr.sigmaMsol c e).beq = false)
    (h : Expr.eval env tg (.sigmaMsol c e) = .ok v) :
    ∃ m dbs, Expr.eval env tg e = .ok (.msol m) ∧
      m.candidates.filterM (msolTest env tg c) = .ok dbs ∧ v = .msol { m with candidates := dbs } := by
  rw [Expr.eval, hnt] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨w, hw, h1⟩ := except_bind_ok.mp h
  obtain ⟨m, hm, h2⟩ := except_bind_ok.mp h1
  obtain ⟨dbs, hd, h3⟩ := except_bind_ok.mp h2
  simp only [pure, Except.pure, Except.ok.injEq] at h3
  rw [Val.asMsol_ok] at hm; subst hm
  exact ⟨m, dbs, hw, hd, h3.symm⟩

/-- **The meaning of σ_msol.** It adds its condition to the operand's set meaning. -/
theorem eval_sigmaMsol_meaning {env : Env} {tg : List Expr} {c : Cond} {e : Expr} {v : Val}
    (hnt : tg.any (Expr.sigmaMsol c e).beq = false)
    (h : Expr.eval env tg (.sigmaMsol c e) = .ok v) {m : Msol}
    (he : Expr.eval env tg e = .ok (.msol m)) {sols : List (String × Sol)}
    {conds : List (Db → Except String Bool)}
    (hc : ∀ db, db ∈ m.candidates ↔ MsolMeaning sols conds db) :
    ∃ m', v = .msol m' ∧ m'.members = m.members ∧
      ∀ db, db ∈ m'.candidates ↔ MsolMeaning sols (msolTest env tg c :: conds) db := by
  obtain ⟨m₀, dbs, he', hf, rfl⟩ := eval_sigmaMsol hnt h
  rw [he] at he'; cases he'
  exact ⟨_, rfl, rfl, sigmaMsol_meaning hc hf⟩

/-! ## ℰ_msol -/

/-- **ℰ_msol, step by step.** -/
theorem eval_enumMsol {env : Env} {tg : List Expr} {c : Count} {key : Option (Order × Expr)}
    {e : Expr} {v : Val} (hnt : tg.any (Expr.enumMsol c key e).beq = false)
    (h : Expr.eval env tg (.enumMsol c key e) = .ok v) :
    ∃ m items, Expr.eval env tg e = .ok (.msol m) ∧ items.map (·.1) = m.candidates ∧
      v = .dbseq m.members (sortTake c.toNat (key.toList.map (·.1)) items) := by
  rw [Expr.eval, hnt] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨w, hw, h1⟩ := except_bind_ok.mp h
  obtain ⟨m, hm, h2⟩ := except_bind_ok.mp h1
  obtain ⟨items, hi, h3⟩ := except_bind_ok.mp h2
  simp only [pure, Except.pure, Except.ok.injEq] at h3
  rw [Val.asMsol_ok] at hm; subst hm
  refine ⟨m, items, hw, mapM_fst ?_ hi, h3.symm⟩
  intro x y hy
  cases key with
  | none => simp only [pure, Except.pure, Except.ok.injEq] at hy; subst hy; rfl
  | some ok =>
    obtain ⟨o, k⟩ := ok
    obtain ⟨z, -, hz⟩ := except_bind_ok.mp hy
    obtain ⟨z', -, hz'⟩ := except_bind_ok.mp hz
    simp only [pure, Except.pure, Except.ok.injEq] at hz'; subst hz'; rfl

/-- **The meaning of ℰ_msol.** Every database in the sequence is a candidate; there are
min(k, number of candidates) of them; with k at least that number, all of them. -/
theorem eval_enumMsol_meaning {env : Env} {tg : List Expr} {c : Count} {key : Option (Order × Expr)}
    {e : Expr} {v : Val} (hnt : tg.any (Expr.enumMsol c key e).beq = false)
    (h : Expr.eval env tg (.enumMsol c key e) = .ok v) :
    ∃ m dbs, Expr.eval env tg e = .ok (.msol m) ∧ v = .dbseq m.members dbs ∧
      (∀ x ∈ dbs, x.1 ∈ m.candidates) ∧ dbs.length = min c.toNat m.candidates.length ∧
      (m.candidates.length ≤ c.toNat → (dbs.map (·.1)).Perm m.candidates) := by
  obtain ⟨m, items, he, hi, rfl⟩ := eval_enumMsol hnt h
  obtain ⟨h1, h2, h3⟩ := sortTake_spec c.toNat (key.toList.map (·.1)) items
  have hlen : items.length = m.candidates.length := by rw [← hi, List.length_map]
  refine ⟨m, _, he, rfl, fun x hx => ?_, by rw [h2, hlen], fun hle => ?_⟩
  · rw [← hi]; exact List.mem_map_of_mem (h1 x hx)
  · rw [← hi]; exact (h3 (hlen ▸ hle)).map _

/-! ## flatten_msol -/

theorem mem_rankUnion {a : String} {h : Heading} {rs : List Finrel} (t : Tuple) :
    t ∈ (rankUnion a h rs).tuples ↔
      ∃ r i, (r, i) ∈ rs.zipIdx 1 ∧ ∃ u ∈ r.tuples, t = Tuple.ofPairs ((a, .int i) :: u) := by
  unfold rankUnion
  rw [Finrel.mem_ofTuples]
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨r, i⟩, hri, u, hu, rfl⟩; exact ⟨r, i, hri, u, hu, rfl⟩
  · rintro ⟨r, i, hri, u, hu, rfl⟩; exact ⟨(r, i), hri, u, hu, rfl⟩

/-- **flatten_msol, step by step.** Without a rank, an empty sequence gives every member
an empty relation and a sequence of one database gives that database; with a rank `a`,
each member's relation is the ranked union (`rankUnion`, see `mem_rankUnion`) of that
member's relations along the sequence. -/
theorem eval_flattenMsol {env : Env} {tg : List Expr} {rank : Option String} {e : Expr}
    {v : Val} (hnt : tg.any (Expr.flattenMsol rank e).beq = false)
    (h : Expr.eval env tg (.flattenMsol rank e) = .ok v) :
    ∃ ms dbs, Expr.eval env tg e = .ok (.dbseq ms dbs) ∧
      ((rank = none ∧ dbs = [] ∧ v = .db (ms.map fun (n, h) => (n, Finrel.ofTuples h []))) ∨
       (rank = none ∧ ∃ db ks, dbs = [(db, ks)] ∧ v = .db db) ∨
       (∃ a, rank = some a ∧ v = .db (ms.map fun (n, h) =>
          (n, rankUnion a h (dbs.map fun (db, _) => (db.lookup n).getD default))))) := by
  rw [Expr.eval, hnt] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨w, hw, h1⟩ := except_bind_ok.mp h
  cases w with
  | dbseq ms dbs =>
    refine ⟨ms, dbs, hw, ?_⟩
    match rank, dbs, h1 with
    | none, [], h1 =>
      simp only [pure, Except.pure, Except.ok.injEq] at h1
      exact Or.inl ⟨rfl, rfl, h1.symm⟩
    | none, [(db, ks)], h1 =>
      simp only [pure, Except.pure, Except.ok.injEq] at h1
      exact Or.inr (Or.inl ⟨rfl, db, ks, rfl, h1.symm⟩)
    | none, _ :: _ :: _, h1 => cases h1
    | some a, dbs, h1 =>
      by_cases hc : (ms.any fun m => m.2.attrs.contains a) = true
      · simp only [hc, ite_true, throw, throwThe, MonadExceptOf.throw] at h1; cases h1
      · simp only [hc, Bool.false_eq_true, ite_false, pure, Except.pure, Except.ok.injEq] at h1
        exact Or.inr (Or.inr ⟨a, rfl, h1.symm⟩)
  | _ => cases h1

/-! ## When the solution-set forms are not refused -/

/-- Filtering is not refused when the test is not refused on any item. -/
theorem filterM_ok_of {ε α : Type} {p : α → Except ε Bool} {l : List α}
    (h : ∀ x ∈ l, ∃ b, p x = .ok b) : ∃ res, l.filterM p = .ok res := by
  refine ⟨_, filterM_ok_iff.mpr ⟨fun x hx => ?_, rfl⟩⟩
  obtain ⟨b, hb⟩ := h x hx
  rw [hb]; trivial

/-- **The tuples of an unrestricted relation are listed** when every domain of its
heading can be listed and its term is not refused on any assignment. -/
theorem Unrel.tuples_ok {u : Unrel} (hfin : ∀ p ∈ u.heading, (p.2.values?).isSome)
    (hholds : ∀ ps, Fits u.heading ps → ∃ b, u.term.holds (Tuple.ofPairs ps.reverse) = .ok b) :
    ∃ ts, u.tuples = .ok ts := by
  obtain ⟨as, has⟩ := (Unrel.assignments_ok_iff u.heading).mpr hfin
  obtain ⟨ts, hts⟩ := filterM_ok_of (p := u.term.holds) (l := as) fun t ht => by
    obtain ⟨ps, hps, rfl⟩ := (Unrel.mem_assignments has t).mp ht
    exact hholds ps hps
  refine ⟨ts, ?_⟩
  unfold Unrel.tuples
  rw [has]; exact hts

theorem forIn_unit_of {ε α : Type} {F : α → PUnit → Except ε (ForInStep PUnit)} :
    ∀ {l : List α}, (∀ a ∈ l, F a () = .ok (.yield ())) → forIn l () F = .ok ()
  | [], _ => rfl
  | b :: l, h => by
    rw [List.forIn_cons, h b List.mem_cons_self]
    exact forIn_unit_of fun a ha => h a (List.mem_cons_of_mem _ ha)

/-- **ω_sol is not refused** when the data is a finite relation, the decision is a
relation whose tuples can be listed (see `Unrel.tuples_ok`), and no attribute is in
both. -/
theorem eval_omegaSol_ok {env : Env} {tg : List Expr} {d dec : Expr}
    (hnt : tg.any (Expr.omegaSol d dec).beq = false) {data : Finrel} {w : Val} {u : Unrel}
    {picks : List Tuple} (hd : Expr.eval env tg d = .ok (.finrel data))
    (hw : Expr.eval env tg dec = .ok w) (hu : w.asUnrel = .ok u)
    (hdx : ∀ a ∈ u.heading.attrs, a ∉ data.attrs) (hp : u.tuples = .ok picks) :
    ∃ v, Expr.eval env tg (.omegaSol d dec) = .ok v := by
  rw [Expr.eval, hnt]
  simp only [Bool.false_eq_true, ite_false]
  rw [hd]
  simp only [bind, Except.bind, Val.asFinrel]
  rw [hw]
  simp only
  rw [hu]
  simp only
  rw [forIn_unit_of]
  · simp only [hp]; exact ⟨_, rfl⟩
  · intro a ha
    have hc : data.attrs.contains a = false := by
      cases hc : data.attrs.contains a
      · rfl
      · exact absurd (List.contains_iff_mem.mp hc) (hdx a ha)
    simp only [hc, Bool.false_eq_true, ite_false]; rfl

/-- **σ_sol is not refused** when its operand is a solution set, the `has_subset`
relations its condition reaches meet the solution set's heading (`Cond.checkSubsets`),
and the condition is not refused on any candidate. -/
theorem eval_sigmaSol_ok {env : Env} {tg : List Expr} {c : Cond} {e : Expr}
    (hnt : tg.any (Expr.sigmaSol c e).beq = false) {s : Sol}
    (he : Expr.eval env tg e = .ok (.sol s))
    (hk : c.checkSubsets env s.heading = .ok ())
    (hc : ∀ r ∈ s.candidates, ∃ b, solTest env tg c e r = .ok b) :
    ∃ v, Expr.eval env tg (.sigmaSol c e) = .ok v := by
  obtain ⟨cands, hf⟩ := filterM_ok_of hc
  rw [Expr.eval, hnt]
  simp only [Bool.false_eq_true, ite_false]
  rw [he]
  simp only [bind, Except.bind, Val.asSol]
  rw [hk]
  unfold solTest at hf
  rw [hf]; exact ⟨_, rfl⟩

/-- **σ_msol is not refused** when its operand is a multi solution set and the
condition is not refused on any database. -/
theorem eval_sigmaMsol_ok {env : Env} {tg : List Expr} {c : Cond} {e : Expr}
    (hnt : tg.any (Expr.sigmaMsol c e).beq = false) {m : Msol}
    (he : Expr.eval env tg e = .ok (.msol m))
    (hc : ∀ db ∈ m.candidates, ∃ b, msolTest env tg c db = .ok b) :
    ∃ v, Expr.eval env tg (.sigmaMsol c e) = .ok v := by
  obtain ⟨dbs, hf⟩ := filterM_ok_of hc
  rw [Expr.eval, hnt]
  simp only [Bool.false_eq_true, ite_false]
  rw [he]
  simp only [bind, Except.bind, Val.asMsol]
  unfold msolTest at hf
  rw [hf]; exact ⟨_, rfl⟩

/-- The members are evaluated when each member form evaluates to a solution set and no
member is named `I`. -/
theorem evalMembers_ok_of {env : Env} {tg : List Expr} :
    ∀ {ms : List (String × Expr)},
      (∀ ne ∈ ms, (ne.1 == "I") = false ∧ ∃ s, Expr.eval env tg ne.2 = .ok (.sol s)) →
      ∃ sols, evalMembers env tg ms = .ok sols
  | [], _ => ⟨[], by rw [evalMembers]⟩
  | (n, e) :: ms, h => by
    obtain ⟨hI, s, he⟩ := h (n, e) List.mem_cons_self
    obtain ⟨sols, hs⟩ := evalMembers_ok_of fun ne hne => h ne (List.mem_cons_of_mem _ hne)
    refine ⟨(n, s) :: sols, ?_⟩
    rw [evalMembers]
    simp only [hI, Bool.false_eq_true, ite_false]
    rw [he]
    simp only [bind, Except.bind, Val.asSol]
    rw [hs]; rfl

theorem MembersEval.length {env : Env} {tg : List Expr} {ms : List (String × Expr)}
    {sols : List (String × Sol)} (h : MembersEval env tg ms sols) : sols.length = ms.length := by
  have := congrArg List.length h.names
  simpa using this

/-- **ω_msol is not refused** when it has at least one member, each member form
evaluates to a solution set, no member is named `I`, no two have one name, and the condition (if any) is not
refused on any candidate database. -/
theorem eval_omegaMsol_ok {env : Env} {tg : List Expr} {ms : List (String × Expr)}
    {c : Option Cond} (hnt : tg.any (Expr.omegaMsol ms c).beq = false) (hne : ms ≠ [])
    (hnd : (ms.map (·.1)).Nodup)
    (hms : ∀ ne ∈ ms, (ne.1 == "I") = false ∧ ∃ s, Expr.eval env tg ne.2 = .ok (.sol s))
    (hc : ∀ sols, MembersEval env tg ms sols → ∀ cond, c = some cond →
      ∀ db, CandOf sols db → ∃ b, msolTest env tg cond db = .ok b) :
    ∃ v, Expr.eval env tg (.omegaMsol ms c) = .ok v := by
  obtain ⟨sols, hs⟩ := evalMembers_ok_of hms
  have hme := evalMembers_ok hs
  have hsne : sols.isEmpty = false := by
    cases sols with
    | nil => exact absurd (List.length_eq_zero_iff.mp (hme.length.symm.trans rfl)) hne
    | cons _ _ => rfl
  have hcond : ∃ dbs, evalMsolCond env tg c (omegaMsolDbs sols) = .ok dbs := by
    cases c with
    | none => exact ⟨_, by rw [evalMsolCond]⟩
    | some cond =>
      simp only [evalMsolCond]
      exact filterM_ok_of fun db hdb =>
        hc sols hme cond rfl db ((mem_omegaMsolDbs db).mp hdb)
  obtain ⟨dbs, hd⟩ := hcond
  have hsnd : ((sols.map (·.1)).eraseDups.length != sols.length) = false := by
    have hl := (length_eraseDups_eq (sols.map (·.1))).mpr (by rw [hme.names]; exact hnd)
    simp only [List.length_map] at hl
    simp [hl]
  rw [Expr.eval, hnt]
  simp only [Bool.false_eq_true, ite_false]
  rw [hs]
  simp only [bind, Except.bind, hsne, hsnd, Bool.false_eq_true, ite_false]
  unfold omegaMsolDbs at hd
  rw [hd]; exact ⟨_, rfl⟩

end Rasso
