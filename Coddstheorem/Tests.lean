import Coddstheorem.Algebra
import Coddstheorem.Calculus
import Coddstheorem.Tuples

/-!
# Codd's theorem for Rasso: σ's tests, run by Rasso and read in the calculus

* `Test.evalOn u t`: the truth of the test `t` on the tuple `u`, computed directly.
* `holds_toTerm`: Rasso's evaluator, given the test as a Rasso term, gives that same
  truth and never refuses, when the tuple has the attributes the test reads, its values
  are in `D`, and the constants are in `D` (with `DomOK D`, so `=` never meets an int and
  a float, nor a symbol and a string).
* `Test.toFormula μ t`: the test as a calculus formula, each attribute `a` read as the
  variable `μ a`; `sat_toFormula` says it holds exactly when the test is true on a
  matching tuple.
-/

set_option linter.deprecated false

namespace Coddstheorem

open Rasso

/-- Two values of a domain that holds no int or rat beside a float are compared by `=` without
refusal. -/
theorem applyOp_eq {D : Domain} (hD : DomOK D = true) {v w : Value} (hv : D.mem v = true)
    (hw : D.mem w = true) : applyOp "=" [v, w] = .ok (.bool (v == w)) := by
  have mix : ¬ (isExact v = true ∧ isFloat w = true) ∧ ¬ (isFloat v = true ∧ isExact w = true) ∧
      ¬ (v.isSymbol = true ∧ w.isString = true) ∧ ¬ (v.isString = true ∧ w.isSymbol = true) := by
    cases D with
    | kind k =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro ⟨h1, h2⟩ <;>
        cases k <;> cases v <;> cases w <;>
          simp_all [Domain.mem, Kind.has, isExact, isFloat, Value.isSymbol, Value.isString]
    | range lo hi =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro ⟨h1, h2⟩ <;>
        cases v <;> cases w <;>
          simp_all [Domain.mem, isExact, isFloat, Value.isSymbol, Value.isString]
    | set vs =>
      simp only [DomOK, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
        List.any_eq_false] at hD
      obtain ⟨hn, hs⟩ := hD
      simp only [Domain.mem, List.contains_iff_mem] at hv hw
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro ⟨h1, h2⟩
      · rcases hn with h | h
        · exact absurd h1 (h _ hv)
        · exact absurd h2 (h _ hw)
      · rcases hn with h | h
        · exact absurd h2 (h _ hw)
        · exact absurd h1 (h _ hv)
      · rcases hs with h | h
        · exact absurd h1 (h _ hv)
        · exact absurd h2 (h _ hw)
      · rcases hs with h | h
        · exact absurd h2 (h _ hw)
        · exact absurd h1 (h _ hv)
  cases v <;> cases w <;> first
    | rfl
    | (exfalso; exact mix.1 ⟨rfl, rfl⟩)
    | (exfalso; exact mix.2.1 ⟨rfl, rfl⟩)
    | (exfalso; exact mix.2.2.1 ⟨rfl, rfl⟩)
    | (exfalso; exact mix.2.2.2 ⟨rfl, rfl⟩)

/-- Rasso's order comparisons never refuse: they compute `Cmp.holds`. -/
theorem applyOp_cmp (o : Cmp) (v w : Value) : applyOp o.op [v, w] = .ok (.bool (o.holds v w)) := by
  cases o <;> rfl

namespace Test

/-- The truth of a test on a tuple. -/
def evalOn (u : Tuple) : Test → Bool
  | eqA a b => u.get? a == u.get? b
  | eqC a c => u.get? a == some c
  | cmpA o a b => match u.get? a, u.get? b with
    | some v, some w => o.holds v w
    | _, _ => false
  | cmpC o a c => match u.get? a with
    | some v => o.holds v c
    | none => false
  | and s t => s.evalOn u && t.evalOn u
  | or s t => s.evalOn u || t.evalOn u
  | not t => !t.evalOn u

/-- The test as a calculus formula, attribute `a` read as variable `μ a`. -/
def toFormula (μ : String → String) : Test → Formula
  | eqA a b => .eqv (μ a) (μ b)
  | eqC a c => .eqc (μ a) c
  | cmpA o a b => .cmpv o (μ a) (μ b)
  | cmpC o a c => .cmpc o (μ a) c
  | and s t => .and (s.toFormula μ) (t.toFormula μ)
  | or s t => .or (s.toFormula μ) (t.toFormula μ)
  | not t => .not (t.toFormula μ)

theorem eval_toTerm {D : Domain} (hD : DomOK D = true) {as : List String} {u : Tuple}
    (f : u.Fits (headerOf D as)) :
    (t : Test) → (∀ a ∈ t.attrs, a ∈ as) → (∀ c ∈ t.consts, D.mem c = true) →
      Term.eval u t.toTerm = .ok (.bool (t.evalOn u))
  | eqA a b, ha, _ => by
    obtain ⟨v, hv, dv, -⟩ := get?_fits f (ha a (by simp [attrs]))
    obtain ⟨w, hw, dw, -⟩ := get?_fits f (ha b (by simp [attrs]))
    have e1 : Term.eval u (.attr a) = .ok v := by rw [Term.eval]; simp [hv]
    have e2 : Term.eval u (.attr b) = .ok w := by rw [Term.eval]; simp [hw]
    simp only [toTerm]
    rw [Term.eval]
    simp [e1, e2, List.mapM_cons, bind, Except.bind, pure, Except.pure, applyOp_eq hD dv dw,
      evalOn, hv, hw]
  | eqC a c, ha, hc => by
    obtain ⟨v, hv, dv, -⟩ := get?_fits f (ha a (by simp [attrs]))
    have dc : D.mem c = true := hc c (by simp [consts])
    have e1 : Term.eval u (.attr a) = .ok v := by rw [Term.eval]; simp [hv]
    have e2 : Term.eval u (.val c) = .ok c := by rw [Term.eval]
    simp only [toTerm]
    rw [Term.eval]
    simp [e1, e2, List.mapM_cons, bind, Except.bind, pure, Except.pure, applyOp_eq hD dv dc,
      evalOn, hv]
  | cmpA o a b, ha, _ => by
    obtain ⟨v, hv, -, -⟩ := get?_fits f (ha a (by simp [attrs]))
    obtain ⟨w, hw, -, -⟩ := get?_fits f (ha b (by simp [attrs]))
    have e1 : Term.eval u (.attr a) = .ok v := by rw [Term.eval]; simp [hv]
    have e2 : Term.eval u (.attr b) = .ok w := by rw [Term.eval]; simp [hw]
    simp only [toTerm]
    rw [Term.eval]
    simp [e1, e2, List.mapM_cons, bind, Except.bind, pure, Except.pure, applyOp_cmp, evalOn, hv, hw]
  | cmpC o a c, ha, _ => by
    obtain ⟨v, hv, -, -⟩ := get?_fits f (ha a (by simp [attrs]))
    have e1 : Term.eval u (.attr a) = .ok v := by rw [Term.eval]; simp [hv]
    have e2 : Term.eval u (.val c) = .ok c := by rw [Term.eval]
    simp only [toTerm]
    rw [Term.eval]
    simp [e1, e2, List.mapM_cons, bind, Except.bind, pure, Except.pure, applyOp_cmp, evalOn, hv]
  | and s t, ha, hc => by
    have h1 := eval_toTerm hD f s (fun a h => ha a (by simp [attrs, h])) (fun c h => hc c (by simp [consts, h]))
    have h2 := eval_toTerm hD f t (fun a h => ha a (by simp [attrs, h])) (fun c h => hc c (by simp [consts, h]))
    simp only [toTerm]
    rw [Term.eval]
    simp [h1, h2, List.mapM_cons, bind, Except.bind, pure, Except.pure, applyOp, asBool, evalOn]
  | or s t, ha, hc => by
    have h1 := eval_toTerm hD f s (fun a h => ha a (by simp [attrs, h])) (fun c h => hc c (by simp [consts, h]))
    have h2 := eval_toTerm hD f t (fun a h => ha a (by simp [attrs, h])) (fun c h => hc c (by simp [consts, h]))
    simp only [toTerm]
    rw [Term.eval]
    simp [h1, h2, List.mapM_cons, bind, Except.bind, pure, Except.pure, applyOp, asBool, evalOn]
  | not t, ha, hc => by
    have h1 := eval_toTerm hD f t (fun a h => ha a (by simp [attrs, h])) (fun c h => hc c (by simp [consts, h]))
    simp only [toTerm]
    rw [Term.eval]
    simp [h1, List.mapM_cons, bind, Except.bind, pure, Except.pure, applyOp, asBool, evalOn]

theorem holds_toTerm {D : Domain} (hD : DomOK D = true) {as : List String} {u : Tuple}
    (f : u.Fits (headerOf D as)) {t : Test} (ha : ∀ a ∈ t.attrs, a ∈ as)
    (hc : ∀ c ∈ t.consts, D.mem c = true) : Term.holds u t.toTerm = .ok (t.evalOn u) := by
  simp [Term.holds, eval_toTerm hD f t ha hc, bind, Except.bind, asBool]

theorem sat_toFormula {dom : Value → Prop} {S : Schema} {env : Env} {as : List String}
    {μ : String → String} {ρ : String → Value} {u : Tuple} (hm : Match as μ ρ u) :
    (t : Test) → (∀ a ∈ t.attrs, a ∈ as) →
      (Formula.Sat dom S env (t.toFormula μ) ρ ↔ t.evalOn u = true)
  | eqA a b, ha => by
    simp only [toFormula, Formula.Sat, evalOn, hm a (ha a (by simp [attrs])),
      hm b (ha b (by simp [attrs])), beq_iff_eq, Option.some.injEq]
  | eqC a c, ha => by
    simp only [toFormula, Formula.Sat, evalOn, hm a (ha a (by simp [attrs])), beq_iff_eq,
      Option.some.injEq]
  | cmpA o a b, ha => by
    simp only [toFormula, Formula.Sat, evalOn, hm a (ha a (by simp [attrs])),
      hm b (ha b (by simp [attrs]))]
  | cmpC o a c, ha => by
    simp only [toFormula, Formula.Sat, evalOn, hm a (ha a (by simp [attrs]))]
  | and s t, ha => by
    simp only [toFormula, Formula.Sat, evalOn, Bool.and_eq_true,
      sat_toFormula hm s (fun a h => ha a (by simp [attrs, h])),
      sat_toFormula hm t (fun a h => ha a (by simp [attrs, h]))]
  | or s t, ha => by
    simp only [toFormula, Formula.Sat, evalOn, Bool.or_eq_true,
      sat_toFormula hm s (fun a h => ha a (by simp [attrs, h])),
      sat_toFormula hm t (fun a h => ha a (by simp [attrs, h]))]
  | not t, ha => by
    simp only [toFormula, Formula.Sat, evalOn, Bool.not_eq_true',
      sat_toFormula hm t (fun a h => ha a (by simp [attrs, h]))]
    cases t.evalOn u <;> simp

end Test

end Coddstheorem
