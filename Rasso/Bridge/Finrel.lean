import Rasso.Eval
import Rasso.Bridge.Sol
import Rasso.WF

/-!
# Rasso: bridge lemmas for the finite-algebra forms of `Expr.eval`

The finite-algebra half (the solution-set half is `Rasso.Bridge.Sol`). Each lemma computes
one form of `Expr.eval` from the values of its operands, so a proof about a program can go
form by form.

All lemmas here are for evaluation with no targets (`tg = []`), which is how a program's
statements and a multi solution set's condition are evaluated.

Conventions:

* Only the forms the ESO construction uses are covered: names, ω with rows, σ, π, ρ,
  n-ary ⋈, ∪ and − of finite relations, and γ with no grouping.
-/

set_option linter.unusedSimpArgs false

namespace Rasso

theorem eval_name {env : Env} {n : String} {v : Val} (h : env.lookup n = some v) :
    Expr.eval env [] (.name n) = .ok v := by
  rw [Expr.eval]; simp [h]

theorem eval_select {env : Env} {p : Term} {e : Expr} {r s : Finrel}
    (he : Expr.eval env [] e = .ok (.finrel r)) (hs : r.select p.holds = .ok s)
    (hp : ∀ a ∈ p.attrs, a ∈ r.heading.attrs) :
    Expr.eval env [] (.select p e) = .ok (.finrel s) := by
  rw [Expr.eval]; simp [he, hs, Heading.scoped_ok.mpr hp, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]

theorem eval_project {env : Env} {as : List String} {e : Expr} {r s : Finrel}
    (he : Expr.eval env [] e = .ok (.finrel r)) (hs : r.project as = .ok s) :
    Expr.eval env [] (.project as e) = .ok (.finrel s) := by
  rw [Expr.eval]; simp [he, hs, bind, Except.bind, Functor.map, Except.map, Val.asFinrel, pure, Except.pure]

/-- π of an unrestricted relation evaluates to the relation `Unrel.project` gives, and is
refused exactly when it refuses. -/
theorem eval_project_unrel {env : Env} {as : List String} {e : Expr} {u w : Unrel}
    (he : Expr.eval env [] e = .ok (.unrel u)) :
    Expr.eval env [] (.project as e) = .ok (.unrel w) ↔ u.project as = .ok w := by
  rw [Expr.eval]
  simp only [he, bind, Except.bind, pure, Except.pure]
  cases u.project as with
  | error _ => simp
  | ok w' => simp

theorem eval_rename {env : Env} {ren : List (String × String)} {e : Expr} {r s : Finrel}
    (he : Expr.eval env [] e = .ok (.finrel r)) (hs : r.rename ren = .ok s) :
    Expr.eval env [] (.rename ren e) = .ok (.finrel s) := by
  rw [Expr.eval]; simp [he, hs, bind, Except.bind, Functor.map, Except.map, Val.asFinrel, pure, Except.pure]

theorem eval_join2 {env : Env} {e₁ e₂ : Expr} {r₁ r₂ s : Finrel}
    (h₁ : Expr.eval env [] e₁ = .ok (.finrel r₁)) (h₂ : Expr.eval env [] e₂ = .ok (.finrel r₂))
    (hs : r₁.join r₂ = .ok s) :
    Expr.eval env [] (.nary .join [e₁, e₂]) = .ok (.finrel s) := by
  rw [Expr.eval]
  simp [h₁, h₂, hs, bind, Except.bind, Functor.map, Except.map, Val.asFinrel, List.mapM_cons,
    List.foldlM, pure, Except.pure]

theorem eval_union2 {env : Env} {e₁ e₂ : Expr} {r₁ r₂ s : Finrel}
    (h₁ : Expr.eval env [] e₁ = .ok (.finrel r₁)) (h₂ : Expr.eval env [] e₂ = .ok (.finrel r₂))
    (hs : r₁.union r₂ = .ok s) :
    Expr.eval env [] (.nary .union [e₁, e₂]) = .ok (.finrel s) := by
  rw [Expr.eval]
  simp [h₁, h₂, hs, bind, Except.bind, Functor.map, Except.map, Val.asFinrel, List.mapM_cons,
    List.foldlM, pure, Except.pure]

theorem eval_except2 {env : Env} {e₁ e₂ : Expr} {r₁ r₂ s : Finrel}
    (h₁ : Expr.eval env [] e₁ = .ok (.finrel r₁)) (h₂ : Expr.eval env [] e₂ = .ok (.finrel r₂))
    (hs : r₁.diff r₂ = .ok s) :
    Expr.eval env [] (.nary .except [e₁, e₂]) = .ok (.finrel s) := by
  rw [Expr.eval]
  simp [h₁, h₂, hs, bind, Except.bind, Functor.map, Except.map, Val.asFinrel, List.mapM_cons,
    List.foldlM, pure, Except.pure]

end Rasso
