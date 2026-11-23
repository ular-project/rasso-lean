import Rasso.ESO.Meaning

/-!
# Every ESO sentence is a multi solution set (the forward direction)

Theorems `thm:r2-eso-forward` and `thm:r2-eso-same` of the Rasso blueprint.

Forward direction (F1). This is one half of the result. The other half holds only for
selection on Boolean function spaces (`Rasso.ESO.BoolSelection`). So the name says "expresses", not
"captures", which in descriptive complexity means both halves.

For every ESO sentence `ψ` there is one Rasso form, `esoForm ψ A`, in which the structure `A` appears only as data, such that the multi solution set it
evaluates to has a candidate exactly when `ψ` holds on `A`.
-/

namespace Rasso.ESO

open Rasso

theorem esoForm_expresses (ψ : Sentence) (A : Str) (hA : A.WF) (hC : A.Comparable) :
    ∃ m, Expr.eval [] [] (esoForm ψ A) = .ok (.msol m) ∧
      ((∃ db, db ∈ m.candidates) ↔ ψ.Holds A) := by
  obtain ⟨m, hm, hiff⟩ := eval_esoMsol A ψ.ar _ (fun G => decide (ψ.φ.Sat A G (fun _ => default)))
    (fun G E hG hE => cond_meaning A hA hC ψ G hG E hE)
  refine ⟨m, hm, hiff.trans ?_⟩
  exact ⟨fun ⟨G, hG, h⟩ => ⟨G, hG, of_decide_eq_true h⟩, fun ⟨G, hG, h⟩ => ⟨G, hG, decide_eq_true h⟩⟩

end Rasso.ESO
