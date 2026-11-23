import Coddstheorem.AlgebraToCalculus
import Coddstheorem.CalculusToAlgebra
import Coddstheorem.Theorem

/-!
# Codd's theorem for Rasso: the axioms the theorems use

Built with the library, so a new axiom (or a `sorry`, which shows as `sorryAx`) appears in
the build log. Expected: `propext`, `Quot.sound` and `Classical.choice`, Lean's standard
axioms (`Classical.choice` comes in through core lemmas about lists and strings and the
case splits in the proofs).
-/

#print axioms Coddstheorem.algebra_to_calculus
#print axioms Coddstheorem.toCalc_WT
#print axioms Coddstheorem.toCalc_domainIndependent
#print axioms Coddstheorem.check_toRA
#print axioms Coddstheorem.calculus_to_algebra
#print axioms Coddstheorem.codd
#print axioms Coddstheorem.algebra_domainIndependent
#print axioms Coddstheorem.toRA_natural
