import Rasso.Phi.Fragment
import Rasso.Phi.FragmentExamples
import Rasso.Phi.Phi
import Rasso.Phi.Examples
import Rasso.Phi.Answer
import Rasso.Phi.Sound.Term
import Rasso.Phi.Sound.Kinds
import Rasso.Phi.Sound.Agg
import Rasso.Phi.Sound.Perm
import Rasso.Phi.Sound.Group
import Rasso.Phi.Sound.Rel
import Rasso.Phi.Sound.Join
import Rasso.Phi.Sound.Gamma
import Rasso.Phi.Sound.Leaf
import Rasso.Phi.Sound.RelEval
import Rasso.Phi.Sound.Cond
import Rasso.Phi.Theorems.Square
import Rasso.Phi.Theorems.Cells
import Rasso.Phi.Theorems.Lift
import Rasso.Phi.Theorems.Key
import Rasso.Phi.Theorems.Msol
import Rasso.Phi.Theorems.MsolLift

/-!
# φ: from a solution set to one relation over cells

The core files never import this.

* `Rasso.Phi.Fragment`: which solution-set statements φ takes.
* `Rasso.Phi.FragmentExamples`: examples.
* `Rasso.Phi.Phi`: φ itself, `substitute`, `accepts`, `checkSquare`; `phiMsol`,
  `msolSubstitute`, `acceptsMsol`, `checkSquareMsol`.
* `Rasso.Phi.Examples`: φ's examples, each with the square checked on every assignment.
* `Rasso.Phi.Sound.Term`, `Rasso.Phi.Sound.Kinds`: soundness of φ's pieces, terms.
* `Rasso.Phi.Theorems.Square`: theorems B (`phi_square`) and D (`phi_no_refusal`).
* `Rasso.Phi.Theorems.Cells`: theorem C (`phi_cells`).
* `Rasso.Phi.Theorems.Lift`: theorem B′ (`phi_lift`).
* `Rasso.Phi.Theorems.Key`: theorem K (`phiKey_sound`), the ℰ_sol key.
* `Rasso.Phi.Theorems.Msol`: theorem M (`msol_square`), φ of a multi solution set.
* `Rasso.Phi.Theorems.MsolLift`: the `ℰ_msol` key (`phiMsolKey_sound`), theorem M′
  (`phiMsol_lift`) and C for databases (`msol_cells_inj`).
* `Rasso.Phi.Answer`: φ written as the Racket implementation's conformance services read it.
-/
