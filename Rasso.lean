import Rasso.Value
import Rasso.Finrel
import Rasso.Form
import Rasso.Term
import Rasso.Eval
import Rasso.Mem
import Rasso.WF
import Rasso.Built
import Rasso.Laws
import Rasso.Laws.Finrel
import Rasso.Laws.FinrelExamples
import Rasso.Laws.Unrel
import Rasso.Laws.UnrelExamples
import Rasso.Laws.Sol
import Rasso.Laws.SolExamples
import Rasso.Laws.SolJoin
import Rasso.Laws.SolJoinMembers
import Rasso.Laws.SolJoinPicks
import Rasso.Laws.SolJoinSlices
import Rasso.Laws.SolJoinComplete
import Rasso.Laws.SolRenameMembers
import Rasso.Laws.SolJoinExamples
import Rasso.FSpace
import Rasso.FunctionSpace
import Rasso.FunctionSpaceExamples
import Rasso.HasSubsetExamples
import Rasso.Bridge.Sol
import Rasso.Bridge.Finrel
import Rasso.Rep
import Rasso.FormEq
import Rasso.ESO
import Rasso.Json.Text
import Rasso.Json.Surface
import Rasso.Json.Result
import Rasso.Json.Answer
import Rasso.Unrel
import Rasso.NormalForm
import Rasso.DenseElim
import Rasso.EqElim
import Rasso.LinForm
import Rasso.LinElim
import Rasso.Project
import Rasso.Subst
import Rasso.NormalFormProof
import Rasso.Dense
import Rasso.Equality
import Rasso.LinRead
import Rasso.Linear
import Rasso.Classes
import Rasso.DenseClosure
import Rasso.EqClosure
import Rasso.LinClosure
import Rasso.Examples.Rat
import Rasso.Examples.SymbolString
import Rasso.Examples.Unrel
import Rasso.Examples.Project
import Rasso.Examples.SolRename
import Rasso.Examples.SolJoin
import Rasso.Phi

/-!
# Rasso

A small reference evaluator for rasso, built to agree type for type and operator for
operator with the Racket implementation, and to run programs given in its JSON surface.

* `Rasso.Value`: one universe of values; domains as sets of values.
* `Rasso.Finrel`: headings, tuples, and finite relations whose body is a quotient.
* `Rasso.Form`: the forms, one constructor per shape of Racket's `form-table`.
* `Rasso.Term`: evaluating terms and γ's expressions; γ; unrestricted relations
  (heading + term).
* `Rasso.Eval`: solution sets, multi solution sets, sequences, the evaluator.
* `Rasso.Mem`: membership lemmas, and when each finite operator is not refused.
* `Rasso.WF`: well-formed finite relations, kept by each finite operator.
* `Rasso.Built`: a well-formed finite relation is exactly what empty and adjoin build; the
  equations of adjoin; induction on empty and adjoin; γ keeps well-formedness.
* `Rasso.Unrel`: what an unrestricted relation means (`Holds`, `Total`, `WF`), and what
  σ, ⋈, ×, ∪, ∩, −, ρ and lift hold.
* `Rasso.Project`: π on unrestricted relations: the classes, the recogniser, and removal
  of attributes one at a time.
* `Rasso.NormalForm`: the normal form π's classes share (an `or` of `and`s), generic in the
  class's literals, the executable part.
* `Rasso.DenseElim`: removing an attribute by dense order (Fourier's method), the
  executable part.
* `Rasso.EqElim`: removing an attribute by equality, the executable part.
* `Rasso.LinForm`: linear forms (`Σ cᵢ·bᵢ + k` over ℚ) and the algebra of their values.
* `Rasso.LinElim`: reading terms as linear forms, and removing an attribute by linear
  arithmetic (Fourier–Motzkin), the executable part.
* `Rasso.Subst`: substitution and setting one attribute of a tuple, proved.
* `Rasso.NormalFormProof`: the shared normal form means the term, and a class that removes
  an attribute through it is sound when its leaves and its step on one `and` are.
* `Rasso.Dense`: the dense-order class, proved: its leaves, Fourier's step, and the
  class obligation.
* `Rasso.Equality`: the equality class, proved: its leaves, the step on one `and` (substitute,
  or a fresh value of an infinite domain), and the class obligation.
* `Rasso.LinRead`: a term read as a linear form evaluates as the form, and so does the form
  written back as a term.
* `Rasso.Linear`: the linear class, proved: its rows and bounds, Fourier's step on the
  bounds, and the class obligation.
* `Rasso.DenseClosure`: the dense class as a global class: total, and kept by σ, ⋈, ∪,
  ∩, −, ρ and π.
* `Rasso.EqClosure`: the equality class as a global class over symbol, string or int:
  total, and kept by σ, ⋈, ∪, ∩, −, ρ and π.
* `Rasso.LinClosure`: the linear class as a global class over rat: total, and kept by σ,
  ⋈, ∪, ∩, −, ρ and π, which removes by dense order or linear arithmetic.
* `Rasso.Classes`: π proved: substitution, each class's soundness, agreement
  (`project_ok_iff`), soundness (`project_sound`), and the finite class's closure.
* `Rasso.Laws`: laws of the finite algebra (⋈ commutative and associative, σ over ∪ and ⋈).
* `Rasso.Laws.Finrel`, `Rasso.Laws.FinrelExamples`: every finite-relation law of the paper's
  catalogue, with its definedness, and the laws that fail.
* `Rasso.Laws.Unrel`, `Rasso.Laws.UnrelExamples`: the same for unrestricted relations.
* `Rasso.Laws.Sol`, `Rasso.Laws.SolExamples`: the same for solution sets, multiple solution
  sets and the boundary operators.
* `Rasso.Laws.SolJoin`, `Rasso.Laws.SolJoinExamples`: ρ and ⋈ on solution sets:
  ρ_sol's members, ⋈_sol's shape and refusal proved; the rest checked.
* `Rasso.Laws.SolJoinMembers`: well-formed members (`Sol.MembersOk`); σ_sol keeps them and
  ω_sol gives them. `Rasso.Laws.SolJoinPicks`: ⋈_sol's members as a list of glued picks, and
  the Data/decision clash and the whole-Data check read back from success. `Rasso.Laws.SolJoinSlices`: a
  member's slices are members of the operands, no member twice, and ⋈_sol keeps `MembersOk`.
  `Rasso.Laws.SolJoinComplete`: membership both ways (`mem_join`). `Rasso.Laws.SolRenameMembers`:
  ρ_sol keeps `MembersOk`, and so does an n-ary ⋈_sol.
* `Rasso.FSpace`: solution sets are function spaces; the set meaning of multi
  solution sets.
* `Rasso.FunctionSpace`: why function spaces and not powersets, for plain types (the
  "+1 attribute", the product law, counting, choice); `Rasso.FunctionSpaceExamples` checks
  the counts on solution sets.
* `Rasso.HasSubsetExamples`: `has_subset` as a condition, in γ, and in a multi solution set.
* `Rasso.Bridge.Sol`: the solution-set forms of `Expr.eval` have that meaning.
* `Rasso.FormEq`: decidable equality of forms.
* `Rasso.ESO`: ESO and Rasso: the logic, a sentence
  on a structure as a Rasso program, selection on Boolean function spaces, and its recogniser.
* `Rasso.Phi`: φ, from a solution set or a multi solution set to one relation over
  cells: the fragment it takes, φ itself, the key, and the theorems B, B′,
  C, D, K, M, M′ (`Rasso/Phi/Theorems/`). No core file imports it.
* `Rasso.Json.Text`: JSON text: the strict reader, the writer, rassoAST's layout
  (`write-json` at an indent of 2), the Wadler layout `rasso-lean`'s results use, and
  JSON on one line (`J.compact`).
* `Rasso.Json.Surface`: the JSON surface, rassoAST documents ⇄ programs, a port of the
  Racket implementation's reader and printer of rassoAST.
* `Rasso.Json.Result`: a program's values as JSON.
* `Rasso.Json.Answer`: a statement's answer in the Racket implementation's answer format.
* `Rasso.Examples.Rat`: checks of rat values: the one-`1` rule, the two orders, arithmetic,
  domains and JSON.
* `Rasso.Examples.SymbolString`: checks that `=` refuses a symbol beside a string, and
  that no set domain lets it meet one.
* `Rasso.Examples.Unrel`: checks of the heading checks and of what the operators on
  unrestricted relations hold.
* `Rasso.Examples.Project`: checks of π on unrestricted relations.
* `Rasso.Main`: the `rasso-lean` command, which runs a rassoAST program.
-/
