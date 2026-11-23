import Rasso.Phi.Fragment

/-!
# The φ fragment: examples

Each `#guard` says whether the last statement of a small program is a solution set φ takes.

The solution set: data `Cells` (`c ∈ 1..3`), decision `v ∈ 1..2`.
-/

namespace Rasso.Phi.FragmentExamples

open Rasso Rasso.Phi

def Cells : Expr := .omegaRows [("c", .range 1 3)] [[.int 1], [.int 2], [.int 3]]
def V : Expr := .omega [("v", .range 1 2)]
def Req : Expr := .omegaRows [("c", .kind .int), ("v", .kind .int)] [[.int 1, .int 2]]
def Two : Expr := .omegaRows [("v", .kind .int)] [[.int 2]]

def base : Program := [("Cells", Cells), ("V", V), ("Req", Req), ("Two", Two),
  ("S", .omegaSol (.name "Cells") (.name "V"))]

/-- Whether the last statement of `p` is in the fragment. -/
def lastIn (p : Program) : Bool := (statementChain p (p.length - 1)).isSome

/-- The markers of the last statement's levels, inner first. -/
def markers (p : Program) : List Expr :=
  ((statementChain p (p.length - 1)).map fun ch => ch.levels.map (·.marker)).getD []

/-- `γ[][sum(v) <= k]` over `x`: a bound on the sum of the cells. -/
def sumAtMost (k : Int) (x : Expr) : Cond :=
  .expr (.gamma [] (.call "<=" [.agg "sum" (.attr "v"), .val (.int k)]) none x)

/-- "All cells differ, in each group by c": γ[c][all_different(v) → ok], then bool_and. -/
def allDiff (x : Expr) : Cond :=
  .expr (.gamma [] (.agg "bool_and" (.attr "ok")) none
    (.gamma ["c"] (.agg "all_different" (.attr "v")) (some "ok") x))

/-! ## In the fragment -/

-- ω_sol itself, with no condition.
#guard lastIn base
-- A bound on a sum (as the cakes' conditions are).
#guard lastIn (base ++ [("T", .sigmaSol (sumAtMost 4 (.name "S")) (.name "S"))])
-- Grouping, then an aggregate of the groups (as the Latin square's conditions are).
#guard lastIn (base ++ [("T", .sigmaSol (allDiff (.name "S")) (.name "S"))])
-- has_subset of a leaf, and its negation.
#guard lastIn (base ++ [("T", .sigmaSol (.not (.hasSubset (.name "Req"))) (.name "S"))])
-- A join of the candidate with a leaf, on a cell (φ will need a guard here).
#guard lastIn (base ++ [("T", .sigmaSol
  (.expr (.gamma [] (.call ">=" [.agg "count" (.attr "c"), .val (.int 1)]) none
    (.nary .join [.name "S", .name "Two"]))) (.name "S"))])
-- extend over the candidate.
#guard lastIn (base ++ [("T", .sigmaSol
  (.expr (.gamma [] (.agg "bool_and" (.attr "ok")) none
    (.extend "ok" (.call "<=" [.attr "v", .attr "c"]) (.name "S")))) (.name "S"))])
-- ω_sol written in place: its form is the marker.
#guard lastIn [("Cells", Cells), ("V", V),
  ("T", .sigmaSol (sumAtMost 4 (.omegaSol (.name "Cells") (.name "V"))) (.omegaSol (.name "Cells") (.name "V")))]
-- Through two names: each level keeps its own operand as its marker.
#guard exprsBeq (markers (base ++ [("T", .sigmaSol (sumAtMost 5 (.name "S")) (.name "S")),
  ("U", .sigmaSol (allDiff (.name "T")) (.name "T"))])) [.name "S", .name "T"]
-- A leaf naming a second name for the same solution set is in the fragment: it is refused
-- on its value (a solution set), not on its form.
#guard lastIn (base ++ [("S2", .name "S"),
  ("T", .sigmaSol (.expr (.gamma [] (.agg "count" (.attr "c")) none (.nary .join [.name "S2", .name "S"]))) (.name "S2"))])

/-! ## Outside the fragment -/

-- A statement that is not a solution set.
#guard !lastIn (base ++ [("X", .name "Cells")])
-- A name bound again to something else: the latest binding wins, as in the evaluator.
#guard !lastIn (base ++ [("S", .name "Cells"), ("T", .sigmaSol (sumAtMost 4 (.name "S")) (.name "S"))])
-- σ over the candidate (Racket refuses it; Lean's evaluator does not).
#guard !lastIn (base ++ [("T", .sigmaSol
  (.expr (.gamma [] (.agg "count" (.attr "c")) none (.select (.call "=" [.attr "v", .val (.int 1)]) (.name "S"))))
  (.name "S"))])
-- A has_subset whose relation contains the candidate.
#guard !lastIn (base ++ [("T", .sigmaSol (.hasSubset (.nary .join [.name "S", .name "Req"])) (.name "S"))])
-- A leaf with a solution-set form inside.
#guard !lastIn (base ++ [("T", .sigmaSol
  (.hasSubset (.forget (.flatten none (.enumSol (.int 1) none (.omegaSol (.name "Cells") (.name "V"))))))
  (.name "S"))])
-- A float constant.
#guard !lastIn (base ++ [("T", .sigmaSol
  (.expr (.gamma [] (.call "<=" [.agg "sum" (.attr "v"), .val (.float ⟨false, 15, -1⟩)]) none (.name "S")))
  (.name "S"))])
-- An unknown aggregate.
#guard !lastIn (base ++ [("T", .sigmaSol
  (.expr (.gamma [] (.agg "median" (.attr "v")) none (.name "S"))) (.name "S"))])
-- One level outside the fragment takes the whole chain out.
#guard !lastIn (base ++ [("T", .sigmaSol (.hasSubset (.name "S")) (.name "S")),
  ("U", .sigmaSol (sumAtMost 4 (.name "T")) (.name "T"))])

end Rasso.Phi.FragmentExamples
