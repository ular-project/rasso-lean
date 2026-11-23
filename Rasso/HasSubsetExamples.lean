import Rasso.Eval

/-!
# `has_subset`: examples

Each example is a small program run by `runProgram`; the `#guard`s state what it gives.

The solution set: data `Cells` (`c ∈ 1..3`), decision `v ∈ 1..2`, so 2^3 = 8 candidates.
`Req` requires cell 1 to be 2 and cell 3 to be 1: two of the 8 candidates hold it.
-/

namespace Rasso.HasSubsetExamples

open Rasso

def Cells : Expr := .omegaRows [("c", .range 1 3)] [[.int 1], [.int 2], [.int 3]]
def V : Expr := .omega [("v", .range 1 2)]
/-- Required cells, over the solution set's attributes, with plain `int` domains (they
meet the solution set's ranges, as a join's do). -/
def Req : Expr := .omegaRows [("c", .kind .int), ("v", .kind .int)] [[.int 1, .int 2], [.int 3, .int 1]]

def base : Program := [("Cells", Cells), ("V", V), ("S", .omegaSol (.name "Cells") (.name "V")), ("Req", Req)]

/-- The number of candidates of the solution set the last statement names. -/
def cands (p : Program) : Option Nat :=
  match runProgram p with
  | .ok env => match env.getLast? with
    | some (_, .sol s) => some s.candidates.length
    | _ => none
  | .error _ => none

/-- Whether the program is refused. -/
def refused (p : Program) : Bool := (runProgram p).toOption.isNone

/-! ## As a condition -/

-- σ_sol[has_subset(Req)](S): the candidates that contain both required cells.
#guard cands (base ++ [("T", .sigmaSol (.hasSubset (.name "Req")) (.name "S"))]) = some 2

-- Its negation keeps the other six.
#guard cands (base ++ [("T", .sigmaSol (.not (.hasSubset (.name "Req"))) (.name "S"))]) = some 6

-- A relation written in place works too.
#guard cands (base ++ [("T", .sigmaSol (.hasSubset
  (.omegaRows [("c", .range 1 3), ("v", .range 1 2)] [[.int 2, .int 2]])) (.name "S"))]) = some 4

-- The empty relation is a subset of every candidate.
#guard cands (base ++ [("T", .sigmaSol (.hasSubset
  (.omegaRows [("c", .kind .int), ("v", .kind .int)] [])) (.name "S"))]) = some 8

-- A relation over other attributes is refused, even with no candidates: the heading
-- is checked before any candidate is tested.
#guard refused (base ++ [("T", .sigmaSol (.hasSubset (.omegaRows [("c", .kind .int)] [[.int 1]])) (.name "S"))])
#guard refused (base ++ [
  ("E", .omegaSol (.omegaRows [("c", .range 1 3)] [[.int 1]]) (.omega [("v", .set [])])),
  ("T", .sigmaSol (.hasSubset (.omegaRows [("c", .kind .int)] [[.int 1]])) (.name "E"))])


-- The candidate itself is not a relation `has_subset` may read: refused. So is a form
-- that only contains it.
#guard refused (base ++ [("T", .sigmaSol (.hasSubset (.name "S")) (.name "S"))])
#guard refused (base ++ [("T", .sigmaSol (.hasSubset (.nary .join [.name "S", .name "Req"])) (.name "S"))])

/-! ## In γ's expression -/

-- γ[][has_subset(Req) → ok] over the candidate, as a condition: the same two.
#guard cands (base ++ [("T", .sigmaSol
  (.expr (.gamma [] (.hasSubset (.name "Req")) (some "ok") (.name "S"))) (.name "S"))]) = some 2

/-- Grouped: in each group of the candidate by `v`, the group holds cell 2 with that
value. Over a plain relation, outside any solution set. -/
def G : Expr := .omegaRows [("c", .range 1 3), ("v", .range 1 2)]
  [[.int 1, .int 1], [.int 2, .int 1], [.int 3, .int 2]]
def Need : Expr := .omegaRows [("c", .kind .int)] [[.int 1]]

-- γ[v][has_subset(Need) → ok](G): `v = 1` has cell 1, `v = 2` does not.
#guard (match runProgram [("G", G), ("Need", Need),
    ("R", .gamma ["v"] (.hasSubset (.name "Need")) (some "ok") (.name "G"))] with
  | .ok env => match env.getLast? with
    | some (_, .finrel r) => r.tuples.map (fun t => (t.get? "v", t.get? "ok"))
    | _ => []
  | .error _ => []) =
  [(some (.int 2), some (.bool false)), (some (.int 1), some (.bool true))]

-- An attribute of the relation that γ's operand lacks is refused.
#guard refused [("G", G), ("R", .gamma [] (.hasSubset (.omegaRows [("w", .kind .int)] [[.int 1]])) (some "ok") (.name "G"))]

/-! ## In a multi solution set -/

-- As a condition of ω_msol it is refused: it reads one candidate, not the members.
#guard refused (base ++ [("M", .omegaMsol [("A", .name "S")] (some (.hasSubset (.name "Req"))))])

-- Inside γ it is allowed; a member's name is not a relation it may read.
#guard refused (base ++ [("M", .omegaMsol [("A", .name "S")]
  (some (.expr (.gamma [] (.hasSubset (.name "A")) (some "ok") (.name "A")))))])

end Rasso.HasSubsetExamples
