import Rasso.Eval

/-!
# ρ on a solution set: examples

Each example is a small program run by `runProgram`; the `#guard`s state what it gives.

The solution set is the Latin vector of length 2: Data `pos ∈ {1, 2}`, Decision
`value ∈ {1, 2}`, and the condition that its values all differ. It has two members.
-/

namespace Rasso.SolRenameExamples

open Rasso

def Positions : Expr := .omegaRows [("pos", .kind .int)] [[.int 1], [.int 2]]
def Values : Expr := .omega [("value", .range 1 2)]

/-- The Latin vector: all different values. -/
def vector : Program := [
  ("P", Positions), ("V", Values),
  ("S", .omegaSol (.name "P") (.name "V")),
  ("U", .sigmaSol (.expr (.gamma [] (.agg "all_different" (.attr "value")) (some "ret") (.name "S")))
    (.name "S"))]

/-- The solution set the last statement names. -/
def lastSol (p : Program) : Option Sol :=
  match runProgram p with
  | .ok env => match env.getLast? with
    | some (_, .sol s) => some s
    | _ => none
  | .error _ => none

/-- Whether the program is refused. -/
def refused (p : Program) : Bool := (runProgram p).toOption.isNone

/-- The members, each as its sorted list of rows `(attribute, value)`. -/
def members (s : Sol) : List (List Tuple) := s.candidates.map (·.tuples)

-- The vector has two members.
#guard (lastSol vector).map (·.candidates.length) = some 2

-- ρ[pos → row]: the same two members, over `row`; the Data is renamed too.
#guard (lastSol (vector ++ [("R", .rename [("pos", "row")] (.name "U"))])).map
  (fun s => (s.data.attrs, s.heading.attrs, s.candidates.length)) = some (["row"], ["row", "value"], 2)

-- The members are the renamed members: row 1 ↦ 1, row 2 ↦ 2 is one of them.
#guard ((lastSol (vector ++ [("R", .rename [("pos", "row")] (.name "U"))])).map members).map
  (fun ms => ms.contains [Tuple.ofPairs [("row", .int 1), ("value", .int 1)],
                          Tuple.ofPairs [("row", .int 2), ("value", .int 2)]]) = some true

-- A Decision attribute can be renamed as well, and both at once.
#guard (lastSol (vector ++ [("R", .rename [("pos", "col"), ("value", "v")] (.name "U"))])).map
  (fun s => (s.data.attrs, s.heading.attrs, s.candidates.length)) = some (["col"], ["col", "v"], 2)

-- Renaming swaps work: the renames are simultaneous.
#guard (lastSol (vector ++ [("R", .rename [("pos", "value"), ("value", "pos")] (.name "U"))])).map
  (fun s => (s.data.attrs, s.candidates.length)) = some (["value"], 2)

-- Refused: an old name that is not an attribute.
#guard refused (vector ++ [("R", .rename [("row", "col")] (.name "U"))])

-- Refused: two attributes given one name (a Data and a Decision attribute here).
#guard refused (vector ++ [("R", .rename [("pos", "value")] (.name "U"))])

-- σ_sol after ρ reads the new names: the member with row 1 ↦ 2.
#guard (lastSol (vector ++ [("R", .rename [("pos", "row")] (.name "U")),
    ("T", .sigmaSol (.hasSubset (.omegaRows [("row", .kind .int), ("value", .kind .int)]
      [[.int 1, .int 2]])) (.name "R"))])).map (·.candidates.length) = some 1

end Rasso.SolRenameExamples
