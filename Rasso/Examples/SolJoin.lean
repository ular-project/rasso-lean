import Rasso.Eval

/-!
# ⋈ on solution sets: examples

Each example is a small program run by `runProgram`; the `#guard`s state what it gives.

The running example is the ladder of the paper's listing 8: the Latin
vector, renamed to run over rows, columns and layers, and joined. Under ⋈_sol's
meaning, every row and every column of a joined square is a
Latin vector, so the square is a Latin square.
-/

namespace Rasso.SolJoinExamples

open Rasso

/-- The solution set the last statement names. -/
def lastSol (p : Program) : Option Sol :=
  match runProgram p with
  | .ok env => match env.getLast? with
    | some (_, .sol s) => some s
    | _ => none
  | .error _ => none

/-- The number of members of the solution set the last statement names. -/
def count (p : Program) : Option Nat := (lastSol p).map (·.candidates.length)

/-- Whether the program is refused. -/
def refused (p : Program) : Bool := (runProgram p).toOption.isNone

/-- Positions `1..n`. -/
def positions (n : Nat) : Expr :=
  .omegaRows [("pos", .kind .int)] ((List.range n).map fun i => [.int (Int.ofNat i + 1)])

/-- The Latin vector of length `n` over values `1..n`, named `U`. -/
def vector (n : Nat) : Program := [
  ("P", positions n), ("V", .omega [("value", .range 1 n)]),
  ("S", .omegaSol (.name "P") (.name "V")),
  ("U", .sigmaSol (.expr (.gamma [] (.agg "all_different" (.attr "value")) (some "ret") (.name "S")))
    (.name "S"))]

def rows : Expr := .rename [("pos", "row")] (.name "U")
def cols : Expr := .rename [("pos", "col")] (.name "U")
def layers : Expr := .rename [("pos", "layer")] (.name "U")

/-! ## The Latin ladder -/

-- Vectors: n! members.
#guard count (vector 2) = some 2
#guard count (vector 3) = some 6

-- Squares by join: 2 of order 2, 12 of order 3 (the Latin squares).
#guard count (vector 2 ++ [("Q", .nary .join [rows, cols])]) = some 2
#guard count (vector 3 ++ [("Q", .nary .join [rows, cols])]) = some 12

-- The square's Data is rows × columns and its Decision the one shared `value`.
#guard (lastSol (vector 2 ++ [("Q", .nary .join [rows, cols])])).map
  (fun s => (s.data.attrs, s.decision.attrs, s.data.tuples.length)) = some (["row", "col"], ["value"], 4)

-- Cubes by join: 2 of order 2. (Order 3, 24 Latin cubes, was checked with the compiled
-- `rasso-lean`: the interpreter that runs `#guard` is too slow for it.)
#guard count (vector 2 ++ [("Q", .nary .join [rows, cols, layers])]) = some 2

-- Either bracketing gives the same members.
/-- Two solution sets have the same members (as sets of tuple lists). -/
def sameMembers (p q : Program) : Bool :=
  match lastSol p, lastSol q with
  | some s, some t =>
    let ms := s.candidates.map (·.tuples)
    let ns := t.candidates.map (·.tuples)
    ms.length == ns.length && ms.all ns.contains && ns.all ms.contains
  | _, _ => false

#guard sameMembers (vector 2 ++ [("Q", .nary .join [.nary .join [rows, cols], layers])])
  (vector 2 ++ [("Q", .nary .join [rows, .nary .join [cols, layers]])])

-- Joined with itself, a solution set is itself (one group: the whole function).
#guard count (vector 3 ++ [("Q", .nary .join [.name "U", .name "U"])]) = some 6

-- The required cell (row 1, col 1) = 1 keeps 4 of the 12 squares of order 3.
#guard count (vector 3 ++ [("Q", .nary .join [rows, cols]),
  ("R", .sigmaSol (.hasSubset (.omegaRows [("row", .kind .int), ("col", .kind .int), ("value", .kind .int)]
    [[.int 1, .int 1, .int 1]])) (.name "Q"))]) = some 4

/-! ## Powers: ⋈_sol counts as a power

With disjoint Data and disjoint Decisions, `U ⋈ V` has `|U|^|B| · |V|^|A|` members. -/

/-- Data `a` (or `b`) over `1..n`, Decision `x` (or `y`) over `0..1`; `atLeastOne`
keeps the members with at least one 1. -/
def side (d x : String) (n : Nat) (atLeastOne : Bool) (name : String) : Program :=
  let D := .omegaRows [(d, .kind .int)] ((List.range n).map fun i => [.int (Int.ofNat i + 1)])
  let W := Expr.omegaSol D (.omega [(x, .range 0 1)])
  if atLeastOne then
    [(name ++ "0", W), (name, .sigmaSol (.expr (.gamma [] (.agg "bool_or"
      (.call "=" [.attr x, .val (.int 1)])) (some "ok") (.name (name ++ "0")))) (.name (name ++ "0")))]
  else [(name, W)]

-- ω[A, X] ⋈ ω[B, Y] with |A| = |B| = 2: 4^2 · 4^2 = 256, all of ω[A × B, X × Y].
#guard count (side "a" "x" 2 false "U" ++ side "b" "y" 2 false "W" ++
  [("Q", .nary .join [.name "U", .name "W"])]) = some 256

-- |U| = 3, |A| = 2; V = ω with |V| = 4, |B| = 2: 3^2 · 4^2 = 144.
#guard count (side "a" "x" 2 true "U" ++ side "b" "y" 2 false "W" ++
  [("Q", .nary .join [.name "U", .name "W"])]) = some 144

-- |U| = 3, |A| = 2, |B| = 3, V with one member (all ones): 3^3 · 1^2 = 27.
#guard count (side "a" "x" 2 true "U" ++ side "b" "y" 3 false "W0" ++
  [("W", .sigmaSol (.expr (.gamma [] (.agg "bool_and" (.call "=" [.attr "y", .val (.int 1)])) (some "ok")
      (.name "W0"))) (.name "W0")),
   ("Q", .nary .join [.name "U", .name "W"])]) = some 27

/-! ## Conditions Racket does not yet lift

Racket refuses these as "not yet implemented"; here they hold in every group. -/

-- `not`: a vector that is not all ones, in every column of a 2 × 2 square of 0..1.
-- Each column has 3 such vectors, and the rows are free: 3^2 = 9.
#guard count (side "a" "x" 2 false "S" ++ [
  ("U", .sigmaSol (.not (.expr (.gamma [] (.agg "bool_and" (.call "=" [.attr "x", .val (.int 1)])) (some "ok")
      (.name "S")))) (.name "S")),
  ("C", .omegaRows [("c", .kind .int)] [[.int 1], [.int 2]]),
  ("W", .omegaSol (.name "C") (.omega [("y", .range 0 0)])),
  ("Q", .nary .join [.name "U", .name "W"])]) = some 9

/-! ## Refusals -/

-- the Data/decision clash: an attribute that is Data on one side and decided on the other.
#guard refused (vector 2 ++ [
  ("D2", .omegaSol (.omegaRows [("value", .kind .int)] [[.int 1]]) (.omega [("z", .range 0 1)])),
  ("Q", .nary .join [.name "U", .name "D2"])])

-- the whole-Data check: a shared Data attribute whose values do not all match: the left's pos 2 has no
-- partner, so its conditions would be checked over part of its data.
#guard refused (vector 2 ++ [
  ("D2", .omegaSol (.omegaRows [("pos", .kind .int), ("k", .kind .int)] [[.int 1, .int 7]])
    (.omega [("z", .range 0 1)])),
  ("Q", .nary .join [.name "U", .name "D2"])])

-- the whole-Data check: the joined Data is empty while a side's is not.
#guard refused (vector 2 ++ [
  ("D2", .omegaSol (.omegaRows [("pos", .kind .int)] [[.int 9]]) (.omega [("z", .range 0 1)])),
  ("Q", .nary .join [.name "U", .name "D2"])])

-- A solution set joined with a finite relation; and × of solution sets (not yet).
#guard refused (vector 2 ++ [("Q", .nary .join [.name "U", .name "P"])])
#guard refused (vector 2 ++ [("Q", .nary .product [rows, cols])])

-- Shared Data attributes that do match: U over (pos), V over (pos, k) with each pos
-- paired with k ∈ {1, 2}. G_U = {k}: U holds in each k-copy; G_V = {}: V's one slice.
#guard count (vector 2 ++ [
  ("D2", .omegaSol (.omegaRows [("pos", .kind .int), ("k", .kind .int)]
    [[.int 1, .int 1], [.int 1, .int 2], [.int 2, .int 1], [.int 2, .int 2]]) (.omega [("z", .range 0 0)])),
  ("Q", .nary .join [.name "U", .name "D2"])]) = some 4

end Rasso.SolJoinExamples
