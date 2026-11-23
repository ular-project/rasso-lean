import Rasso.Laws.SolJoinSlices
import Rasso.Examples.SolJoin

/-!
# Examples: the laws of ⋈ and ρ on solution sets

Each example is a named definition checked by `#guard`, on programs run by `runProgram`.
Members are compared as sets (`Rasso.SolJoinExamples.sameMembers`): a member's body is
canonical, so two solution sets whose headings list the attributes in different orders still
compare equal.
-/

namespace Rasso.SolJoinLaws.Examples

open Rasso

/-- The helpers of `Rasso/Examples/SolJoin.lean`, by short names. -/
abbrev same := Rasso.SolJoinExamples.sameMembers
abbrev cnt := Rasso.SolJoinExamples.count
abbrev refusedP := Rasso.SolJoinExamples.refused
abbrev side := Rasso.SolJoinExamples.side
abbrev vector := Rasso.SolJoinExamples.vector
abbrev rows := Rasso.SolJoinExamples.rows
abbrev cols := Rasso.SolJoinExamples.cols
abbrev layers := Rasso.SolJoinExamples.layers
abbrev lastSol := Rasso.SolJoinExamples.lastSol

/-- `p` with one more statement, `Q := e`. -/
def andThen (p : Program) (e : Expr) : Program := p ++ [("Q", e)]

def j (a b : String) : Expr := .nary .join [.name a, .name b]

/-- Data `a` over `1..n` (or another name), Decision over `lo..hi`, named `name`. -/
def omegaOver (d x : String) (n lo hi : Nat) (name : String) : Program :=
  [(name, .omegaSol (.omegaRows [(d, .kind .int)] ((List.range n).map fun i => [.int (Int.ofNat i + 1)]))
    (.omega [(x, .range lo hi)]))]

/-- U: ω over Data `a` (2 tuples), Decision `x ∈ 0..1`, cut to members with a 1;
W: ω over Data `b` (2 tuples), Decision `y ∈ 0..1`. -/
def UW : Program := side "a" "x" 2 true "U" ++ side "b" "y" 2 false "W"

/-! ## Commutative and associative, up to heading order -/

def join_comm_powers : Bool := same (andThen UW (j "U" "W")) (andThen UW (j "W" "U"))
#guard join_comm_powers

def join_comm_latin : Bool :=
  same (vector 3 ++ [("Q", .nary .join [rows, cols])]) (vector 3 ++ [("Q", .nary .join [cols, rows])])
#guard join_comm_latin

def join_assoc_latin : Bool :=
  same (vector 2 ++ [("Q", .nary .join [.nary .join [rows, cols], layers])])
    (vector 2 ++ [("Q", .nary .join [rows, .nary .join [cols, layers]])])
#guard join_assoc_latin

/-! ## Idempotent -/

def join_idem : Bool :=
  same (andThen (vector 3) (j "U" "U")) (vector 3) &&
    same (andThen UW (j "U" "U")) (UW ++ [("Q", .name "U")])
#guard join_idem

/-- With empty Data: ω over empty Data has one member (the empty function), and so has its
join with itself; σ_sol that keeps no member gives none, and so does its join with itself.
The catalogue lists idempotence with empty Data as failing; in Rasso it holds. -/
def join_idem_empty_data : Bool :=
  let E : Program := [("E", .omegaSol (.omegaRows [("a", .kind .int)] []) (.omega [("x", .range 0 1)])),
    ("N", .sigmaSol (.expr (.gamma [] (.agg "bool_or" (.call "=" [.attr "x", .val (.int 1)])) (some "ok")
      (.name "E"))) (.name "E"))]
  cnt (andThen E (j "E" "E")) == some 1 && same (andThen E (j "E" "E")) (E ++ [("Q", .name "E")]) &&
    cnt (andThen E (j "N" "N")) == some 0 && cnt (E ++ [("Q", .name "N")]) == some 0
#guard join_idem_empty_data

/-- Empty data on both sides, each adding a Data attribute the other lacks: there are no
groups on either side, so the join has one member (|U|^0 · |V|^0 = 1), even when neither
side has a member. -/
def join_empty_data_one_member : Bool :=
  let none_ (d x name : String) : Program :=
    [(name ++ "0", .omegaSol (.omegaRows [(d, .kind .int)] []) (.omega [(x, .range 0 1)])),
     (name, .sigmaSol (.expr (.gamma [] (.agg "bool_or" (.call "=" [.attr x, .val (.int 1)])) (some "ok")
       (.name (name ++ "0")))) (.name (name ++ "0")))]
  let P := none_ "a" "x" "U" ++ none_ "b" "y" "W"
  cnt (P ++ [("Q", .name "U")]) == some 0 && cnt (P ++ [("Q", .name "W")]) == some 0 &&
    cnt (andThen P (j "U" "W")) == some 1
#guard join_empty_data_one_member

/-! ## The unit ω[DEE, DEE] -/

def unitDEE : Expr := .omegaSol (.omegaRows [] [[]]) (.omega [])

def join_unit : Bool :=
  cnt ([("E", unitDEE)]) == some 1 &&
    same (vector 3 ++ [("E", unitDEE), ("Q", j "U" "E")]) (vector 3) &&
    same (vector 3 ++ [("E", unitDEE), ("Q", j "E" "U")]) (vector 3)
#guard join_unit

/-- With empty Data the unit is refusedP (the whole-Data check: the joined Data is empty, the unit's is not). -/
def join_unit_empty_data_refused : Bool :=
  refusedP ([("Z", .omegaSol (.omegaRows [("a", .kind .int)] []) (.omega [("x", .range 0 1)])),
    ("E", unitDEE), ("Q", j "Z" "E")])
#guard join_unit_empty_data_refused

/-! ## Exponents -/

/-- ω[A, X] ⋈ ω[B, Y] = ω[A × B, X × Y] for disjoint Data and Decisions: 256 members each. -/
def join_omega_omega : Bool :=
  let P := omegaOver "a" "x" 2 0 1 "U" ++ omegaOver "b" "y" 2 0 1 "W"
  let AB : Expr := .nary .join [.omegaRows [("a", .kind .int)] [[.int 1], [.int 2]],
    .omegaRows [("b", .kind .int)] [[.int 1], [.int 2]]]
  cnt (andThen P (j "U" "W")) == some 256 &&
    same (andThen P (j "U" "W")) (andThen P (.omegaSol AB (.omega [("x", .range 0 1), ("y", .range 0 1)])))
#guard join_omega_omega

/-- X^A ⋈ Y^B is not X^A × Y^B: the left has (|X|·|Y|)^(|A|·|B|) = 256 members, the
product of counts is 4^2 · 4^2 / … = 16 for |A| = |B| = 2, |X| = |Y| = 2 (4 · 4). -/
def join_not_product : Bool :=
  let P := omegaOver "a" "x" 2 0 1 "U" ++ omegaOver "b" "y" 2 0 1 "W"
  cnt (andThen P (j "U" "W")) == some 256 &&
    cnt (P ++ [("Q", .name "U")]) == some 4 && cnt (P ++ [("Q", .name "W")]) == some 4 &&
    refusedP (andThen P (.nary .product [.name "U", .name "W"]))
#guard join_not_product

/-- The product law with the same Data: ω[A, X] ⋈ ω[A, Y] = ω[A, X × Y] (36 members). -/
def join_same_data_product : Bool :=
  let P := omegaOver "a" "x" 2 0 2 "U" ++ omegaOver "a" "y" 2 0 1 "W"
  let A : Expr := .omegaRows [("a", .kind .int)] [[.int 1], [.int 2]]
  cnt (andThen P (j "U" "W")) == some 36 &&
    same (andThen P (j "U" "W")) (andThen P (.omegaSol A (.omega [("x", .range 0 2), ("y", .range 0 1)])))
#guard join_same_data_product

/-- The catalogue's shared-Data case (X^A ⋈ Y^B with A, B sharing `a` but not all its
values): there it gives 0 members; in Rasso it is refusedP (the whole-Data check). -/
def join_shared_data_refused : Bool :=
  refusedP ([("U", .omegaSol (.omegaRows [("a", .kind .int)] [[.int 1], [.int 2]]) (.omega [("x", .range 0 1)])),
    ("W", .omegaSol (.omegaRows [("a", .kind .int)] [[.int 2], [.int 3]]) (.omega [("y", .range 0 1)])),
    ("Q", j "U" "W")])
#guard join_shared_data_refused

/-! ## Not distributive over a union of members

V3's members are V1's and V2's together, but U ⋈ V3 has 16 members, not 4 + 4. -/

def join_not_distributive : Bool :=
  let U := omegaOver "a" "x" 2 0 1 "U"
  let C := fun lo hi name => omegaOver "c" "y" 1 lo hi name
  let P := U ++ C 0 0 "V1" ++ C 1 1 "V2" ++ C 0 1 "V3"
  cnt (andThen P (j "U" "V3")) == some 16 &&
    cnt (andThen P (j "U" "V1")) == some 4 && cnt (andThen P (j "U" "V2")) == some 4 &&
    cnt (P ++ [("Q", .name "V3")]) == some 2
#guard join_not_distributive

/-! ## No member twice -/

def noDup (p : Program) : Bool :=
  match lastSol p with
  | some s => let ms := s.candidates.map (·.tuples); (dedup ms).length == ms.length
  | none => false

def join_nodup : Bool :=
  noDup (vector 3 ++ [("Q", .nary .join [rows, cols])]) && noDup (andThen UW (j "U" "W")) &&
    noDup (andThen (vector 3) (j "U" "U"))
#guard join_nodup

/-! ## ρ -/

/-- ρ∘ρ is ρ of the composed renaming, on members. -/
def rename_rename : Bool :=
  same (vector 3 ++ [("Q", .rename [("row", "col")] (.rename [("pos", "row")] (.name "U")))])
    (vector 3 ++ [("Q", .rename [("pos", "col")] (.name "U"))])
#guard rename_rename

/-- ρ with the inverse renaming gives U back. -/
def rename_inverse : Bool :=
  same (vector 3 ++ [("Q", .rename [("row", "pos")] (.rename [("pos", "row")] (.name "U")))]) (vector 3)
#guard rename_inverse

/-- ρ distributes over ⋈_sol (a renaming injective on both headings), on member sets. -/
def rename_join : Bool :=
  let P := UW
  same (andThen P (.rename [("a", "c"), ("y", "z")] (j "U" "W")))
    (andThen P (.nary .join [.rename [("a", "c")] (.name "U"), .rename [("y", "z")] (.name "W")]))
#guard rename_join

/-- ρ commutes with σ_sol, on a program: rename then select, or select then rename. -/
def rename_select : Bool :=
  let cond (s : Expr) (x : String) : Cond :=
    .expr (.gamma [] (.agg "bool_and" (.call "=" [.attr x, .val (.int 1)])) (some "ok") s)
  let P := side "a" "x" 2 false "S"
  same (P ++ [("R", .rename [("x", "z")] (.name "S")), ("Q", .sigmaSol (cond (.name "R") "z") (.name "R"))])
    (P ++ [("T", .sigmaSol (cond (.name "S") "x") (.name "S")), ("Q", .rename [("x", "z")] (.name "T"))])
#guard rename_select

end Rasso.SolJoinLaws.Examples

namespace Rasso.SolJoinLaws.Examples
open Rasso

/-! ## Why members must be functions on their Data

A member of U with a tuple outside U's Data (`a = 2`) is not kept whole by ⋈_sol: the
joined member keeps only the tuple at `a = 1`, so its U-slice is not U's member. This is
why `Sol.MembersOk` (`Rasso/Laws/SolJoinMembers.lean`) is a hypothesis of membership. -/

def intH (as : List String) : Heading := as.map fun a => (a, .kind .int)
def tup (ps : List (String × Int)) : Tuple := ps.map fun (a, v) => (a, .int v)

def badU : Sol := ⟨Finrel.ofTuples (intH ["a"]) [tup [("a", 1)]], intH ["a", "x"],
  [Finrel.ofTuples (intH ["a", "x"]) [tup [("a", 1), ("x", 0)], tup [("a", 2), ("x", 1)]]]⟩
def okV : Sol := ⟨Finrel.ofTuples (intH ["a"]) [tup [("a", 1)]], intH ["a", "y"],
  [Finrel.ofTuples (intH ["a", "y"]) [tup [("a", 1), ("y", 0)]]]⟩

def join_needs_members_ok : Bool :=
  match badU.join okV with
  | .ok W => W.candidates.length == 1 && W.candidates.all (·.tuples.length == 1)
  | .error _ => false
#guard join_needs_members_ok

end Rasso.SolJoinLaws.Examples

namespace Rasso.SolJoinLaws.Examples
open Rasso

/-! ## ⋈_sol's members, as picks

`join_candidates_picks` (`Rasso/Laws/SolJoinPicks.lean`) on the 3 × 3 Latin square: the pure
list of glued picks is `Sol.join`'s member list, member for member. -/

def latinSides : Option (Sol × Sol) := do
  let r ← lastSol (vector 3 ++ [("R", rows)])
  let c ← lastSol (vector 3 ++ [("C", cols)])
  return (r, c)

def join_picks_latin : Bool :=
  match latinSides with
  | some (R, C) => match R.join C with
    | .ok W =>
      let pure_ := (choices ((joinGroups W.data (gU R C)).map fun _ => R.candidates)).flatMap
        fun ps => (choices (okOptions R C W.data ps)).map (glue R C W.data W.heading ps)
      W.candidates.length == 12 && W.candidates.map (·.tuples) == pure_.map (·.tuples)
    | .error _ => false
  | none => false
#guard join_picks_latin

end Rasso.SolJoinLaws.Examples
