import Rasso.Laws.Finrel

/-!
# Examples: laws of finite relations that fail, and definedness gaps

Each example is a named definition, so the blueprint can cite it, and each `#guard` runs
when the file is built.

* **Fails**: a law of the paper's catalogue that does not hold, shown on small relations.
* **Gap**: a law that holds when both sides succeed, but where one side can refuse while the
  other succeeds.
-/

namespace Rasso.FinrelLaws.Examples

open Rasso Rasso.Finrel

def ok? {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

def tups : Except String Rasso.Finrel → Option (List Tuple)
  | .ok r => some r.tuples
  | .error _ => none

def int1 (a : String) (n : Int) : Tuple := [(a, .int n)]
def I : Domain := .kind .int

/-- r over (a) with 1, 2; s over (a) with 2, 3; u over (a) with 3. -/
def r : Rasso.Finrel := ofTuples [("a", I)] [int1 "a" 1, int1 "a" 2]
def s : Rasso.Finrel := ofTuples [("a", I)] [int1 "a" 2, int1 "a" 3]
def u : Rasso.Finrel := ofTuples [("a", I)] [int1 "a" 3]

/-! ## Fails -/

/-- ∪ is commutative on bodies, but not as Lean `=`: the heading keeps the left operand's
order. -/
def ab : Rasso.Finrel := ofTuples [("a", I), ("b", I)] []
def ba : Rasso.Finrel := ofTuples [("b", I), ("a", I)] []
def union_not_eq_comm : Bool :=
  match ab.union ba, ba.union ab with
  | .ok x, .ok y => x.heading != y.heading
  | _, _ => false
#guard union_not_eq_comm

/-- − is not commutative. -/
def diff_not_comm : Bool := tups (r.diff s) != tups (s.diff r)
#guard diff_not_comm


/-- p over (a, b): (1, 1), (1, 2); q over (a, b): (1, 1). -/
def p2 : Rasso.Finrel := ofTuples [("a", I), ("b", I)] [[("a", .int 1), ("b", .int 1)],
  [("a", .int 1), ("b", .int 2)]]
def q2 : Rasso.Finrel := ofTuples [("a", I), ("b", I)] [[("a", .int 1), ("b", .int 1)]]
def q3 : Rasso.Finrel := ofTuples [("a", I), ("b", I)] [[("a", .int 1), ("b", .int 2)]]

/-- π does not distribute over −: π_a (p − q) = {1}, but π_a p − π_a q = {}. -/
def project_diff_fails : Bool :=
  tups (do (← p2.diff q2).project ["a"]) != tups (do (← p2.project ["a"]).diff (← q2.project ["a"]))
#guard project_diff_fails

/-- π does not distribute over ∩: π_a (q2 ∩ q3) = {}, but π_a q2 ∩ π_a q3 = {1}. -/
def project_inter_fails : Bool :=
  tups (do (← q2.inter q3).project ["a"]) != tups (do (← q2.project ["a"]).inter (← q3.project ["a"]))
#guard project_inter_fails

/-- π does not undo ⋈: π_a (r ⋈ s) is the semijoin, {2}, not r. -/
def project_join_fails : Bool := tups (do (← r.join s).project ["a"]) != some r.tuples
#guard project_join_fails

/-! ## Gaps -/

/-- With an attribute named twice, `r ∪ r` refuses: the heading check is reflexive only for
well-formed headings. -/
def twice : Rasso.Finrel := ofTuples [("a", I), ("a", .kind .string)] []
def union_self_gap : Bool := !ok? (twice.union twice)
#guard union_self_gap

def F : Domain := .kind .float
def S : Domain := .kind .string
def E : Domain := .set []
def xF : Rasso.Finrel := ofTuples [("x", F)] []
def xS : Rasso.Finrel := ofTuples [("x", S)] []
def xE : Rasso.Finrel := ofTuples [("x", E)] []

/-- ⋈ assoc: (xF ⋈ xS) ⋈ xE refuses (float ∩ string), but xF ⋈ (xS ⋈ xE) succeeds
(string ∩ {} = {}, float ∩ {} = {}). -/
def join_assoc_gap : Bool :=
  !ok? (do (← xF.join xS).join xE) && ok? (do xF.join (← xS.join xE))
#guard join_assoc_gap

/-- A test that refuses on 1 and keeps 2. -/
def refuse1 : Tuple → Except String Bool := fun t =>
  if t = int1 "a" 1 then .error "refused" else .ok true
/-- A test that keeps only 2. -/
def only2 : Tuple → Except String Bool := fun t => .ok (t = int1 "a" 2)

/-- σ comm: σ_refuse1 (σ_only2 r) succeeds, σ_only2 (σ_refuse1 r) refuses. -/
def select_comm_gap : Bool :=
  ok? (do (← r.select only2).select refuse1) && !ok? (do (← r.select refuse1).select only2)
#guard select_comm_gap

/-- σ over −: σ_p (r − r₁) succeeds where σ_p r − r₁ refuses, with r₁ = {1}. -/
def r1 : Rasso.Finrel := ofTuples [("a", I)] [int1 "a" 1]
def select_diff_gap : Bool :=
  ok? (do (← r.diff r1).select refuse1) && !ok? (do (← r.select refuse1).diff r1)
#guard select_diff_gap

/-- − is not associative: (r − s) − r₁ = {} but r − (s − r₁) = {1}. -/
def diff_not_assoc : Bool :=
  tups (do (← r.diff s).diff r1) != tups (do r.diff (← s.diff r1))
#guard diff_not_assoc

/-- Absorption: r ∪ (r ∩ ab) refuses (the headings differ); r alone does not. -/
def absorb_gap : Bool := !ok? (do r.union (← r.inter ab))
#guard absorb_gap

/-- ⋈ over ∪: with s over (a) and t over (b), s ∪ t refuses, but (p ⋈ s) ∪ (p ⋈ t) succeeds. -/
def tb : Rasso.Finrel := ofTuples [("b", I)] [int1 "b" 1]
def join_union_gap : Bool :=
  !ok? (do p2.join (← s.union tb)) && ok? (do (← p2.join s).union (← p2.join tb))
#guard join_union_gap

/-- π over ∪: p2 ∪ (a, c) refuses, but π_a p2 ∪ π_a of it succeeds. -/
def ac : Rasso.Finrel := ofTuples [("a", I), ("c", I)] [[("a", .int 5), ("c", .int 0)]]
def project_union_gap : Bool :=
  !ok? (do (← p2.union ac).project ["a"]) && ok? (do (← p2.project ["a"]).union (← ac.project ["a"]))
#guard project_union_gap

/-- π cascade: π_a (π_c r) refuses (no c), π_a r succeeds. -/
def project_cascade_gap : Bool := !ok? (do (← r.project ["c"]).project ["a"]) && ok? (r.project ["a"])
#guard project_cascade_gap

/-- ρ over ⋈: renaming b refuses on r, which has no b, though r ⋈ tb has it. -/
def rename_join_gap : Bool :=
  ok? (do (← r.join tb).rename [("b", "c")]) && !ok? (r.rename [("b", "c")])
#guard rename_join_gap

end Rasso.FinrelLaws.Examples
