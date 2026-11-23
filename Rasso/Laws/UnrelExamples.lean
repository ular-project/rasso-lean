import Rasso.Laws.Unrel

/-!
# Examples: laws of unrestricted relations that need totality, and definedness gaps

Each example is a named definition checked by `#guard`.

* A term that **refuses** on a tuple that fits (here `x + "a"`, since `+` refuses a string)
  holds nothing, like `false`. But `or` evaluates both operands, so ∪ with it refuses too.
  So the laws of ∪ and − that need totality fail without it, and so does congruence: two
  relations that hold the same tuples are not interchangeable inside ∪.
* **Gaps**: one side refuses where the other succeeds.
-/

namespace Rasso.UnrelLaws.Examples

open Rasso Rasso.Unrel

def ok? {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

/-- The answer is `b` (not a refusal). -/
def is (e : Except String Bool) (b : Bool) : Bool :=
  match e with
  | .ok c => c == b
  | .error _ => false

def I : Domain := .kind .int
def h : Heading := [("x", I)]
def t1 : Tuple := [("x", .int 1)]

/-- A relation whose term refuses on every fitting tuple. -/
def bad : Unrel := ⟨h, .call "=" [.call "+" [.attr "x", .val (.string "a")], .val (.int 0)]⟩

/-- The truth of a relation's term on `t1`, or the refusal. -/
def truth (u : Except String Unrel) : Except String Bool := do (← u).term.holds t1

/-- `bad` holds nothing on `t1` (it refuses), and so does `empty h`. -/
def bad_holds_nothing : Bool :=
  !ok? (bad.term.holds t1) && is ((UnrelLaws.empty h).term.holds t1) false
#guard bad_holds_nothing

/-- u ∪ ⊤ = ⊤ fails without totality: `bad ∪ ω` refuses on `t1`; `ω` holds it. -/
def union_top_needs_total : Bool :=
  !ok? (truth (bad.union (omega h))) && is (truth (.ok (omega h))) true
#guard union_top_needs_total

/-- Congruence fails without totality: `empty h` and `bad` hold the same tuples, but
`empty h ∪ ω` holds `t1` and `bad ∪ ω` refuses on it. -/
def congruence_needs_total : Bool :=
  is (truth ((UnrelLaws.empty h).union (omega h))) true && !ok? (truth (bad.union (omega h)))
#guard congruence_needs_total

/-- u ∪ (⊤ − u) = ⊤ fails without totality. -/
def union_compl_needs_total : Bool :=
  !ok? (truth (do bad.union (← (omega h).diff bad)))
#guard union_compl_needs_total

/-- Absorption u ∪ (u ∩ v) = u: with v = `bad`, the left side refuses on `t1`, while
u = ω holds it. -/
def absorb_needs_total : Bool :=
  !ok? (truth (do (omega h).union (← (omega h).inter bad))) && is (truth (.ok (omega h))) true
#guard absorb_needs_total

/-- σ as a join with an atom: σ refuses a test that reads an attribute outside the heading;
the join with the atom accepts it. -/
def py : Term := .call "=" [.attr "y", .val (.int 0)]
def select_join_gap : Bool :=
  !ok? ((omega h).select py) && ok? ((omega h).join ⟨h, py⟩)
#guard select_join_gap

/-- σ on a finite relation refuses when the test refuses on one of its tuples; σ on its
unrestricted image does not refuse (the term just refuses on that tuple). -/
def r1 : Finrel := Finrel.ofTuples h [t1]
def ptest : Tuple → Except String Bool := fun t => bad.term.holds t
def finite_select_gap : Bool := !ok? (r1.select ptest) && ok? (r1.toUnrel.select bad.term)
#guard finite_select_gap

/-- ⋈ assoc gap, as for finite relations: float ∩ string refuses, both ∩ `.set []` succeed. -/
def xF : Unrel := omega [("x", .kind .float)]
def xS : Unrel := omega [("x", .kind .string)]
def xE : Unrel := omega [("x", .set [])]
def join_assoc_gap : Bool :=
  !ok? (do (← xF.join xS).join xE) && ok? (do xF.join (← xS.join xE))
#guard join_assoc_gap

end Rasso.UnrelLaws.Examples
