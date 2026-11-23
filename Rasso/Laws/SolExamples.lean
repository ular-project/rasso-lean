import Rasso.Laws.Sol

/-!
# Examples: laws of solution sets that fail, and definedness gaps

Each example is a named definition checked by `#guard`. Programs are evaluated with `Expr.eval`.

Data `A` has tuples `a = 1, 2`, data `B` has `a = 2, 3`; `X` is a two-valued decision.
-/

namespace Rasso.SolLaws.Examples

open Rasso

def ok? {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

def A : Expr := .omegaRows [("a", .range 1 3)] [[.int 1], [.int 2]]
def B : Expr := .omegaRows [("a", .range 1 3)] [[.int 2], [.int 3]]
def X : Expr := .omega [("x", .kind .bool)]
def U : Expr := .omegaSol A X

/-- The number of candidates of a solution set, or none if it is refused. -/
def count (e : Expr) : Option Nat :=
  match Expr.eval [] [] e with
  | .ok (.sol s) => some s.candidates.length
  | _ => none

/-- The number of databases of a multi solution set, or none if it is refused. -/
def countDbs (e : Expr) : Option Nat :=
  match Expr.eval [] [] e with
  | .ok (.msol m) => some m.candidates.length
  | _ => none

/-! ## Selection: commutative only where both orders are defined -/

/-- The test `q` drops `1`; the test `p` refuses on `1`. -/
def q (n : Nat) : Except String Bool := .ok (n != 1)
def p (n : Nat) : Except String Bool := if n == 1 then .error "refused" else .ok true

/-- σ_p (σ_q l) succeeds, since `q` drops the item `p` refuses on; σ_q (σ_p l) is refused. -/
def select_comm_gap : Bool :=
  ok? (do let lq ← [1, 2].filterM q; lq.filterM p) &&
    !ok? (do let lp ← [1, 2].filterM p; lp.filterM q)
#guard select_comm_gap

/-! ## Selection by DEE or DUM: refused, not identity and zero -/

def DEE : Expr := .omegaRows [] [[]]
def DUM : Expr := .omegaRows [] []

/-- "A DEE test is the identity, a DUM test is zero", a law of the paper, does not carry over: a
written condition must give one value (one attribute, one tuple), so σ_sol refuses both. -/
def nullary_tests_refused : Bool :=
  (count (.sigmaSol (.expr DEE) U)).isNone && (count (.sigmaSol (.expr DUM) U)).isNone &&
    count U == some 4
#guard nullary_tests_refused

/-! ## Exponent laws -/

/-- **The sum law needs disjoint data.** A and B share `a = 2`, so A ∪ B has three tuples:
2^3 = 8 candidates, not 2^2 · 2^2 = 16. -/
def sum_needs_disjoint : Bool :=
  count (.omegaSol (.nary .union [A, B]) X) == some 8 &&
    count (.omegaSol A X) == some 4 && count (.omegaSol B X) == some 4
#guard sum_needs_disjoint

/-- **Currying is not expressible inside solution sets**: ω_sol's decision must be a
relation, so ω_sol(A, ω_sol(A, X)) is refused. -/
def curry_not_expressible : Bool :=
  (count (.omegaSol A U)).isNone
#guard curry_not_expressible

/-! ## Multi solution sets -/

/-- ω_msol with no members is refused. -/
def omegaMsol_no_members : Bool :=
  (countDbs (.omegaMsol [] none)).isNone
#guard omegaMsol_no_members

/-- ω_msol refuses two members with the same name, as the Racket implementation does: a
candidate would name the member twice, and not be a database. -/
def omegaMsol_duplicate_names : Bool :=
  (countDbs (.omegaMsol [("V", U), ("V", U)] none)).isNone
#guard omegaMsol_duplicate_names

/-! ## The boundary -/

/-- The tuples of a sequence, or none if it is refused. -/
def tuples (e : Expr) : Option (List Tuple) :=
  match Expr.eval [] [] e with
  | .ok (.tseq _ ts) => some (ts.map (·.1))
  | _ => none

/-- **The prefix law** on a program: ℰ₁ gives the first item of ℰ₂ (key `a`, descending). -/
def enum_prefix_example : Bool :=
  match tuples (.enum (.int 1) (some (.desc, .attr "a")) A),
      tuples (.enum (.int 2) (some (.desc, .attr "a")) A) with
  | some ts, some ts' => ts == ts'.take 1 && ts.length == 1
  | _, _ => false
#guard enum_prefix_example

/-- ℰ with count 0 gives nothing. -/
def enum_zero : Bool :=
  tuples (.enum (.int 0) none A) == some []
#guard enum_zero

/-- **flatten and flatten_msol treat a rank attribute alike.** Each refuses a rank attribute
that the solution set, or a member, already has, as the Racket implementation does. -/
def flatten_rank_clash : Bool :=
  !ok? (Expr.eval [] [] (.flatten (some "a") (.enumSol (.int 10) none U))) &&
    !ok? (Expr.eval [] [] (.flattenMsol (some "a")
      (.enumMsol (.int 10) none (.omegaMsol [("V", U)] none))))
#guard flatten_rank_clash

end Rasso.SolLaws.Examples
