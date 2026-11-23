import Rasso.Eval

/-!
# Function spaces, not powersets: the "+1 attribute" on Rasso's solution sets

`Rasso/FunctionSpace.lean` states the facts for plain Lean types. This file checks the
counts on Rasso's own solution sets, by evaluating `ω_sol` with `Expr.eval` and counting
its candidates. Blueprint chapter "Why function spaces".

Data `A` has three tuples (`a ∈ 1..3`); `X` is a two-valued decision (`x ∈ 1..2`).

| Solution set | What it is | Candidates |
| --- | --- | --- |
| ω_sol(A, X) | functions A → X | 2^3 = 8 |
| ω_sol(A, S), `s : bool` | subsets of A (subset selection) | 2^3 = 8 |
| ω_sol(A ⋈ X, S) | relations R ⊆ A × X (the +1 attribute) | 2^6 = 64 |
| ω_sol(A, M), `m ∈ 0..2` | multisets over A, multiplicity ≤ 2 | 3^3 = 27 |
| ω_sol(A ⋈ X, M) | multisets over A × X, multiplicity ≤ 2 | 3^6 = 729 |

The relation and multiset rows have the old decision attribute `x` in the data, and one
new decision attribute (`s` or `m`). That is the move `FunctionSpace.psetIso` makes. It
needs `X` to be finite, because data is.
-/

namespace Rasso.FunctionSpaceExamples

open Rasso

def A : Expr := .omegaRows [("a", .range 1 3)] [[.int 1], [.int 2], [.int 3]]
def Xdata : Expr := .omegaRows [("x", .range 1 2)] [[.int 1], [.int 2]]
def X : Expr := .omega [("x", .range 1 2)]
def S : Expr := .omega [("s", .kind .bool)]
def M : Expr := .omega [("m", .range 0 2)]
def AX : Expr := .nary .join [A, Xdata]

/-- The number of candidates of `ω_sol(data, decision)`, or none if it is refused. -/
def count (data decision : Expr) : Option Nat :=
  match Expr.eval [] [] (.omegaSol data decision) with
  | .ok (.sol s) => some s.candidates.length
  | _ => none

#guard count A X == some 8      -- functions A → X
#guard count A S == some 8      -- subsets of A
#guard count AX S == some 64    -- relations R ⊆ A × X
#guard count A M == some 27     -- multisets over A, multiplicity ≤ 2
#guard count AX M == some 729   -- multisets over A × X, multiplicity ≤ 2

end Rasso.FunctionSpaceExamples
