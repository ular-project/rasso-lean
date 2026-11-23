import Rasso.Phi.Phi
import Rasso.Phi.Fragment
import Rasso.Json.Answer

/-!
# φ's answer, in the Racket implementation's Φ record

A solution set's φ written as the Racket implementation's conformance services read a
consumer's Φ (`ast phi DOC YOURS`, rasso-racket's `rasso/answers.rkt`):

    {"flat": omega[cells](where term), "symbolic_candidate": omega[heading](rows)}

The flat relation is `omega` over the cells with φ's term. The symbolic candidate is a
literal over the solution set's heading, one row for each Data tuple; each Decision
attribute is typed `symbol` and holds its cell's name. Racket pairs the cells with its own
by Data tuple, so the cells' names don't have to match its own.

`phiAnswersOf` gives φ of each solution-set statement of a program, in order, stopping, as
`Rasso.Json.answersOf` does, at the evaluator's first refusal. Each entry is
`[k, name, R]`, `k` the statement's index among the program's statements and `R` one of

* `{"phi": record}`;
* `{"refused": message}`, φ's refusal;
* `{"not-implemented": message, "cause": c}`, a limit of this φ rather than the program:
  a statement outside φ's fragment (`outside the fragment`); a refusal that says it is not
  implemented yet (`not yet`); a flat term with a conditional, which rassoAST has no form
  for (`conditional`); and a float, or a Data value whose printed form φ doesn't check
  (`float or printed form`).
-/

namespace Rasso.Phi
open Rasso Rasso.Json

/-- The flat relation `omega[cells](where term)`. -/
def flatJ (F : Flat) : P J := do
  return node "omega" (record [("heading", ← answerHeading F.cells), ("where", ← pTerm F.term)])

/-- The symbolic candidate: each Decision attribute typed `symbol`, holding its cell's
name. -/
def symbolicJ (F : Flat) : P J := do
  let dec := F.decision.attrs
  let h : Heading := F.heading.map fun (a, d) => if dec.contains a then (a, .kind .symbol) else (a, d)
  let rows ← F.symI.mapM fun row => do
    return J.arr (← F.heading.mapM fun (a, _) => do
      match row.lookup a with
      | some (.attr c) => pValue (.symbol c)
      | some (.val v) => pValue v
      | _ => refuseP s!"the symbolic candidate holds a term for {a}")
  return node "omega" (record [("heading", ← answerHeading h), ("rows", .arr rows)])

/-- φ as the services' record. -/
def phiRecord (F : Flat) : P J := do
  return record [("flat", ← flatJ F), ("symbolic_candidate", ← symbolicJ F)]

/-- The printer's refusal of a conditional term. -/
def conditionalMessage : String := "if is not an operator of terms"

/-- φ's refusals that are a limit of this φ, each with its cause. -/
def phiLimitMessages : List (String × String) :=
  [("is not yet implemented", "not yet"),
   ("floats are not in φ's first version", "float or printed form"),
   ("a float, or a printed form not checked", "float or printed form"),
   ("is not finite, or holds a float", "float or printed form")]

private def contains (msg part : String) : Bool := (msg.splitOn part).length > 1

/-- φ of statement `k`, as an answer. -/
def phiAnswer (p : Program) (k : Nat) : J :=
  match statementChain p k with
  | none => limit "outside the fragment" "φ: this statement is not in φ's fragment"
  | some _ => match phi p k with
    | .error e => match phiLimitMessages.find? (contains e ·.1) with
      | some (_, cause) => limit cause e
      | none => node "refused" (.str e)
    | .ok F => match phiRecord F with
      | .ok j => node "phi" j
      | .error e => if contains e conditionalMessage then limit "conditional" e
        else node "refused" (.str s!"φ's record could not be written: {e}")

/-- φ of each solution-set statement, in order, stopping at the evaluator's first
refusal. -/
def phiAnswersOf (prog : Program) : J := Id.run do
  let mut env : Env := []
  let mut out : List J := []
  let mut k : Nat := 0
  for (n, f) in prog do
    match f.eval env.reverse [] with
    | .ok v =>
      env := env ++ [(n, v)]
      if let .sol _ := v then
        out := out ++ [.arr [.int (Int.ofNat k), .str n, phiAnswer prog k]]
    | .error _ => break
    k := k + 1
  return .arr out

end Rasso.Phi
