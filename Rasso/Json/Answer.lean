import Rasso.Eval
import Rasso.Json.Surface

/-!
# Rasso: answers, in the Racket implementation's answer format

A statement's value written as the Racket implementation's conformance services write an
answer (`rasso-answer-1`, rasso-racket's `docs-site/public/schema/`), so that its
`ast answer DOC YOURS` can judge it:

* a finite relation, and an unrestricted relation that can be listed:
  `{"relation": omega[h](rows)}`;
* a sequence of tuples: `{"tuples": omega[h](rows)}`, in its order;
* a solution set: `{"candidates": {"heading": h, "of": [literal, …]}}`, and a sequence of
  candidates, `{"candidate_sequence": …}`, in its order;
* a multi solution set: `{"databases": {"members": [{"name", "heading"}, …], "of": [db, …]}}`,
  each database a list of `{"member": {"name", "expr": literal}}`; a sequence of
  databases, `{"database_sequence": …}`, in its order; and a database, as one database.

A heading's columns are written in their own order, and a set domain's values without
repeats in Racket's value order (`racketSetValues`), as rassoAST requires.

`answersOf` answers each statement of a program in order, and stops after the first that
has no answer: `{"refused": message}` when the evaluator refuses it, and
`{"not-implemented": message, "cause": c}` when the cause is a limit of this evaluator
rather than the program: an unrestricted relation it can't list (`not listed`), a
statement that holds `lateral`, which it doesn't evaluate (`lateral`), and a refusal that
says it is not evaluated yet (`not yet`: `limitMessages`).
-/

namespace Rasso.Json
open Rasso

private def domainExpr : Domain → DomExpr
  | .kind k => .kind k
  | .range lo hi => .range lo hi
  | .set vs => .set (racketSetValues vs)

/-- A heading as rassoAST columns. -/
def answerHeading (h : Heading) : P J := pHeading (h.map fun (a, d) => (a, domainExpr d))

/-- A literal `omega[h](rows)`, each row's values in the heading's order. -/
def answerLiteral (h : Heading) (ts : List Tuple) : P J := do
  let rows ← ts.mapM fun t => do
    return J.arr (← h.attrs.mapM fun a => match t.get? a with
      | some v => pValue v
      | none => refuseP s!"a tuple has no value for {a}")
  return node "omega" (record [("heading", ← answerHeading h), ("rows", .arr rows)])

private def candidatesJ (h : Heading) (rs : List Finrel) : P J := do
  return record [("heading", ← answerHeading h),
    ("of", .arr (← rs.mapM fun r => answerLiteral r.heading r.tuples))]

private def databaseJ (db : Db) : P J := do
  return .arr (← db.mapM fun (n, r) => do
    return node "member" (record [("name", .str n), ("expr", ← answerLiteral r.heading r.tuples)]))

private def databasesJ (members : List (String × Heading)) (dbs : List Db) : P J := do
  return record [
    ("members", .arr (← members.mapM fun (n, h) => do
      return record [("name", .str n), ("heading", ← answerHeading h)])),
    ("of", .arr (← dbs.mapM databaseJ))]

/-- A value's answer; `.error` when it can't be listed. -/
def answerOf : Val → P J
  | .finrel r => do return node "relation" (← answerLiteral r.heading r.tuples)
  | .unrel u => do
    let ts ← match u.tuples with
      | .ok ts => pure ts
      | .error e => throw e
    return node "relation" (← answerLiteral u.heading ts)
  | .tseq h ts => do return node "tuples" (← answerLiteral h (ts.map (·.1)))
  | .sol s => do return node "candidates" (← candidatesJ s.heading s.candidates)
  | .cseq h rs => do return node "candidate_sequence" (← candidatesJ h (rs.map (·.1)))
  | .msol m => do return node "databases" (← databasesJ m.members m.candidates)
  | .dbseq ms dbs => do return node "database_sequence" (← databasesJ ms (dbs.map (·.1)))
  | .db d => do return node "databases" (← databasesJ (d.map fun (n, r) => (n, r.heading)) [d])

mutual
/-- Whether an expression holds `lateral` anywhere. -/
partial def exprHoldsLateral : Expr → Bool
  | .nary .lateral _ => true
  | .nary _ es => es.any exprHoldsLateral
  | .name _ | .omega _ | .omegaWhere .. | .omegaRows .. => false
  | .select _ e | .project _ e | .rename _ e | .gamma _ _ _ e | .extend _ _ e
  | .enum _ _ e | .flattenMsol _ e | .dbRef _ e | .flatten _ e | .forget e | .lift e => exprHoldsLateral e
  | .omegaSol d e => exprHoldsLateral d || exprHoldsLateral e
  | .sigmaSol c e | .sigmaMsol c e => condHoldsLateral c || exprHoldsLateral e
  | .enumSol _ k e | .enumMsol _ k e => (k.map (exprHoldsLateral ·.2)).getD false || exprHoldsLateral e
  | .omegaMsol ms c => ms.any (exprHoldsLateral ·.2) || (c.map condHoldsLateral).getD false

/-- Whether a condition holds `lateral` anywhere. -/
partial def condHoldsLateral : Cond → Bool
  | .and cs | .or cs => cs.any condHoldsLateral
  | .not c => condHoldsLateral c
  | .hasSubset e | .expr e => exprHoldsLateral e
end

/-- The refusals that say they are a limit of this evaluator: `lateral` (`Expr.eval`). -/
def limitMessages : List String :=
  ["lateral is not evaluated yet"]

/-- Whether a refusal is one of `limitMessages`. -/
def limitWords (msg : String) : Bool :=
  limitMessages.any fun m => (msg.splitOn m).length > 1

/-- A limit of this evaluator: `{"not-implemented": message, "cause": cause}`. -/
def limit (cause msg : String) : J := record [("not-implemented", .str msg), ("cause", .str cause)]

/-- Each statement's answer, in order, stopping after the first with none. -/
def answersOf (prog : Program) : J := Id.run do
  let mut env : Env := []
  let mut out : List J := []
  for (n, f) in prog do
    match f.eval env.reverse [] with
    | .ok v =>
      env := env ++ [(n, v)]
      match answerOf v with
      | .ok a => out := out ++ [.arr [.str n, node "answer" a]]
      | .error e => out := out ++ [.arr [.str n, limit "not listed" e]]; break
    | .error e =>
      let r := if exprHoldsLateral f then limit "lateral" e
        else if limitWords e then limit "not yet" e
        else node "refused" (.str e)
      out := out ++ [.arr [.str n, r]]; break
  return .arr out

end Rasso.Json
