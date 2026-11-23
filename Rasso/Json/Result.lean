import Rasso.Eval
import Rasso.Json.Text

/-!
# Rasso: results as JSON

A program's values written as JSON (`rasso-lean PROGRAM.json`), in the form the examples'
expected answers use: a relation
or a sequence of tuples as `{"columns": [...], "rows": [[...], ...]}`, as the Racket
implementation's expected answers have them. A value is written as JSON's own (an int or a
float as a number, a symbol or a string as a string, a Boolean as itself).
-/

namespace Rasso.Json
open Rasso

def resultValue : Value → J
  | .bool b => .bool b
  | .int n => .int n
  | .float d => .float d
  | .symbol s => .str s
  | .string s => .str s
  | .rat q _ => .obj [("rat", .obj [("num", .int q.num), ("den", .int q.den)])]

def rowsJ (h : Heading) (ts : List Tuple) : J :=
  .obj [("columns", .arr (h.map fun p => J.str p.1)),
        ("rows", .arr (ts.map fun t => .arr (h.map fun p => ((t.get? p.1).map resultValue).getD (.str ""))))]

/-- A finite relation, its rows shown in value order column by column (display only: the
relation has no order). -/
def relJ (r : Finrel) : J :=
  let row (t : Tuple) := r.heading.map fun p => (t.get? p.1).getD default
  let dirs := r.heading.map fun _ => Order.asc
  rowsJ r.heading (r.tuples.mergeSort fun t u => cmpKeys dirs (row t) (row u) != .gt)

def dbJ (db : Db) : J := .obj (db.map fun (n, r) => (n, relJ r))

def keysJ (ks : List Value) : J := .arr (ks.map resultValue)

def columnsJ (h : Heading) : J := .arr (h.map fun p => J.str p.1)

def valJ : Val → J
  | .finrel r => relJ r
  | .unrel u => .obj [("relation", columnsJ u.heading)]
  | .tseq h ts => rowsJ h (ts.map (·.1))
  | .sol s => .obj [("solution_set", .obj [("columns", columnsJ s.heading), ("candidates", .int s.candidates.length)])]
  | .cseq _ rs => .arr (rs.map fun (r, ks) => .obj [("keys", keysJ ks), ("relation", relJ r)])
  | .msol m => .obj [("multi_solution_set", .obj
      [("members", .arr (m.members.map fun p => J.str p.1)), ("candidates", .int m.candidates.length)])]
  | .dbseq _ dbs => .arr (dbs.map fun (db, ks) => .obj [("keys", keysJ ks), ("database", dbJ db)])
  | .db db => dbJ db

/-- Every definition's value, in program order. -/
def envJ (env : Env) : J := .obj (env.map fun (n, v) => (n, valJ v))

end Rasso.Json
