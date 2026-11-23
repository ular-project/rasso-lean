import Rasso.Form
import Rasso.Json.Text

/-!
# Rasso: the JSON surface (rassoAST)

Programs (`Rasso.Form`) to rassoAST documents and back, a port of the Racket
implementation's reader and printer of rassoAST. A program is a document,
`{"rasso": "1", "program": [item, …]}`; its items are statements, comment lines, blank
lines and pragmas, and inside a statement any value may stand wrapped in a `commented`.
Held to the Racket implementation's invariants:

* **I1, the round trip:** `parseProgram (printProgram p) = p` for every program.
* **I3, only programs come back:** a document is read, or refused, naming the place: a
  path such as `$.program[0].define.expr.sigma.where.int` where the JSON is wrong, the
  statement where it is well formed but not a form.
* **I4, one layout:** a document's printed text, read and printed again, is itself
  (`readDocument`, `Document.print`). The layout is Racket's printer's; the Racket
  implementation promises a document's JSON value, not its layout.

Checked against a corpus written by the Racket implementation's conformance services
(`tests/json-corpus/`; checked when the release is built, and not part of it): every
document Racket reads, Rasso reads and prints as the same JSON value, in a layout that
prints back to itself; every document and JSON text Racket refuses, Rasso refuses, at
Racket's place or, for a document, below it. Against the Racket implementation as it is
now, through the same services.

No duck typing: where a position can hold more than one kind of thing, the thing is a
node, an object with one key naming its kind. A JSON scalar stands bare only where one
kind of scalar can (a statement's name, an attribute in `as`, `by` or `attrs`, a call's
`op`, an order, a range's ends, a database's relation name).
-/

namespace Rasso.Json
open Rasso

/-! ## Printing -/

def node (k : String) (v : J) : J := .obj [(k, v)]
def record (kvs : List (String × J)) : J := .obj kvs

abbrev P := Except String

def refuseP {α : Type} (msg : String) : P α := throw s!"json-print: {msg}"

def pName (s : String) : P J := match nameProblem s with
  | some m => refuseP m
  | none => return .str s

def pValue : Value → P J
  | .int n => return node "int" (.int n)
  | .float d => return node "float" (.float d)
  | .string s => return node "string" (.str s)
  | .symbol s => match symbolProblem s with
    | some m => refuseP m
    | none => return node "symbol" (.str s)
  | .bool b => return node "bool" (.bool b)
  | .rat q _ => return node "rat" (record [("num", .int q.num), ("den", .int q.den)])

def Kind.ofName : String → Option Kind
  | "int" => some .int | "float" => some .float | "string" => some .string
  | "symbol" => some .symbol | "bool" => some .bool | "rat" => some .rat | _ => none

def pCount : Count → J
  | .all => node "all" (.obj [])
  | .int k => node "int" (.int k)

def pOrder : Order → J
  | .asc => .str "asc"
  | .desc => .str "desc"

def pRank : Option String → P J
  | none => return node "none" (.obj [])
  | some a => do return node "attr" (← pName a)

def pCall (op : String) (args : List J) (n : Nat) : P J := do
  unless termNames.contains op do refuseP s!"{op} is not an operator of terms"
  if let some m := callProblem op n then refuseP m
  return node "call" (record [("op", .str op), ("args", .arr args)])

mutual
partial def pExpr : Expr → P J
  | .name n => do return node "name" (← pName n)
  | .omega h => do return form "omega" [("heading", ← pHeading h)]
  | .omegaWhere h t => do return form "omega" [("heading", ← pHeading h), ("where", ← pTerm t)]
  | .omegaRows h rows => do
    return form "omega" [("heading", ← pHeading h),
      ("rows", .arr (← rows.mapM fun r => do return .arr (← r.mapM pValue)))]
  | .select t r => do return form "sigma" [("where", ← pTerm t), ("of", ← pExpr r)]
  | .project as r => do return form "pi" [("attrs", .arr (← as.mapM pName)), ("of", ← pExpr r)]
  | .rename ren r => do
    let ps ← ren.mapM fun (a, b) => do
      return node "rename" (record [("from", ← pName a), ("to", ← pName b)])
    return form "rho" [("renaming", .arr ps), ("of", ← pExpr r)]
  | .nary op rs => do return form op.name [("operands", .arr (← rs.mapM pExpr))]
  | .gamma by_ x res r => do
    let b ← by_.mapM pName
    match res with
    | some a => return form "gamma" [("by", .arr b), ("aggregate", ← pAgg x), ("as", ← pName a), ("of", ← pExpr r)]
    | none => return form "gamma" [("by", .arr b), ("aggregate", ← pAgg x), ("of", ← pExpr r)]
  | .extend a t r => do return form "extend" [("as", ← pName a), ("term", ← pTerm t), ("of", ← pExpr r)]
  | .enum c none r => do return form "enum" [("count", pCount c), ("of", ← pExpr r)]
  | .enum c (some (o, k)) r => do
    return form "enum" [("count", pCount c), ("order", pOrder o), ("key", ← pTerm k), ("of", ← pExpr r)]
  | .omegaSol a b => do return form "omega_sol" [("data", ← pExpr a), ("decision", ← pExpr b)]
  | .sigmaSol c r => do return form "sigma_sol" [("condition", ← pCond c), ("of", ← pExpr r)]
  | .enumSol c none r => do return form "enum_sol" [("count", pCount c), ("of", ← pExpr r)]
  | .enumSol c (some (o, k)) r => do
    return form "enum_sol" [("count", pCount c), ("order", pOrder o), ("key", ← pExpr k), ("of", ← pExpr r)]
  | .omegaMsol ms c => do
    let m ← ms.mapM fun (n, e) => do
      return node "member" (record [("name", ← pName n), ("expr", ← pExpr e)])
    match c with
    | none => return form "omega_msol" [("members", .arr m)]
    | some c => return form "omega_msol" [("members", .arr m), ("condition", ← pCond c)]
  | .sigmaMsol c r => do return form "sigma_msol" [("condition", ← pCond c), ("of", ← pExpr r)]
  | .enumMsol c none r => do return form "enum_msol" [("count", pCount c), ("of", ← pExpr r)]
  | .enumMsol c (some (o, k)) r => do
    return form "enum_msol" [("count", pCount c), ("order", pOrder o), ("key", ← pExpr k), ("of", ← pExpr r)]
  | .flattenMsol k r => do return form "flatten_msol" [("rank", ← pRank k), ("of", ← pExpr r)]
  | .dbRef n r => do return form "db_ref" [("relation", ← pName n), ("of", ← pExpr r)]
  | .flatten k r => do return form "flatten" [("rank", ← pRank k), ("of", ← pExpr r)]
  | .forget r => do return form "forget" [("of", ← pExpr r)]
  | .lift r => do return form "lift" [("of", ← pExpr r)]

partial def form (name : String) (fields : List (String × J)) : J := node name (record fields)

partial def pHeading (h : List (String × DomExpr)) : P J := do
  return .arr (← h.mapM fun (a, d) => do
    return node "column" (record [("attr", ← pName a), ("domain", ← pDomExpr d)]))

partial def pDomExpr : DomExpr → P J
  | .kind k => return node "type" (.str k.name)
  | .range lo hi => return node "range" (record [("lo", .int lo), ("hi", .int hi)])
  | .set vs => do return node "set" (.arr (← vs.mapM pValue))
  | .in_ r => do return node "in" (← pExpr r)

partial def pTerm : Term → P J
  | .attr a => do return node "attr" (← pName a)
  | .val v => pValue v
  | .call op args => do pCall op (← args.mapM pTerm) args.length

partial def pAgg : Agg → P J
  | .hasSubset r => do return node "has_subset" (← pExpr r)
  | .agg op t => do return node "agg" (record [("op", .str op), ("of", ← pTerm t)])
  | .attr a => do return node "attr" (← pName a)
  | .val v => pValue v
  | .call op args => do pCall op (← args.mapM pAgg) args.length

partial def pCond : Cond → P J
  | .and cs => do
    if cs.length < 2 then refuseP s!"and takes two or more conditions, not {cs.length}"
    return node "and" (.arr (← cs.mapM pCond))
  | .or cs => do
    if cs.length < 2 then refuseP s!"or takes two or more conditions, not {cs.length}"
    return node "or" (.arr (← cs.mapM pCond))
  | .not c => do return node "not" (← pCond c)
  | .hasSubset r => do return node "has_subset" (← pExpr r)
  | .expr r => pExpr r
end

/-- One form as JSON text, in rassoAST's layout. Lean-only, as `parseForm` is: Racket has
no single-form printer any more. -/
def printForm (f : Expr) : P String := do
  if let .name _ := f then refuseP "not a form: a name alone"
  if let some p := f.problem then refuseP s!"not a form: {p}"
  return (← pExpr f).textAst

/-! ## Parsing -/

inductive Seg where
  | i (n : Nat)
  | k (s : String)

abbrev Path := List Seg

def pathText (p : Path) : String :=
  "$" ++ String.join (p.reverse.map fun | .i n => s!"[{n}]" | .k s => s!".{s}")

def refuse {α : Type} (p : Path) (msg : String) : P α := throw s!"json-parse: at {pathText p}: {msg}"

/-- A string as Racket's `~s` writes it. -/
def rs (s : String) : String := reprStr s

def show_ : J → String
  | .obj [] => "an object with no key"
  | .obj ps => "an object with " ++ ", ".intercalate (ps.map fun p => rs p.1)
  | .arr _ => "an array"
  | .str s => s!"the string {rs s}"
  | .bool b => if b then "#t" else "#f"
  | .int n => s!"the number {n}"
  | .float d => s!"the number {d.toRacket}"

def fieldsOf (t : J) (p : Path) (names : List String) (what : String) : P (List J) :=
  match t with
  | .obj ps => do
    let keys := ps.map (·.1)
    let missing := names.filter fun f => !keys.contains f
    let unknown := keys.filter fun k => !names.contains k
    unless missing.isEmpty && unknown.isEmpty do
      refuse p s!"{what} has the fields {", ".intercalate names}{if missing.isEmpty then "" else s!"; {", ".intercalate missing} missing"}{if unknown.isEmpty then "" else s!"; {", ".intercalate unknown} unknown"}"
    return names.map fun f => (ps.lookup f).getD default
  | _ => refuse p s!"{what} is a record, an object of the fields {", ".intercalate names}, not {show_ t}"

def arrayOf (t : J) (p : Path) (what : String) : P (List J) := match t with
  | .arr xs => return xs
  | _ => refuse p s!"{what} is an array, not {show_ t}"

def stringOf (t : J) (p : Path) (what : String) : P String := match t with
  | .str s => return s
  | _ => refuse p s!"{what} is a string, not {show_ t}"

def nodeOf (t : J) (p : Path) (allowed : List String) (what : String) : P (String × J) :=
  match t with
  | .obj [(k, v)] =>
    if allowed.contains k then return (k, v)
    else refuse p s!"{what} takes {", ".intercalate (allowed.map fun a => "{" ++ rs a ++ ": …}")}, not \{{rs k}: …}"
  | _ => refuse p s!"{what} is a node, an object with one key naming its kind ({", ".intercalate allowed}), not {show_ t}"

/-! ### Comments inside a statement (rassoAST's `commented`)

`{"commented": {"comments": [" text", …], "value": v}}` stands where `v` may, holding the
comments written just before `v`. Rasso reads it as `v` and drops the comments (the
checked document keeps them, so it prints back as itself). Where one may stand is
Racket's `lower`: any place read through `unwrap` here (a relation, a
term, an aggregate, a condition, a domain, a count, a rank but not its `none`, and each
element of an array); never a bare field (a name, an `as`, an op, an order), never the
first operand of an infix value (`noCommentedFirst`), never an item or a pragma's part
(`plainNodeOf`). -/

def isCommented : J → Bool
  | .obj [("commented", _)] => true
  | _ => false

/-- A comment's text: one line; on a line of its own, or before a value, not starting
with `#` (on a line of its own, a pragma). -/
def commentText (t : J) (p : Path) (what : String) (ownLine : Bool := true) : P String := do
  let s ← stringOf t p what
  if s.any (fun c => c == '\n' || c == '\r') then refuse p s!"{what} is one line, not {rs s}"
  if ownLine && s.startsWith "#" then
    refuse p s!"{what} doesn't start with #, which on a line of its own is a pragma: {rs s}"
  return s

/-- A place a `commented` may stand: its value and the value's place, and whether it was
wrapped (Racket's `unwrap`). -/
def unwrap (t : J) (p : Path) : P (J × Path × Bool) := do
  match t with
  | .obj [("commented", c)] =>
    let q := .k "commented" :: p
    let cv ← fieldsOf c q ["comments", "value"] "commented"
    let texts ← arrayOf cv[0]! (.k "comments" :: q) "commented's comments"
    if texts.isEmpty then refuse (.k "comments" :: q) "commented holds at least one comment"
    for (x, i) in texts.zipIdx do
      let _ ← commentText x (.i i :: .k "comments" :: q) "a comment"
    if isCommented cv[1]! then
      refuse (.k "value" :: q) "commented doesn't wrap another commented: put its comments together"
    return (cv[1]!, .k "value" :: q, true)
  | _ => return (t, p, false)

/-- The first operand of an infix value starts where the value does, so a comment before
it is the value's own (Racket's `no-commented-first`). -/
def noCommentedFirst (t : J) (p : Path) (what : String) : P Unit :=
  match t with
  | .arr (x :: _) =>
    if isCommented x then
      refuse (.i 0 :: p) s!"{what}'s first operand starts where it does, so a comment before it is {what}'s own: wrap {what}, not its first operand"
    else pure ()
  | _ => pure ()

/-- A node that holds no comment: an item of a program, and a pragma's parts. -/
def plainNodeOf (t : J) (p : Path) (allowed : List String) (what : String) : P (String × J) := do
  if isCommented t then
    refuse p s!"{what} holds no commented: a comment between statements is a comment line"
  nodeOf t p allowed what

/-- An array's elements, each maybe commented. -/
def each {α : Type} (t : J) (p : Path) (what : String) (f : J → Path → P α) : P (List α) := do
  let xs ← arrayOf t p what
  (xs.zipIdx).mapM fun (x, i) => do
    let (x, q, _) ← unwrap x (.i i :: p)
    f x q

def attrOf (t : J) (p : Path) (what : String := "an attribute") : P String := do
  let s ← stringOf t p what
  unless isAttribute s do
    refuse p s!"{rs s} is not an attribute's name: letters, digits and _, not starting with a digit"
  if let some m := nameProblem s then refuse p m
  return s

def valueKinds : List String := ["int", "rat", "float", "string", "symbol", "bool"]

def valueOf (k : String) (v : J) (p : Path) : P Value := match k, v with
  | "int", .int n => return .int n
  | "int", _ => refuse (.k k :: p) s!"an int is a JSON integer, not {show_ v}"
  | "float", .int n => return .float (Decimal.normalize ⟨n < 0, n.natAbs, 0⟩)
  | "float", .float d => return .float d
  | "float", _ => refuse (.k k :: p) s!"a float is a JSON number, not {show_ v}"
  | "string", _ => do return .string (← stringOf v (.k k :: p) "a string value")
  | "symbol", _ => do
    let s ← stringOf v (.k k :: p) "a symbol value"
    if let some m := symbolProblem s then refuse (.k k :: p) m
    return .symbol s
  | "bool", .bool b => return .bool b
  | "rat", _ => do
    -- `{"rat": {"num": n, "den": d}}`, read with `Rat.divInt`: lowest terms, a positive
    -- denominator, `den = 0` gives 0 as in Lean, and a whole number
    -- is the int.
    -- Each of num and den is refused at its own place, as Racket refuses it.
    let nd ← fieldsOf v (.k k :: p) ["num", "den"] "a rat"
    let int_ (x : J) (f : String) : P Int := match x with
      | .int i => pure i
      | _ => refuse (.k f :: .k k :: p) s!"a rat's {f} is a JSON integer, not {show_ x}"
    let n ← int_ nd[0]! "num"
    let d ← int_ nd[1]! "den"
    return Value.ofRat (Rat.divInt n d)
  | _, _ => refuse (.k k :: p) s!"a bool is true or false, not {show_ v}"

def value (t : J) (p : Path) : P Value := do
  let (k, v) ← nodeOf t p valueKinds "a value"
  valueOf k v p

/-- Each form's name and its shapes' fields, in Racket's `form-table` order. -/
def formTable : List (String × List (List String)) :=
  [("omega", [["heading"], ["heading", "where"], ["heading", "rows"]]),
   ("sigma", [["where", "of"]]), ("pi", [["attrs", "of"]]), ("rho", [["renaming", "of"]]),
   ("join", [["operands"]]), ("cross", [["operands"]]), ("lateral", [["operands"]]),
   ("union", [["operands"]]), ("intersect", [["operands"]]), ("except", [["operands"]]),
   ("gamma", [["by", "aggregate", "as", "of"], ["by", "aggregate", "of"]]),
   ("extend", [["as", "term", "of"]]),
   ("enum", [["count", "of"], ["count", "order", "key", "of"]]),
   ("omega_sol", [["data", "decision"]]), ("sigma_sol", [["condition", "of"]]),
   ("enum_sol", [["count", "of"], ["count", "order", "key", "of"]]),
   ("omega_msol", [["members"], ["members", "condition"]]),
   ("sigma_msol", [["condition", "of"]]),
   ("enum_msol", [["count", "of"], ["count", "order", "key", "of"]]),
   ("flatten_msol", [["rank", "of"]]), ("db_ref", [["relation", "of"]]),
   ("flatten", [["rank", "of"]]), ("forget", [["of"]]), ("lift", [["of"]])]

def sortStrings (l : List String) : List String := l.mergeSort (fun a b => decide (a ≤ b))

def exprKinds : List String := sortStrings ("name" :: formTable.map (·.1))

/-- The calls written between their operands (Racket's `infix-ops`, as JSON spells them). -/
def infixOps : List String := ["=", "<", ">", "<=", ">=", "+", "*", "/", "%", "and", "or"]

def termKinds : List String := valueKinds ++ ["attr", "call"]

def count (t : J) (p : Path) : P Count := do
  let (t, p, _) ← unwrap t p
  let (k, v) ← nodeOf t p ["all", "int"] "a count"
  if k == "all" then let _ ← fieldsOf v (.k k :: p) [] "all"; return .all
  match ← valueOf k v p with
  | .int n => return .int n
  | _ => refuse p "not a count"

def order (t : J) (p : Path) : P Order := do
  match ← stringOf t p "an order" with
  | "asc" => return .asc
  | "desc" => return .desc
  | o => refuse p s!"an order is \"asc\" or \"desc\", not {rs o}"

def rank (t : J) (p : Path) : P (Option String) := do
  let (t, p, wrapped) ← unwrap t p
  let (k, v) ← nodeOf t p ["none", "attr"] "a rank"
  if wrapped && k == "none" then refuse p "a rank of none is written as nothing, so it can't hold a comment"
  if k == "none" then let _ ← fieldsOf v (.k k :: p) [] "none"; return none
  return some (← attrOf v (.k k :: p))

def relname (t : J) (p : Path) : P String := do
  let n ← stringOf t p "a relation's name"
  unless isAttribute n do refuse p s!"{rs n} is not a relation's name"
  if let some m := nameProblem n then refuse p m
  return n

mutual
partial def expr (t : J) (p : Path) : P Expr := do
  let (t, p, _) ← unwrap t p
  let (k, v) ← nodeOf t p exprKinds "an expression"
  if k == "name" then return .name (← attrOf v (.k k :: p) "a statement's name")
  formOf k v (.k k :: p)

partial def formOf (name : String) (t : J) (p : Path) : P Expr := do
  let shapes := (formTable.lookup name).getD []
  let keys := match t with
    | .obj ps => ps.map (·.1)
    | _ => []
  let shape ← match shapes.find? (fun s => sortStrings s == sortStrings keys), t with
    | some s, _ => pure s
    | none, .obj _ =>
      refuse p s!"{name} takes the fields {"; or ".intercalate (shapes.map (", ".intercalate ·))}, not {if keys.isEmpty then "none" else ", ".intercalate keys}"
    | none, _ => refuse p s!"{name}'s payload is a record of its fields, not {show_ t}"
  let vs ← fieldsOf t p shape name
  let f (n : String) : J := ((shape.zip vs).lookup n).getD default
  let at_ (n : String) : Path := .k n :: p
  match name, shape with
  | "omega", ["heading"] => return .omega (← heading (f "heading") (at_ "heading"))
  | "omega", ["heading", "where"] =>
    return .omegaWhere (← heading (f "heading") (at_ "heading")) (← term (f "where") (at_ "where"))
  | "omega", ["heading", "rows"] =>
    return .omegaRows (← heading (f "heading") (at_ "heading"))
      (← each (f "rows") (at_ "rows") "rows" fun r q => each r q "a row" value)
  | "sigma", _ => return .select (← term (f "where") (at_ "where")) (← expr (f "of") (at_ "of"))
  | "pi", _ =>
    return .project (← each (f "attrs") (at_ "attrs") "attributes" fun a q => attrOf a q) (← expr (f "of") (at_ "of"))
  | "rho", _ =>
    let ren ← each (f "renaming") (at_ "renaming") "a renaming" fun r q => do
      let (_, v) ← nodeOf r q ["rename"] "a renaming's pair"
      let ab ← fieldsOf v (.k "rename" :: q) ["from", "to"] "a renaming's pair"
      return (← attrOf ab[0]! (.k "from" :: .k "rename" :: q), ← attrOf ab[1]! (.k "to" :: .k "rename" :: q))
    return .rename ren (← expr (f "of") (at_ "of"))
  | "gamma", _ =>
    let by_ ← each (f "by") (at_ "by") "attributes" fun a q => attrOf a q
    let x ← agg (f "aggregate") (at_ "aggregate")
    let res ← if shape.contains "as" then (some <$> attrOf (f "as") (at_ "as")) else pure none
    return .gamma by_ x res (← expr (f "of") (at_ "of"))
  | "extend", _ =>
    return .extend (← attrOf (f "as") (at_ "as")) (← term (f "term") (at_ "term")) (← expr (f "of") (at_ "of"))
  | "enum", _ =>
    let c ← count (f "count") (at_ "count")
    let k ← if shape.contains "key" then
        (do pure (some (← order (f "order") (at_ "order"), ← term (f "key") (at_ "key")))) else pure none
    return .enum c k (← expr (f "of") (at_ "of"))
  | "omega_sol", _ => return .omegaSol (← expr (f "data") (at_ "data")) (← expr (f "decision") (at_ "decision"))
  | "sigma_sol", _ => return .sigmaSol (← cond (f "condition") (at_ "condition")) (← expr (f "of") (at_ "of"))
  | "enum_sol", _ =>
    let c ← count (f "count") (at_ "count")
    let k ← if shape.contains "key" then
        (do pure (some (← order (f "order") (at_ "order"), ← expr (f "key") (at_ "key")))) else pure none
    return .enumSol c k (← expr (f "of") (at_ "of"))
  | "omega_msol", _ =>
    let ms ← each (f "members") (at_ "members") "members" fun m q => do
      let (_, v) ← nodeOf m q ["member"] "a member"
      let ne ← fieldsOf v (.k "member" :: q) ["name", "expr"] "a member"
      return (← attrOf ne[0]! (.k "name" :: .k "member" :: q) "a member's name",
              ← expr ne[1]! (.k "expr" :: .k "member" :: q))
    let c ← if shape.contains "condition" then (some <$> cond (f "condition") (at_ "condition")) else pure none
    return .omegaMsol ms c
  | "sigma_msol", _ => return .sigmaMsol (← cond (f "condition") (at_ "condition")) (← expr (f "of") (at_ "of"))
  | "enum_msol", _ =>
    let c ← count (f "count") (at_ "count")
    let k ← if shape.contains "key" then
        (do pure (some (← order (f "order") (at_ "order"), ← expr (f "key") (at_ "key")))) else pure none
    return .enumMsol c k (← expr (f "of") (at_ "of"))
  | "flatten_msol", _ => return .flattenMsol (← rank (f "rank") (at_ "rank")) (← expr (f "of") (at_ "of"))
  | "db_ref", _ => return .dbRef (← relname (f "relation") (at_ "relation")) (← expr (f "of") (at_ "of"))
  | "flatten", _ => return .flatten (← rank (f "rank") (at_ "rank")) (← expr (f "of") (at_ "of"))
  | "forget", _ => return .forget (← expr (f "of") (at_ "of"))
  | "lift", _ => return .lift (← expr (f "of") (at_ "of"))
  | _, ["operands"] =>
    let some op := NOp.all.find? (·.name == name) | refuse p s!"{name} is not an operator"
    let xs ← arrayOf (f "operands") (at_ "operands") s!"{name}'s operands"
    if xs.length < 2 then refuse (at_ "operands") s!"{name} takes two or more operands, not {xs.length}"
    -- every n-ary form (join cross lateral union intersect except) is infix
    noCommentedFirst (f "operands") (at_ "operands") name
    return .nary op (← (xs.zipIdx).mapM fun (x, i) => expr x (.i i :: at_ "operands"))
  | _, _ => refuse p s!"{name} is not an operator"

partial def heading (t : J) (p : Path) : P (List (String × DomExpr)) :=
  each t p "a heading" fun c q => do
    let (_, v) ← nodeOf c q ["column"] "a heading's column"
    let ad ← fieldsOf v (.k "column" :: q) ["attr", "domain"] "a column"
    return (← attrOf ad[0]! (.k "attr" :: .k "column" :: q), ← dom ad[1]! (.k "domain" :: .k "column" :: q))

partial def dom (t : J) (p : Path) : P DomExpr := do
  let (t, p, _) ← unwrap t p
  let (k, v) ← nodeOf t p ["type", "range", "set", "in"] "a domain"
  let q := .k k :: p
  match k with
  | "type" =>
    let s ← stringOf v q "a type"
    match Kind.ofName s with
    | some kd => return .kind kd
    | none => refuse q s!"a type is int, rat, float, string, symbol or bool, not {rs s}"
  | "range" =>
    let lh ← fieldsOf v q ["lo", "hi"] "a range"
    let end_ (x : J) (n : String) : P Int := match x with
      | .int i => return i
      | _ => refuse (.k n :: q) s!"a range's end is a JSON integer, not {show_ x}"
    let lo ← end_ lh[0]! "lo"
    let hi ← end_ lh[1]! "hi"
    return .range lo hi
  | "set" => return .set (← each v q "a set" value)
  | _ => return .in_ (← expr v q)

partial def call {α : Type} (v : J) (p : Path) (recur : J → Path → P α) : P (String × List α) := do
  let oa ← fieldsOf v p ["op", "args"] "a call"
  let s ← stringOf oa[0]! (.k "op" :: p) "a call's op"
  unless termNames.contains s do refuse (.k "op" :: p) s!"{rs s} is not an operator of terms"
  let xs ← each oa[1]! (.k "args" :: p) "a call's args" recur
  if let some m := callProblem s xs.length then refuse p m
  if infixOps.contains s || (s == "-" && xs.length ≥ 2) then noCommentedFirst oa[1]! (.k "args" :: p) s
  return (s, xs)

partial def term (t : J) (p : Path) : P Term := do
  let (t, p, _) ← unwrap t p
  let (k, v) ← nodeOf t p termKinds "a term"
  let q := .k k :: p
  if valueKinds.contains k then return .val (← valueOf k v p)
  match k with
  | "attr" => return .attr (← attrOf v q)
  | _ =>
    let (op, xs) ← call v q term
    unless termOperators.contains op do
      refuse (.k "op" :: q) s!"{op} is an aggregate, not an operator of terms"
    return .call op xs

partial def agg (t : J) (p : Path) : P Agg := do
  let (t, p, _) ← unwrap t p
  let (k, v) ← nodeOf t p (valueKinds ++ ["attr", "call", "agg", "has_subset"]) "an aggregate"
  let q := .k k :: p
  if valueKinds.contains k then return .val (← valueOf k v p)
  match k with
  | "attr" => return .attr (← attrOf v q)
  | "has_subset" => return .hasSubset (← expr v q)
  | "agg" =>
    let oo ← fieldsOf v q ["op", "of"] "an aggregate"
    let s ← stringOf oo[0]! (.k "op" :: q) "an aggregate's op"
    unless aggNames.contains s do refuse (.k "op" :: q) s!"{rs s} is not an aggregate"
    return .agg s (← term oo[1]! (.k "of" :: q))
  | _ =>
    let (op, xs) ← call v q agg
    if aggNames.contains op && xs.length == 1 then
      refuse q s!"{op} over one operand is the aggregate: write it \{\"agg\": \{\"op\": {rs op}, \"of\": …}}"
    return .call op xs

partial def cond (t : J) (p : Path) : P Cond := do
  let (t, p, _) ← unwrap t p
  let (k, v) ← nodeOf t p (sortStrings (["and", "or", "not", "has_subset"] ++ exprKinds)) "a condition"
  let q := .k k :: p
  let twoOrMore (xs : List Cond) : P (List Cond) :=
    if xs.length < 2 then refuse q s!"{k} takes two or more conditions, not {xs.length}"
    else pure xs
  match k with
  | "and" => noCommentedFirst v q "and"; return .and (← twoOrMore (← each v q "and" cond))
  | "or" => noCommentedFirst v q "or"; return .or (← twoOrMore (← each v q "or" cond))
  | "not" => return .not (← cond v q)
  | "has_subset" => return .hasSubset (← expr v q)
  | _ => return .expr (← expr t p)
end

/-- A statement's name and expression, read at the statement's place `p`. -/
def statementOf (n e : J) (p : Path) : P (String × Expr) := do
  let name ← attrOf n (.k "name" :: .k "define" :: p) "a statement's name"
  let f ← expr e (.k "expr" :: .k "define" :: p)
  if let some m := f.problem then refuse p s!"the statement {name}: {m}"
  return (name, f)

/-- One form from JSON text. Lean-only: Racket has no single-form reader any more; it
is kept for tests and the readable-syntax work. -/
def parseForm (text : String) : P Expr := do
  let f ← expr (← read text) []
  if let .name _ := f then refuse [] "a form, not a name alone"
  if let some m := f.problem then refuse [] m
  return f

/-! ## Documents (rassoAST's `{"rasso": "1", "program": [item, …]}`)

Racket's `document->program` and `document->program/pragmas`. A document's
items are statements, comment lines, blank lines and pragmas. The checked document is
kept as JSON (`Doc.json`), so that it prints back as itself, comments and all.
Lowering drops the annotations.

Pragmas: each statement carries the most recent `backend` and `epsilon` above it, and its
line, as Racket's `document->program/pragmas` gives them. They are kept beside the program
and ignored when evaluating: `backend` chooses a solver and `epsilon` the tolerance a
solver's answers are checked within; neither changes what a program means (directional,
recorded here). -/

/-- The versions of rassoAST this reader reads. -/
def versions : List String := ["1"]

/-- An `epsilon` pragma: the default, or a tolerance. -/
inductive Epsilon where
  | default
  | float (d : Decimal)
  deriving Repr

/-- What a document says of one statement beyond its form (Racket's
`document->program/pragmas`): the backend and epsilon of the most recent pragmas above
it, and its line. -/
structure StatementInfo where
  backend : Option String := none
  epsilon : Option Epsilon := none
  line : Option Nat := none
  deriving Repr

/-- A checked document (Racket's checked jobj): its JSON as read, and what it lowers to. -/
structure Document where
  json : J
  program : Program
  info : List StatementInfo

/-- An item of a program, as read. -/
inductive Item where
  | stmt (line : Option Nat) (name : String) (f : Expr)
  | comment
  | blank
  | backend (w : String)
  | epsilon (e : Epsilon)

/-- The largest epsilon, 1e-3 (Racket's `max-epsilon`). -/
def _root_.Rasso.Decimal.isEpsilon (d : Decimal) : Bool :=
  if d.mant = 0 then true
  else if d.neg then false
  else if d.exp ≥ -3 then d.mant * 10 ^ (d.exp + 3).toNat ≤ 1
  else d.mant ≤ 10 ^ (-3 - d.exp).toNat

def documentItems (t : J) : P (List J) := do
  if let .arr _ := t then
    refuse [] "a program is a document, {\"rasso\": \"1\", \"program\": [item, …]}, not an array of statements"
  let vp ← fieldsOf t [] ["rasso", "program"] "a document"
  match vp[0]! with
  | .str v =>
    unless versions.contains v do
      refuse [.k "rasso"] s!"this reader reads version {", ".intercalate versions} of rassoAST, not {v}"
  | v => refuse [.k "rasso"] s!"this reader reads version {", ".intercalate versions} of rassoAST, not {show_ v}"
  arrayOf vp[1]! [.k "program"] "a document's program"

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c.toNat == 11 || c.toNat == 12 || c == '\r'

def item (t : J) (p : Path) : P Item := do
  let (k, v) ← plainNodeOf t p ["define", "comment", "blank", "pragma"] "an item of a program"
  let q := .k k :: p
  match k with
  | "define" =>
    let .obj fields := v | refuse q s!"a statement is a record, not {show_ v}"
    let keys := fields.map (·.1)
    let unknown := keys.filter fun k => !["name", "expr", "line", "note"].contains k
    unless unknown.isEmpty do
      refuse q s!"a statement has the fields name, expr, and optionally line and note; {", ".intercalate unknown} unknown"
    for f in ["name", "expr"] do
      unless keys.contains f do
        refuse q s!"a statement has the fields name, expr, and optionally line and note; {f} missing"
    let field (f : String) : J := (fields.lookup f).getD default
    let line ← if keys.contains "line" then
        match field "line" with
        | .int n => if n > 0 then pure (some n.toNat)
                    else refuse (.k "line" :: q) s!"a line is a positive integer, not {show_ (field "line")}"
        | x => refuse (.k "line" :: q) s!"a line is a positive integer, not {show_ x}"
      else pure none
    if keys.contains "note" then
      let _ ← commentText (field "note") (.k "note" :: q) "a note" (ownLine := false)
    let (n, f) ← statementOf (field "name") (field "expr") p
    return .stmt line n f
  | "comment" => let _ ← commentText v q "a comment line"; return .comment
  | "blank" => let _ ← fieldsOf v q [] "blank"; return .blank
  | _ =>
    let (pk, pv) ← plainNodeOf v q ["backend", "epsilon"] "a pragma"
    let r := .k pk :: q
    if pk == "backend" then
      let w ← stringOf pv r "a backend"
      if w.isEmpty || w.any isWs then refuse r s!"a backend is a word: not empty, no whitespace, not {rs w}"
      return .backend w
    let (ek, ev) ← plainNodeOf pv r ["float", "default"] "an epsilon"
    if ek == "default" then let _ ← fieldsOf ev (.k ek :: r) [] "default"; return .epsilon .default
    let bad {α : Type} : P α := refuse (.k ek :: r) s!"an epsilon is a tolerance, from 0 to the largest, not {show_ ev}"
    match ev with
    | .int n => if n == 0 then return .epsilon (.float ⟨false, 0, 0⟩) else bad
    | .float d => if d.isEpsilon then return .epsilon (.float d) else bad
    | _ => bad

/-- A document's JSON checked by rassoAST's rules (Racket's `check-document`) and lowered:
its statements' forms, and what each statement carries. -/
def lowerDocument (t : J) : P (Program × List StatementInfo) := do
  let items ← documentItems t
  let read ← items.zipIdx.mapM fun (x, i) => item x [.i i, .k "program"]
  let n := read.length
  for (x, i) in read.zipIdx do
    if let .blank := x then
      if i == 0 || i + 1 == n then refuse [.i i, .k "program"] "a blank line is never first or last in a program"
      if let some .blank := read[i - 1]? then
        refuse [.i i, .k "program"] "a blank is one or more blank lines, so never two in a row"
  let stmts := read.filterMap fun | .stmt l n f => some (l, n, f) | _ => none
  if stmts.isEmpty then refuse [.k "program"] "a program has at least one statement"
  let mut last := 0
  for ((l, _, _), i) in stmts.zipIdx do
    if let some l := l then
      -- two statements may share a line, as rassoSQL's CTEs may
      if l < last then
        refuse [.k "program"] s!"lines don't decrease down a program: statement {i}'s line {l} is before {last}"
      last := l
  let mut b : Option String := none
  let mut e : Option Epsilon := none
  let mut info : Array StatementInfo := #[]
  for x in read do
    match x with
    | .stmt l _ _ => info := info.push { backend := b, epsilon := e, line := l }
    | .backend w => b := some w
    | .epsilon v => e := some v
    | _ => pure ()
  return (stmts.map fun (_, n, f) => (n, f), info.toList)

/-- Read a rassoAST document (Racket's `json-read-ast`): the strict JSON reader, then
rassoAST's rules, each refusal at its place under `json-parse:`. -/
def readDocument (text : String) : P Document := do
  let t ← read text
  let (prog, info) ← lowerDocument t
  return ⟨t, prog, info⟩

/-- A document's text (Racket's `json-print-ast`). -/
def Document.print (d : Document) : String := d.json.textAst

/-- A program raised to a document of `define` items only, with no lines, notes or
comments (Racket's `program->document`). -/
def raiseProgram (prog : Program) : P J := do
  if prog.isEmpty then refuseP "not a program, a non-empty list of statements (define name form)"
  let ss ← prog.mapM fun (n, f) => do
    if let some p := f.problem then refuseP s!"the statement {n}: {p}"
    return node "define" (record [("name", ← pName n), ("expr", ← pExpr f)])
  return record [("rasso", .str "1"), ("program", .arr ss)]

/-- A program from a rassoAST document's text, its annotations dropped. -/
def parseProgram (text : String) : P Program := do
  return (← readDocument text).program

/-- A program as a rassoAST document's text (Racket's `json-print-ast` of
`program->document`). -/
def printProgram (prog : Program) : P String := do
  return (← raiseProgram prog).textAst


/-! ### Checks: Racket's refusals of documents -/

def refusedAt (text : String) : String :=
  match readDocument text with
  | .error m => ((m.dropPrefix? "json-parse: at ").map (·.toString) |>.getD m).splitOn ": " |>.headD ""
  | .ok _ => "read"

#guard refusedAt "[{\"define\": {\"name\": \"A\", \"expr\": {\"name\": \"R\"}}}]" == "$"
#guard refusedAt "{\"rasso\": \"1\", \"program\": [{\"define\": {\"name\": \"A\", \"expr\": {\"sigma\": {\"where\": {\"call\": {\"op\": \"<\", \"args\": [{\"attr\": \"a\"}]}}, \"of\": {\"name\": \"R\"}}}}}]}" == "$.program[0].define.expr.sigma.where.call"
#guard refusedAt "{\"rasso\": \"1\", \"program\": [{\"define\": {\"name\": \"A\", \"expr\": {\"name\": \"R\"}, \"line\": 3}}, {\"define\": {\"name\": \"B\", \"expr\": {\"name\": \"R\"}, \"line\": 2}}]}" == "$.program"
#guard refusedAt "{\"rasso\": \"1\", \"program\": [{\"blank\": {}}, {\"define\": {\"name\": \"A\", \"expr\": {\"name\": \"R\"}}}]}" == "$.program[0]"
#guard refusedAt "{\"rasso\": \"1\", \"program\": [{\"pragma\": {\"epsilon\": {\"float\": 0.5}}}, {\"define\": {\"name\": \"A\", \"expr\": {\"name\": \"R\"}}}]}" == "$.program[0].pragma.epsilon.float"
#guard refusedAt "{\"rasso\": \"1\", \"program\": [{\"comment\": \" only\"}]}" == "$.program"
#guard refusedAt "{\"rasso\": \"1\", \"program\": [{\"define\": {\"name\": \"A\", \"expr\": {\"join\": {\"operands\": [{\"commented\": {\"comments\": [\" c\"], \"value\": {\"name\": \"R\"}}}, {\"name\": \"S\"}]}}}}]}" == "$.program[0].define.expr.join.operands[0]"
#guard refusedAt "{\"rasso\": \"1\", \"program\": [{\"define\": {\"name\": \"A\", \"expr\": {\"join\": {\"operands\": [{\"name\": \"R\"}, {\"commented\": {\"comments\": [\" c\"], \"value\": {\"name\": \"S\"}}}]}}}}]}" == "read"

end Rasso.Json
