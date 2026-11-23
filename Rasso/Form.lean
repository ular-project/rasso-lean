import Rasso.Value

/-!
# Rasso: the forms

The vocabulary of a rasso program, one Lean constructor for each shape of each operator
of Racket's `form-table`, so that a program read from the JSON surface
and printed again is the program it was (`Rasso/Json/`). This is the syntax only: what
the evaluator runs of it is in `Rasso/Eval.lean`.

| Racket's operator (`.rasso` name) | shapes | here |
|---|---|---|
| `omega` | heading; heading, where; heading, rows | `omega`, `omegaWhere`, `omegaRows` |
| `select` (`sigma`) | where, of | `select` |
| `project` (`pi`) | attrs, of | `project` |
| `rename` (`rho`) | renaming, of | `rename` (its field `renaming_`: `renaming` is a Lean keyword) |
| `join`, `product` (`cross`), `lateral`, `union`, `intersect`, `except` | operands (two or more) | `nary` with `NOp` |
| `gamma` | by, aggregate, as, of; by, aggregate, of | `gamma` (`as` optional) |
| `extend` | as, term, of | `extend` |
| `enum` | count, of; count, order, key, of | `enum` (key optional) |
| `omega-sol` (`omega_sol`) | data, decision | `omegaSol` |
| `sigma-sol` (`sigma_sol`) | condition, of | `sigmaSol` |
| `enum-sol` (`enum_sol`) | count, of; count, order, key, of | `enumSol` |
| `omega-msol` (`omega_msol`) | members; members, condition | `omegaMsol` (condition optional) |
| `sigma-msol` (`sigma_msol`) | condition, of | `sigmaMsol` |
| `enum-msol` (`enum_msol`) | count, of; count, order, key, of | `enumMsol` |
| `flatten-msol` (`flatten_msol`) | rank, of | `flattenMsol` |
| `db-ref` (`db_ref`) | relation, of | `dbRef` |
| `flatten`, `forget`, `lift` | rank, of; of; of | `flatten`, `forget`, `lift` |

A form `.rasso` doesn't write is internal to Racket's implementation and has no
constructor here: a condition's `holds`, `has` and `each-group`.

`Expr.problem` is Racket's `form-problem` for these forms: what makes a form that has the
right shape still not a form (an attribute named twice in a heading, a set not written
in value order, `not` of two operands, …).

Conventions:

* A heading is a list of (attribute, domain) pairs; a name is a `String`.
* `Expr.problem`'s words are close to `form-problem`'s, not the same: the JSON surface's
  checks compare where a refusal is, not its words.
* A set's order (`Domain` `set`) is Racket's `value<?`, which orders across kinds by the
  printed form, since the surface refuses a set not written in that order. Rasso's own
  order on values is kind first (`Rasso.Value`). They agree within a kind for int,
  bool and a symbol or string needing no quoting.
-/

namespace Rasso

/-- The relational operators of two or more operands. -/
inductive NOp where
  | join | product | lateral | union | intersect | except
  deriving DecidableEq, Repr, Inhabited, BEq

inductive Count where
  | all
  | int (k : Int)
  deriving DecidableEq, Repr, Inhabited, BEq

inductive Order where
  | asc | desc
  deriving DecidableEq, Repr, Inhabited, BEq

mutual
/-- A relation position: a statement's name, or a form. -/
inductive Expr where
  | name (n : String)
  | omega (heading : List (String × DomExpr))
  | omegaWhere (heading : List (String × DomExpr)) (where_ : Term)
  | omegaRows (heading : List (String × DomExpr)) (rows : List (List Value))
  | select (where_ : Term) (of : Expr)
  | project (attrs : List String) (of : Expr)
  | rename (renaming_ : List (String × String)) (of : Expr)
  | nary (op : NOp) (operands : List Expr)
  | gamma (by_ : List String) (aggregate : Agg) (as : Option String) (of : Expr)
  | extend (as : String) (term : Term) (of : Expr)
  | enum (count : Count) (key : Option (Order × Term)) (of : Expr)
  | omegaSol (data decision : Expr)
  | sigmaSol (condition : Cond) (of : Expr)
  | enumSol (count : Count) (key : Option (Order × Expr)) (of : Expr)
  | omegaMsol (members : List (String × Expr)) (condition : Option Cond)
  | sigmaMsol (condition : Cond) (of : Expr)
  | enumMsol (count : Count) (key : Option (Order × Expr)) (of : Expr)
  | flattenMsol (rank : Option String) (of : Expr)
  | dbRef (relation : String) (of : Expr)
  | flatten (rank : Option String) (of : Expr)
  | forget (of : Expr)
  | lift (of : Expr)

/-- A domain as written: a type, a range, a set of values, or `in R`. -/
inductive DomExpr where
  | kind (k : Kind)
  | range (lo hi : Int)
  | set (vs : List Value)
  | in_ (r : Expr)

/-- A term (Racket's `term?`). -/
inductive Term where
  | attr (a : String)
  | val (v : Value)
  | call (op : String) (args : List Term)

/-- γ's expression: a term in which an aggregate, or `has_subset(R)`, may stand. -/
inductive Agg where
  | attr (a : String)
  | val (v : Value)
  | call (op : String) (args : List Agg)
  | agg (op : String) (of : Term)
  | hasSubset (r : Expr)

/-- A solution set's condition. A relation position means: its one value is `true`. -/
inductive Cond where
  | and (cs : List Cond)
  | or (cs : List Cond)
  | not (c : Cond)
  | hasSubset (r : Expr)
  | expr (e : Expr)
end


instance : Inhabited Expr := ⟨.name "R"⟩
instance : Inhabited Term := ⟨.attr "a"⟩

/-- A program: statements `name := form`. -/
abbrev Program := List (String × Expr)

/-! ## Equality of forms -/

mutual
def Expr.beq : Expr → Expr → Bool
  | .name a, .name b => a == b
  | .omega h, .omega k => headBeq h k
  | .omegaWhere h t, .omegaWhere k u => headBeq h k && t.beq u
  | .omegaRows h r, .omegaRows k s => headBeq h k && r == s
  | .select t r, .select u s => t.beq u && r.beq s
  | .project a r, .project b s => a == b && r.beq s
  | .rename a r, .rename b s => a == b && r.beq s
  | .nary o rs, .nary p ss => o == p && exprsBeq rs ss
  | .gamma b x a r, .gamma c y d s => b == c && x.beq y && a == d && r.beq s
  | .extend a t r, .extend b u s => a == b && t.beq u && r.beq s
  | .enum c none r, .enum d none s => c == d && r.beq s
  | .enum c (some (o, t)) r, .enum d (some (p, u)) s => c == d && o == p && t.beq u && r.beq s
  | .omegaSol a b, .omegaSol c d => a.beq c && b.beq d
  | .sigmaSol x r, .sigmaSol y s => x.beq y && r.beq s
  | .enumSol c none r, .enumSol d none s => c == d && r.beq s
  | .enumSol c (some (o, k)) r, .enumSol d (some (p, l)) s => c == d && o == p && k.beq l && r.beq s
  | .omegaMsol ms none, .omegaMsol ns none => membersBeq ms ns
  | .omegaMsol ms (some x), .omegaMsol ns (some y) => membersBeq ms ns && x.beq y
  | .sigmaMsol x r, .sigmaMsol y s => x.beq y && r.beq s
  | .enumMsol c none r, .enumMsol d none s => c == d && r.beq s
  | .enumMsol c (some (o, k)) r, .enumMsol d (some (p, l)) s => c == d && o == p && k.beq l && r.beq s
  | .flattenMsol a r, .flattenMsol b s => a == b && r.beq s
  | .dbRef a r, .dbRef b s => a == b && r.beq s
  | .flatten a r, .flatten b s => a == b && r.beq s
  | .forget r, .forget s => r.beq s
  | .lift r, .lift s => r.beq s
  | _, _ => false
def exprsBeq : List Expr → List Expr → Bool
  | [], [] => true
  | r :: rs, s :: ss => r.beq s && exprsBeq rs ss
  | _, _ => false
def membersBeq : List (String × Expr) → List (String × Expr) → Bool
  | [], [] => true
  | (a, r) :: rs, (b, s) :: ss => a == b && r.beq s && membersBeq rs ss
  | _, _ => false
def headBeq : List (String × DomExpr) → List (String × DomExpr) → Bool
  | [], [] => true
  | (a, d) :: h, (b, e) :: k => a == b && d.beq e && headBeq h k
  | _, _ => false
def DomExpr.beq : DomExpr → DomExpr → Bool
  | .kind k, .kind l => k == l
  | .range a b, .range c d => a == c && b == d
  | .set vs, .set ws => vs == ws
  | .in_ r, .in_ s => r.beq s
  | _, _ => false
def Term.beq : Term → Term → Bool
  | .attr a, .attr b => a == b
  | .val v, .val w => v == w
  | .call o xs, .call p ys => o == p && termsBeq xs ys
  | _, _ => false
def termsBeq : List Term → List Term → Bool
  | [], [] => true
  | x :: xs, y :: ys => x.beq y && termsBeq xs ys
  | _, _ => false
def Agg.beq : Agg → Agg → Bool
  | .attr a, .attr b => a == b
  | .val v, .val w => v == w
  | .call o xs, .call p ys => o == p && aggsBeq xs ys
  | .agg o t, .agg p u => o == p && t.beq u
  | .hasSubset r, .hasSubset s => r.beq s
  | _, _ => false
def aggsBeq : List Agg → List Agg → Bool
  | [], [] => true
  | x :: xs, y :: ys => x.beq y && aggsBeq xs ys
  | _, _ => false
def Cond.beq : Cond → Cond → Bool
  | .and xs, .and ys => condsBeq xs ys
  | .or xs, .or ys => condsBeq xs ys
  | .not x, .not y => x.beq y
  | .hasSubset r, .hasSubset s => r.beq s
  | .expr r, .expr s => r.beq s
  | _, _ => false
def condsBeq : List Cond → List Cond → Bool
  | [], [] => true
  | x :: xs, y :: ys => x.beq y && condsBeq xs ys
  | _, _ => false
end

instance : BEq Expr := ⟨Expr.beq⟩

/-! ## Names -/

/-- Each operator of `NOp`, as `.rasso` (and JSON) names it. -/
def NOp.name : NOp → String
  | .join => "join" | .product => "cross" | .lateral => "lateral"
  | .union => "union" | .intersect => "intersect" | .except => "except"

def NOp.all : List NOp := [.join, .product, .lateral, .union, .intersect, .except]

/-- The words `.rasso` keeps for itself, which no name may be. -/
def reservedWords : List String :=
  ["and", "or", "not", "true", "false", "join", "cross", "lateral", "union", "intersect",
   "except", "omega", "sigma", "pi", "rho", "in", "has_subset", "int", "rat", "float",
   "string", "symbol", "bool", "omega_sol", "sigma_sol", "gamma", "extend", "enum_sol",
   "enum", "flatten", "forget", "lift", "all", "asc", "desc", "omega_msol", "sigma_msol",
   "enum_msol", "flatten_msol", "db_ref"]

/-- The operators of terms, as `.rasso` spells them (Racket's `term-operators` through
`term-names`). -/
def termOperators : List String :=
  ["*", "+", "-", "<", "<=", "=", ">", ">=", "abs", "all_different", "and", "list", "max",
   "min", "%", "not", "or", "sum"]

/-- The aggregates, as `.rasso` spells them (Racket's `agg-names`). -/
def aggNames : List String :=
  ["all_different", "sum", "count", "bool_and", "bool_or", "min", "max"]

/-- Every spelling `term-names` has. -/
def termNames : List String := (termOperators ++ aggNames).eraseDups

/-- An attribute's (and a statement's, and a relation's) name: letters, digits and `_`,
not starting with a digit (Racket's `attribute?`). -/
def isAttribute (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    let ok (c : Char) := c.isAlphanum || c == '_'
    (c.isAlpha || c == '_') && cs.all ok && s.toList.all (·.toNat < 128)

/-- rassoAST's rule on names: a reserved word is no name (Racket's
`name-problem`), or none. -/
def nameProblem (s : String) : Option String :=
  if reservedWords.contains s then some s!"{s} is a reserved word, not a name" else none

/-- rassoAST's rule on symbol values: none holds a `|` (Racket's
`symbol-problem`). -/
def symbolProblem (s : String) : Option String :=
  if s.toList.contains '|' then some s!"the symbol {reprStr s} has a | in it, which no symbol value may"
  else none

/-- rassoAST's rule on a call's arity (Racket's `call-problem`). Racket's `/`
(two operands) is not here: Rasso has no `/` yet. -/
def callProblem (op : String) (n : Nat) : Option String :=
  if ["=", "<", ">", "<=", ">="].contains op && n != 2 then
    some s!"{op} compares exactly two operands, not {n}"
  else if ["+", "*", "%", "and", "or"].contains op && n < 2 then
    some s!"{op} takes two or more operands, not {n}"
  else if op == "-" && n < 1 then some "- takes one or more operands, not 0"
  else none

/-! ## Racket's order on values, for a set -/

/-- A symbol as Racket's `write` prints it, approximately: with bars when it holds a
character that would otherwise end or change it, or could read as a number (a decimal,
or a fraction such as `1/2`, so that the symbol never prints like a rat). -/
def racketSymbolText (s : String) : String :=
  let special (c : Char) := c.isWhitespace || "()[]{}\",'`;|\\".toList.contains c
  let numeric := (s.toList.head?.map fun c => c.isDigit || c == '-' || c == '+' || c == '.').getD false
    && s.toList.all fun c => c.isDigit || "+-.eE/".toList.contains c
  if s.isEmpty || s.toList.any special || numeric || s.startsWith "#" then "|" ++ s ++ "|" else s

/-- A value as Racket's `~s` prints it, for `value<?`'s comparison across kinds. -/
def racketText : Value → String
  | .bool b => if b then "#t" else "#f"
  | .int n => toString n
  | .float d => d.toRacket
  | .string s => reprStr s
  | .symbol s => racketSymbolText s
  | .rat q _ => s!"{q.num}/{q.den}"

/-- Two numbers (int, rat or float) compared as the rationals they denote. -/
def numCompare : Value → Value → Option Ordering
  | .int a, .int b => some (compare a b)
  | a, b =>
    match a.num?, b.num? with
    | some x, some y => some (compare x y)
    | _, _ => none

/-- Racket's `value<?`: numbers by `<`, then by their printed form; anything else by its
printed form. -/
def racketValueLt (a b : Value) : Bool :=
  match numCompare a b with
  | some .lt => true
  | some .gt => false
  | _ => racketText a < racketText b

/-! ## What makes a form not a form (Racket's `form-problem`) -/

def Kind.name : Kind → String
  | .int => "int" | .float => "float" | .string => "string" | .symbol => "symbol" | .bool => "bool"
  | .rat => "rat"

def sortedStrictly : List Value → Bool
  | a :: b :: rest => racketValueLt a b && sortedStrictly (b :: rest)
  | _ => true

/-- A set's values as Racket's `dom-set` gives them: without repeats, in value order. -/
def racketSetValues (vs : List Value) : List Value :=
  vs.eraseDups.mergeSort fun a b => !racketValueLt b a

def firstSome {α : Type} : List (Option α) → Option α
  | [] => none
  | some a :: _ => some a
  | none :: xs => firstSome xs

mutual
partial def Expr.problem : Expr → Option String
  | .name n => if isAttribute n then none else some s!"{n} is not a name"
  | .omega h => headingProblem false h
  | .omegaWhere h t => firstSome [headingProblem false h, t.problem]
  | .omegaRows h _ => headingProblem true h
  | .select t r => firstSome [t.problem, r.problem]
  | .project _ r => r.problem
  | .rename ren r =>
    if (ren.map (·.1)).eraseDups.length != ren.length then some "a renaming renames an attribute twice"
    else if (ren.map (·.2)).eraseDups.length != ren.length then some "a renaming gives an attribute twice"
    else r.problem
  | .nary _ rs => if rs.length < 2 then some "takes two or more operands" else firstSome (rs.map Expr.problem)
  | .gamma _ x _ r => firstSome [x.problem, r.problem]
  | .extend _ t r => firstSome [t.problem, r.problem]
  | .enum c k r => firstSome [countProblem c, (k.bind fun p => p.2.problem), r.problem]
  | .omegaSol a b => firstSome [a.problem, b.problem]
  | .sigmaSol c r => firstSome [c.problem, r.problem]
  | .enumSol c k r => firstSome [countProblem c, (k.bind fun p => p.2.problem), r.problem]
  | .omegaMsol ms c =>
    if ms.isEmpty then some "omega_msol has at least one member"
    else if (ms.map (·.1)).eraseDups.length != ms.length then
      some "omega_msol: two members have one name"
    else firstSome ((ms.map fun m => m.2.problem) ++ [c.bind Cond.problem])
  | .sigmaMsol c r => firstSome [c.problem, r.problem]
  | .enumMsol c k r => firstSome [countProblem c, (k.bind fun p => p.2.problem), r.problem]
  | .flattenMsol _ r | .dbRef _ r | .flatten _ r | .forget r | .lift r => r.problem

partial def countProblem : Count → Option String
  | .all => none
  | .int k => if k < 0 then some s!"{k} is not a count" else none

/-- A heading's problem; `data` for a finite relation's, which takes no `in`. -/
partial def headingProblem (data : Bool) (h : List (String × DomExpr)) : Option String :=
  if (h.map (·.1)).eraseDups.length != h.length then some "the heading names an attribute twice"
  else firstSome (h.map fun (_, d) => match d with
    | .in_ r =>
      if data then some "in gives a relation's domain; a finite relation's heading takes a domain"
      else r.problem
    | .range lo hi => if lo ≤ hi then none else some s!"(range {lo} {hi}) is empty"
    | .set vs =>
      if !sortedStrictly vs then
        -- Racket's words; Racket gives a set with a repeat its general message instead,
        -- and Lean this one, which is true of it too
        some s!"(set {" ".intercalate (vs.map racketText)}) is not in value order: write (set {" ".intercalate ((racketSetValues vs).map racketText)})"
      -- a domain is the set an attribute's values range over; as no Lean type holds both a
      -- float and an exact number, no domain does
      else if vs.any Value.isFloat && vs.any Value.isExact then
        some s!"(set {" ".intercalate (vs.map racketText)}) mixes floats with exact numbers: give it one kind of number"
      -- likewise a symbol and a string, as `=` refuses to compare them;
      -- Lean only, as above
      else if vs.any Value.isSymbol && vs.any Value.isString then
        some s!"(set {" ".intercalate (vs.map racketText)}) mixes symbols with strings: give it one type"
      else none
    | .kind _ => none)

partial def Term.problem : Term → Option String
  | .attr _ | .val _ => none
  | .call "not" args => if args.length != 1 then some "not takes one operand" else firstSome (args.map Term.problem)
  | .call op args =>
    if (op == "and" || op == "or") && args.length < 2 then some s!"{op} takes two or more operands"
    else firstSome (args.map Term.problem)

partial def Agg.problem : Agg → Option String
  | .attr _ | .val _ => none
  | .agg _ t => t.problem
  | .hasSubset r => r.problem
  | .call "not" args => if args.length != 1 then some "not takes one operand" else firstSome (args.map Agg.problem)
  | .call op args =>
    if (op == "and" || op == "or") && args.length < 2 then some s!"{op} takes two or more operands"
    else if !termOperators.contains op && args.length != 1 then
      some s!"{op} is an aggregate of one term"
    else firstSome (args.map Agg.problem)

partial def Cond.problem : Cond → Option String
  | .and cs | .or cs => firstSome (cs.map Cond.problem)
  | .not c => c.problem
  | .hasSubset r | .expr r => r.problem
end

end Rasso

namespace Rasso

/-! ## Replacing a relation position

`Expr.replace target new f`: `f` with every relation position that is `target` (as a
form, `Expr.beq`) made `new`. Racket's evaluator reads a solution set's condition and key
so: each occurrence of the operand's form is the candidate. -/

mutual
def Expr.replace (target new : Expr) (f : Expr) : Expr :=
  if f.beq target then new else
  match f with
  | .name n => .name n
  | .omega hd => .omega (headReplace target new hd)
  | .omegaWhere hd w => .omegaWhere (headReplace target new hd) w
  | .omegaRows hd rows => .omegaRows (headReplace target new hd) rows
  | .select w of => .select w (Expr.replace target new of)
  | .project as of => .project as (Expr.replace target new of)
  | .rename ren of => .rename ren (Expr.replace target new of)
  | .nary op rs => .nary op (rs.map fun x => Expr.replace target new x)
  | .gamma by_ x res of => .gamma by_ (Agg.replace target new x) res (Expr.replace target new of)
  | .extend res tm of => .extend res tm (Expr.replace target new of)
  | .enum c k of => .enum c k (Expr.replace target new of)
  | .omegaSol a b => .omegaSol (Expr.replace target new a) (Expr.replace target new b)
  | .sigmaSol c of => .sigmaSol (Cond.replace target new c) (Expr.replace target new of)
  | .enumSol c k of =>
    .enumSol c (k.attach.map fun ⟨(o, x), _⟩ => (o, Expr.replace target new x)) (Expr.replace target new of)
  | .omegaMsol ms c =>
    .omegaMsol (membersReplace target new ms)
      (c.attach.map fun ⟨x, _⟩ => Cond.replace target new x)
  | .sigmaMsol c of => .sigmaMsol (Cond.replace target new c) (Expr.replace target new of)
  | .enumMsol c k of =>
    .enumMsol c (k.attach.map fun ⟨(o, x), _⟩ => (o, Expr.replace target new x)) (Expr.replace target new of)
  | .flattenMsol k of => .flattenMsol k (Expr.replace target new of)
  | .dbRef n of => .dbRef n (Expr.replace target new of)
  | .flatten k of => .flatten k (Expr.replace target new of)
  | .forget of => .forget (Expr.replace target new of)
  | .lift of => .lift (Expr.replace target new of)
def membersReplace (target new : Expr) : List (String × Expr) → List (String × Expr)
  | [] => []
  | (n, e) :: ms => (n, Expr.replace target new e) :: membersReplace target new ms
def headReplace (target new : Expr) : List (String × DomExpr) → List (String × DomExpr)
  | [] => []
  | (a, .in_ x) :: h => (a, .in_ (Expr.replace target new x)) :: headReplace target new h
  | (a, d) :: h => (a, d) :: headReplace target new h
def Agg.replace (target new : Expr) : Agg → Agg
  | .call op args => .call op (args.map fun x => Agg.replace target new x)
  | .hasSubset x => .hasSubset (Expr.replace target new x)
  | a => a
def Cond.replace (target new : Expr) : Cond → Cond
  | .and cs => .and (cs.map fun x => Cond.replace target new x)
  | .or cs => .or (cs.map fun x => Cond.replace target new x)
  | .not c => .not (Cond.replace target new c)
  | .hasSubset x => .hasSubset (Expr.replace target new x)
  | .expr x => .expr (Expr.replace target new x)
end

end Rasso
