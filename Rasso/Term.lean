import Rasso.Finrel
import Rasso.Form

/-!
# Rasso: terms, γ's expressions, and unrestricted relations

One Racket term is one Lean term: the terms are the
forms' (`Rasso.Form`: `Term`, and γ's expression `Agg`), and this module evaluates
them. The operators evaluated here: `+ - * %`, `abs`, `min`, `max`, `sum`,
`all_different`, `= < <= > >=` and `and or not`, on ints and Booleans. `list` and
arithmetic on floats are deferred, and refused when evaluated.

In γ's expression an aggregate applied to a term stands for a value (Racket's
`eval-group-expr`). Aggregates: `count`, `sum`, `bool_and`, `bool_or`, `min`, `max`,
`all_different`; and `has_subset(R)`, true when every tuple of `R` matches some tuple of
the group on `R`'s attributes (Racket's `concrete-has-subset`). `Agg.eval` has no
environment, so it reads `R` only as a literal (`.omegaRows`): `Expr.eval` evaluates `R`
first and puts its value in as one (`Agg.splice`, `Rasso.Eval`).

An unrestricted relation (`Unrel`, Racket's `unrel`) is a heading and one Boolean term: its tuples are the assignments of values from the
heading's domains that make the term true.

Conventions:

* The evaluator is untyped, like Racket's: a term that misuses a value (`1 + true`) is
  refused when it is evaluated (`Except String`), not ruled out by a type.
* Comparisons use the value order (kind first, then within kind); `=` is equality of
  values.
* Term and γ evaluation are total (well-founded recursion on the term), so theorems
  can state what they compute.
* Racket's aggregate names are spelled with `-` (`bool-and`); the JSON CST spells them
  with `_` (`bool_and`). Both spellings are accepted.
-/

namespace Rasso

def asInt (who : String) : Value → Except String Int
  | .int n => .ok n
  | v => .error s!"{who}: {v} is not an int"

/-- An exact number (an int or a rat). -/
def asExact (who : String) : Value → Except String Rat
  | .int n => .ok n
  | .rat q _ => .ok q
  | v => .error s!"{who}: {v} is not an int or a rat"

/-- The values as ints, when every one is an int. -/
def allInts (vs : List Value) : Option (List Int) :=
  vs.mapM fun | .int n => some n | _ => none

/-- Arithmetic on ints stays on ints; with a rat among the operands it is done on the
rationals, and the result is `Value.ofRat` of it (so `1/2 + 1/2` is the int `1`). -/
def arith (who : String) (onInt : List Int → Int) (onRat : List Rat → Rat) (vs : List Value) :
    Except String Value := do
  match allInts vs with
  | some ns => return .int (onInt ns)
  | none => return Value.ofRat (onRat (← vs.mapM (asExact who)))

def asBool (who : String) : Value → Except String Bool
  | .bool b => .ok b
  | v => .error s!"{who}: {v} is not a bool"

/-- Apply an operator to values (Racket's `concrete-ops`, the slice of them used here), and the internal `if` of φ. -/
def applyOp (op : String) (vs : List Value) : Except String Value := do
  match op, vs with
  | "+", _ => return (← arith "+" (·.foldl (· + ·) 0) (·.foldl (· + ·) 0) vs)
  | "*", _ => return (← arith "*" (·.foldl (· * ·) 1) (·.foldl (· * ·) 1) vs)
  | "-", [v] => return (← arith "-" (fun ns => - ns.headD 0) (fun qs => - qs.headD 0) [v])
  | "-", v :: ws => return (← arith "-" (fun ns => ns.tail.foldl (· - ·) (ns.headD 0))
      (fun qs => qs.tail.foldl (· - ·) (qs.headD 0)) (v :: ws))
  | "%", [v, w] => return .int ((← asInt "%" v) % (← asInt "%" w))
  | "abs", [v] => return .int (← asInt "abs" v).natAbs
  | "sum", _ => return (← arith "sum" (·.foldl (· + ·) 0) (·.foldl (· + ·) 0) vs)
  | "min", v :: ws => return ws.foldl (fun m w => if Value.cmp w m == .lt then w else m) v
  | "max", v :: ws => return ws.foldl (fun m w => if Value.cmp w m == .gt then w else m) v
  | "all_different", _ => return .bool (vs.eraseDups.length == vs.length)
  | "=", [v, w] =>
    match v, w with
    | .int _, .float _ | .float _, .int _ =>
      throw s!"{v} = {w} compares an int with a float: give both one type"
    | .rat _ _, .float _ | .float _, .rat _ _ =>
      throw s!"{v} = {w} compares a rat with a float: give both one type"
    -- as Racket's `value=` does
    | .symbol s, .string u =>
      throw s!"{s} = {reprStr u} compares a symbol with a string: give both one type"
    | .string s, .symbol u =>
      throw s!"{reprStr s} = {u} compares a symbol with a string: give both one type"
    | _, _ => return .bool (v == w)
  | "<", [v, w] => return .bool (Value.cmp v w == .lt)
  | "<=", [v, w] => return .bool (Value.cmp v w != .gt)
  | ">", [v, w] => return .bool (Value.cmp v w == .gt)
  | ">=", [v, w] => return .bool (Value.cmp v w != .lt)
  | "and", _ => return .bool ((← vs.mapM (asBool "and")).all id)
  | "or", _ => return .bool ((← vs.mapM (asBool "or")).any id)
  | "not", [v] => return .bool (!(← asBool "not" v))
  -- internal: φ's guarded aggregates (`Rasso.Phi.Phi`); the JSON surface
  -- does not write it (`termNames`), as Racket's `term-operators` leaves it out
  | "if", [c, a, b] => return (if (← asBool "if" c) then a else b)
  | _, _ => throw s!"unknown operator {op} on {vs.length} operands"

/-- The value of a term on a tuple. -/
def Term.eval (t : Tuple) : Term → Except String Value
  | .attr a => match t.get? a with
    | some v => .ok v
    | none => .error s!"no attribute {a} in the tuple"
  | .val v => .ok v
  | .call op args => do applyOp op (← args.mapM (Term.eval t))

/-- A Boolean term's truth on a tuple. -/
def Term.holds (t : Tuple) (e : Term) : Except String Bool := do asBool "a test" (← e.eval t)

def Term.attrs : Term → List String
  | .attr a => [a]
  | .val _ => []
  | .call _ args => args.flatMap Term.attrs

/-! ## The domain of a computed value

Read from the expression and the heading alone, never from the data (Racket's
`expr-domain`). -/

def Value.kindDomain : Value → Domain
  | .bool _ => .kind .bool
  | .int _ => .kind .int
  | .symbol _ => .kind .symbol
  | .string _ => .kind .string
  | .float _ => .kind .float
  | .rat _ _ => .kind .rat

/-- The numeric kind of a domain, if it has one: int, or rat when it may hold a rat. -/
def Domain.numeric : Domain → Option Domain
  | .kind .int | .range _ _ => some (.kind .int)
  | .kind .rat => some (.kind .rat)
  | .set vs =>
    if vs.all (fun | .int _ => true | _ => false) then some (.kind .int)
    else if vs.all (fun v => v.exact?.isSome) then some (.kind .rat) else none
  | _ => none

/-- The domain of an arithmetic result from its operands' numeric kinds: int when all
are int; rat when one is rat, except for `%` and `abs`, which take ints only. -/
def arithDomain (op : String) (ks : List (Option Domain)) : Option Domain :=
  if ks.all (· == some (.kind .int)) then some (.kind .int)
  else if ["%", "abs"].contains op then none
  else if ks.all (·.isSome) then some (.kind .rat) else none

def isBoolOp (op : String) : Bool := ["=", "<", "<=", ">", ">=", "and", "or", "not"].contains op
def isArithOp (op : String) : Bool := ["+", "-", "*", "%", "abs", "sum", "min", "max"].contains op

def Term.domain (h : Heading) : Term → Option Domain
  | .attr a => h.lookup a
  | .val v => some v.kindDomain
  | .call op args =>
    if isBoolOp op then some (.kind .bool)
    else if isArithOp op then
      arithDomain op (args.attach.map fun ⟨x, _⟩ => (x.domain h).bind Domain.numeric)
    else none

/-! ## γ's expressions -/

/-- An aggregate's name in the `_` spelling. Written as a table rather than as
`op.replace "-" "_"`: it gives the same name for every aggregate, and core Lean has no
lemmas about `String.replace`, so a proof could not compute the table's result. -/
def aggName (op : String) : String :=
  match op with
  | "bool-and" => "bool_and"
  | "bool-or" => "bool_or"
  | "all-different" => "all_different"
  | s => s

/-- An aggregate of the values a term takes on a group. -/
def aggregate (op : String) (vs : List Value) : Except String Value := do
  match aggName op, vs with
  | "count", _ => return .int vs.length
  | "sum", _ => return (← arith "sum" (·.foldl (· + ·) 0) (·.foldl (· + ·) 0) vs)
  | "bool_and", _ => return .bool ((← vs.mapM (asBool "bool_and")).all id)
  | "bool_or", _ => return .bool ((← vs.mapM (asBool "bool_or")).any id)
  | "all_different", _ => return .bool (vs.eraseDups.length == vs.length)
  | "min", [] | "max", [] => throw s!"{op} of an empty group"
  | "min", v :: ws => return ws.foldl (fun m w => if Value.cmp w m == .lt then w else m) v
  | "max", v :: ws => return ws.foldl (fun m w => if Value.cmp w m == .gt then w else m) v
  | _, _ => throw s!"unknown aggregate {op}"

/-- The value of γ's expression on a group: `key` holds the grouping attributes. Each
aggregate's term is evaluated on every tuple of the group (a set: no repeats). -/
def Agg.eval (key : Tuple) (group : List Tuple) : Agg → Except String Value
  | .agg op t => do aggregate op (← group.mapM t.eval)
  | .attr a => match key.get? a with
    | some v => .ok v
    | none => .error s!"γ: {a} is not a grouping attribute and not inside an aggregate"
  | .val v => .ok v
  | .call op args => do applyOp op (← args.mapM (Agg.eval key group))
  | .hasSubset (.omegaRows h rows) =>
    .ok (.bool (rows.all fun row => group.any fun t =>
      (h.zip row).all fun ((a, _), v) => t.get? a == some v))
  | .hasSubset _ => .error "has_subset: its relation has not been evaluated"

/-- Whether γ's expression holds a `has_subset`. -/
def Agg.hasSub : Agg → Bool
  | .hasSubset _ => true
  | .call _ args => args.attach.any fun ⟨x, _⟩ => x.hasSub
  | _ => false

@[simp] theorem Agg.hasSub_agg (op : String) (t : Term) : (Agg.agg op t).hasSub = false := by
  simp [Agg.hasSub]

@[simp] theorem Agg.hasSub_attr (a : String) : (Agg.attr a).hasSub = false := by simp [Agg.hasSub]

@[simp] theorem Agg.hasSub_val (v : Value) : (Agg.val v).hasSub = false := by simp [Agg.hasSub]

/-- The attributes that the evaluated `has_subset` relations in γ's expression name. -/
def Agg.subsetAttrs : Agg → List String
  | .hasSubset (.omegaRows h _) => h.map (·.1)
  | .call _ args => args.attach.flatMap fun ⟨x, _⟩ => x.subsetAttrs
  | _ => []

def Agg.domain (h : Heading) : Agg → Option Domain
  | .agg op t => match aggName op with
    | "count" => some (.kind .int)
    | "bool_and" | "bool_or" | "all_different" => some (.kind .bool)
    | "sum" => (t.domain h).bind Domain.numeric
    | "min" | "max" => t.domain h
    | _ => none
  | .attr a => h.lookup a
  | .val v => some v.kindDomain
  | .call op args =>
    if isBoolOp op then some (.kind .bool)
    else if isArithOp op then
      arithDomain op (args.attach.map fun ⟨x, _⟩ => (x.domain h).bind Domain.numeric)
    else none
  | .hasSubset _ => some (.kind .bool)

/-- The name Racket gives γ's result when the program names none. -/
def gammaDefaultName : String := "value%"

/-- The keys γ groups by: the tuples of `R` restricted to the grouping attributes. With no
grouping attribute there is one key, the empty tuple, even if `R` is empty. -/
def Finrel.gammaKeys (by_ : List String) (r : Finrel) : List Tuple :=
  if by_.isEmpty then [[]] else (r.tuples.map (·.restrict by_)).eraseDups

/-- The attributes that `ex` reads outside every aggregate. -/
def Agg.bareAttrs : Agg → List String
  | .agg _ _ => []
  | .attr a => [a]
  | .val _ => []
  | .call _ args => args.flatMap Agg.bareAttrs
  | .hasSubset _ => []

/-- γ[by][ex → res](R). With no `by` there is one group, even if R is empty. Naming a grouping attribute twice is refused, as π refuses a repeated
attribute: the result's heading would name it twice. -/
def Finrel.gamma (by_ : List String) (ex : Agg) (res : String) (r : Finrel) :
    Except String Finrel := do
  for a in by_ do
    if (r.domainOf? a).isNone then throw s!"γ: no attribute {a} to group by in {r.attrs}"
  if by_.eraseDups.length != by_.length then
    throw s!"γ: {by_} names a grouping attribute twice"
  if by_.contains res then throw s!"γ: the result {res} is also a grouping attribute"
  -- checked here, before grouping, so that it holds when there is no group (R empty)
  for a in ex.bareAttrs do
    if !by_.contains a then throw s!"γ: {a} is not a grouping attribute and not inside an aggregate"
  let some d := ex.domain r.heading
    | throw s!"γ: the expression gives no domain's values, so its result can't be an attribute"
  let h ← by_.mapM fun a => match r.domainOf? a with
    | some d => .ok (a, d)
    | none => .error s!"γ: no attribute {a}"
  let ts ← (r.gammaKeys by_).mapM fun k => do
    let g := r.tuples.filter fun t => t.restrict by_ == k
    let v ← ex.eval k g
    return Tuple.ofPairs ((res, v) :: k)
  return Finrel.ofTuples (h ++ [(res, d)]) ts

/-! ## Unrestricted relations -/

/-- An unrestricted relation (Racket's `unrel`): a heading and one Boolean term. -/
structure Unrel where
  heading : Heading
  term : Term
  deriving Inhabited

/-- A term reads only attributes of the heading (Racket's `check-term-attrs!`). ω[H](p)
and σ_p refuse a term that reads an attribute outside the heading. Such a term would refuse on every tuple of a finite relation, and, on an
unrestricted one, a later ⋈ could make it read the other operand's attribute. -/
def Heading.scoped (who : String) (h : Heading) (p : Term) : Except String Unit :=
  let unknown := p.attrs.filter fun a => !h.attrs.contains a
  if unknown.isEmpty then .ok ()
  else .error s!"{who}: the term reads {unknown}, which are not attributes of the heading {h.attrs}"

/-- A term with the attributes it reads renamed, all at once. -/
def Term.rename (ren : List (String × String)) : Term → Term
  | .attr a => .attr (Finrel.renameAttr ren a)
  | .val v => .val v
  | .call op args => .call op (args.map (Term.rename ren))

namespace Unrel

def tt : Term := .val (.bool true)

/-- ω[heading]: every assignment of values from the domains. -/
def omega (h : Heading) : Unrel := ⟨h, tt⟩

def select (p : Term) (u : Unrel) : Except String Unrel := do
  Heading.scoped "σ" u.heading p
  return ⟨u.heading, .call "and" [u.term, p]⟩

def join (u v : Unrel) : Except String Unrel := do
  return ⟨← Finrel.joinHeading u.heading v.heading, .call "and" [u.term, v.term]⟩

/-- × : ⋈ of operands that share no attribute. -/
def product (u v : Unrel) : Except String Unrel := do
  Heading.disjoint "×" u.heading v.heading
  u.join v

/-- ρ: the heading and the term renamed; refused as on a finite relation. -/
def rename (ren : List (String × String)) (u : Unrel) : Except String Unrel := do
  Heading.renameCheck ren u.heading
  return ⟨Finrel.renameHeading ren u.heading, u.term.rename ren⟩

/-- ∪, ∩ and − need the same heading, as on finite relations. -/
def union (u v : Unrel) : Except String Unrel := do
  Heading.same "∪" u.heading v.heading
  return ⟨u.heading, .call "or" [u.term, v.term]⟩

def inter (u v : Unrel) : Except String Unrel := do
  Heading.same "∩" u.heading v.heading
  return ⟨u.heading, .call "and" [u.term, v.term]⟩

def diff (u v : Unrel) : Except String Unrel := do
  Heading.same "−" u.heading v.heading
  return ⟨u.heading, .call "and" [u.term, .call "not" [v.term]]⟩

/-- Every assignment over a heading whose domains are all finite. -/
def assignments (h : Heading) : Except String (List Tuple) := do
  let mut acc : List Tuple := [[]]
  for (a, d) in h do
    let some vs := d.values?
      | throw s!"the domain of {a} is not finite, so its values can't be listed"
    acc := acc.flatMap fun t => vs.map fun v => (a, v) :: t
  return acc.map Tuple.ofPairs

/-- The tuples of an unrestricted relation, when its domains are finite. -/
def tuples (u : Unrel) : Except String (List Tuple) := do
  (← assignments u.heading).filterM u.term.holds

end Unrel

/-- A finite relation as a term: the disjunction of its tuples (Racket's lift). -/
def Finrel.toUnrel (r : Finrel) : Unrel :=
  ⟨r.heading, .call "or" (r.tuples.map fun t =>
    .call "and" (t.map fun (a, v) => .call "=" [.attr a, .val v]))⟩

end Rasso
