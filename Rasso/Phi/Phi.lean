import Rasso.Phi.Fragment

/-!
# φ: a solution set as one relation over cells

A port of Racket's `phi`.

A solution set `σ_sol[cₙ](… σ_sol[c₁](ω_sol[D, Dec]))` has one candidate for each way of
giving every Data tuple one Decision tuple. φ gives one **cell** to each pair (Data tuple
`i`, Decision attribute `a`), named `a ++ i`, ranging over `a`'s domain, and writes the
conditions as one Boolean term over the cells. The result, `Flat`, is an ordinary
unrestricted relation (`Flat.rel`) plus what is needed to turn an assignment of the cells
back into a candidate (`substitute`).

How: the **symbolic candidate** holds the Data tuples, with each Decision value replaced
by its cell (`.attr "a3"`). The conditions run over it with symbolic γ, extend and join:
an operator on known values (`.val`) computes now, with `applyOp`; one that touches a cell
builds a term. A row that a join matched on a cell carries a **guard**. A symbolic value
is a `Term`, so the output needs no new type.

φ refuses (an `Except` error) wherever Lean's evaluator could refuse on some candidate,
using a **kind check** on every term it builds (`Phi.opKinds`); and, as Racket's `phi`,
on grouping by a cell, on `all_different`/`min`/`max`/`has_subset` over guarded rows, and
on a condition whose expression is not one unguarded row.

Conventions:

* What counts as decided mirrors Racket: an aggregate always builds a term
  (`symbolic-agg`), except `count` over rows that are all present.
* γ's `has_subset` tests "decided" (`.val`), where Racket's `phi-has` tests "is a bare
  cell" and compares any other term with `equal?`: a Racket bug, not copied.
* Data tuples are numbered as Racket numbers them (`tuple<?` over the Data's declared
  heading order, by `racketValueLt`). A Data value whose printed form the port may get
  wrong is refused.
* No floats anywhere.
-/

namespace Rasso.Phi

open Rasso

/-! ## Kinds: the static pass -/

/-- The kinds of exact values. -/
inductive VK where
  | bool | int | rat | sym | str
  deriving DecidableEq, Repr, Inhabited

def vkOf : Value → Option VK
  | .bool _ => some .bool
  | .int _ => some .int
  | .rat _ _ => some .rat
  | .symbol _ => some .sym
  | .string _ => some .str
  | .float _ => none

/-- The kinds a cell over this domain can take (its values', for a finite domain). -/
def domKinds (d : Domain) : Option (List VK) := do
  let vs ← d.values?
  let ks ← vs.mapM vkOf
  return ks.eraseDups

def subKinds (ks allowed : List VK) : Bool := ks.all allowed.contains

def numKinds : List VK := [.int, .rat]

/-- The kinds of `op` applied to arguments of the given kinds, or why `applyOp` might
refuse on some values of those kinds (read off `applyOp`, `Rasso.Term`). -/
def opKinds (op : String) (ks : List (List VK)) : Except String (List VK) := do
  let all := ks.flatten.eraseDups
  let need (allowed : List VK) : Except String Unit :=
    unless ks.all (subKinds · allowed) do
      throw s!"φ: {op} may be applied to a value it refuses"
  let arity (ok : Bool) : Except String Unit :=
    unless ok do throw s!"φ: {op} on {ks.length} operands"
  match op with
  | "+" | "*" | "sum" | "-" =>
    if op == "-" then arity (ks.length ≥ 1)
    need numKinds
    return if all.contains .rat then [.int, .rat] else [.int]
  | "%" => arity (ks.length == 2); need [.int]; return [.int]
  | "abs" => arity (ks.length == 1); need [.int]; return [.int]
  | "min" | "max" => arity (ks.length ≥ 1); return all
  | "all_different" => return [.bool]
  | "=" =>
    arity (ks.length == 2)
    -- `=` refuses a symbol beside a string (`applyOp`)
    unless !(all.contains .sym && all.contains .str) do
      throw s!"φ: = may compare a symbol with a string"
    return [.bool]
  | "<" | "<=" | ">" | ">=" => arity (ks.length == 2); return [.bool]
  | "and" | "or" => need [.bool]; return [.bool]
  | "not" => arity (ks.length == 1); need [.bool]; return [.bool]
  | "if" =>
    match ks with
    | [c, a, b] =>
      unless subKinds c [.bool] do throw "φ: if on a test that may not be a bool"
      return (a ++ b).eraseDups
    | _ => throw s!"φ: if on {ks.length} operands"
  | _ => throw s!"φ: unknown operator {op}"

/-- The kinds of a term over cells. -/
def termKinds (cells : List (String × List VK)) : Term → Except String (List VK)
  | .val v => match vkOf v with
    | some k => .ok [k]
    | none => .error "φ: a float (floats are not in φ's first version)"
  | .attr c => match cells.lookup c with
    | some ks => .ok ks
    | none => .error s!"φ: {c} is not a cell"
  | .call op args => do opKinds op (← args.attach.mapM fun ⟨x, _⟩ => termKinds cells x)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ args›; omega)

/-- Each cell's kinds, from its domain. -/
def cellKinds (cells : Heading) : Except String (List (String × List VK)) :=
  cells.mapM fun (c, d) => match domKinds d with
    | some ks => .ok (c, ks)
    | none => .error s!"φ: the domain of {c} is not finite, or holds a float"

/-- What is proved of the kind check (`Rasso/Phi/Sound/Kinds.lean`, `kindsSound`): when
`kinds` are the cells' kinds, for every assignment `x` of the cells within their domains, a
term whose kinds are found evaluates without refusal, to a value of one of those kinds. -/
def KindsSound (cells : Heading) (kinds : List (String × List VK)) : Prop :=
  cellKinds cells = .ok kinds →
  ∀ (t : Term) (ks : List VK) (x : Tuple),
    termKinds kinds t = .ok ks →
    (∀ c d, cells.lookup c = some d → ∃ v, x.get? c = some v ∧ d.mem v = true) →
    ∃ v, t.eval x = .ok v ∧ ∃ k, vkOf v = some k ∧ k ∈ ks

/-! ## Symbolic relations -/

def tt : Term := .val (.bool true)

def isTrue : Term → Bool
  | .val (.bool true) => true
  | _ => false

def decided? : Term → Option Value
  | .val v => some v
  | _ => none

/-- A symbolic row: each attribute's value as a term over cells. -/
abbrev SRow := List (String × Term)

/-- A symbolic relation: the heading Lean's evaluator would compute, and rows, each with
a guard (Racket's `erel`). -/
structure SRel where
  heading : Heading
  rows : List (SRow × Term)
  deriving Inhabited

/-- The context of one condition: the cells' kinds. -/
abbrev Kinds := List (String × List VK)

/-- Build `op args` as a term, after the kind check. -/
def mk (ks : Kinds) (op : String) (args : List Term) : Except String Term := do
  let _ ← opKinds op (← args.mapM (termKinds ks))
  return .call op args

/-- An operator symbolically: on known values computed now (Lean's `applyOp`, its result
and its refusal), otherwise built (Racket's symbolic `op`). -/
def sApply (ks : Kinds) (op : String) (args : List Term) : Except String Term :=
  match args.mapM decided? with
  | some vs => do return .val (← applyOp op vs)
  | none => mk ks op args

/-- A term on a symbolic row. -/
def sEval (ks : Kinds) (row : SRow) : Term → Except String Term
  | .attr a => match row.lookup a with
    | some v => .ok v
    | none => .error s!"no attribute {a} in the tuple"
  | .val v => .ok (.val v)
  | .call op args => do sApply ks op (← args.attach.mapM fun ⟨x, _⟩ => sEval ks row x)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ args›; omega)

/-- An aggregate over a group (Racket's `symbolic-agg`): always a term, except `count`
over rows that are all present. -/
def sAgg (ks : Kinds) (op : String) (vs gs : List Term) : Except String Term := do
  let present := gs.all isTrue
  let whenPresent (v g z : Term) : Except String Term :=
    if isTrue g then .ok v else mk ks "if" [g, v, z]
  match aggName op with
  | "count" =>
    if present then return .val (.int vs.length)
    mk ks "sum" (← gs.mapM fun g => whenPresent (.val (.int 1)) g (.val (.int 0)))
  | "sum" => mk ks "sum" (← (vs.zip gs).mapM fun (v, g) => whenPresent v g (.val (.int 0)))
  | "bool_and" => mk ks "and" (← (vs.zip gs).mapM fun (v, g) =>
      if isTrue g then .ok v else do mk ks "or" [← mk ks "not" [g], v])
  | "bool_or" => mk ks "or" (← (vs.zip gs).mapM fun (v, g) =>
      if isTrue g then .ok v else mk ks "and" [g, v])
  | o =>
    unless present do
      throw s!"φ: {o} over tuples a join matched on a decided value is not yet implemented"
    match o with
    | "all_different" => mk ks "all_different" vs
    | "min" => mk ks "min" vs
    | "max" => mk ks "max" vs
    | _ => throw s!"unknown aggregate {op}"

/-- The equalities under which `row` matches every (attribute, value) pair: `none` when a
decided value differs or an attribute is missing (Racket's `phi-has`, one row). -/
def sHasConds (ks : Kinds) (row : SRow) : List (String × Value) → Except String (Option (List Term))
  | [] => .ok (some [])
  | (a, v) :: ps => match row.lookup a with
    | some (.val w) => if w != v then .ok none else sHasConds ks row ps
    | some t => do
      let c ← mk ks "=" [t, .val v]
      match ← sHasConds ks row ps with
      | none => return none
      | some cs => return some (c :: cs)
    | none => .ok none

/-- Some row of `rows` matches every (attribute, value) pair: an `or` of `and`s, an
equality term where the row's value is not decided (Racket's `phi-has`, testing "decided"
rather than "is a cell"). -/
def sHasAlts (ks : Kinds) (pairs : List (String × Value)) : List SRow → Except String (List Term)
  | [] => .ok []
  | row :: rows => do
    match ← sHasConds ks row pairs with
    | none => sHasAlts ks pairs rows
    | some cs => do
      let a ← mk ks "and" cs
      let rest ← sHasAlts ks pairs rows
      return a :: rest

def sHas (ks : Kinds) (rows : List SRow) (pairs : List (String × Value)) : Except String Term := do
  mk ks "or" (← sHasAlts ks pairs rows)

/-- γ's expression on a group (Racket's `eval-group-expr` with the symbolic algebra). -/
def sAggEval (ks : Kinds) (key : SRow) (group : List (SRow × Term)) : Agg → Except String Term
  | .agg op t => do sAgg ks op (← group.mapM fun (r, _) => sEval ks r t) (group.map (·.2))
  | .attr a => match key.lookup a with
    | some v => .ok v
    | none => .error s!"γ: {a} is not a grouping attribute and not inside an aggregate"
  | .val v => .ok (.val v)
  | .call op args => do sApply ks op (← args.attach.mapM fun ⟨x, _⟩ => sAggEval ks key group x)
  | .hasSubset (.omegaRows h rows) => do
    unless group.all (isTrue ·.2) do
      throw "φ: has_subset over tuples a join matched on a decided value is not yet implemented"
    let terms ← rows.mapM fun row => sHas ks (group.map (·.1)) (h.map (·.1) |>.zip row)
    mk ks "and" terms
  | .hasSubset _ => .error "has_subset: its relation has not been evaluated"
termination_by x => sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ args›; omega)

/-- γ symbolically: Lean's checks (`Finrel.gamma`), then groups by decided keys. -/
def sGamma (ks : Kinds) (by_ : List String) (ex : Agg) (res : String) (r : SRel) :
    Except String SRel := do
  for a in by_ do
    if (r.heading.lookup a).isNone then throw s!"γ: no attribute {a} to group by in {r.heading.attrs}"
  if by_.contains res then throw s!"γ: the result {res} is also a grouping attribute"
  if by_.eraseDups.length != by_.length then throw "φ: γ groups by an attribute twice"
  -- as Finrel.gamma: checked before grouping, so that it holds when there is no group
  for a in ex.bareAttrs do
    if !by_.contains a then throw s!"γ: {a} is not a grouping attribute and not inside an aggregate"
  let some d := ex.domain r.heading
    | throw s!"γ: the expression gives no domain's values, so its result can't be an attribute"
  let h ← by_.mapM fun a => match r.heading.lookup a with
    | some d => .ok (a, d)
    | none => .error s!"γ: no attribute {a}"
  -- each row's key, which must be decided
  let keyed ← r.rows.mapM fun (row, g) => do
    let key ← by_.mapM fun a => match row.lookup a with
      | some (.val v) => .ok (a, v)
      | some _ => .error s!"γ: cannot group by {a}: its value depends on the assignment"
      | none => .error s!"γ: no attribute {a}"
    return (key, row, g)
  let keys : List (List (String × Value)) :=
    if by_.isEmpty then [[]] else (keyed.map (·.1)).eraseDups
  let out ← keys.mapM fun k => do
    let group := (keyed.filter (·.1 == k)).map fun (_, row, g) => (row, g)
    let keyRow : SRow := k.map fun (a, v) => (a, .val v)
    let v ← sAggEval ks keyRow group ex
    let g ← if by_.isEmpty then pure tt else sApply ks "or" (group.map (·.2))
    return (keyRow ++ [(res, v)], g)
  return ⟨h ++ [(res, d)], out⟩

/-- extend symbolically: Lean's checks (`Finrel.extend`), then the term on each row. -/
def sExtend (ks : Kinds) (res : String) (t : Term) (r : SRel) : Except String SRel := do
  if r.heading.attrs.contains res then throw s!"extend: the attribute {res} is already in {r.heading.attrs}"
  let some d := t.domain r.heading
    | throw "extend: the term gives no domain's values, so its result can't be an attribute"
  let rows ← r.rows.mapM fun (row, g) => do return (row ++ [(res, ← sEval ks row t)], g)
  return ⟨r.heading ++ [(res, d)], rows⟩

/-- The shared attributes of two rows: whether no decided value differs and no attribute is
missing, and the equalities needed where a value is not decided (Racket's `join/e`, one
pair). Every attribute is visited, as the `for` loop this replaces did, so a refusal of
`mk` is not skipped. -/
def sJoinEqs (ks : Kinds) (a b : SRow) : List String → Except String (Bool × List Term)
  | [] => .ok (true, [])
  | c :: cs => do
    let (ok, es) ← (match a.lookup c, b.lookup c with
      | some (.val x), some (.val y) => .ok (x == y, [])
      | some x, some y => do return (true, [← mk ks "=" [x, y]])
      | _, _ => .ok (false, []) : Except String (Bool × List Term))
    let (ok', es') ← sJoinEqs ks a b cs
    return (ok && ok', es ++ es')

/-- Two rows joined: the merged row (decided values from the right where shared), present
when both are and the shared values are equal; `none` when they cannot match. -/
def sJoinPair (ks : Kinds) (shared : List String) (ra rb : SRow × Term) :
    Except String (Option (SRow × Term)) := do
  let (ok, eqs) ← sJoinEqs ks ra.1 rb.1 shared
  if ok then
    let row : SRow := ra.1.map (fun (c, x) =>
        if shared.contains c then
          match rb.1.lookup c with
          | some (.val y) => (c, .val y)
          | _ => (c, x)
        else (c, x)) ++
      rb.1.filter fun (c, _) => !shared.contains c
    return some (row, ← sApply ks "and" (ra.2 :: rb.2 :: eqs))
  else return none

/-- One left row against every right row, in order. -/
def sJoinWith (ks : Kinds) (shared : List String) (ra : SRow × Term) :
    List (SRow × Term) → Except String (List (SRow × Term))
  | [] => .ok []
  | rb :: rbs => do
    let p ← sJoinPair ks shared ra rb
    let rest ← sJoinWith ks shared ra rbs
    return match p with
      | some q => q :: rest
      | none => rest

/-- Every left row against every right row, left rows outer. -/
def sJoinRows (ks : Kinds) (shared : List String) (srows : List (SRow × Term)) :
    List (SRow × Term) → Except String (List (SRow × Term))
  | [] => .ok []
  | ra :: rs => do
    let here ← sJoinWith ks shared ra srows
    let rest ← sJoinRows ks shared srows rs
    return here ++ rest

/-- Natural join symbolically (Racket's `join/e`): a shared attribute decided on both sides
is compared now; otherwise the pair is present only when the two are equal. -/
def sJoin (ks : Kinds) (r s : SRel) : Except String SRel := do
  let h ← Finrel.joinHeading r.heading s.heading
  let shared := r.heading.attrs.filter s.heading.attrs.contains
  return ⟨h, ← sJoinRows ks shared s.rows r.rows⟩

/-! ## A condition over the symbolic candidate -/

/-- `t` read through the heading `h`: each attribute of `h` with `t`'s value (the row
`ofFinrel` builds). `t` fits `h` when it is this tuple. -/
def fitTuple (h : Heading) (t : Tuple) : Tuple :=
  Tuple.ofPairs (h.map fun (a, _) => (a, (t.get? a).getD default))

/-- A finite relation as a symbolic one: its values known, every row present. No float, no
attribute twice, every tuple fits the heading. -/
def ofFinrel (r : Finrel) : Except String SRel := do
  if r.heading.attrs.eraseDups.length != r.heading.length then
    throw "φ: a relation names an attribute twice"
  if r.tuples.any (·.any (·.2.isFloat)) then throw "φ: a float (floats are not in φ's first version)"
  if r.tuples.any fun t => t != fitTuple r.heading t then
    throw "φ: a tuple does not fit its relation's heading"
  return ⟨r.heading, r.tuples.map fun t => (r.heading.map fun (a, _) => (a, .val ((t.get? a).getD default)), tt)⟩

/-- What a condition at one level reads: the environment of the statement it is in, the
cells' kinds, and the symbolic relations it can name. A solution set's condition has a
marker (the operand as written, the evaluator's target) and the symbolic candidate; a
multi solution set's condition has no marker and names its members, each bound to its
symbolic candidate. -/
structure Ctx where
  env : Env
  kinds : Kinds
  cand : Option (Expr × SRel)
  named : List (String × SRel) := []

/-- The evaluator's targets in this condition: the marker, if there is one. -/
def Ctx.tg (c : Ctx) : List Expr :=
  match c.cand with
  | some (m, _) => [m]
  | none => []

/-- The environment of a condition's leaves (`inCondition`, with every candidate bound to
an empty relation of its heading, which no leaf reads): the candidate for a solution set
(`σ_sol`), the members after a `%leaf` mark for a multi solution set (`bindDb`). -/
def Ctx.condEnv (c : Ctx) : Env :=
  match c.cand with
  | some (_, R) => inCondition ((candidateName, .finrel (Finrel.ofTuples R.heading [])) :: c.env)
  | none => inCondition (bindDb (c.named.map fun p => (p.1, Finrel.ofTuples p.2.heading [])) c.env)

/-- `g` is the candidate's placeholder or a member's name. -/
def Ctx.isBound (c : Ctx) (g : Expr) : Bool :=
  g.beq (.name candidateName) || c.named.any fun p => g.beq (.name p.1)

/-- A leaf of this condition: it mentions no target and holds no solution-set form. -/
def Ctx.isLeaf (c : Ctx) (f : Expr) : Bool :=
  (c.tg.all fun m => !f.mentions m) && !f.hasSolForm

/-- A leaf, evaluated once, concretely (Racket's `candidate-leaf` and `member-leaf`). -/
def sLeaf (c : Ctx) (f : Expr) : Except String SRel :=
  if c.isLeaf f then do
    if f.anySub c.isBound then
      throw "φ: a leaf reads the candidate's placeholder or a member"
    ofFinrel (← (← Expr.eval c.condEnv c.tg f).asFinrel "a leaf")
  else .error "φ: this relational expression is not in φ's fragment"

/-- A relational expression over the candidate (`Rasso.Phi.Fragment`'s `PhiExpr`), read as structure
first, then as a leaf. -/
def sRel (c : Ctx) (f : Expr) : Except String SRel :=
  if c.tg.any f.beq then
    match c.cand with
    | some (_, R) => .ok R
    | none => .error "φ: no candidate"
  else
  match f with
  | .name n =>
    match c.named.lookup n with
    | some R => .ok R
    | none => sLeaf c (.name n)
  | .gamma by_ ex res e => do
    let r ← sRel c e
    let ex ← if ex.hasSub then do
        let ex' ← ex.splice c.condEnv
        for a in ex'.subsetAttrs do
          if (r.heading.lookup a).isNone then throw s!"γ: has_subset's relation has {a}, which {r.heading.attrs} lacks"
        pure ex'
      else pure ex
    sGamma c.kinds by_ ex (res.getD gammaDefaultName) r
  | .extend res t e => do sExtend c.kinds res t (← sRel c e)
  | .nary .join es => do
    match ← es.attach.mapM fun ⟨e, _⟩ => sRel c e with
    | [] => throw "no operands"
    | r :: rs => rs.foldlM (sJoin c.kinds) r
  | f => sLeaf c f
termination_by sizeOf f
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ es›; omega)

/-- A condition as a Boolean term over the cells. -/
def sCond (c : Ctx) : Cond → Except String Term
  | .and cs => do mk c.kinds "and" (← cs.attach.mapM fun ⟨x, _⟩ => sCond c x)
  | .or cs => do mk c.kinds "or" (← cs.attach.mapM fun ⟨x, _⟩ => sCond c x)
  | .not x => do mk c.kinds "not" [← sCond c x]
  | .hasSubset r => do
    let some (_, cand) := c.cand
      | throw "has_subset: a condition here reads no one candidate"
    let req ← (← Expr.eval (leafEnv c.condEnv) [] r).asFinrel "has_subset"
    let req ← ofFinrel req
    let terms ← req.rows.mapM fun (row, _) => do
      let pairs := row.filterMap fun (a, t) => (decided? t).map (a, ·)
      sHas c.kinds (cand.rows.map (·.1)) pairs
    mk c.kinds "and" terms
  | .expr e => do
    let r ← sRel c e
    match r.heading, r.rows with
    | [(a, _)], [(row, g)] =>
      unless isTrue g do
        throw "φ: the condition's one tuple is present only under a condition on the assignment"
      let some v := row.lookup a | throw "scalar: malformed tuple"
      let ks ← termKinds c.kinds v
      unless subKinds ks [.bool] do throw "a condition: its value may not be a bool"
      return v
    | h, rows => throw s!"scalar: needs one attribute and one tuple, got {h.attrs} and {rows.length} tuples"
termination_by x => sizeOf x
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-! ## The simplifier (Racket's `simp`) -/

/-- `and`/`or` of simplified operands: nested ones flattened, identities dropped, an
absorbing operand absorbs. -/
def simpFlat (op : String) (ident absorb : Term) (ss : List Term) : Term :=
  let ys := ss.flatMap fun s => match s with
    | .call o zs => if o == op then zs else [s]
    | s => if s.beq ident then [] else [s]
  if ys.any (·.beq absorb) then absorb
  else match ys with
    | [] => ident
    | [y] => y
    | ys => .call op ys

def simpNot : Term → Term
  | .val (.bool b) => .val (.bool !b)
  | s => .call "not" [s]

/-- Flatten nested `and`/`or`, drop their identities, absorb, fold `not` of a constant. -/
def simpTerm : Term → Term
  | .call "and" xs => simpFlat "and" (.val (.bool true)) (.val (.bool false)) (xs.attach.map fun ⟨x, _⟩ => simpTerm x)
  | .call "or" xs => simpFlat "or" (.val (.bool false)) (.val (.bool true)) (xs.attach.map fun ⟨x, _⟩ => simpTerm x)
  | .call "not" [x] => simpNot (simpTerm x)
  | .call op xs => .call op (xs.attach.map fun ⟨x, _⟩ => simpTerm x)
  | t => t
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ xs›; omega)

/-! ## φ -/

/-- φ's result. -/
structure Flat where
  /-- The solution set's heading: Data, then Decision. -/
  heading : Heading
  /-- The Decision attributes. -/
  decision : Heading
  /-- The symbolic candidate: Data tuple `i` with its cells, in Racket's numbering. -/
  symI : List SRow
  /-- Each cell and its Decision attribute's domain. -/
  cells : Heading
  /-- The conditions, unrolled and simplified. -/
  term : Term
  deriving Inhabited

def Flat.rel (F : Flat) : Unrel := ⟨F.cells, F.term⟩

/-- A Data value whose printed form `racketText` gives as Racket's `~s` does. -/
def printSafe : Value → Bool
  | .symbol s => racketSymbolText s == s
  | .string s => s.toList.all fun c => c.toNat ≥ 32 && c.toNat < 127 && c != '"' && c != '\\'
  | .float _ => false
  | _ => true

/-- Racket's `tuple<?` over the given attributes, by `racketValueLt`. -/
def tupleLt (attrs : List String) (s t : Tuple) : Bool :=
  match attrs with
  | [] => false
  | a :: as =>
    let x := (s.get? a).getD default
    let y := (t.get? a).getD default
    if racketValueLt x y then true else if racketValueLt y x then false else tupleLt as s t

/-- Replace each attribute of the term with a term from the map (the Decision's `p` read
over one Data tuple's cells). -/
def substAttrs (m : List (String × Term)) : Term → Term
  | .attr a => (m.lookup a).getD (.attr a)
  | .call op xs => .call op (xs.attach.map fun ⟨x, _⟩ => substAttrs m x)
  | t => t
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ xs›; omega)

/-- The ω_sol of a chain, evaluated as the evaluator evaluates it: the Data, the Decision,
and the Decision's tuples (which also checks its term `p` on every assignment). -/
def omegaOf (p : Program) (ch : Chain) : Except String (Finrel × Unrel × List Tuple) := do
  let env ← envAt p ch.stmt
  let data ← (← Expr.eval env [] ch.data).asFinrel "ω_sol data"
  let u ← (← Expr.eval env [] ch.decision).asUnrel
  for a in u.heading.attrs do
    if data.attrs.contains a then throw s!"ω_sol: {a} is both a data and a decision attribute"
  let picks ← u.tuples
  return (data, u, picks)

/-- A cell's name: Decision attribute `a` of copy `i` (Racket's `phi` without a prefix). -/
def cellName (a : String) (i : Nat) : String := a ++ toString i

/-- φ of a chain of program `p`: a statement's own, the operand of an `ℰ_sol`, or a member
of a multi solution set. `nm a i` names the cell of Decision attribute `a`, copy `i`
(`cellName` for a solution set; a member's prefix in a multi solution set). -/
def phiOf (nm : String → Nat → String) (p : Program) (ch : Chain) : Except String Flat := do
  let (data, u, _) ← omegaOf p ch
  -- no float, and printed forms the numbering can trust
  for t in data.tuples do
    for (_, v) in t do
      unless printSafe v do throw s!"φ: the data value {racketText v} (a float, or a printed form not checked)"
  -- cells
  -- the shape φ's proofs read
  let heading := data.heading ++ u.heading
  if heading.attrs.eraseDups.length != heading.length then
    throw "φ: the solution set names an attribute twice"
  if data.tuples.any fun t => t != fitTuple data.heading t then
    throw "φ: a Data tuple does not fit its heading"
  let rows := data.tuples.mergeSort fun s t => !tupleLt data.attrs t s
  let idx := (List.range rows.length).map (· + 1)
  let cells : Heading := idx.flatMap fun i => u.heading.map fun (a, d) => (nm a i, d)
  if cells.attrs.eraseDups.length != cells.length then throw "φ: two cells would have one name"
  let kinds ← cellKinds cells
  let symI : List SRow := (rows.zip idx).map fun (t, i) =>
    data.heading.map (fun (a, _) => (a, .val ((t.get? a).getD default))) ++
    u.heading.map fun (a, _) => (a, .attr (nm a i))
  let cand : SRel := ⟨heading, symI.map (·, tt)⟩
  -- the Decision's own term, on every copy (its attributes read as that copy's cells)
  let pTerms : List Term :=
    if isTrue u.term then [] else
    (idx.map fun i => substAttrs (u.heading.map fun (a, _) => (a, .attr (nm a i))) u.term)
  for a in u.term.attrs do
    unless u.heading.attrs.contains a do throw s!"φ: the Decision's term reads {a}, not a Decision attribute"
  -- the conditions, inner first, each in its own statement's environment
  let conds ← ch.levels.mapM fun lv => do
    let env ← envAt p lv.stmt
    lv.cond.checkSubsets env heading
    sCond ⟨env, kinds, some (lv.marker, cand), []⟩ lv.cond
  return ⟨heading, u.heading, symI, cells, simpTerm (.call "and" (pTerms ++ conds))⟩

/-- φ of statement `k` of program `p` (from 0). -/
def phi (p : Program) (k : Nat) : Except String Flat := do
  let some ch := statementChain p k | throw "φ: this statement is not in φ's fragment"
  phiOf cellName p ch

/-! ## Back from an assignment -/

/-- The candidate an assignment of the cells gives (Racket's `substitute`). -/
def substitute (F : Flat) (x : Tuple) : Finrel :=
  Finrel.ofTuples F.heading (F.symI.map fun row => Tuple.ofPairs (row.map fun (a, t) =>
    (a, match t with
      | .attr c => (x.get? c).getD default
      | .val v => v
      | _ => default)))

/-- What Lean's evaluator does to one candidate of chain `ch` (theorem B's reference): the
Decision's term on every copy, then the conditions from the innermost out, each in its
statement's environment with its marker as the target, stopping at the first false. -/
def acceptsOf (p : Program) (ch : Chain) (cand : Finrel) : Except String Bool := do
  let (_, u, _) ← omegaOf p ch
  for t in cand.tuples do
    unless ← u.term.holds (t.restrict u.heading.attrs |> Tuple.ofPairs) do return false
  for lv in ch.levels do
    let env ← envAt p lv.stmt
    unless ← lv.cond.eval (inCondition ((candidateName, .finrel cand) :: env)) [lv.marker] do
      return false
  return true

/-- `acceptsOf` for the chain of statement `k`. -/
def accepts (p : Program) (k : Nat) (cand : Finrel) : Except String Bool := do
  let some ch := statementChain p k | throw "φ: this statement is not in φ's fragment"
  acceptsOf p ch cand

/-- The commuting square, by trying every assignment: (assignments, mismatches between the
flat term and `accepts`, mismatches between the satisfying substitutes and the candidates
Lean's evaluator gives). A refusal on either side is a mismatch. -/
def checkSquare (p : Program) (k : Nat) : Except String (Nat × Nat × Nat) := do
  let F ← phi p k
  let xs ← Unrel.assignments F.cells
  let mut bad := 0
  let mut sat : List Finrel := []
  for x in xs do
    let lhs := F.term.holds x
    let rhs := accepts p k (substitute F x)
    match lhs, rhs with
    | .ok a, .ok b => if a != b then bad := bad + 1
    | _, _ => bad := bad + 1
    if let .ok true := lhs then sat := sat ++ [substitute F x]
  -- the evaluator's own candidates
  let env ← runProgram (p.take (k + 1))
  let some (_, v) := env.getLast? | throw "no statement"
  let s ← v.asSol
  let same (r t : Finrel) : Bool := r.tuples == t.tuples
  let missing := (s.candidates.filter fun c => !sat.any (same c)).length +
    (sat.filter fun c => !s.candidates.any (same c)).length
  let missing := missing + (if s.candidates.length == sat.length then 0 else 1)
  return (xs.length, bad, missing)

/-! ## The ℰ_sol key -/

/-- Statement `j` is `ℰ_sol[c, key](e)` with a key, and `e` unfolds, through the earlier
statements, to a chain: the chain, the operand as written, and the key. -/
def keyOf (p : Program) (j : Nat) : Option (Chain × Expr × Expr) :=
  match p[j]? with
  | some (_, .enumSol _ (some (_, key)) e) =>
    (chainOf ((programChains p).take j).reverse j e).map fun ch => (ch, e, key)
  | _ => none

/-- The key of statement `j` as one term over the cells of its operand's φ (Racket's
`phi-objective`): read as the evaluator reads it, in the statement's environment with the
operand as the target, one tuple with one attribute. -/
def phiKey (p : Program) (j : Nat) : Except String (Flat × Term) := do
  let some (ch, e, key) := keyOf p j
    | throw "φ: this statement is not an ℰ_sol with a key over a solution set in φ's fragment"
  let F ← phiOf cellName p ch
  let env ← envAt p j
  key.checkSubsets env F.heading
  let kinds ← cellKinds F.cells
  let r ← sRel ⟨env, kinds, some (e, ⟨F.heading, F.symI.map (·, tt)⟩), []⟩ key
  match r.heading, r.rows with
  | [(a, _)], [(row, g)] =>
    unless isTrue g do
      throw "φ: the key's one tuple is present only under a condition on the assignment"
    let some v := row.lookup a | throw "scalar: malformed tuple"
    return (F, simpTerm v)
  | h, rows => throw s!"scalar: needs one attribute and one tuple, got {h.attrs} and {rows.length} tuples"

/-- What Lean's evaluator computes as the key of one candidate (theorem K's reference). -/
def keyValue (p : Program) (j : Nat) (cand : Finrel) : Except String Value := do
  let some (_, e, key) := keyOf p j | throw "φ: this statement is not an ℰ_sol with a key"
  let env ← envAt p j
  scalar (← key.eval (inCondition ((candidateName, .finrel cand) :: env)) [e])

/-- Theorem K by trying every assignment: (assignments, mismatches between the key term and
`keyValue`, items of the evaluator's own `ℰ_sol` whose key is not the key term's value on
an assignment giving that candidate). A refusal on either side is a mismatch. -/
def checkKeySquare (p : Program) (j : Nat) : Except String (Nat × Nat × Nat) := do
  let (F, t) ← phiKey p j
  let xs ← Unrel.assignments F.cells
  let mut bad := 0
  for x in xs do
    match t.eval x, keyValue p j (substitute F x) with
    | .ok a, .ok b => if a != b then bad := bad + 1
    | _, _ => bad := bad + 1
  -- the evaluator's own items
  let env ← runProgram (p.take (j + 1))
  let some (_, v) := env.getLast? | throw "no statement"
  let .cseq _ items := v | throw "φ: the statement is not an ℰ_sol"
  let mut badItems := 0
  for (r, ks) in items do
    let ok := xs.any fun x => (substitute F x).tuples == r.tuples && (t.eval x).toOption.map (·) == ks.head?
    unless ok do badItems := badItems + 1
  return (xs.length, bad, badItems)

/-! ## Multi solution sets -/

/-- A condition on a multi solution set: the statement it is written in, and the
condition (the `ω_msol`'s own, or a `σ_msol`'s). -/
structure MLevel where
  stmt : Nat
  cond : Cond

/-- A multi solution set as φ reads it: `ω_msol` written at statement `stmt`, each member
unfolding to a solution set's chain, then its conditions from the inside out. -/
structure MChain where
  stmt : Nat
  members : List (String × Chain)
  levels : List MLevel

/-- The multi solution set chain of `f`, written at statement `i`. `known` holds the
earlier statements' solution set chains and `mknown` their multi solution set chains,
latest first. -/
def mchainOf (known : List (String × Option Chain)) (mknown : List (String × Option MChain))
    (i : Nat) : Expr → Option MChain
  | .omegaMsol ms c => do
    let chs ← ms.mapM fun (n, e) => (chainOf known i e).map (n, ·)
    some ⟨i, chs, c.toList.map (⟨i, ·⟩)⟩
  | .sigmaMsol c e => (mchainOf known mknown i e).map fun mc => { mc with levels := mc.levels ++ [⟨i, c⟩] }
  | .name n => (mknown.lookup n).bind id
  | _ => none

/-- The multi solution set chain of every statement, in order. -/
def programMChains (p : Program) : List (String × Option MChain) :=
  (p.zipIdx.foldl (fun mk ((n, f), i) =>
    (n, mchainOf ((programChains p).take i).reverse mk i f) :: mk) []).reverse

/-- The multi solution set chain of statement `k`, if it is in the fragment. -/
def statementMChain (p : Program) (k : Nat) : Option MChain :=
  ((programMChains p)[k]?).bind (·.2)

/-- The cell of Decision attribute `a`, copy `i`, of member `n` (Racket's `phi #:prefix`). -/
def memberCell (n : String) (a : String) (i : Nat) : String := n ++ "_" ++ a ++ "_" ++ toString i

/-- φ's result for a multi solution set: each member's φ, all the cells, one term. -/
structure MFlat where
  members : List (String × Flat)
  cells : Heading
  term : Term
  deriving Inhabited

/-- Names a multi solution set's member may not have: the evaluator's own bindings in a
condition's environment. -/
def reservedNames : List String := [candidateName, leafName, inConditionName]

/-- A member's symbolic candidate. -/
def Flat.sym (F : Flat) : SRel := ⟨F.heading, F.symI.map (·, tt)⟩

/-- φ of a multi solution set chain. -/
def phiMsolOf (p : Program) (mc : MChain) : Except String MFlat := do
  if mc.members.isEmpty then throw "ω_msol: needs at least one member"
  let names := mc.members.map (·.1)
  if names.contains "I" then throw "ω_msol: no member may be named I"
  if names.eraseDups.length != names.length then throw "φ: two members have one name"
  if names.any reservedNames.contains then throw "φ: a member has a name the evaluator reserves"
  let Fs ← mc.members.mapM fun (n, ch) => do return (n, ← phiOf (memberCell n) p ch)
  let cells : Heading := Fs.flatMap (·.2.cells)
  if cells.attrs.eraseDups.length != cells.length then throw "φ: two cells would have one name"
  let kinds ← cellKinds cells
  let named := Fs.map fun p => (p.1, p.2.sym)
  let conds ← mc.levels.mapM fun lv => do
    let env ← envAt p lv.stmt
    sCond ⟨env, kinds, none, named⟩ lv.cond
  return ⟨Fs, cells, simpTerm (.call "and" (Fs.map (·.2.term) ++ conds))⟩

/-- φ of statement `k`, a multi solution set. -/
def phiMsol (p : Program) (k : Nat) : Except String MFlat := do
  let some mc := statementMChain p k | throw "φ: this statement is not a multi solution set in φ's fragment"
  phiMsolOf p mc

/-- The database an assignment gives: each member's candidate. -/
def msolSubstitute (M : MFlat) (x : Tuple) : Db := M.members.map fun p => (p.1, substitute p.2 x)

/-- What Lean's evaluator does to one database of a multi solution set chain (theorem
M's reference): each member's candidate through its chain, then the conditions from the
inside out, each in its statement's environment with the database bound, stopping at the
first false. -/
def acceptsMsolOf (p : Program) (mc : MChain) (db : Db) : Except String Bool := do
  for (n, ch) in mc.members do
    let some r := db.lookup n | throw s!"no member {n} in the database"
    unless ← acceptsOf p ch r do return false
  for lv in mc.levels do
    let env ← envAt p lv.stmt
    unless ← lv.cond.eval (inCondition (bindDb db env)) [] do return false
  return true

/-- `acceptsMsolOf` for the chain of statement `k`. -/
def acceptsMsol (p : Program) (k : Nat) (db : Db) : Except String Bool := do
  let some mc := statementMChain p k | throw "φ: this statement is not a multi solution set in φ's fragment"
  acceptsMsolOf p mc db

/-- Theorem M by trying every assignment: (assignments, mismatches between the flat term and
`acceptsMsol`, mismatches between the satisfying databases and the databases Lean's
evaluator gives). A refusal on either side is a mismatch. -/
def checkSquareMsol (p : Program) (k : Nat) : Except String (Nat × Nat × Nat) := do
  let M ← phiMsol p k
  let xs ← Unrel.assignments M.cells
  let mut bad := 0
  let mut sat : List Db := []
  for x in xs do
    let lhs := M.term.holds x
    let rhs := acceptsMsol p k (msolSubstitute M x)
    match lhs, rhs with
    | .ok a, .ok b => if a != b then bad := bad + 1
    | _, _ => bad := bad + 1
    if let .ok true := lhs then sat := sat ++ [msolSubstitute M x]
  let env ← runProgram (p.take (k + 1))
  let some (_, v) := env.getLast? | throw "no statement"
  let m ← v.asMsol
  let same (a b : Db) : Bool := a.length == b.length &&
    (a.zip b).all fun ((n, r), (n', t)) => n == n' && r.tuples == t.tuples
  let missing := (m.candidates.filter fun c => !sat.any (same c)).length +
    (sat.filter fun c => !m.candidates.any (same c)).length
  let missing := missing + (if m.candidates.length == sat.length then 0 else 1)
  return (xs.length, bad, missing)

/-! ## The ℰ_msol key -/

/-- Statement `j` is `ℰ_msol[c, key](e)` with a key, and `e` unfolds to a multiple solution
set chain: the chain and the key. -/
def mkeyOf (p : Program) (j : Nat) : Option (MChain × Expr) :=
  match p[j]? with
  | some (_, .enumMsol _ (some (_, key)) e) =>
    (mchainOf ((programChains p).take j).reverse ((programMChains p).take j).reverse j e).map (·, key)
  | _ => none

/-- The key of statement `j` as one term over the cells of its operand's φ (Racket's
`msol-objective`): read as the evaluator reads it, in the statement's environment with the
database bound and no target, one tuple with one attribute. -/
def phiMsolKey (p : Program) (j : Nat) : Except String (MFlat × Term) := do
  let some (mc, key) := mkeyOf p j
    | throw "φ: this statement is not an ℰ_msol with a key over a multi solution set in φ's fragment"
  let M ← phiMsolOf p mc
  let env ← envAt p j
  let kinds ← cellKinds M.cells
  let r ← sRel ⟨env, kinds, none, M.members.map fun q => (q.1, q.2.sym)⟩ key
  match r.heading, r.rows with
  | [(a, _)], [(row, g)] =>
    unless isTrue g do
      throw "φ: the key's one tuple is present only under a condition on the assignment"
    let some v := row.lookup a | throw "scalar: malformed tuple"
    return (M, simpTerm v)
  | h, rows => throw s!"scalar: needs one attribute and one tuple, got {h.attrs} and {rows.length} tuples"

/-- What Lean's evaluator computes as the key of one database (the reference). -/
def keyValueMsol (p : Program) (j : Nat) (db : Db) : Except String Value := do
  let some (_, key) := mkeyOf p j | throw "φ: this statement is not an ℰ_msol with a key"
  let env ← envAt p j
  scalar (← key.eval (inCondition (bindDb db env)) [])

/-- The ℰ_msol key by trying every assignment: (assignments, mismatches between the key term
and `keyValueMsol`). A refusal on either side is a mismatch. -/
def checkKeySquareMsol (p : Program) (j : Nat) : Except String (Nat × Nat) := do
  let (M, t) ← phiMsolKey p j
  let xs ← Unrel.assignments M.cells
  let mut bad := 0
  for x in xs do
    match t.eval x, keyValueMsol p j (msolSubstitute M x) with
    | .ok a, .ok b => if a != b then bad := bad + 1
    | _, _ => bad := bad + 1
  return (xs.length, bad)

end Rasso.Phi
