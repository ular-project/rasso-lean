import Rasso.Term
import Rasso.Project

/-!
# Rasso: the evaluator

Runs the forms (`Rasso.Form`), the program as the JSON surface reads it. A program is a
list of definitions; each is evaluated in the environment of the ones before it.

What a value can be (Racket's `algebra-types`, the slice of them used here):

* `finrel`: a finite relation (`Finrel`).
* `unrel`: an unrestricted relation (`Unrel`), a heading and one Boolean term.
* `tseq`: a sequence of tuples, what ℰ gives from a finite relation; `forget` takes it
  back to a finite relation.
* `sol`: a solution set: a finite relation, a decision heading, and its members (each a
  function from the data's tuples to decision tuples, held as its graph, a finite
  relation over both headings).
* `cseq`: a sequence of candidates, what ℰ_sol gives; `flatten` takes it to a sequence
  of tuples, as Racket's does.
* `msol`: a multi solution set: named members, and its candidates (each a database
  binding every member's name to one of that member's graphs).
* `dbseq`: a sequence of databases, what ℰ_msol gives; `flatten_msol` takes it to a
  database.
* `db`: a database, relation names bound to finite relations; `db_ref` reads one.

A condition (`Cond`) holds when each relation in it has one attribute and one tuple,
and its value is `true` (`holds E` is `scalar E = true`); `and`, `or`, `not` combine them. `scalar E` is the value of E's one attribute in
its one tuple, and is refused otherwise.

Evaluated so far: ω in its three shapes, σ, π, ρ, ⋈, ×, ∪, ∩, − on finite relations
(σ, ρ, ⋈, ×, ∪, ∩, − also on unrestricted ones), γ, extend, ℰ, forget, lift, ω_sol, σ_sol,
ρ_sol, ⋈_sol, ℰ_sol, flatten, ω_msol, σ_msol, ℰ_msol, flatten_msol, db_ref. π of a sequence of tuples; ℰ of an unrestricted relation whose domains are finite.
∪, ∩ and − refuse operands whose headings differ, and × operands that share an attribute,
on finite and unrestricted relations alike. ω[H](p) and σ_p refuse a term that reads an
attribute outside the heading (as Racket's `check-term-attrs!`).
π of an unrestricted relation is evaluated when every dropped attribute is in a class:
finite domains, dense order, equality, or linear arithmetic (`Rasso.Project`).
Refused when met: `lateral`, and `list` in a term.

`has_subset(R)`, as Racket gives it:

* As a condition of σ_sol, it holds when every tuple of `R` is a tuple of the candidate.
  As a condition of a multi solution set it is refused: it reads one candidate.
* In γ's expression, it is true when every tuple of `R` matches some tuple of the group
  on `R`'s attributes. `R` is evaluated first and put in as a literal (`Agg.splice`);
  an attribute of `R` that γ's operand lacks is refused.
* `R` is a **leaf**: it is evaluated with no targets and in the **leaf environment**, the
  program's environment without the condition's own bindings (`leafEnv`). So an `R` that
  reads the candidate, or a member of a multi solution set, is refused, as in
  Racket's `candidate-leaf` and `member-leaf`. `R`'s value must be a finite relation.
* In σ_sol's condition and ℰ_sol's key, every `has_subset(R)` that the condition's
  structure reaches (`and`, `or`, `not`, γ, extend, join) must have the solution set's
  attributes, and each pair of domains must intersect, as a join's do. This is checked
  before any candidate is tested (`Cond.checkSubsets`), so it is refused even with no
  candidates, as Racket's `prepare-E` does.

Known differences from Racket: an attribute of `R` that γ's operand lacks is always
refused (Racket refuses only when a comparison reaches it); and a multi solution set
with no databases does not refuse a `has_subset` condition, or a `has_subset` relation
in γ that is not a finite relation (Racket checks those when it builds the condition);
and a bare member name that is also a statement's name is read as the statement here,
refused in Racket.

Conventions:

* Solution sets and multi solution sets are held by listing their members: a member
  of a solution set is a whole function, so this is exponential in the data, and is
  meant for small examples only. The decision's domains must be finite.
* Members are listed in a fixed order (the canonical order of the data's tuples and of
  the decision tuples), and ℰ breaks ties in that order. Which tie wins is not meant to
  be part of rasso's meaning. ℰ with no key gives that order.
* In a condition or a key of a solution set, each occurrence of the operand's form (its
  name, or the form written inline) is the candidate, as in Racket's evaluator;
  in a multi solution set, each member's name names that member's candidate. They
  shadow the program's own definitions. Rasso lets any operator read the candidate;
  Racket reads it only through γ, extend and join.
* The evaluator is total (well-founded recursion on the form), so theorems can state
  what a program computes. To keep the recursion on sub-forms, a condition is not
  rewritten before it is evaluated:
  the evaluator carries the operands as targets, and a position equal to a target
  evaluates to the candidate. This agrees with replacing first, except possibly when
  a solution set is nested inside a condition and its operand mentions the outer
  operand.
* ℰ's count is mandatory; Racket's `all` is the largest 64-bit integer, 2^63 − 1.
* The forms give ℰ one key; the evaluator takes a list of keys, each with its own
  direction, for when the surface has one.
* `join` of finite and unrestricted relations lifts the finite ones (their tuples as a
  disjunction); so does `lift`.
-/

namespace Rasso

/-- The name the candidate is bound to in a solution set's condition or key: not a
name a program can write. -/
def candidateName : String := "%candidate"

/-- Racket's `all`, as a count. -/
def countAll : Nat := 2 ^ 63 - 1

def Count.toNat : Count → Nat
  | .all => countAll
  | .int k => k.toNat

/-- A database: relation names bound to finite relations. -/
abbrev Db := List (String × Finrel)

structure Sol where
  data : Finrel
  heading : Heading
  candidates : List Finrel
  deriving Inhabited

structure Msol where
  members : List (String × Heading)
  candidates : List Db
  deriving Inhabited

/-- A value a rasso expression can have. -/
inductive Val where
  | finrel (r : Finrel)
  | unrel (u : Unrel)
  | tseq (h : Heading) (ts : List (Tuple × List Value))
  | sol (s : Sol)
  | cseq (h : Heading) (rs : List (Finrel × List Value))
  | msol (m : Msol)
  | dbseq (members : List (String × Heading)) (dbs : List (Db × List Value))
  | db (d : Db)
  deriving Inhabited

/-- What a value is, in words (Racket's `carrier-text`). -/
def Val.sortText : Val → String
  | .finrel _ => "a finite relation" | .unrel _ => "an unrestricted relation" | .tseq .. => "a sequence of tuples"
  | .sol _ => "a solution set" | .cseq .. => "a sequence of candidates"
  | .msol _ => "a multi solution set" | .dbseq .. => "a sequence of databases"
  | .db _ => "a database"

abbrev Env := List (String × Val)

def Val.asFinrel (who : String) : Val → Except String Finrel
  | .finrel r => .ok r
  | v => .error s!"{who}: expected a finite relation, got {v.sortText}"

def Val.asUnrel : Val → Except String Unrel
  | .unrel u => .ok u
  | .finrel r => .ok r.toUnrel
  | v => .error s!"expected an unrestricted relation, got {v.sortText}"

def Val.asSol : Val → Except String Sol
  | .sol s => .ok s
  | v => .error s!"expected a solution set, got {v.sortText}"

def Val.asMsol : Val → Except String Msol
  | .msol m => .ok m
  | v => .error s!"expected a multi solution set, got {v.sortText}"


/-- Bound while a condition or a key is evaluated. -/
def inConditionName : String := "%condition"

def inCondition (env : Env) : Env := (inConditionName, .db []) :: env

/-- Marks where a multi solution set's member bindings end: what follows is the
environment the program's own forms see (`leafEnv`). Not a name a program can write. -/
def leafName : String := "%leaf"

def bindDb (db : Db) (env : Env) : Env := db.map (fun (n, r) => (n, .finrel r)) ++ (leafName, .db []) :: env

/-- The environment after the last `%leaf` mark, if there is one: the program's own
environment, outside every multi solution set's condition. -/
def afterLeaf : Env → Option Env
  | [] => none
  | (n, _) :: r => match afterLeaf r with
    | some e => some e
    | none => if n == leafName then some r else none

/-- The environment a leaf of a condition is evaluated in (Racket's `eval-form` in
`candidate-leaf` and `member-leaf`): without a multi solution set's member bindings,
the candidate, or the condition marker. -/
def leafEnv (env : Env) : Env :=
  ((afterLeaf env).getD env).filter fun p => p.1 != inConditionName && p.1 != candidateName

/-- A domain written back as a form's domain. -/
def Domain.toDomExpr : Domain → DomExpr
  | .kind k => .kind k
  | .range lo hi => .range lo hi
  | .set vs => .set vs

/-- A finite relation as a literal form (ω with rows), in its heading's order. -/
def Finrel.literal (r : Finrel) : Expr :=
  .omegaRows (r.heading.map fun (a, d) => (a, d.toDomExpr))
    (r.tuples.map fun t => r.heading.map fun (a, _) => (t.get? a).getD default)

/-- `has_subset(R)`'s heading rule (Racket's `check-subset-heading!`): `R` has the solution
set's attributes, and each pair of domains intersects, as a join's do. -/
def checkSubsetHeading (req : Finrel) (h : Heading) : Except String Unit := do
  let ra := req.attrs
  let ha := h.attrs
  unless ra.length == ha.length && ra.all ha.contains && ha.all ra.contains do
    throw s!"has_subset: the relation's attributes {ra} are not the solution set's {ha}"
  for (a, d) in req.heading do
    match h.lookup a with
    | some d' => let _ ← d.inter d'
    | none => throw s!"has_subset: no attribute {a} in the solution set"

/-- `scalar E`: the value of E's one attribute in its one tuple. -/
def scalar (v : Val) : Except String Value := do
  let r ← v.asFinrel "scalar"
  match r.attrs, r.tuples with
  | [a], [t] => match t.get? a with
    | some x => return x
    | none => throw "scalar: malformed tuple"
  | as, ts => throw s!"scalar: needs one attribute and one tuple, got {as} and {ts.length} tuples"

/-- Compare two key lists, each place in its own direction. -/
def cmpKeys : List Order → List Value → List Value → Ordering
  | d :: ds, v :: vs, w :: ws =>
    match Value.cmp v w with
    | .eq => cmpKeys ds vs ws
    | o => if d == .desc then o.swap else o
  | _, _, _ => .eq

/-- Order items by their keys (stable, so ties keep their order) and take `n`. -/
def sortTake {α : Type} (n : Nat) (dirs : List Order) (xs : List (α × List Value)) :
    List (α × List Value) :=
  (xs.mergeSort fun a b => cmpKeys dirs a.2 b.2 != .gt).take n

/-- Every way of picking one item from each list (in order). -/
def choices {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss => xs.flatMap fun x => (choices xss).map (x :: ·)

/-- Add a rank attribute to every tuple and union them. -/
def rankUnion (rank : String) (h : Heading) (rs : List Finrel) : Finrel :=
  Finrel.ofTuples (h ++ [(rank, .kind .int)])
    ((rs.zipIdx 1).flatMap fun (r, i) => r.tuples.map fun t => Tuple.ofPairs ((rank, .int i) :: t))

/-- ρ on a finite relation. -/
def Finrel.rename (ren : List (String × String)) (r : Finrel) : Except String Finrel := do
  Heading.renameCheck ren r.heading
  return Finrel.ofTuples (Finrel.renameHeading ren r.heading) (r.tuples.map (Finrel.renameTuple ren))

/-- ρ on a solution set, as Racket's `rename-sol`: the Data, the heading and every member
renamed. A solution set holds its members, so its conditions need no rewriting: they were
applied when it was built. Refused as ρ on its heading is: an old name that is not an
attribute (of the Data or the Decision), or two attributes given one name. -/
def Sol.rename (ren : List (String × String)) (s : Sol) : Except String Sol := do
  let _ ← (Finrel.ofTuples s.heading []).rename ren
  let data ← s.data.rename (ren.filter fun p => s.data.attrs.contains p.1)
  let cands ← s.candidates.mapM fun c => (Finrel.ofTuples s.heading c.tuples).rename ren
  return ⟨data, s.heading.map fun (a, d) => ((ren.lookup a).getD a, d), cands⟩

/-! ## ⋈ on solution sets

Its meaning:
`U ⋈ V` has Data `J = Data_U ⋈ Data_V` and Decision `Decision_U ⋈ Decision_V`. A
function on `J` is a member when each of its slices along the Data attributes that V
adds (`G_U`) is a member of U, and each of its slices along those U adds (`G_V`) is a
member of V. The slices may differ: every copy of U is a member of U, as every row and
every column of a Latin square is a Latin vector. When `G_U` is empty, there is one
slice, the whole function.

Lean's solution sets hold their members, so the join is computed from them: a member of
U for each `G_U` group, and for each `G_V` group the members of V that agree with those
picks on the shared Decision attributes. Racket (`join-sol`) instead rewrites each side's
condition into γ regrouped by `G`. The two agree wherever Racket's lift is defined. Racket
refuses, "not yet implemented", a side's condition with `join`, `or`, `not`, `has` or
`has_subset`; Lean has nothing to rewrite, so it accepts those, with the meaning "holds in
every group".

Refused, as Racket refuses: an attribute that is Data on one side and decided on the
other (the Data/decision clash); a side whose Data the joined Data does not hold whole
in every group (the whole-Data check, Racket's `check-whole!`). -/

/-- A solution set's Decision heading: its heading without the Data attributes. -/
def Sol.decision (s : Sol) : Heading := s.heading.filter fun p => !s.data.attrs.contains p.1

/-- The groups of `J` by attributes `G`: the distinct values of `G` in `J`'s tuples, or
the one empty group when `G` is empty (even when `J` is empty). -/
def joinGroups (J : Finrel) (G : List String) : List Tuple :=
  if G.isEmpty then [[]] else dedup (J.tuples.map (·.restrict G))

/-- The whole-Data check (Racket's `check-whole!`): every group of `J` by `G` holds every tuple of the
side's Data, and `J` holds the side's Data at all. -/
def checkWhole (J : Finrel) (A : Sol) (G : List String) (aSide bSide : String) :
    Except String Unit := do
  let show_ (t : Tuple) := ", ".intercalate (t.map fun (a, v) => s!"{a} = {v}")
  let refuse (wh : String) (d : Tuple) : Except String Unit :=
    throw s!"join_sol: {wh} the {aSide} operand's data tuple {show_ d} has no match in the {bSide} operand's data. The {aSide} operand's conditions would be checked over part of its data"
  if J.tuples.isEmpty then
    match A.data.tuples with
    | d :: _ => refuse "the joined data is empty, so" d
    | [] => pure ()
  for g in joinGroups J G do
    for d in A.data.tuples do
      unless J.body.mem (d.merge g) do
        refuse (if G.isEmpty then "in the joined data," else s!"in the group {show_ g},") d

/-- The Decision part of a member's tuple at a Data tuple `d` (its attributes `as`). -/
def Sol.decisionAt (s : Sol) (m : Finrel) (d : Tuple) : Option Tuple :=
  (m.tuples.find? fun r => r.restrict s.data.attrs == d).map (·.restrict s.decision.attrs)

/-- `U ⋈ V` on solution sets. -/
def Sol.join (U V : Sol) : Except String Sol := do
  for (A, B, aSide, bSide) in [(U, V, "left", "right"), (V, U, "right", "left")] do
    for a in A.data.attrs do
      if B.decision.attrs.contains a then
        throw s!"join_sol: {a} is data in the {aSide} operand and decided in the {bSide}: a solution set's data and decision share no attribute"
  let J ← U.data.join V.data
  let dec ← Finrel.joinHeading U.decision V.decision
  let h := J.heading ++ dec
  let gU := V.data.attrs.filter fun a => !U.data.attrs.contains a
  let gV := U.data.attrs.filter fun a => !V.data.attrs.contains a
  checkWhole J U gU "left" "right"
  checkWhole J V gV "right" "left"
  let gsU := joinGroups J gU
  let gsV := joinGroups J gV
  -- a J tuple's U decision, under one member of U for each U-group
  let decU (picks : List (Tuple × Finrel)) (t : Tuple) : Except String Tuple :=
    match picks.lookup (t.restrict gU) with
    | none => throw "join_sol: internal: no group"
    | some m => match U.decisionAt m (t.restrict U.data.attrs) with
      | some x => pure x
      | none => throw "join_sol: internal: a member has no tuple for a data tuple"
  let decV (m : Finrel) (t : Tuple) : Except String Tuple :=
    match V.decisionAt m (t.restrict V.data.attrs) with
    | some x => pure x
    | none => throw "join_sol: internal: a member has no tuple for a data tuple"
  let mut cands : List Finrel := []
  for ps in choices (gsU.map fun _ => U.candidates) do
    let picks := gsU.zip ps
    -- for each V-group, the members of V that agree with the U picks there
    let mut options : List (List (Tuple × Finrel)) := []
    for g in gsV do
      let ts := J.tuples.filter fun t => t.restrict gV == g
      let ok ← V.candidates.filterM fun m => ts.allM fun t => do
        return (← decU picks t).agrees (← decV m t)
      options := options ++ [ok.map (g, ·)]
    for vs in choices options do
      let ts ← J.tuples.mapM fun t => do
        let some (_, m) := vs.find? (·.1 == t.restrict gV)
          | throw "join_sol: internal: no group"
        return (t.merge (← decU picks t)).merge (← decV m t)
      cands := cands ++ [Finrel.ofTuples h ts]
  return ⟨J, h, cands⟩

/-- ∩ (same attributes). -/
def Finrel.inter (r s : Finrel) : Except String Finrel := do
  r.sameHeading "∩" s
  return Finrel.ofTuples r.heading (r.tuples.filter s.body.mem)

/-- × (no attribute shared; then the same as ⋈). -/
def Finrel.product (r s : Finrel) : Except String Finrel := do
  Heading.disjoint "×" r.heading s.heading
  r.join s

/-- extend[res := t](R). -/
def Finrel.extend (res : String) (t : Term) (r : Finrel) : Except String Finrel := do
  if r.attrs.contains res then throw s!"extend: the attribute {res} is already in {r.attrs}"
  let some d := t.domain r.heading
    | throw "extend: the term gives no domain's values, so its result can't be an attribute"
  let ts ← r.tuples.mapM fun u => do return Tuple.ofPairs ((res, ← t.eval u) :: u)
  return Finrel.ofTuples (r.heading ++ [(res, d)]) ts

mutual
def Expr.eval (env : Env) (tg : List Expr) (f : Expr) : Except String Val :=
  -- a position that is a target (a candidate's operand, as a form) is the candidate
  if tg.any f.beq then
    match env.lookup candidateName with
    | some v => .ok v
    | none => .error "no candidate is bound"
  else match f with
  | .name n => match env.lookup n with
    | some v => .ok v
    | none => .error s!"{n} is not defined"
  | .omega hd => do return .unrel (Unrel.omega (← evalHeading env tg hd))
  | .omegaWhere hd t => do
    let h ← evalHeading env tg hd
    Heading.scoped "ω" h t
    return .unrel ⟨h, t⟩
  | .omegaRows hd rows => do
    let h ← evalHeading env tg hd
    let ts ← rows.mapM fun row => do
      if row.length != h.length then throw s!"ω: a row of {row.length} values for {h.length} attributes"
      for ((a, d), v) in h.zip row do
        if !d.mem v then throw s!"ω: {v} is not in the domain of {a}"
      return Tuple.ofPairs (h.attrs.zip row)
    return .finrel (Finrel.ofTuples h ts)
  | .select p e => do
    match ← e.eval env tg with
    | .finrel r =>
      Heading.scoped "σ" r.heading p
      return .finrel (← r.select p.holds)
    | v => return .unrel (← (← v.asUnrel).select p)
  | .project as e => do
    match ← e.eval env tg with
    | .tseq h ts =>
      -- π of a sequence keeps its order and each tuple's first place (Racket's t-project)
      if as.eraseDups.length != as.length then throw s!"π: {as} names an attribute twice"
      for a in as do
        unless h.attrs.contains a do throw s!"π: no attribute {a} in {h.attrs}"
      let kept := h.filter fun p => as.contains p.1
      let ts' := ts.foldl (fun acc (t, k) =>
        let u := t.restrict as
        if acc.any (·.1 == u) then acc else acc ++ [(u, k)]) []
      return .tseq kept ts'
    | .unrel u => return .unrel (← u.project as)
    | v => return .finrel (← (← v.asFinrel "π").project as)
  | .rename ren e => do
    match ← e.eval env tg with
    | .sol s => return .sol (← s.rename ren)
    | .finrel r => return .finrel (← r.rename ren)
    | v => return .unrel (← (← v.asUnrel).rename ren)
  | .nary op es => do
    let vs ← es.mapM (·.eval env tg)
    let allDrel := vs.all fun | .finrel _ => true | _ => false
    match op, vs with
    | _, [] => throw "no operands"
    | .lateral, _ => throw "lateral is not evaluated yet"
    | .join, v :: ws =>
      let isSol : Val → Bool := fun | .sol _ => true | _ => false
      if vs.any isSol then
        unless vs.all isSol do
          throw s!"join: both operands of ⋈ must be solution sets, or neither; got {vs.map Val.sortText}"
        return .sol (← ws.foldlM (fun acc w => do acc.join (← w.asSol)) (← v.asSol))
      if allDrel then
        let r ← v.asFinrel "join"
        return .finrel (← ws.foldlM (fun acc w => do acc.join (← w.asFinrel "join")) r)
      else
        return .unrel (← ws.foldlM (fun acc w => do acc.join (← w.asUnrel)) (← v.asUnrel))
    | .product, v :: ws =>
      if allDrel then
        let r ← v.asFinrel "×"
        return .finrel (← ws.foldlM (fun acc w => do acc.product (← w.asFinrel "×")) r)
      else
        return .unrel (← ws.foldlM (fun acc w => do acc.product (← w.asUnrel)) (← v.asUnrel))
    | .union, v :: ws =>
      if allDrel then
        return .finrel (← ws.foldlM (fun acc w => do acc.union (← w.asFinrel "∪")) (← v.asFinrel "∪"))
      else return .unrel (← ws.foldlM (fun acc w => do acc.union (← w.asUnrel)) (← v.asUnrel))
    | .intersect, v :: ws =>
      if allDrel then
        return .finrel (← ws.foldlM (fun acc w => do acc.inter (← w.asFinrel "∩")) (← v.asFinrel "∩"))
      else return .unrel (← ws.foldlM (fun acc w => do acc.inter (← w.asUnrel)) (← v.asUnrel))
    | .except, v :: ws =>
      if allDrel then
        return .finrel (← ws.foldlM (fun acc w => do acc.diff (← w.asFinrel "−")) (← v.asFinrel "−"))
      else return .unrel (← ws.foldlM (fun acc w => do acc.diff (← w.asUnrel)) (← v.asUnrel))
  | .gamma by_ ex res e => do
    -- with no result name, γ stands only in a condition or a key (as in Racket)
    if res.isNone && (env.lookup inConditionName).isNone then
      throw "gamma names no result; as a statement, write gamma[...][... -> res](...)"
    let r ← (← e.eval env tg).asFinrel "γ"
    -- has_subset's relations are evaluated first, as leaves, and put in as literals
    let ex ← if ex.hasSub then do
        let ex' ← ex.splice env
        for a in ex'.subsetAttrs do
          if (r.domainOf? a).isNone then throw s!"γ: has_subset's relation has {a}, which {r.attrs} lacks"
        pure ex'
      else pure ex
    return .finrel (← r.gamma by_ ex (res.getD gammaDefaultName))
  | .extend res t e => do return .finrel (← (← (← e.eval env tg).asFinrel "extend").extend res t)
  | .enum c key e => do
    -- ℰ of an unrestricted relation lists its tuples when its domains are finite
    let r ← match ← e.eval env tg with
      | .unrel u => pure (Finrel.ofTuples u.heading (← u.tuples))
      | v => v.asFinrel "ℰ"
    -- a key list(t, …) orders by each t in turn, as Racket's value<? orders lists
    let keys : List (Term × Order) := match key with
      | some (o, .call "list" ks) => ks.map (·, o)
      | some (o, k) => [(k, o)]
      | none => []
    let items ← r.tuples.mapM fun t => do return (t, ← keys.mapM fun (k, _) => k.eval t)
    return .tseq r.heading (sortTake c.toNat (keys.map (·.2)) items)
  | .forget e => do
    match ← e.eval env tg with
    | .tseq h ts => return .finrel (Finrel.ofTuples h (ts.map (·.1)))
    | v => throw s!"forget: expected a sequence of tuples, got {v.sortText}"
  | .lift e => do
    match ← e.eval env tg with
    | .finrel r => return .unrel r.toUnrel
    | .tseq h ts => return .unrel (Finrel.ofTuples h (ts.map (·.1))).toUnrel
    | v => throw s!"lift: expected a finite relation or a sequence of tuples, got {v.sortText}"
  | .omegaSol d dec => do
    let data ← (← d.eval env tg).asFinrel "ω_sol data"
    let u ← (← dec.eval env tg).asUnrel
    for a in u.heading.attrs do
      if data.attrs.contains a then throw s!"ω_sol: {a} is both a data and a decision attribute"
    let picks ← u.tuples
    let rows := data.tuples
    let h := data.heading ++ u.heading
    let cands := (choices (rows.map fun _ => picks)).map fun ps =>
      Finrel.ofTuples h ((rows.zip ps).map fun (t, p) => t.merge p)
    return .sol ⟨data, h, cands⟩
  | .sigmaSol c e => do
    let s ← (← e.eval env tg).asSol
    c.checkSubsets env s.heading
    let cands ← s.candidates.filterM fun r => c.eval (inCondition ((candidateName, .finrel r) :: env)) (e :: tg)
    return .sol { s with candidates := cands }
  | .enumSol c key e => do
    let s ← (← e.eval env tg).asSol
    Expr.checkKey env s.heading key
    let items ← s.candidates.mapM fun r => do
      match key with
      | some (_, k) => return (r, [← scalar (← k.eval (inCondition ((candidateName, .finrel r) :: env)) (e :: tg))])
      | none => return (r, [])
    return .cseq s.heading (sortTake c.toNat (key.toList.map (·.1)) items)
  | .flatten rank e => do
    -- a sequence of tuples, as Racket's flatten gives: each candidate's tuples in the
    -- heading's order, the candidates in the sequence's, each tuple with its rank
    match ← e.eval env tg with
    | .cseq h rs =>
      let sorted (r : Finrel) : List Tuple :=
        let row (t : Tuple) := h.map fun p => (t.get? p.1).getD default
        r.tuples.mergeSort fun t u => cmpKeys (h.map fun _ => .asc) (row t) (row u) != .gt
      match rank, rs with
      | none, [] => return .tseq h []
      | none, [(r, _)] => return .tseq h ((sorted r).map (·, []))
      | none, _ => throw "flatten without a rank: more than one relation"
      | some a, _ =>
        if h.attrs.contains a then throw s!"flatten: rank attribute {a} clashes with an attribute of the solution set"
        return .tseq (h ++ [(a, .kind .int)]) ((rs.zipIdx 1).flatMap fun ((r, _), i) =>
          (sorted r).map fun t => (Tuple.ofPairs ((a, .int i) :: t), []))
    | v => throw s!"flatten: expected a sequence of candidates, got {v.sortText}"
  | .omegaMsol ms c => do
    let sols ← evalMembers env tg ms
    if sols.isEmpty then throw "ω_msol: needs at least one member"
    if (sols.map (·.1)).eraseDups.length != sols.length then throw "ω_msol: two members have one name"
    let dbs := choices (sols.map fun (n, s) => s.candidates.map (n, ·))
    let dbs ← evalMsolCond env tg c dbs
    return .msol ⟨sols.map fun (n, s) => (n, s.heading), dbs⟩
  | .sigmaMsol c e => do
    let m ← (← e.eval env tg).asMsol
    return .msol { m with candidates := ← m.candidates.filterM fun db => c.eval (inCondition (bindDb db env)) tg }
  | .enumMsol c key e => do
    let m ← (← e.eval env tg).asMsol
    let items ← m.candidates.mapM fun db => do
      match key with
      | some (_, k) => return (db, [← scalar (← k.eval (inCondition (bindDb db env)) tg)])
      | none => return (db, [])
    return .dbseq m.members (sortTake c.toNat (key.toList.map (·.1)) items)
  | .flattenMsol rank e => do
    match ← e.eval env tg with
    | .dbseq ms dbs => match rank, dbs with
      | none, [] => return .db (ms.map fun (n, h) => (n, Finrel.ofTuples h []))
      | none, [(db, _)] => return .db db
      | none, _ => throw "flatten_msol without a rank: more than one database"
      | some a, _ =>
        -- as flatten: the rank attribute must be new to every member's heading
        if ms.any (fun m => m.2.attrs.contains a) then
          throw s!"flatten_msol: rank attribute {a} clashes with an attribute of a member"
        else return .db (ms.map fun (n, h) =>
          (n, rankUnion a h (dbs.map fun (db, _) => (db.lookup n).getD default)))
    | v => throw s!"flatten_msol: expected a sequence of databases, got {v.sortText}"
  | .dbRef n e => do
    match ← e.eval env tg with
    | .db db => match db.lookup n with
      | some r => return .finrel r
      | none => throw s!"db_ref: no relation {n} in the database"
    | v => throw s!"db_ref: expected a database, got {v.sortText}"
termination_by sizeOf f

def evalMembers (env : Env) (tg : List Expr) : List (String × Expr) → Except String (List (String × Sol))
  | [] => .ok []
  | (n, e) :: ms => do
    if n == "I" then throw "ω_msol: no member may be named I"
    return (n, ← (← e.eval env tg).asSol) :: (← evalMembers env tg ms)
termination_by x => sizeOf x

def evalMsolCond (env : Env) (tg : List Expr) : Option Cond → List Db → Except String (List Db)
  | none, dbs => .ok dbs
  | some c, dbs => dbs.filterM fun db => c.eval (inCondition (bindDb db env)) tg
termination_by c _ => sizeOf c

def evalHeading (env : Env) (tg : List Expr) : List (String × DomExpr) → Except String Heading
  | [] => .ok []
  | (a, d) :: h => do return (a, ← d.eval env tg) :: (← evalHeading env tg h)
termination_by x => sizeOf x

def DomExpr.eval (env : Env) (tg : List Expr) : DomExpr → Except String Domain
  | .kind k => .ok (.kind k)
  | .range lo hi => .ok (.range lo hi)
  | .set vs => .ok (.set vs)
  | .in_ e => do
    let r ← (← e.eval env tg).asFinrel "in"
    match r.attrs with
    | [a] => return Domain.ofValues (r.tuples.filterMap (·.get? a))
    | as => throw s!"in: the finite relation must have one attribute, it has {as}"
termination_by x => sizeOf x

def Cond.eval (env : Env) (tg : List Expr) : Cond → Except String Bool
  | .expr e => do asBool "a condition" (← scalar (← e.eval env tg))
  | .and cs => cs.attach.allM fun ⟨c, _⟩ => c.eval env tg
  | .or cs => cs.attach.anyM fun ⟨c, _⟩ => c.eval env tg
  | .not c => do return !(← c.eval env tg)
  | .hasSubset r => do
    let some (.finrel cand) := env.lookup candidateName
      | throw "has_subset: a condition here reads no one candidate"
    let req ← (← r.eval (leafEnv env) []).asFinrel "has_subset"
    return req.tuples.all fun t => cand.tuples.contains t
termination_by x => sizeOf x

/-- γ's expression with each `has_subset(R)` replaced by the literal of `R`'s value. -/
def Agg.splice (env : Env) : Agg → Except String Agg
  | .hasSubset r => do return .hasSubset (← (← r.eval (leafEnv env) []).asFinrel "has_subset").literal
  | .call op args => do return .call op (← args.attach.mapM fun ⟨x, _⟩ => x.splice env)
  | a => pure a
termination_by x => sizeOf x

/-- The `has_subset` relations in γ's expression meet the solution set's heading. -/
def Agg.checkSubsets (env : Env) (h : Heading) : Agg → Except String Unit
  | .hasSubset r => do checkSubsetHeading (← (← r.eval (leafEnv env) []).asFinrel "has_subset") h
  | .call _ args => args.attach.forM fun ⟨x, _⟩ => x.checkSubsets env h
  | _ => pure ()
termination_by x => sizeOf x

/-- The `has_subset` relations that a condition's structure reaches (γ, extend and join;
not inside a leaf, as Racket's `prepare-E`) meet the solution set's heading. -/
def Expr.checkSubsets (env : Env) (h : Heading) : Expr → Except String Unit
  | .gamma _ ex _ e => do ex.checkSubsets env h; e.checkSubsets env h
  | .extend _ _ e => e.checkSubsets env h
  | .nary .join es => es.attach.forM fun ⟨x, _⟩ => x.checkSubsets env h
  | _ => pure ()
termination_by x => sizeOf x

/-- ℰ_sol's key, checked as a condition is. -/
def Expr.checkKey (env : Env) (h : Heading) : Option (Order × Expr) → Except String Unit
  | some (_, k) => k.checkSubsets env h
  | none => pure ()
termination_by x => sizeOf x

def Cond.checkSubsets (env : Env) (h : Heading) : Cond → Except String Unit
  | .expr e => e.checkSubsets env h
  | .and cs | .or cs => cs.attach.forM fun ⟨c, _⟩ => c.checkSubsets env h
  | .not c => c.checkSubsets env h
  | .hasSubset r => do checkSubsetHeading (← (← r.eval (leafEnv env) []).asFinrel "has_subset") h
termination_by x => sizeOf x
end

/-- A leaf of a condition (`has_subset`'s relation): evaluated with no targets, in the
leaf environment, and a finite relation. -/
def Expr.leaf (env : Env) (r : Expr) : Except String Finrel := do
  (← r.eval (leafEnv env) []).asFinrel "has_subset"

/-- A program: definitions, each evaluated in the environment of those before it. -/
def runProgram (defs : Program) : Except String Env :=
  defs.foldlM (fun env (n, e) => do return env ++ [(n, ← e.eval env.reverse [])]) []

end Rasso
