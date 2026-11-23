import Rasso.Eval
import Rasso.ESO.Logic

/-!
# ESO, the construction: a sentence and a structure give a Rasso program

`toProgram ψ A` is a Rasso program (a list of statements, the same `Program` the JSON
surface reads) whose last statement, `eso`, is a multi solution set. The intended theorem
(`Rasso.ESO.Capture`) is:

    `eso` has a candidate  ↔  ψ holds on A.

`ToProgram.decide` runs the program and reads off that answer; the examples in
`Rasso.ESO.Examples` check it on small structures. The proofs are in `Rasso.ESO.Program` (the program)
and `Rasso.ESO.Capture` (the form with the data in place); this file is the construction.

## How the program is built, in plain words

The structure becomes data:

* `univ` is the universe, a finite relation with one attribute `e`.
* `rel_E_2` is the relation symbol `E` at arity 2, a finite relation with attributes
  `c0, c1`. One statement for each symbol (and arity) the sentence uses.

The second-order variables become the members of the multi solution set:

* `member_R`, for a variable `R` of arity `k`, is `ω_sol(univ^k, holds: bool)`. A candidate
  of it gives every `k`-tuple of the universe the value `true` or `false`, which is the
  same as a subset of `univ^k`, which the logic calls a guess for `R`. The tuples in the
  subset are those whose `holds` is `true`.

The first-order formula becomes the condition, by Codd's translation. A formula with
free variables `x, y` becomes a relation with attributes `x_x, x_y`: the assignments that
make it true. Then:

* an atom `E(x, y)` is: join `rel_E_2` with a copy of the universe for each variable,
  keep the rows where `c0 = x_x` and `c1 = x_y`, and project onto `x_x, x_y`. A repeated
  variable (`E(x, x)`) needs no special case. An atom `R(x)` on a member does the same
  with `member_R`, keeping only rows with `holds = true`.
* `x = y` is the universe twice, keeping the rows where `x_x = x_y`.
* `and` is natural join. `or` is union, after each side is joined with the universe for
  the variables only the other side has (so both sides have the same attributes).
* `not φ` is "every assignment" (the universe once per variable) minus φ's relation.
* `∃ x φ` is projection: drop `x_x`. (`φ` is first joined with the universe for `x`, which
  changes nothing when `x` is free in `φ`, and makes `∃ x` false on an empty universe when
  it is not.)
* `∀ x φ` is `not ∃ x not φ`, written out with two differences.

The sentence is closed, so its relation has no attributes: it is either the relation
with one empty tuple (true) or the empty relation (false). The condition asks which,
with γ: `bool_or` of the constant `true` over the relation's tuples is `true` exactly when
there is a tuple. (NP-Alg's spelling, "FAIL = ∅", is the same test on the negated
formula.)

Conventions:

* **Names.** Statement and attribute names come from the sentence's names with fixed
  prefixes (`x_`, `rel_`, `member_`), so they cannot clash with each other or with `univ`,
  `eso`, `e`, `c0, c1, …` and `holds`. The sentence's names must be such that the results
  are Rasso names (letters, digits and `_`); `Sentence.problem` checks this. Nothing in
  the construction itself depends on it.
* **The universe's domain** is the finite set of its values (`DomExpr.set`, written in
  Racket's value order, without repeats). Every attribute of every relation in the
  program has this domain, so `∪` and `−` always meet equal headings.
* **Data is cleaned, not refused.** A symbol's tuples of the wrong length, or with an
  entry outside the universe, are left out of its finite relation. This changes nothing
  that `Sat` can see: variables range over the universe only, and an atom compares a
  tuple of its own length.
* **An atom on a second-order variable used at the wrong arity** (or one not listed in
  the sentence) is the empty relation, matching `Guess.Fits`, which makes such a guess
  hold no tuple of that length. A variable listed twice is a member once, at its first
  arity (as `List.lookup` reads `ar`).
* **No second-order variables.** `ω_msol` needs at least one member, so a sentence with
  none gets one unused member, `member_` of arity 0. It has two candidates and is not
  mentioned by the condition, so the answer is unchanged.
* **Exponential, by design.** The evaluator lists every candidate, so the program is
  only run on small structures. This is a test of meaning, not a solver.
-/

namespace Rasso.ESO

open Rasso

/-! ## Names -/

def varAttr (x : String) : String := "x_" ++ x
def colAttr (m : Nat) : String := s!"c{m}"
def holdsAttr : String := "holds"
def univName : String := "univ"
def univAttr : String := "e"
def relName (i : String) (n : Nat) : String := s!"rel_{i}_{n}"
def memberName (j : String) : String := "member_" ++ j
def esoName : String := "eso"

def cols (n : Nat) : List String := (List.range n).map colAttr

/-! ## The formula's variables -/

/-- The free variables without repeats: the attributes of the formula's relation. -/
def FO.vars (φ : FO) : List String := φ.fv.eraseDups

/-- The input symbols a formula uses, each with the arity it is used at. -/
def FO.rels : FO → List (String × Nat)
  | .rel i args => [(i, args.length)]
  | .gvar _ _ | .eq _ _ => []
  | .not φ | .ex _ φ | .all _ φ => φ.rels
  | .and φ ψ | .or φ ψ => φ.rels ++ ψ.rels

/-! ## Building blocks -/

/-- A conjunction of tests (`and` takes two or more operands). -/
def conj : List Term → Term
  | [] => .val (.bool true)
  | [t] => t
  | ts => .call "and" ts

def eqT (a b : String) : Term := .call "=" [.attr a, .attr b]

/-- The relation with no attributes and one tuple. -/
def dee : Expr := .omegaRows [] [[]]

/-- Natural join of a list of relations (two or more operands for `join`). -/
def joinAll : List Expr → Expr
  | [] => dee
  | [r] => r
  | rs => .nary .join rs

/-- `univ` once for each name, the copy for `a` renamed to attribute `f a`. -/
def univPow (f : String → String) (as : List String) : Expr :=
  joinAll (as.map fun a => .rename [(univAttr, f a)] (.name univName))

/-- Every assignment to some variables: `univ^xs`. -/
def domOf (xs : List String) : Expr := univPow varAttr xs

/-- Join `r` with the universe for the variables `xs` it lacks. -/
def pad (r : Expr) (xs : List String) : Expr :=
  if xs.isEmpty then r else .nary .join [r, domOf xs]

/-- The empty relation over some variables. -/
def emptyOn (xs : List String) : Expr := .nary .except [domOf xs, domOf xs]

/-- An atom: `base`'s columns `cs` equal to the variables `args`, with extra tests; the
result has the attributes of `args` (without repeats). -/
def atom (base : Expr) (cs : List String) (extra : List Term) (args : List String) : Expr :=
  let xs := args.eraseDups
  .project (xs.map varAttr)
    (.select (conj (extra ++ (cs.zip args).map fun (c, x) => eqT c (varAttr x)))
      (.nary .join [base, domOf xs]))

/-! ## Codd's translation of a first-order formula -/

/-- The relation of the assignments (to `φ.vars`, as `x_…` attributes) that satisfy `φ`,
given the second-order variables' arities `ar`. -/
def compile (ar : List (String × Nat)) : FO → Expr
  | .rel i args => atom (.name (relName i args.length)) (cols args.length) [] args
  | .gvar j args =>
    if ar.lookup j = some args.length then
      atom (.name (memberName j)) (cols args.length)
        [.call "=" [.attr holdsAttr, .val (.bool true)]] args
    else emptyOn args.eraseDups
  | .eq x y => if x = y then domOf [x] else .select (eqT (varAttr x) (varAttr y)) (domOf [x, y])
  | .not φ => .nary .except [domOf φ.vars, compile ar φ]
  | .and φ ψ => .nary .join [compile ar φ, compile ar ψ]
  | .or φ ψ =>
    .nary .union [pad (compile ar φ) (ψ.vars.filter (!φ.vars.contains ·)),
                  pad (compile ar ψ) (φ.vars.filter (!ψ.vars.contains ·))]
  | .ex x φ =>
    .project ((FO.ex x φ).vars.map varAttr)
      (pad (compile ar φ) (if φ.vars.contains x then [] else [x]))
  | .all x φ =>
    let ys := if φ.vars.contains x then φ.vars else φ.vars ++ [x]
    let notφ := Expr.nary .except [domOf ys, pad (compile ar φ) (if φ.vars.contains x then [] else [x])]
    let zs := (FO.all x φ).vars
    .nary .except [domOf zs, .project (zs.map varAttr) notφ]

/-- "The relation has a tuple", as a condition: `bool_or` of `true` over its tuples. -/
def nonEmpty (r : Expr) : Cond :=
  .expr (.gamma [] (.agg "bool_or" (.val (.bool true))) none r)

/-! ## The program -/

/-- Values without repeats, in Racket's value order (how `.set` must be written). -/
def racketSorted (vs : List Value) : List Value :=
  vs.eraseDups.mergeSort fun a b => !racketValueLt b a

/-- The domain of every attribute: the universe as a finite set. -/
def univDom (A : Str) : DomExpr := .set (racketSorted A.univ)

/-- The data statement for symbol `i` at arity `n`: its tuples of length `n` over the
universe. -/
def relStatement (A : Str) (i : String) (n : Nat) : String × Expr :=
  let ok (t : List Value) := t.length == n && t.all A.univ.contains
  (relName i n, .omegaRows ((cols n).map (·, univDom A)) ((A.rel i).filter ok).eraseDups)

/-- The second-order variables, each once (the first listing wins). -/
def members (ar : List (String × Nat)) : List (String × Nat) :=
  ar.foldl (fun acc (j, k) => if acc.any (·.1 == j) then acc else acc ++ [(j, k)]) []

/-- The member for a second-order variable of arity `k`: every subset of `univ^k`, as a
function from `univ^k` to `holds: bool`. -/
def boolMember (j : String) (k : Nat) : String × Expr :=
  (memberName j, .omegaSol (univPow id (cols k)) (.omega [(holdsAttr, .kind .bool)]))

/-- The Rasso program for sentence `ψ` on structure `A`. Its last statement, `eso`, is a
multi solution set that has a candidate exactly when `ψ` holds on `A` (see
`Rasso.ESO.Capture`). -/
def toProgram (ψ : Sentence) (A : Str) : Program :=
  let ms := match members ψ.ar with
    | [] => [boolMember "" 0]
    | ms => ms.map fun (j, k) => boolMember j k
  [(univName, .omegaRows [(univAttr, univDom A)] ((racketSorted A.univ).map ([·])))] ++
  (ψ.φ.rels.eraseDups.map fun (i, n) => relStatement A i n) ++
  [(esoName, .omegaMsol ms (some (nonEmpty (compile ψ.ar ψ.φ))))]

/-- What makes a sentence's names unusable as Rasso names, or none. -/
def Sentence.problem (ψ : Sentence) : Option String :=
  let rec names : FO → List String
    | .rel i args => i :: args
    | .gvar j args => j :: args
    | .eq x y => [x, y]
    | .not φ => names φ
    | .and φ ψ | .or φ ψ => names φ ++ names ψ
    | .ex x φ | .all x φ => x :: names φ
  let bad := (ψ.ar.map (·.1) ++ names ψ.φ).filter fun n => !isAttribute ("x_" ++ n)
  if let n :: _ := bad then some s!"{n} can't be part of a Rasso name"
  else if (ψ.ar.map (·.1)).eraseDups.length != ψ.ar.length then
    some "a second-order variable is listed twice"
  else none

/-! ## Running it -/

namespace ToProgram

/-- Run the program and answer: does `eso` have a candidate? -/
def decide (ψ : Sentence) (A : Str) : Except String Bool := do
  let env ← runProgram (toProgram ψ A)
  match env.lookup esoName with
  | some (.msol m) => return !m.candidates.isEmpty
  | _ => throw "eso is not a multi solution set"

end ToProgram

end Rasso.ESO
