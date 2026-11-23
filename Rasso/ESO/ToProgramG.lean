import Rasso.ESO.ToProgram

/-!
# ESO, the construction in Racket's condition fragment (γ, extend, join)

A second version of the translation, written because the
first (`Rasso.ESO.ToProgram`, Codd's translation with π, −, ∪ and σ) does not run in
Racket. In Racket's evaluator a multi solution set's condition reads its members only
through γ, extend and join (`rexp-value`); any other operator
in a condition is evaluated as an ordinary form, where a member's name is not defined.
Rasso's own evaluator is more liberal (`Rasso.Eval`, assumptions), so the first version
runs in Lean only. This version keeps to the fragment both evaluators read, so the
same program runs in both.

## How the program is built, in plain words

Every subformula φ, with free variables V, becomes the **graph of its truth function**:
a relation with an attribute `x_v` for each variable in V and one Boolean attribute `t_…`
(named by φ's position in the formula), with exactly one row for each assignment of
universe values to V. The row's Boolean is `true` exactly when the assignment satisfies
φ. Then:

* An atom on the structure (`E(x, y)`), or an equality (`x = y`), is data: Lean works out
  its truth table from the structure and writes it as a finite relation (`data_…`).
* An atom on a member (`R(x, y)`) joins the member `member_R` (a total function from
  `univ^k` to `holds`) with a finite relation `data_…` that links its columns `c0, c1, …`
  to the variables (`c0 = x`, `c1 = y`), and γ groups by the variables, keeping `holds`.
* `not`, `and`, `or`: γ groups by the variables and computes the Boolean of the one row
  in each group (`and` and `or` first join their operands, which pairs up their rows).
* `∃ x φ`: γ groups by the other variables with `bool_or`; `∀ x φ` with `bool_and`. (If
  `x` is not free in φ, φ is first joined with the universe as `x`, so that an empty
  universe makes `∃` false and `∀` true.)

The sentence is closed, so its relation has no variables: γ with no grouping gives one
row with one Boolean. That is exactly the shape a condition reads (`holds E`): the
condition is the sentence's relation itself.

Compared with the Codd version: quantifiers are aggregates (`bool_or`, `bool_and`)
instead of projection and difference, and connectives are terms (`and`, `or`, `not`)
instead of join, union and difference. It is closer to Racket's terms, each of which is one Lean term, and to Racket's
condition fragment, which the converse reads back.

Conventions, in addition to those of
`Rasso.ESO.ToProgram` (names, the universe's domain, wrong arities, no second-order
variables, exponential by design):

* **Position names.** A subformula's position is the string of child indices from the
  root (`r`, `r0`, `r01`, …); its Boolean is `t_r01` and its finite relation `data_r01`.
  These cannot clash with `x_…`, `c…`, `holds`, `e`, `univ`, `rel_…`, `member_…` or `eso`.
* **Finite relations carry truth tables**, `|univ|^|V|` rows each. Data is free in the
  construction (it may depend on the structure any way at all), which is the usual
  reading of a query's input; the uniformity of the construction is that the data is
  computed the same way from every structure.
-/

namespace Rasso.ESO

open Rasso

def boolCol (p : String) : String := "t_" ++ p
def dataName (p : String) : String := "data_" ++ p

/-- Every assignment of universe values to the variables `xs` (all lists of pairs). -/
def assigns (U : List Value) (xs : List String) : List (List (String × Value)) :=
  choices (xs.map fun x => U.map (x, ·))

/-- The look-up of a variable in an assignment. -/
def look (ρ : List (String × Value)) (x : String) : Value := (ρ.lookup x).getD default

/-- A finite relation: a truth table over the variables `xs`. -/
def truthTable (A : Str) (p : String) (xs : List String)
    (f : List (String × Value) → Bool) : String × Expr :=
  let U := racketSorted A.univ
  (dataName p, .omegaRows ((xs.map fun x => (varAttr x, univDom A)) ++ [(boolCol p, .kind .bool)])
    ((assigns U xs).map fun ρ => xs.map (look ρ) ++ [.bool (f ρ)]))

/-- γ by the variables `xs`, computing the Boolean `ex` into the column for `p`. -/
def gammaBy (xs : List String) (ex : Agg) (p : String) (r : Expr) : Expr :=
  .gamma (xs.map varAttr) ex (some (boolCol p)) r

/-- The graph of `φ`'s truth function at position `p`, and the finite relations it needs. -/
def compileG (A : Str) (ar : List (String × Nat)) (p : String) : FO → Expr × Program
  | .rel i args =>
    let xs := args.eraseDups
    let d := truthTable A p xs fun ρ => (A.rel i).contains (args.map (look ρ))
    (.name d.1, [d])
  | .gvar j args =>
    let xs := args.eraseDups
    if ar.lookup j = some args.length then
      let U := racketSorted A.univ
      let link : String × Expr :=
        (dataName p, .omegaRows
          ((cols args.length ++ xs.map varAttr).map (·, univDom A))
          ((assigns U xs).map fun ρ => args.map (look ρ) ++ xs.map (look ρ)))
      (gammaBy xs (.agg "bool_or" (.attr holdsAttr)) p
        (.nary .join [.name (memberName j), .name link.1]), [link])
    else
      let d := truthTable A p xs fun _ => false
      (.name d.1, [d])
  | .eq x y =>
    let d := truthTable A p [x, y].eraseDups fun ρ => look ρ x == look ρ y
    (.name d.1, [d])
  | .not φ =>
    let (r, ds) := compileG A ar (p ++ "0") φ
    (gammaBy φ.vars (.call "not" [.agg "bool_or" (.attr (boolCol (p ++ "0")))]) p r, ds)
  | .and φ ψ =>
    let (r, ds) := compileG A ar (p ++ "0") φ
    let (s, es) := compileG A ar (p ++ "1") ψ
    (gammaBy (FO.and φ ψ).vars
      (.agg "bool_or" (.call "and" [.attr (boolCol (p ++ "0")), .attr (boolCol (p ++ "1"))])) p
      (.nary .join [r, s]), ds ++ es)
  | .or φ ψ =>
    let (r, ds) := compileG A ar (p ++ "0") φ
    let (s, es) := compileG A ar (p ++ "1") ψ
    (gammaBy (FO.or φ ψ).vars
      (.agg "bool_or" (.call "or" [.attr (boolCol (p ++ "0")), .attr (boolCol (p ++ "1"))])) p
      (.nary .join [r, s]), ds ++ es)
  | .ex x φ =>
    let (r, ds) := compileG A ar (p ++ "0") φ
    (gammaBy (FO.ex x φ).vars (.agg "bool_or" (.attr (boolCol (p ++ "0")))) p
      (pad r (if φ.vars.contains x then [] else [x])), ds)
  | .all x φ =>
    let (r, ds) := compileG A ar (p ++ "0") φ
    (gammaBy (FO.all x φ).vars (.agg "bool_and" (.attr (boolCol (p ++ "0")))) p
      (pad r (if φ.vars.contains x then [] else [x])), ds)

/-- The Rasso program for sentence `ψ` on structure `A`, in Racket's condition fragment.
Its last statement, `eso`, is a multi solution set that has a candidate exactly when
`ψ` holds on `A` (see `Rasso.ESO.Capture`). -/
def toProgramG (ψ : Sentence) (A : Str) : Program :=
  let ms := match members ψ.ar with
    | [] => [boolMember "" 0]
    | ms => ms.map fun (j, k) => boolMember j k
  let (cond, data) := compileG A ψ.ar "r" ψ.φ
  [(univName, .omegaRows [(univAttr, univDom A)] ((racketSorted A.univ).map ([·])))] ++
  data ++ [(esoName, .omegaMsol ms (some (.expr cond)))]

namespace ToProgram

/-- Run the γ version and answer: does `eso` have a candidate? -/
def decideG (ψ : Sentence) (A : Str) : Except String Bool := do
  let env ← runProgram (toProgramG ψ A)
  match env.lookup esoName with
  | some (.msol m) => return !m.candidates.isEmpty
  | _ => throw "eso is not a multi solution set"

end ToProgram

end Rasso.ESO
