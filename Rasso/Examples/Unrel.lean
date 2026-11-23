import Rasso.Eval
import Rasso.Unrel

/-!
# Examples: unrestricted relations, heading checks

Each `#guard` is run when the file is built. They check:

* ∪, ∩ and − refuse unrestricted operands whose headings differ, as they do finite ones;
* × refuses operands that share an attribute;
* ω[H](p) and σ_p refuse a term that reads an attribute outside the heading;
* a set domain that mixes floats with exact numbers is refused when it is written;
* over finite domains, ∪, ∩, − and ⋈ of unrestricted relations list the expected tuples;
* ρ of an unrestricted relation renames its heading and its term, and refuses as
  on a finite relation.
-/

namespace Rasso.Examples.Unrel

open Rasso

/-- The value a program gives a name, or the refusal. -/
def run (p : Program) (n : String) : Except String Val := do
  let env ← runProgram p
  match env.lookup n with
  | some v => return v
  | none => throw s!"{n} is not bound"

def refused (p : Program) (n : String) : Bool :=
  match run p n with | .error _ => true | .ok _ => false

/-- The tuples of an unrestricted (or finite) result, as lists of values in heading order. -/
def tuplesOf (p : Program) (n : String) : Option (List (List Value)) :=
  match run p n with
  | .ok (.unrel u) => match u.tuples with
    | .ok ts => some (ts.map fun t => t.map (·.2))
    | .error _ => none
  | .ok (.finrel r) => some (r.tuples.map fun t => t.map (·.2))
  | _ => none

def x05 : Expr := .omega [("x", .range 0 5)]
def xEven : Expr := .omegaWhere [("x", .range 0 5)]
  (.call "=" [.call "%" [.attr "x", .val (.int 2)], .val (.int 0)])
def xSmall : Expr := .omegaWhere [("x", .range 0 5)] (.call "<" [.attr "x", .val (.int 3)])

/-! ## ∪, ∩, − check headings -/

-- ω[x int](false) ∪ ω[x range 0 5]: the domains differ, so the headings differ
#guard refused [("u", .nary .union [.omegaWhere [("x", .kind .int)] (.val (.bool false)), x05])] "u"
#guard refused [("u", .nary .intersect [.omega [("x", .kind .int)], x05])] "u"
#guard refused [("u", .nary .except [.omega [("y", .range 0 5)], x05])] "u"
-- the refusal says why
#guard match run [("u", .nary .union [.omega [("y", .range 0 5)], x05])] "u" with
  | .error m => m == "∪: the headings [y] and [x] differ"
  | .ok _ => false

/-! ## × refuses shared attributes -/

#guard refused [("u", .nary .product [x05, xEven])] "u"
#guard refused [("u", .nary .product [.omegaRows [("x", .range 0 5)] [[.int 1]],
  .omegaRows [("x", .range 0 5)] [[.int 1]]])] "u"
#guard tuplesOf [("u", .nary .product [xSmall, .omega [("y", .set [.bool true])]])] "u" ==
  some [[.int 0, .bool true], [.int 1, .bool true], [.int 2, .bool true]]

/-! ## Terms must read only the heading -/

-- ω[a int](b = 1) is refused; before the heading checks it held nothing, and under ⋈ with ω[b] it
-- held every tuple with b = 1
#guard refused [("u", .omegaWhere [("a", .range 0 2)] (.call "=" [.attr "b", .val (.int 1)]))] "u"
#guard refused [("u", .select (.call "=" [.attr "b", .val (.int 1)]) x05)] "u"
#guard refused [("u", .select (.call "=" [.attr "b", .val (.int 1)])
  (.omegaRows [("a", .range 0 2)] [[.int 1]]))] "u"
#guard match run [("u", .select (.call "=" [.attr "b", .val (.int 1)]) x05)] "u" with
  | .error m => m == "σ: the term reads [b], which are not attributes of the heading [x]"
  | .ok _ => false

/-! ## No domain mixes floats with exact numbers -/

#guard (Expr.omega [("x", .set [.int 1, .float ⟨false, 25, -1⟩])]).problem.isSome
#guard (Expr.omega [("x", .set [.float ⟨false, 15, -1⟩, .float ⟨false, 25, -1⟩])]).problem.isNone
#guard (Expr.omega [("x", .set [.int 1, .int 2])]).problem.isNone

/-! ## What the operators hold, over finite domains -/

#guard tuplesOf [("u", .nary .union [xEven, xSmall])] "u" ==
  some [[.int 0], [.int 1], [.int 2], [.int 4]]
#guard tuplesOf [("u", .nary .intersect [xEven, xSmall])] "u" == some [[.int 0], [.int 2]]
#guard tuplesOf [("u", .nary .except [xEven, xSmall])] "u" == some [[.int 4]]
#guard tuplesOf [("u", .nary .except [xSmall, xEven])] "u" == some [[.int 1]]
-- ∩ keeps one heading, as it does on finite relations
#guard match run [("u", .nary .intersect [xEven, xSmall])] "u" with
  | .ok (.unrel u) => u.heading.attrs == ["x"]
  | _ => false
-- ⋈ of an unrestricted and a finite relation (lift)
#guard tuplesOf [("u", .nary .join [xEven, .omegaRows [("x", .range 0 5), ("y", .range 0 1)]
  [[.int 2, .int 0], [.int 3, .int 1]]])] "u" == some [[.int 2, .int 0]]
-- σ on an unrestricted relation
#guard tuplesOf [("u", .select (.call ">" [.attr "x", .val (.int 2)]) xEven)] "u" ==
  some [[.int 4]]

/-! ## ρ -/

def xy : Expr := .omegaWhere [("x", .range 0 2), ("y", .range 0 2)]
  (.call "<" [.attr "x", .attr "y"])

#guard tuplesOf [("u", .rename [("x", "a")] xEven)] "u" == some [[.int 0], [.int 2], [.int 4]]
#guard match run [("u", .rename [("x", "a")] xEven)] "u" with
  | .ok (.unrel u) => u.heading.attrs == ["a"]
  | _ => false
-- a swap: x < y becomes y < x
#guard tuplesOf [("u", .rename [("x", "y"), ("y", "x")] xy)] "u" ==
  some [[.int 1, .int 0], [.int 2, .int 0], [.int 2, .int 1]]
-- ρ, then ⋈ with a finite relation
#guard tuplesOf [("u", .nary .join [.rename [("x", "a")] xSmall,
  .omegaRows [("a", .range 0 5), ("b", .range 0 1)] [[.int 1, .int 0], [.int 4, .int 1]]])] "u" ==
  some [[.int 1, .int 0]]
-- refusals, in the same words as on a finite relation
#guard match run [("u", .rename [("z", "a")] xEven)] "u",
    run [("u", .rename [("z", "a")] (.omegaRows [("x", .range 0 5)] [[.int 1]]))] "u" with
  | .error m, .error m' => m == m' && m == "ρ: no attribute z to rename in [x]"
  | _, _ => false
#guard match run [("u", .rename [("x", "y")] xy)] "u" with
  | .error m => m == "ρ: the renaming names an attribute twice"
  | .ok _ => false

end Rasso.Examples.Unrel
