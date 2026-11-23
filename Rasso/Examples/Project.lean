import Rasso.Examples.Unrel

/-!
# Examples: π on unrestricted relations

Each `#guard` is run when the file is built. They check:

* π drops a finite attribute and keeps an infinite one; ⋈ with a finite ω then lists the
  result (σ does not change domains, so it would not make the result listable);
* π refuses to drop an attribute whose domain has no end, and says why;
* π drops two finite attributes;
* π drops an attribute whose domain is empty, which gives the empty relation;
* π of a lifted finite relation lists the same tuples as π of the finite relation;
* π refuses an attribute named twice, or not in the heading, in the same words as on a
  finite relation;
* the recogniser is sound but not complete: a float attribute that no
  term reads is still refused;
* the dense-order class, the equality class and the linear class:
  what they remove, and what they refuse.
-/

namespace Rasso.Examples.Project

open Rasso Rasso.Examples.Unrel

/-- x = y + 1, with x an int and y in 0..3. -/
def xy1 : Expr := .omegaWhere [("x", .kind .int), ("y", .range 0 3)]
  (.call "=" [.attr "x", .call "+" [.attr "y", .val (.int 1)]])

/-- x + y = z, all in 0..3. -/
def xyz : Expr := .omegaWhere [("x", .range 0 3), ("y", .range 0 3), ("z", .range 0 3)]
  (.call "=" [.call "+" [.attr "x", .attr "y"], .attr "z"])

/-- A finite relation over x and y. -/
def fr : Expr := .omegaRows [("x", .range 0 5), ("y", .range 0 1)]
  [[.int 2, .int 0], [.int 3, .int 1], [.int 2, .int 1]]

/-! ## Dropping a finite attribute, keeping an infinite one -/

-- π[x](x = y + 1): an unrestricted relation over x int
#guard match run [("u", .project ["x"] xy1)] "u" with
  | .ok (.unrel u) => u.heading.attrs == ["x"]
  | _ => false
-- ⋈ with ω[x range 0 10] makes x finite, so the result can be listed
#guard tuplesOf [("u", .nary .join [.project ["x"] xy1, .omega [("x", .range 0 10)]])] "u" ==
  some [[.int 1], [.int 2], [.int 3], [.int 4]]

/-! ## Refusing an attribute whose domain has no end -/

#guard match run [("u", .project ["y"] xy1)] "u" with
  | .error m => m == "π: no class can remove attribute x, of domain int (finite: the domain has no end; dense order: the domain is not rat; equality: x is used other than in = with a value of its domain; linear: the domain is not rat)"
  | .ok _ => false

/-! ## Two finite attributes dropped -/

#guard tuplesOf [("u", .project ["z"] xyz)] "u" == some [[.int 0], [.int 1], [.int 2], [.int 3]]
-- the heading follows the order of the list
#guard match run [("u", .project ["z", "x"] xyz)] "u" with
  | .ok (.unrel u) => u.heading.attrs == ["z", "x"]
  | _ => false

/-! ## An empty domain -/

#guard tuplesOf [("u", .project ["x"] (.omega [("x", .range 0 3), ("e", .set [])]))] "u" == some []

/-! ## A lifted finite relation -/

#guard match run [("u", .project ["x"] (.lift fr))] "u" with
  | .ok (.unrel _) => true
  | _ => false
#guard tuplesOf [("u", .project ["x"] (.lift fr))] "u" == tuplesOf [("u", .project ["x"] fr)] "u"
#guard tuplesOf [("u", .project ["x"] (.lift fr))] "u" == some [[.int 2], [.int 3]]

/-! ## Refusals shared with finite relations -/

#guard match run [("u", .project ["x", "x"] xy1)] "u", run [("u", .project ["x", "x"] fr)] "u" with
  | .error m, .error m' => m == m' && m == "π: [x, x] names an attribute twice"
  | _, _ => false
#guard match run [("u", .project ["q"] xy1)] "u" with
  | .error m => m == "π: no attribute q in [x, y]"
  | .ok _ => false

/-! ## Sound, not complete -/

-- z is a float that no term reads, so ∃ z is true; no class takes a float domain, so π
-- still refuses it
#guard refused [("u", .project ["x"] (.nary .join [.lift fr, .omega [("z", .kind .float)]]))] "u"
-- with z an int, the equality class removes it: no leaf mentions z
#guard tuplesOf [("u", .project ["x"] (.nary .join [.lift fr, .omega [("z", .kind .int)]]))] "u" ==
  some [[.int 2], [.int 3]]

/-! ## The dense-order class -/

/-- y < x < z, with x a rat and y, z in 0..4. -/
def yxz : Expr := .omegaWhere [("x", .kind .rat), ("y", .range 0 4), ("z", .range 0 4)]
  (.call "and" [.call "<" [.attr "y", .attr "x"], .call "<" [.attr "x", .attr "z"]])

-- π[y, z] holds the same tuples as y < z (the term is not simplified)
#guard tuplesOf [("u", .project ["y", "z"] yxz)] "u" ==
  tuplesOf [("u", .omegaWhere [("y", .range 0 4), ("z", .range 0 4)]
    (.call "<" [.attr "y", .attr "z"]))] "u"
-- a rat lies between 1 and 2, so (1, 2) is kept, though no int does
#guard (tuplesOf [("u", .project ["y", "z"] yxz)] "u").map (·.contains [.int 1, .int 2]) == some true

-- an equality: x = y and x > 0 holds y > 0
#guard tuplesOf [("u", .project ["y"] (.omegaWhere [("x", .kind .rat), ("y", .range (-2) 2)]
  (.call "and" [.call "=" [.attr "x", .attr "y"], .call ">" [.attr "x", .val (.int 0)]])))] "u" ==
  some [[.int 1], [.int 2]]

-- not: not (x <= y) holds every y (x can be above it)
#guard tuplesOf [("u", .project ["y"] (.omegaWhere [("x", .kind .rat), ("y", .range 0 2)]
  (.call "not" [.call "<=" [.attr "x", .attr "y"]])))] "u" == some [[.int 0], [.int 1], [.int 2]]

-- not (x = y) with x < 1 and x > 0 and y in 0..1: a rat lies in (0, 1) apart from y
#guard tuplesOf [("u", .project ["y"] (.omegaWhere [("x", .kind .rat), ("y", .range 0 1)]
  (.call "and" [.call "not" [.call "=" [.attr "x", .attr "y"]],
    .call ">" [.attr "x", .val (.int 0)], .call "<" [.attr "x", .val (.int 1)]])))] "u" ==
  some [[.int 0], [.int 1]]

-- both classes in one π: x by dense order, then y by finite
#guard tuplesOf [("u", .nary .join [.project ["z"] (.omegaWhere
    [("x", .kind .rat), ("y", .range 0 3), ("z", .kind .int)]
    (.call "and" [.call "<" [.attr "y", .attr "x"], .call "<" [.attr "x", .attr "z"]])),
  .omega [("z", .range 0 5)]])] "u" == some [[.int 1], [.int 2], [.int 3], [.int 4], [.int 5]]

-- refused: x in arithmetic
#guard match run [("u", .project ["y"] (.omegaWhere [("x", .kind .rat), ("y", .range 0 2)]
    (.call "<" [.call "*" [.attr "x", .attr "y"], .val (.int 1)])))] "u" with
  | .error m => m == "π: no class can remove attribute x, of domain rat (finite: the domain has no end; dense order: x is used other than in a comparison with a number; equality: the domain is not symbol, string or int; linear: x is used other than in a comparison of linear terms)"
  | .ok _ => false
-- refused: x compared with a symbol (always true, since numbers sort first)
#guard refused [("u", .project ["s"] (.omegaWhere [("x", .kind .rat), ("s", .set [.symbol "a"])]
  (.call "<" [.attr "x", .attr "s"])))] "u"

/-! ## The equality class -/

/-- A symbol constant. -/
def sy (s : String) : Term := .val (.symbol s)

-- x = y and not (x = 'a), over symbols: holds the same tuples as not (y = 'a)
#guard tuplesOf [("u", .nary .join [.project ["y"] (.omegaWhere [("x", .kind .symbol), ("y", .kind .symbol)]
    (.call "and" [.call "=" [.attr "x", .attr "y"], .call "not" [.call "=" [.attr "x", sy "a"]]])),
  .omega [("y", .set [.symbol "a", .symbol "b", .symbol "c"])]])] "u" == some [[.symbol "b"], [.symbol "c"]]
-- only a disequality: not (x = y) holds every y, since the symbols have no end
#guard tuplesOf [("u", .nary .join [.project ["y"] (.omegaWhere [("x", .kind .symbol), ("y", .kind .symbol)]
    (.call "not" [.call "=" [.attr "x", .attr "y"]])),
  .omega [("y", .set [.symbol "a", .symbol "b"])]])] "u" == some [[.symbol "a"], [.symbol "b"]]
-- over int: x = y with y in 0..3
#guard tuplesOf [("u", .project ["y"] (.omegaWhere [("x", .kind .int), ("y", .range 0 3)]
  (.call "=" [.attr "x", .attr "y"])))] "u" == some [[.int 0], [.int 1], [.int 2], [.int 3]]
-- x = x is true, and not (x = x) is false
#guard tuplesOf [("u", .project ["y"] (.omegaWhere [("x", .kind .int), ("y", .range 0 1)]
  (.call "=" [.attr "x", .attr "x"])))] "u" == some [[.int 0], [.int 1]]
#guard tuplesOf [("u", .project ["y"] (.omegaWhere [("x", .kind .int), ("y", .range 0 1)]
  (.call "not" [.call "=" [.attr "x", .attr "x"]])))] "u" == some []
-- not (x = 1 or x = 2): some int is neither
#guard tuplesOf [("u", .project ["y"] (.omegaWhere [("x", .kind .int), ("y", .range 0 1)]
  (.call "not" [.call "or" [.call "=" [.attr "x", .val (.int 1)],
    .call "=" [.attr "x", .val (.int 2)]]])))] "u" == some [[.int 0], [.int 1]]
-- an operand whose domain is a set of ints, on the left of =
#guard tuplesOf [("u", .project ["y"] (.omegaWhere [("x", .kind .int), ("y", .set [.int 3, .int 5])]
  (.call "=" [.attr "y", .attr "x"])))] "u" == some [[.int 3], [.int 5]]
-- two disjuncts, only one with x = τ; y > 1 and y = 0 are parts without x
#guard tuplesOf [("u", .project ["y"] (.omegaWhere [("x", .kind .int), ("y", .range 0 2)]
  (.call "or" [.call "and" [.call "=" [.attr "x", .attr "y"], .call ">" [.attr "y", .val (.int 1)]],
    .call "and" [.call "not" [.call "=" [.attr "x", .val (.int 5)]],
      .call "=" [.attr "y", .val (.int 0)]]])))] "u" == some [[.int 0], [.int 2]]
-- a part without x (y < 3) beside x = y
#guard tuplesOf [("u", .project ["y"] (.omegaWhere [("x", .kind .int), ("y", .range 0 5)]
  (.call "and" [.call "=" [.attr "x", .attr "y"], .call "<" [.attr "y", .val (.int 3)]])))] "u" ==
  some [[.int 0], [.int 1], [.int 2]]

-- refused: x = 1.5 over int (a float is not a value of x's domain)
#guard match run [("u", .project ["y"] (.omegaWhere [("x", .kind .int), ("y", .range 0 1)]
    (.call "=" [.attr "x", .val (.float ⟨false, 15, -1⟩)])))] "u" with
  | .error m => m == "π: no class can remove attribute x, of domain int (finite: the domain has no end; dense order: the domain is not rat; equality: x is used other than in = with a value of its domain; linear: the domain is not rat)"
  | .ok _ => false
-- refused: x = y with y a string and x a symbol (y's domain is not inside x's)
#guard refused [("u", .project ["y"] (.omegaWhere [("x", .kind .symbol), ("y", .kind .string)]
  (.call "=" [.attr "x", .attr "y"])))] "u"
-- refused: order over int is in no class
#guard refused [("u", .project ["y"] (.omegaWhere [("x", .kind .int), ("y", .range 0 1)]
  (.call "<" [.attr "x", .attr "y"])))] "u"

/-! ## The linear class -/

/-- `x` rat, `y` an int range, and a term. -/
def xr (lo hi : Int) (e : Term) : Expr := .project ["y"] (.omegaWhere [("x", .kind .rat), ("y", .range lo hi)] e)

def x' : Term := .attr "x"
def y' : Term := .attr "y"
def n (k : Int) : Term := .val (.int k)

-- a linear example: x + y <= 3 and 2 * x >= y, y in 0..4, gives y in 0..2
#guard tuplesOf [("u", xr 0 4 (.call "and" [.call "<=" [.call "+" [x', y'], n 3],
  .call ">=" [.call "*" [n 2, x'], y']]))] "u" == some [[.int 0], [.int 1], [.int 2]]
-- an equality row: x + y = 1 and x > 2 gives y < -1
#guard tuplesOf [("u", xr (-3) 0 (.call "and" [.call "=" [.call "+" [x', y'], n 1],
  .call ">" [x', n 2]]))] "u" == some [[.int (-3)], [.int (-2)]]
-- a coefficient below zero: -2 * x <= y and x <= 1 gives y >= -2
#guard tuplesOf [("u", xr (-4) 0 (.call "and" [.call "<=" [.call "*" [n (-2), x'], y'],
  .call "<=" [x', n 1]]))] "u" == some [[.int (-2)], [.int (-1)], [.int 0]]
-- a row where x cancels: x - x < 1 is true
#guard tuplesOf [("u", xr 0 1 (.call "<" [.call "-" [x', x'], n 1]))] "u" ==
  some [[.int 0], [.int 1]]
-- not of an equality: x + y <= 1 and x + y >= 1 leave only x + y = 1, which not (=) excludes
#guard tuplesOf [("u", xr 0 1 (.call "and" [.call "not" [.call "=" [.call "+" [x', y'], n 1]],
  .call "<=" [.call "*" [n 2, x'], .call "-" [n 2, .call "*" [n 2, y']]],
  .call ">=" [x', .call "-" [n 1, y']]]))] "u" == some []
-- the same without not: x + y = 1 has a solution for every y
#guard tuplesOf [("u", xr 0 1 (.call "and" [
  .call "<=" [.call "*" [n 2, x'], .call "-" [n 2, .call "*" [n 2, y']]],
  .call ">=" [x', .call "-" [n 1, y']]]))] "u" == some [[.int 0], [.int 1]]
-- refused: x * x is not linear
#guard match run [("u", xr 0 1 (.call "<" [.call "*" [x', x'], n 1]))] "u" with
  | .error m => m == "π: no class can remove attribute x, of domain rat (finite: the domain has no end; dense order: x is used other than in a comparison with a number; equality: the domain is not symbol, string or int; linear: x is used other than in a comparison of linear terms)"
  | .ok _ => false
-- dense order still takes order-only terms first; linear takes x + y
#guard match recognise ⟨[("x", .kind .rat), ("y", .range 0 1)], .call "<" [x', y']⟩ "x" with
  | .ok .dense => true
  | _ => false
#guard match recognise ⟨[("x", .kind .rat), ("y", .range 0 1)], .call "<" [.call "+" [x', y'], n 1]⟩
    "x" with
  | .ok .linear => true
  | _ => false

end Rasso.Examples.Project
