import Rasso.Phi.Phi

/-!
# φ: examples

For each small program, φ of its last statement: the cells, and the commuting square checked
on every assignment (`checkSquare`: no mismatch with `accepts`, and the satisfying
substitutes are exactly the candidates Lean's evaluator gives). Then the refusals.
-/

namespace Rasso.Phi.Examples

open Rasso Rasso.Phi

/-- The last statement's index. -/
def last (p : Program) : Nat := p.length - 1

/-- The square holds on every assignment of the last statement. -/
def square (p : Program) : Bool :=
  match checkSquare p (last p) with
  | .ok (_, 0, 0) => true
  | _ => false

/-- The number of assignments the square was checked on. -/
def tried (p : Program) : Nat :=
  match checkSquare p (last p) with
  | .ok (n, _, _) => n
  | _ => 0

/-- The cells' names. -/
def cellNames (p : Program) : List String :=
  match phi p (last p) with
  | .ok F => F.cells.map (·.1)
  | .error _ => []

/-- How many assignments satisfy the flat relation. -/
def solutions (p : Program) : Nat :=
  match phi p (last p) with
  | .ok F => match Unrel.tuples F.rel with
    | .ok ts => ts.length
    | .error _ => 0
  | .error _ => 0

def refused (p : Program) : Bool := (phi p (last p)).toOption.isNone

/-- `γ[][bool_and(ok)](γ[by][all_different(v) → ok](x))`: in each group by `by`, the
decisions differ. -/
def allDiffBy (by_ : String) (x : Expr) : Cond :=
  .expr (.gamma [] (.agg "bool_and" (.attr "ok")) none
    (.gamma [by_] (.agg "all_different" (.attr "v")) (some "ok") x))

/-! ## A 2×2 Latin square -/

def Board : Expr := .omegaRows [("r", .range 1 2), ("c", .range 1 2)]
  [[.int 1, .int 1], [.int 1, .int 2], [.int 2, .int 1], [.int 2, .int 2]]
def Sym : Expr := .omega [("v", .range 1 2)]
def latin : Program := [("Board", Board), ("Sym", Sym),
  ("S", .omegaSol (.name "Board") (.name "Sym")),
  ("T", .sigmaSol (.and [allDiffBy "r" (.name "S"), allDiffBy "c" (.name "S")]) (.name "S"))]

-- Cells numbered as Racket numbers them: by r, then c, in the Data's heading order.
#guard cellNames latin = ["v1", "v2", "v3", "v4"]
#guard square latin
#guard tried latin = 16
#guard solutions latin = 2

/-! ## A knapsack (as the cakes' conditions are: a bound on a weighted sum) -/

def Items : Expr := .omegaRows [("i", .range 1 3), ("w", .range 0 9)]
  [[.int 1, .int 4], [.int 2, .int 3], [.int 3, .int 5]]
def Take : Expr := .omega [("take", .range 0 1)]
def knap : Program := [("Items", Items), ("Take", Take),
  ("S", .omegaSol (.name "Items") (.name "Take")),
  ("T", .sigmaSol (.expr (.gamma []
    (.call "<=" [.agg "sum" (.call "*" [.attr "w", .attr "take"]), .val (.int 8)]) none (.name "S")))
    (.name "S"))]

#guard square knap
-- 8 subsets; {1,3} weighs 9 and {1,2,3} 12, so 6 fit.
#guard solutions knap = 6

/-! ## `has_subset`, a join on a cell (guards), names, the Decision's term -/

def Cells : Expr := .omegaRows [("c", .range 1 3)] [[.int 1], [.int 2], [.int 3]]
def V : Expr := .omega [("v", .range 1 2)]
def Req : Expr := .omegaRows [("c", .kind .int), ("v", .kind .int)] [[.int 1, .int 2], [.int 3, .int 1]]
def Two : Expr := .omegaRows [("v", .kind .int)] [[.int 2]]
def base : Program := [("Cells", Cells), ("V", V), ("Req", Req), ("Two", Two),
  ("S", .omegaSol (.name "Cells") (.name "V"))]

-- has_subset as a condition, and negated.
#guard square (base ++ [("T", .sigmaSol (.hasSubset (.name "Req")) (.name "S"))])
#guard solutions (base ++ [("T", .sigmaSol (.hasSubset (.name "Req")) (.name "S"))]) = 2
#guard square (base ++ [("T", .sigmaSol (.not (.hasSubset (.name "Req"))) (.name "S"))])

-- A join on a cell: "at least two cells are 2", a guarded count (an `if` in a `sum`).
def atLeastTwoTwosOf (x : Expr) : Cond :=
  .expr (.gamma [] (.call ">=" [.agg "count" (.attr "c"), .val (.int 2)]) none
    (.nary .join [x, .name "Two"]))
def atLeastTwoTwos : Cond := atLeastTwoTwosOf (.name "S")
#guard square (base ++ [("T", .sigmaSol atLeastTwoTwos (.name "S"))])
#guard solutions (base ++ [("T", .sigmaSol atLeastTwoTwos (.name "S"))]) = 4

-- A guarded sum and a guarded bool_or.
#guard square (base ++ [("T", .sigmaSol (.expr (.gamma []
  (.call "<=" [.agg "sum" (.attr "c"), .val (.int 3)]) none (.nary .join [.name "S", .name "Two"]))) (.name "S"))])
#guard square (base ++ [("T", .sigmaSol (.expr (.gamma []
  (.agg "bool_or" (.call "=" [.attr "c", .val (.int 3)])) none (.nary .join [.name "S", .name "Two"]))) (.name "S"))])

-- has_subset in γ over a computed attribute (Racket's phi would say false here).
def sumAsV : Expr := .gamma ["c"] (.agg "sum" (.attr "v")) (some "v") (.name "S")
#guard square (base ++ [("T", .sigmaSol (.expr (.gamma []
  (.hasSubset (.omegaRows [("c", .kind .int), ("v", .kind .int)] [[.int 1, .int 2]])) none sumAsV)) (.name "S"))])

-- The same, exactly as reported against Racket's phi (which gives `false` here): data
-- d ∈ {1, 2}, v ∈ 0..1, has_subset({(d 1, v 1)}) over γ[d][sum(v) → v]. Two solutions.
def racketBug : Program := [("Data", .omegaRows [("d", .range 1 2)] [[.int 1], [.int 2]]),
  ("V", .omega [("v", .range 0 1)]), ("S", .omegaSol (.name "Data") (.name "V")),
  ("T", .sigmaSol (.expr (.gamma [] (.hasSubset (.omegaRows [("d", .range 1 2), ("v", .range 0 1)] [[.int 1, .int 1]]))
    (some "ok") (.gamma ["d"] (.agg "sum" (.attr "v")) (some "v") (.name "S")))) (.name "S"))]
#guard square racketBug
#guard solutions racketBug = 2

-- Through two names: each level its own marker.
#guard square (base ++ [("T", .sigmaSol (.hasSubset (.name "Req")) (.name "S")),
  ("U", .sigmaSol (.not (atLeastTwoTwosOf (.name "T"))) (.name "T"))])
-- There, `S` is not the candidate of the outer level but a leaf whose value is a solution
-- set: refused, as the evaluator refuses it.
#guard refused (base ++ [("T", .sigmaSol (.hasSubset (.name "Req")) (.name "S")),
  ("U", .sigmaSol (.not atLeastTwoTwos) (.name "T"))])

-- The Decision's own term: v ≠ 2 leaves one value, so one candidate.
#guard square [("Cells", Cells), ("W", .omegaWhere [("v", .range 1 3)] (.call "not" [.call "=" [.attr "v", .val (.int 2)]])),
  ("S", .omegaSol (.name "Cells") (.name "W")),
  ("T", .sigmaSol (.expr (.gamma [] (.call "<=" [.agg "sum" (.attr "v"), .val (.int 5)]) none (.name "S"))) (.name "S"))]

-- Empty Data: no cells, one candidate (the empty one).
#guard square [("E", .omegaRows [("c", .range 1 3)] []), ("V", V),
  ("S", .omegaSol (.name "E") (.name "V")),
  ("T", .sigmaSol (.expr (.gamma [] (.call "=" [.agg "count" (.attr "c"), .val (.int 0)]) none (.name "S"))) (.name "S"))]

-- A Data under π (numbered in the order π gives).
#guard square [("B", .project ["c", "r"] Board), ("Sym", Sym),
  ("S", .omegaSol (.name "B") (.name "Sym")),
  ("T", .sigmaSol (allDiffBy "r" (.name "S")) (.name "S"))]

-- Rationals: a decision over halves, its sum bounded.
def Halves : Expr := .omega [("v", .set [.int 0, Value.ofRat (1/2), .int 1])]
#guard square [("Cells", Cells), ("H", Halves), ("S", .omegaSol (.name "Cells") (.name "H")),
  ("T", .sigmaSol (.expr (.gamma [] (.call "=" [.agg "sum" (.attr "v"), .val (.int 1)]) none
    (.nary .join [.name "S", .omegaRows [("v", .kind .rat)] [[Value.ofRat (1/2)], [.int 1]]]))) (.name "S"))]

/-! ## Refusals -/

-- Grouping by a cell.
#guard refused (base ++ [("T", .sigmaSol (.expr (.gamma [] (.agg "bool_and" (.call ">=" [.attr "n", .val (.int 0)])) none
  (.gamma ["v"] (.agg "count" (.attr "c")) (some "n") (.name "S")))) (.name "S"))])
-- min over guarded rows.
#guard refused (base ++ [("T", .sigmaSol (.expr (.gamma [] (.call ">=" [.agg "min" (.attr "c"), .val (.int 1)]) none
  (.nary .join [.name "S", .name "Two"]))) (.name "S"))])
-- `v + 1` on a cell that may hold a symbol.
#guard refused [("Cells", Cells), ("V", .omega [("v", .set [.int 1, .symbol "a"])]),
  ("S", .omegaSol (.name "Cells") (.name "V")),
  ("T", .sigmaSol (.expr (.gamma [] (.call "<=" [.agg "sum" (.call "+" [.attr "v", .val (.int 1)]), .val (.int 9)]) none (.name "S"))) (.name "S"))]
-- abs on a cell that may hold a rat.
#guard refused [("Cells", Cells), ("H", Halves), ("S", .omegaSol (.name "Cells") (.name "H")),
  ("T", .sigmaSol (.expr (.gamma [] (.call "<=" [.agg "sum" (.call "abs" [.attr "v"]), .val (.int 9)]) none (.name "S"))) (.name "S"))]
-- A guarded group, with `by`, under a condition.
#guard refused (base ++ [("T", .sigmaSol (.expr (.gamma ["c"] (.agg "count" (.attr "v")) none
  (.nary .join [.name "S", .name "Two"]))) (.name "S"))])
-- A level-2 condition that may refuse, though the evaluator never reaches it (level 1
-- rejects every candidate): φ refuses.
#guard refused [("Cells", Cells), ("V", .omega [("v", .set [.int 1, .symbol "a"])]),
  ("S", .omegaSol (.name "Cells") (.name "V")),
  ("T", .sigmaSol (.expr (.gamma [] (.call "<" [.agg "count" (.attr "c"), .val (.int 0)]) none (.name "S"))) (.name "S")),
  ("U", .sigmaSol (.expr (.gamma [] (.call "<=" [.agg "sum" (.attr "v"), .val (.int 9)]) none (.name "T"))) (.name "T"))]
-- A statement outside the fragment.
#guard refused (base ++ [("T", .sigmaSol (.hasSubset (.name "S")) (.name "S"))])

/-! ## The ℰ_sol key -/

/-- The key square holds on every assignment of the last statement. -/
def keySquare (p : Program) : Bool :=
  match checkKeySquare p (last p) with
  | .ok (_, 0, 0) => true
  | _ => false

def keyTried (p : Program) : Nat :=
  match checkKeySquare p (last p) with
  | .ok (n, _, _) => n
  | _ => 0

def keyRefused (p : Program) : Bool := (phiKey p (last p)).toOption.isNone

/-- The knapsack's weight taken, as an ℰ_sol key. -/
def weightKey : Expr := .gamma [] (.agg "sum" (.call "*" [.attr "w", .attr "take"])) none (.name "T")
def knapKey : Program := knap ++ [("E", .enumSol (.int 2) (some (.desc, weightKey)) (.name "T"))]

#guard keySquare knapKey
#guard keyTried knapKey = 8

/-- A key reading a Data-only relation through a join: the price of what is taken. -/
def Price : Expr := .omegaRows [("i", .range 1 3), ("price", .range 0 9)]
  [[.int 1, .int 2], [.int 2, .int 7], [.int 3, .int 1]]
def priceKey : Expr := .gamma [] (.agg "sum" (.call "*" [.attr "price", .attr "take"])) none
  (.nary .join [.name "T", .name "Price"])
def knapPrice : Program := knap ++ [("Price", Price),
  ("E", .enumSol (.int 2) (some (.asc, priceKey)) (.name "T"))]

#guard keySquare knapPrice
#guard keyTried knapPrice = 8

/-- The key is the operand itself: the Data is one tuple with no attribute, so each
candidate is one tuple with one attribute, and the key term is the cell `take1`. -/
def One : Expr := .omegaRows [] [[]]
def oneKey : Program := [("One", One), ("Take", Take),
  ("S", .omegaSol (.name "One") (.name "Take")),
  ("E", .enumSol (.int 2) (some (.desc, .name "S")) (.name "S"))]

#guard keySquare oneKey
#guard keyTried oneKey = 2
#guard match phiKey oneKey (last oneKey) with
  | .ok (_, .attr "take1") => true
  | _ => false

/-- A key joining on a Decision attribute: the rows' guards are not `tt`, and the sum runs
its guarded path, while the γ[]'s own row stays present. -/
def Bonus : Expr := .omegaRows [("take", .range 0 1), ("bonus", .range 0 9)] [[.int 1, .int 5]]
def bonusKey : Expr := .gamma [] (.agg "sum" (.attr "bonus")) none
  (.nary .join [.name "T", .name "Bonus"])
def knapBonus : Program := knap ++ [("Bonus", Bonus),
  ("E", .enumSol (.int 3) (some (.desc, bonusKey)) (.name "T"))]

#guard keySquare knapBonus
#guard keyTried knapBonus = 8

/-- A key that gives one tuple per item is refused, as the evaluator refuses it. -/
def perItem : Expr := .gamma ["i"] (.agg "sum" (.attr "take")) none (.name "T")
#guard keyRefused (knap ++ [("E", .enumSol (.int 2) (some (.asc, perItem)) (.name "T"))])

-- A statement with no key has no φ of a key.
#guard keyRefused (knap ++ [("E", .enumSol (.int 2) none (.name "T"))])


/-! ## Multi solution sets -/

namespace Msol

def last (p : Program) : Nat := p.length - 1

def square (p : Program) : Bool :=
  match checkSquareMsol p (last p) with
  | .ok (_, 0, 0) => true
  | _ => false

def tried (p : Program) : Nat :=
  match checkSquareMsol p (last p) with
  | .ok (n, _, _) => n
  | _ => 0

def cellNames (p : Program) : List String :=
  match phiMsol p (last p) with
  | .ok M => M.cells.map (·.1)
  | .error _ => []

def refused (p : Program) : Bool := (phiMsol p (last p)).toOption.isNone

def TakeB : Expr := .omega [("tb", .range 0 1)]

/-- No item is taken by both members. -/
def notBoth : Cond :=
  .expr (.gamma [] (.agg "bool_and" (.call "<=" [.call "+" [.attr "take", .attr "tb"], .val (.int 1)])) none
    (.nary .join [.name "A", .name "B"]))

/-- `A`'s weight is at most 8. -/
def lightA (e : Expr) : Cond :=
  .expr (.gamma [] (.call "<=" [.agg "sum" (.call "*" [.attr "w", .attr "take"]), .val (.int 8)]) none e)

def base : Program := [("Items", Items), ("Take", Take), ("TakeB", TakeB),
  ("SA", .omegaSol (.name "Items") (.name "Take")),
  ("SB", .omegaSol (.name "Items") (.name "TakeB"))]

/-- Two members with a joint condition. -/
def two : Program := base ++ [("M", .omegaMsol [("A", .name "SA"), ("B", .name "SB")] (some notBoth))]

#guard cellNames two = ["A_take_1", "A_take_2", "A_take_3", "B_tb_1", "B_tb_2", "B_tb_3"]
#guard square two
#guard tried two = 64

/-- A member written as a `σ_sol` in the statement itself, and no condition. -/
def inner : Program := base ++
  [("M", .omegaMsol [("A", .sigmaSol (lightA (.name "SA")) (.name "SA")), ("B", .name "SB")] none)]

#guard square inner
#guard tried inner = 64

/-- A `σ_msol` over a name for an earlier multi solution set (as Racket's `Plan`). -/
def later : Program := two ++
  [("N", .sigmaMsol (.expr (.gamma [] (.call ">=" [.agg "sum" (.call "*" [.attr "w", .attr "tb"]), .val (.int 5)]) none (.name "B"))) (.name "M"))]

#guard square later
#guard tried later = 64

-- Refusals: no member; a member named I; two members with one name; a reserved name;
-- has_subset in a multi solution set's condition.
#guard refused (base ++ [("M", .omegaMsol [] none)])
#guard refused (base ++ [("M", .omegaMsol [("I", .name "SA")] none)])
#guard refused (base ++ [("M", .omegaMsol [("A", .name "SA"), ("A", .name "SB")] none)])
#guard refused (base ++ [("M", .omegaMsol [("%leaf", .name "SA")] none)])
#guard refused (base ++ [("M", .omegaMsol [("A", .name "SA")]
  (some (.hasSubset (.omegaRows [("i", .range 1 3), ("w", .range 0 9), ("take", .range 0 1)] [[.int 1, .int 4, .int 1]]))))])

/-! ### The ℰ_msol key -/

def keySquare (p : Program) : Bool :=
  match checkKeySquareMsol p (last p) with
  | .ok (_, 0) => true
  | _ => false

def keyTried (p : Program) : Nat :=
  match checkKeySquareMsol p (last p) with
  | .ok (n, _) => n
  | _ => 0

/-- The weight both members take. -/
def bothWeight : Expr :=
  .gamma [] (.agg "sum" (.call "*" [.attr "w", .call "+" [.attr "take", .attr "tb"]])) none
    (.nary .join [.name "A", .name "B"])

def keyed : Program := two ++ [("E", .enumMsol (.int 3) (some (.desc, bothWeight)) (.name "M"))]

#guard keySquare keyed
#guard keyTried keyed = 64

-- A key that reads a member through a form φ takes as a leaf (here π) is refused.
#guard (phiMsolKey (two ++ [("E", .enumMsol (.int 3) (some (.desc, .project ["w"] (.name "A"))) (.name "M"))]) 6).toOption.isNone

end Msol

/-! ## `=` between a symbol and a string

`applyOp` refuses it, so φ refuses an `=` whose operands may be a symbol and a
string. -/

#guard (opKinds "=" [[.sym], [.str]]).toOption.isNone
#guard (opKinds "=" [[.sym, .int], [.int, .str]]).toOption.isNone
#guard (opKinds "=" [[.sym], [.sym]]).toOption == some [.bool]

end Rasso.Phi.Examples
