import Coddstheorem.Calculus
import Coddstheorem.Algebra
import Coddstheorem.AlgebraToCalculus
import Coddstheorem.CalculusToAlgebra
import Rasso.Eval

/-!
# Codd's theorem for Rasso: examples

A test, not a proof. Each
`#guard` is checked by Lean when the file is built:

* the algebra side runs the compiled form with Rasso's evaluator (`Rasso.Expr.eval`);
* the calculus side lists the active-domain answers with `Query.answersList`, which
  `Query.mem_answersList` proves is exactly `Query.answers`;
* the two are compared as sets, and both against the answer worked out by hand.

The database: employees and departments, every value a symbol (`D = symbol`).

| Emp: name | dept |   | Dept: dept | floor |
|---|---|---|---|---|
| ann | sales |   | sales | f1 |
| bob | sales |   | dev | f2 |
| cat | dev |   | hr | f1 |

and a nullary relation `Flag` holding the empty tuple (so it is "true").
-/

namespace Coddstheorem.Examples

open Rasso Coddstheorem

def D : Domain := .kind .symbol
def sym (s : String) : Value := .symbol s

def S : Schema := [("Emp", ["name", "dept"]), ("Dept", ["dept", "floor"]), ("Flag", [])]

def rowsOf (as : List String) (rows : List (List String)) : Finrel :=
  Finrel.ofTuples (headerOf D as) (rows.map fun r => Tuple.ofPairs (as.zip (r.map sym)))

def env : Env :=
  [("Emp", .finrel (rowsOf ["name", "dept"] [["ann", "sales"], ["bob", "sales"], ["cat", "dev"]])),
   ("Dept", .finrel (rowsOf ["dept", "floor"] [["sales", "f1"], ["dev", "f2"], ["hr", "f1"]])),
   ("Flag", .finrel (rowsOf [] [[]]))]

/-- The same schema with nothing stored: the active domain is empty. -/
def envEmpty : Env :=
  [("Emp", .finrel (rowsOf ["name", "dept"] [])), ("Dept", .finrel (rowsOf ["dept", "floor"] [])),
   ("Flag", .finrel (rowsOf [] []))]

#guard decide S.WF
#guard DomOK D

/-- The tuples Rasso's evaluator gives for an algebra query (none if it refuses). -/
def runA (env : Env) (e : CRA) : Option (List Tuple) :=
  match Expr.eval env [] (e.toExpr D) with
  | .ok (.finrel r) => some r.tuples
  | _ => none

/-- The active-domain answers of a calculus query. -/
def runC (env : Env) (q : Query) : List Tuple := q.answersList (q.adom S env) S env

def sameSet (l l' : List Tuple) : Bool := l.all l'.contains && l'.all l.contains

def tup (ps : List (String × String)) : Tuple := Tuple.ofPairs (ps.map fun (a, v) => (a, sym v))

/-! ## 1. Who works on floor f1? -/

def a1 : CRA := .proj ["name"] (.sel (.eqC "floor" (sym "f1")) (.join (.rel "Emp") (.rel "Dept")))
def q1 : Query :=
  ⟨[("name", "n")], .ex "d" (.ex "f" (.and (.and (.rel "Emp" ["n", "d"]) (.rel "Dept" ["d", "f"]))
      (.eqc "f" (sym "f1"))))⟩
def ans1 : List Tuple := [tup [("name", "ann")], tup [("name", "bob")]]

#guard a1.WT S D
#guard decide (q1.WT S D)
#guard (runA env a1).map (sameSet · ans1) == some true
#guard sameSet (runC env q1) ans1

/-! ## 2. Departments with no employees (difference) -/

def a2 : CRA := .diff (.proj ["dept"] (.rel "Dept")) (.proj ["dept"] (.rel "Emp"))
def q2 : Query :=
  ⟨[("dept", "d")], .and (.ex "f" (.rel "Dept" ["d", "f"])) (.not (.ex "n" (.rel "Emp" ["n", "d"])))⟩
def ans2 : List Tuple := [tup [("dept", "hr")]]

#guard a2.WT S D
#guard decide (q2.WT S D)
#guard (runA env a2).map (sameSet · ans2) == some true
#guard sameSet (runC env q2) ans2

/-! ## 3. A swap by ρ: attribute and variable names part company -/

def a3 : CRA := .ren [("name", "dept"), ("dept", "name")] (.rel "Emp")
def q3 : Query := ⟨[("dept", "n"), ("name", "d")], .rel "Emp" ["n", "d"]⟩
def ans3 : List Tuple :=
  [tup [("dept", "ann"), ("name", "sales")], tup [("dept", "bob"), ("name", "sales")],
   tup [("dept", "cat"), ("name", "dev")]]

#guard a3.WT S D
#guard decide (q3.WT S D)
#guard (runA env a3).map (sameSet · ans3) == some true
#guard sameSet (runC env q3) ans3

/-! ## 4. `x = x`: every value of the active domain -/

def q4 : Query := ⟨[("v", "x")], .eqv "x" "x"⟩
-- ann, bob, cat, sales, dev, f1, f2, hr. (`answersList` may repeat a tuple: the active
-- domain is a list with repeats. Answers are compared as sets.)
#guard (runC env q4).eraseDups.length == 8

/-! ## 5. A nullary relation, and an empty active domain -/

def a5 : CRA := .rel "Flag"
def q5 : Query := ⟨[], .rel "Flag" []⟩
#guard (runA env a5) == some [[]]
#guard runC env q5 == [[]]
#guard (runA envEmpty a5) == some []
#guard runC envEmpty q5 == []
/-- `∀ z. z = z` is true even on the empty domain: one answer, the empty tuple. -/
def qTrue : Query := ⟨[], .all "%z" (.eqv "%z" "%z")⟩
#guard runC envEmpty qTrue == [[]]
#guard runC envEmpty q4 == []

/-! ## 6. Constant relations, and refusals the typing rules out -/

def a6 : CRA := .union (.lit ["dept"] [[sym "ops"]]) (.proj ["dept"] (.rel "Dept"))
#guard a6.WT S D
#guard (runA env a6).map (·.length) == some 4
/-- ∪ of different attributes: not well typed, and Rasso's evaluator refuses it. -/
def bad : CRA := .union (.proj ["dept"] (.rel "Dept")) (.proj ["name"] (.rel "Emp"))
#guard !bad.WT S D
#guard runA env bad == none

/-! ## The compiled forms are forms the surface accepts (a check, not a proof) -/

#guard [a1, a2, a3, a5, a6].all fun e => (e.toExpr D).problem.isNone

/-! ## 7. Theorem A at work: `toCalc` and the evaluator agree

`CRA.toCalc` translates an algebra query into a calculus query
(`Coddstheorem/AlgebraToCalculus.lean`). Theorem A says the two have the same answers;
here the machine checks it on the examples, through Rasso's evaluator and
`answersList`. -/

/- ρ only changes which variable stands for which attribute: the swap of `name` and
`dept` reads `Emp`'s columns the other way round. -/
#guard (a3.toCalc S D).body == .rel "Emp" ["dept", "name"]
#guard (a3.toCalc S D).out == [("dept", "dept"), ("name", "name")]

/- π binds a fresh variable for each attribute it drops (`%dept%`, `%floor%`), so ⋈'s
shared `dept` becomes one bound variable. -/
#guard (a1.toCalc S D).body ==
  .ex "%dept%" (.ex "%floor%"
    (.and (.and (.rel "Emp" ["name", "%dept%"]) (.rel "Dept" ["%dept%", "%floor%"]))
      (.eqc "%floor%" (sym "f1"))))

/-- Nested π: the inner and outer fresh names differ by depth (`%floor%` at depth 0,
`%dept%#` at depth 1). -/
def a7 : CRA := .proj ["name"] (.proj ["name", "floor"] (.join (.rel "Emp") (.rel "Dept")))
#guard a7.WT S D
#guard (a7.toCalc S D).body ==
  .ex "%floor%" (.ex "%dept%#" (.and (.rel "Emp" ["name", "%dept%#"]) (.rel "Dept" ["%dept%#", "%floor%"])))

/-- The translations are well typed, and on both databases the evaluator and the
calculus give the same answers. -/
def agree (env : Env) (e : CRA) : Bool :=
  match runA env e with
  | some ts => sameSet ts (runC env (e.toCalc S D))
  | none => false

#guard [a1, a2, a3, a5, a6, a7].all fun e => decide ((e.toCalc S D).WT S D)
#guard [a1, a2, a3, a5, a6, a7].all (agree env)
#guard [a1, a2, a3, a5, a6, a7].all (agree envEmpty)

/-! ## 8. Theorem B at work: `toRA` and the calculus agree

`Query.toRA` translates a calculus query into an algebra query
(`Coddstheorem/CalculusToAlgebra.lean`). Theorem B says the algebra query is well typed
and gives exactly the active-domain answers; here the machine checks it on the examples.
The translation builds the active domain as a relation, and `¬` takes a difference from
every assignment of active-domain values to its variables, so the queries here have at
most three variables. -/

/- Variables become attributes `v_` and the character codes: `n` is `v_110`. -/
#guard enc "n" == "v_110"

/- `∃ x` with `x` not free: true only when the active domain has a value, so false on the
empty database even though `Flag` is set (theorem B pads with the active domain). -/
def q6 : Query := ⟨[], .ex "x" (.rel "Flag" [])⟩
/- One variable for two output attributes. -/
def q7 : Query := ⟨[("a", "n"), ("b", "n")], .ex "d" (.rel "Emp" ["n", "d"])⟩
/- `∀`: the values `d` such that every employee of `d` is ann (in the active domain, so
also `ann`, `f1`, … that have no employees). -/
def q8 : Query := ⟨[("dept", "d")], .all "n" (.or (.not (.rel "Emp" ["n", "d"])) (.eqc "n" (sym "ann")))⟩
/- An output variable the body does not mention ranges over the active domain. -/
def q9 : Query := ⟨[("x", "x")], .rel "Flag" []⟩
/- `∨` of formulas with different variables, and `x = y`. -/
def q10 : Query := ⟨[("x", "x"), ("y", "y")], .or (.rel "Dept" ["x", "y"]) (.and (.eqv "x" "y") (.eqc "x" (sym "ops")))⟩

def qs : List Query := [q1, q2, q3, q4, q5, qTrue, q6, q7, q8, q9, q10]

/-- On a database, the evaluator runs `toRA` without refusing and gives the calculus's
answers. -/
def agreeB (env : Env) (q : Query) : Bool :=
  match runA env (q.toRA S) with
  | some ts => sameSet ts (runC env q)
  | none => false

#guard qs.all fun q => decide (q.WT S D)
#guard qs.all fun q => (q.toRA S).WT S D
#guard qs.all fun q => (q.toRA S).check S D == some (q.out.map (·.1))
#guard qs.all (agreeB env)
#guard qs.all (agreeB envEmpty)
#guard runA envEmpty (q6.toRA S) == some []
#guard runA env (q6.toRA S) == some [[]]
#guard (runA env (q8.toRA S)).map (·.length) == some 6

/-! ## 9. Codd's theorem at work: the round trips

`Coddstheorem/Theorem.lean` puts theorems A and B together. Here the machine checks the
round trips on the examples: an algebra query, translated to the calculus and back, gives
the same relation; a calculus query, translated to the algebra and back, gives the same
answers. (Only small queries: each `π` adds a bound variable, and the way back multiplies
the active domain once per variable.) -/

/-- An algebra query and its round trip through the calculus give the same tuples. -/
def roundA (env : Env) (e : CRA) : Bool :=
  match runA env e, runA env ((e.toCalc S D).toRA S) with
  | some ts, some ts' => sameSet ts ts'
  | _, _ => false

#guard [a1, a2, a3, a5, a6, a7].all (roundA env)
#guard [a1, a2, a3, a5, a6, a7].all (roundA envEmpty)
#guard [q1, q3, q5, q7, q9].all fun q => sameSet (runC env q) (runC env ((q.toRA S).toCalc S D))

/-! ## 10. Order comparisons

A second schema over `int`: `Item(id, price)`. σ and the calculus compare by Rasso's value
order (`Value.cmp`); the comparisons never refuse. -/

def DI : Domain := .kind .int
def SI : Schema := [("Item", ["id", "price"])]

def intRows (as : List String) (rows : List (List Int)) : Finrel :=
  Finrel.ofTuples (headerOf DI as) (rows.map fun r => Tuple.ofPairs (as.zip (r.map .int)))

def envI : Env := [("Item", .finrel (intRows ["id", "price"] [[1, 5], [2, 12], [3, 8], [4, 12]]))]
def envIEmpty : Env := [("Item", .finrel (intRows ["id", "price"] []))]

def runAI (env : Env) (e : CRA) : Option (List Tuple) :=
  match Expr.eval env [] (e.toExpr DI) with
  | .ok (.finrel r) => some r.tuples
  | _ => none

def runCI (env : Env) (q : Query) : List Tuple := q.answersList (q.adom SI env) SI env

def itup (ps : List (String × Int)) : Tuple := Tuple.ofPairs (ps.map fun (a, v) => (a, .int v))

/- Items cheaper than 10 (σ against a constant). -/
def b1 : CRA := .proj ["id"] (.sel (.cmpC .lt "price" (.int 10)) (.rel "Item"))
def p1 : Query := ⟨[("id", "i")], .ex "p" (.and (.rel "Item" ["i", "p"]) (.cmpc .lt "p" (.int 10)))⟩
/- Items that some other item costs more than (σ comparing two attributes). -/
def b2 : CRA := .proj ["id"] (.sel (.cmpA .lt "price" "p2")
  (.prod (.rel "Item") (.ren [("id", "id2"), ("price", "p2")] (.rel "Item"))))
def p2 : Query := ⟨[("id", "i")], .ex "p" (.and (.rel "Item" ["i", "p"])
  (.ex "j" (.ex "q" (.and (.rel "Item" ["j", "q"]) (.cmpv .lt "p" "q")))))⟩
/- The most expensive items (`∀` with `≤`). -/
def p3 : Query := ⟨[("id", "i")], .ex "p" (.and (.rel "Item" ["i", "p"])
  (.all "q" (.or (.not (.ex "j" (.rel "Item" ["j", "q"]))) (.cmpv .le "q" "p"))))⟩

#guard b1.WT SI DI && b2.WT SI DI
#guard [p1, p2, p3].all fun q => decide (q.WT SI DI)
#guard (runAI envI b1).map (sameSet · [itup [("id", 1)], itup [("id", 3)]]) == some true
#guard (runAI envI b2).map (sameSet · [itup [("id", 1)], itup [("id", 3)]]) == some true
#guard sameSet (runCI envI p1) [itup [("id", 1)], itup [("id", 3)]]
#guard sameSet (runCI envI p2) [itup [("id", 1)], itup [("id", 3)]]
#guard sameSet (runCI envI p3) [itup [("id", 2)], itup [("id", 4)]]

/-- Theorem A at work: the evaluator and the translation agree. -/
def agreeI (env : Env) (e : CRA) : Bool :=
  match runAI env e with
  | some ts => sameSet ts (runCI env (e.toCalc SI DI))
  | none => false

/-- Theorem B at work. -/
def agreeBI (env : Env) (q : Query) : Bool :=
  match runAI env (q.toRA SI) with
  | some ts => sameSet ts (runCI env q)
  | none => false

#guard [b1, b2].all (agreeI envI) && [b1, b2].all (agreeI envIEmpty)
#guard [p1, p2].all fun q => (q.toRA SI).WT SI DI
#guard [p1, p2].all (agreeBI envI) && [p1, p2].all (agreeBI envIEmpty)

/- `{x | x < 5}` is accepted by the calculus but is not domain independent: adding the
value 0 to the domain adds an answer (1, 2, 3, 4 become 0, 1, 2, 3, 4). Theorem C says
nothing about it. -/
def pLow : Query := ⟨[("x", "x")], .cmpc .lt "x" (.int 5)⟩
#guard (pLow.answersList (pLow.adom SI envI) SI envI).eraseDups.length == 4
#guard (pLow.answersList (.int 0 :: pLow.adom SI envI) SI envI).eraseDups.length == 5

end Coddstheorem.Examples
