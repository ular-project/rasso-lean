import Rasso.ESO.ToProgramG
import Rasso.ESO.Converse

/-!
# ESO examples: SAT and graph colouring

Run the construction of `Rasso.ESO.ToProgram` (Codd's translation) and
`Rasso.ESO.ToProgramG` (Racket's condition fragment) on small structures. This is a test,
not a proof. Each `#guard` runs the program with Rasso's evaluator and checks the answer
that the logic gives (worked out by hand, and, where the answer is yes, confirmed by a
witness guess that `FO.Sat` accepts). The same programs, printed as JSON, were also run
through Racket.

* **SAT, Fagin style.** A CNF formula is a structure: the universe holds its variables
  and its clauses, `C(c)` says `c` is a clause, `P(c, x)` that `x` occurs positively in
  `c`, `N(c, x)` that it occurs negatively. The sentence guesses the true variables `T`:

      ∃ T. ∀ c. C(c) → ∃ x. (P(c, x) ∧ T(x)) ∨ (N(c, x) ∧ ¬T(x))

* **2-colouring** (`∃ R B`, every vertex coloured, no edge inside one colour) of a path
  (yes) and of a triangle (no).
* **No second-order variables**: "every vertex has an out-edge", a first-order sentence,
  on a cycle (yes) and a path (no).
-/

namespace Rasso.ESO.Examples

open Rasso Rasso.ESO FO

def symbol (s : String) : Value := .symbol s

def imp (φ ψ : FO) : FO := .or (.not φ) ψ

/-! ## SAT -/

def satSentence : Sentence where
  ar := [("T", 1)]
  φ := .all "c" (imp (.rel "C" ["c"])
        (.ex "x" (.or (.and (.rel "P" ["c", "x"]) (.gvar "T" ["x"]))
                      (.and (.rel "N" ["c", "x"]) (.not (.gvar "T" ["x"]))))))
  closed := by decide

/-- (p ∨ q) ∧ (¬p ∨ q) ∧ (p ∨ ¬q): satisfiable, by p = q = true. -/
def cnfYes : Str := Str.ofList (["p", "q", "k1", "k2", "k3"].map symbol)
  [("C", [[symbol "k1"], [symbol "k2"], [symbol "k3"]]),
   ("P", [[symbol "k1", symbol "p"], [symbol "k1", symbol "q"], [symbol "k2", symbol "q"], [symbol "k3", symbol "p"]]),
   ("N", [[symbol "k2", symbol "p"], [symbol "k3", symbol "q"]])]

/-- p ∧ ¬p: unsatisfiable. -/
def cnfNo : Str := Str.ofList (["p", "k1", "k2"].map symbol)
  [("C", [[symbol "k1"], [symbol "k2"]]),
   ("P", [[symbol "k1", symbol "p"]]),
   ("N", [[symbol "k2", symbol "p"]])]

/-- The witness for `cnfYes`: both variables true. -/
def cnfYesWitness : Guess := fun j => if j = "T" then [[symbol "p"], [symbol "q"]] else []

#guard satSentence.problem.isNone
#guard decide (satSentence.φ.Sat cnfYes cnfYesWitness fun _ => default)
#guard (ToProgram.decide satSentence cnfYes).toOption == some true
#guard (ToProgram.decide satSentence cnfNo).toOption == some false

/-- x₁ ∧ (x₂ ∨ ¬x₃), the formula of the RassoReport blueprint's SAT examples: the clause
`c1` is x₁ and `c2` is x₂ ∨ ¬x₃. -/
def cnfReport : Str := Str.ofList (["x1", "x2", "x3", "c1", "c2"].map symbol)
  [("C", [[symbol "c1"], [symbol "c2"]]),
   ("P", [[symbol "c1", symbol "x1"], [symbol "c2", symbol "x2"]]),
   ("N", [[symbol "c2", symbol "x3"]])]

/-- The number of candidates of the program's `eso`. -/
def esoCandidates (ψ : Sentence) (A : Str) : Except String Nat := do
  match (← runProgram (toProgram ψ A)).lookup esoName with
  | some (.msol m) => return m.candidates.length
  | _ => throw "eso is not a multi solution set"

/- `T` is guessed over the whole universe, clauses included: 2⁵ = 32 guesses. Those that
pass are the 3 satisfying assignments of x₁, x₂, x₃, each with any values on `c1` and
`c2`: 3 × 4 = 12. -/
#guard (ToProgram.decide satSentence cnfReport).toOption == some true
#guard (esoCandidates satSentence cnfReport).toOption == some 12

/-! ## 2-colouring -/

def twoColour : Sentence where
  ar := [("R", 1), ("B", 1)]
  φ := .and (.all "x" (.or (.gvar "R" ["x"]) (.gvar "B" ["x"])))
        (.all "x" (.all "y" (imp (.rel "E" ["x", "y"])
          (.and (.not (.and (.gvar "R" ["x"]) (.gvar "R" ["y"])))
                (.not (.and (.gvar "B" ["x"]) (.gvar "B" ["y"])))))))
  closed := by decide

def path3 : Str := Str.ofList [.int 1, .int 2, .int 3]
  [("E", [[.int 1, .int 2], [.int 2, .int 3]])]

def triangle : Str := Str.ofList [.int 1, .int 2, .int 3]
  [("E", [[.int 1, .int 2], [.int 2, .int 3], [.int 3, .int 1]])]

def path3Witness : Guess := fun j =>
  if j = "R" then [[.int 1], [.int 3]] else if j = "B" then [[.int 2]] else []

#guard twoColour.problem.isNone
#guard decide (twoColour.φ.Sat path3 path3Witness fun _ => default)
#guard (ToProgram.decide twoColour path3).toOption == some true
#guard (ToProgram.decide twoColour triangle).toOption == some false

/-! ## Rat elements

The universe may hold rats: `Str.Comparable` forbids only mixing exact numbers with
floats (and symbols with strings). The same 2-colouring, on a path and a triangle whose vertices are 1/2, 1, 3/2.
Not in `all` below: the Racket JSON surface has no rat yet. -/

def half (n : Int) : Value := Value.ofRat (Rat.divInt n 2)

def ratPath : Str := Str.ofList [half 1, half 2, half 3]
  [("E", [[half 1, half 2], [half 2, half 3]])]

def ratTriangle : Str := Str.ofList [half 1, half 2, half 3]
  [("E", [[half 1, half 2], [half 2, half 3], [half 3, half 1]])]

#guard half 2 == .int 1
#guard (ToProgram.decide twoColour ratPath).toOption == some true
#guard (ToProgram.decide twoColour ratTriangle).toOption == some false
#guard (ToProgram.decideG twoColour ratPath).toOption == some true

/-! ## No second-order variables -/

def outEdge : Sentence where
  ar := []
  φ := .all "x" (.ex "y" (.rel "E" ["x", "y"]))
  closed := by decide

#guard (ToProgram.decide outEdge triangle).toOption == some true
#guard (ToProgram.decide outEdge path3).toOption == some false

/-! ## Equality and a repeated variable -/

/-- "Some vertex has a loop, or two distinct vertices exist": `E(x, x)` repeats `x`. -/
def loopOrTwo : Sentence where
  ar := []
  φ := .or (.ex "x" (.rel "E" ["x", "x"])) (.ex "x" (.ex "y" (.not (.eq "x" "y"))))
  closed := by decide

def oneLoop : Str := Str.ofList [.int 7] [("E", [[.int 7, .int 7]])]
def oneBare : Str := Str.ofList [.int 7] []

#guard (ToProgram.decide loopOrTwo oneLoop).toOption == some true
#guard (ToProgram.decide loopOrTwo oneBare).toOption == some false
#guard (ToProgram.decide loopOrTwo path3).toOption == some true

/-- The examples, by name, for runs through Racket (the answer is the one checked
above). -/
def all : List (String × Sentence × Str × Bool) :=
  [("sat_yes", satSentence, cnfYes, true), ("sat_no", satSentence, cnfNo, false),
   ("two_colour_path", twoColour, path3, true), ("two_colour_triangle", twoColour, triangle, false),
   ("out_edge_cycle", outEdge, triangle, true), ("out_edge_path", outEdge, path3, false),
   ("loop_or_two_loop", loopOrTwo, oneLoop, true), ("loop_or_two_bare", loopOrTwo, oneBare, false)]

-- Both constructions give every example's answer.
#guard all.all fun (_, ψ, A, ans) =>
  (ToProgram.decide ψ A).toOption == some ans && (ToProgram.decideG ψ A).toOption == some ans

/-! ## A BoolSelection query (the converse, `Rasso.ESO.Converse`)

"Some edge ends in a vertex of the member R, and the universe is not empty": a `Query`, run as
the multi solution set `Query.form`. -/

def edgeIntoMember : Query :=
  ⟨[("R", 1)], .and (.some (.join (.rel "E" ["x", "y"]) (.member "R" ["y"])))
    (.not (.some (.diff (.eq "x" "x") (.eq "x" "x"))))⟩

def runQuery (Q : Query) (A : Str) : Option Bool :=
  match Expr.eval [] [] (Q.form A) with
  | .ok (.msol m) => some !m.candidates.isEmpty
  | _ => none

#guard runQuery edgeIntoMember path3 == some true
#guard runQuery edgeIntoMember triangle == some true
#guard runQuery edgeIntoMember oneBare == some false

end Rasso.ESO.Examples
