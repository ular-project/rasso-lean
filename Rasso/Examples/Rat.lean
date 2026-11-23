import Rasso.Json.Text
import Rasso.Term
import Rasso.Json.Surface

/-!
# Examples: rat values

Each `#guard` is run when the file is built. They check these decisions:

* One `1`: a whole number is an int, so `4/2` is the int `2`.
* `den = 0` gives 0, as Lean's `Rat.divInt` does.
* Two orders: the program's order `Value.cmp` compares numbers as numbers and
  keeps Racket's ties (`0`, `0.0`, `-0.0`); the canonical order (`compare`) breaks them
  by the key.
* `=` refuses a rat against a float, as it refuses an int against a float.
-/

namespace Rasso.Examples.Rat

open Rasso

def q (n d : Int) : Value := Value.ofRat (Rat.divInt n d)
def f (neg : Bool) (mant : Nat) (exp : Int) : Value := .float ⟨neg, mant, exp⟩

/-! ## One representation per number -/

#guard q 4 2 == .int 2
#guard q 1 0 == .int 0
#guard q (-3) 1 == .int (-3)
#guard q 1 (-2) == q (-1) 2
#guard (q 1 2).exact? == some (Rat.divInt 1 2)
#guard (q 2 4) == q 1 2
#guard (q 1 2).toString == "1/2"
#guard (q (-2) 5).toString == "-2/5"

/-! ## The program's order: numbers as numbers, Racket's ties -/

def lt (v w : Value) : Bool := Value.cmp v w == .lt

#guard lt (.int 0) (q 1 2) && lt (q 1 2) (.int 1)
#guard lt (q 1 3) (q 1 2)
#guard lt (q (-1) 2) (q (-1) 3)
#guard lt (q 1 2) (f false 6 (-1))          -- 1/2 < 0.6
#guard lt (f false 4 (-1)) (q 1 2)          -- 0.4 < 1/2
#guard !lt (.int 0) (f false 0 0) && !lt (f false 0 0) (.int 0)    -- 0 and 0.0 tie
#guard !lt (f true 0 0) (f false 0 0) && !lt (f false 0 0) (f true 0 0)   -- -0.0 and 0.0 tie
#guard Value.cmp (q 1 2) (f false 5 (-1)) == .eq    -- 1/2 and 0.5 tie
#guard lt (.int 5) (.symbol "a")               -- kind first

/-! ## The canonical order: `Value.cmp`, ties broken by the key -/

def sorted (vs : List Value) : List Value := vs.mergeSort Value.le

#guard sorted [.int 1, q 1 2, .int 0] == [.int 0, q 1 2, .int 1]
#guard sorted [f false 5 (-1), q 1 2, .int 1, .int 0, f false 2 0] ==
  [.int 0, q 1 2, f false 5 (-1), .int 1, f false 2 0]     -- 0.5 right after 1/2; 2.0 last
#guard sorted [f false 0 0, .int 0, f true 0 0] == [.int 0, f false 0 0, f true 0 0]
#guard sorted [f false 1 (-300), .int 0, q 1 (10 ^ 400)] ==
  [.int 0, q 1 (10 ^ 400), f false 1 (-300)]               -- tiny numbers sort at once
#guard (Domain.ofValues [.int 1, q 1 2, .int 1]).values? == some [q 1 2, .int 1]

/-! ## Equality and arithmetic -/

#guard (applyOp "=" [.int 1, q 2 2]).toOption == some (.bool true)
#guard (applyOp "=" [q 1 2, q 2 4]).toOption == some (.bool true)
#guard (applyOp "=" [q 1 2, f false 5 (-1)]).toOption.isNone     -- rat = float refused
#guard (applyOp "+" [q 1 2, q 1 2]).toOption == some (.int 1)
#guard (applyOp "+" [.int 1, q 1 3]).toOption == some (q 4 3)
#guard (applyOp "*" [q 2 3, .int 3]).toOption == some (.int 2)
#guard (applyOp "-" [q 1 2]).toOption == some (q (-1) 2)
#guard (applyOp "-" [.int 1, q 1 4, q 1 4]).toOption == some (q 1 2)
#guard (applyOp "sum" [q 1 3, q 1 3, q 1 3]).toOption == some (.int 1)
#guard (applyOp "+" [.int 2, .int 3]).toOption == some (.int 5)
#guard (applyOp "%" [q 1 2, .int 2]).toOption.isNone            -- % is int only
#guard (applyOp "<" [.int 1, q 3 2]).toOption == some (.bool true)
#guard (applyOp "min" [.int 1, q 1 2, .int 2]).toOption == some (q 1 2)

/-! ## Domains and term typing -/

#guard (Domain.kind .rat).mem (.int 3) && (Domain.kind .rat).mem (q 1 2)
#guard !(Domain.kind .int).mem (q 1 2)
#guard !(Domain.kind .rat).mem (f false 5 (-1))
#guard (Domain.inter (.kind .rat) (.kind .int)).toOption == some (.kind .int)
#guard (Domain.inter (.kind .int) (.kind .rat)).toOption == some (.kind .int)
#guard (Domain.inter (.kind .rat) (.range 0 3)).toOption == some (.range 0 3)
#guard (Domain.inter (.range 0 3) (.kind .rat)).toOption == some (.range 0 3)
#guard Term.domain [("x", .kind .rat), ("n", .kind .int)] (.call "+" [.attr "x", .attr "n"])
  == some (.kind .rat)
#guard Term.domain [("n", .kind .int)] (.call "+" [.attr "n", .val (.int 1)]) == some (.kind .int)
#guard Term.domain [("x", .kind .rat)] (.call "%" [.attr "x", .val (.int 2)]) == none

/-! ## JSON: `{"rat": {"num": n, "den": d}}` -/

def readValue (text : String) : Except String Value := do
  Json.value (← Json.read text) []

def printValue (v : Value) : Except String String := do
  return Json.J.compact (← Json.pValue v)

#guard (readValue "{\"rat\": {\"num\": 1, \"den\": 3}}").toOption == some (q 1 3)
#guard (readValue "{\"rat\": {\"num\": 4, \"den\": 2}}").toOption == some (.int 2)
#guard (readValue "{\"rat\": {\"num\": 1, \"den\": -2}}").toOption == some (q (-1) 2)
#guard (readValue "{\"rat\": {\"num\": 6, \"den\": 0}}").toOption == some (.int 0)
#guard (readValue "{\"rat\": {\"num\": 1}}").toOption.isNone
#guard (readValue "{\"rat\": {\"num\": 1.5, \"den\": 2}}").toOption.isNone
#guard (printValue (q 1 3)).toOption == some "{\"rat\":{\"num\":1,\"den\":3}}"
#guard (printValue (q (-1) 2)).toOption == some "{\"rat\":{\"num\":-1,\"den\":2}}"
#guard ((do readValue (← printValue (q (-7) 3)))).toOption == some (q (-7) 3)
#guard Json.Kind.ofName "rat" == some .rat
#guard nameProblem "rat" |>.isSome
#guard racketSymbolText "1/2" == "|1/2|" && racketSymbolText "a/b" == "a/b"

end Rasso.Examples.Rat
