import Rasso.Term
import Rasso.Form

/-!
# Examples: a symbol beside a string

Each `#guard` is run when the file is built. They check that `=` refuses to compare a
symbol with a string, as it refuses an int or a rat with a float, so that
`name = "apple"` over a symbol column is an error, not an empty result. The words are Racket's
(`value=` in `rasso/finrel.rkt`).
-/

namespace Rasso.Examples.SymbolString

open Rasso

def errOf : Except String Value → Option String
  | .error m => some m
  | .ok _ => none

-- refused, naming both types, either way round
#guard errOf (applyOp "=" [.symbol "apple", .string "apple"]) ==
  some "apple = \"apple\" compares a symbol with a string: give both one type"
#guard errOf (applyOp "=" [.string "apple", .symbol "apple"]) ==
  some "\"apple\" = apple compares a symbol with a string: give both one type"
-- two symbols, or two strings, are compared as before
#guard (applyOp "=" [.symbol "apple", .symbol "apple"]).toOption == some (.bool true)
#guard (applyOp "=" [.symbol "apple", .symbol "pear"]).toOption == some (.bool false)
#guard (applyOp "=" [.string "apple", .string "apple"]).toOption == some (.bool true)
-- the orders still compare them (symbols before strings), as Racket's do not
#guard (applyOp "<" [.symbol "b", .string "a"]).toOption == some (.bool true)

-- a set domain may not hold both: no domain's `=` refuses its own values
#guard (headingProblem true [("x", .set [.symbol "a", .string "b"])]).isSome
#guard (headingProblem true [("x", .set [.symbol "a", .symbol "b"])]).isNone

-- φ refuses an `=` that may meet a symbol and a string: `Rasso/Phi/Examples.lean`

end Rasso.Examples.SymbolString
