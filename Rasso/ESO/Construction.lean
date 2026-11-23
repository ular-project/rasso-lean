import Rasso.ESO.ToProgram

/-!
# ESO: the construction, with its data as parameters

`Rasso.ESO.ToProgram.compile` names its data: the universe is the statement `univ`, a
relation symbol is the statement `rel_i_n`. Here the same translation takes the forms for
the universe (`U`) and for each symbol at each arity (`R i n`) as parameters, so that a
proof can give them either as names (`compile` is the case `U = .name univName`,
`compile_eq_compileP`) or as the data itself, written in the form (`esoForm`).

`esoForm ψ A` is one Rasso form: the multi solution set of `toProgram ψ A`, with the
structure's data written into it as ω-with-rows literals instead of named statements.
The forward ESO theorem (`Rasso.ESO.Capture`) is about it. Writing the data in place
means the proof needs no facts about which statement names differ.

Conventions:

* The theorem is stated for `esoForm`, not for `toProgram`. The two differ only in where
  the data is written: in the form, or in named statements before it. Relating them
  needs only that the statement names `univ` and `rel_i_n` are all different, which is
  string reasoning left for later.
-/

namespace Rasso.ESO

open Rasso

/-- `U` once for each name, the copy for `a` renamed to attribute `f a`. -/
def univPowP (U : Expr) (f : String → String) (as : List String) : Expr :=
  joinAll (as.map fun a => .rename [(univAttr, f a)] U)

/-- Every assignment to some variables: `U^xs`. -/
def domOfP (U : Expr) (xs : List String) : Expr := univPowP U varAttr xs

def padP (U : Expr) (r : Expr) (xs : List String) : Expr :=
  if xs.isEmpty then r else .nary .join [r, domOfP U xs]

def emptyOnP (U : Expr) (xs : List String) : Expr := .nary .except [domOfP U xs, domOfP U xs]

def atomP (U : Expr) (base : Expr) (cs : List String) (extra : List Term) (args : List String) : Expr :=
  let xs := args.eraseDups
  .project (xs.map varAttr)
    (.select (conj (extra ++ (cs.zip args).map fun (c, x) => eqT c (varAttr x)))
      (.nary .join [base, domOfP U xs]))

/-- Codd's translation of `compile`, with the data as parameters. -/
def compileP (U : Expr) (R : String → Nat → Expr) (ar : List (String × Nat)) : FO → Expr
  | .rel i args => atomP U (R i args.length) (cols args.length) [] args
  | .gvar j args =>
    if ar.lookup j = some args.length then
      atomP U (.name (memberName j)) (cols args.length)
        [.call "=" [.attr holdsAttr, .val (.bool true)]] args
    else emptyOnP U args.eraseDups
  | .eq x y => if x = y then domOfP U [x] else .select (eqT (varAttr x) (varAttr y)) (domOfP U [x, y])
  | .not φ => .nary .except [domOfP U φ.vars, compileP U R ar φ]
  | .and φ ψ => .nary .join [compileP U R ar φ, compileP U R ar ψ]
  | .or φ ψ =>
    .nary .union [padP U (compileP U R ar φ) (ψ.vars.filter (!φ.vars.contains ·)),
                  padP U (compileP U R ar ψ) (φ.vars.filter (!ψ.vars.contains ·))]
  | .ex x φ =>
    .project ((FO.ex x φ).vars.map varAttr)
      (padP U (compileP U R ar φ) (if φ.vars.contains x then [] else [x]))
  | .all x φ =>
    let ys := if φ.vars.contains x then φ.vars else φ.vars ++ [x]
    let notφ := Expr.nary .except [domOfP U ys, padP U (compileP U R ar φ) (if φ.vars.contains x then [] else [x])]
    let zs := (FO.all x φ).vars
    .nary .except [domOfP U zs, .project (zs.map varAttr) notφ]

/-- `compile` is the named case. -/
theorem compile_eq_compileP (ar : List (String × Nat)) :
    ∀ φ : FO, compile ar φ = compileP (.name univName) (fun i n => .name (relName i n)) ar φ
  | .rel i args => rfl
  | .gvar j args => rfl
  | .eq x y => rfl
  | .not φ => by simp only [compile, compileP, compile_eq_compileP ar φ]; rfl
  | .and φ ψ => by simp only [compile, compileP, compile_eq_compileP ar φ, compile_eq_compileP ar ψ]
  | .or φ ψ => by simp only [compile, compileP, compile_eq_compileP ar φ, compile_eq_compileP ar ψ]; rfl
  | .ex x φ => by simp only [compile, compileP, compile_eq_compileP ar φ]; rfl
  | .all x φ => by simp only [compile, compileP, compile_eq_compileP ar φ]; rfl

/-! ## The data written in place -/

/-- The universe as a literal: one attribute `e`, one row per element. -/
def univLit (A : Str) : Expr :=
  .omegaRows [(univAttr, univDom A)] ((racketSorted A.univ).map ([·]))

/-- Symbol `i` at arity `n` as a literal: its tuples of length `n` over the universe. -/
def relLit (A : Str) (i : String) (n : Nat) : Expr := (relStatement A i n).2

/-- The member for a second-order variable, with the universe given by `U`. -/
def boolMemberP (U : Expr) (j : String) (k : Nat) : String × Expr :=
  (memberName j, .omegaSol (univPowP U id (cols k)) (.omega [(holdsAttr, .kind .bool)]))

/-- The members of the multi solution set (one unused member when there are no
second-order variables, as in `toProgram`). -/
def membersP (U : Expr) (ar : List (String × Nat)) : List (String × Expr) :=
  match members ar with
  | [] => [boolMemberP U "" 0]
  | ms => ms.map fun (j, k) => boolMemberP U j k

/-- The multi solution set of `toProgram ψ A`, with the data written in place. -/
def esoForm (ψ : Sentence) (A : Str) : Expr :=
  .omegaMsol (membersP (univLit A) ψ.ar)
    (some (nonEmpty (compileP (univLit A) (relLit A) ψ.ar ψ.φ)))

end Rasso.ESO
