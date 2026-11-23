import Rasso.Mem
import Rasso.WF

/-!
# Codd's theorem for Rasso: schemas, databases, the active domain

In plain words:

* A **schema** names the stored relations and, for each, its attributes in order. The
  order matters only to the calculus, whose atoms `R(x₁, …, xₙ)` are positional.
* Every attribute of every stored relation, and every heading a query builds, has **one
  domain** `D`, a Rasso `Domain` such as `int`.
* A **database** for a schema is a Rasso environment (`Rasso.Env`) that binds each
  relation name to a finite relation (`.finrel r`) whose heading is the schema's, every
  attribute with domain `D`, and which is well formed (`Rasso.Finrel.WF`: each tuple has
  exactly the heading's attributes, with values in `D`). That is `Conforms`.
* The **active domain** of a database is the list of the values its stored relations
  hold.

Conventions:

* One domain for the whole schema.
* `DomOK D`: `D` does not hold both an exact number (int or rat) and a float, nor both a
  symbol and a string, so Rasso's `=` never refuses to compare two of its values.
* Relation and attribute names satisfy `Rasso.isAttribute`, so they contain no `%`;
  the translations use `%` for names of their own. Rasso's evaluator does
  not check names itself, so this is an assumption of the theorems, in `Schema.WF`.
-/

namespace Coddstheorem

open Rasso

/-- A schema: each stored relation's name with its attributes, in order. -/
abbrev Schema := List (String × List String)

/-- The attributes of a stored relation (`[]` if the schema doesn't have it). -/
def Schema.attrsOf (S : Schema) (n : String) : List String := (S.lookup n).getD []

/-- A schema is well formed: no relation twice, no attribute twice in a relation, and
every name a Rasso name. -/
def Schema.WF (S : Schema) : Prop :=
  (S.map (·.1)).Nodup ∧ ∀ p ∈ S, p.2.Nodup ∧ isAttribute p.1 = true ∧ ∀ a ∈ p.2, isAttribute a = true

instance (S : Schema) : Decidable S.WF := inferInstanceAs (Decidable (_ ∧ _))

/-- The heading of a list of attributes, each with domain `D`. -/
def headerOf (D : Domain) (as : List String) : Heading := as.map (·, D)

/-- An exact number: an int or a (non-whole) rat. Rasso's `=` refuses one beside a float. -/
def isExact : Value → Bool
  | .int _ | .rat _ _ => true
  | _ => false

/-- A float. -/
def isFloat : Value → Bool
  | .float _ => true
  | _ => false

/-- `D` holds no int or rat beside a float, so `=` compares any two of its values. -/
def DomOK : Domain → Bool
  | .kind _ => true
  | .range _ _ => true
  | .set vs => !(vs.any isExact && vs.any isFloat) && !(vs.any Value.isSymbol && vs.any Value.isString)

/-- The form-level domain that evaluates to `D`, so a query can write `D` into a heading.
(Named in Coddstheorem's namespace, not as `Rasso.Domain.toDomExpr`: Coddstheorem declares
nothing in Rasso's.) -/
def toDomExpr : Domain → DomExpr
  | .kind k => .kind k
  | .range lo hi => .range lo hi
  | .set vs => .set vs

theorem dom_eval_toDomExpr (env : Env) (tg : List Expr) (D : Domain) :
    DomExpr.eval env tg (toDomExpr D) = .ok D := by
  cases D <;> simp [toDomExpr, DomExpr.eval]

/-- The form-level domain read back, when it names a domain directly (not `in R`). -/
def ofDomExpr? : DomExpr → Option Domain
  | .kind k => some (.kind k)
  | .range lo hi => some (.range lo hi)
  | .set vs => some (.set vs)
  | .in_ _ => none

theorem ofDomExpr?_toDomExpr (D : Domain) : ofDomExpr? (toDomExpr D) = some D := by
  cases D <;> rfl

theorem toDomExpr_of_ofDomExpr? {d : DomExpr} {D : Domain} (h : ofDomExpr? d = some D) : toDomExpr D = d := by
  cases d <;> simp [ofDomExpr?] at h <;> subst h <;> rfl

/-- The tuples of the stored relation `n` in `env` (none if it isn't a finite relation). -/
def tuplesOf (env : Env) (n : String) : List Tuple :=
  match env.lookup n with
  | some (.finrel r) => r.tuples
  | _ => []

/-- `env` is a database for schema `S` over domain `D`. -/
def Conforms (S : Schema) (D : Domain) (env : Env) : Prop :=
  ∀ p ∈ S, ∃ r, env.lookup p.1 = some (.finrel r) ∧ r.WF ∧
    ∀ a, r.heading.lookup a = (headerOf D p.2).lookup a

/-- The active domain: the values the schema's stored relations hold. -/
def adom (S : Schema) (env : Env) : List Value :=
  S.flatMap fun p => (tuplesOf env p.1).flatMap fun t => t.map (·.2)

/-! ## Order comparisons, shared by the algebra and the calculus -/

/-- An order comparison: `<`, `<=`, `>`, `>=`. -/
inductive Cmp where
  | lt | le | gt | ge
  deriving Repr, Inhabited, DecidableEq

/-- Rasso's name for the comparison. -/
def Cmp.op : Cmp → String
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

/-- The comparison as Rasso's evaluator computes it (`Rasso.applyOp`, `Rasso/Term.lean`):
by `Value.cmp`, which orders by kind first, ints and floats together as numbers. It never
refuses. -/
def Cmp.holds : Cmp → Value → Value → Bool
  | .lt, v, w => Value.cmp v w == .lt
  | .le, v, w => Value.cmp v w != .gt
  | .gt, v, w => Value.cmp v w == .gt
  | .ge, v, w => Value.cmp v w != .lt

end Coddstheorem
