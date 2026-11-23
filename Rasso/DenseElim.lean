import Rasso.NormalForm

/-!
# Rasso: removing an attribute by dense order (the executable part)

The proofs are in `Rasso.Dense`.

The dense-order class removes an attribute `x` whose domain is the whole rat kind, when
every comparison that mentions `x` compares it with a number: a number constant, or an
attribute whose domain holds numbers only. The method is Fourier's for order, as in the
constraint query languages of Kanellakis, Kuper and Revesz and the algebra of Goldin and
Kanellakis:

1. Read the term as a Boolean formula (the shared normal form, `Rasso.NormalForm`). Push `not`
   down to the comparisons, and write the formula as an `or` of `and`s (DNF). A part that does not mention `x` is kept whole. `not (x = τ)` becomes `x < τ or x > τ`.
2. In each `and`: if it has `x = τ`, put `τ` for `x` in its other comparisons. Otherwise
   pair every lower bound of `x` with every upper bound. The rat kind has no ends and no
   gaps, so this is exact.

The user writes any Boolean term; the normal form is internal. The
result is not simplified.
-/

namespace Rasso.Dense

/-- How `x` compares with the other operand: `x < τ`, `x ≤ τ`, `x = τ`, `x ≥ τ`, `x > τ`. -/
inductive XRel where
  | lt | le | eq | ge | gt
  deriving DecidableEq, Repr

/-- The operator that tests it. -/
def XRel.op : XRel → String
  | .lt => "<" | .le => "<=" | .eq => "=" | .ge => ">=" | .gt => ">"

def XRel.ofOp (op : String) : Option XRel :=
  if op = "<" then some .lt else if op = "<=" then some .le else if op = "=" then some .eq
  else if op = ">=" then some .ge else if op = ">" then some .gt else none

/-- The relation with the operands swapped: `τ < x` is `x > τ`. -/
def XRel.flip : XRel → XRel
  | .lt => .gt | .le => .ge | .eq => .eq | .ge => .le | .gt => .lt

/-- The negation, as a disjunction: not `x = τ` is `x < τ` or `x > τ`. -/
def XRel.neg : XRel → List XRel
  | .lt => [.ge] | .le => [.gt] | .eq => [.lt, .gt] | .ge => [.lt] | .gt => [.le]

/-- Whether `x ⋈ x` is true. -/
def XRel.refl : XRel → Bool
  | .le | .eq | .ge => true
  | .lt | .gt => false

/-- A literal of the normal form (`Rasso.NormalForm`): a part that does not mention `x`, with
its sign; a comparison `x ⋈ τ`; or a constant. -/
abbrev Lit := NF.Lit (XRel × Term)

export NF (isAttr)

/-- One comparison `l ⋈ r` that mentions `x`, under the sign `p`. -/
def atom (a : String) (p : Bool) (r : XRel) (l r' : Term) : List (List Lit) :=
  let rs := if p then [r] else r.neg
  if isAttr a l then
    if isAttr a r' then [[.const (r.refl == p)]] else rs.map fun s => [.atom (s, r')]
  else rs.map fun s => [.atom (s.flip, l)]

/-- A leaf of the normal form that mentions `x`: a comparison with two operands. -/
def leaf (a : String) (p : Bool) (op : String) (es : List Term) : List (List Lit) :=
  match XRel.ofOp op, es with
  | some r, [l, r'] => atom a p r l r'
  | _, _ => []

/-- The normal form of `e` under the sign `p` (`true`: `e`; `false`: not `e`). -/
def dnf (a : String) (p : Bool) (e : Term) : List (List Lit) := NF.dnf (leaf a) a p e

/-- The lower bounds of `x` in a list of comparisons: `τ < x` (strict) and `τ ≤ x`. -/
def lows (xs : List (XRel × Term)) : List (Term × Bool) :=
  xs.filterMap fun | (.gt, τ) => some (τ, true) | (.ge, τ) => some (τ, false) | _ => none

/-- The upper bounds of `x`: `x < τ` (strict) and `x ≤ τ`. -/
def ups (xs : List (XRel × Term)) : List (Term × Bool) :=
  xs.filterMap fun | (.lt, τ) => some (τ, true) | (.le, τ) => some (τ, false) | _ => none

/-- The comparisons of `x` in one `and`, with `x` removed: with `x = τ₀`, put `τ₀` for `x`;
otherwise pair each lower bound with each upper bound. -/
def xpart (xs : List (XRel × Term)) : List Term :=
  match xs.find? (·.1 == .eq) with
  | some (_, τ₀) => xs.map fun p => .call p.1.op [τ₀, p.2]
  | none => (lows xs).flatMap fun l =>
      (ups xs).map fun u => .call (if l.2 || u.2 then "<" else "<=") [l.1, u.1]

/-- One `and` of the normal form, with `x` removed. -/
def elimConj (c : List Lit) : List Term := NF.elimConj xpart c

/-- The term `e` with the attribute `a` removed by dense order. -/
def elim (a : String) (e : Term) : Term := NF.elim (leaf a) xpart a e

/-- An operand that compares with `x` as a number: a number constant, or an attribute other
than `a` whose domain holds numbers only. -/
def numOperand? (h : Heading) (a : String) : Term → Bool
  | .attr b => b != a && ((h.lookup b).bind Domain.numeric).isSome
  | .val v => v.exact?.isSome
  | _ => false

def operand? (h : Heading) (a : String) (e : Term) : Bool := isAttr a e || numOperand? h a e

/-- A leaf the class accepts: a comparison whose operands are each `x` or a number. -/
def leafOk (h : Heading) (a : String) (op : String) (es : List Term) : Bool :=
  match XRel.ofOp op, es with
  | some _, [l, r] => operand? h a l && operand? h a r
  | _, _ => false

/-- Does every comparison that mentions `a` in `e` compare it with a number, in a Boolean
skeleton of `and`, `or` and `not`? -/
def accepts? (h : Heading) (a : String) (e : Term) : Bool := NF.accepts? (leafOk h a) a e

end Rasso.Dense
