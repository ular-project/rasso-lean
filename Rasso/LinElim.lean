import Rasso.LinForm
import Rasso.DenseElim

/-!
# Rasso: removing an attribute by linear arithmetic (the executable part)

The proofs are in `Rasso.LinRead` (reading terms as forms) and `Rasso.Linear` (the class).

The linear class removes an attribute `x` whose domain is the whole rat kind, when every
comparison that mentions `x` compares two linear terms: sums of number constants times
attributes, plus a constant. The method is Fourier–Motzkin
elimination (Fourier 1826, Motzkin 1936), as in the linear constraint databases of
Kanellakis, Kuper and Revesz:

1. Write the term as an `or` of `and`s, by the shared normal form (`Rasso.NormalForm`).
   A comparison `l ⋈ r` is read as the row `c·x + L ⋈ 0`, with `c` the coefficient of `x` in
   `l − r`. When `c ≠ 0` the row is a bound `x ⋈ −L/c`, with `⋈` flipped when `c < 0`. When
   `c = 0` it does not mention `x`, and is kept as the comparison `L ⋈ 0`.
2. In each `and`, the bounds are removed as in dense order (`Dense.xpart`): with `x = B₀`,
   put `B₀` for `x`; otherwise pair each lower bound with each upper bound.

The bounds are linear forms; the new comparisons are written from them (`Lin.render`),
since Fourier–Motzkin adds scaled rows and its comparisons are not parts of the old term.
The result is not simplified.
-/

namespace Rasso

/-! ## Reading a term as a linear form -/

namespace Lin

/-- A product of two forms when one of them is a constant. -/
def mul? (L M : Lin) : Option Lin :=
  if L.isConst then some (M.scale L.const)
  else if M.isConst then some (L.scale M.const) else none

/-- The form of an operator applied to forms, when it is linear. -/
def combine (op : String) (Ls : List Lin) : Option Lin :=
  match op, Ls with
  | "+", _ => some (Ls.foldl add (ofConst 0))
  | "-", [L] => some L.neg
  | "-", L :: Ms => some (Ms.foldl sub L)
  | "*", _ => Ls.foldlM mul? (ofConst 1)
  | _, _ => none

mutual
/-- The reading of a term as a linear form; `ok b` says the attribute `b` may be read. -/
def ofTerm? (ok : String → Bool) : Term → Option Lin
  | .attr b => if ok b then some (ofAttr b) else none
  | .val v => v.exact?.map ofConst
  | .call op es => (ofTerms? ok es).bind (combine op)

def ofTerms? (ok : String → Bool) : List Term → Option (List Lin)
  | [] => some []
  | e :: es => (ofTerm? ok e).bind fun L => (ofTerms? ok es).map (L :: ·)
end

/-- `c * b` as a term. -/
def pairTerm (p : String × Rat) : Term := .call "*" [.val (Value.ofRat p.2), .attr p.1]

/-- The form as a Rasso term: `k + c₁ * b₁ + …`. -/
def render (L : Lin) : Term := .call "+" (.val (Value.ofRat L.const) :: L.terms.map pairTerm)

end Lin

namespace Linear

open Dense (XRel)

/-- A literal of the normal form: a part without `x`, with its sign; a bound `x ⋈ B`, where
the form `B` does not read `x`; or a constant. -/
abbrev Lit := NF.Lit (XRel × Lin)

/-- The attributes a linear term may read: `x` itself, and attributes whose domain holds
numbers only. -/
def okAttr (h : Heading) (a : String) (b : String) : Bool :=
  b == a || ((h.lookup b).bind Domain.numeric).isSome

/-- The row `c·x + L ⋈ 0`, under the sign `p`. -/
def row (p : Bool) (r : XRel) (c : Rat) (L : Lin) : List (List Lit) :=
  if c = 0 then [[.opq p (.call r.op [L.render, .val (.int 0)])]]
  else (if p then [r] else r.neg).map fun s =>
    [.atom (if 0 < c then s else s.flip, L.scale (-1 / c))]

/-- A leaf of the normal form that mentions `x`: a comparison of two linear terms. -/
def leaf (h : Heading) (a : String) (p : Bool) (op : String) (es : List Term) : List (List Lit) :=
  match XRel.ofOp op, es with
  | some r, [l, r'] =>
    match Lin.ofTerm? (okAttr h a) l, Lin.ofTerm? (okAttr h a) r' with
    | some Ll, some Lr => row p r ((Ll.sub Lr).coeff a) ((Ll.sub Lr).drop a)
    | _, _ => []
  | _, _ => []

/-- The bounds of `x` in one `and`, with `x` removed: Fourier's step of dense order, on the
rendered bounds. -/
def xpart (xs : List (XRel × Lin)) : List Term :=
  Dense.xpart (xs.map fun x => (x.1, x.2.render))

/-- The term `e` with the attribute `a` removed by linear arithmetic. -/
def elim (h : Heading) (a : String) (e : Term) : Term := NF.elim (leaf h a) xpart a e

/-- A leaf the class accepts: a comparison of two linear terms. -/
def leafOk (h : Heading) (a : String) (op : String) (es : List Term) : Bool :=
  match XRel.ofOp op, es with
  | some _, [l, r] => (Lin.ofTerm? (okAttr h a) l).isSome && (Lin.ofTerm? (okAttr h a) r).isSome
  | _, _ => false

/-- Does every comparison that mentions `a` in `e` compare two linear terms, in a Boolean
skeleton of `and`, `or` and `not`? -/
def accepts? (h : Heading) (a : String) (e : Term) : Bool := NF.accepts? (leafOk h a) a e

end Linear

end Rasso
