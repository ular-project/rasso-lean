import Rasso.NormalForm

/-!
# Rasso: removing an attribute by equality (the executable part)

The proofs are in `Rasso.Equality`.

The equality class removes an attribute `x` whose domain is infinite (the whole symbol,
string or int kind), when every leaf that mentions `x` is `=` between `x`
and an operand whose values lie in `x`'s domain. The two cases of step 2 are those of
Kanellakis, Kuper and Revesz's Lemma 4.6 (JCSS 51(1), 1995, §4), which organises the
elimination by e-configurations.

1. Write the term as an `or` of `and`s, by the shared normal form (`Rasso.NormalForm`). A
   literal on `x` is `x = τ` or `not (x = τ)`; `not` is not split, unlike dense order.
2. In each `and`: if it has `x = τ₀`, put `τ₀` for `x` in its other literals on `x`.
   Otherwise its literals on `x` are all `not (x = τ)`. They exclude finitely many values,
   and the domain is infinite, so some value of `x` meets them all: they are dropped.

The result is not simplified.
-/

namespace Rasso

/-- Is every value of `d` a value of `e`? A syntactic test: sound, not complete. -/
def Domain.subset? : Domain → Domain → Bool
  | .kind k', .kind k => k' == k || (k' == .int && k == .rat)
  | .range _ _, .kind k => k == .int || k == .rat
  | .set vs, .kind k => vs.all k.has
  | _, _ => false

namespace Equality

/-- The domains the class removes: infinite, with `=` as equality of values. -/
def infinite? : Domain → Bool
  | .kind .symbol | .kind .string | .kind .int => true
  | _ => false

/-- A literal of the normal form: a part that does not mention `x`, with its sign; `x = τ`
(`(true, τ)`) or `not (x = τ)` (`(false, τ)`); or a constant. -/
abbrev Lit := NF.Lit (Bool × Term)

export NF (isAttr)

/-- A leaf of the normal form that mentions `x`: `l = r`, under the sign `p`. -/
def leaf (a : String) (p : Bool) (op : String) (es : List Term) : List (List Lit) :=
  if op = "=" then
    match es with
    | [l, r] =>
      if isAttr a l then
        if isAttr a r then [[.const p]] else [[.atom (p, r)]]
      else [[.atom (p, l)]]
    | _ => []
  else []

/-- The literals on `x` of one `and`, with `x` removed: with `x = τ₀`, put `τ₀` for `x`;
otherwise there is nothing left to say. -/
def xpart (xs : List (Bool × Term)) : List Term :=
  match xs.find? (·.1) with
  | some (_, τ₀) => xs.map fun q =>
      if q.1 then .call "=" [τ₀, q.2] else .call "not" [.call "=" [τ₀, q.2]]
  | none => []

/-- The term `e` with the attribute `a` removed by equality. -/
def elim (a : String) (e : Term) : Term := NF.elim (leaf a) xpart a e

/-- An operand whose values lie in `d`, the domain of `x`: an attribute other than `a` whose
domain is included in `d`, or a value of `d`. -/
def inDom (h : Heading) (a : String) (d : Domain) : Term → Bool
  | .attr b =>
    b != a && match h.lookup b with
      | some db => db.subset? d
      | none => false
  | .val v => d.mem v
  | _ => false

def operand? (h : Heading) (a : String) (d : Domain) (e : Term) : Bool :=
  isAttr a e || inDom h a d e

/-- A leaf the class accepts: `=` whose operands are each `x` or in `x`'s domain. -/
def leafOk (h : Heading) (a : String) (d : Domain) (op : String) (es : List Term) : Bool :=
  if op = "=" then
    match es with
    | [l, r] => operand? h a d l && operand? h a d r
    | _ => false
  else false

/-- Does every leaf that mentions `a` in `e` compare it by `=` with a value of its domain `d`,
in a Boolean skeleton of `and`, `or` and `not`? -/
def accepts? (h : Heading) (a : String) (d : Domain) (e : Term) : Bool :=
  NF.accepts? (leafOk h a d) a e

end Equality

end Rasso
