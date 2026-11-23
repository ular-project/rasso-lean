import Rasso.Term
import Rasso.DenseElim
import Rasso.EqElim
import Rasso.LinElim

/-!
# Rasso: π on unrestricted relations (the executable part)

The specifications and proofs are in `Rasso.Classes`; this module holds only what the
evaluator runs, because `Rasso.Eval` imports it.

π is an operator of the algebra. On an unrestricted relation it is computed by removing
the dropped attributes from the representing term one at a time. Each removal is done by
a **class**: a kind of term for which a removal is known. The **recogniser** finds the
class for a relation and an attribute, or says why there is none. π succeeds exactly when
every removal finds a class. Terms
never get a quantifier: the removal is how π is computed, not a
construct of the language.

Classes so far:

* `finite`: the dropped attribute's domain is finite. The term becomes the `or` of copies
  of it, one for each value of the domain, with the value in place of the attribute.
* `dense`: the dropped attribute's domain is the whole rat kind, and every comparison that
  mentions it compares it with a number (`Rasso.DenseElim`).
* `equality`: the dropped attribute's domain is the whole symbol, string or int kind, and
  every leaf that mentions it is `=` with a value of its domain (`Rasso.EqElim`).
* `linear`: the dropped attribute's domain is the whole rat kind, and every comparison that
  mentions it compares two linear terms (`Rasso.LinElim`). Fourier–Motzkin.

Conventions:

* The dropped attributes are removed in this order: those with an infinite domain first,
  then the finite ones, each in heading order.
* The result's heading lists the attributes in the order π names them, as on a finite
  relation.
* The eliminated term is not simplified.
-/

namespace Rasso

/-- `t` with the attribute `a` given the value `v`. -/
def Tuple.set (t : Tuple) (a : String) (v : Value) : Tuple :=
  Tuple.ofPairs ((a, v) :: t.filter (·.1 ≠ a))

/-- `e` with each read of `a` replaced by `τ`. -/
def Term.subst : Term → String → Term → Term
  | .attr b, a, τ => if b = a then τ else .attr b
  | .val v, _, _ => .val v
  | .call op args, a, τ => .call op (args.attach.map fun ⟨x, _⟩ => Term.subst x a τ)

/-- A domain as a program writes it. -/
def Domain.text : Domain → String
  | .kind k => k.name
  | .range lo hi => s!"(range {lo} {hi})"
  | .set vs => s!"(set {" ".intercalate (vs.map racketText)})"

/-! ## Classes -/

/-- The kinds of term for which π knows how to remove an attribute. -/
inductive Class where
  | finite
  | dense
  | equality
  | linear
  deriving DecidableEq, Repr

/-- The classes, in the order the recogniser tries them. -/
def Class.all : List Class := [.finite, .dense, .equality, .linear]

def Class.name : Class → String
  | .finite => "finite"
  | .dense => "dense order"
  | .equality => "equality"
  | .linear => "linear"

/-- The domain of a finite attribute, listed. -/
def Unrel.values? (u : Unrel) (a : String) : Option (List Value) :=
  (u.heading.lookup a).bind Domain.values?

/-- Does the class know how to remove `a` from `u`? -/
def Class.accepts? : Class → Unrel → String → Bool
  | .finite, u, a => (u.values? a).isSome
  | .dense, u, a => u.heading.lookup a == some (.kind .rat) && Dense.accepts? u.heading a u.term
  | .equality, u, a =>
    match u.heading.lookup a with
    | some d => Equality.infinite? d && Equality.accepts? u.heading a d u.term
    | none => false
  | .linear, u, a => u.heading.lookup a == some (.kind .rat) && Linear.accepts? u.heading a u.term

/-- Why the class does not accept. -/
def Class.why : Class → Unrel → String → String
  | .finite, _, _ => "the domain has no end"
  | .dense, u, a =>
    if u.heading.lookup a != some (.kind .rat) then "the domain is not rat"
    else s!"{a} is used other than in a comparison with a number"
  | .equality, u, a =>
    match u.heading.lookup a with
    | some d =>
      if !Equality.infinite? d then "the domain is not symbol, string or int"
      else s!"{a} is used other than in = with a value of its domain"
    | none => "the attribute is not in the heading"
  | .linear, u, a =>
    if u.heading.lookup a != some (.kind .rat) then "the domain is not rat"
    else s!"{a} is used other than in a comparison of linear terms"

/-- The term with `a` removed, when the class accepts. -/
def Class.elimTerm : Class → Unrel → String → Term
  | .finite, u, a => .call "or" (((u.values? a).getD []).map fun v => u.term.subst a (.val v))
  | .dense, u, a => Dense.elim a u.term
  | .equality, u, a => Equality.elim a u.term
  | .linear, u, a => Linear.elim u.heading a u.term

/-- The first class that accepts, or why none does. -/
def recognise (u : Unrel) (a : String) : Except String Class :=
  match Class.all.find? (·.accepts? u a) with
  | some c => .ok c
  | none =>
    let d := match u.heading.lookup a with | some d => d.text | none => "none"
    let why := "; ".intercalate (Class.all.map fun c => s!"{c.name}: {c.why u a}")
    .error s!"π: no class can remove attribute {a}, of domain {d} ({why})"

/-- `u` with `a` removed by the class `c`. -/
def Unrel.dropOne (u : Unrel) (a : String) (c : Class) : Unrel :=
  ⟨u.heading.filter (·.1 ≠ a), c.elimTerm u a⟩

/-- Remove the attributes one at a time, recognising each. -/
def Unrel.eliminate : Unrel → List String → Except String Unrel
  | u, [] => .ok u
  | u, a :: rest => do Unrel.eliminate (u.dropOne a (← recognise u a)) rest

/-- The attributes π drops, in the order they are removed. -/
def dropOrder (h : Heading) (as : List String) : List String :=
  let dropped := h.attrs.filter fun a => !as.contains a
  dropped.filter (fun a => ((h.lookup a).bind Domain.values?).isNone) ++
    dropped.filter (fun a => ((h.lookup a).bind Domain.values?).isSome)

/-- The attributes `as` of a heading, in the order of `as`, with their domains. -/
def Heading.pick (h : Heading) : List String → Except String Heading
  | [] => .ok []
  | a :: as => match h.lookup a with
    | some d => do return (a, d) :: (← h.pick as)
    | none => .error s!"π: no attribute {a} in {h.attrs}"

/-- π on an unrestricted relation. It refuses as on a finite relation, and when an
attribute it drops is in no class. -/
def Unrel.project (as : List String) (u : Unrel) : Except String Unrel := do
  if as.eraseDups.length != as.length then throw s!"π: {as} names an attribute twice"
  let h ← u.heading.pick as
  let w ← u.eliminate (dropOrder u.heading as)
  return ⟨h, w.term⟩

end Rasso
