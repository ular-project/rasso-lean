import Rasso.Term

/-!
# Rasso: the normal form π's classes share (the executable part)

The dense-order class, the equality class and the linear class all remove an attribute `x`
the same way at the top:

1. Read the term as a Boolean formula. Push `not` down to the leaves, and write the formula as
   an `or` of `and`s (DNF). A part that does not mention `x` is kept whole.
2. In each `and`, remove `x` from the leaves that mention it, by the class's own method.

This file holds step 1 and the frame of step 2, generic in the type of the leaves that mention
`x`. Each class gives:

* `leaf`: a leaf `op es` that mentions `x`, under a sign, as a normal form of its own literals;
* `leafOk`: the test that a class accepts such a leaf;
* `part`: how one `and`'s literals on `x` become terms without `x`.

The proofs are in `Rasso.NormalFormProof`.
-/

namespace Rasso.NF

/-- A literal of the normal form: a part that does not mention `x`, with its sign; a literal of
the class, on `x`; or a constant. -/
inductive Lit (α : Type) where
  | opq (pos : Bool) (e : Term)
  | atom (l : α)
  | const (b : Bool)

variable {α : Type}

/-- The `and` of two normal forms. -/
def conj (d₁ d₂ : List (List (Lit α))) : List (List (Lit α)) :=
  d₁.flatMap fun c => d₂.map (c ++ ·)

/-- The normal form of `e` under the sign `p` (`true`: `e`; `false`: not `e`). A leaf that
mentions `a` is handed to `leaf`, with its sign, operator and operands. -/
def dnf (leaf : Bool → String → List Term → List (List (Lit α))) (a : String) (p : Bool) :
    Term → List (List (Lit α))
  | .call op es =>
    if !(Term.call op es).attrs.contains a then [[.opq p (.call op es)]]
    else if op = "and" then
      if p then es.attach.foldr (fun ⟨x, _⟩ acc => conj (dnf leaf a p x) acc) [[]]
      else es.attach.flatMap fun ⟨x, _⟩ => dnf leaf a p x
    else if op = "or" then
      if p then es.attach.flatMap fun ⟨x, _⟩ => dnf leaf a p x
      else es.attach.foldr (fun ⟨x, _⟩ acc => conj (dnf leaf a p x) acc) [[]]
    else if op = "not" then
      match es with
      | [x] => dnf leaf a (!p) x
      | _ => []
    else leaf p op es
  | e => if !e.attrs.contains a then [[.opq p e]] else []

/-- A literal that does not mention `x`, as a term. -/
def Lit.rest : Lit α → Option Term
  | .opq p e => some (if p then e else .call "not" [e])
  | .const b => some (.val (.bool b))
  | .atom _ => none

/-- A literal of the class. -/
def Lit.atom? : Lit α → Option α
  | .atom l => some l
  | _ => none

/-- One `and` of the normal form, with `x` removed by `part`. -/
def elimConj (part : List α → List Term) (c : List (Lit α)) : List Term :=
  c.filterMap Lit.rest ++ part (c.filterMap Lit.atom?)

/-- The term `e` with the attribute `a` removed: the `or` of the `and`s, each with `x` removed. -/
def elim (leaf : Bool → String → List Term → List (List (Lit α)))
    (part : List α → List Term) (a : String) (e : Term) : Term :=
  .call "or" ((dnf leaf a true e).map fun c => .call "and" (elimConj part c))

/-- Is every leaf that mentions `a` one the class accepts, in a Boolean skeleton of `and`, `or`
and `not`? A part that does not mention `a` is accepted first, whatever it is. -/
def accepts? (leafOk : String → List Term → Bool) (a : String) : Term → Bool
  | .call op es =>
    !(Term.call op es).attrs.contains a ||
      if op = "and" ∨ op = "or" then es.attach.all fun ⟨x, _⟩ => accepts? leafOk a x
      else if op = "not" then
        match es with
        | [x] => accepts? leafOk a x
        | _ => false
      else leafOk op es
  | e => !e.attrs.contains a

/-- Is the term the attribute `a` itself? -/
def isAttr (a : String) : Term → Bool
  | .attr b => b == a
  | _ => false

end Rasso.NF
