import Coddstheorem.Schema

/-!
# Codd's theorem for Rasso: the algebra (Rasso's own)

The algebra side of Codd's theorem is Rasso's algebra as Rasso's evaluator runs it:
a query is a `Rasso.Expr` form, and its meaning is
`Rasso.Expr.eval`. To prove things by induction, the part of the forms that is Codd's
algebra is written here as a small inductive type, `CRA`, with a compiler `CRA.toExpr`
into forms and a recogniser `CRA.ofExpr?` back, proved to be inverse to each other.

In plain words, a `CRA` expression is one of:

* `rel n`: the stored relation `n` (the form `n`);
* `lit as rows`: a constant relation with attributes `as`, every attribute with domain `D`
  (the form `omega[a: D, …](rows)`);
* `sel t e`: σ, keeping the tuples that pass the test `t` (`=` between attributes or
  with a constant, the order comparisons `<`, `<=`, `>`, `>=` likewise,
  combined with `and`, `or`, `not`);
* `proj as e`: π onto the attributes `as`;
* `ren r e`: ρ, renaming attributes (all at once, so a swap is allowed);
* `join e f`, `prod e f`, `union e f`, `diff e f`, `inter e f`: ⋈, ×, ∪, −, ∩, each with
  two operands (the forms' `nary`).

`CRA.check S D e` gives the attributes `e` has, when `e` is well typed for the schema:
the conditions under which Rasso's evaluator will not refuse it (proved in `Coddstheorem.AlgebraToCalculus`).

Conventions:

* σ tests `=` and the order comparisons; `and` and `or` take exactly two
  operands.
* × is checked to have operands with no attribute in common, as in Codd's algebra
  (Rasso's evaluator runs × as ⋈, so without the check it would be a join).
* Every name is a Rasso name (`isAttribute`), so none contains `%`.
* A ρ that renames one attribute twice is refused by `check` (Rasso's evaluator would
  take the first).
* `toExpr` gives forms Rasso's evaluator runs; whether `Expr.problem` also accepts them is
  not claimed (`Expr.problem` is `partial`).
-/

namespace Coddstheorem

open Rasso

/-- σ's tests. -/
inductive Test where
  | eqA (a b : String)
  | eqC (a : String) (c : Value)
  | cmpA (o : Cmp) (a b : String)
  | cmpC (o : Cmp) (a : String) (c : Value)
  | and (s t : Test)
  | or (s t : Test)
  | not (t : Test)
  deriving Repr, Inhabited, DecidableEq

/-- Codd's algebra, as a fragment of Rasso's forms. -/
inductive CRA where
  | rel (n : String)
  | lit (as : List String) (rows : List (List Value))
  | sel (t : Test) (e : CRA)
  | proj (as : List String) (e : CRA)
  | ren (r : List (String × String)) (e : CRA)
  | join (e f : CRA)
  | prod (e f : CRA)
  | union (e f : CRA)
  | diff (e f : CRA)
  | inter (e f : CRA)
  deriving Repr, Inhabited, DecidableEq

namespace Test

/-- The Rasso term a test is. -/
def toTerm : Test → Rasso.Term
  | eqA a b => .call "=" [.attr a, .attr b]
  | eqC a c => .call "=" [.attr a, .val c]
  | cmpA o a b => .call o.op [.attr a, .attr b]
  | cmpC o a c => .call o.op [.attr a, .val c]
  | and s t => .call "and" [s.toTerm, t.toTerm]
  | or s t => .call "or" [s.toTerm, t.toTerm]
  | not t => .call "not" [t.toTerm]

/-- A Rasso term read back as a test, when it is one. -/
def ofTerm? : Rasso.Term → Option Test
  | .call "=" [.attr a, .attr b] => some (eqA a b)
  | .call "=" [.attr a, .val c] => some (eqC a c)
  | .call "<" [.attr a, .attr b] => some (cmpA .lt a b)
  | .call "<" [.attr a, .val c] => some (cmpC .lt a c)
  | .call "<=" [.attr a, .attr b] => some (cmpA .le a b)
  | .call "<=" [.attr a, .val c] => some (cmpC .le a c)
  | .call ">" [.attr a, .attr b] => some (cmpA .gt a b)
  | .call ">" [.attr a, .val c] => some (cmpC .gt a c)
  | .call ">=" [.attr a, .attr b] => some (cmpA .ge a b)
  | .call ">=" [.attr a, .val c] => some (cmpC .ge a c)
  | .call "and" [s, t] => do return and (← ofTerm? s) (← ofTerm? t)
  | .call "or" [s, t] => do return or (← ofTerm? s) (← ofTerm? t)
  | .call "not" [t] => do return not (← ofTerm? t)
  | _ => none

theorem ofTerm?_toTerm : (t : Test) → ofTerm? t.toTerm = some t
  | eqA _ _ | eqC _ _ => rfl
  | cmpA o _ _ | cmpC o _ _ => by cases o <;> rfl
  | and s t => by simp [toTerm, ofTerm?, ofTerm?_toTerm s, ofTerm?_toTerm t]
  | or s t => by simp [toTerm, ofTerm?, ofTerm?_toTerm s, ofTerm?_toTerm t]
  | not t => by simp [toTerm, ofTerm?, ofTerm?_toTerm t]

theorem toTerm_of_ofTerm? {u : Rasso.Term} {t : Test} (h : ofTerm? u = some t) : t.toTerm = u := by
  induction u using ofTerm?.induct generalizing t with
  | case11 s t' ih1 ih2 =>
    cases hx : ofTerm? s <;> cases hy : ofTerm? t' <;> simp_all [ofTerm?] <;> (subst h; simp_all [toTerm])
  | case12 s t' ih1 ih2 =>
    cases hx : ofTerm? s <;> cases hy : ofTerm? t' <;> simp_all [ofTerm?] <;> (subst h; simp_all [toTerm])
  | case13 t' ih =>
    cases hx : ofTerm? t' <;> simp_all [ofTerm?] <;> (subst h; simp_all [toTerm])
  | case14 => simp_all [ofTerm?]
  | _ => simp [ofTerm?] at h; subst h; rfl

/-- The attributes a test reads. -/
def attrs : Test → List String
  | eqA a b | cmpA _ a b => [a, b]
  | eqC a _ | cmpC _ a _ => [a]
  | and s t | or s t => s.attrs ++ t.attrs
  | not t => t.attrs

/-- The constants a test compares with. -/
def consts : Test → List Value
  | eqA _ _ | cmpA _ _ _ => []
  | eqC _ c | cmpC _ _ c => [c]
  | and s t | or s t => s.consts ++ t.consts
  | not t => t.consts

/-- The term of a test reads only the test's attributes (σ refuses a term that reads an
attribute outside the heading). -/
theorem attrs_toTerm : ∀ (t : Test), ∀ a ∈ t.toTerm.attrs, a ∈ t.attrs
  | eqA _ _, a, h | eqC _ _, a, h | cmpA _ _ _, a, h | cmpC _ _ _, a, h => by
    simp_all [toTerm, attrs, Rasso.Term.attrs]
  | and s t, a, h | or s t, a, h => by
    simp only [toTerm, Rasso.Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append] at h
    rcases h with h | h
    · exact List.mem_append_left _ (attrs_toTerm s a h)
    · exact List.mem_append_right _ (attrs_toTerm t a h)
  | not t, a, h => by
    simp only [toTerm, Rasso.Term.attrs, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at h
    exact attrs_toTerm t a h

end Test

namespace CRA

/-- The Rasso form an expression is, with `D` for a constant relation's domains. -/
def toExpr (D : Domain) : CRA → Rasso.Expr
  | rel n => .name n
  | lit as rows => .omegaRows (as.map (·, toDomExpr D)) rows
  | sel t e => .select t.toTerm (e.toExpr D)
  | proj as e => .project as (e.toExpr D)
  | ren r e => .rename r (e.toExpr D)
  | join e f => .nary .join [e.toExpr D, f.toExpr D]
  | prod e f => .nary .product [e.toExpr D, f.toExpr D]
  | union e f => .nary .union [e.toExpr D, f.toExpr D]
  | diff e f => .nary .except [e.toExpr D, f.toExpr D]
  | inter e f => .nary .intersect [e.toExpr D, f.toExpr D]

/-- A heading in which every attribute's domain is `D`, read back as its attributes. -/
def litHead? (D : Domain) (h : List (String × DomExpr)) : Option (List String) :=
  if h.all (fun p => ofDomExpr? p.2 == some D) then some (h.map (·.1)) else none

/-- A Rasso form read back as an expression of the fragment, when it is one. -/
def ofExpr? (D : Domain) : Rasso.Expr → Option CRA
  | .name n => some (rel n)
  | .omegaRows h rows => do return lit (← litHead? D h) rows
  | .select t e => do return sel (← Test.ofTerm? t) (← ofExpr? D e)
  | .project as e => do return proj as (← ofExpr? D e)
  | .rename r e => do return ren r (← ofExpr? D e)
  | .nary .join [e, f] => do return join (← ofExpr? D e) (← ofExpr? D f)
  | .nary .product [e, f] => do return prod (← ofExpr? D e) (← ofExpr? D f)
  | .nary .union [e, f] => do return union (← ofExpr? D e) (← ofExpr? D f)
  | .nary .except [e, f] => do return diff (← ofExpr? D e) (← ofExpr? D f)
  | .nary .intersect [e, f] => do return inter (← ofExpr? D e) (← ofExpr? D f)
  | _ => none

theorem litHead?_map (D : Domain) (as : List String) :
    litHead? D (as.map (·, toDomExpr D)) = some as := by
  simp [litHead?, ofDomExpr?_toDomExpr, List.map_map, Function.comp_def]

theorem map_of_litHead? {D : Domain} {h : List (String × DomExpr)} {as : List String}
    (e : litHead? D h = some as) : as.map (·, toDomExpr D) = h := by
  unfold litHead? at e
  split at e
  · rename_i hall
    cases e
    rw [List.map_map]
    conv => rhs; rw [← List.map_id h]
    apply List.map_congr_left
    intro p hp
    have := List.all_eq_true.mp hall p hp
    simp only [beq_iff_eq] at this
    simp [toDomExpr_of_ofDomExpr? this]
  · cases e

/-- The recogniser reads back what the compiler writes. -/
theorem ofExpr?_toExpr (D : Domain) : (e : CRA) → ofExpr? D (e.toExpr D) = some e
  | rel _ => rfl
  | lit as rows => by simp [toExpr, ofExpr?, litHead?_map]
  | sel t e => by simp [toExpr, ofExpr?, Test.ofTerm?_toTerm, ofExpr?_toExpr D e]
  | proj _ e => by simp [toExpr, ofExpr?, ofExpr?_toExpr D e]
  | ren _ e => by simp [toExpr, ofExpr?, ofExpr?_toExpr D e]
  | join e f => by simp [toExpr, ofExpr?, ofExpr?_toExpr D e, ofExpr?_toExpr D f]
  | prod e f => by simp [toExpr, ofExpr?, ofExpr?_toExpr D e, ofExpr?_toExpr D f]
  | union e f => by simp [toExpr, ofExpr?, ofExpr?_toExpr D e, ofExpr?_toExpr D f]
  | diff e f => by simp [toExpr, ofExpr?, ofExpr?_toExpr D e, ofExpr?_toExpr D f]
  | inter e f => by simp [toExpr, ofExpr?, ofExpr?_toExpr D e, ofExpr?_toExpr D f]

/-- The recogniser accepts only forms of the fragment: what it reads back compiles to
the form it read. -/
theorem toExpr_of_ofRel? {D : Domain} {r : Rasso.Expr} {e : CRA} (h : ofExpr? D r = some e) :
    e.toExpr D = r := by
  induction r using ofExpr?.induct generalizing e with
  | case1 n => simp [ofExpr?] at h; subst h; rfl
  | case2 hd rows =>
    cases hx : litHead? D hd <;> simp_all [ofExpr?] <;> (subst h; simp [toExpr, map_of_litHead? hx])
  | case3 t e' ih =>
    cases hx : Test.ofTerm? t <;> cases hy : ofExpr? D e' <;> simp_all [ofExpr?] <;>
      (subst h; simp_all [toExpr, Test.toTerm_of_ofTerm? hx])
  | case4 _ e' ih | case5 _ e' ih =>
    cases hy : ofExpr? D e' <;> simp_all [ofExpr?] <;> (subst h; simp_all [toExpr])
  | case6 e' f ih1 ih2 | case7 e' f ih1 ih2 | case8 e' f ih1 ih2 | case9 e' f ih1 ih2
  | case10 e' f ih1 ih2 =>
    cases hx : ofExpr? D e' <;> cases hy : ofExpr? D f <;> simp_all [ofExpr?] <;>
      (subst h; simp_all [toExpr])
  | case11 => simp_all [ofExpr?]

/-! ## Typing against a schema -/

/-- The attributes after ρ renames them. -/
def renamed (r : List (String × String)) (as : List String) : List String :=
  as.map fun a => (r.lookup a).getD a

/-- The attributes `e` has, when it is well typed for schema `S` over domain `D` (none
otherwise): the conditions under which Rasso's evaluator does not refuse `e.toExpr D`. -/
def check (S : Schema) (D : Domain) : CRA → Option (List String)
  | rel n => S.lookup n
  | lit as rows =>
    if as.Nodup ∧ as.all isAttribute ∧ rows.all (·.length == as.length) ∧
        rows.all (·.all D.mem) then some as else none
  | sel t e => do
    let as ← check S D e
    if t.attrs.all as.contains ∧ t.consts.all D.mem then some as else none
  | proj bs e => do
    let as ← check S D e
    if bs.Nodup ∧ bs.all as.contains then some bs else none
  | ren r e => do
    let as ← check S D e
    let srcs := r.map (·.1)
    if srcs.Nodup ∧ srcs.all as.contains ∧ (r.map (·.2)).all isAttribute ∧
        (renamed r as).Nodup then some (renamed r as) else none
  | join e f => do
    let as ← check S D e
    let bs ← check S D f
    some (as ++ bs.filter fun b => !as.contains b)
  | prod e f => do
    let as ← check S D e
    let bs ← check S D f
    if bs.all fun b => !as.contains b then some (as ++ bs) else none
  | union e f | diff e f | inter e f => do
    let as ← check S D e
    let bs ← check S D f
    if as.all bs.contains ∧ bs.all as.contains then some as else none

/-- Well typed for schema `S` over domain `D`. -/
def WT (S : Schema) (D : Domain) (e : CRA) : Bool := (check S D e).isSome

/-- The constants an expression mentions. -/
def consts : CRA → List Value
  | rel _ => []
  | lit _ rows => rows.flatten
  | sel t e => t.consts ++ e.consts
  | proj _ e | ren _ e => e.consts
  | join e f | prod e f | union e f | diff e f | inter e f => e.consts ++ f.consts

end CRA
end Coddstheorem
