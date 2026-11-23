<a id="chap-r2-unrestricted"></a>
# 7 Unrestricted relations

This chapter gives the unrestricted relations: relations given by a test that their tuples pass, so that they can have infinitely many tuples. It gives their algebra; their projection, which removes attributes by quantifier elimination, one class of terms at a time; and their enumeration, the one way from an unrestricted relation to its tuples.

In databases, Kanellakis, Kuper and Revesz use the term unrestricted relation for a set of points, finite or infinite, given by a finite formula [[40](references.md#kanellakis_1995_constraint.query.languages), § 1.2]; Van den Bussche develops queries on such relations [[74](references.md#bussche_2000_constraint.databases.queries.query.languages), § § 2.3–2.4]. Rasso takes the name. A Rasso unrestricted relation is a heading and one Boolean term, with no normal form required, and the tuples it holds are an unrestricted relation in their sense. Goldin and Kanellakis gave an algebra on such relations [[31](references.md#goldin_1996_constraint.query.algebras)], and Chapter [8](cdb.md) places Rasso in their line of work. Earlier, Maier and Warren had brought computed relations, given by a procedure rather than stored, into relational databases [[50](references.md#maier_1981_incorporating.computed.relations.relational.databases)].

In optimisation, a problem has variables, each with a domain, and constraints, each satisfied or violated by an assignment of the variables; it asks for an assignment in the product of the domains that satisfies every constraint, and may ask for the one that minimises or maximises an objective [[36](references.md#hooker_2011_integrated.methods.for.optimization), p. 20]. Constraint programming, linear and mixed integer programming, SAT and SMT all take this form, and Hooker treats them as one field. The feasible assignments of such a problem form an unrestricted relation: its attributes are the problem’s variables, each with its domain, and its characteristic function is the conjunction of the constraints. MiniZinc, for example, has a construct which closely models an unrestricted relation: a `predicate` is a Boolean term over named variables, each with its domain [[55](references.md#nethercote_2007_minizinc.standard.cp.modelling.language)].

In rule-based languages, relations have long been stated, not stored, and searched. Constraint logic programming extends logic programming to reason over a domain of constraints [[39](references.md#jaffar_1987_constraint.logic.programming)]. In SWI-Prolog’s CLP(FD), a constraint such as `X #= Y + Z` is a relation over the integers, and the system searches for values that satisfy it [[71](references.md#triska_2012_finite.domain.constraint.solver.swi)]. LogicBlox’s LogiQL lets a program declare predicates as the variables of an optimisation problem, which a solver then decides [[6](references.md#aref_2015_design.implementation.the.logicblox.system)]. Rel has conceptually infinite relations, such as `add`, the triples $`\langle x, y, z\rangle`$ with $`x + y = z`$, and accepts an expression over them when its safety rules show the result finite [[5](references.md#aref_2025_rel.programming.language.relational.data), § 3]; the rules come from work on queries with external predicates, which are often infinite [[32](references.md#guagliardo_2025_queries.with.external.predicates)].

<a id="sec-7-1"></a>
## 7.1 Unrestricted relations and their algebra

<a id="def-r2-unrel"></a>

**Definition 7.1 (Unrestricted relation).** ✓

> An *unrestricted relation* $`U`$ is a heading $`H_U`$ and a Boolean term $`\chi _U`$, its *characteristic function*. Its tuples are the tuples $`t`$ that fit $`H_U`$ and have $`\chi _U(t) = \texttt{true}`$. Two unrestricted relations are *equivalent* when they hold the same tuples; their terms, and the domains of their headings, may differ.
>
> $`\omega [H](p)`$ is the unrestricted relation with heading $`H`$ and characteristic function $`p`$. $`\omega [H](p)`$ refuses a term $`p`$ that reads an attribute not in $`H`$. $`\omega [H]`$ is $`\omega [H](\texttt{true})`$: every tuple that fits $`H`$.

Uses: [Definition 5.1](tuples.md#def-r2-heading), [Definition 5.3](tuples.md#def-r2-term).<br>
Lean: [`Rasso.Unrel`](../Rasso/Term.lean#L273-L277), [`Rasso.Unrel.omega`](../Rasso/Term.lean#L297-L298), [`Rasso.UnrelLaws.Same`](../Rasso/Laws/Unrel.lean#L32-L33).

A term can refuse a tuple, for example when it compares an integer with a float. The next definition says what $`U`$ holds when that can happen.

<a id="def-r2-unrel-meaning"></a>

**Definition 7.2 (Meaning of an unrestricted relation).** ✓

> $`U`$ *holds* $`t`$ when $`t`$ fits $`H_U`$ and $`\chi _U(t) = \texttt{true}`$. A tuple that $`\chi _U`$ refuses is not held. $`U`$ is *total* when $`\chi _U`$ refuses no tuple that fits $`H_U`$. $`U`$ is *well formed* when $`H_U`$ names no attribute twice and $`\chi _U`$ reads only attributes of $`H_U`$.

Uses: [Definition 7.1](#def-r2-unrel), [Definition 5.2](tuples.md#def-r2-tuple).<br>
Lean: [`Rasso.Unrel.Holds`](../Rasso/Unrel.lean#L285-L286), [`Rasso.Unrel.Total`](../Rasso/Unrel.lean#L288-L289), [`Rasso.Unrel.WF`](../Rasso/Unrel.lean#L291-L294).

A well-formed term gives the same value on two tuples that agree on the attributes it reads (Lean: `Rasso.Term.eval_congr`). So the meaning of a well-formed relation does not depend on attributes outside its heading.

<a id="def-r2-unrel-ops"></a>

**Definition 7.3 (The algebra on unrestricted relations).** ✓

> The operators of Chapter [6](finite.md) act on characteristic functions:
>
> - $`\sigma [p](U)`$ has $`\chi _U \wedge p`$, and $`p`$ can read only attributes of $`U`$;
> - $`\rho [a \to b](U)`$ renames $`a`$ to $`b`$ in the heading and in $`\chi _U`$. It refuses as on a finite relation: an attribute that $`U`$ does not have, or a result that names an attribute twice;
> - $`U \bowtie V`$ has the heading of Definition [6.5](finite.md#def-r2-join) and $`\chi _U \wedge \chi _V`$; $`U \times V`$ is $`U \bowtie V`$, and refuses operands that share an attribute;
> - $`U \cup V`$ has $`\chi _U \vee \chi _V`$, $`U \cap V`$ has $`\chi _U \wedge \chi _V`$, and $`U - V`$ has $`\chi _U \wedge \neg \chi _V`$. All three need the same heading, and refuse operands whose headings differ.
>
> These operators never compute a tuple.

Uses: [Definition 7.1](#def-r2-unrel), [Definition 6.5](finite.md#def-r2-join).<br>
Lean: [`Rasso.Unrel.select`](../Rasso/Term.lean#L300-L302), [`Rasso.Unrel.join`](../Rasso/Term.lean#L304-L305), [`Rasso.Unrel.product`](../Rasso/Term.lean#L307-L310), [`Rasso.Unrel.union`](../Rasso/Term.lean#L317-L320), [`Rasso.Unrel.inter`](../Rasso/Term.lean#L322-L324), [`Rasso.Unrel.diff`](../Rasso/Term.lean#L326-L328), [`Rasso.Unrel.rename`](../Rasso/Term.lean#L312-L315), [`Rasso.Term.rename`](../Rasso/Term.lean#L287-L291), [`Rasso.Heading.same`](../Rasso/Finrel.lean#L39-L45), [`Rasso.Heading.scoped`](../Rasso/Term.lean#L279-L285), [`Rasso.Heading.renameCheck`](../Rasso/Finrel.lean#L264-L270).

<a id="def-r2-lift"></a>

**Definition 7.4 (Lifting a finite relation).** ✓

> $`\mathrm{lift}(R)`$, written `↑(R)` in $`\rho \alpha`$, makes a finite relation $`R`$, or the tuples of a sequence, an unrestricted relation. Its characteristic function is the disjunction, over the tuples $`t`$ of $`R`$, of the conjunctions $`\bigwedge _a (a = t(a))`$.

Uses: [Definition 7.1](#def-r2-unrel), [Definition 6.1](finite.md#def-r2-finrel).<br>
Lean: [`Rasso.Finrel.toUnrel`](../Rasso/Term.lean#L345-L348).

This is the Rasso paper’s observation that a finite relation is an unrestricted one whose characteristic function is in disjunctive normal form [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation), Appendix D.4, Listing 7]. A program writes $`\mathrm{lift}(\mathcal{E}[\texttt{all}](R))`$ to use a finite relation $`R`$ with an unrestricted one. RassoLean also lifts a finite operand of $`\bowtie`$, $`\cup`$ and $`-`$ when the other operand is unrestricted; the Racket implementation refuses that, and asks for `↑`.

<a id="sec-r2-unrel-projection"></a>
## 7.2 Projection

<a id="def-r2-unrel-pi"></a>

**Definition 7.5 (Projection of an unrestricted relation).** ✓

> $`\pi [A](U)`$ keeps the attributes $`A`$ of $`U`$. It holds a tuple $`t`$ over $`A`$ when $`U`$ holds some tuple whose restriction to $`A`$ is $`t`$. It refuses as on a finite relation: an attribute that $`U`$ does not have, or a list that names an attribute twice. The heading of the result follows the order of $`A`$.
>
> $`\pi`$ is an operator of the algebra. Rasso’s terms have no quantifier, and $`\pi`$ adds none. Projection by quantifier elimination is the method of constraint databases, after Kanellakis, Kuper and Revesz; where they fix one class of constraints, Rasso recognises a class for each attribute it removes. The connections with their work are explored in Chapter [8](cdb.md). Rasso fixes what $`\pi`$ holds, not how it is computed: an implementation accepts at least the four classes below, may accept more, and a refusal beyond them is the implementation’s limit. To compute $`\pi`$, RassoLean removes the dropped attributes one at a time. For each attribute $`a`$, a *recogniser* looks for a *class* that accepts $`U`$ and $`a`$. The class gives a new term without $`a`$. If no class accepts, $`\pi`$ refuses, and says why. Attributes whose domain has no end are removed first, then the others.
>
> There are four classes, tried in this order.
>
> - The *finite class* accepts $`a`$ when the domain of $`a`$ is finite. Its new term is the disjunction, over the values $`v`$ of the domain, of $`\chi _U`$ with $`v`$ in place of $`a`$.
> - The *dense-order class* accepts $`a`$ when the domain of $`a`$ is the `rat` kind, and every comparison that mentions $`a`$ compares it with an exact number: a constant, or an attribute whose domain holds exact numbers only. Its new term comes from Fourier’s method for order. Write $`\chi _U`$ as a disjunction of conjunctions, with $`\neg`$ pushed down to the comparisons ($`\neg (a = \tau )`$ becomes $`a {\lt} \tau \vee a {\gt} \tau`$). In each conjunction, if it has $`a = \tau`$, put $`\tau`$ for $`a`$. Otherwise, require each lower bound of $`a`$ to be below each upper bound. Parts of $`\chi _U`$ that do not mention $`a`$ stay as they are.
> - The *equality class* accepts $`a`$ when the domain of $`a`$ is the whole symbol, string or int kind, and every comparison that mentions $`a`$ is $`a = \tau`$, with the values of $`\tau`$ in the domain of $`a`$: a value of the domain, or an attribute whose domain is inside it. Write $`\chi _U`$ as a disjunction of conjunctions, with $`\neg`$ pushed down to the comparisons, and $`\neg (a = \tau )`$ kept as it is. In each conjunction, if it has $`a = \tau`$, put $`\tau`$ for $`a`$. Otherwise drop the comparisons on $`a`$: they are all $`\neg (a = \tau )`$, and the domain has more values than they exclude.
> - The *linear class* accepts $`a`$ when the domain of $`a`$ is the `rat` kind, and every comparison that mentions $`a`$ compares two *linear terms*: terms built by $`+`$, $`-`$ and $`\times`$ from exact numbers and attributes whose domain holds numbers only, with at most one factor that is not a constant in each product. Its new term comes from Fourier–Motzkin elimination. Read each comparison $`l \bowtie r`$ as the row $`c\, a + L \bowtie 0`$, where $`c`$ is the coefficient of $`a`$ in $`l - r`$ and $`L`$ is the rest. When $`c \neq 0`$ the row is the bound $`a \bowtie ' -L/c`$, with $`\bowtie`$ reversed when $`c {\lt} 0`$. When $`c = 0`$ the row does not mention $`a`$. Then remove $`a`$ as the dense-order class does, on the bounds. The new comparisons are written from the linear forms, because the method adds multiples of rows.
>
> The dense-order, equality and linear classes share the normal form. Each gives only how a comparison on $`a`$ is written, and how one conjunction loses $`a`$. When no class accepts, the refusal gives each class’s reason.

Uses: [Definition 7.1](#def-r2-unrel), [Definition 7.3](#def-r2-unrel-ops).<br>
Lean: [`Rasso.Unrel.project`](../Rasso/Project.lean#L145-L151), [`Rasso.recognise`](../Rasso/Project.lean#L114-L121), [`Rasso.Class`](../Rasso/Project.lean#L60-L66), [`Rasso.Class.elimTerm`](../Rasso/Project.lean#L107-L112), [`Rasso.Unrel.dropOne`](../Rasso/Project.lean#L123-L125), [`Rasso.Unrel.eliminate`](../Rasso/Project.lean#L127-L130), [`Rasso.dropOrder`](../Rasso/Project.lean#L132-L136), [`Rasso.Term.subst`](../Rasso/Project.lean#L46-L50).

The recogniser is sound, but it is not complete. The test for a linear term is syntactic, so $`x \times x - x \times x {\lt} 1`$ is refused, though $`x`$ cancels. An attribute with the float kind as its domain is refused even when no term reads it. A comparison of a `rat` attribute with a symbol is refused, though it is always true (numbers come before symbols). A later class can accept more. Each class meets one obligation, `Rasso.Class.elimTerm_sound`, and then the properties of projection (Theorem [7.9](#thm-r2-unrel-pi)) hold for it with no other change.

<a id="sec-7-3"></a>
## 7.3 Enumeration

<a id="def-r2-unrel-enum"></a>

**Definition 7.6 (Enumeration of an unrestricted relation).** ✓

> $`\mathcal{E}[k, d, e](U)`$ is a sequence $`s`$ of tuples of $`U`$ in the order of the key, as for a finite relation. It has $`k`$ tuples, or every tuple of $`U`$ when $`U`$ has fewer. No tuple of $`U`$ outside $`s`$ comes before a tuple of $`s`$ in the order of the key. $`\mathcal{E}[k, d, e](U)`$ has a result only when such a sequence exists. It is the boundary from unrestricted to finite.

Uses: [Definition 7.1](#def-r2-unrel), [Definition 6.9](finite.md#def-r2-enum).<br>
Lean: [`Rasso.Unrel.tuples`](../Rasso/Term.lean#L339-L341), [`Rasso.Unrel.assignments`](../Rasso/Term.lean#L330-L337).

RassoLean computes it only when $`U`$ is total and every domain of $`H_U`$ is finite.

When $`U`$ has finitely many tuples, the sequence exists. When $`U`$ has infinitely many, it can fail to exist. Over `x int` with the term `true`, no tuple is first in ascending order of $`x`$. Over the positive rationals, no tuple is first either: the values have a lower bound, and no tuple reaches it. In these cases $`\mathcal{E}[k, d, e](U)`$ has no result. Rasso states the problem, and whether a requested optimum exists is a fact about the problem.

$`\mathcal{E}`$ is the only way from an unrestricted relation to its tuples. To compute it, an implementation must find tuples that pass a test, and this is a search problem. RassoLean’s evaluator lists every tuple that fits the heading and tests each one, so it needs every domain to be finite. The Racket implementation can also give the problem to a constraint solver. Constraint databases optimise over such relations too: MLPQ has an operator that optimises a linear objective over a constraint relation by linear programming [[59](references.md#revesz_2010_introduction.databases.biological.spatio.temporal), § 13.7].

<a id="sec-7-4"></a>
## 7.4 In $`\rho \alpha`$ and RassoLean terms

The decision of the cakes problem is the number of cakes of a kind, from $`0`$ to $`100`$. `Qty` is an unrestricted relation with a finite domain, so RassoLean’s evaluator can list it. `Affordable` lists, in descending order, the values of `qty` for which `qty` cakes at $`400`$ each cost at most $`1000`$. In $`\rho \alpha`$:

```
Qty := ω[qty 0..100]
-- the qty with qty * 400 at most 1000, descending: 2, then 1, then 0
Affordable := ℰ[all, desc, qty](σ[qty * 400 <= 1000](Qty))
```

As RassoLean terms:

```
[("Qty", .omega [("qty", .range 0 100)]),
 ("Affordable",
  .enum
    .all
    (some (.desc, .attr "qty"))
    (.select
       (.call "<=" [.call "*" [.attr "qty", .val (.int 400)], .val (.int 1000)])
       (.name "Qty")))]
```

An unrestricted relation can also have infinitely many tuples. Australia’s goods and services tax (GST) is one eleventh of a price that includes it. This example comes from the Rasso paper [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation), Appendix D.3, Listings 5 and 6], with amounts in whole cents. In $`\rho \alpha`$:

```
GST := ω[price int, gst int, exgst int](
    price = gst * 11 ∧ exgst = price - gst)
Prices := ω[item symbol, price int]({<'p, 1100>, <'q, 2200>})
-- two tuples: <'p, 1100, 100, 1000>, <'q, 2200, 200, 2000>
Priced := ↑(ℰ[all](Prices)) ⋈ GST
```

As RassoLean terms:

```
[("GST",
  .omegaWhere
    [("price", .kind .int), ("gst", .kind .int), ("exgst", .kind .int)]
    (.call
       "and"
       [.call "=" [.attr "price", .call "*" [.attr "gst", .val (.int 11)]],
        .call "=" [.attr "exgst", .call "-" [.attr "price", .attr "gst"]]])),
 ("Prices",
  .omegaRows
    [("item", .kind .symbol), ("price", .kind .int)]
    [[.symbol "p", .int 1100], [.symbol "q", .int 2200]]),
 ("Priced", .nary .join [.lift (.enum .all none (.name "Prices")), .name "GST"])]
```

`GST` has infinitely many tuples, one for each multiple of $`11`$. It works in each direction: a price gives the tax, and a tax gives the price. RassoLean’s evaluator does not list the tuples of `Priced`, because its domains are not finite.

<a id="sec-7-5"></a>
## 7.5 Traditions to explore

We have yet to explore:

- the literature on external relations, whose tuples are given by a procedure or a test and not stored, to which the Rasso paper also refers;
- quantifier elimination for richer theories than the four classes here, such as linear arithmetic over the integers, and the constraint databases built on them.

An unrestricted relation can be the codomain of a function. The development continues in Chapter [9](sol.md), which takes the function space $`\mathit{Decision}^{\mathit{Data}}`$ from a finite relation $`\mathit{Data}`$ into an unrestricted relation $`\mathit{Decision}`$, and calls it a solution set. The next chapter is for the reader who wants more detail on the line of constraint databases that unrestricted relations come from.

<a id="properties"></a>
## Properties

Each property is proved in Lean. Sketches of the proofs are in Section [A.4](proofs.md#sec-r2-proofs-unrestricted).

<a id="thm-r2-unrel-ops"></a>

**Theorem 7.7 (What the operators hold).** ✓

> When the operator does not refuse:
>
> - $`\sigma [p](U)`$ holds $`t`$ exactly when $`U`$ holds $`t`$ and $`p(t) = \texttt{true}`$;
> - for well-formed $`U`$ and $`V`$, $`U \bowtie V`$ holds $`t`$ exactly when $`t`$ fits its heading, $`U`$ holds the restriction of $`t`$ to $`H_U`$, and $`V`$ holds its restriction to $`H_V`$;
> - for well-formed $`U`$, $`\rho [a \to b](U)`$ holds exactly the renamed tuples of what $`U`$ holds;
> - $`U \cap V`$ holds what both hold;
> - for total $`U`$ and $`V`$, $`U \cup V`$ holds what either holds;
> - for total $`V`$, $`U - V`$ holds what $`U`$ holds and $`V`$ does not.
>
> Each operator keeps well-formedness. Each keeps totality, for well-formed operands, and for $`\sigma`$ when $`p`$ gives a Boolean on every tuple that fits. $`U \times V`$ is $`U \bowtie V`$ on operands that share no attribute, and has its properties.

Uses: [Definition 7.2](#def-r2-unrel-meaning), [Definition 7.3](#def-r2-unrel-ops).<br>
Lean: [`Rasso.Unrel.select_holds`](../Rasso/Unrel.lean#L325-L336), [`Rasso.Unrel.join_holds`](../Rasso/Unrel.lean#L556-L569), [`Rasso.Unrel.union_holds`](../Rasso/Unrel.lean#L386-L408), [`Rasso.Unrel.inter_holds`](../Rasso/Unrel.lean#L429-L439), [`Rasso.Unrel.diff_holds`](../Rasso/Unrel.lean#L460-L475), [`Rasso.Unrel.product_ok`](../Rasso/Unrel.lean#L604-L613), [`Rasso.Unrel.select_wf`](../Rasso/Unrel.lean#L338-L346), [`Rasso.Unrel.join_wf`](../Rasso/Unrel.lean#L571-L580), [`Rasso.Unrel.union_wf`](../Rasso/Unrel.lean#L419-L427), [`Rasso.Unrel.inter_wf`](../Rasso/Unrel.lean#L450-L458), [`Rasso.Unrel.diff_wf`](../Rasso/Unrel.lean#L486-L494), [`Rasso.Unrel.select_total`](../Rasso/Unrel.lean#L348-L355), [`Rasso.Unrel.join_total`](../Rasso/Unrel.lean#L582-L589), [`Rasso.Unrel.union_total`](../Rasso/Unrel.lean#L410-L417), [`Rasso.Unrel.inter_total`](../Rasso/Unrel.lean#L441-L448), [`Rasso.Unrel.diff_total`](../Rasso/Unrel.lean#L477-L484), [`Rasso.Unrel.rename_holds`](../Rasso/Unrel.lean#L771-L783), [`Rasso.Unrel.rename_onto`](../Rasso/Unrel.lean#L785-L826), [`Rasso.Unrel.rename_wf`](../Rasso/Unrel.lean#L828-L834), [`Rasso.Unrel.rename_total`](../Rasso/Unrel.lean#L836-L848).<br>
[Proof sketch](proofs.md#sketch-thm-r2-unrel-ops).

<a id="thm-r2-lift"></a>

**Theorem 7.8 (Lift holds the finite relation’s tuples).** ✓

> For a well-formed finite relation $`R`$ whose domains are unmixed (Definition [4.3](values.md#def-r2-domain)), $`\mathrm{lift}(R)`$ is well formed and total, and holds exactly the tuples of $`R`$.

Uses: [Definition 7.4](#def-r2-lift), [Definition 7.2](#def-r2-unrel-meaning).<br>
Lean: [`Rasso.Finrel.toUnrel_holds`](../Rasso/Unrel.lean#L900-L928), [`Rasso.Finrel.toUnrel_total`](../Rasso/Unrel.lean#L930-L942), [`Rasso.Finrel.toUnrel_wf`](../Rasso/Unrel.lean#L944-L953).<br>
[Proof sketch](proofs.md#sketch-thm-r2-lift).

<a id="thm-r2-unrel-pi"></a>

**Theorem 7.9 (Projection agrees with the recogniser, and is sound).** ✓

> $`\pi [A](U)`$ gives a result exactly when $`A`$ names attributes of $`U`$, none twice, and the recogniser accepts, in turn, each attribute that $`\pi`$ removes.
>
> When $`U`$ is well formed and total and $`\pi [A](U)`$ gives a result, the result is well formed and total, and it holds $`t`$ exactly when $`U`$ holds some $`s`$ whose restriction to $`A`$ is $`t`$.

Uses: [Definition 7.5](#def-r2-unrel-pi), [Definition 7.2](#def-r2-unrel-meaning).<br>
Lean: [`Rasso.project_ok_iff`](../Rasso/Classes.lean#L438-L465), [`Rasso.project_sound`](../Rasso/Classes.lean#L485-L545), [`Rasso.recognise_ok_iff`](../Rasso/Classes.lean#L77-L89), [`Rasso.Class.elimTerm_sound`](../Rasso/Classes.lean#L130-L189), [`Rasso.eliminate_sound`](../Rasso/Classes.lean#L259-L320), [`Rasso.Term.eval_subst`](../Rasso/Subst.lean#L43-L60), [`Rasso.eval_project_unrel`](../Rasso/Bridge/Finrel.lean#L40-L49), [`Rasso.Dense.elim_sound`](../Rasso/Dense.lean#L706-L722), [`Rasso.Dense.accepts_iff`](../Rasso/Dense.lean#L740-L742), [`Rasso.Dense.DenseIn`](../Rasso/Dense.lean#L338-L347), [`Rasso.NF.elim_sound`](../Rasso/NormalFormProof.lean#L614-L714), [`Rasso.NF.dnf_sem`](../Rasso/NormalFormProof.lean#L241-L324), [`Rasso.Equality.elim_sound`](../Rasso/Equality.lean#L376-L391), [`Rasso.Equality.accepts_iff`](../Rasso/Equality.lean#L413-L416), [`Rasso.Equality.EqIn`](../Rasso/Equality.lean#L151-L154), [`Rasso.Equality.fresh`](../Rasso/Equality.lean#L81-L89), [`Rasso.Domain.subset?_mem`](../Rasso/Equality.lean#L21-L45), [`Rasso.Linear.elim_sound`](../Rasso/Linear.lean#L261-L276), [`Rasso.Linear.accepts_iff`](../Rasso/Linear.lean#L295-L297), [`Rasso.Linear.LinIn`](../Rasso/Linear.lean#L62-L64), [`Rasso.Linear.test_row`](../Rasso/Linear.lean#L32-L50), [`Rasso.Lin.ofTerm?_eval`](../Rasso/LinRead.lean#L169-L187), [`Rasso.Lin.render_eval`](../Rasso/LinRead.lean#L245-L250), [`Rasso.Lin.eval_split`](../Rasso/LinForm.lean#L88-L107).<br>
[Proof sketch](proofs.md#sketch-thm-r2-unrel-pi).

<a id="thm-r2-finite-class"></a>

**Theorem 7.10 (The finite class is closed).** ✓

> Call $`U`$ *in the finite class* when it is well formed and total, and each domain of its heading is finite. Then $`\sigma`$ with a total term, $`\bowtie`$, $`\cup`$, $`\cap`$, $`-`$, $`\rho`$ and $`\pi`$ keep the finite class. $`\pi`$ never refuses a relation in the finite class, except for its two checks on $`A`$.

Uses: [Definition 7.5](#def-r2-unrel-pi), [Theorem 7.7](#thm-r2-unrel-ops).<br>
Lean: [`Rasso.FiniteClass`](../Rasso/Classes.lean#L580-L585), [`Rasso.FiniteClass.select`](../Rasso/Classes.lean#L602-L606), [`Rasso.FiniteClass.join`](../Rasso/Classes.lean#L623-L633), [`Rasso.FiniteClass.union`](../Rasso/Classes.lean#L608-L611), [`Rasso.FiniteClass.inter`](../Rasso/Classes.lean#L613-L616), [`Rasso.FiniteClass.diff`](../Rasso/Classes.lean#L618-L621), [`Rasso.FiniteClass.rename`](../Rasso/Classes.lean#L635-L640), [`Rasso.FiniteClass.project`](../Rasso/Classes.lean#L642-L647), [`Rasso.FiniteClass.project_ok`](../Rasso/Classes.lean#L587-L592), [`Rasso.Domain.inter_finite`](../Rasso/Classes.lean#L594-L600).<br>
[Proof sketch](proofs.md#sketch-thm-r2-finite-class).

<a id="thm-r2-dense-class"></a>

**Theorem 7.11 (The dense-order class is closed).** ✓

> Call $`U`$ *in the dense-order class* when it is well formed, every domain of its heading is the `rat` kind, and $`\chi _U`$ is built from $`\wedge`$, $`\vee`$, $`\neg`$, the constants, and comparisons $`= {\lt} \le {\gt} \ge`$ of two operands, each an attribute or an exact number. Then $`U`$ is total. $`\sigma`$ with such a term, $`\bowtie`$, $`\cup`$, $`\cap`$, $`-`$, $`\rho`$ and $`\pi`$ keep the class. $`\pi`$ never refuses a relation in the class, except for its two checks on $`A`$.

Uses: [Definition 7.5](#def-r2-unrel-pi), [Theorem 7.9](#thm-r2-unrel-pi), [Theorem 7.7](#thm-r2-unrel-ops).<br>
Lean: [`Rasso.DenseClass`](../Rasso/DenseClosure.lean#L34-L38), [`Rasso.DenseShaped`](../Rasso/DenseClosure.lean#L22-L29), [`Rasso.DenseClass.total`](../Rasso/DenseClosure.lean#L88-L89), [`Rasso.DenseClass.select`](../Rasso/DenseClosure.lean#L102-L105), [`Rasso.DenseClass.join`](../Rasso/DenseClosure.lean#L123-L137), [`Rasso.DenseClass.union`](../Rasso/DenseClosure.lean#L107-L110), [`Rasso.DenseClass.inter`](../Rasso/DenseClosure.lean#L112-L115), [`Rasso.DenseClass.diff`](../Rasso/DenseClosure.lean#L117-L121), [`Rasso.DenseClass.rename`](../Rasso/DenseClosure.lean#L161-L167), [`Rasso.DenseClass.project`](../Rasso/DenseClosure.lean#L365-L382), [`Rasso.DenseClass.project_ok`](../Rasso/DenseClosure.lean#L359-L363).<br>
[Proof sketch](proofs.md#sketch-thm-r2-dense-class).

<a id="thm-r2-eq-class"></a>

**Theorem 7.12 (The equality class is closed).** ✓

> Let $`k`$ be the symbol, string or int kind. Call $`U`$ *in the equality class over $`k`$&#8203;* when it is well formed, every domain of its heading is the $`k`$ kind, and $`\chi _U`$ is built from $`\wedge`$, $`\vee`$, $`\neg`$, the constants, and $`=`$ of two operands, each an attribute or a value of $`k`$. Then $`U`$ is total. $`\sigma`$ with such a term, $`\bowtie`$, $`\cup`$, $`\cap`$, $`-`$, $`\rho`$ and $`\pi`$ keep the class. $`\pi`$ never refuses a relation in the class, except for its two checks on $`A`$.

Uses: [Definition 7.5](#def-r2-unrel-pi), [Theorem 7.9](#thm-r2-unrel-pi), [Theorem 7.7](#thm-r2-unrel-ops).<br>
Lean: [`Rasso.EqClass`](../Rasso/EqClosure.lean#L36-L40), [`Rasso.EqShaped`](../Rasso/EqClosure.lean#L25-L31), [`Rasso.EqClass.total`](../Rasso/EqClosure.lean#L87-L89), [`Rasso.EqClass.select`](../Rasso/EqClosure.lean#L104-L107), [`Rasso.EqClass.join`](../Rasso/EqClosure.lean#L127-L141), [`Rasso.EqClass.union`](../Rasso/EqClosure.lean#L109-L113), [`Rasso.EqClass.inter`](../Rasso/EqClosure.lean#L115-L119), [`Rasso.EqClass.diff`](../Rasso/EqClosure.lean#L121-L125), [`Rasso.EqClass.rename`](../Rasso/EqClosure.lean#L165-L171), [`Rasso.EqClass.project`](../Rasso/EqClosure.lean#L347-L364), [`Rasso.EqClass.project_ok`](../Rasso/EqClosure.lean#L341-L345).<br>
[Proof sketch](proofs.md#sketch-thm-r2-eq-class).

<a id="thm-r2-lin-class"></a>

**Theorem 7.13 (The linear class is closed).** ✓

> Call $`U`$ *in the linear class* when it is well formed, every domain of its heading is the `rat` kind, and $`\chi _U`$ is built from $`\wedge`$, $`\vee`$, $`\neg`$, the constants, and comparisons $`= {\lt} \le {\gt} \ge`$ of two linear terms. A linear term here is read from its syntax alone: attributes, exact numbers, $`+`$, $`-`$ with at least one operand, and $`\times`$ in which every factor but one reads no attribute. Then $`U`$ is total. $`\sigma`$ with such a term, $`\bowtie`$, $`\cup`$, $`\cap`$, $`-`$, $`\rho`$ and $`\pi`$ keep the class. $`\pi`$ never refuses a relation in the class, except for its two checks on $`A`$.

Uses: [Definition 7.5](#def-r2-unrel-pi), [Theorem 7.9](#thm-r2-unrel-pi), [Theorem 7.7](#thm-r2-unrel-ops).<br>
Lean: [`Rasso.LinClass`](../Rasso/LinClosure.lean#L46-L50), [`Rasso.LinShaped`](../Rasso/LinClosure.lean#L37-L44), [`Rasso.LinTerm`](../Rasso/LinClosure.lean#L24-L35), [`Rasso.LinTerm.read`](../Rasso/LinClosure.lean#L109-L169), [`Rasso.LinClass.total`](../Rasso/LinClosure.lean#L221-L222), [`Rasso.LinClass.select`](../Rasso/LinClosure.lean#L235-L238), [`Rasso.LinClass.join`](../Rasso/LinClosure.lean#L256-L270), [`Rasso.LinClass.union`](../Rasso/LinClosure.lean#L240-L243), [`Rasso.LinClass.inter`](../Rasso/LinClosure.lean#L245-L248), [`Rasso.LinClass.diff`](../Rasso/LinClosure.lean#L250-L254), [`Rasso.LinClass.rename`](../Rasso/LinClosure.lean#L319-L325), [`Rasso.LinClass.project`](../Rasso/LinClosure.lean#L593-L610), [`Rasso.LinClass.project_ok`](../Rasso/LinClosure.lean#L587-L591).<br>
[Proof sketch](proofs.md#sketch-thm-r2-lin-class).
