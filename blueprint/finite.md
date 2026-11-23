<a id="chap-r2-finite"></a>
# 6 Finite relations and databases

This chapter gives the finite relations and their algebra: Codd’s relational algebra, with grouping and aggregation and with computed attributes. It also gives databases, from which a program reads its relations with $`\mathrm{db\_ ref}`$. It ends with sequences, which order an answer and cut it to a length, and so leave the algebra.

The algebra is that of Codd [[20](references.md#codd_1970_relational.model.data.large.shared), [19](references.md#codd_1972_relational.completeness.data.base.sublanguages)], on relations with a heading of named attributes, each with a domain. It has two later additions: grouping with aggregation, whose meaning Klug made precise [[41](references.md#klug_1982_equivalence.relational.algebra.relational.calculus)], and computed attributes, Tutorial D’s EXTEND [[21](references.md#date_2007_databases.types.relational.model.third)]. Relational algebra and SQL have been formalised in Coq [[9](references.md#benzaken_2014_coq.formalization.relational.data.model), [8](references.md#benzaken_2019_coq.mechanised.formal.semantics.realistic)]. Rasso’s operators are Codd’s: the project’s Coddstheorem library proves Codd’s theorem for them (Theorem [6.14](#thm-r2-codd)). Chapter [12](eso.md) uses Codd’s translation to turn the first-order part of an existential second-order sentence into a Rasso condition.

<a id="sec-6-1"></a>
## 6.1 Relations and their bodies

<a id="def-r2-finrel"></a>

**Definition 6.1 (Finite relation).** ✓

> A *finite relation* over a heading $`H`$, in which no attribute is named twice, is what these two build:
>
> - *empty*: the relation with no tuples;
> - *adjoin* $`t`$ to $`R`$: the relation $`R`$ with the tuple $`t`$ added, where $`t`$ fits $`H`$.
>
> Adjoining a tuple that is already there changes nothing, and the order in which tuples are adjoined does not matter. For a finite relation $`R`$, $`H_R`$ is its heading and its *body* $`B_R`$ is the set of tuples adjoined.
>
> That the operators of this chapter give finite relations again is a property of each operator (Theorem [6.13](#thm-r2-finrel-closed)), not part of this definition.

Uses: [Definition 5.1](tuples.md#def-r2-heading), [Definition 5.2](tuples.md#def-r2-tuple).<br>
Lean: [`Rasso.Finrel`](../Rasso/Finrel.lean#L193-L197), [`Rasso.Body`](../Rasso/Finrel.lean#L148-L149), [`Rasso.Body.empty`](../Rasso/Finrel.lean#L184), [`Rasso.Body.adjoin`](../Rasso/Finrel.lean#L185), [`Rasso.Body.ofList`](../Rasso/Finrel.lean#L168), [`Rasso.Body.toList`](../Rasso/Finrel.lean#L170-L171), [`Rasso.Finrel.WF`](../Rasso/WF.lean#L156-L160), [`Rasso.Finrel.empty`](../Rasso/Built.lean#L81-L82), [`Rasso.Finrel.adjoin`](../Rasso/Built.lean#L84-L85), [`Rasso.Finrel.Built`](../Rasso/Built.lean#L133-L138).

Lean writes this definition in two parts. The type `Rasso.Finrel` is a heading and a body, and it admits any body. The predicate `Finrel.WF`, *well formed*, says that the heading names no attribute twice and that each tuple of the body fits the heading. The well-formed values of the type are exactly the finite relations of the definition (Theorem [6.10](#thm-r2-built)).

The body is a set. So the order in which a program writes or computes the tuples is not part of the relation, and a tuple written twice is in the body once. Lean renders this with a quotient: a body is a list of tuples, up to the relation “has the same elements”. Mathlib builds its finite collections from lists in the same way: a `Multiset` is a list up to the order of its elements, and a `Finset` is a multiset with no repeats [[69](references.md#community_2019_the.lean.mathematical.library)]. RassoLean’s quotient also ignores repeats, and uses only the quotients of core Lean. The one way to look into a body is its *canonical list*: its tuples with no repeats, sorted in the order on tuples. Each operator computes on canonical lists and makes a body again (Theorem [6.12](#thm-r2-canon)).

A heading with no attributes has exactly two relations: one with the empty tuple in its body, and one with an empty body. Darwen named them TABLE\_DEE and TABLE\_DUM [[21](references.md#date_2007_databases.types.relational.model.third)]. They act as `true` and `false`: $`R \bowtie \mathrm{DEE} = R`$ and $`R \bowtie \mathrm{DUM}`$ is empty.

A program gets a relation in one of two ways: it instantiates a relation with the $`\omega`$ operator, or it reads the relation from a database (below). In Codd’s algebra, the operands are the relations of the database, and, for a constant in a comparison, the relation $`\{ a\}`$ of one tuple [[19](references.md#codd_1972_relational.completeness.data.base.sublanguages), § 4.1, Step 4]. Abiteboul, Hull and Vianu make such constants part of the language, and with union they give any finite relation [[1](references.md#abiteboul_1995_foundations.of.databases), § 4.4, § 5.1]. Rasso’s $`\omega`$ writes a relation from its heading, which gives each attribute a domain, in the manner of SQL’s `CREATE TABLE` with `VALUES` [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation), Appendix C.1]. The $`\omega`$ operator has one form for each kind of value in this report and is nullary in the algebra of its kind. The form for finite relations is below (Definition [6.3](#def-r2-omega-rows)); the others are in their chapters.

<a id="def-r2-db"></a>

**Definition 6.2 (Database).** ✓

> A *database* is a finite map from names to finite relations. $`\mathrm{db\_ ref}[n](D)`$ is the relation that the database $`D`$ gives to the name $`n`$.

Uses: [Definition 6.1](#def-r2-finrel).<br>
Lean: [`Rasso.Db`](../Rasso/Eval.lean#L105-L106).

The running example reads its relations from $`D`$ (Chapter [3](cakes.md)).

<a id="sec-6-2"></a>
## 6.2 The algebra

The set of operators is a choice. Codd’s algebra has Cartesian product, $`\theta`$-join and division among its operations [[19](references.md#codd_1972_relational.completeness.data.base.sublanguages), § 2.3]. Abiteboul, Hull and Vianu give two nonredundant sets, $`\{ \sigma , \pi , \times , \cup , -\}`$ over positions and $`\{ \sigma , \pi , \bowtie , \rho , \cup , -\}`$ over named attributes, and show that the two have the same expressive power [[1](references.md#abiteboul_1995_foundations.of.databases), § 4.4, § 5.1]. Rasso takes the named set, with natural join, and keeps two operators that it derives: product, which is natural join when no attribute is shared, and intersection, which is $`R - (R - S)`$.

The definitions write each operator in mathematical notation that mirrors $`\rho \alpha`$: $`\sigma [p](R)`$ in a definition is written `σ[p](R)` in a listing. Italic letters stand for any value of their kind; code font is literal $`\rho \alpha`$. In these definitions $`R`$ and $`S`$ are finite relations, $`p`$ and $`e`$ are terms, and $`A`$ is a list of attributes. An operator refuses its operands when the stated conditions do not hold.

<a id="def-r2-omega-rows"></a>

**Definition 6.3 (Relation by enumeration).** ✓

> $`\omega [H](\{ t_1, \ldots , t_n\} )`$ is the finite relation with heading $`H`$ and body $`\{ t_1, \ldots , t_n\}`$. Each tuple must fit $`H`$.

Uses: [Definition 6.1](#def-r2-finrel).<br>
Lean: [`Rasso.Expr.eval`](../Rasso/Eval.lean#L366-L561).

<a id="def-r2-spr"></a>

**Definition 6.4 (Selection, projection, renaming).** ✓

> - $`\sigma [p](R)`$ has heading $`H_R`$ and body $`\{ t \in B_R \mid p(t) = \texttt{true}\}`$. The term $`p`$ can read only attributes of $`R`$.
> - $`\pi [A](R)`$ has the attributes $`A`$, which must be attributes of $`R`$, with their domains, and body $`\{ t|_A \mid t \in B_R\}`$.
> - $`\rho [a \to b](R)`$ renames the attribute $`a`$ of $`R`$ to $`b`$. The name $`b`$ must not be an attribute of $`R`$ already.

Uses: [Definition 6.1](#def-r2-finrel), [Definition 5.3](tuples.md#def-r2-term).<br>
Lean: [`Rasso.Finrel.select`](../Rasso/Finrel.lean#L207-L210), [`Rasso.Finrel.project`](../Rasso/Finrel.lean#L212-L219), [`Rasso.Finrel.rename`](../Rasso/Eval.lean#L238-L241).

<a id="def-r2-join"></a>

**Definition 6.5 (Natural join, product).** ✓

> $`R \bowtie S`$ has the attributes of $`R`$, then the attributes of $`S`$ that $`R`$ does not have. A shared attribute has the intersection of its two domains. The body is $`\{ t \cup u \mid t \in B_R,\ u \in B_S,\ t \text{ and } u \text{ agree}\}`$. $`R \times S`$ is $`R \bowtie S`$ when $`R`$ and $`S`$ share no attribute. It refuses operands that share an attribute.

Uses: [Definition 6.1](#def-r2-finrel), [Definition 4.4](values.md#def-r2-domain-inter).<br>
Lean: [`Rasso.Finrel.join`](../Rasso/Finrel.lean#L229-L234), [`Rasso.Finrel.joinHeading`](../Rasso/Finrel.lean#L221-L227), [`Rasso.Finrel.product`](../Rasso/Eval.lean#L352-L355).

<a id="def-r2-setops"></a>

**Definition 6.6 (Union, intersection, difference).** ✓

> $`R \cup S`$, $`R \cap S`$ and $`R - S`$ need the same heading: the same attributes, each with the same domain. The body is $`B_R \cup B_S`$, $`B_R \cap B_S`$ or $`B_R \setminus B_S`$.

Uses: [Definition 6.1](#def-r2-finrel).<br>
Lean: [`Rasso.Finrel.union`](../Rasso/Finrel.lean#L241-L244), [`Rasso.Finrel.inter`](../Rasso/Eval.lean#L347-L350), [`Rasso.Finrel.diff`](../Rasso/Finrel.lean#L246-L249), [`Rasso.Finrel.sameHeading`](../Rasso/Finrel.lean#L236-L239).

<a id="def-r2-extend"></a>

**Definition 6.7 (Extension).** ✓

> $`\mathrm{extend}[e \to a](R)`$ adds the attribute $`a`$ to each tuple $`t`$ of $`R`$, with the value $`e(t)`$. The domain of $`a`$ comes from $`e`$ and $`H_R`$, never from the data.

Uses: [Definition 6.1](#def-r2-finrel), [Definition 5.3](tuples.md#def-r2-term).<br>
Lean: [`Rasso.Finrel.extend`](../Rasso/Eval.lean#L357-L363), [`Rasso.Term.domain`](../Rasso/Term.lean#L149-L156).

<a id="def-r2-gamma"></a>

**Definition 6.8 (Grouping and aggregation).** ✓

> $`\gamma [G][e \to a](R)`$ groups the tuples of $`R`$ by their values on the attributes $`G`$. Its result has the attributes $`G`$ and $`a`$, and one tuple for each group. In that tuple, $`a`$ has the value of $`e`$ on the group. In $`e`$, an aggregate applied to a term stands for a value: `count`, `sum`, `min`, `max`, `bool_and`, `bool_or` or `all_different` of the values that the term takes on the group’s tuples. Outside an aggregate, $`e`$ can use only the attributes $`G`$. $`G`$ must name attributes of $`R`$, none twice, and $`a`$ must not be in $`G`$.
>
> When $`G`$ is empty, there is exactly one group, also when $`R`$ is empty. On an empty group, `count` and `sum` give $`0`$, `bool_and` gives `true`, `bool_or` gives `false`, and `min` and `max` are refused.

Uses: [Definition 6.1](#def-r2-finrel), [Definition 5.3](tuples.md#def-r2-term).<br>
Lean: [`Rasso.Finrel.gamma`](../Rasso/Term.lean#L248-L269), [`Rasso.Agg`](../Rasso/Form.lean#L104-L110), [`Rasso.Agg.eval`](../Rasso/Term.lean#L183-L195), [`Rasso.aggregate`](../Rasso/Term.lean#L170-L181).

The rule for an empty $`G`$ is SQL’s: a query with aggregates and no GROUP BY gives one row.

<a id="sec-r2-sequences"></a>
## 6.3 Leaving the algebra: sequences

A database answer is often a list in an order, cut to a length. Rasso has a separate kind of value for this.

<a id="def-r2-enum"></a>

**Definition 6.9 (Sequence of tuples; enumeration).** ✓

> A *sequence of tuples* is a heading and a list of tuples with no tuple twice. $`\mathcal{E}[k, d, e](R)`$ is the sequence of at most $`k`$ tuples of $`R`$, in the order of the values $`e(t)`$: ascending when $`d`$ is `asc`, descending when it is `desc`. The key $`e`$ can be list($`e_1`$, …, $`e_n`$): the tuples are then ordered by $`e_1`$, then by $`e_2`$ when $`e_1`$ ties, and so on. The count $`k`$ can be `all`. With no key, $`\mathcal{E}[k](R)`$ gives at most $`k`$ tuples of $`R`$.

Uses: [Definition 6.1](#def-r2-finrel), [Definition 4.2](values.md#def-r2-order).<br>
Lean: [`Rasso.Val`](../Rasso/Eval.lean#L119-L129), [`Rasso.sortTake`](../Rasso/Eval.lean#L223-L226), [`Rasso.cmpKeys`](../Rasso/Eval.lean#L215-L221), [`Rasso.Count`](../Rasso/Form.lean#L56-L59), [`Rasso.Order`](../Rasso/Form.lean#L61-L63).

When two tuples tie on the key, Rasso does not say which comes first. RassoLean breaks ties by the canonical order, and `all` is the count $`2^{63}-1`$.

Three operators take a sequence. $`\pi [A](Q)`$ gives a sequence: it keeps the order, and keeps each restricted tuple at its first place. So a program can order by an attribute and then drop it. $`\mathrm{forget}(Q)`$ gives the finite relation with the tuples of $`Q`$, and $`\mathrm{lift}(Q)`$ (Definition [7.4](unrestricted.md#def-r2-lift)) the unrestricted relation; both forget the order.

<a id="sec-6-4"></a>
## 6.4 In $`\rho \alpha`$ and RassoLean terms

In $`\rho \alpha`$, an operator is written with its symbol, its subscripts in square brackets and its operands in parentheses, as in $`\sigma [p](R)`$, or between its operands, as in $`R \bowtie S`$. A program is a list of statements, each a name and an expression, and its answer is the value of the last. As RassoLean terms, a program is a list of pairs, each a name and a value of type `Rasso.Expr`.

The cakes program (Chapter [3](cakes.md)) starts by reading its three relations from the database $`D`$. In $`\rho \alpha`$:

```
Cakes := db_ref[Cakes](D)
Recipe := db_ref[Recipe](D)
Inventory := db_ref[Inventory](D)
```

As RassoLean terms:

```
[("Cakes", .dbRef "Cakes" (.name "D")),
 ("Recipe", .dbRef "Recipe" (.name "D")),
 ("Inventory", .dbRef "Inventory" (.name "D"))]
```

In the line `Cakes := db_ref[Cakes](D)`, the word `Cakes` appears twice. Inside `db_ref[…]`, it names a relation in $`D`$. Before `:=`, it names the statement, and the rest of the program refers to the statement by that name. The two need not agree; here they do, for readability.

Over these three relations, each operator of this chapter gives an expression, one to a line. In $`\rho \alpha`$:

```
-- the dearer cake: <'Chocolate, 450>
σ[price > 400](Cakes)
-- the five ingredients: 'Banana, 'Butter, 'Cocoa, 'Flour, 'Sugar
π[ingredient](Recipe)
-- Inventory with the heading [ingredient symbol, stock int]
ρ[avail → stock](Inventory)
-- each recipe line with its stock, 8 tuples, such as <'Banana, 'Flour, 250, 4000>
Recipe ⋈ Inventory
-- the ingredients of both cakes: 'Butter, 'Flour, 'Sugar
π[ingredient](σ[cake = 'Banana](Recipe)) ∩ π[ingredient](σ[cake = 'Chocolate](Recipe))
-- what one cake leaves of an ingredient, such as <'Banana, 'Flour, 250, 4000, 3750>
extend[avail - amount → left](Recipe ⋈ Inventory)
-- each ingredient's amount over both cakes, such as <'Flour, 450>
γ[ingredient][sum(amount) → total](Recipe)
-- a sequence, not a relation: Chocolate, then Banana
ℰ[all, desc, price](Cakes)
```

As RassoLean terms:

```
[.select (.call ">" [.attr "price", .val (.int 400)]) (.name "Cakes"),
 .project ["ingredient"] (.name "Recipe"),
 .rename [("avail", "stock")] (.name "Inventory"),
 .nary .join [.name "Recipe", .name "Inventory"],
 .nary
   .intersect
   [.project
      ["ingredient"]
      (.select
         (.call "=" [.attr "cake", .val (.symbol "Banana")])
         (.name "Recipe")),
    .project
      ["ingredient"]
      (.select
         (.call "=" [.attr "cake", .val (.symbol "Chocolate")])
         (.name "Recipe"))],
 .extend
   "left"
   (.call "-" [.attr "avail", .attr "amount"])
   (.nary .join [.name "Recipe", .name "Inventory"]),
 .gamma
   ["ingredient"]
   (.agg "sum" (.attr "amount"))
   (some "total")
   (.name "Recipe"),
 .enum .all (some (.desc, .attr "price")) (.name "Cakes")]
```

<a id="sec-6-5"></a>
## 6.5 Traditions to explore

We have yet to explore:

- algebras on bags, which keep repeated tuples as SQL does, and their aggregation;
- algebras on lists or ordered relations, such as po-relations, which keep an order inside the algebra, where Rasso’s sequences leave it.

A finite relation lists its tuples. The next chapter gives relations that may have infinitely many tuples, written by constraints: the unrestricted relations, from which a decision draws its values.

<a id="properties"></a>
## Properties

Each property is proved in Lean. Codd’s theorem is proved in the Coddstheorem library, which imports RassoLean, following the proof of the Equivalence Theorem of Abiteboul, Hull and Vianu [[1](references.md#abiteboul_1995_foundations.of.databases), Theorem 5.3.10, Lemmas 5.3.11 and 5.3.12], extended with order comparisons. Sketches of the other proofs are in Section [A.3](proofs.md#sec-r2-proofs-finite).

<a id="thm-r2-built"></a>

**Theorem 6.10 (A finite relation is what empty and adjoin build).** ✓

> - Adjoining a tuple that is already in $`R`$ gives $`R`$. Adjoining $`t`$ and then $`u`$ gives the same relation as adjoining $`u`$ and then $`t`$.
> - The empty relation over $`H`$ is well formed when $`H`$ names no attribute twice. Adjoin to a well-formed $`R`$ gives a well-formed relation exactly when the tuple fits $`H_R`$.
> - A value of `Rasso.Finrel` is well formed exactly when its heading names no attribute twice and the value is built from empty by adjoining tuples that fit the heading.

Uses: [Definition 6.1](#def-r2-finrel).<br>
Lean: [`Rasso.Finrel.wf_iff_built`](../Rasso/Built.lean#L170-L173), [`Rasso.Finrel.wf_and_heading_iff_built`](../Rasso/Built.lean#L175-L184), [`Rasso.Finrel.empty_wf`](../Rasso/Built.lean#L188-L189), [`Rasso.Finrel.adjoin_wf`](../Rasso/Built.lean#L191-L193), [`Rasso.Finrel.adjoin_wf_iff`](../Rasso/Built.lean#L195-L198), [`Rasso.Body.adjoin_idem`](../Rasso/Built.lean#L56-L58), [`Rasso.Body.adjoin_comm`](../Rasso/Built.lean#L60-L65), [`Rasso.Body.adjoin_of_mem`](../Rasso/Built.lean#L50-L54), [`Rasso.Finrel.adjoin_idem`](../Rasso/Built.lean#L109-L111), [`Rasso.Finrel.adjoin_comm`](../Rasso/Built.lean#L113-L116), [`Rasso.Finrel.ext`](../Rasso/Built.lean#L97-L102).<br>
[Proof sketch](proofs.md#sketch-thm-r2-built).

<a id="thm-r2-finrel-induction"></a>

**Theorem 6.11 (Induction on empty and adjoin).** ✓

> Let $`P`$ be a property of finite relations over $`H`$. Suppose that $`P`$ holds of the empty relation, and that $`P`$ holds of $`R`$ with $`t`$ adjoined whenever $`P`$ holds of $`R`$ and $`t`$ fits $`H`$. Then $`P`$ holds of every finite relation over $`H`$. The same is true when the second supposition is made only for tuples $`t`$ that are not in $`R`$.

Uses: [Theorem 6.10](#thm-r2-built).<br>
Lean: [`Rasso.Finrel.WF.induction`](../Rasso/Built.lean#L234-L241), [`Rasso.Finrel.WF.induction_fresh`](../Rasso/Built.lean#L224-L232), [`Rasso.Finrel.nodup_tuples`](../Rasso/Built.lean#L217-L222).<br>
[Proof sketch](proofs.md#sketch-thm-r2-finrel-induction).

<a id="thm-r2-canon"></a>

**Theorem 6.12 (The body is well defined).** ✓

> Two lists of tuples with the same elements give the same canonical list. The canonical list of a body has the same elements as the body, and gives the body back.

Uses: [Definition 6.1](#def-r2-finrel), [Theorem 5.5](tuples.md#thm-r2-tuple-order).<br>
Lean: [`Rasso.canon_eq`](../Rasso/Finrel.lean#L157-L166), [`Rasso.Body.toList_eq`](../Rasso/Finrel.lean#L173-L174), [`Rasso.Body.ofList_toList`](../Rasso/Finrel.lean#L179-L182), [`Rasso.Body.mem_toList_ofList`](../Rasso/Finrel.lean#L176-L177).<br>
[Proof sketch](proofs.md#sketch-thm-r2-canon).

<a id="thm-r2-finrel-closed"></a>

**Theorem 6.13 (The operators give finite relations again).** ✓

> When its operands are finite relations and it does not refuse them, each of $`\sigma`$, $`\pi`$, $`\rho`$, $`\bowtie`$, $`\times`$, $`\cup`$, $`\cap`$, $`-`$, $`\mathrm{extend}`$ and $`\gamma`$ gives a finite relation. For $`\mathrm{extend}`$ and $`\gamma`$, the theorem supposes that each value of the expression is in the domain that the expression and $`H_R`$ give to the new attribute.

Uses: [Theorem 6.10](#thm-r2-built), [Definition 6.4](#def-r2-spr), [Definition 6.5](#def-r2-join), [Definition 6.6](#def-r2-setops), [Definition 6.7](#def-r2-extend), [Definition 6.8](#def-r2-gamma).<br>
Lean: [`Rasso.Finrel.select_wf`](../Rasso/WF.lean#L200-L203), [`Rasso.Finrel.project_wf`](../Rasso/WF.lean#L258-L274), [`Rasso.Finrel.rename_wf`](../Rasso/WF.lean#L276-L302), [`Rasso.Finrel.join_wf`](../Rasso/WF.lean#L457-L467), [`Rasso.Finrel.product_wf`](../Rasso/Unrel.lean#L642-L646), [`Rasso.Finrel.union_wf`](../Rasso/WF.lean#L214-L224), [`Rasso.Finrel.inter_wf`](../Rasso/WF.lean#L234-L240), [`Rasso.Finrel.diff_wf`](../Rasso/WF.lean#L226-L232), [`Rasso.Finrel.extend_wf`](../Rasso/WF.lean#L485-L527), [`Rasso.Finrel.gamma_wf`](../Rasso/Built.lean#L302-L390), [`Rasso.Finrel.gamma_spec`](../Rasso/Built.lean#L245-L285), [`Rasso.Finrel.mem_gamma`](../Rasso/Built.lean#L287-L300).<br>
[Proof sketch](proofs.md#sketch-thm-r2-finrel-closed).

<a id="thm-r2-codd"></a>

**Theorem 6.14 (Codd’s theorem for Rasso’s operators).** ✓

> The relational algebra of $`\omega`$ with rows, $`\sigma`$, $`\pi`$, $`\rho`$, $`\bowtie`$, $`\times`$, $`\cup`$, $`\cap`$ and $`-`$, as RassoLean’s evaluator runs them, with each condition of $`\sigma`$ built from comparisons ($`=`$, $`{\lt}`$, $`\le`$, $`{\gt}`$, $`\ge`$) of an attribute with an attribute or a constant, under $`\wedge`$, $`\vee`$ and $`\neg`$; the relational calculus under active-domain semantics, with the same comparisons; and the domain-independent calculus define the same queries [[1](references.md#abiteboul_1995_foundations.of.databases), Theorem 5.3.10]. The schema is one-sorted and well formed, with a domain that does not mix exact numbers with floats, nor symbols with strings; the queries are well typed, and their constants are in the domain. Proved in Lean in the library Coddstheorem, which imports RassoLean.

Uses: [Definition 6.3](#def-r2-omega-rows), [Definition 6.4](#def-r2-spr), [Definition 6.5](#def-r2-join), [Definition 6.6](#def-r2-setops).<br>
Lean: [`Coddstheorem.codd`](../Coddstheorem/Theorem.lean#L112-L120), [`Coddstheorem.algebra_domainIndependent`](../Coddstheorem/Theorem.lean#L122-L135).
