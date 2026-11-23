<a id="chap-r2-tuples"></a>
# 5 Headings, tuples and terms

This chapter gives the heading, which the rest of the report rests on. Every relation, finite or unrestricted, and every solution set has a heading. Every operator of the algebra says first what heading its result has, and refuses operands whose headings do not fit. The chapter then gives the tuples that fit a heading, and the terms that compute a value from a tuple.

Rasso uses the named perspective of the relational model: attributes have names, and a tuple is a function from names to values [[1](references.md#abiteboul_1995_foundations.of.databases), § 3.2]. A heading gives each attribute a domain, as a heading gives each attribute a type in The Third Manifesto [[21](references.md#date_2007_databases.types.relational.model.third)].

<a id="sec-5-1"></a>
## 5.1 Headings

<a id="def-r2-heading"></a>

**Definition 5.1 (Attribute, heading).** ✓

> An *attribute* is a name. A *heading* $`H`$ is a finite list of attributes, each with a domain, and no attribute appears twice; in RassoLean, this is part of a well-formed relation. $`\mathrm{attrs}(H)`$ is its set of attributes. The order of the list does not change which tuples a relation holds. It matters only where a relation is laid out column by column, as when it is written, displayed or flattened (Definition [9.7](sol.md#def-r2-flatten)): the columns follow the heading.

Uses: [Definition 4.3](values.md#def-r2-domain).<br>
Lean: [`Rasso.Heading`](../Rasso/Finrel.lean#L34-L35), [`Rasso.Heading.attrs`](../Rasso/Finrel.lean#L37), [`Rasso.Finrel.WF`](../Rasso/WF.lean#L156-L160), [`Rasso.Unrel.WF`](../Rasso/Unrel.lean#L291-L294).

The heading carries the structure of the algebra. Union, intersection and difference need two operands with the same heading. A join matches the attributes that two headings share, and gives each shared attribute the intersection of its two domains (Definition [4.4](values.md#def-r2-domain-inter)). A projection keeps some attributes of the heading, and a renaming changes their names. The heading with no attributes has two relations, which act as `true` and `false` (Chapter [6](finite.md)).

<a id="sec-5-2"></a>
## 5.2 Tuples

<a id="def-r2-tuple"></a>

**Definition 5.2 (Tuple).** ✓

> A *tuple* over a set of attributes $`A`$ is a function $`t : A \to \mathbb {V}`$. A tuple fits a heading $`H`$ when $`A = \mathrm{attrs}(H)`$ and $`t(a)`$ is in the domain of $`a`$ for each $`a`$. Two tuples $`t`$ and $`u`$ *agree* when $`t(a) = u(a)`$ for each attribute $`a`$ that they share; their *union* $`t \cup u`$ is then a tuple.

Uses: [Definition 5.1](#def-r2-heading).<br>
Lean: [`Rasso.Tuple`](../Rasso/Finrel.lean#L31-L32), [`Rasso.Tuple.ofPairs`](../Rasso/Finrel.lean#L56-L58), [`Rasso.Tuple.Sorted`](../Rasso/FSpace.lean#L125-L127), [`Rasso.Tuple.Fits`](../Rasso/WF.lean#L149-L154).

Lean holds a tuple as a list of (attribute, value) pairs, sorted by attribute, and orders tuples attribute by attribute, each value in the canonical order on values (Definition [4.2](values.md#def-r2-order)).

<a id="sec-5-3"></a>
## 5.3 Terms

<a id="def-r2-term"></a>

**Definition 5.3 (Term).** ✓

> A *term* computes a value from a tuple. A term is a value, an attribute, or an operator applied to terms. The operators, as RassoLean evaluates them, are:
>
> - arithmetic on exact numbers (integers and rationals): $`+`$, $`-`$, $`\times`$;
> - arithmetic on integers only: $`\%`$ and `abs`, which refuse a rational that is not an integer;
> - `min`, `max` and `sum` of their arguments, and `all_different`;
> - comparisons: $`=`$, $`{\lt}`$, $`\le`$, $`{\gt}`$, $`\ge`$; $`=`$ refuses an exact number beside a float, and a symbol beside a string;
> - logic: `∧`, `∨`, `¬`.
>
> The value of a term $`e`$ on a tuple $`t`$ is $`e(t)`$. A term that misuses a value, such as $`1 + \texttt{true}`$, has no value: evaluation refuses it. A *Boolean term* is a term whose value is a Boolean.

Uses: [Definition 5.2](#def-r2-tuple), [Definition 4.2](values.md#def-r2-order).<br>
Lean: [`Rasso.Term`](../Rasso/Form.lean#L98-L102), [`Rasso.Term.eval`](../Rasso/Term.lean#L101-L107), [`Rasso.applyOp`](../Rasso/Term.lean#L63-L99).

Terms have no quantifier. Over unrestricted relations, the existential quantifier is projection (Definition [7.5](unrestricted.md#def-r2-unrel-pi)), an operator of the algebra, not a part of terms. The language also has `has_subset` of a relation, which RassoLean evaluates in conditions of solution sets and in grouping.

<a id="sec-5-4"></a>
## 5.4 In $`\rho \alpha`$ and RassoLean terms

A heading is written as attribute and domain pairs, as in SQL’s `CREATE TABLE`. A tuple lists its values in the order of the heading, between angle brackets. The cakes of the running example (Chapter [3](cakes.md)) have this heading, and these tuples fit it. In $`\rho \alpha`$:

```
[cake symbol, price int] -- heading
{<'Banana, 400>, <'Chocolate, 450>} -- two tuples
```

As RassoLean terms:

```
[("cake", .kind .symbol), ("price", .kind .int)] -- heading
[[.symbol "Banana", .int 400], [.symbol "Chocolate", .int 450]] -- two tuples
```

In $`\rho \alpha`$, terms are written as in SQL. A RassoLean term is an attribute (`.attr`), a value (`.val`), or an operator, named by a string, applied to a list of terms (`.call`). The cakes program uses this term, where `qty` is the number of cakes of a kind and `price` its price. In $`\rho \alpha`$:

```
qty * price
```

As a RassoLean term:

```
.call "*" [.attr "qty", .attr "price"]
```

<a id="sec-5-5"></a>
## 5.5 Traditions to explore

We have yet to explore:

- type systems for query languages, which refuse a term such as $`1 + \texttt{true}`$ before evaluation, where RassoLean refuses it when it is evaluated.

A heading and the tuples that fit it are the material of a relation. The next chapter gives the finite relations and their algebra.

<a id="properties"></a>
## Properties

Each property is proved in Lean. Sketches of the proofs are in Section [A.2](proofs.md#sec-r2-proofs-tuples).

<a id="thm-r2-tuple-ext"></a>

**Theorem 5.4 (Tuples are functions).** ✓

> Two tuples, each sorted by attribute as RassoLean holds them, are equal exactly when they give each attribute the same value.

Uses: [Definition 5.2](#def-r2-tuple).<br>
Lean: [`Rasso.Tuple.ext_get?`](../Rasso/FSpace.lean#L157-L211).<br>
[Proof sketch](proofs.md#sketch-thm-r2-tuple-ext).

<a id="thm-r2-tuple-order"></a>

**Theorem 5.5 (The order on tuples).** ✓

> The order on tuples is a total order.

Uses: [Definition 5.2](#def-r2-tuple), [Theorem 4.6](values.md#thm-r2-value-orders).<br>
Lean: [`Rasso.Tuple.le_trans`](../Rasso/Finrel.lean#L90-L92), [`Rasso.Tuple.le_total`](../Rasso/Finrel.lean#L94-L99), [`Rasso.Tuple.le_antisymm`](../Rasso/Finrel.lean#L101-L103).<br>
[Proof sketch](proofs.md#sketch-thm-r2-tuple-order).
