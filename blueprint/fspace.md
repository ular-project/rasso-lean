<a id="chap-r2-fspace"></a>
# 10 Why function spaces

Rasso extends Codd’s algebra one level up: from relations to sets of candidate relations. Such an algebra needs a carrier, a set of relations that its operators act on. This chapter says why the carrier is the function space $`\mathit{Decision}^{\mathit{Data}}`$ of Chapter [9](sol.md), as the Rasso paper builds its search spaces by exponentiation [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation), § 4.1], and not the powerset $`\mathcal{P}(\mathit{Data}\times \mathit{Decision})`$. Chapter [9](sol.md) sets this choice against earlier algebras.

<a id="sec-10-1"></a>
## 10.1 The goal: Codd’s algebra one level up

A search problem has data, decisions and constraints. Rasso makes the function space of its candidates a carrier, so that the operators of the algebra act on it as they act on a relation: selection keeps candidates, join combines two spaces, rename renames them. This chapter does not define these operators; Chapter [9](sol.md) does. The question here is which set of relations they act on.

<a id="sec-10-2"></a>
## 10.2 Two carriers

The first carrier to hand is the powerset $`\mathcal{P}(\mathit{Data}\times \mathit{Decision})`$: every relation between the data and the decisions. The second is the function space $`\mathit{Decision}^{\mathit{Data}}`$: every function from the tuples of $`\mathit{Data}`$ to the tuples of $`\mathit{Decision}`$, held as its graph. A graph is a relation in $`\mathcal{P}(\mathit{Data}\times \mathit{Decision})`$ that is total and functional, so $`\mathit{Decision}^{\mathit{Data}}`$ is a part of the powerset (Theorem [10.1](#thm-r2-fspace-graph)).

The function space is the shape of a search problem. A schedule gives each task one slot. A selection gives each item “in” or “out”. A Latin square gives each cell one symbol. Each is one decision for each data item. Subset selection, the subject of the Rasso paper, is the case $`\mathbb {B}^{\mathit{Data}}`$, as Chapter [9](sol.md) notes (Lemma [10.3](#lem-r2-fspace-select)). An objective is then defined on every candidate, with no rule for a missing or a repeated decision.

<a id="sec-10-3"></a>
## 10.3 Why the exponential carries the algebra

<a id="sec-10-3-the-laws-of-exponents-hold"></a>
**The laws of exponents hold.**

In these laws the letters stand for any relations: $`X`$ and $`Y`$ in the place of the decision, and $`A`$, $`B`$ and $`D`$ in the place of the data. $`X^\emptyset`$ has one candidate, $`X^D`$ with $`X`$ empty and $`D`$ not empty has none, and $`1^D`$ has one. The sum law $`X^{A + B} \cong X^A \times X^B`$ holds for disjoint data. The product law $`(X \times Y)^D \cong X^D \times Y^D`$ holds (Theorem [10.2](#thm-r2-fspace-exp), Lemma [10.4](#lem-r2-fspace-prod)). This is why $`\omega _\mathrm{sol}(\mathit{Data}, \mathit{Decision})`$ is written $`\mathit{Decision}^{\mathit{Data}}`$.

<a id="sec-10-3-the-product-law-fails-for-relations"></a>
**The product law fails for relations.**

A function into $`X \times Y`$ is a pair of functions, so a decision over several attributes can be made one attribute at a time and joined back with no loss. A relation cannot: with one data item and $`X = Y = \mathbb {B}`$, the relations $`\{ (\mathrm{f}, \mathrm{f}), (\mathrm{t}, \mathrm{t})\}`$ and $`\{ (\mathrm{f}, \mathrm{t}), (\mathrm{t}, \mathrm{f})\}`$ are different but have the same two projections (Lemma [10.4](#lem-r2-fspace-prod)). With equal data $`D`$, and decisions $`X`$ and $`Y`$ that share no attribute, $`\bowtie _\mathrm{sol}`$ has one slice on each side, so its candidates are the pairs of a candidate of each (Theorem [9.12](sol.md#thm-r2-join-sol), and checked on an example): the product law $`(X \times Y)^D \cong X^D \times Y^D`$. On the powerset the law fails, so the same join would lose information. Read on the function space, the lifted operators also keep the simplification the paper states for them: with equal data the join is the conjunction of the two conditions, as the paper’s $`\cap _\mathrm{sol}`$ says, where the paper’s own lifting does not give it (Chapter [2](changes.md)).

<a id="sec-10-3-the-space-is-smaller"></a>
**The space is smaller.**

With $`|\mathit{Data}| = m`$ and $`|\mathit{Decision}| = n`$ there are $`n^m`$ functions and $`2^{nm}`$ relations (Lemma [10.5](#lem-r2-fspace-size)). Totality and the functional dependency cut the space before any constraint of the problem does. NP-Spec offers function-shaped search spaces for the same reason: “the size of the search space is smaller” [[15](references.md#cadoli_2000_np.spec.executable.specification.language), § 4.1]. Each candidate has exactly $`|\mathit{Data}|`$ tuples, so in Rasso it is a finite relation even when $`\mathit{Decision}`$ is infinite; RassoLean’s evaluator lists only finite decisions.

<a id="sec-10-4"></a>
## 10.4 Nothing is lost

The powerset is itself a function space: $`\mathcal{P}(A \times X) \cong \mathbb {B}^{A \times X}`$, a relation is its characteristic function (Lemma [10.6](#lem-r2-fspace-pset)). Koch expresses the subset guess by the function guess in the same way [[42](references.md#koch_2009_compositional.query.algebra.second.order), Proposition 3.2]. In Rasso, move the attributes of $`X`$ into the data and add one decision attribute of kind `bool`. The relations $`R \subseteq A \times X`$ are then, as checked on an example, the candidates of $`\omega _\mathrm{sol}(A \bowtie X, \omega [s\ \texttt{bool}])`$. This needs $`X`$ finite, because the data is finite. A guess of a relation in existential second-order logic is such a Boolean decision (Chapter [12](eso.md)).

A multiset is a function space in the same way: a decision $`m`$ in $`0..k`$ gives the multisets over $`A`$ with multiplicity at most $`k`$, and a multiset is its multiplicity function (Lemma [10.6](#lem-r2-fspace-pset)). This is how the paper supports subset and multiset queries, by a cardinality attribute in the decision [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation), § 4.2, Remark 1].

<a id="sec-10-5"></a>
## 10.5 Traditions to explore

We have yet to explore:

- exponential objects in cartesian closed categories, where the laws of exponents are the defining structure;
- bag semantics for relational algebra, and its laws;

A solution set is one function space. The next chapter takes a product of them, so that several functions are chosen together, under conditions that relate them.

<a id="properties"></a>
## Properties

Each property is proved in Lean, unless it says it is checked on an example. Sketches of the proofs are in Section [A.7](proofs.md#sec-r2-proofs-fspace).

<a id="thm-r2-fspace-graph"></a>

**Theorem 10.1 (Candidates are graphs of total functions).** ✓

> A finite relation is a candidate of $`\omega _\mathrm{sol}(\mathit{Data}, \mathit{Decision})`$ exactly when it is the graph of a function from the tuples of $`\mathit{Data}`$ to the tuples of $`\mathit{Decision}`$. When $`\mathit{Data}`$ and $`\mathit{Decision}`$ are well formed, and RassoLean lists no tuple of $`\mathit{Decision}`$ twice, a graph determines its function on the tuples of $`\mathit{Data}`$. So each function is a candidate once, and there are $`|\mathit{Decision}|^{|\mathit{Data}|}`$ candidates.

Uses: [Definition 9.1](sol.md#def-r2-sol).<br>
Lean: [`Rasso.mem_omegaSolCandidates`](../Rasso/FSpace.lean#L534-L551), [`Rasso.length_omegaSolCandidates`](../Rasso/FSpace.lean#L553-L560), [`Rasso.graph_inj`](../Rasso/FSpace.lean#L568-L581), [`Rasso.nodup_omegaSolCandidates`](../Rasso/FSpace.lean#L615-L635).<br>
[Proof sketch](proofs.md#sketch-thm-r2-fspace-graph).

<a id="thm-r2-fspace-exp"></a>

**Theorem 10.2 (The laws of exponents on candidates).** ✓

> With no data tuple, the empty relation is the only candidate. With a data tuple and no decision tuple, there is no candidate. With one decision tuple, there is one candidate. For data $`A`$ and $`B`$ with no tuple in common, a candidate over $`A \cup B`$ is exactly a candidate over $`A`$ and a candidate over $`B`$, joined. If $`X \times Y`$ has $`|X| \cdot |Y|`$ tuples, then $`(X \times Y)^D`$ has $`|X^D| \cdot |Y^D|`$ candidates.

Uses: [Theorem 10.1](#thm-r2-fspace-graph).<br>
Lean: [`Rasso.SolLaws.omegaSolCandidates_no_rows`](../Rasso/Laws/Sol.lean#L330-L332), [`Rasso.SolLaws.omegaSolCandidates_no_picks`](../Rasso/Laws/Sol.lean#L334-L341), [`Rasso.SolLaws.length_omegaSolCandidates_one`](../Rasso/Laws/Sol.lean#L343-L346), [`Rasso.SolLaws.omegaSolCandidates_append_split`](../Rasso/Laws/Sol.lean#L371-L389), [`Rasso.SolLaws.omegaSolCandidates_append_join`](../Rasso/Laws/Sol.lean#L391-L417), [`Rasso.SolLaws.length_omegaSolCandidates_product`](../Rasso/Laws/Sol.lean#L354-L360).<br>
[Proof sketch](proofs.md#sketch-thm-r2-fspace-exp).

<a id="lem-r2-fspace-select"></a>

**Lemma 10.3 (Subset selection is a function space).** ✓

> $`\mathcal{P}(\mathit{Data}) \cong \mathbb {B}^{\mathit{Data}}`$, where RassoLean takes a subset to be its characteristic function, by definition. In Rasso, checked on an example, the candidates of $`\omega _\mathrm{sol}(\mathit{Data}, \omega [s\ \texttt{bool}])`$ are the subsets of $`\mathit{Data}`$: there are $`2^{|\mathit{Data}|}`$ of them.

Lean: [`Rasso.FunctionSpace.selectIso`](../Rasso/FunctionSpace.lean#L153-L158), [`Rasso.FunctionSpaceExamples.count`](../Rasso/FunctionSpaceExamples.lean#L36-L40).<br>
[Proof sketch](proofs.md#sketch-lem-r2-fspace-select).

<a id="lem-r2-fspace-prod"></a>

**Lemma 10.4 (The product law holds for functions and fails for relations).** ✓

> $`(X \times Y)^A \cong X^A \times Y^A`$, and $`X^{A + B} \cong X^A \times X^B`$. For relations, the map that projects a relation in $`\mathcal{P}(A \times (X \times Y))`$ onto $`\mathcal{P}(A \times X) \times \mathcal{P}(A \times Y)`$ is not injective.

Lean: [`Rasso.FunctionSpace.prodIso`](../Rasso/FunctionSpace.lean#L236-L242), [`Rasso.FunctionSpace.prod_law_fails_for_relations`](../Rasso/FunctionSpace.lean#L256-L261), [`Rasso.FunctionSpace.sumIso`](../Rasso/FunctionSpace.lean#L267-L272).<br>
[Proof sketch](proofs.md#sketch-lem-r2-fspace-prod).

<a id="lem-r2-fspace-size"></a>

**Lemma 10.5 (The function space is smaller).** ✓

> With $`|\mathit{Data}| = m`$ and $`|\mathit{Decision}| = n`$, $`n^m \le 2^{nm}`$.

Lean: [`Rasso.FunctionSpace.fspace_le_pset`](../Rasso/FunctionSpace.lean#L134-L136).<br>
[Proof sketch](proofs.md#sketch-lem-r2-fspace-size).

<a id="lem-r2-fspace-pset"></a>

**Lemma 10.6 (The powerset and multisets are function spaces).** ✓

> $`\mathcal{P}(A \times X) \cong \mathbb {B}^{A \times X}`$, where RassoLean takes a relation to be its characteristic function, by definition. A finite multiset over a listed domain is its multiplicity function: it is recovered from it, up to the order of its elements. In Rasso, $`\omega _\mathrm{sol}(A, \omega [m 0..k])`$ has the multisets over $`A`$ with multiplicity at most $`k`$ as its candidates, checked on an example.

Lean: [`Rasso.FunctionSpace.psetIso`](../Rasso/FunctionSpace.lean#L144-L151), [`Rasso.FunctionSpace.mult_ofMult`](../Rasso/FunctionSpace.lean#L216-L219), [`Rasso.FunctionSpace.ofMult_mult_perm`](../Rasso/FunctionSpace.lean#L221-L230), [`Rasso.FunctionSpaceExamples.count`](../Rasso/FunctionSpaceExamples.lean#L36-L40).<br>
[Proof sketch](proofs.md#sketch-lem-r2-fspace-pset).
