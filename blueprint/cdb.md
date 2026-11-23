<a id="chap-r2-cdb"></a>
# 8 Rasso and constraint databases

This chapter places Rasso’s unrestricted relations in the line of constraint databases. It sets out what Rasso builds on in the work of Kanellakis, Kuper and Revesz, in Van den Bussche’s treatment of queries on such relations [[74](references.md#bussche_2000_constraint.databases.queries.query.languages)], and in the constraint algebra of Goldin and Kanellakis; gives the correspondence between their constructs and Rasso’s; and, for dense order, compares the two formally.

<a id="sec-8-1"></a>
## 8.1 The line of work

Kanellakis, Kuper and Revesz represent a possibly infinite relation by a finite formula. A *generalized tuple* is a finite conjunction of constraints, and a *generalized relation* is a finite set of generalized tuples, read as their disjunction. The relation *represents* the set of points that satisfies the formula, which they call an *unrestricted relation* [[40](references.md#kanellakis_1995_constraint.query.languages), Definitions 1.3 and 1.4]. A query computes a new formula from the formulas of its operands, so the answer is again a finite formula. This is evaluation in closed form [[40](references.md#kanellakis_1995_constraint.query.languages), § 1.1]. Projection is the elimination of an existential quantifier, and whether it can be done depends on the class of constraints [[40](references.md#kanellakis_1995_constraint.query.languages), § 1.2, Example 1.9].

Goldin and Kanellakis give an algebra on generalized relations of dense-order constraints. It keeps each generalized tuple in canonical form, its tightest equivalent, so that projection is restriction [[31](references.md#goldin_1996_constraint.query.algebras)].

<a id="sec-8-2"></a>
## 8.2 The correspondence

In Rasso, *unrestricted relation* names the representation, a heading and a term; for Kanellakis, Kuper and Revesz it names the set of points that a representation stands for. Where the constraints of a class are Rasso terms, a generalized relation is a Rasso unrestricted relation of one form: a total term in disjunctive normal form over that class. Chapter [7](unrestricted.md) defines each construct. The table gives the correspondence.

| **Constraint databases** | **Rasso** | **Where** |
|---|---|---|
| generalized relation | unrestricted relation: a heading and a term | Definition [7.1](unrestricted.md#def-r2-unrel) |
| the points it represents (their unrestricted relation) | the tuples the relation holds | Definition [7.2](unrestricted.md#def-r2-unrel-meaning) |
| evaluation in closed form | $`\sigma`$, $`\bowtie`$, $`\times`$, $`\cup`$, $`\cap`$, $`-`$, $`\rho`$ build a term | Theorem [7.7](unrestricted.md#thm-r2-unrel-ops) |
| projection by quantifier elimination | $`\pi`$, by the elimination of a class | Theorem [7.9](unrestricted.md#thm-r2-unrel-pi) |
| the class of constraints | a class, recognised for each removed attribute | Definition [7.5](unrestricted.md#def-r2-unrel-pi) |
| closure of the class | closure of each of four classes | Theorems [7.10](unrestricted.md#thm-r2-finite-class) to [7.13](unrestricted.md#thm-r2-lin-class) |

The four classes are finite domains, dense order over the rationals, equality over an infinite domain, and linear arithmetic over the rationals. Their eliminations are classical. The dense-order elimination is Fourier’s method for order constraints [[62](references.md#schrijver_1986_theory.linear.and.integer.programming)]. Quantifier elimination for dense linear order without endpoints is due to Langford [[45](references.md#langford_1926_some.theorems.on.deducibility)]. Kanellakis, Kuper and Revesz eliminate quantifiers for dense order through r-configurations [[40](references.md#kanellakis_1995_constraint.query.languages), § 3]; Goldin and Kanellakis keep tuples in canonical form, where projection is restriction [[31](references.md#goldin_1996_constraint.query.algebras), § 3.3]. The equality elimination substitutes for the attribute where a conjunct equates it to a term, and otherwise drops its disequalities, which an infinite domain can always meet. These follow the cases in the proof of Lemma 4.6 of Kanellakis, Kuper and Revesz: an element equal to another or to a constant, and a fresh one. They organise the elimination by e-configurations [[40](references.md#kanellakis_1995_constraint.query.languages), § 4]. The linear elimination is Fourier–Motzkin elimination [[62](references.md#schrijver_1986_theory.linear.and.integer.programming)]. For monotone two-variable linear constraints, the algebra of Goldin and Kanellakis projects by a variant of it [[31](references.md#goldin_1996_constraint.query.algebras), § 4]. In Rasso, elimination is how $`\pi`$ is computed, not a construct of the language.

Over the integers, order constraints alone cannot state the result of a projection. A Lean example of this project shows it (`ConstraintDB.int_not_closed`).

<a id="sec-8-3"></a>
## 8.3 The dense-order case, compared formally

For dense order over $`\mathbb {Q}`$ the correspondence is a theorem. Translate a generalized relation into an unrestricted relation whose term is a disjunction of conjunctions of comparisons. Then the translation is faithful, it is in Rasso’s dense-order class, every relation of that class is a translation up to the tuples it holds, and Rasso’s $`\pi`$ holds the same tuples as projection on generalized relations, the elimination of an existential quantifier (Theorem [8.1](#thm-r2-cdb-dense)). The two projections hold the same tuples, and can write different terms.

<a id="sec-8-4"></a>
## 8.4 Traditions to explore

Rasso has more to draw from this field:

- the rest of the work of Kanellakis, Kuper and Revesz: Datalog with constraints, and the data complexity of constraint query languages for each class of constraints [[40](references.md#kanellakis_1995_constraint.query.languages)];
- the whole constraint algebra of Goldin and Kanellakis, of which this chapter uses the dense-order projection [[31](references.md#goldin_1996_constraint.query.algebras)];
- the equality constraints of Kanellakis, Kuper and Revesz, and linear constraints, compared formally with Rasso’s equality and linear classes, as dense order is in Theorem [8.1](#thm-r2-cdb-dense);
- the later development of the field, including safe query languages for constraint databases [[44](references.md#kuper_2000_constraint.databases), ch. 5];
- the expressive power of constraint query languages [[7](references.md#benedikt_1998_relational.expressive.power.constraint.query)];
- constraint database implementations such as MLPQ, DISCO and PReSTO, and MLPQ’s linear-programming operator, set against $`\mathcal{E}`$ with a key [[59](references.md#revesz_2010_introduction.databases.biological.spatio.temporal)].

An unrestricted relation can be the codomain of a function. The next chapter takes, for a finite relation $`\mathit{Data}`$ and an unrestricted relation $`\mathit{Decision}`$, the function space $`\mathit{Decision}^{\mathit{Data}}`$: every function from the tuples of $`\mathit{Data}`$ to the tuples of $`\mathit{Decision}`$, each held as its graph, which is again a finite relation. Chapter [11](msol.md) takes a product of such function spaces, so that several functions are chosen together, under conditions that relate them.

<a id="properties"></a>
## Properties

The property is proved in Lean, in the module `ConstraintDB.RassoEmbedding` of this project’s ConstraintDB library, which formalises the generalized relations of dense order, and projection on them by eliminating one variable at a time. A sketch of the proof is in Section [A.5](proofs.md#sec-r2-proofs-cdb).

<a id="thm-r2-cdb-dense"></a>

**Theorem 8.1 (Dense order: generalized relations and the dense-order class).** ✓

> Let $`h`$ be a heading of `rat` attributes with distinct names. Let $`r`$ be a generalized relation of dense-order constraints over $`\mathbb {Q}`$ whose variables are attributes of $`h`$. Let $`T_h(r)`$ be the unrestricted relation with heading $`h`$ whose term is the disjunction, over the generalized tuples of $`r`$, of the conjunction of their comparisons.
>
> 1. *Faithful.* On a tuple $`t`$ that fits $`h`$, $`T_h(r)`$ holds $`t`$ exactly when the values of $`t`$ satisfy $`r`$ (`ConstraintDB.ToRasso.toUnrel_holds`, `ConstraintDB.ToRasso.sat_iff_holds_tupleOf`).
> 2. *In the class.* $`T_h(r)`$ is in the dense-order class, so $`\pi`$ does not refuse it (`ConstraintDB.ToRasso.toUnrel_dense`).
> 3. *The image.* Every relation $`U`$ in the dense-order class holds the same tuples as $`T_{H_U}(r)`$ for some $`r`$ (`ConstraintDB.ToRasso.image`).
> 4. *Projection agrees.* For a list $`A`$ of attributes of $`h`$, none twice, $`\pi [A](T_h(r))`$ does not refuse. It holds a tuple $`t`$ exactly when $`t`$ fits its heading and the values of $`t`$ satisfy the elimination of the other attributes of $`h`$ from $`r`$ (`ConstraintDB.ToRasso.projection_agrees`).

Uses: [Definition 7.2](unrestricted.md#def-r2-unrel-meaning), [Definition 7.5](unrestricted.md#def-r2-unrel-pi), [Theorem 7.9](unrestricted.md#thm-r2-unrel-pi), [Theorem 7.11](unrestricted.md#thm-r2-dense-class).<br>
Lean: [`ConstraintDB.ToRasso.toUnrel_holds`](../ConstraintDB/RassoEmbedding.lean#L134-L139), [`ConstraintDB.ToRasso.sat_iff_holds_tupleOf`](../ConstraintDB/RassoEmbedding.lean#L238-L247), [`ConstraintDB.ToRasso.toUnrel_dense`](../ConstraintDB/RassoEmbedding.lean#L169-L180), [`ConstraintDB.ToRasso.image`](../ConstraintDB/RassoEmbedding.lean#L653-L665), [`ConstraintDB.ToRasso.projection_agrees`](../ConstraintDB/RassoEmbedding.lean#L290-L333).<br>
[Proof sketch](proofs.md#sketch-thm-r2-cdb-dense).
