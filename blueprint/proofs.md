<a id="chap-r2-proofs"></a>
# A Proof sketches

The chapters state their properties without proofs. This appendix holds the prose arguments: for a property proved in Lean, a sketch of the Lean proof; for a property not proved in Lean, the argument that the text relies on. Each sketch is under the section of its chapter, and links back to the property it is for.

The Lean proofs and these sketches were developed with Claude (Anthropic). Lean checks each proof against its statement; it does not check the sketches, which are prose. The proofs, the sketches, and whether the statements say what we intend are being investigated, and we welcome readers’ checks.

<a id="sec-r2-proofs-values"></a>
## A.1 Values and domains

<a id="sketch-thm-r2-value-ofrat"></a>

**Sketch for Theorem [4.5](values.md#thm-r2-value-ofrat).**

The value of $`q`$ is an integer when the denominator of $`q`$ is $`1`$, and a non-integer rational otherwise. In both cases its exact number is $`q`$, so two rationals with the same value are equal.

<a id="sketch-thm-r2-value-orders"></a>

**Sketch for Theorem [4.6](values.md#thm-r2-value-orders).**

The order on values compares lexicographically: the rank of the kind, then the number, then the characters. Each part is a total preorder, so the lexicographic order is one. The canonical order breaks ties by a key that is injective on values, so two values that it ties are equal.

<a id="sketch-thm-r2-domain-unmixed"></a>

**Sketch for Theorem [4.7](values.md#thm-r2-domain-unmixed).**

By cases on the domain and the two values: a kind holds values of one kind only, and a range holds integers only. For a finite set, the check made when it is written excludes the mix. On values of an unmixed domain, `=` never meets a float and an exact number, nor a symbol and a string, and so it never refuses.

<a id="sketch-thm-r2-domain-inter"></a>

**Sketch for Theorem [4.8](values.md#thm-r2-domain-inter).**

By cases on the two domains, following the definition of the intersection: equal domains; two ranges; a range or `int` with a kind that holds it; or a finite domain, filtered by the other.

<a id="sec-r2-proofs-tuples"></a>
## A.2 Headings, tuples and terms

<a id="sketch-thm-r2-tuple-ext"></a>

**Sketch for Theorem [5.4](tuples.md#thm-r2-tuple-ext).**

Lean holds a tuple as a list of pairs sorted by attribute, with no attribute twice. By induction on the two lists: two sorted lists that give each attribute the same value have the same first pair, and the same rest.

<a id="sketch-thm-r2-tuple-order"></a>

**Sketch for Theorem [5.5](tuples.md#thm-r2-tuple-order).**

Tuples are compared attribute by attribute, each value in the canonical order. A lexicographic order of total orders is a total order.

<a id="sec-r2-proofs-finite"></a>
## A.3 Finite relations

<a id="sketch-thm-r2-built"></a>

**Sketch for Theorem [6.10](finite.md#thm-r2-built).**

Two relations with the same heading and the same tuples are equal, because a body is a set. Each equation of adjoin then follows from the tuples of the two sides. A built relation has only tuples that fit, by induction on how it was built. For the converse, a relation is its heading with the tuples of its canonical list adjoined one by one, and each of them fits.

<a id="sketch-thm-r2-finrel-induction"></a>

**Sketch for Theorem [6.11](finite.md#thm-r2-finrel-induction).**

By induction on the canonical list, which has no tuple twice.

<a id="sketch-thm-r2-canon"></a>

**Sketch for Theorem [6.12](finite.md#thm-r2-canon).**

Removing repeats from two lists with the same elements gives two lists that are permutations of each other. Sorting two permutations by a total order gives the same list, because the order on tuples is antisymmetric (Theorem [5.5](tuples.md#thm-r2-tuple-order)).

<a id="sketch-thm-r2-finrel-closed"></a>

**Sketch for Theorem [6.13](finite.md#thm-r2-finrel-closed).**

One lemma for each operator: the heading of the result names no attribute twice, and each tuple of the result fits it. $`\times`$ is $`\bowtie`$ after a check of the headings.

<a id="sec-r2-proofs-unrestricted"></a>
## A.4 Unrestricted relations

<a id="sketch-thm-r2-unrel-ops"></a>

**Sketch for Theorem [7.7](unrestricted.md#thm-r2-unrel-ops).**

Rasso’s `∧`, `∨` and `¬` evaluate every operand, and refuse when one refuses. So $`\wedge`$ is true exactly when both operands are true, with no condition. $`\vee`$ and $`\neg`$ need the operands not to refuse, which is totality. For $`\bowtie`$, a well-formed term reads only its own heading, so it has the same value on $`t`$ and on the restriction of $`t`$. A shared attribute’s domain is the intersection of two domains, so a value in it is in each of them (`Rasso.Domain.inter_complete`). For $`\rho`$, the check makes the renaming one-to-one on the heading, so a renamed term on a renamed tuple has the value of the term on the tuple, and each tuple over the renamed heading is a renamed tuple.

<a id="sketch-thm-r2-lift"></a>

**Sketch for Theorem [7.8](unrestricted.md#thm-r2-lift).**

Each test $`a = t(a)`$ compares two values of the domain of $`a`$. No domain holds both a float and an exact number, nor both a symbol and a string (Lean states this as a hypothesis, which the form check guarantees), so the test does not refuse, and it is true exactly when the values are equal. Two tuples that fit one heading and agree on every attribute are equal.

<a id="sketch-thm-r2-unrel-pi"></a>

**Sketch for Theorem [7.9](unrestricted.md#thm-r2-unrel-pi).**

A term with a value $`v`$ in place of $`a`$ has, on $`t`$, the value the term has on $`t`$ with $`a`$ set to $`v`$ (`Rasso.Term.eval_subst`). So the finite class’s disjunction is true exactly when some value of the domain makes $`\chi _U`$ true. Totality makes each disjunct give a Boolean. Removing the attributes one at a time keeps well-formedness and totality, and each removal keeps the meaning, so the whole removal does too. Agreement holds because the recogniser returns the first class, in a fixed order, whose condition holds.

For the dense-order class: on exact numbers, Rasso’s comparisons are the order of $`\mathbb {Q}`$, and they never refuse. So the normal form has the truth value of $`\chi _U`$ for every rational value of $`a`$. In a conjunction with $`a = \tau`$, the value must be $`\tau`$. Otherwise, if each lower bound is below each upper bound, a rational lies between all of them, because $`\mathbb {Q}`$ is dense and has no endpoints (the midpoint of two bounds, or a bound plus or minus one). The converse is transitivity.

For the equality class: on values of one of these domains, $`=`$ is equality of values, and it never refuses. In a conjunction with $`a = \tau`$, the value must be $`\tau`$, which lies in the domain of $`a`$. Otherwise the conjunction excludes finitely many values, and the domain is infinite, so a value outside them exists (one longer than every string named, or one more than every integer named, `Rasso.Equality.fresh`).

For the linear class: a linear term evaluates, on exact numbers, to the value of its linear form, and never refuses (`Rasso.Lin.ofTerm?_eval`); arithmetic on exact numbers is arithmetic on $`\mathbb {Q}`$, because the cast from the integers commutes with $`+`$, $`-`$ and $`\times`$. A form is its coefficient of $`a`$ times $`a`$, plus the rest (`Rasso.Lin.eval_split`). So a comparison is its row, and with $`c \neq 0`$ the row is its bound (`Rasso.Linear.test_row`). The bounds written as terms evaluate to their values (`Rasso.Lin.render_eval`), and the dense-order argument for one conjunction applies to them unchanged.

The three proofs are instances of one theorem about the shared normal form (`Rasso.NF.elim_sound`): if a class’s comparisons have normal forms that mean them, and its step on one conjunction is right, the class is sound.

<a id="sketch-thm-r2-finite-class"></a>

**Sketch for Theorem [7.10](unrestricted.md#thm-r2-finite-class).**

Each operator keeps well-formedness and totality (Theorem [7.7](unrestricted.md#thm-r2-unrel-ops) and Theorem [7.9](unrestricted.md#thm-r2-unrel-pi)). A heading of the result has domains of the operands, or, for a shared attribute of $`\bowtie`$, an intersection of two domains. An intersection with a finite domain is finite.

<a id="sketch-thm-r2-dense-class"></a>

**Sketch for Theorem [7.11](unrestricted.md#thm-r2-dense-class).**

A comparison of two exact numbers never refuses, so such a term always gives a Boolean. The operators combine the terms with $`\wedge`$, $`\vee`$ and $`\neg`$, and rename attributes. The intersection of two `rat` domains is the `rat` domain. The dense-order class accepts every attribute of such a relation, and its new term has the same shape.

<a id="sketch-thm-r2-eq-class"></a>

**Sketch for Theorem [7.12](unrestricted.md#thm-r2-eq-class).**

As for the dense-order class. Neither the finite class nor the dense-order class accepts an attribute of the $`k`$ kind, so $`\pi`$ uses the equality class, whose new term has the same shape. Over `rat`, the dense-order class comes first and accepts these terms; such a relation is in the dense-order class.

<a id="sketch-thm-r2-lin-class"></a>

**Sketch for Theorem [7.13](unrestricted.md#thm-r2-lin-class).**

In a heading of `rat` attributes a linear term reads as a linear form (`Rasso.LinTerm.read`), so it evaluates to an exact number, and such a term always gives a Boolean. The operators combine terms with $`\wedge`$, $`\vee`$ and $`\neg`$, and renaming keeps a term linear. For $`\pi`$: the finite and equality classes do not accept a `rat` attribute; the dense-order class accepts when the term is order-only on it, and otherwise the linear class accepts. Both new terms have the shape: dense order keeps the parts it does not change and writes comparisons of the old operands, and the linear class writes comparisons of linear forms written as terms.

<a id="sec-r2-proofs-cdb"></a>
## A.5 Rasso and constraint databases

The proofs are in `ConstraintDB/RassoEmbedding.lean`, in the `ConstraintDB.ToRasso` namespace. The library `ConstraintDB` formalises, in the `ConstraintDB` namespace, the generalized relations of Kanellakis, Kuper and Revesz over a dense order, with the comparisons $`{\lt}`$, $`\le`$ and $`=`$, which express their others, and projection on them by eliminating one variable at a time (`ConstraintDB.GRel.elimAll`). The module imports Rasso; Rasso does not import it. A *valuation* gives each variable a rational. A generalized relation $`r`$ holds at a valuation $`v`$ when some generalized tuple of $`r`$ has all its constraints true at $`v`$. For a tuple $`t`$, $`v_t`$ is the valuation that reads the value of each attribute from $`t`$.

<a id="sketch-thm-r2-cdb-dense"></a>

**Sketch for Theorem [8.1](cdb.md#thm-r2-cdb-dense).**

*The translation.* A variable becomes the attribute of the same name, and a constant becomes an exact number. A constraint $`x {\lt} y`$, $`x \le y`$ or $`x = y`$ becomes the Rasso comparison of the two operands. A generalized tuple becomes the conjunction of its comparisons, and the relation the disjunction of its tuples (`ConstraintDB.ToRasso.toUnrel`).

*Faithful.* On a tuple that fits $`h`$, each attribute holds an exact number. On exact numbers, Rasso’s comparisons are the order of $`\mathbb {Q}`$, and they do not refuse. So each comparison is true exactly when its constraint holds at $`v_t`$, and `∧` and `∨` are true exactly when all, or some, of their operands are. The converse starts from a valuation $`v`$, and takes the tuple of $`v`$’s values on $`h`$. Whether $`r`$ holds depends only on the variables it mentions (`ConstraintDB.GRel.sat_congr`), and these are attributes of $`h`$.

*In the class.* The term is built from `∧`, `∨` and comparisons of attributes and exact numbers, and its heading has `rat` attributes with distinct names. So the relation is well formed and in the dense-order class, and $`\pi`$ does not refuse it (Theorem [7.11](unrestricted.md#thm-r2-dense-class)).

*The image.* A term of the dense-order class is put into disjunctive normal form (`ConstraintDB.ToRasso.ofDense`): `∧` becomes the intersection of generalized relations, `∨` their union, and `¬` the complement. On a dense order, the complement of a constraint is a disjunction of constraints ($`\neg (x {\lt} y)`$ is $`y \le x`$, and $`\neg (x = y)`$ is $`x {\lt} y \vee y {\lt} x`$), so the complement of a generalized relation is again one. A comparison with $`{\gt}`$ or $`\ge`$ is written with its operands swapped. Each step keeps the truth value at every $`v_t`$ (`ConstraintDB.ToRasso.ofDense_sat`). So $`U`$ and the translation of its normal form hold the same tuples. Their terms differ: Rasso does not ask for the normal form.

*Projection agrees.* By the part *In the class*, Theorem [7.11](unrestricted.md#thm-r2-dense-class) and Theorem [7.9](unrestricted.md#thm-r2-unrel-pi), $`\pi [A](T_h(r))`$ gives a result, and it holds $`t`$ exactly when $`t`$ fits the new heading and $`T_h(r)`$ holds some tuple $`s`$ whose restriction to $`A`$ is $`t`$. The ConstraintDB library proves that its elimination of a list of variables $`Z`$ holds at $`v`$ exactly when $`r`$ holds at some valuation that agrees with $`v`$ outside $`Z`$ (`ConstraintDB.GRel.sat_elimAll`, `ConstraintDB.ToRasso.existsAll_iff_agree`). Take $`Z`$ to be the attributes of $`h`$ that are not in $`A`$. From $`s`$, the valuation $`v_s`$ agrees with $`v_t`$ outside $`Z`$, and faithfulness gives that $`r`$ holds at it. In the other direction, a valuation $`w`$ that agrees with $`v_t`$ outside $`Z`$ and satisfies $`r`$ gives the tuple over $`h`$ with the values of $`t`$ on $`A`$ and those of $`w`$ elsewhere. Faithfulness shows that $`T_h(r)`$ holds it, and its restriction to $`A`$ is $`t`$. The two eliminations can write different terms. The library’s elimination removes one variable at a time from the normal form; it does not use the canonical form of Goldin and Kanellakis.

<a id="sec-r2-proofs-sol"></a>
## A.6 Solution sets

<a id="sketch-thm-r2-sol-meaning"></a>

**Sketch for Theorem [9.10](sol.md#thm-r2-sol-meaning).**

$`\omega _\mathrm{sol}`$ lists the graphs of the functions from the data’s tuples to the decision tuples (Theorem [10.1](fspace.md#thm-r2-fspace-graph)). Each $`\sigma _\mathrm{sol}`$ filters the list by its condition, so a candidate is kept exactly when it was there before and the condition is true of it. By induction on the number of conditions.

<a id="sketch-thm-r2-sol-order"></a>

**Sketch for Theorem [9.11](sol.md#thm-r2-sol-order).**

Filtering by a condition that may refuse is a monadic filter. On two lists with the same members it meets the same members, so it refuses on both or neither, and otherwise keeps the same members.

<a id="sketch-thm-r2-join-sol"></a>

**Sketch for Theorem [9.12](sol.md#thm-r2-join-sol).**

The evaluator first checks that no data attribute of one side is decided by the other, then joins the data and the decision headings, and checks that each group of the joined data holds all of each side’s data. It then builds the candidates: for each choice of a candidate of $`U`$ for every group along $`G_U`$, it takes, for every group along $`G_V`$, the candidates of $`V`$ that agree with that choice there, and glues them. Soundness: each glued function has, along $`G_U`$, the chosen candidates of $`U`$ as its slices, and along $`G_V`$ the chosen candidates of $`V`$. Completeness: a function whose slices are candidates is glued from those slices, which are among the choices. The members keep their shape because each glued tuple is a joined data tuple with one decision tuple. Distinct choices give distinct functions, so no candidate repeats.

<a id="sketch-thm-r2-rename-sol"></a>

**Sketch for Theorem [9.13](sol.md#thm-r2-rename-sol).**

$`\rho _\mathrm{sol}`$ renames the heading, the data and each candidate with the same renaming, so it succeeds exactly when $`\rho`$ does on the heading and the data. Renaming is one-to-one on attributes, so a function on the data stays a function on the renamed data.

<a id="sec-r2-proofs-fspace"></a>
## A.7 Why function spaces

<a id="sketch-thm-r2-fspace-graph"></a>

**Sketch for Theorem [10.1](fspace.md#thm-r2-fspace-graph).**

$`\omega _\mathrm{sol}`$ builds its list data tuple by data tuple: each candidate of the shorter data is extended by each decision tuple, joined to the next data tuple. By induction on the data, a relation is in the list exactly when it is $`\{ t \cup f(t) \mid t \in B_{\mathit{Data}}\}`$ for some choice $`f`$ of one decision tuple for each data tuple. The data tuples are distinct, and under the theorem’s hypotheses so are the decision tuples, each fitting its heading, so the decision for $`t`$ is read back from the graph, and two different choices give different graphs. So the list has no repeats, and its length is the product of $`|\mathit{Decision}|`$ over the data tuples.

<a id="sketch-thm-r2-fspace-exp"></a>

**Sketch for Theorem [10.2](fspace.md#thm-r2-fspace-exp).**

With no data tuple there is one choice, the empty one. With a data tuple and no decision tuple there is none. With one decision tuple there is one. For data $`A`$ followed by $`B`$, a choice for the whole is a choice for $`A`$ followed by a choice for $`B`$. With no tuple in common, the graph splits into its part over $`A`$ and its part over $`B`$, and the two parts join back to it. For $`(X \times Y)^D`$, each data tuple has $`|X| \cdot |Y|`$ choices, by the hypothesis, and the count is the product over the data tuples.

<a id="sketch-lem-r2-fspace-select"></a>

**Sketch for Lemma [10.3](fspace.md#lem-r2-fspace-select).**

A subset of $`\mathit{Data}`$ is sent to its indicator function, and a function $`\mathit{Data}\to \mathbb {B}`$ to the set where it is true. The two maps are inverse. The count in Rasso is checked by evaluation.

<a id="sketch-lem-r2-fspace-prod"></a>

**Sketch for Lemma [10.4](fspace.md#lem-r2-fspace-prod).**

A function $`f`$ into $`X \times Y`$ is sent to its two components, and a pair of functions to the function that pairs their values; the maps are inverse. For the sum law, a function on $`A + B`$ is its restrictions to $`A`$ and to $`B`$. For relations, the two relations of the text, over one data item and $`X = Y = \mathbb {B}`$, are different and have the same projections.

<a id="sketch-lem-r2-fspace-size"></a>

**Sketch for Lemma [10.5](fspace.md#lem-r2-fspace-size).**

$`n \le 2^n`$, so $`n^m \le (2^n)^m = 2^{nm}`$.

<a id="sketch-lem-r2-fspace-pset"></a>

**Sketch for Lemma [10.6](fspace.md#lem-r2-fspace-pset).**

A relation is sent to its characteristic function, and a function into $`\mathbb {B}`$ to the pairs where it is true. The two maps are inverse. A multiset, as a list, is sent to the function that counts each element; a multiplicity function $`f`$ on a domain listed with no repeats is sent to the list with $`f(a)`$ copies of each $`a`$. Counting that list gives $`f`$ back, and the list from the counts of a multiset is a permutation of it.

<a id="sec-r2-proofs-msol"></a>
## A.8 Multi-solution sets

<a id="sketch-thm-r2-msol-cands"></a>

**Sketch for Theorem [11.4](msol.md#thm-r2-msol-cands).**

$`\omega _{\mathrm{msol}}`$ lists the choices of one candidate from each member’s list, in order: a cartesian product of lists, whose members are the databases described and whose length is the product of the lengths. A choice binds the names in order, and the names are distinct, so each name looks up its own member’s candidate.

<a id="sketch-thm-r2-msol-meaning"></a>

**Sketch for Theorem [11.5](msol.md#thm-r2-msol-meaning).**

As for solution sets (Theorem [9.10](sol.md#thm-r2-sol-meaning)): each condition filters the list of databases, and a database is kept exactly when it was there before and the condition is true of it.

<a id="sec-r2-proofs-eso"></a>
## A.9 Selection on Boolean function spaces and existential second-order logic

The proofs show, formula by formula, that $`T(\varphi )`$ evaluates to the relation of the assignments that satisfy $`\varphi`$. They use this definition and these lemmas.

<a id="def-r2-eso-rep"></a>

**Definition A.1 (A relation represents a property).** ✓

> A finite relation $`r`$ *represents* a property $`P`$ of tuples over a heading $`H`$ when $`r`$ is well formed, its heading is $`H`$, and its tuples are exactly the tuples that fit $`H`$ and satisfy $`P`$.
>
> $`r`$ represents a property $`Q`$ of assignments to the variables $`\bar x`$ when $`r`$ represents, over the heading of the attributes `x_`$`x`$ with domain $`\mathrm{DD}_A`$, the property “the assignment that the tuple gives satisfies $`Q`$”.

Uses: [Definition 6.1](finite.md#def-r2-finrel).<br>
Lean: [`Rasso.Rep`](../Rasso/Rep.lean#L31-L36), [`Rasso.ESO.RepV`](../Rasso/ESO/Meaning.lean#L25-L28), [`Rasso.ESO.Dep`](../Rasso/ESO/Meaning.lean#L21-L23).

<a id="lem-r2-eso-rep-ops"></a>

**Lemma A.2 (The operators on represented properties).** ✓

> If $`r`$ represents $`P`$ and $`s`$ represents $`P'`$, then $`\cup`$, $`-`$, $`\bowtie`$ and $`\pi`$ are not refused, under simple conditions, and, when $`\sigma`$ gives a result, the results represent: $`P`$ and the test; $`P`$ or $`P'`$; $`P`$ and not $`P'`$; $`P`$ on the left part and $`P'`$ on the right part; and “some tuple that satisfies $`P`$ restricts to this one”.

Uses: [Definition A.1](#def-r2-eso-rep), [Definition 6.4](finite.md#def-r2-spr), [Definition 6.5](finite.md#def-r2-join), [Definition 6.6](finite.md#def-r2-setops).<br>
Lean: [`Rasso.rep_select`](../Rasso/Rep.lean#L59-L66), [`Rasso.rep_union`](../Rasso/Rep.lean#L108-L121), [`Rasso.rep_diff`](../Rasso/Rep.lean#L123-L132), [`Rasso.rep_join`](../Rasso/Rep.lean#L221-L347), [`Rasso.rep_project`](../Rasso/Rep.lean#L392-L426).<br>
[Proof sketch](#sketch-lem-r2-eso-rep-ops).

<a id="sketch-lem-r2-eso-rep-ops"></a>

**Sketch for Lemma [A.2](#lem-r2-eso-rep-ops).**

From the membership lemmas of each operator (Chapter [6](finite.md)). Union and difference need the same heading, and join needs the same domain on each shared attribute. Here every attribute has the domain $`\mathrm{DD}_A`$, so these always hold.

<a id="lem-r2-eso-repv-ops"></a>

**Lemma A.3 (Assignments: join, union, difference, equality, quantifiers).** ✓

> Let the universe be unmixed. On relations of assignments: $`\bowtie`$ is “and”, $`\cup`$ is “or”, $`-`$ is “and not”, $`\sigma _{x\_ x = x\_ y}`$ adds $`\rho (x) = \rho (y)`$, $`U^{\bar x}`$ represents “true”, and the projection that drops `x_`$`x`$ represents “for some element $`a`$ of the universe, $`Q`$ holds with $`x`$ set to $`a`$”.

Uses: [Lemma A.2](#lem-r2-eso-rep-ops).<br>
Lean: [`Rasso.ESO.repV_join`](../Rasso/ESO/Meaning.lean#L95-L110), [`Rasso.ESO.repV_union`](../Rasso/ESO/Meaning.lean#L112-L115), [`Rasso.ESO.repV_diff`](../Rasso/ESO/Meaning.lean#L117-L120), [`Rasso.ESO.repV_select_eq`](../Rasso/ESO/Meaning.lean#L135-L150), [`Rasso.ESO.repV_domOf`](../Rasso/ESO/Meaning.lean#L152-L154), [`Rasso.ESO.repV_pad`](../Rasso/ESO/Meaning.lean#L289-L302), [`Rasso.ESO.repV_exists`](../Rasso/ESO/Meaning.lean#L196-L243).<br>
[Proof sketch](#sketch-lem-r2-eso-repv-ops).

<a id="sketch-lem-r2-eso-repv-ops"></a>

**Sketch for Lemma [A.3](#lem-r2-eso-repv-ops).**

From Lemma [A.2](#lem-r2-eso-rep-ops). For the projection, a tuple without `x_`$`x`$ extends to a tuple with it by adding the pair (`x_`$`x`$, $`a`$). The lemmas for join, padding and projection need $`Q`$ and $`Q'`$ to depend only on their own variables.

<a id="lem-r2-eso-atoms"></a>

**Lemma A.4 (Atoms).** ✓

> Let $`A`$ be well formed, with an unmixed universe, and let the guess $`G`$ fit the arities. $`T(i(\bar x))`$ represents the assignments $`\rho`$ with $`\rho (\bar x) \in A(i)`$, and, under a guess $`G`$ written into the members, $`T(R(\bar x))`$ represents the assignments with $`\rho (\bar x) \in G(R)`$.

Uses: [Lemma A.2](#lem-r2-eso-rep-ops), [Definition 12.4](eso.md#def-r2-eso-compile).<br>
Lean: [`Rasso.ESO.meaning_atom`](../Rasso/ESO/Meaning.lean#L414-L580), [`Rasso.ESO.meaning_rel`](../Rasso/ESO/Meaning.lean#L656-L668), [`Rasso.ESO.meaning_gvar`](../Rasso/ESO/Meaning.lean#L670-L716).<br>
[Proof sketch](#sketch-lem-r2-eso-atoms).

<a id="sketch-lem-r2-eso-atoms"></a>

**Sketch for Lemma [A.4](#lem-r2-eso-atoms).**

One general lemma covers both atoms: the base relation (the data, or the member), joined with $`U^{\bar x}`$, the tests, and the projection. For a tuple $`t`$ of the result, take a tuple $`u`$ of the join that restricts to $`t`$. The tests say that the columns of $`u`$ are $`\rho (\bar x)`$. Conversely, from $`\rho (\bar x)`$ in the data, build $`u`$ from the data tuple and $`t`$. Their attributes are different: `c`$`k`$, `holds` and `x_`$`x`$ start with different letters.

<a id="sketch-thm-r2-eso-codd"></a>

**Sketch for Theorem [12.10](eso.md#thm-r2-eso-codd).**

By induction on $`\varphi`$, one case for each line of Definition [12.4](eso.md#def-r2-eso-compile), with Lemmas [A.3](#lem-r2-eso-repv-ops) and [A.4](#lem-r2-eso-atoms). In the case $`\forall x\, \varphi`$, the result represents “not for some $`a`$, not $`\varphi`$”, which is “for all $`a`$, $`\varphi`$”. The condition: $`\varphi`$ has no free variables, so $`T(\varphi )`$ has no attributes. It holds the empty tuple exactly when $`\varphi`$ holds, and $`\gamma`$ with `bool_or` of `true` gives `true` exactly when the relation has a tuple.

<a id="lem-r2-eso-guesses"></a>

**Lemma A.5 (The candidates are the fitting guesses).** ✓

> Let $`c`$ be a condition whose value, when the members are the guess $`G`$, is a Boolean that depends only on $`G`$. Then the multi-solution set with the members of Definition [12.5](eso.md#def-r2-eso-form) and the condition $`c`$ is not refused. It has a candidate exactly when some guess that fits the arities makes $`c`$ true.

Uses: [Definition 12.5](eso.md#def-r2-eso-form), [Definition 11.1](msol.md#def-r2-msol).<br>
Lean: [`Rasso.ESO.GuessEnv`](../Rasso/ESO/Guesses.lean#L37-L41), [`Rasso.ESO.eval_esoMsol`](../Rasso/ESO/Guesses.lean#L594-L656).<br>
[Proof sketch](#sketch-lem-r2-eso-guesses).

<a id="sketch-lem-r2-eso-guesses"></a>

**Sketch for Lemma [A.5](#lem-r2-eso-guesses).**

A candidate of $`\omega _\mathrm{sol}(U^k, \omega [\texttt{holds}\ \texttt{bool}])`$ is the graph of a function from the $`k`$-tuples of the universe to `bool` (Theorem [9.10](sol.md#thm-r2-sol-meaning)). The tuples with `holds` true are a guess that fits arity $`k`$. Each fitting guess comes from one such function.

<a id="sketch-thm-r2-eso-forward"></a>

**Sketch for Theorem [12.11](eso.md#thm-r2-eso-forward).**

Lemma [A.5](#lem-r2-eso-guesses), with the condition of Theorem [12.10](eso.md#thm-r2-eso-codd).

<a id="sketch-thm-r2-eso-program"></a>

**Sketch for Theorem [12.12](eso.md#thm-r2-eso-program).**

Each data statement is a literal, so its value does not depend on the statements before it. Each form in `eso` has a value that depends only on the values of its parts. Where `eso` reads `univ` or `rel_`$`i`$`_`$`n`$, the environment gives the value of the literal; the names are all different, and none is the name of a member. So `eso` has the value of the multi-solution set of Definition [12.5](eso.md#def-r2-eso-form). Then apply Theorem [12.11](eso.md#thm-r2-eso-forward).

<a id="sketch-thm-r2-eso-converse"></a>

**Sketch for Theorem [12.13](eso.md#thm-r2-eso-converse).**

Read the sentence off the query, the other half of Codd’s theorem: $`\bowtie`$ is $`\wedge`$, $`\cup`$ is $`\vee`$, $`-`$ is “and not”, the complement is $`\neg`$, $`\pi`$ over a variable of the relation is $`\exists`$, and $`\pi`$ over any other variable leaves the formula as it is, and “has a tuple” is $`\exists`$ over the remaining variables. By induction on the relation, each one represents the assignments that satisfy its formula (the atoms by Lemma [A.4](#lem-r2-eso-atoms)). Then apply Lemma [A.5](#lem-r2-eso-guesses).

<a id="sketch-thm-r2-eso-boolsel-decide"></a>

**Sketch for Theorem [12.14](eso.md#thm-r2-eso-boolsel-decide).**

The procedure reads $`r`$ back as a finite list of candidate queries, one node at a time. The members give the arities. A test “has a tuple” gives a test. The atom gadgets give atoms: the names `x_`$`v`$, `rel_`$`i`$`_`$`n`$ and `member_`$`R`$ are decoded. The operators $`\bowtie`$, $`\cup`$, $`-`$ and $`\pi`$ give the operators. Then the procedure keeps a candidate $`Q`$ when $`Q`$ is well formed and its statement is $`r`$. Equality of forms is decidable, so this check is a computation.

If the answer is “yes”, $`r`$ is a Boolean selection statement, by the check. For the converse, take a well formed query $`Q`$. The read-back of its statement need not contain $`Q`$ itself, because the statement forgets three things. A member that is not listed at its arity becomes the empty relation, without its name. A projection of a variable that is not there keeps every attribute, and so it loses the variable. And a difference from the universe can be a complement or a difference with the atom $`x = x`$. For the first two, the read-back offers a candidate with a fresh name. For the third, it offers both readings. By induction on $`Q`$, some candidate is well formed, has the same variables at each node, and has the same statement as $`Q`$.

<a id="sketch-thm-r2-eso-boolsel-converse"></a>

**Sketch for Theorem [12.15](eso.md#thm-r2-eso-boolsel-converse).**

Let $`r`$ be the statement of the query $`Q`$, and let $`\psi`$ be the sentence of Theorem [12.13](eso.md#thm-r2-eso-converse). In the program’s environment, the names `univ` and `rel_`$`i`$`_`$`n`$ have the values of the literals, as in the proof of Theorem [12.12](eso.md#thm-r2-eso-program). Each form in $`r`$ has a value that depends only on the values of its parts. So $`r`$ has the value of the multi-solution set of $`Q`$ with the data in place. Then apply Theorem [12.13](eso.md#thm-r2-eso-converse).

<a id="sketch-thm-r2-eso-same"></a>

**Sketch for Theorem [12.16](eso.md#thm-r2-eso-same).**

Write each formula as a relation of Definition [12.6](eso.md#def-r2-eso-query). The connectives $`\neg`$, $`\vee`$, $`\exists`$ and $`\forall`$ need care: $`-`$ and $`\cup`$ ask for both sides over the same variables, and $`\exists`$ must fail on an empty universe. Join each side with $`x = x`$ for each variable it lacks; for $`\exists x\, \varphi`$, join $`\varphi`$ with $`x = x`$ when $`x`$ is not free in $`\varphi`$, then project $`x`$ away; write $`\neg \varphi`$ as the universe minus $`\varphi`$, and $`\forall x\, \varphi`$ as $`\neg \exists x\, \neg \varphi`$. Then apply Theorems [12.13](eso.md#thm-r2-eso-converse) and [12.15](eso.md#thm-r2-eso-boolsel-converse).

<a id="sec-r2-proofs-phi"></a>
## A.10 $`\Phi`$: from solution sets to one relation

The proofs follow $`\Phi`$’s symbolic evaluation step by step. Each piece of it is first proved sound on its own: terms, $`\gamma`$ with its aggregates, extend, and join (`Rasso/Phi/Sound/`).

<a id="sketch-thm-r2-phi-square"></a>

**Sketch for Theorem [13.8](phi.md#thm-r2-phi-square).**

By induction on the chain and its conditions. On an assignment that respects the cells, each symbolic value that $`\Phi`$ computes evaluates to the value that the evaluator computes on $`\mathrm{subst}(F, x)`$: for terms, for $`\gamma`$ with each aggregate, for extend and for join, by the soundness of each piece. The term of $`F`$ is the conjunction of these, and $`\mathrm{accepts}`$ is the evaluator’s check, so the two give the same Boolean.

<a id="sketch-thm-r2-phi-no-refusal"></a>

**Sketch for Theorem [13.9](phi.md#thm-r2-phi-no-refusal).**

From Theorem [13.8](phi.md#thm-r2-phi-square): the term gives a Boolean, and $`\mathrm{accepts}`$ gives the same Boolean, so it does not refuse.

<a id="sketch-thm-r2-phi-cells"></a>

**Sketch for Theorem [13.10](phi.md#thm-r2-phi-cells).**

$`\mathrm{subst}(F, x)`$ is the graph that gives the data tuple numbered $`i`$ the values of its cells. It is a candidate of $`\omega _\mathrm{sol}(\mathit{Data}, \mathit{Decision})`$ exactly when each of these decision tuples is in $`\mathit{Decision}`$, which is the decision’s term on each copy. A candidate is read back cell by cell, which gives an exact assignment; two exact assignments that give the same graph agree on every cell.

<a id="sketch-thm-r2-phi-lift"></a>

**Sketch for Theorem [13.11](phi.md#thm-r2-phi-lift).**

The earlier statements run, so the chain’s names have their values, and statement $`k`$ evaluates level by level. Its candidates are those of $`\omega _\mathrm{sol}(\mathit{Data}, \mathit{Decision})`$ that each level’s condition keeps. Theorem [13.10](phi.md#thm-r2-phi-cells) gives the candidates of $`\omega _\mathrm{sol}`$ as substitutions, and Theorem [13.8](phi.md#thm-r2-phi-square) gives the conditions’ value on each.

<a id="sketch-thm-r2-phi-key"></a>

**Sketch for Theorem [13.12](phi.md#thm-r2-phi-key).**

As for Theorem [13.8](phi.md#thm-r2-phi-square), for the key: its symbolic value evaluates, on an assignment that respects the cells, to the value the evaluator gives the key on $`\mathrm{subst}(F, x)`$.

<a id="sketch-thm-r2-phi-msol-square"></a>

**Sketch for Theorem [13.13](phi.md#thm-r2-phi-msol-square).**

As for Theorem [13.8](phi.md#thm-r2-phi-square), member by member: each member’s symbolic candidate stands for its name in the conditions, and the term joins the members’ terms and the conditions.

<a id="sketch-thm-r2-phi-msol-lift"></a>

**Sketch for Theorem [13.14](phi.md#thm-r2-phi-msol-lift).**

As for Theorem [13.11](phi.md#thm-r2-phi-lift), with the databases of $`\omega _{\mathrm{msol}}`$ in place of the candidates of $`\omega _\mathrm{sol}`$.

<a id="sketch-thm-r2-phi-msol-cells"></a>

**Sketch for Theorem [13.15](phi.md#thm-r2-phi-msol-cells).**

The cells of different members have different names, because $`\Phi`$ refuses a statement in which two cells would share one. Two exact assignments that give the same database give the same candidate to each member, and so agree on that member’s cells (Theorem [13.10](phi.md#thm-r2-phi-cells)).

<a id="sketch-thm-r2-phi-msol-key"></a>

**Sketch for Theorem [13.16](phi.md#thm-r2-phi-msol-key).**

As for Theorem [13.12](phi.md#thm-r2-phi-key), with the key read over the members’ join.
