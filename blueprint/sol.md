<a id="chap-r2-sol"></a>
# 9 Solution sets

This chapter gives solution sets, the construct that turns the algebra into a language for search problems. A search problem has data, decisions, constraints and an objective. A solution set states the first two as relations. Conditions state the constraints, and a key on enumeration states the objective.

Informally, a solution set is the set of all total functions from a finite relation, the data, to an unrestricted relation, the decision, whose headings share no attribute. A function makes one decision for each data item. The set of all of them is the exponential $`\mathit{Decision}^{\mathit{Data}}`$, with $`|\mathit{Decision}|^{|\mathit{Data}|}`$ members. A subset of $`\mathit{Data}`$ is the special case of a decision `in` or `out`, so the power set is an exponential too: $`\mathcal{P}(\mathit{Data}) \cong \mathbb {B}^{\mathit{Data}}`$. In the terms of existential second-order logic, a solution set is a guessed function, and a guessed relation is a guessed function into the Booleans (Chapter [12](eso.md)). The algebra of the earlier chapters then works one level up: its operators act on solution sets as they act on relations.

The development of solution sets continues in Section [9.2](#sec-r2-sol-space). Before it, Section [9.1](#sec-r2-sol-prior) sets solution sets in the work they come from.

<a id="sec-r2-sol-prior"></a>
## 9.1 Prior work

Solution sets come from the Rasso paper [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation), § 4]. They stand in a long line of work on subset selection and optimisation in databases, whose evolution and contributions the paper traces [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation), § 7 and Appendix H.2]: SQLMP [[18](references.md#choobineh_1991_sqlmp.data.sublanguage.representation.formulation)]; the nested and powerset algebras [[57](references.md#paredaens_1992_converting.nested.algebra.expressions.flat), [33](references.md#gyssens_1992_powerset.algebra.natural.tool.handle)]; ESRA [[24](references.md#flener_2001_towards.relational.modelling.combinatorial.optimisation), [25](references.md#flener_2004_introducing.esra.relational.language.modelling)]; the subset algebra of Valluri and Karlapalem [[73](references.md#valluri_2004_subset.queries.in.relational.databases)]; NP-Alg and ConSQL+ [[16](references.md#cadoli_2007_relational.algebra.sql.constraint.modelling), [52](references.md#mancini_2010_local.search.over.relational.databases), [53](references.md#mancini_2012_combinatorial.problem.relational.databases.view), 52 , 53]; SCL [[66](references.md#siva_2011_enabling.relational.databases.effective.csp)]; DivDB [[75](references.md#vieira_2011_divdb)]; package queries [[23](references.md#fernandes_2014_packagebuilder.querying.for.packages.tuples), [11](references.md#brucato_2018_package.queries.efficient.scalable.computation), [14](references.md#brucato_2020_spaqltools.stochastic.package.query.interface), [49](references.md#mai_2023_scaling.package.queries.billion.tuples), 11 , 14 , 49]; SolveDB [[76](references.md#siksnys_2016_solvedb.optimization.problem.solvers.sql), [64](references.md#siksnys_2017_demonstrating.solvedb.sql.dbms.optimization), [65](references.md#siksnys_2021_solvedb.sql.based.prescriptive.analytics), 64 , 65]; CombSQL+ [[60](references.md#sakanashi_2018_transformation.combinatorial.optimization.written.sql), [61](references.md#sakanashi_2020_transformation.sql.combinatorial.optimization.constraint)]; and the relational constraint programming of Valdron and Pu [[72](references.md#valdron_2020_data.driven.relational.constraint.programming)]. Two systems that were released in 2026, after the paper was published, continue the line: DeQL [[12](references.md#brucato_2026_deql.decision.query.language.prescriptive)] and DeciDB [[48](references.md#mai_2026_decidb.database.processing.decision.queries)].

Like Rasso, NP-Alg extends relational algebra itself rather than SQL, and its expressive power is characterised: it adds guessed relations, and captures existential second-order logic, so its programs express exactly the NP properties [[16](references.md#cadoli_2007_relational.algebra.sql.constraint.modelling)], [[51](references.md#mancini_2004_declarative.constraint.modelling.specification.level), § 8.4, Theorems 8.4.1 and 8.4.3]. NP-Alg keeps the second-order quantifier as a binder: a query declares its guessed relations, Guess $`Q_1, \ldots , Q_n`$, ahead of an ordinary expression of relational algebra, and holds when some extension of them makes a relation FAIL empty [[51](references.md#mancini_2004_declarative.constraint.modelling.specification.level), § 8.2]. Biskup, Paredaens, Schwentick and Van den Bussche make the guesses a value: the set of all solutions of an equation in relational algebra is a nested relation, and enumerating it is a primitive of the nested algebra [[10](references.md#biskup_2004_solving.equations.in.relational.algebra), pp. 1052–1053]. The resulting equation algebra is equivalent to the powerset algebra [[10](references.md#biskup_2004_solving.equations.in.relational.algebra), Proposition 4.4]. Whether an equation has a solution is, by Fagin’s theorem, exactly an NP property [[10](references.md#biskup_2004_solving.equations.in.relational.algebra), § 6]. Koch’s world-set algebra adds to relational algebra an operator, repair-key, that guesses within a set of possible worlds, each a database, and captures second-order logic [[42](references.md#koch_2009_compositional.query.algebra.second.order), § 3.1, Theorems 4.1 and 4.3].

These approaches differ in the shape of a guess, and in what the algebra acts on. In NP-Alg and in the equation algebra a guess is a set of tuples, and a function is a guess with functionality and totality added by a condition: a FAIL relation, an equation. Koch’s repair-key, like the witness operator of Abiteboul and Vianu [[1](references.md#abiteboul_1995_foundations.of.databases), § 17.4], guesses a function directly, as a maximal subset on which some attributes form a key [[42](references.md#koch_2009_compositional.query.algebra.second.order), Figure 1, Example 3.1]; Koch derives the subset guess from it (Proposition 3.2). But each function is one choice, in one possible world or as one outcome, and the set of all of them is not an operand. The equation algebra does make its set of solutions a value, but the nested algebra acts on it, not Codd’s operators. The powerset algebras were studied as query languages, in which the powerset takes exponential time to evaluate [[1](references.md#abiteboul_1995_foundations.of.databases), § § 20.6–20.7]. Rasso makes the function space $`\mathit{Decision}^{\mathit{Data}}`$ itself the carrier, and lifts Codd’s operators to act on it. It states a search problem without listing its candidates. Evaluating the algebra directly, as RassoLean’s evaluator does, takes exponential time and is useful on small instances; for larger ones, the translation $`\Phi`$ lowers the problem for a constraint solver, which searches instead (Chapter [13](phi.md)). Chapter [10](fspace.md) gives our reasons.

A solution set represents a set of relations, its candidates, as a table with variables does in the representation systems of incomplete databases [[37](references.md#imielinski_1984_incomplete.information.in.relational.databases), § 3]: in the terms of Abiteboul, Kanellakis and Grahne, a set of possible worlds [[2](references.md#abiteboul_1987_representation.querying.sets.possible.worlds)].

Function spaces as decision variables are not new in constraint programming. The language F has function variables [[35](references.md#hnich_2003_function.variables.for.constraint.programming)], Essence has decision variables of function type [[26](references.md#frisch_2008_essence.constraint.language.specifying.combinatorial), [4](references.md#akgun_2022_conjure.automatic.generation.constraint.models), [27](references.md#frisch_2026_reflections.essence.constraint.language.specifying), 4 , 27], and ESRA declares relation variables, with functions as the relations whose multiplicity is exactly one (total) or at most one (partial), and states its constraints in a bounded first-order calculus [[25](references.md#flener_2004_introducing.esra.relational.language.modelling)]. LogicBlox’s LogiQL declares a functional predicate as a free second-order variable for a solver to populate, with totality as an integrity constraint and an aggregate predicate as the objective [[6](references.md#aref_2015_design.implementation.the.logicblox.system), § § 2.2, 2.3.2].

Answer set programming expresses search over functions under the stable model semantics [[30](references.md#gelfond_1988_stable.model.semantics.logic.programming)]. Clingo [[29](references.md#gebser_2018_multi.shot.asp.solving.clingo)] is a leading system that implements it.

<a id="sec-r2-sol-space"></a>
## 9.2 The space of candidates

<a id="def-r2-sol"></a>

**Definition 9.1 (Solution set).** ✓

> Let $`\mathit{Data}`$ be a finite relation, the *data*, and $`\mathit{Decision}`$ an unrestricted relation, the *decision*. They share no attribute. A *candidate* is a function $`f`$ from the tuples of $`\mathit{Data}`$ to the tuples of $`\mathit{Decision}`$. Rasso holds a candidate as its graph: the finite relation with heading $`H_{\mathit{Data}}`$ followed by $`H_{\mathit{Decision}}`$, and body $`\{ t \cup f(t) \mid t \in B_{\mathit{Data}}\}`$.
>
> $`\omega _\mathrm{sol}(\mathit{Data}, \mathit{Decision})`$ is the solution set of all candidates. It has $`|\mathit{Decision}|^{|\mathit{Data}|}`$ candidates, so we write it $`\mathit{Decision}^{\mathit{Data}}`$. A *solution set* is the data, the decision and a set of candidates.

Uses: [Definition 6.1](finite.md#def-r2-finrel), [Definition 7.1](unrestricted.md#def-r2-unrel).<br>
Lean: [`Rasso.Sol`](../Rasso/Eval.lean#L108-L112), [`Rasso.choices`](../Rasso/Eval.lean#L228-L231).

A candidate is a relation with two kinds of attribute. Its data attributes say which data item a tuple is about, and they hold the same values in every candidate. Its decision attributes say what is decided for that item. Its body has one tuple for each data tuple. In the algebra on relations, the tuple is the unit that a selection keeps or drops. In the algebra on solution sets, the candidate is that unit: a condition is tested on a whole candidate, not on one of its tuples.

In Rasso the decision may be any unrestricted relation. RassoLean’s evaluator lists the candidates one by one, so it accepts only a finite decision. It is meant for small examples. For larger problems, $`\Phi`$ (Chapter [13](phi.md)) lowers a solution set to one flat relation, which backend solvers search over the integers and the floats. Chapter [10](fspace.md) gives the reasons for a function space, and not a power set, as the space of candidates.

<a id="sec-9-3"></a>
## 9.3 Conditions

<a id="def-r2-cond"></a>

**Definition 9.2 (Condition).** ✓

> A *condition* on a solution set $`U`$ is a relational expression in which $`U`$ stands for the candidate. On a candidate $`I`$, its value is the expression’s value with $`I`$ in place of $`U`$. That value must be a finite relation with one attribute and one tuple, whose value is a Boolean. The condition is *true* of $`I`$ when that value is `true`, and it refuses $`I`$ when the expression refuses or its value has another shape.

Uses: [Definition 9.1](#def-r2-sol).<br>
Lean: [`Rasso.Cond`](../Rasso/Form.lean#L112-L118), [`Rasso.Cond.eval`](../Rasso/Eval.lean#L591-L601), [`Rasso.scalar`](../Rasso/Eval.lean#L206-L213).

Conditions combine with `∧`, `∨` and `¬`. Three forms are common:

- $`\gamma [][\mathtt{bool\_and}(b) \to \mathit{ret}](E)`$: every tuple of $`E`$ has $`b`$ true. The cakes condition below has this form.
- $`\gamma [][\mathtt{bool\_or}(b) \to \mathit{ret}](E)`$: some tuple of $`E`$ has $`b`$ true.
- $`\mathtt{has\_subset}(R)`$: the candidate holds every tuple of $`R`$.

A test that a relational expression is not empty, as `EXISTS` is in SQL, is also a function from a relation to the Booleans, and it is being added to Rasso.

<a id="sec-9-4"></a>
## 9.4 The algebra on solution sets

The operators of this section take solution sets and give a solution set.

<a id="def-r2-sigma-sol"></a>

**Definition 9.3 (Selection of candidates).** ✓

> $`\sigma _\mathrm{sol}[c](U)`$ keeps the candidates $`I`$ of $`U`$ for which the condition $`c`$ holds. Inside $`c`$, the expression $`U`$ stands for the candidate $`I`$. So $`c`$ can join the candidate with data, group it and aggregate it, as it does any finite relation.

Uses: [Definition 9.1](#def-r2-sol), [Definition 9.2](#def-r2-cond).<br>
Lean: [`Rasso.Expr.eval`](../Rasso/Eval.lean#L366-L561), [`Rasso.Cond.eval`](../Rasso/Eval.lean#L591-L601), [`Rasso.candidateName`](../Rasso/Eval.lean#L94-L96).

<a id="def-r2-join-sol"></a>

**Definition 9.4 (Join of solution sets).** ✓

> Let $`U`$ and $`V`$ be solution sets, with data $`\mathit{Data}_U`$ and $`\mathit{Data}_V`$ and decisions $`\mathit{Decision}_U`$ and $`\mathit{Decision}_V`$, and let no data attribute of one be a decision attribute of the other. $`U \bowtie _\mathrm{sol}V`$ has the data $`J = \mathit{Data}_U \bowtie \mathit{Data}_V`$ and the decision $`\mathit{Decision}_U \bowtie \mathit{Decision}_V`$. Let $`G_U`$ be the data attributes of $`V`$ that $`\mathit{Data}_U`$ does not have, and $`G_V`$ those of $`U`$ that $`\mathit{Data}_V`$ does not have. Fix a value $`g`$ of $`G_U`$ in $`J`$: the *slice* of a function $`f`$ on $`J`$ at $`g`$ is $`f`$ on the tuples of $`J`$ that agree with $`g`$, with $`G_U`$ dropped and only the decision attributes of $`U`$ kept. A function $`f`$ from the tuples of $`J`$ to the tuples of $`\mathit{Decision}_U \bowtie \mathit{Decision}_V`$ is a candidate of $`U \bowtie _\mathrm{sol}V`$ when each of its slices along $`G_U`$ is a candidate of $`U`$, and each of its slices along $`G_V`$ is a candidate of $`V`$.
>
> $`U \bowtie _\mathrm{sol}V`$ is refused when a slice would not cover the data of its side: when, for some value of $`G_U`$, the tuples of $`J`$ that agree with it do not hold every tuple of $`\mathit{Data}_U`$, and in the same way for $`V`$. The conditions of a side would otherwise be tested on part of its data.

Uses: [Definition 9.1](#def-r2-sol), [Definition 6.5](finite.md#def-r2-join).<br>
Lean: [`Rasso.Sol.join`](../Rasso/Eval.lean#L303-L345).

The slices of one candidate can differ. In the Latin square below, each row of a square and each column of it is a Latin vector, and the rows are not all the same vector.

This join is not the join of Chapter [6](finite.md) applied to candidates. That join is still there, one level down: inside a condition, the candidate joined with a relation is an ordinary join of finite relations, tuple by tuple, as in the cakes problem below. Joined that way, two candidates give the tuples $`t_1 \cup t_2 \cup f_1(t_1) \cup f_2(t_2)`$ only where $`f_1(t_1)`$ and $`f_2(t_2)`$ agree, and the result need not be a candidate of anything. Read as an operator on solution sets, such a pointwise join would pair one candidate of each side, and a shared decision attribute would then have to take one value across the other side’s data: the join of a row space and a column space would hold no Latin square. $`\bowtie _\mathrm{sol}`$ is the other reading, one level up: the paper’s lifting of each side’s condition to the joined data [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation), Appendix E.2], with the slices grouped by the data attributes the other side adds (Chapter [2](changes.md)). Choosing one candidate from each of several solution sets, together and under conditions that relate them, is what multi-solution sets do (Chapter [11](msol.md)).

<a id="def-r2-rename-sol"></a>

**Definition 9.5 (Renaming of a solution set).** ✓

> $`\rho _\mathrm{sol}[a \to b](U)`$ renames the attribute $`a`$ to $`b`$ in the data, in the heading and in every candidate of $`U`$. It is refused where $`\rho`$ on the heading of $`U`$ is refused: when $`a`$ is not an attribute of $`U`$, or when two attributes would get one name.

Uses: [Definition 9.1](#def-r2-sol), [Definition 6.4](finite.md#def-r2-spr).<br>
Lean: [`Rasso.Sol.rename`](../Rasso/Eval.lean#L243-L251).

The paper’s $`\times _\mathrm{sol}`$ is $`\bowtie _\mathrm{sol}`$ on operands that share no attribute, and Rasso writes it so. The paper’s $`\cap _\mathrm{sol}`$, $`-_\mathrm{sol}`$ and $`\cup _\mathrm{sol}`$ are not yet in either implementation (Chapter [2](changes.md)).

<a id="sec-9-5"></a>
## 9.5 Enumeration of candidates

<a id="def-r2-enum-sol"></a>

**Definition 9.6 (Enumeration of a solution set).** ✓

> $`\mathcal{E}_\mathrm{sol}[k, d, e](U)`$ is the sequence of at most $`k`$ candidates of $`U`$, in the order of their keys. The key $`e`$ is a relational expression in which $`U`$ stands for the candidate, as in a condition. Its value must have one attribute and one tuple, and that value is the key. With no key, $`\mathcal{E}_\mathrm{sol}[k](U)`$ gives $`k`$ candidates.

Uses: [Definition 9.3](#def-r2-sigma-sol), [Definition 6.9](finite.md#def-r2-enum).<br>
Lean: [`Rasso.sortTake`](../Rasso/Eval.lean#L223-L226).

The result is a sequence of candidates. With $`d = \texttt{desc}`$ and $`k = 1`$, the expression states the optimisation problem $`\max f(x)`$ subject to $`C(x)`$, with $`x`$ a candidate, $`C`$ the conditions and $`f`$ the key. Rasso states the problem; how an implementation finds the answer is outside the algebra.

<a id="def-r2-flatten"></a>

**Definition 9.7 (Flattening).** ✓

> $`\mathrm{flatten}[r](S)`$ makes a sequence of candidates one sequence of tuples: the tuples of the first candidate, then those of the second, and so on. Each tuple gets the attribute $`r`$, an integer, with its candidate’s place in $`S`$, counted from $`1`$. The tuples of one candidate are in ascending order of their values, compared attribute by attribute in the order of the heading. So two headings with the same attributes in a different order can give the same tuples in a different order. $`\mathrm{flatten}[](S)`$ has no rank attribute, and $`S`$ must have at most one candidate.

Uses: [Definition 9.6](#def-r2-enum-sol).<br>
Lean: [`Rasso.Expr.eval`](../Rasso/Eval.lean#L366-L561).

The answer to the search problem is then a finite relation again. The algebra of Chapter [6](finite.md) applies to it.

<a id="sec-9-6"></a>
## 9.6 In $`\rho \alpha`$ and RassoLean terms

A join and a renaming of solution sets are written as on relations, `⋈` and `ρ`, and the operands decide which is meant. With these forms the cakes problem is complete.

<a id="ex-r2-cakes"></a>

**Example 9.8 (Cakes production).**

> Choose how many of each cake to bake, with no ingredient overused, for the largest profit. Chapter [3](cakes.md) states the problem and gives its data. In $`\rho \alpha`$:
>
> ```
> Cakes := db_ref[Cakes](D)
> Recipe := db_ref[Recipe](D)
> Inventory := db_ref[Inventory](D)
> 
> Qty := ω[qty 0..100]
> B := ω_sol(Cakes, Qty)
> 
> MakableBatches := σ_sol[
>     γ[][bool_and(ret) → ret](
>         γ[ingredient, avail][sum(qty * amount) <= avail → ret](
>             B ⋈ Recipe ⋈ Inventory))](B)
> 
> ProfitableBatch := ℰ_sol[1, desc,
>     γ[][sum(qty * price)](MakableBatches)](MakableBatches)
> 
> LetsMakeBatch := π[cake, price, qty](
>     ℰ[all, asc, cake](forget(flatten[](ProfitableBatch))))
> ```
>
> As RassoLean terms:
>
> ```
> [("Cakes", .dbRef "Cakes" (.name "D")),
>  ("Recipe", .dbRef "Recipe" (.name "D")),
>  ("Inventory", .dbRef "Inventory" (.name "D")),
>  ("Qty", .omega [("qty", .range 0 100)]),
>  ("B", .omegaSol (.name "Cakes") (.name "Qty")),
>  ("MakableBatches",
>   .sigmaSol
>     (.expr
>        (.gamma
>           []
>           (.agg "bool_and" (.attr "ret"))
>           (some "ret")
>           (.gamma
>              ["ingredient", "avail"]
>              (.call
>                 "<="
>                 [.agg "sum" (.call "*" [.attr "qty", .attr "amount"]),
>                  .attr "avail"])
>              (some "ret")
>              (.nary .join [.name "B", .name "Recipe", .name "Inventory"]))))
>     (.name "B")),
>  ("ProfitableBatch",
>   .enumSol
>     (.int 1)
>     (some
>        (.desc,
>         .gamma
>           []
>           (.agg "sum" (.call "*" [.attr "qty", .attr "price"]))
>           none
>           (.name "MakableBatches")))
>     (.name "MakableBatches")),
>  ("LetsMakeBatch",
>   .project
>     ["cake", "price", "qty"]
>     (.enum
>        .all
>        (some (.asc, .attr "cake"))
>        (.forget (.flatten none (.name "ProfitableBatch")))))]
> ```
>
> The data is `Cakes`, and the decision is `Qty`. So `B` has $`101^2 = 10\, 201`$ candidates, each one batch: a number of each cake. The condition keeps the batches that overuse no ingredient: joined with the recipes and the stock, each ingredient’s use sums to at most its stock. The key ranks the kept batches by profit. $`12`$ batches pass the condition, and the best is two banana cakes and two chocolate cakes, with profit $`1700`$ cents. RassoLean’s evaluator and the Racket implementation both give this answer. The release’s examples hold the program and its data.
>
> This says which batches the solution set holds, not how to find them. RassoLean’s evaluator finds them as the definitions read: it lists all $`10\, 201`$ candidates and computes the condition on each. That is exact, and it is practical only for a small space like this one. A problem with a large space of candidates, such as Sudoku, or with a decision over an infinite domain, is instead lowered by $`\Phi`$ to one flat relation and a Boolean term over it, which a solver takes (Chapter [13](phi.md)).

Uses: [Definition 9.1](#def-r2-sol), [Definition 9.3](#def-r2-sigma-sol), [Definition 9.6](#def-r2-enum-sol), [Definition 9.7](#def-r2-flatten), [Definition 6.8](finite.md#def-r2-gamma).

<a id="ex-r2-latin"></a>

**Example 9.9 (Latin squares by join).**

> The Rasso paper builds the Latin square from two simpler solution sets [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation), Appendix E.2, Listing 8]. Here the order is $`3`$: `Positions` holds the positions $`1`$, $`2`$ and $`3`$, in its one attribute `pos`. A Latin vector gives each position a value in `1..3`, all different. The square renames the vector to run over the rows, and again over the columns, and joins the two. In $`\rho \alpha`$:
>
> ```
> S := ω_sol(Positions, ω[value 1..3])
> Vector := σ_sol[γ[][all_different(value) → ret](S)](S)
> Square := ρ[pos → row](Vector) ⋈ ρ[pos → col](Vector)
> ```
>
> As RassoLean terms:
>
> ```
> [("S", .omegaSol (.name "Positions") (.omega [("value", .range 1 3)])),
>  ("Vector",
>   .sigmaSol
>     (.expr
>        (.gamma [] (.agg "all_different" (.attr "value")) (some "ret") (.name "S")))
>     (.name "S")),
>  ("Square",
>   .nary
>     .join
>     [.rename [("pos", "row")] (.name "Vector"),
>      .rename [("pos", "col")] (.name "Vector")])]
> ```
>
> The data of `Square` is every row with every column, and its decision is the one shared attribute `value`. Each candidate gives each cell a value so that every row and every column is a Latin vector: it is a Latin square. RassoLean’s evaluator finds the $`12`$ Latin squares of order $`3`$.

Uses: [Definition 9.4](#def-r2-join-sol), [Definition 9.5](#def-r2-rename-sol), [Definition 9.3](#def-r2-sigma-sol).

<a id="sec-9-7"></a>
## 9.7 Traditions to explore

We have yet to explore:

- top-$`k`$ and preference queries, which order the answers of a query by a score, among them rank-aware relational algebra (RankSQL) and rank-aware databases (RankDB);
- functional aggregate queries, which take constraint satisfaction, joins and aggregation over semirings as one problem [[3](references.md#khamis_2016_faq.questions.asked.frequently)].

A solution set decides one function from its data. The next chapter gives the reasons for a function space as the space of candidates; the chapter after it decides several functions together, with conditions across them.

<a id="properties"></a>
## Properties

Each property is proved in Lean. Sketches of the proofs are in Section [A.6](proofs.md#sec-r2-proofs-sol). That the candidates of $`\omega _\mathrm{sol}(\mathit{Data}, \mathit{Decision})`$ are exactly the graphs of the functions from $`\mathit{Data}`$ to $`\mathit{Decision}`$, each once for well-formed data and decision, is Theorem [10.1](fspace.md#thm-r2-fspace-graph) in Chapter [10](fspace.md). That $`\bowtie _\mathrm{sol}`$ is commutative and associative, up to the order of the heading, is checked on examples, the Latin square among them, and not proved (Appendix [B](laws.md)).

<a id="thm-r2-sol-meaning"></a>

**Theorem 9.10 (The meaning of a solution set).** ✓

> When each selection gives a result, the candidates of $`\sigma _\mathrm{sol}[c_n](\cdots \sigma _\mathrm{sol}[c_1](\omega _\mathrm{sol}(\mathit{Data}, \mathit{Decision})))`$ are exactly the graphs of the functions from the tuples of $`\mathit{Data}`$ to the tuples of $`\mathit{Decision}`$ for which each condition $`c_1, \ldots , c_n`$ is true.

Uses: [Definition 9.1](#def-r2-sol), [Definition 9.3](#def-r2-sigma-sol).<br>
Lean: [`Rasso.omegaSolCandidates_meaning`](../Rasso/FSpace.lean#L647-L649), [`Rasso.sigmaSol_meaning`](../Rasso/FSpace.lean#L651-L664).<br>
[Proof sketch](proofs.md#sketch-thm-r2-sol-meaning).

<a id="thm-r2-sol-order"></a>

**Theorem 9.11 (Selection does not depend on the order of candidates).** ✓

> $`\sigma _\mathrm{sol}[c]`$ on two lists of candidates with the same members, in any order and with any repeats, is refused for both or for neither, and otherwise keeps the same candidates.

Uses: [Definition 9.3](#def-r2-sigma-sol).<br>
Lean: [`Rasso.sigmaSol_order`](../Rasso/FSpace.lean#L666-L673).<br>
[Proof sketch](proofs.md#sketch-thm-r2-sol-order).

<a id="thm-r2-join-sol"></a>

**Theorem 9.12 (The meaning of the join of solution sets).** ✓

> Let $`U \bowtie _\mathrm{sol}V`$ succeed, on solution sets whose candidates are graphs of functions on their data. Its data is $`\mathit{Data}_U \bowtie \mathit{Data}_V`$ and its heading that data’s heading followed by $`\mathit{Decision}_U \bowtie \mathit{Decision}_V`$. A function on its data is a candidate exactly when each of its slices along $`G_U`$ is a candidate of $`U`$ and each of its slices along $`G_V`$ is a candidate of $`V`$. Its candidates are again graphs of functions on its data, and when neither operand lists a candidate twice, neither does the result. When a data attribute of one operand is a decision attribute of the other, $`\bowtie _\mathrm{sol}`$ is refused.

Uses: [Definition 9.4](#def-r2-join-sol).<br>
Lean: [`Rasso.SolJoinLaws.mem_join`](../Rasso/Laws/SolJoinComplete.lean#L442-L457), [`Rasso.SolJoinLaws.join_shape`](../Rasso/Laws/SolJoin.lean#L105-L128), [`Rasso.SolJoinLaws.join_refuses_data_decision`](../Rasso/Laws/SolJoin.lean#L149-L185), [`Rasso.SolJoinLaws.join_membersOk`](../Rasso/Laws/SolJoinSlices.lean#L758-L829), [`Rasso.SolJoinLaws.nodup_join`](../Rasso/Laws/SolJoinSlices.lean#L886-L939).<br>
[Proof sketch](proofs.md#sketch-thm-r2-join-sol).

<a id="thm-r2-rename-sol"></a>

**Theorem 9.13 (Renaming a solution set).** ✓

> $`\rho _\mathrm{sol}[a \to b](U)`$ succeeds exactly when $`\rho`$ succeeds on the heading of $`U`$ and on its data. Then it renames the data, the heading and each candidate, and its candidates are again graphs of functions on its data.

Uses: [Definition 9.5](#def-r2-rename-sol).<br>
Lean: [`Rasso.SolJoinLaws.rename_ok`](../Rasso/Laws/SolJoin.lean#L20-L47), [`Rasso.SolJoinLaws.rename_eq`](../Rasso/Laws/SolJoin.lean#L49-L77), [`Rasso.SolJoinLaws.rename_membersOk`](../Rasso/Laws/SolRenameMembers.lean#L123-L258).<br>
[Proof sketch](proofs.md#sketch-thm-r2-rename-sol).
