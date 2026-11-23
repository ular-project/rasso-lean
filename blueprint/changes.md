<a id="chap-r2-changes"></a>
# 2 Changes since the paper

This technical report builds on the Rasso paper [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation)], and this chapter is for readers who are familiar with it.

The paper is under revision and will be updated to align with this technical report. For the present, this chapter identifies changes to the original paper following it section by section. For each section of the paper, it notes four things:

**Differences..** What the paper has that is now done another way.

**New since the paper..** What the paper does not have.

**Proved in Lean..** A claim of the paper that RassoLean proves, and where. The chapters state the results, with their hypotheses.

**Not yet in Lean..** What the paper has that RassoLean does not yet render or prove.

The list is not exhaustive: it aims to assist a reader to navigate the changes. A change is listed where the paper first meets it.

<a id="sec-2-1"></a>
## 2.1 Paper abstract and §1: the contributions

**Differences..** The paper presents complete domain relations as the first of its three contributions. This report recognises them as prior work: unrestricted relations take the name and the idea of a finite representation of a possibly infinite relation from the constraint databases of Kanellakis, Kuper and Revesz (Chapters [7](unrestricted.md) and [8](cdb.md)). The paper illustrates the algebras in “polymorphic SQL” (Figures 1 and 3) and in “SQL” (the figures of its appendices). This written form is now *rassoSQL*, one of Rasso’s written forms (Section [1.2](intro.md#sec-r2-intro-names)). It is polymorphic: a clause such as `WHERE` is $`\sigma`$ on a relation and $`\sigma _\mathrm{sol}`$ on a solution set, as its operand decides. But “polymorphic SQL” is not its name.

<a id="sec-2-2"></a>
## 2.2 Paper §2: active domain relations

**Differences..** An active domain relation (ADR) is now a *finite relation* (Chapter [6](finite.md)). The paper’s space $`\mathit{Decision}^{\mathit{Base}}`$ is now written $`\mathit{Decision}^{\mathit{Data}}`$: the paper’s $`\mathit{Base}`$ is renamed the *data*, because in the exponential it is the exponent, not the base. The paper’s order $`\tau`$ and limit $`\lambda`$ are now one operator, $`\mathcal{E}[k, d, e]`$: at most $`k`$ tuples, in the order of the key $`e`$. Its result is a sequence, not a relation, and $`\mathrm{forget}`$ makes it a finite relation again (Definition [6.9](finite.md#def-r2-enum)).

**New since the paper..** One universe of values, in which domains overlap, with exact rationals beside floats and no written domain holding an exact number beside a float, or a symbol beside a string (Chapter [4](values.md), Theorem [4.7](values.md#thm-r2-domain-unmixed)). Extension, which adds an attribute computed from each tuple (Definition [6.7](finite.md#def-r2-extend)).

**Proved in Lean..** That the operators give finite relations again (Theorem [6.13](finite.md#thm-r2-finrel-closed)). The paper takes the domain independence of the active-domain algebra from the literature; Codd’s theorem, for Rasso’s operators, is proved in the Coddstheorem library (Theorem [6.14](finite.md#thm-r2-codd)).

<a id="sec-2-3"></a>
## 2.3 Paper §3: complete domain relations

**Differences..** A complete domain relation (CDR) is now an *unrestricted relation*. It takes the name and the idea of a finite representation of a possibly infinite relation from Kanellakis, Kuper and Revesz (Chapters [7](unrestricted.md) and [8](cdb.md)). In the paper a characteristic function is any function from tuples to Booleans (§2–§3); here it is a Boolean term (Definition [5.3](tuples.md#def-r2-term)), whose form projection and $`\Phi`$ can examine. In the paper, projection is the boundary, the operator where evaluation must occur (§3 and Appendix D.5). Now $`\mathcal{E}`$ is the boundary (Definition [7.6](unrestricted.md#def-r2-unrel-enum)). Projection of an unrestricted relation gives an unrestricted relation again, removing an attribute from a relation whose class is recognised: finite domains, dense order, equality and linear arithmetic (Definition [7.5](unrestricted.md#def-r2-unrel-pi)).

**New since the paper..** $`\mathrm{lift}`$, which makes a finite relation or a sequence an unrestricted relation (Definition [7.4](unrestricted.md#def-r2-lift)). Each of the four classes is closed under the operators, projection included (Theorems [7.10](unrestricted.md#thm-r2-finite-class), [7.11](unrestricted.md#thm-r2-dense-class), [7.12](unrestricted.md#thm-r2-eq-class) and [7.13](unrestricted.md#thm-r2-lin-class)).

**Proved in Lean..** The meaning of the core operators on unrestricted relations (Theorem [7.7](unrestricted.md#thm-r2-unrel-ops)). The laws by which the total unrestricted relations of one heading form a Boolean algebra, as the paper says they inherit from their characteristic functions (Section [B.3](laws.md#sec-r2-laws-unrestricted)). The soundness of projection (Theorem [7.9](unrestricted.md#thm-r2-unrel-pi)). For query safety (Appendix D.4): $`\mathrm{lift}`$ (Theorem [7.8](unrestricted.md#thm-r2-lift)) and the finite class (Theorem [7.10](unrestricted.md#thm-r2-finite-class)).

**Not yet in Lean..** The paper’s bound that the finite region is reached in polynomial time (Appendix D.4).

<a id="sec-2-4"></a>
## 2.4 Paper §3, Listing 1: the 3-SAT example

**Differences..** The paper writes a 3-SAT formula as a complete domain relation, to show that the algebra expresses NP-complete problems. That relation is one fixed formula. In this report, the formula is data, a finite structure, and one program states SAT for every formula: a multi-solution set whose one member is the truth assignment, by the construction from existential second-order logic (Example [12.8](eso.md#ex-r2-sat-boolsel)). The claim behind the example is a theorem (Chapter [12](eso.md), Theorem [12.16](eso.md#thm-r2-eso-same)).

<a id="sec-2-5"></a>
## 2.5 Paper §4.1: exponentiation

**New since the paper..** The laws of exponents hold for solution sets, the product law for the number of candidates, and the product law fails for relations, which is why the space of candidates is a function space and not a power set (Chapter [10](fspace.md)).

<a id="sec-2-6"></a>
## 2.6 Paper §4.2: solution sets

**Differences..** $`\omega _\mathrm{sol}(\mathit{Data}, \mathit{Decision})`$ takes the data and the decision; a condition on the candidates is a separate $`\sigma _\mathrm{sol}`$ (Definitions [9.1](sol.md#def-r2-sol) and [9.3](sol.md#def-r2-sigma-sol)). RassoLean’s evaluator lists the candidates, so it accepts only a finite decision.

**Proved in Lean..** The domain of a solution set, Equation (1) of the paper (Theorem [10.1](fspace.md#thm-r2-fspace-graph)). The meaning of selection (Theorem [9.10](sol.md#thm-r2-sol-meaning)).

**Not yet in Lean..** Remark 1, that subsets need no special case: the subsets of $`\mathit{Data}`$ are the candidates of $`\omega _\mathrm{sol}(\mathit{Data}, \omega [s\ \texttt{bool}])`$. It is proved for Lean functions; for Rasso’s candidates, it is checked on an example (Lemma [10.3](fspace.md#lem-r2-fspace-select)).

<a id="sec-2-7"></a>
## 2.7 Paper §4.3: the algebra on solution sets

**Differences..** The paper’s outer $`\tau _\mathrm{sol}`$ and $`\lambda _\mathrm{sol}`$ are now one operator: $`\lambda _\mathrm{sol}[n](\tau _\mathrm{sol}[\mu ](U))`$ is $`\mathcal{E}_\mathrm{sol}[n, d, \mu ](U)`$, a sequence of candidates (Definition [9.6](sol.md#def-r2-enum-sol)). The paper’s $`\pi _\mathrm{sol}[r][A](U)`$ is now $`\pi [A](\mathrm{forget}(\mathrm{flatten}[r](S)))`$, with $`S`$ the sequence; the rank attribute $`r`$ is the paper’s candRankAttr (Definition [9.7](sol.md#def-r2-flatten)). The decision, satisfaction and optimisation queries of Appendix G.5 are $`\mathcal{E}_\mathrm{sol}`$ with $`k = 1`$, with $`k`$ larger or `all`, and with a key. $`\bowtie _\mathrm{sol}`$ and $`\rho _\mathrm{sol}`$ have no forms of their own: Rasso writes them with the forms of $`\bowtie`$ and $`\rho`$, and the operands decide (Definitions [9.4](sol.md#def-r2-join-sol) and [9.5](sol.md#def-r2-rename-sol)). The definition of $`\bowtie _\mathrm{sol}`$ is corrected. The paper’s lifting groups the joined candidate by all of the other side’s data attributes, the paper’s base attributes (Appendix E.2). When the two sides share data attributes, each group then fixes them, and a side’s condition is tested on part of its data; when the data are equal, each group is one tuple. Here the slices are grouped by the data attributes that the other side adds. The two agree when the data share no attribute, as in the Latin square, and with equal data the join is the conjunction of the two conditions, as the paper’s $`\cap _\mathrm{sol}`$ states. Two refusals are new: a data attribute of one side that the other side decides, and a slice that would not cover its side’s data. The paper says the algebraic properties of the algebra on solution sets inherit from the Boolean algebra of their characteristic functions. This report withdraws that. $`\bowtie _\mathrm{sol}`$ changes the data and the decision, so it is not a meet within one Boolean algebra: its candidates are the functions on the joined data whose slices are candidates of each side (Section [B.7](laws.md#sec-r2-laws-soljoin)). Only selection on one function space behaves as its conditions do, a cascade of selections being their conjunction (Section [B.4](laws.md#sec-r2-laws-sol)).

**Proved in Lean..** The meaning of $`\bowtie _\mathrm{sol}`$, as corrected, and that $`\bowtie _\mathrm{sol}`$ and $`\rho _\mathrm{sol}`$ give solution sets again (Theorem [9.12](sol.md#thm-r2-join-sol); Section [B.7](laws.md#sec-r2-laws-soljoin)).

**Not yet in Lean..** $`\times _\mathrm{sol}`$ exists only as $`\bowtie _\mathrm{sol}`$ on disjoint attributes. $`\cap _\mathrm{sol}`$, $`-_\mathrm{sol}`$ and $`\cup _\mathrm{sol}`$ are in neither implementation. That $`\bowtie _\mathrm{sol}`$ is commutative and associative is checked on examples, among them the paper’s Latin square of Listing 8, but not proved.

<a id="sec-2-8"></a>
## 2.8 Paper §5 and Appendix G: translation to relations

**Differences..** $`\Phi`$ follows the algorithm of the Racket implementation, not the paper’s: it evaluates the conditions once over symbolic values. The result is one unrestricted relation, the flat relation, with a variable for each pair of a data tuple and a decision attribute (Chapter [13](phi.md)). $`\Phi`$ takes a fragment of the language: the conditions it can translate.

**Proved in Lean..** The paper’s claim that the translation keeps the meaning, for RassoLean’s $`\Phi`$ (Section [13.7](phi.md#sec-r2-phi-theorems)).

**Not yet in Lean..** $`\Phi`$ of $`\bowtie _\mathrm{sol}`$ and $`\rho _\mathrm{sol}`$, and of floats.

<a id="sec-2-9"></a>
## 2.9 Paper §6: the cakes problem

**Differences..** Chapter [3](cakes.md) states the problem and its data. RassoLean’s evaluator and the Racket implementation give the paper’s answer (Example [9.8](sol.md#ex-r2-cakes)).

<a id="sec-2-10"></a>
## 2.10 Paper §7: related work

**Differences..** The paper sets complete domain relations apart from constraint databases, on the ground that a constraint relation is a quantifier-free formula in disjunctive normal form, so that the tuple is privileged. This report withdraws that reading. The object of Kanellakis, Kuper and Revesz is the unrestricted relation, and its representation in disjunctive normal form does not change that (Chapter [8](cdb.md)). The difference is one of goals. Both traditions join data and constraints. The constraint database tradition seeks closure: queries, projection included, with a closed form, for classes of constraints that admit quantifier elimination (Kanellakis, Kuper and Revesz [[40](references.md#kanellakis_1995_constraint.query.languages)]), and an algebra with the same property (Goldin and Kanellakis [[31](references.md#goldin_1996_constraint.query.algebras)]). Rasso admits any term as the characteristic function of a decision relation, and keeps their closure only within such classes (Chapter [7](unrestricted.md)). The decision relation is the codomain of the function space $`\mathit{Decision}^{\mathit{Data}}`$, the search space of constraint programming.

<a id="sec-2-11"></a>
## 2.11 Paper Appendix H.2.2: nested and powerset algebras

**Differences..** The paper says the nested and powerset algebras add no expressive power to flat relational algebra. That is true of the nested algebra [[57](references.md#paredaens_1992_converting.nested.algebra.expressions.flat)], but not of the powerset algebra [[1](references.md#abiteboul_1995_foundations.of.databases), Theorem 20.7.1]. This report withdraws the sentence. Rasso’s function space is the total, functional part of the powerset (Chapter [10](fspace.md)).

<a id="sec-2-12"></a>
## 2.12 Beyond the paper

**New since the paper..** Multi-solution sets: several solution sets decided together, with conditions across them, each candidate a database. Databases are values, and $`\mathrm{db\_ ref}`$ takes a relation from one (Definition [6.2](finite.md#def-r2-db); Chapter [11](msol.md)). Selection on Boolean function spaces, and its relation to existential second-order logic (Chapter [12](eso.md)). $`\Phi`$ of a multi-solution set (Chapter [13](phi.md)).

The next chapter gives the running example. The development starts in Chapter [4](values.md), with the values that relations hold.
