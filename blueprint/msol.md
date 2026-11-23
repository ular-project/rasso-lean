<a id="chap-r2-msol"></a>
# 11 Multi-solution sets

This chapter gives multi-solution sets. Some problems decide several things at once, each over its own data, such as a facility location problem: which facilities to open, and which customer each one serves (Example [11.3](#ex-r2-facility)). A multi solution set decides several solution sets together, with conditions across them. Each of its candidates is a database (Definition [6.2](finite.md#def-r2-db)).

Deciding several relations together is the shape of an existential second-order sentence with several second-order variables, as Chapter [12](eso.md) shows. NP-Alg guesses several relations in the same way [[51](references.md#mancini_2004_declarative.constraint.modelling.specification.level), § 8.2]. A solution of an equation in relational algebra is a database over its variables [[10](references.md#biskup_2004_solving.equations.in.relational.algebra), Definition 3.1], and each possible world of Koch’s world-set algebra is a database [[42](references.md#koch_2009_compositional.query.algebra.second.order), § 1]. A constraint model in MiniZinc may have several arrays of decision variables, linked by its constraints [[55](references.md#nethercote_2007_minizinc.standard.cp.modelling.language)].

<a id="sec-11-1"></a>
## 11.1 Multi-solution sets

<a id="def-r2-msol"></a>

**Definition 11.1 (Multi-solution set).** ✓

> Let $`U_1, \ldots , U_m`$ be solution sets and $`n_1, \ldots , n_m`$ distinct names, the *members*. A *candidate* of the multi-solution set is a database that gives each name $`n_i`$ one candidate of $`U_i`$.
>
> $`\omega _{\mathrm{msol}}[n_1\ U_1, \ldots , n_m\ U_m](c)`$ is the multi-solution set of the candidates for which the condition $`c`$ holds. Inside $`c`$, the name $`n_i`$ stands for that candidate’s relation for $`n_i`$. So $`c`$ can relate the members to each other. With no condition, every candidate is kept.

Uses: [Definition 9.1](sol.md#def-r2-sol), [Definition 6.2](finite.md#def-r2-db), [Definition 9.2](sol.md#def-r2-cond).<br>
Lean: [`Rasso.Msol`](../Rasso/Eval.lean#L114-L117).

<a id="def-r2-msol-ops"></a>

**Definition 11.2 (Operators on multi-solution sets).** ✓

> - $`\sigma _{\mathrm{msol}}[c](M)`$ keeps the candidates of $`M`$ for which $`c`$ holds.
> - $`\mathcal{E}_{\mathrm{msol}}[k, d, e](M)`$ is the sequence of at most $`k`$ candidates of $`M`$, in the order of the key $`e`$. In $`e`$, as in a condition, the member names stand for the candidate’s relations.
> - $`\mathrm{flatten\_ msol}[r](S)`$ makes a sequence of databases one database. For each member, it takes the union of that member’s relations, each tuple with the attribute $`r`$ for its database’s place in $`S`$, counted from $`1`$. With no $`r`$, $`S`$ must have at most one database. The result is that database, or, when $`S`$ is empty, the database that gives each member the empty relation.

Uses: [Definition 11.1](#def-r2-msol), [Definition 9.6](sol.md#def-r2-enum-sol).<br>
Lean: [`Rasso.Expr.eval`](../Rasso/Eval.lean#L366-L561), [`Rasso.eval_sigmaMsol_meaning`](../Rasso/Bridge/Sol.lean#L415-L426), [`Rasso.eval_enumMsol_meaning`](../Rasso/Bridge/Sol.lean#L453-L466), [`Rasso.eval_flattenMsol`](../Rasso/Bridge/Sol.lean#L480-L511), [`Rasso.rankUnion`](../Rasso/Eval.lean#L233-L236).

<a id="sec-11-2"></a>
## 11.2 In $`\rho \alpha`$ and RassoLean terms

<a id="ex-r2-facility"></a>

**Example 11.3 (Facility location).**

> Choose which sites to open, and give each customer one site, for the least cost of opening plus assignment. The problem is simplified from DeQL’s facility location [[12](references.md#brucato_2026_deql.decision.query.language.prescriptive), § 9.7]: here a site has no capacity, a customer has no demand, and each customer is served by one site. The data are `Sites`, with an opening cost for each site, `Customers`, and `AssignCost`, the cost of serving each customer from each site, read from the database $`D`$:
>
> | `Sites` |  |
> |---|---|
> | `site symbol` | `openCost int` |
> | s1 | 5 |
> | s2 | 3 |
>
> | `Customers` |
> |---|
> | `c symbol` |
> | c1 |
> | c2 |
> | c3 |
>
> | `AssignCost` |  |  |
> |---|---|---|
> | `c symbol` | `site symbol` | `cost int` |
> | c1 | s1 | 1 |
> | c1 | s2 | 4 |
> | c2 | s1 | 2 |
> | c2 | s2 | 2 |
> | c3 | s1 | 4 |
> | c3 | s2 | 1 |
>
> In $`\rho \alpha`$:
>
> ```
> Sites := db_ref[Sites](D)
> Customers := db_ref[Customers](D)
> AssignCost := db_ref[AssignCost](D)
> 
> Open := ω_sol(Sites, ω[isOpen 0..1])
> Assign := ω_sol(Customers, ω[site ∈ π[site](Sites)])
> 
> Plan := ω_msol[Open Open, Assign Assign](
>     γ[][bool_and(isOpen = 1)](Assign ⋈ Open))
> 
> Best := ℰ_msol[1, asc,
>     γ[][sum(o + a)](
>         γ[][sum(openCost * isOpen) → o](Open)
>             ⋈ γ[][sum(cost) → a](Assign ⋈ AssignCost))](Plan)
> 
> Assignment := ℰ[all, asc, c](db_ref[Assign](flatten_msol[](Best)))
> ```
>
> As RassoLean terms:
>
> ```
> [("Sites", .dbRef "Sites" (.name "D")),
>  ("Customers", .dbRef "Customers" (.name "D")),
>  ("AssignCost", .dbRef "AssignCost" (.name "D")),
>  ("Open", .omegaSol (.name "Sites") (.omega [("isOpen", .range 0 1)])),
>  ("Assign",
>   .omegaSol
>     (.name "Customers")
>     (.omega [("site", .in_ (.project ["site"] (.name "Sites")))])),
>  ("Plan",
>   .omegaMsol
>     [("Open", .name "Open"), ("Assign", .name "Assign")]
>     (some
>        (.expr
>           (.gamma
>              []
>              (.agg "bool_and" (.call "=" [.attr "isOpen", .val (.int 1)]))
>              none
>              (.nary .join [.name "Assign", .name "Open"]))))),
>  ("Best",
>   .enumMsol
>     (.int 1)
>     (some
>        (.asc,
>         .gamma
>           []
>           (.agg "sum" (.call "+" [.attr "o", .attr "a"]))
>           none
>           (.nary
>              .join
>              [.gamma
>                 []
>                 (.agg "sum" (.call "*" [.attr "openCost", .attr "isOpen"]))
>                 (some "o")
>                 (.name "Open"),
>               .gamma
>                 []
>                 (.agg "sum" (.attr "cost"))
>                 (some "a")
>                 (.nary .join [.name "Assign", .name "AssignCost"])])))
>     (.name "Plan")),
>  ("Assignment",
>   .enum
>     .all
>     (some (.asc, .attr "c"))
>     (.dbRef "Assign" (.flattenMsol none (.name "Best"))))]
> ```
>
> `Open` decides, for each site, whether it is open, and `Assign` decides, for each customer, its site. The condition of `Plan` relates the two members: every site that a customer uses is open. $`10`$ plans pass the condition: one opens `s1` only, one `s2` only, and eight open both. The cheapest opens `s2` only and serves every customer from it, at cost $`3 + 4 + 2 + 1 = 10`$. RassoLean’s evaluator gives this answer for the program with the tables’ data in place of $`D`$, as the release’s examples hold it.

Uses: [Definition 11.1](#def-r2-msol), [Definition 11.2](#def-r2-msol-ops), [Definition 6.2](finite.md#def-r2-db).

<a id="sec-11-3"></a>
## 11.3 Traditions to explore

We have yet to explore:

- channelling constraints in constraint programming, which link two models of one problem, each with its own decision variables [[17](references.md#cheng_1999_increasing.constraint.propagation.redundant.modeling), [34](references.md#hnich_2004_dual.modelling.permutation.injection.problems)]. We expect that a dual model is a multi-solution set of two members, $`\mathit{Decision}^{\mathit{Data}}`$ and $`(\mathit{Data}+ 1)^{\mathit{Decision}}`$, where the extra value marks a decision value that is not used, and is dropped when the function is a bijection. This needs the decision to be finite, since it is the data of the second member. Since a candidate is held as its graph, and the named perspective makes a relation and its converse the same, the channel would then be one condition: the two graphs are equal, once the extra value is removed. Whether this holds beyond dual models, for channels between a function and a 0/1 matrix or a set (Chapter [10](fspace.md)), and whether $`\Phi`$ (Chapter [13](phi.md)) passes such a channel to a solver in a form that propagates well, is to be explored;

A multi-solution set decides several relations, as an existential second-order sentence quantifies several. The next chapter makes this precise, for the properties that existential second-order logic defines.

<a id="properties"></a>
## Properties

Each property is proved in Lean. Sketches of the proofs are in Section [A.8](proofs.md#sec-r2-proofs-msol).

<a id="thm-r2-msol-cands"></a>

**Theorem 11.4 (The candidates of a multi-solution set).** ✓

> Before its condition, $`\omega _{\mathrm{msol}}[n_1\ U_1, \ldots , n_m\ U_m]`$ has exactly the databases that give each $`n_i`$ one candidate of $`U_i`$, and there are as many as the product of the numbers of candidates of the $`U_i`$. In each, the name $`n_i`$ looks up a candidate of $`U_i`$.

Uses: [Definition 11.1](#def-r2-msol).<br>
Lean: [`Rasso.mem_omegaMsolDbs`](../Rasso/FSpace.lean#L708-L711), [`Rasso.length_omegaMsolDbs`](../Rasso/FSpace.lean#L713-L719), [`Rasso.CandOf.lookup`](../Rasso/FSpace.lean#L727-L741).<br>
[Proof sketch](proofs.md#sketch-thm-r2-msol-cands).

<a id="thm-r2-msol-meaning"></a>

**Theorem 11.5 (The meaning of a multi-solution set).** ✓

> When each condition gives a result, a database is a candidate of $`\sigma _{\mathrm{msol}}[c_k](\cdots \omega _{\mathrm{msol}}[n_1 U_1, \ldots , n_m\ U_m](c_0))`$ exactly when it gives each $`n_i`$ one candidate of $`U_i`$, and each condition $`c_0, \ldots , c_k`$ is true of it.

Uses: [Definition 11.1](#def-r2-msol), [Definition 11.2](#def-r2-msol-ops).<br>
Lean: [`Rasso.omegaMsol_meaning`](../Rasso/FSpace.lean#L750-L755), [`Rasso.omegaMsol_meaning_none`](../Rasso/FSpace.lean#L757-L760), [`Rasso.sigmaMsol_meaning`](../Rasso/FSpace.lean#L762-L772).<br>
[Proof sketch](proofs.md#sketch-thm-r2-msol-meaning).
