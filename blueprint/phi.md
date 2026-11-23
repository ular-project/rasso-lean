<a id="chap-r2-phi"></a>
# 13 $`\Phi`$: from solution sets to one relation

A solution set $`\mathit{Decision}^{\mathit{Data}}`$ has $`|\mathit{Decision}|^{|\mathit{Data}|}`$ candidates. The evaluator of Chapter [9](sol.md) lists every candidate and tests the conditions on each. That enumeration defines the meaning of Rasso. It is exact, and it takes time exponential in $`|\mathit{Data}|`$. When the function space is large, the candidates are too many to list; when it is infinite, as with a decision over the integers, they cannot be listed at all. Such a problem is searched instead, and search takes it in a flat form.

This chapter defines $`\Phi`$, which lowers a solution set, or a multi-solution set, to one unrestricted relation (Chapter [7](unrestricted.md)), the *flat relation*. Its attributes are the *cells*, one for each pair of a data tuple and a decision attribute, each with that attribute’s domain. Its characteristic function is the conditions, written as one Boolean term over the cells. Each tuple of the flat relation gives one candidate, and the candidates that the tuples give are exactly the candidates of the solution set. In a solver’s terms, the flat relation is a constraint model: each attribute is a *variable* with its domain, and the characteristic function is one *constraint*. A constraint solver, a SAT solver or a mixed integer solver takes a problem in this form.

$`\Phi`$ comes from the Rasso paper [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation), Appendix G]. The idea of lowering a model to variables and one constraint is not new. Essence states a problem with decision variables of function and relation type [[26](references.md#frisch_2008_essence.constraint.language.specifying.combinatorial)], and Conjure can lower each such variable to a matrix of first-order variables, one for each element of its domain [[4](references.md#akgun_2022_conjure.automatic.generation.constraint.models)]. MiniZinc compiles a model to FlatZinc, a flat list of variables and constraints [[55](references.md#nethercote_2007_minizinc.standard.cp.modelling.language)]. Answer set programming grounds a program before it solves it [[28](references.md#gebser_2013_answer.set.solving.in.practice)]. NP-Alg [[16](references.md#cadoli_2007_relational.algebra.sql.constraint.modelling)] also translates guessed relations to a solver.

<a id="sec-13-1"></a>
## 13.1 Where $`\Phi`$ stands

<a id="sec-13-1-the-eso-chapter-does-not-use"></a>
**The ESO chapter does not use $`\Phi`$.**

Chapter [12](eso.md) proves its theorems about Rasso’s evaluator, `Expr.eval`, directly. No file of those proofs (`Rasso/ESO.lean` and `Rasso/ESO/`) imports `Rasso.Phi`, directly or through another module. No other file of RassoLean imports it either, apart from `Rasso.lean`, which gathers every module. Selection on Boolean function spaces states exactly the NP properties whether or not $`\Phi`$ exists.

<a id="sec-13-1-states-it-does-not-solve"></a>
**$`\Phi`$ states; it does not solve.**

Rasso’s aim is to state a problem precisely. $`\Phi`$ states the same problem in another form. How a solver finds tuples of the flat relation, and which tuple it finds first, is outside the algebra.

<a id="sec-13-1-does-not-optimise"></a>
**$`\Phi`$ does not optimise.**

$`\Phi`$ translates that meaning mechanically: one cell for each data tuple and decision attribute, and the conditions as the evaluator interprets them. It makes no choice. Conjure, by contrast, chooses among several representations of each abstract decision variable, and selects one of the models that result [[4](references.md#akgun_2022_conjure.automatic.generation.constraint.models)]; Savile Row then improves the chosen model, by common subexpression elimination among other reformulations [[56](references.md#nightingale_2017_automatically.constraint.models.savile.row)]. DeQL’s Planner rewrites the problem before it lowers it: it detects structure in the query, such as a bipartite pattern of supply and demand, and selects a formulation to suit it. In its demonstration, a transportation problem solved as min-cost network flow rather than as a mixed integer program reaches the same optimum thirty times faster [[13](references.md#brucato_2026_deql.studio.declarative.decision.making)]. Which flat relation a solver searches fastest is outside $`\Phi`$.

<a id="sec-13-1-the-symbol"></a>
**The symbol.**

The ESO chapter writes $`\varphi`$ for a first-order formula. This chapter writes $`\Phi`$, as the Rasso paper does. The two are not related.

<a id="sec-13-2"></a>
## 13.2 The fragment

$`\Phi`$ takes a solution-set statement whose conditions it can translate.

<a id="def-r2-phi-chain"></a>

**Definition 13.1 (Chain).** ✓

> A statement *unfolds to a chain* when it is
>
> ```math
> \sigma _\mathrm{sol}[c_n](\ldots \sigma _\mathrm{sol}[c_1](\omega _\mathrm{sol}(\mathit{Data}, \mathit{Decision}))),
> ```
>
> perhaps through the names of earlier statements. The chain is the $`\omega _\mathrm{sol}`$ and the list of *levels*. A level is one condition $`c_i`$ with the statement that wrote it. A statement is *in the $`\Phi`$ fragment* when it unfolds to a chain.

Uses: [Definition 9.1](sol.md#def-r2-sol), [Definition 9.3](sol.md#def-r2-sigma-sol).<br>
Lean: [`Rasso.Phi.Chain`](../Rasso/Phi/Fragment.lean#L468-L474), [`Rasso.Phi.Level`](../Rasso/Phi/Fragment.lean#L461-L466), [`Rasso.Phi.chainOf`](../Rasso/Phi/Fragment.lean#L476-L485), [`Rasso.Phi.Unfolds`](../Rasso/Phi/Fragment.lean#L487-L494), [`Rasso.Phi.statementChain`](../Rasso/Phi/Fragment.lean#L540-L542), [`Rasso.Phi.InPhiFragment`](../Rasso/Phi/Fragment.lean#L544-L545).

<a id="def-r2-phi-cond"></a>

**Definition 13.2 (Conditions that $`\Phi`$ translates).** ✓

> In a condition, a *leaf* is an expression that does not mention the candidate and holds no solution-set form. $`\Phi`$ translates a condition built from `∧`, `∨`, `¬`, `has_subset` of a leaf, and relational expressions over the candidate. Such an expression is the candidate, a leaf, $`\gamma`$, extend or a join. Its terms use the known operators, with no float.

Uses: [Definition 9.2](sol.md#def-r2-cond), [Definition 13.1](#def-r2-phi-chain).<br>
Lean: [`Rasso.PhiCond`](../Rasso/Phi/Fragment.lean#L395-L400), [`Rasso.PhiExpr`](../Rasso/Phi/Fragment.lean#L330-L336), [`Rasso.PhiTerm`](../Rasso/Phi/Fragment.lean#L243-L247), [`Rasso.PhiAgg`](../Rasso/Phi/Fragment.lean#L281-L287), [`Rasso.IsLeaf`](../Rasso/Phi/Fragment.lean#L207).

Some refusals depend on values, not on forms. $`\Phi`$ refuses to group by a cell, a float in the data, and a leaf whose value is a solution set. The evaluator accepts more than the fragment: it also evaluates $`\sigma`$, $`\pi`$, $`\rho`$, $`\cup`$, $`\cap`$ and $`-`$ over the candidate inside a condition. RassoLean’s $`\Phi`$ refuses these.

<a id="sec-13-3"></a>
## 13.3 The flat relation

<a id="def-r2-phi-cell"></a>

**Definition 13.3 (Cell).** ✓

> Number the data tuples $`1, \ldots , |\mathit{Data}|`$, in a fixed order. For the decision attribute $`a`$ and the data tuple $`i`$, the *cell* $`a_i`$ is a variable whose domain is the domain of $`a`$.

Uses: [Definition 13.1](#def-r2-phi-chain).<br>
Lean: [`Rasso.Phi.cellName`](../Rasso/Phi/Phi.lean#L563-L564).

<a id="def-r2-phi"></a>

**Definition 13.4 ($`\Phi`$ of a solution set).** ✓

> $`\Phi`$ of a statement in the fragment gives:
>
> - the solution set’s heading, data then decision, and its decision attributes;
> - the *symbolic candidate*: data tuple $`i`$ with the cell $`a_i`$ in place of each decision attribute $`a`$;
> - the cells, each with its domain;
> - the *term*: the decision’s own term on every copy, then each level’s condition, evaluated over the symbolic candidate, all joined by `∧` and simplified.
>
> The *flat relation* is the unrestricted relation whose attributes are the cells and whose characteristic function is the term. $`\Phi`$ refuses a statement outside the fragment.

Uses: [Definition 13.3](#def-r2-phi-cell), [Definition 13.2](#def-r2-phi-cond), [Definition 7.1](unrestricted.md#def-r2-unrel).<br>
Lean: [`Rasso.Phi.Flat`](../Rasso/Phi/Phi.lean#L509-L521), [`Rasso.Phi.phi`](../Rasso/Phi/Phi.lean#L604-L607), [`Rasso.Phi.phiOf`](../Rasso/Phi/Phi.lean#L566-L602).

<a id="def-r2-phi-subst"></a>

**Definition 13.5 (Assignment, substitution, reference check).** ✓

> An assignment *respects* the cells when it gives each cell a value in the cell’s domain. It *covers exactly* the cells when it gives values to the cells and to nothing else.
>
> $`\mathrm{subst}(F, x)`$ is the finite relation that the assignment $`x`$ gives: the symbolic candidate with each cell replaced by its value in $`x`$.
>
> $`\mathrm{accepts}(c)`$ is what the evaluator does with one finite relation $`c`$: it evaluates the decision’s term on every tuple of $`c`$, then each level’s condition, from the innermost out, with $`c`$ in place of the candidate.

Uses: [Definition 13.4](#def-r2-phi).<br>
Lean: [`Rasso.Phi.FitsCells`](../Rasso/Phi/Theorems/Square.lean#L218-L220), [`Rasso.Tuple.Over`](../Rasso/FSpace.lean#L129-L131), [`Rasso.Phi.substitute`](../Rasso/Phi/Phi.lean#L611-L617), [`Rasso.Phi.accepts`](../Rasso/Phi/Phi.lean#L632-L635), [`Rasso.Phi.checkSquare`](../Rasso/Phi/Phi.lean#L637-L660).

<a id="sec-13-4"></a>
## 13.4 The key

$`\mathcal{E}_\mathrm{sol}[k, d, e](U)`$ orders candidates by a key $`e`$ (Definition [9.6](sol.md#def-r2-enum-sol)). A solver that optimises needs the key as a term over the cells. $`\Phi`$ writes it so.

<a id="def-r2-phi-key"></a>

**Definition 13.6 ($`\Phi`$ of a key).** ✓

> For a statement $`\mathcal{E}_\mathrm{sol}[k, d, e](U)`$ with $`U`$ in the fragment, $`\Phi`$ gives the flat result of $`U`$ and the key $`e`$ as a term over its cells. $`\mathrm{key}(c)`$ is the value that the evaluator gives to the key on the candidate $`c`$.

Uses: [Definition 13.4](#def-r2-phi), [Definition 9.6](sol.md#def-r2-enum-sol).<br>
Lean: [`Rasso.Phi.phiKey`](../Rasso/Phi/Phi.lean#L672-L689), [`Rasso.Phi.keyValue`](../Rasso/Phi/Phi.lean#L691-L695).

<a id="sec-13-5"></a>
## 13.5 Multi-solution sets

A multi-solution set (Chapter [11](msol.md)) has several members. $`\Phi`$ flattens each member, with the member’s name in its cells’ names, and joins the members’ terms with the multi-solution set’s own conditions.

<a id="def-r2-phi-msol"></a>

**Definition 13.7 ($`\Phi`$ of a multi-solution set).** ✓

> A multi-solution set statement unfolds to an $`\omega _{\mathrm{msol}}`$ with its members, then levels from $`\sigma _{\mathrm{msol}}`$, perhaps through the names of earlier statements. The cell of attribute $`a`$, copy $`i`$, of the member $`n`$ is $`n\_ a\_ i`$. The term is every member’s term and every condition, joined by `∧`. Each condition is evaluated with every member’s symbolic candidate in place of its name. $`\mathrm{msubst}(M, x)`$ is the database that gives each member $`n`$ the candidate $`\mathrm{subst}(F_n, x)`$. $`\mathrm{acceptsMsol}`$ is the evaluator’s check on one database: each member’s check, then each condition.
>
> $`\Phi`$ refuses what the evaluator refuses: no member, a member named $`I`$, and two members with one name. It also refuses the names that the evaluator uses for itself (`%candidate`, `%leaf`, `%condition`). It refuses `has_subset` in a multi-solution set’s condition, which has no single candidate.

Uses: [Definition 13.4](#def-r2-phi), [Definition 11.1](msol.md#def-r2-msol), [Definition 11.2](msol.md#def-r2-msol-ops).<br>
Lean: [`Rasso.Phi.MChain`](../Rasso/Phi/Phi.lean#L726-L731), [`Rasso.Phi.MLevel`](../Rasso/Phi/Phi.lean#L720-L724), [`Rasso.Phi.MFlat`](../Rasso/Phi/Phi.lean#L757-L762), [`Rasso.Phi.memberCell`](../Rasso/Phi/Phi.lean#L754-L755), [`Rasso.Phi.phiMsol`](../Rasso/Phi/Phi.lean#L788-L791), [`Rasso.Phi.phiMsolOf`](../Rasso/Phi/Phi.lean#L771-L786), [`Rasso.Phi.msolSubstitute`](../Rasso/Phi/Phi.lean#L793-L794), [`Rasso.Phi.acceptsMsol`](../Rasso/Phi/Phi.lean#L809-L812).

The key may read the members through $`\gamma`$ over their join. A key that reads a member as a leaf, for example $`\pi`$ over a member, is refused.

<a id="sec-r2-phi-example"></a>
## 13.6 In $`\rho \alpha`$ and RassoLean terms

The cakes program (Example [9.8](sol.md#ex-r2-cakes)) is in the fragment. Its statement `MakableBatches` is one condition on `B`, which is $`\omega _\mathrm{sol}`$ of the data `Cakes` and the decision `Qty`. The condition joins the candidate with `Recipe` and `Inventory`, which are leaves, and groups by `ingredient` and `avail`, which are data. `Cakes` has two tuples, so $`\Phi`$ gives two cells, both for the attribute `qty`: `qty__1` for the banana cake and `qty__2` for the chocolate cake, each with the domain `0..100`. The flat relation, as the Racket implementation’s conformance service writes it. In $`\rho \alpha`$:

```
Flat := ω[qty__1 0..100, qty__2 0..100](
    sum(qty__1 * 2) <= 6
        ∧ sum(qty__1 * 100, qty__2 * 150) <= 500
        ∧ sum(qty__1 * 250, qty__2 * 200) <= 4000
        ∧ sum(qty__1 * 75, qty__2 * 150) <= 2000
        ∧ sum(qty__2 * 75) <= 500
)
```

As RassoLean terms:

```
[("Flat",
  .omegaWhere
    [("qty__1", .range 0 100), ("qty__2", .range 0 100)]
    (.call
       "and"
       [.call
          "<="
          [.call "sum" [.call "*" [.attr "qty__1", .val (.int 2)]], .val (.int 6)],
        .call
          "<="
          [.call
             "sum"
             [.call "*" [.attr "qty__1", .val (.int 100)],
              .call "*" [.attr "qty__2", .val (.int 150)]],
           .val (.int 500)],
        .call
          "<="
          [.call
             "sum"
             [.call "*" [.attr "qty__1", .val (.int 250)],
              .call "*" [.attr "qty__2", .val (.int 200)]],
           .val (.int 4000)],
        .call
          "<="
          [.call
             "sum"
             [.call "*" [.attr "qty__1", .val (.int 75)],
              .call "*" [.attr "qty__2", .val (.int 150)]],
           .val (.int 2000)],
        .call
          "<="
          [.call "sum" [.call "*" [.attr "qty__2", .val (.int 75)]],
           .val (.int 500)]]))]
```

The term has one constraint for each ingredient: bananas, butter, flour, sugar and cocoa, in turn. Each says that the two cakes together use no more of the ingredient than the stock. These are the constraints of the MiniZinc model of the problem [[68](references.md#stuckey_2026_the.minizinc.handbook), § 2.1.2], which $`\Phi`$ derives from the relational condition. The term holds on $`12`$ of the $`10\, 201`$ assignments of the cells, and they give the $`12`$ batches that pass the condition. By the theorems of Section [13.7](#sec-r2-phi-theorems), these are exactly the candidates that the evaluator accepts. RassoLean’s $`\Phi`$ gives the same five constraints, in another order, and names the cells `qty1` and `qty2`.

<a id="sec-r2-phi-theorems"></a>
## 13.7 What the theorems say

Together, Theorems B, C and B$`'`$ give that wherever RassoLean’s $`\Phi`$ gives a flat relation, it is a faithful restatement: its tuples that cover exactly the cells correspond one to one, by $`\mathrm{subst}`$, with the statement’s candidates (or databases), the term holds exactly on those the evaluator accepts, and the key keeps its value. We welcome comments on these statements and on the limits of the fragment.

<a id="sec-r2-phi-racket"></a>
## 13.8 Checked against Racket

Lean’s $`\Phi`$ and Racket’s `phi` are compared on a fixed set of 500 random programs, with the cells compared up to a renaming (a bijection between the two implementations’ names). Wherever both give a flat relation, the two agree. Racket’s `phi-msol` was not compared: the differential harness observed solution sets only.

<a id="sec-13-9"></a>
## 13.9 Not covered

- **Infinite decision domains.** RassoLean’s $`\Phi`$ lists the domain of each decision attribute, so it takes finite decision domains only, and its theorems cover those. $`\Phi`$ itself, as an algebraic lowering, does not need the domain listed.
- **Floats.** Racket checks a solver’s float answers within a tolerance. A theorem about floats needs that tolerance in its statement.
- **$`\bowtie _\mathrm{sol}`$ and $`\rho _\mathrm{sol}`$.** $`\Phi`$ does not yet take a solution set that they build.
- **An $`\mathcal{E}_\mathrm{sol}`$ inside a statement**, for example under $`\mathrm{flatten}`$. Only a statement that is itself an $`\mathcal{E}_\mathrm{sol}`$ has its key flattened.
- **A solver’s input format.** The flat relation is the input in the abstract; writing it in a given solver’s format is a separate step.

<a id="sec-13-10"></a>
## 13.10 Traditions to explore

We have yet to explore:

- model expansion, which takes a search problem as the expansion of a structure to a model of a sentence, and its systems;
- grounding, which writes a second-order guess over a finite structure as one propositional variable for each tuple it might hold, as $`\Phi`$ writes one variable for each cell; answer set programming grounds so, beyond the comparison at the opening of this chapter, with its own treatment of aggregates.
- Conjure’s choice among several representations of a function or relation variable, where $`\Phi`$ has one;

$`\Phi`$ ends the development: Rasso states a search problem, and $`\Phi`$ writes it in the form a solver takes. The next chapter says how the Lean rendering is checked against the Racket implementation, and which proofs come next.

<a id="properties"></a>
## Properties

Each property is proved in `Rasso/Phi/Theorems/` with no `sorry`. The proofs follow $`\Phi`$’s symbolic evaluation step by step. Each piece of it is first proved sound on its own: terms, $`\gamma`$ with its aggregates, extend, and join (`Rasso/Phi/Sound/`). Each depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. Sketches of the proofs are in Section [A.10](proofs.md#sec-r2-proofs-phi).

<a id="thm-r2-phi-square"></a>

**Theorem 13.8 (B: the square).** ✓

> Let $`\Phi`$ succeed on a statement, with result $`F`$. For every assignment $`x`$ that respects the cells, the term of $`F`$ evaluates on $`x`$ to a Boolean $`b`$, and $`\mathrm{accepts}(\mathrm{subst}(F, x))`$ gives the same $`b`$.

Uses: [Definition 13.5](#def-r2-phi-subst).<br>
Lean: [`Rasso.Phi.phi_square`](../Rasso/Phi/Theorems/Square.lean#L694-L702).<br>
[Proof sketch](proofs.md#sketch-thm-r2-phi-square).

<a id="thm-r2-phi-no-refusal"></a>

**Theorem 13.9 (D: no refusal).** ✓

> Let $`\Phi`$ succeed, with result $`F`$. For every assignment $`x`$ that respects the cells, $`\mathrm{accepts}(\mathrm{subst}(F, x))`$ does not refuse.

Uses: [Theorem 13.8](#thm-r2-phi-square).<br>
Lean: [`Rasso.Phi.phi_no_refusal`](../Rasso/Phi/Theorems/Square.lean#L704-L708).<br>
[Proof sketch](proofs.md#sketch-thm-r2-phi-no-refusal).

D says nothing about a finite relation that no assignment gives.

<a id="thm-r2-phi-cells"></a>

**Theorem 13.10 (C: the cells and the candidates).** ✓

> Let $`\Phi`$ succeed on a statement, with result $`F`$. The statement unfolds to a chain whose $`\omega _\mathrm{sol}(\mathit{Data}, \mathit{Decision})`$ has the candidates $`C`$. Then:
>
> 1. for an assignment $`x`$ that respects the cells, $`\mathrm{subst}(F, x) \in C`$ exactly when the decision’s term holds on every copy;
> 2. every candidate in $`C`$ is $`\mathrm{subst}(F, x)`$ for some $`x`$ that respects and covers exactly the cells;
> 3. two assignments that respect and cover exactly the cells, and give the same candidate, are equal.

Uses: [Definition 13.5](#def-r2-phi-subst).<br>
Lean: [`Rasso.Phi.phi_cells`](../Rasso/Phi/Theorems/Cells.lean#L389-L402), [`Rasso.Phi.phi_cells_agree`](../Rasso/Phi/Theorems/Cells.lean#L330-L357), [`Rasso.Phi.substitute_congr`](../Rasso/Phi/Theorems/Cells.lean#L371-L387).<br>
[Proof sketch](proofs.md#sketch-thm-r2-phi-cells).

C is about the candidates of the chain’s $`\omega _\mathrm{sol}`$. The levels’ conditions select from them. B$`'`$ adds the conditions.

<a id="thm-r2-phi-lift"></a>

**Theorem 13.11 (B$`'`$: the statement’s candidates).** ✓

> Let $`\Phi`$ succeed on statement $`k`$, with result $`F`$, and let the statements before $`k`$ run without refusal. Then statement $`k`$ evaluates without refusal to a solution set $`S`$ with the heading of $`F`$, and:
>
> 1. for an assignment $`x`$ that respects the cells, $`\mathrm{subst}(F, x)`$ is a candidate of $`S`$ exactly when $`\mathrm{accepts}(\mathrm{subst}(F, x))`$ gives `true`;
> 2. every candidate of $`S`$ is $`\mathrm{subst}(F, x)`$ for some $`x`$ that respects and covers exactly the cells.

Uses: [Theorem 13.8](#thm-r2-phi-square), [Theorem 13.10](#thm-r2-phi-cells).<br>
Lean: [`Rasso.Phi.phi_lift`](../Rasso/Phi/Theorems/Lift.lean#L345-L361).<br>
[Proof sketch](proofs.md#sketch-thm-r2-phi-lift).

<a id="thm-r2-phi-key"></a>

**Theorem 13.12 (K: the key).** ✓

> Let $`\Phi`$ of the key succeed, with result $`F`$ and term $`t`$. For every assignment $`x`$ that respects the cells, $`t`$ evaluates on $`x`$ to a value $`v`$, and $`\mathrm{key}(\mathrm{subst}(F, x)) = v`$.

Uses: [Definition 13.6](#def-r2-phi-key), [Definition 13.5](#def-r2-phi-subst).<br>
Lean: [`Rasso.Phi.phiKey_sound`](../Rasso/Phi/Theorems/Key.lean#L17-L80).<br>
[Proof sketch](proofs.md#sketch-thm-r2-phi-key).

K is about the key’s value, of any kind, not only a number. $`\Phi`$ restates the key. A solver that maximises or minimises it does work outside the algebra.

<a id="thm-r2-phi-msol-square"></a>

**Theorem 13.13 (M: the square for databases).** ✓

> Let $`\Phi`$ succeed on a multi-solution set statement, with result $`M`$. For every assignment $`x`$ that respects the cells, the term of $`M`$ evaluates on $`x`$ to a Boolean $`b`$, and $`\mathrm{acceptsMsol}(\mathrm{msubst}(M, x))`$ gives the same $`b`$.

Uses: [Definition 13.7](#def-r2-phi-msol).<br>
Lean: [`Rasso.Phi.msol_square`](../Rasso/Phi/Theorems/Msol.lean#L445-L457).<br>
[Proof sketch](proofs.md#sketch-thm-r2-phi-msol-square).

<a id="thm-r2-phi-msol-lift"></a>

**Theorem 13.14 (M$`'`$: the statement’s databases).** ✓

> Let $`\Phi`$ succeed on statement $`k`$, a multi-solution set, with result $`M`$, and let the statements before $`k`$ run without refusal. Then statement $`k`$ evaluates without refusal to a multi-solution set, and:
>
> 1. for an assignment $`x`$ that respects the cells, $`\mathrm{msubst}(M, x)`$ is one of its databases exactly when $`\mathrm{acceptsMsol}(\mathrm{msubst}(M, x))`$ gives `true`;
> 2. every one of its databases is $`\mathrm{msubst}(M, x)`$ for some $`x`$ that respects and covers exactly the cells.

Uses: [Theorem 13.13](#thm-r2-phi-msol-square), [Theorem 13.11](#thm-r2-phi-lift).<br>
Lean: [`Rasso.Phi.phiMsol_lift`](../Rasso/Phi/Theorems/MsolLift.lean#L656-L699).<br>
[Proof sketch](proofs.md#sketch-thm-r2-phi-msol-lift).

<a id="thm-r2-phi-msol-cells"></a>

**Theorem 13.15 (C for databases).** ✓

> Let $`\Phi`$ succeed on a multi-solution set’s chain, with result $`M`$. Two assignments that respect and cover exactly the cells, and give the same database, are equal.

Uses: [Definition 13.7](#def-r2-phi-msol), [Theorem 13.10](#thm-r2-phi-cells).<br>
Lean: [`Rasso.Phi.msol_cells_inj`](../Rasso/Phi/Theorems/MsolLift.lean#L701-L723).<br>
[Proof sketch](proofs.md#sketch-thm-r2-phi-msol-cells).

<a id="thm-r2-phi-msol-key"></a>

**Theorem 13.16 (K for databases).** ✓

> Let $`\Phi`$ succeed on the key of an $`\mathcal{E}_{\mathrm{msol}}`$ statement, with result $`M`$ and term $`t`$. For every assignment $`x`$ that respects the cells, $`t`$ evaluates on $`x`$ to a value $`v`$, and the evaluator’s key on $`\mathrm{msubst}(M, x)`$ is $`v`$.

Uses: [Definition 13.7](#def-r2-phi-msol), [Definition 11.2](msol.md#def-r2-msol-ops).<br>
Lean: [`Rasso.Phi.phiMsolKey`](../Rasso/Phi/Phi.lean#L849-L865), [`Rasso.Phi.keyValueMsol`](../Rasso/Phi/Phi.lean#L867-L871), [`Rasso.Phi.phiMsolKey_sound`](../Rasso/Phi/Theorems/MsolLift.lean#L34-L87).<br>
[Proof sketch](proofs.md#sketch-thm-r2-phi-msol-key).
