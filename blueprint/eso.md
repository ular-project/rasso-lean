<a id="chap-r2-eso"></a>
# 12 Selection on Boolean function spaces and existential second-order logic

This chapter relates Rasso to existential second-order sentences over finite structures. Full Rasso says more than these sentences. It has objectives and enumeration, it compares values with $`{\lt}`$, it computes with $`+`$, and it aggregates with $`\gamma`$. A program with an objective states an optimisation problem, and the matching question is about NP optimisation problems, not NP properties: a later question, on which logical accounts exist [[43](references.md#kolaitis_1994_logical.definability.np.optimization.problems)]. So the claim “Rasso is exactly existential second-order logic” is not true of the whole language, and we do not make it. The result is about yes/no properties, “does the program have a candidate?”, and has two parts.

- **Rasso states every existential second-order property.** For each sentence, one Rasso program states it. The sentence fixes the program; the structure enters only as data (Theorems [12.11](#thm-r2-eso-forward) and [12.12](#thm-r2-eso-program)).
- **A named subalgebra of Rasso states exactly these properties.** *Selection on Boolean function spaces* (Definition [12.7](#def-r2-eso-boolsel)) is a set of Rasso statements. Every program in it states a property that a sentence defines (Theorem [12.15](#thm-r2-eso-boolsel-converse)). Every sentence has a program in it (Theorem [12.16](#thm-r2-eso-same)).

By Fagin’s theorem [[22](references.md#fagin_1974_generalized.first.order.spectra.polynomial), Theorem 6], a class of finite structures that is closed under isomorphism is defined by an existential second-order sentence exactly when it is in NP. So the Boolean selection programs state exactly the NP properties. Fagin’s theorem itself is cited, not proved here. All the other theorems of this chapter are proved in the Lean library, in `Rasso/ESO/`, with no `sorry`.

The idea is not new. The second-order variables become members; the first-order part becomes the condition, by Codd’s translation of the relational calculus into the relational algebra [[19](references.md#codd_1972_relational.completeness.data.base.sublanguages)], [[1](references.md#abiteboul_1995_foundations.of.databases), ch. 5]. NP-Alg uses the same idea: it guesses relations $`Q`$ over the domain, and a program holds when, for some guess, a relation called FAIL is empty [[51](references.md#mancini_2004_declarative.constraint.modelling.specification.level), § 8.2, Definitions 8.2.1 and 8.2.2]. Koch proves that world-set algebra captures second-order logic by the same construction, one guess for each second-order quantifier [[42](references.md#koch_2009_compositional.query.algebra.second.order), Theorem 4.1], and Biskup et al. reach the NP properties through Fagin’s theorem, as this chapter does [[10](references.md#biskup_2004_solving.equations.in.relational.algebra), § 6]. Their algebras as a whole reach further: Koch’s captures second-order logic, and the equation algebra is the powerset algebra. What this chapter adds is a proof about Rasso’s own evaluator: the multi-solution set that the construction writes is evaluated by `Expr.eval`, the same function that runs every Rasso program.

<a id="sec-r2-eso-logic"></a>
## 12.1 The logic

<a id="def-r2-eso-str"></a>

**Definition 12.1 (Structure).** ✓

> A *structure* $`A`$ is a finite list of values, the *universe*, and for each relation symbol $`i`$ a finite list of tuples of values, $`A(i)`$. A structure is *well formed* when every entry of every tuple is in the universe.

Uses: [Definition 4.1](values.md#def-r2-value).<br>
Lean: [`Rasso.ESO.Str`](../Rasso/ESO/Logic.lean#L67-L70), [`Rasso.ESO.Str.WF`](../Rasso/ESO/Logic.lean#L72-L73).

A formula in conjunctive normal form is a structure. Its universe holds its variables and its clauses; $`C(c)`$ says that $`c`$ is a clause, $`P(c, x)`$ that $`x`$ occurs positively in $`c`$, and $`N(c, x)`$ that it occurs negatively. The universe may be empty.

<a id="def-r2-eso-fo"></a>

**Definition 12.2 (First-order formula, satisfaction).** ✓

> A *first-order formula* is one of: $`i(x_1, \ldots , x_n)`$ for a relation symbol $`i`$; $`R(x_1, \ldots , x_n)`$ for a second-order variable $`R`$; $`x = y`$; $`\neg \varphi`$; $`\varphi \wedge \psi`$; $`\varphi \vee \psi`$; $`\exists x\, \varphi`$; $`\forall x\, \varphi`$. The variables $`x, y, \ldots`$ are first-order variables.
>
> A *guess* $`G`$ gives each second-order variable a finite list of tuples. A guess *fits* a list of arities when the guess for each listed variable holds tuples of its arity over the universe, and the guess for every other variable is empty.
>
> An *assignment* $`\rho`$ gives each first-order variable a value. $`A, G, \rho \models \varphi`$ is defined as usual. The quantifiers range over the universe. $`i(\bar x)`$ holds when $`\rho (\bar x) \in A(i)`$, and $`R(\bar x)`$ holds when $`\rho (\bar x) \in G(R)`$.

Uses: [Definition 12.1](#def-r2-eso-str).<br>
Lean: [`Rasso.ESO.FO`](../Rasso/ESO/Logic.lean#L88-L99), [`Rasso.ESO.FO.fv`](../Rasso/ESO/Logic.lean#L114-L123), [`Rasso.ESO.FO.Sat`](../Rasso/ESO/Logic.lean#L125-L134), [`Rasso.ESO.Guess.Fits`](../Rasso/ESO/Logic.lean#L83-L86).

<a id="def-r2-eso-sentence"></a>

**Definition 12.3 (Existential second-order sentence).** ✓

> An *existential second-order sentence* $`\exists R_1 \ldots \exists R_m\, \varphi`$ is a list of second-order variables with their arities and a first-order formula $`\varphi`$ with no free first-order variables. The sentence *holds* on $`A`$ when some guess that fits the arities satisfies $`\varphi`$.

Uses: [Definition 12.2](#def-r2-eso-fo).<br>
Lean: [`Rasso.ESO.Sentence`](../Rasso/ESO/Logic.lean#L197-L203), [`Rasso.ESO.Sentence.Holds`](../Rasso/ESO/Logic.lean#L205-L208).

SAT, the standard NP-complete problem, is defined by an existential second-order sentence with one second-order variable, $`T`$, the set of true variables. A formula is satisfiable when

```math
\exists T\;  \forall c\,  \Bigl(C(c) \rightarrow \exists x\,  \bigl[(P(c, x) \wedge T(x)) \vee (N(c, x) \wedge \neg T(x))\bigr]\Bigr)
```

holds on it. The formula $`x_1 \wedge (x_2 \vee \neg x_3)`$ is the structure with universe $`\{ x_1, x_2, x_3, c_1, c_2\}`$, $`C = \{ c_1, c_2\}`$, $`P = \{ (c_1, x_1), (c_2, x_2)\}`$ and $`N = \{ (c_2, x_3)\}`$: the clause $`c_1`$ is $`x_1`$, and $`c_2`$ is $`x_2 \vee \neg x_3`$. Section [12.6](#sec-r2-eso-examples) gives its program.

<a id="sec-12-2"></a>
## 12.2 The construction

The construction writes one multi-solution set for a sentence $`\psi`$ and a structure $`A`$. Every attribute in it has the same domain $`\mathrm{DD}_A`$: the universe, as a finite set. The one exception is the attribute `holds`, whose domain is `bool`.

<a id="def-r2-eso-compile"></a>

**Definition 12.4 (The translation of a formula).** ✓

> Let $`U`$ be the universe as a finite relation with one attribute `e`. For a list of variables $`\bar x`$, $`U^{\bar x}`$ is the join of one copy of $`U`$ for each variable $`x`$, the copy renamed to the attribute `x_`$`x`$. Its tuples are all the assignments to $`\bar x`$.
>
> The translation $`T(\varphi )`$ of a formula is a relational expression. Its attributes are `x_`$`x`$ for the free variables $`x`$ of $`\varphi`$.
>
> - $`T(i(x_1, \ldots , x_n))`$: join the data of symbol $`i`$ at arity $`n`$ (attributes `c0`, …, `c`$`(n{-}1)`$) with $`U^{\bar x}`$. Keep the tuples where each `c`$`k`$ equals `x_`$`x_{k+1}`$. Project onto the variables. A repeated variable, as in $`P(x, x)`$, needs no special case.
> - $`T(R(x_1, \ldots , x_n))`$: the same, on the member for $`R`$, and also keep only the tuples where `holds` is `true`. If $`R`$ is not listed at arity $`n`$, the result is the empty relation.
> - $`T(x = y)`$: $`\sigma _{x\_ x = x\_ y}(U^{x,y})`$, or $`U^{x}`$ when $`x`$ and $`y`$ are the same variable.
> - $`T(\neg \varphi ) = U^{\mathrm{fv}(\varphi )} - T(\varphi )`$.
> - $`T(\varphi \wedge \psi ) = T(\varphi ) \bowtie T(\psi )`$.
> - $`T(\varphi \vee \psi )`$: join each side with $`U`$ for the variables that only the other side has, then take the union.
> - $`T(\exists x\, \varphi )`$: join $`T(\varphi )`$ with $`U^{x}`$ if $`x`$ is not free in $`\varphi`$, then project away `x_`$`x`$.
> - $`T(\forall x\, \varphi )`$ is $`\neg \exists x\, \neg \varphi`$, written with two differences and one projection.

Uses: [Definition 12.2](#def-r2-eso-fo), [Definition 6.3](finite.md#def-r2-omega-rows), [Definition 6.4](finite.md#def-r2-spr), [Definition 6.5](finite.md#def-r2-join), [Definition 6.6](finite.md#def-r2-setops).<br>
Lean: [`Rasso.ESO.compileP`](../Rasso/ESO/Construction.lean#L47-L68), [`Rasso.ESO.compile`](../Rasso/ESO/ToProgram.lean#L152-L174), [`Rasso.ESO.compile_eq_compileP`](../Rasso/ESO/Construction.lean#L70-L80), [`Rasso.ESO.univLit`](../Rasso/ESO/Construction.lean#L84-L86), [`Rasso.ESO.relLit`](../Rasso/ESO/Construction.lean#L88-L89).

The extra join in $`\exists x\, \varphi`$ matters only when $`x`$ is not free in $`\varphi`$. Then it makes $`\exists x\, \varphi`$ false on an empty universe, as the logic says.

The Lean function `compileP` takes the universe and the data of each symbol as parameters. With named statements (`univ`, `rel_E_2`, …) as the parameters, it is the translation of the program `toProgram` (`compile_eq_compileP`). With the data written in place, as literals, it is the translation in the multi-solution set below.

<a id="def-r2-eso-form"></a>

**Definition 12.5 (The multi-solution set of a sentence).** ✓

> For a sentence $`\exists R_1 \ldots \exists R_m\, \varphi`$, with $`R_j`$ of arity $`k_j`$, and a structure $`A`$, the multi-solution set is
>
> ```math
> \omega _\mathrm {msol}[\mathtt{member\_}R_1\  U_1, \ldots , \mathtt{member\_}R_m\  U_m] (\gamma [][\mathtt{bool\_or}(\texttt{true})](T(\varphi )))
> ```
>
> where $`U_j = \omega _\mathrm{sol}(U^{k_j}, \omega [\texttt{holds}\ \texttt{bool}])`$. A candidate of $`U_j`$ gives each $`k_j`$-tuple of the universe the value `true` or `false`. That is a subset of the universe to the power $`k_j`$, which the logic calls a guess for $`R_j`$. The condition asks whether $`T(\varphi )`$ has a tuple. When the sentence has no second-order variables, one unused member of arity $`0`$ takes their place, because a multi-solution set needs at least one member.

Uses: [Definition 12.4](#def-r2-eso-compile), [Definition 12.3](#def-r2-eso-sentence), [Definition 11.1](msol.md#def-r2-msol), [Definition 9.1](sol.md#def-r2-sol), [Definition 6.8](finite.md#def-r2-gamma).<br>
Lean: [`Rasso.ESO.esoForm`](../Rasso/ESO/Construction.lean#L102-L105), [`Rasso.ESO.membersP`](../Rasso/ESO/Construction.lean#L95-L100), [`Rasso.ESO.nonEmpty`](../Rasso/ESO/ToProgram.lean#L176-L178), [`Rasso.ESO.toProgram`](../Rasso/ESO/ToProgram.lean#L204-L213).

The Rasso program `toProgram` is the same multi-solution set, with the data as named statements before it. Theorem [12.11](#thm-r2-eso-forward) is about the form with the data written in place, and Theorem [12.12](#thm-r2-eso-program) carries it to the program.

Rasso’s $`=`$ refuses to compare an exact number (an integer or a rational) with a float, and a symbol with a string. That is why the theorems of this chapter ask that the universe does not mix them (Theorem [12.10](#thm-r2-eso-codd)). On a universe that mixes them, they say nothing. The multi-solution set is refused when a comparison meets an exact number and a float, or a symbol and a string, and it can give the right answer when no comparison does.

So the construction is uniform (Theorem [12.12](#thm-r2-eso-program)). The sentence fixes the statement `eso`. The structure enters only as data: the universe and the symbols’ tuples.

<a id="sec-12-3"></a>
## 12.3 Selection on Boolean function spaces

The converse needs a class of programs to be about. The class is a grammar of Rasso forms. We state it twice: first as a query, the abstract syntax, and then as the Rasso statement that the query writes.

<a id="def-r2-eso-query"></a>

**Definition 12.6 (Boolean selection queries).** ✓

> A *query* lists second-order variables with arities, and a condition. The condition is built with `∧`, `∨` and `¬` from tests “this relation has a tuple”. Each relation is built from atoms (a symbol on variables, a second-order variable on variables, $`x = y`$) with $`\bowtie`$, $`\cup`$, $`-`$, the complement on the same variables, and $`\pi`$ that drops one variable. A query is *well formed* when the two sides of each $`\cup`$ and each $`-`$ have the same variables. The multi-solution set of a query on a structure has the members of Definition [12.5](#def-r2-eso-form) and this condition, with the data written in place.

Uses: [Definition 12.5](#def-r2-eso-form).<br>
Lean: [`Rasso.ESO.Query`](../Rasso/ESO/Converse.lean#L167-L171), [`Rasso.ESO.QE`](../Rasso/ESO/Converse.lean#L66-L81), [`Rasso.ESO.QC`](../Rasso/ESO/Converse.lean#L137-L143), [`Rasso.ESO.Query.WF`](../Rasso/ESO/Converse.lean#L173), [`Rasso.ESO.Query.form`](../Rasso/ESO/Converse.lean#L175-L177).

<a id="def-r2-eso-boolsel"></a>

**Definition 12.7 (Selection on Boolean function spaces).** ✓

> The *Boolean selection statement* of a well formed query $`Q`$ is the Rasso form that $`Q`$ writes when it reads the data by name: the universe as `univ`, and symbol $`i`$ at arity $`n`$ as `rel_`$`i`$`_`$`n`$. It is the multi-solution set
>
> ```math
> \omega _\mathrm {msol}[\mathtt{member\_}R_1\  U_1, \ldots , \mathtt{member\_}R_m\  U_m](c)
> ```
>
> where:
>
> - each member $`U_j`$ is $`\omega _\mathrm{sol}(\texttt{univ}^{k_j}, \omega [\texttt{holds}\ \texttt{bool}])`$, the Boolean function space $`\mathbb {B}^{U^{k_j}}`$: a candidate gives each $`k_j`$-tuple of the universe `true` or `false`, and so a set of $`k_j`$-tuples;
> - the condition $`c`$ is built with `∧`, `∨` and `¬` from tests $`\gamma [][\mathtt{bool\_or}(\texttt{true})](E)`$, “$`E`$ has a tuple”;
> - each relation $`E`$ is an atom, or $`E_1 \bowtie E_2`$, $`E_1 \cup E_2`$, $`E_1 - E_2`$, $`\texttt{univ}^{\bar x} - E_1`$, or $`\pi`$ that drops one attribute `x_`$`x`$;
> - an atom is the gadget of Definition [12.4](#def-r2-eso-compile) for $`i(\bar x)`$, $`R(\bar x)`$ or $`x = y`$, with `rel_`$`i`$`_`$`n`$ or the member `member_`$`R`$ as its base.
>
> A Rasso form is a *Boolean selection statement* when it is the Boolean selection statement of some well formed query. A *Boolean selection program* on a structure $`A`$ is the data statements of $`A`$ (`univ`, then `rel_`$`i`$`_`$`n`$ for each symbol that the statement reads), then one Boolean selection statement `eso`. The program *states* the property “`eso` has a candidate”.

Uses: [Definition 12.6](#def-r2-eso-query), [Definition 11.1](msol.md#def-r2-msol), [Definition 9.1](sol.md#def-r2-sol), [Definition 6.8](finite.md#def-r2-gamma), [Definition 6.5](finite.md#def-r2-join), [Definition 6.6](finite.md#def-r2-setops), [Definition 6.4](finite.md#def-r2-spr).<br>
Lean: [`Rasso.ESO.BoolSelection`](../Rasso/ESO/BoolSelection.lean#L136-L138), [`Rasso.ESO.Query.stmt`](../Rasso/ESO/BoolSelection.lean#L129-L131), [`Rasso.ESO.Query.formP`](../Rasso/ESO/BoolSelection.lean#L118-L121), [`Rasso.ESO.QE.toExprP`](../Rasso/ESO/BoolSelection.lean#L68-L78), [`Rasso.ESO.QC.toCondP`](../Rasso/ESO/BoolSelection.lean#L100-L105), [`Rasso.ESO.dataFor`](../Rasso/ESO/BoolSelection.lean#L140-L143), [`Rasso.ESO.runEso`](../Rasso/ESO/BoolSelection.lean#L147-L153).

The statement does not depend on the structure. It names the data and nothing else. So a Boolean selection program is uniform: one statement, many structures.

Algebraically, these statements are, up to equal value, the subalgebra of multi-solution sets generated by the Boolean function spaces $`\mathbb {B}^{U^k}`$ under two operations: product, which makes spaces the members of one $`\omega _\mathrm {msol}`$, and selection $`\sigma _\mathrm {msol}[c]`$ by a condition $`c`$ of Codd’s algebra, as above. Two laws make one statement enough for the whole subalgebra. Selection cascades, $`\sigma _\mathrm {msol}[d](\sigma _\mathrm {msol}[c](X)) = \sigma _\mathrm {msol}[c \wedge d](X)`$ (`Rasso.SolLaws.sigmaMsol_cascade`), and a condition written in $`\omega _\mathrm {msol}`$ is a selection, $`\omega _\mathrm {msol}[\bar m](c) = \sigma _\mathrm {msol}[c](\omega _\mathrm {msol}[\bar m])`$ (`Rasso.SolLaws.omegaMsol_some`). Selection also commutes, when both orders give a result, and is idempotent (`Rasso.SolLaws.sigmaMsol_comm`, `Rasso.SolLaws.sigmaMsol_idem`). That $`\sigma _\mathrm {msol}[\texttt{true}]`$ is the identity, and that a selection whose condition reads one member distributes over the product, are not proved in Lean. In the words of the logic, the members guess the second-order relations and the condition checks them: the guess and check phases of constraint modelling [[51](references.md#mancini_2004_declarative.constraint.modelling.specification.level), § 1.2].

The subalgebra is narrow, and we state its edges. Every member ranges over every subset of a power of the universe. Every attribute of a variable has the universe as its domain. The subalgebra has no arithmetic, no $`{\lt}`$, no aggregate other than the test “has a tuple”, no extend, no decision domain other than `bool`, no solution set built from another, no objective and no enumeration. It also fixes the names of statements and attributes. A program that renames them states the same property, but it is not a Boolean selection program.

Being a Boolean selection statement is a question about the text of a program, and it is decidable (Theorem [12.14](#thm-r2-eso-boolsel-decide)). Two other questions are about meaning. The first, “do these two programs state the same property?”, is undecidable, also for Boolean selection programs, by Trakhtenbrot’s theorem [[70](references.md#trakhtenbrot_1963_impossibility.algorithm.decision.problem.finite)]: a first-order sentence has a Boolean selection program, and that program states the same property as the program for “true” exactly when the sentence holds on every finite structure. The second is “does this program state the same property as some Boolean selection program?”. The argument for the first does not answer it, because every program in that argument is already a Boolean selection program. We expect that no procedure decides this question either. We have no argument for that, and the question is open.

The statement of $`Q_\psi`$ is not the statement `eso` of Theorem [12.12](#thm-r2-eso-program). The two are different forms, and both state the property that $`\psi`$ defines.

<a id="sec-12-4"></a>
## 12.4 Fagin’s theorem and NP

Fagin’s theorem says that a property of finite structures is in NP exactly when an existential second-order sentence defines it. Descriptive complexity takes this as a definition of NP that needs no machines [[38](references.md#immerman_1999_descriptive.complexity), [46](references.md#libkin_2004_elements.of.finite.model.theory)]. Recently, Senellart and Gnatenko [[63](references.md#senellart_2026_descriptive.complexity.lean.completeness.first)] have formalised descriptive complexity in Lean, with NP defined as the properties that existential second-order sentences define.

With that definition, Theorem [12.16](#thm-r2-eso-same) reads: the properties that Boolean selection programs (Definition [12.7](#def-r2-eso-boolsel)) state are exactly the properties in NP. Selection on Boolean function spaces is a named subalgebra of Rasso, not all of Rasso. Three points qualify this.

- **The same statement, not the same library.** Their library uses Mathlib’s model theory. This library uses core Lean only, with its own structures (Definition [12.1](#def-r2-eso-str)): lists of Rasso values, whose satisfaction is computable, so the definitions run and the examples are evaluated. So the statement here mirrors theirs. It does not import it, and no theorem here connects the two kinds of structure.
- **Renaming the elements.** Their properties do not change when the elements of a structure are renamed. The sentences of this chapter use elements only through equality, so they fit that setting. A Rasso program in general can also compare values with $`{\lt}`$ and compute with $`+`$, so it can state properties that change under renaming. Those properties are outside that setting, and outside this chapter’s theorems.
- **Fagin’s theorem is cited.** The step from existential second-order sentences to NP is Fagin’s theorem. It is not proved here, and no theorem here connects this library’s structures with the structures of a textbook proof.

Rasso states a problem; it does not solve it. A Boolean selection program states an NP property precisely, and how a solver decides it is outside the algebra.

<a id="sec-12-5"></a>
## 12.5 Limits

- **The converse holds for the subalgebra, and only the subalgebra.** Definition [12.7](#def-r2-eso-boolsel) and the text after it list what the subalgebra leaves out. Whether a wider subalgebra still states only existential second-order properties is open. The obvious candidates are rename, $`\sigma`$ with equality tests, named intermediate statements and other finite decision domains. We do not expect the converse for all of Rasso: a program that compares with $`{\lt}`$ or computes with $`+`$ can state a property that changes when the elements are renamed, and no sentence of this chapter does that.
- **Membership, not meaning.** Theorem [12.14](#thm-r2-eso-boolsel-decide) decides whether a form is a Boolean selection statement. It says nothing about a program outside the subalgebra that states the same property as one inside it. That question is about meaning, and it is open. The undecidability of equivalence above is about a different question: whether two programs state the same property.
- **Optimisation.** Objectives and enumeration are outside the subalgebra. This chapter is about yes/no properties only.
- **Exact numbers and floats, symbols and strings.** The theorems ask that the universe does not mix an exact number (an integer or a rational) with a float, nor a symbol with a string, because Rasso’s $`=`$ does not compare them. A sentence uses its elements only through equality, so renaming the elements of a structure (for example, to the integers $`1, \ldots , n`$) does not change whether the sentence holds. This renaming argument is not yet proved in Lean.
- **Meaning, not cost.** The evaluator lists every candidate. The theorems are about what a program states, not about how fast anything decides it. Rasso states a problem; how a solver decides it is outside the algebra.
- **Axioms.** The proof uses `propext`, `Quot.sound` and `Classical.choice`. The last comes from core Lean’s lemmas about `String`, the type of attribute names.

<a id="sec-r2-eso-examples"></a>
## 12.6 In $`\rho \alpha`$ and RassoLean terms

The construction writes an ordinary Rasso program. The example below is the program it writes for SAT, a Boolean selection program; Example [12.9](#ex-r2-sat) states the same property in idiomatic Rasso, outside the subalgebra.

<a id="ex-r2-sat-boolsel"></a>

**Example 12.8 (SAT as selection on Boolean function spaces).**

> For the sentence of SAT and the formula $`x_1 \wedge (x_2 \vee \neg x_3)`$, `toProgram` writes this program. Its names are those of the construction: `univ` is the universe; `rel_C_1`, `rel_P_2` and `rel_N_2` are the symbols $`C`$, $`P`$ and $`N`$ at their arities; `member_T` is the member for $`T`$; and `x_c` and `x_x` hold the first-order variables $`c`$ and $`x`$. In $`\rho \alpha`$:
>
> ```
> univ := ω[e {'c1, 'c2, 'x1, 'x2, 'x3}]({<'c1>, <'c2>, <'x1>, <'x2>, <'x3>})
> rel_C_1 := ω[c0 {'c1, 'c2, 'x1, 'x2, 'x3}]({<'c1>, <'c2>})
> rel_P_2 := ω[c0 {'c1, 'c2, 'x1, 'x2, 'x3}, c1 {'c1, 'c2, 'x1, 'x2, 'x3}]({
>     <'c1, 'x1>,
>     <'c2, 'x2>
> })
> rel_N_2 := ω[c0 {'c1, 'c2, 'x1, 'x2, 'x3}, c1 {'c1, 'c2, 'x1, 'x2, 'x3}]({
>     <'c2, 'x3>
> })
> eso := ω_msol[member_T ω_sol(ρ[e → c0](univ), ω[holds bool])](
>     γ[][bool_or(true)](
>         ω[]({<>})
>             − π[](
>                 ρ[e → x_c](univ)
>                     − (
>                         ρ[e → x_c](univ)
>                             − π[x_c](
>                                 σ[c0 = x_c](
>                                     rel_C_1 ⋈ ρ[e → x_c](univ)
>                                 )
>                             )
>                             ∪ π[x_c](
>                                 π[x_c, x_x](
>                                     σ[c0 = x_c ∧ c1 = x_x](
>                                         rel_P_2
>                                             ⋈ (
>                                                 ρ[e → x_c](univ)
>                                                     ⋈ ρ[e → x_x](univ)
>                                             )
>                                     )
>                                 )
>                                     ⋈ π[x_x](
>                                         σ[holds = true ∧ c0 = x_x](
>                                             member_T ⋈ ρ[e → x_x](univ)
>                                         )
>                                     )
>                                     ∪ π[x_c, x_x](
>                                         σ[c0 = x_c ∧ c1 = x_x](
>                                             rel_N_2
>                                                 ⋈ (
>                                                     ρ[e → x_c](univ)
>                                                         ⋈ ρ[e → x_x](univ)
>                                                 )
>                                         )
>                                     )
>                                         ⋈ (
>                                             ρ[e → x_x](univ)
>                                                 − π[x_x](
>                                                     σ[
>                                                         holds = true
>                                                             ∧ c0 = x_x](
>                                                         member_T
>                                                             ⋈ ρ[e → x_x](
>                                                                 univ
>                                                             )
>                                                     )
>                                                 )
>                                         )
>                             )
>                     )
>             )
>     )
> )
> ```
>
> As RassoLean terms:
>
> ```
> [("univ",
>   .omegaRows
>     [("e",
>       .set [.symbol "c1", .symbol "c2", .symbol "x1", .symbol "x2", .symbol "x3"])]
>     [[.symbol "c1"],
>      [.symbol "c2"],
>      [.symbol "x1"],
>      [.symbol "x2"],
>      [.symbol "x3"]]),
>  ("rel_C_1",
>   .omegaRows
>     [("c0",
>       .set [.symbol "c1", .symbol "c2", .symbol "x1", .symbol "x2", .symbol "x3"])]
>     [[.symbol "c1"], [.symbol "c2"]]),
>  ("rel_P_2",
>   .omegaRows
>     [("c0",
>       .set [.symbol "c1", .symbol "c2", .symbol "x1", .symbol "x2", .symbol "x3"]),
>      ("c1",
>       .set [.symbol "c1", .symbol "c2", .symbol "x1", .symbol "x2", .symbol "x3"])]
>     [[.symbol "c1", .symbol "x1"], [.symbol "c2", .symbol "x2"]]),
>  ("rel_N_2",
>   .omegaRows
>     [("c0",
>       .set [.symbol "c1", .symbol "c2", .symbol "x1", .symbol "x2", .symbol "x3"]),
>      ("c1",
>       .set [.symbol "c1", .symbol "c2", .symbol "x1", .symbol "x2", .symbol "x3"])]
>     [[.symbol "c2", .symbol "x3"]]),
>  ("eso",
>   .omegaMsol
>     [("member_T",
>       .omegaSol
>         (.rename [("e", "c0")] (.name "univ"))
>         (.omega [("holds", .kind .bool)]))]
>     (some
>        (.expr
>           (.gamma
>              []
>              (.agg "bool_or" (.val (.bool true)))
>              none
>              (.nary
>                 .except
>                 [.omegaRows [] [[]],
>                  .project
>                    []
>                    (.nary
>                       .except
>                       [.rename [("e", "x_c")] (.name "univ"),
>                        .nary
>                          .union
>                          [.nary
>                             .except
>                             [.rename [("e", "x_c")] (.name "univ"),
>                              .project
>                                ["x_c"]
>                                (.select
>                                   (.call "=" [.attr "c0", .attr "x_c"])
>                                   (.nary
>                                      .join
>                                      [.name "rel_C_1",
>                                       .rename [("e", "x_c")] (.name "univ")]))],
>                           .project
>                             ["x_c"]
>                             (.nary
>                                .union
>                                [.nary
>                                   .join
>                                   [.project
>                                      ["x_c", "x_x"]
>                                      (.select
>                                         (.call
>                                            "and"
>                                            [.call "=" [.attr "c0", .attr "x_c"],
>                                             .call "=" [.attr "c1", .attr "x_x"]])
>                                         (.nary
>                                            .join
>                                            [.name "rel_P_2",
>                                             .nary
>                                               .join
>                                               [.rename
>                                                  [("e", "x_c")]
>                                                  (.name "univ"),
>                                                .rename
>                                                  [("e", "x_x")]
>                                                  (.name "univ")]])),
>                                    .project
>                                      ["x_x"]
>                                      (.select
>                                         (.call
>                                            "and"
>                                            [.call
>                                               "="
>                                               [.attr "holds", .val (.bool true)],
>                                             .call "=" [.attr "c0", .attr "x_x"]])
>                                         (.nary
>                                            .join
>                                            [.name "member_T",
>                                             .rename
>                                               [("e", "x_x")]
>                                               (.name "univ")]))],
>                                 .nary
>                                   .join
>                                   [.project
>                                      ["x_c", "x_x"]
>                                      (.select
>                                         (.call
>                                            "and"
>                                            [.call "=" [.attr "c0", .attr "x_c"],
>                                             .call "=" [.attr "c1", .attr "x_x"]])
>                                         (.nary
>                                            .join
>                                            [.name "rel_N_2",
>                                             .nary
>                                               .join
>                                               [.rename
>                                                  [("e", "x_c")]
>                                                  (.name "univ"),
>                                                .rename
>                                                  [("e", "x_x")]
>                                                  (.name "univ")]])),
>                                    .nary
>                                      .except
>                                      [.rename [("e", "x_x")] (.name "univ"),
>                                       .project
>                                         ["x_x"]
>                                         (.select
>                                            (.call
>                                               "and"
>                                               [.call
>                                                  "="
>                                                  [.attr "holds", .val (.bool true)],
>                                                .call "=" [.attr "c0", .attr "x_x"]])
>                                            (.nary
>                                               .join
>                                               [.name "member_T",
>                                                .rename
>                                                  [("e", "x_x")]
>                                                  (.name "univ")]))]]])]])])))))]
> ```
>
> The implication $`C(c) \rightarrow \ldots`$ is a union with the complement of $`C`$, and each $`\forall`$ is a difference inside a difference. The structure has one universe, so `member_T` gives a truth value to every element, the clauses included: it has $`2^5 = 32`$ candidates. $`12`$ pass: the $`3`$ satisfying assignments of $`x_1, x_2, x_3`$, each with any values on $`c_1`$ and $`c_2`$. These are the answers of RassoLean’s evaluator, checked in `Rasso/ESO/Examples.lean`.

Uses: [Definition 12.4](#def-r2-eso-compile), [Definition 12.7](#def-r2-eso-boolsel).

<a id="ex-r2-sat"></a>

**Example 12.9 (SAT in idiomatic Rasso).**

> Stated more idiomatically, SAT steps outside the subalgebra. The construction gives one member to each second-order variable, so for SAT’s one variable it writes a multi-solution set of one member. Idiomatic Rasso uses a solution set. The program keeps the variables and the clauses apart, as `Vars` and `Clauses`, so its solution set `T` ranges over the variables only. It gives each occurrence of a variable its sign with `extend`, and it writes $`\forall`$ and $`\exists`$ as `bool_and` and `bool_or` over groups. For the formula of Example [12.8](#ex-r2-sat-boolsel), the data, read from the database $`D`$, is:
>
> | `Vars` |
> |---|
> | `v symbol` |
> | x1 |
> | x2 |
> | x3 |
>
> | `Clauses` |
> |---|
> | `c symbol` |
> | c1 |
> | c2 |
>
> | `P` |  |
> |---|---|
> | `v symbol` | `c symbol` |
> | x1 | c1 |
> | x2 | c2 |
>
> | `N` |  |
> |---|---|
> | `v symbol` | `c symbol` |
> | x3 | c2 |
>
> In $`\rho \alpha`$:
>
> ```
> Vars := db_ref[Vars](D)
> Clauses := db_ref[Clauses](D)
> P := db_ref[P](D)
> N := db_ref[N](D)
> 
> Lit := extend[true → sign](P) ∪ extend[false → sign](N)
> 
> T := ω_sol(Vars, ω[b bool])
> 
> Satisfying := σ_sol[
>     γ[][bool_and(ok) → ok](γ[c][bool_or(b = sign) → ok](T ⋈ Lit))](
>     T
> )
> ```
>
> As RassoLean terms:
>
> ```
> [("Vars", .dbRef "Vars" (.name "D")),
>  ("Clauses", .dbRef "Clauses" (.name "D")),
>  ("P", .dbRef "P" (.name "D")),
>  ("N", .dbRef "N" (.name "D")),
>  ("Lit",
>   .nary
>     .union
>     [.extend "sign" (.val (.bool true)) (.name "P"),
>      .extend "sign" (.val (.bool false)) (.name "N")]),
>  ("T", .omegaSol (.name "Vars") (.omega [("b", .kind .bool)])),
>  ("Satisfying",
>   .sigmaSol
>     (.expr
>        (.gamma
>           []
>           (.agg "bool_and" (.attr "ok"))
>           (some "ok")
>           (.gamma
>              ["c"]
>              (.agg "bool_or" (.call "=" [.attr "b", .attr "sign"]))
>              (some "ok")
>              (.nary .join [.name "T", .name "Lit"]))))
>     (.name "T"))]
> ```
>
> `Lit` gives each occurrence its sign. The condition groups by clause: a clause passes when the candidate gives one of its variables the value of its sign, and every clause must pass. The condition reads a clause through its literals, so the schema of the data asks that every clause has one: a clause with none would not be checked. `T` has $`2^3 = 8`$ candidates, and $`3`$ pass: the satisfying assignments $`(\top , \top , \top )`$, $`(\top , \top , \bot )`$ and $`(\top , \bot , \bot )`$ of $`x_1, x_2, x_3`$. RassoLean’s evaluator gives this answer.

Uses: [Definition 9.1](sol.md#def-r2-sol), [Definition 9.3](sol.md#def-r2-sigma-sol), [Definition 6.8](finite.md#def-r2-gamma), [Example 12.8](#ex-r2-sat-boolsel).

<a id="sec-12-7"></a>
## 12.7 Traditions to explore

We have yet to explore:

- logics for NP optimisation problems, such as that of Kolaitis and Thakur [[43](references.md#kolaitis_1994_logical.definability.np.optimization.problems)], against Rasso’s programs with objectives;
- descriptive complexity beyond NP, such as fixed-point logics for polynomial time [[38](references.md#immerman_1999_descriptive.complexity)], against parts of Rasso other than selection on Boolean function spaces.

Selection on Boolean function spaces writes a property as a condition on Boolean function spaces. The next chapter reads a solution set’s conditions as one constraint over its candidates, in the form a constraint solver takes.

<a id="properties"></a>
## Properties

Each property is proved in Lean, in `Rasso/ESO/`, except Fagin’s theorem, which is cited. Sketches of the proofs, and the lemmas they use, are in Section [A.9](proofs.md#sec-r2-proofs-eso).

<a id="thm-r2-eso-codd"></a>

**Theorem 12.10 (Codd’s theorem for the translation).** ✓

> Let $`A`$ be well formed, with no element an exact number (an integer or a rational) while another is a float, and no element a symbol while another is a string. Let $`G`$ be a guess that fits the arities, written into the members. Then for every formula $`\varphi`$, $`T(\varphi )`$ is not refused, and it represents the assignments to $`\mathrm{fv}(\varphi )`$ that satisfy $`\varphi`$. So the condition of the multi-solution set evaluates to `true` exactly when $`A, G \models \varphi`$.

Uses: [Lemma A.3](proofs.md#lem-r2-eso-repv-ops), [Lemma A.4](proofs.md#lem-r2-eso-atoms), [Definition 12.4](#def-r2-eso-compile).<br>
Lean: [`Rasso.ESO.compile_meaning`](../Rasso/ESO/Meaning.lean#L718-L811), [`Rasso.ESO.cond_meaning`](../Rasso/ESO/Meaning.lean#L813-L851).<br>
[Proof sketch](proofs.md#sketch-thm-r2-eso-codd).

<a id="thm-r2-eso-forward"></a>

**Theorem 12.11 (Forward: every sentence is a multi-solution set).** ✓

> Let $`\psi`$ be an existential second-order sentence and $`A`$ a well formed structure whose universe does not mix exact numbers with floats, nor symbols with strings. Then the multi-solution set of Definition [12.5](#def-r2-eso-form) evaluates, and it has a candidate exactly when $`\psi`$ holds on $`A`$.

Uses: [Theorem 12.10](#thm-r2-eso-codd), [Lemma A.5](proofs.md#lem-r2-eso-guesses).<br>
Lean: [`Rasso.ESO.esoForm_expresses`](../Rasso/ESO/Capture.lean#L20-L26).<br>
[Proof sketch](proofs.md#sketch-thm-r2-eso-forward).

<a id="thm-r2-eso-program"></a>

**Theorem 12.12 (The program: the structure enters only as data).** ✓

> The program `toProgram` for $`\psi`$ and $`A`$ is the data statements of $`A`$ (`univ`, and `rel_`$`i`$`_`$`n`$ for each symbol $`i`$ at each arity $`n`$), then one statement `eso` that depends only on $`\psi`$. Under the assumptions of Theorem [12.11](#thm-r2-eso-forward), the program runs, and `eso` has a candidate exactly when $`\psi`$ holds on $`A`$.

Uses: [Theorem 12.11](#thm-r2-eso-forward), [Definition 12.5](#def-r2-eso-form).<br>
Lean: [`Rasso.ESO.toProgram_eq`](../Rasso/ESO/Program.lean#L450-L455), [`Rasso.ESO.esoStmt`](../Rasso/ESO/Program.lean#L445-L448), [`Rasso.ESO.toProgram_expresses`](../Rasso/ESO/Program.lean#L531-L553), [`Rasso.ESO.run_toProgram`](../Rasso/ESO/Program.lean#L517-L529), [`Rasso.ESO.decide_eq_runEso`](../Rasso/ESO/BoolSelection.lean#L155-L158).<br>
[Proof sketch](proofs.md#sketch-thm-r2-eso-program).

<a id="thm-r2-eso-converse"></a>

**Theorem 12.13 (Converse, for queries).** ✓

> For each well formed query $`Q`$ there is an existential second-order sentence $`\psi`$ such that, on every well formed structure $`A`$ whose universe does not mix exact numbers with floats, nor symbols with strings, the multi-solution set of $`Q`$ evaluates and has a candidate exactly when $`\psi`$ holds on $`A`$.

Uses: [Definition 12.6](#def-r2-eso-query), [Theorem 12.10](#thm-r2-eso-codd), [Lemma A.5](proofs.md#lem-r2-eso-guesses).<br>
Lean: [`Rasso.ESO.Query.form_expresses`](../Rasso/ESO/Converse.lean#L670-L680), [`Rasso.ESO.query_definable_in_ESO`](../Rasso/ESO/Converse.lean#L682-L687), [`Rasso.ESO.Converse.eval_QE`](../Rasso/ESO/Converse.lean#L507-L595), [`Rasso.ESO.Converse.eval_QC`](../Rasso/ESO/Converse.lean#L610-L653).<br>
[Proof sketch](proofs.md#sketch-thm-r2-eso-converse).

<a id="thm-r2-eso-boolsel-decide"></a>

**Theorem 12.14 (Being a Boolean selection statement is decidable).** ✓

> A procedure takes any Rasso form $`r`$ and answers whether $`r`$ is a Boolean selection statement. It answers “yes” exactly when it is.

Uses: [Definition 12.7](#def-r2-eso-boolsel).<br>
Lean: [`Rasso.ESO.isBoolSelection`](../Rasso/ESO/Recognise.lean#L324-L327), [`Rasso.ESO.isBoolSelection_iff`](../Rasso/ESO/Recognise.lean#L595-L606), [`Rasso.ESO.Recognise.queryCands`](../Rasso/ESO/Recognise.lean#L267-L273), [`Rasso.ESO.Recognise.queryCands_complete`](../Rasso/ESO/Recognise.lean#L577-L589), [`Rasso.ESO.QE.wfb_iff`](../Rasso/ESO/Recognise.lean#L294-L304), [`Rasso.FormEq.decExpr`](../Rasso/FormEq.lean#L20-L594).<br>
[Proof sketch](proofs.md#sketch-thm-r2-eso-boolsel-decide).

<a id="thm-r2-eso-boolsel-converse"></a>

**Theorem 12.15 (Converse, for Rasso programs).** ✓

> For each Boolean selection statement $`r`$ there is an existential second-order sentence $`\psi`$ with this property. On every well formed structure $`A`$ whose universe does not mix exact numbers with floats, nor symbols with strings, the Boolean selection program with statement $`r`$ runs, and `eso` has a candidate exactly when $`\psi`$ holds on $`A`$.

Uses: [Definition 12.7](#def-r2-eso-boolsel), [Theorem 12.13](#thm-r2-eso-converse), [Theorem 12.12](#thm-r2-eso-program).<br>
Lean: [`Rasso.ESO.boolSelection_definable_in_ESO`](../Rasso/ESO/BoolSelection.lean#L260-L268), [`Rasso.ESO.Query.stmt_expresses`](../Rasso/ESO/BoolSelection.lean#L245-L258), [`Rasso.ESO.query_stmt`](../Rasso/ESO/BoolSelection.lean#L208-L215).<br>
[Proof sketch](proofs.md#sketch-thm-r2-eso-boolsel-converse).

<a id="thm-r2-eso-same"></a>

**Theorem 12.16 (ESO is selection on Boolean function spaces).** ✓

> Every existential second-order sentence $`\psi`$ is a well formed query $`Q_\psi`$ with the same meaning, so its Boolean selection statement states the property that $`\psi`$ defines. Take the well formed structures whose universes do not mix exact numbers with floats, nor symbols with strings. On them, an existential second-order sentence defines a property exactly when a Boolean selection program states it.

Uses: [Theorem 12.11](#thm-r2-eso-forward), [Theorem 12.13](#thm-r2-eso-converse), [Theorem 12.15](#thm-r2-eso-boolsel-converse), [Definition 12.7](#def-r2-eso-boolsel).<br>
Lean: [`Rasso.ESO.Sentence.toQuery`](../Rasso/ESO/SentenceQuery.lean#L144-L145), [`Rasso.ESO.Sentence.toQuery_holds`](../Rasso/ESO/SentenceQuery.lean#L149-L165), [`Rasso.ESO.Sentence.toQuery_stmt_expresses`](../Rasso/ESO/BoolSelection.lean#L270-L276), [`Rasso.ESO.eso_iff_query`](../Rasso/ESO/SentenceQuery.lean#L167-L185), [`Rasso.ESO.eso_iff_boolSelection`](../Rasso/ESO/BoolSelection.lean#L278-L297).<br>
[Proof sketch](proofs.md#sketch-thm-r2-eso-same).
