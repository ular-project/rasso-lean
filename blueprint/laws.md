<a id="chap-r2-laws"></a>
# B The laws of the Rasso algebras

This appendix lists the algebraic laws of each Rasso algebra: finite relations, unrestricted relations, solution sets, multi-solution sets, and the boundary operators. It covers the laws of the algebras of the Rasso paper [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation)], as extended by this technical report. Each law has a status. The chapters cite results from this appendix; its laws are not needed to follow them.

The Lean proofs of these laws were developed with Claude (Anthropic). Lean checks each proof against its statement. The proofs, and whether the statements say what we intend, are being investigated, and we welcome readers’ checks.

The tables are long. A reader who wants one law can search for its operator. A reader who wants to comment on a status, or knows a reference for a law, is invited to do so.

<a id="sec-r2-laws-how"></a>
## B.1 How a law is stated

<a id="sec-r2-laws-how-when-both-sides-succeed"></a>
**When both sides succeed.**

A Rasso operator can refuse its operands, for example $`\cup`$ of two relations with different headings. A law says: when both sides succeed, they give the same result. Where a row has a *definedness* note, it says whether the two sides refuse together, or which can succeed alone, with a named example.

<a id="sec-r2-laws-how-the-same-result"></a>
**The same result.**

Two finite relations are the same when their bodies are equal; the laws are proved for the bodies, and for the headings only where a row says so. The order of a heading does not change which tuples a relation holds. Two unrestricted relations are the same when they hold the same tuples, the equivalence of Chapter [7](unrestricted.md).

<a id="sec-r2-laws-how-total-relations"></a>
**Total relations.**

An unrestricted relation is *total* when its term does not refuse on a tuple that fits its heading. The laws of $`\cup`$ and $`-`$ on unrestricted relations are stated for total relations. Examples show where they fail without it.

<a id="sec-r2-laws-how-selections-on-tests"></a>
**Selections on tests.**

$`\sigma _\mathrm{sol}`$ and $`\sigma _{\mathrm{msol}}`$ keep the candidates that pass a test, and the test can refuse. Their laws are proved once, for a list of any kind of candidate. A written condition of $`\sigma _\mathrm{sol}`$ names its candidate by repeating the form of its operand. So a law that swaps two written selections is not literally a law about forms. The condition of $`\sigma _{\mathrm{msol}}`$ names members, so its laws hold of written forms.

<a id="sec-r2-laws-how-targets"></a>
**Targets.**

A law about written forms holds when no form in it is a *target* of the evaluator: a position that stands for the candidate. This is true for every form evaluated at the top of a program.

<a id="sec-r2-laws-how-status"></a>
**Status.**

Each law has one status.

**Proved.** A Lean theorem states it. The table names the theorem.

**Checked.** A closed instance is checked by `#guard`.

**Argued.** A short argument is given, and the law is not formalised.

**Open.** Nobody has proved it or found a counterexample.

**Fails.** A named example, checked by `#guard`, shows that it fails.

**Definition.** The row names a construct, not a law. It is listed so that each construct has a row.

**By construction.** The law holds because of how the construct is built (for example, every operator respects equal bodies, because a body is a quotient).

**No operator.** Rasso does not have the operator.

**Not carried over.** The earlier formulation had the form; Rasso has no counterpart.

The tables write each Lean name without its first part, `Rasso`.

<a id="sec-r2-laws-finite"></a>
## B.2 Finite relations

These are the laws of Codd’s relational algebra ([[19](references.md#codd_1972_relational.completeness.data.base.sublanguages)], a closed set of operators; [[20](references.md#codd_1970_relational.model.data.large.shared)] has some of them), for Rasso’s finite relations (Chapter [6](finite.md)). The standard algebraic equivalences are in textbooks [[1](references.md#abiteboul_1995_foundations.of.databases), the chapter on the algebra and on optimisation]. TABLE\_DEE and TABLE\_DUM are Darwen’s [[21](references.md#date_2007_databases.types.relational.model.third)]: DEE is the identity of $`\bowtie`$, and $`r \bowtie \mathrm{DUM}`$ is the empty relation over the heading of $`r`$.

<a id="proposition-B-1"></a>

**Proposition B.1 (Proved laws of finite relations).** ✓

> The laws marked Proved in the table below.

Lean: [`Rasso.FinrelLaws.dee`](../Rasso/Laws/Finrel.lean#L36-L37), [`Rasso.FinrelLaws.dum`](../Rasso/Laws/Finrel.lean#L39-L40), [`Rasso.FinrelLaws.empty`](../Rasso/Laws/Finrel.lean#L42-L43), [`Rasso.FinrelLaws.nullary_dee_or_dum`](../Rasso/Laws/Finrel.lean#L591-L611), [`Rasso.FinrelLaws.SameHeading.trans`](../Rasso/Laws/Finrel.lean#L64-L66), [`Rasso.FinrelLaws.SameHeading.refl`](../Rasso/Laws/Finrel.lean#L75-L77), [`Rasso.FinrelLaws.SameHeading.symm`](../Rasso/Laws/Finrel.lean#L79-L90), [`Rasso.FinrelLaws.union_comm`](../Rasso/Laws/Finrel.lean#L95-L96), [`Rasso.FinrelLaws.union_comm_heading`](../Rasso/Laws/Finrel.lean#L114-L117), [`Rasso.FinrelLaws.union_comm_ok`](../Rasso/Laws/Finrel.lean#L119-L123), [`Rasso.FinrelLaws.union_assoc`](../Rasso/Laws/Finrel.lean#L98-L101), [`Rasso.FinrelLaws.union_idem`](../Rasso/Laws/Finrel.lean#L103-L106), [`Rasso.FinrelLaws.union_empty`](../Rasso/Laws/Finrel.lean#L108-L112), [`Rasso.FinrelLaws.inter_comm`](../Rasso/Laws/Finrel.lean#L127-L128), [`Rasso.FinrelLaws.inter_assoc`](../Rasso/Laws/Finrel.lean#L130-L133), [`Rasso.FinrelLaws.inter_idem`](../Rasso/Laws/Finrel.lean#L135-L138), [`Rasso.FinrelLaws.join_same_heading`](../Rasso/Laws/Finrel.lean#L320-L335), [`Rasso.FinrelLaws.inter_eq_diff_diff`](../Rasso/Laws/Finrel.lean#L140-L146), [`Rasso.FinrelLaws.union_inter_absorb`](../Rasso/Laws/Finrel.lean#L148-L154), [`Rasso.FinrelLaws.inter_union_absorb`](../Rasso/Laws/Finrel.lean#L156-L162), [`Rasso.FinrelLaws.union_inter_distrib`](../Rasso/Laws/Finrel.lean#L164-L167), [`Rasso.FinrelLaws.inter_union_distrib`](../Rasso/Laws/Finrel.lean#L169-L172), [`Rasso.FinrelLaws.diff_self`](../Rasso/Laws/Finrel.lean#L176-L177), [`Rasso.FinrelLaws.diff_empty`](../Rasso/Laws/Finrel.lean#L179-L183), [`Rasso.FinrelLaws.empty_diff`](../Rasso/Laws/Finrel.lean#L185-L186), [`Rasso.FinrelLaws.diff_union`](../Rasso/Laws/Finrel.lean#L188-L192), [`Rasso.FinrelLaws.union_diff`](../Rasso/Laws/Finrel.lean#L194-L198), [`Rasso.Finrel.join_comm`](../Rasso/Laws.lean#L168-L185), [`Rasso.FinrelLaws.join_comm_heading`](../Rasso/Laws/Finrel.lean#L644-L658), [`Rasso.Finrel.join_assoc`](../Rasso/Laws.lean#L187-L212), [`Rasso.FinrelLaws.join_idem`](../Rasso/Laws/Finrel.lean#L254-L267), [`Rasso.FinrelLaws.join_dee`](../Rasso/Laws/Finrel.lean#L269-L278), [`Rasso.FinrelLaws.dee_join`](../Rasso/Laws/Finrel.lean#L280-L289), [`Rasso.FinrelLaws.join_dum`](../Rasso/Laws/Finrel.lean#L300-L301), [`Rasso.FinrelLaws.dum_join`](../Rasso/Laws/Finrel.lean#L303-L304), [`Rasso.FinrelLaws.join_empty_left`](../Rasso/Laws/Finrel.lean#L296-L298), [`Rasso.FinrelLaws.join_empty_right`](../Rasso/Laws/Finrel.lean#L291-L294), [`Rasso.FinrelLaws.join_union`](../Rasso/Laws/Finrel.lean#L306-L318), [`Rasso.FinrelLaws.join_diff`](../Rasso/Laws/Finrel.lean#L568-L589), [`Rasso.FinrelLaws.product_eq_join`](../Rasso/Laws/Finrel.lean#L711-L716), [`Rasso.FinrelLaws.product_ok_disjoint`](../Rasso/Laws/Finrel.lean#L718-L724), [`Rasso.FinrelLaws.select_comm`](../Rasso/Laws/Finrel.lean#L351-L355), [`Rasso.FinrelLaws.select_idem`](../Rasso/Laws/Finrel.lean#L357-L365), [`Rasso.FinrelLaws.select_idem_ok`](../Rasso/Laws/Finrel.lean#L367-L370), [`Rasso.FinrelLaws.select_cascade`](../Rasso/Laws/Finrel.lean#L372-L375), [`Rasso.FinrelLaws.select_cascade_ok`](../Rasso/Laws/Finrel.lean#L662-L693), [`Rasso.Finrel.select_union`](../Rasso/Laws.lean#L214-L219), [`Rasso.FinrelLaws.select_union_ok`](../Rasso/Laws/Finrel.lean#L695-L707), [`Rasso.FinrelLaws.select_diff`](../Rasso/Laws/Finrel.lean#L377-L381), [`Rasso.FinrelLaws.select_inter`](../Rasso/Laws/Finrel.lean#L383-L387), [`Rasso.FinrelLaws.select_true`](../Rasso/Laws/Finrel.lean#L389-L393), [`Rasso.FinrelLaws.select_false`](../Rasso/Laws/Finrel.lean#L395-L397), [`Rasso.FinrelLaws.select_const_ok`](../Rasso/Laws/Finrel.lean#L399-L401), [`Rasso.Finrel.select_join`](../Rasso/Laws.lean#L221-L235), [`Rasso.FinrelLaws.project_self`](../Rasso/Laws/Finrel.lean#L423-L435), [`Rasso.FinrelLaws.project_project`](../Rasso/Laws/Finrel.lean#L437-L454), [`Rasso.FinrelLaws.project_union`](../Rasso/Laws/Finrel.lean#L456-L468), [`Rasso.FinrelLaws.project_empty`](../Rasso/Laws/Finrel.lean#L470-L472), [`Rasso.FinrelLaws.project_mono`](../Rasso/Laws/Finrel.lean#L474-L479), [`Rasso.FinrelLaws.project_nil_dee`](../Rasso/Laws/Finrel.lean#L481-L489), [`Rasso.FinrelLaws.project_nil_dum`](../Rasso/Laws/Finrel.lean#L491-L494), [`Rasso.FinrelLaws.project_join_sub`](../Rasso/Laws/Finrel.lean#L496-L517), [`Rasso.FinrelLaws.rename_nil`](../Rasso/Laws/Finrel.lean#L535-L549), [`Rasso.FinrelLaws.rename_union`](../Rasso/Laws/Finrel.lean#L521-L533), [`Rasso.FinrelLaws.rename_diff`](../Rasso/Laws/Finrel.lean#L760-L776), [`Rasso.FinrelLaws.rename_inter`](../Rasso/Laws/Finrel.lean#L778-L793).

<a id="example-B-2"></a>

**Example B.2 (Examples).** ✓

> The examples named in the table below, each checked by `#guard`.

Lean: [`Rasso.FinrelLaws.Examples.union_self_gap`](../Rasso/Laws/FinrelExamples.lean#L76), [`Rasso.FinrelLaws.Examples.union_not_eq_comm`](../Rasso/Laws/FinrelExamples.lean#L40-L43), [`Rasso.FinrelLaws.Examples.absorb_gap`](../Rasso/Laws/FinrelExamples.lean#L114-L115), [`Rasso.FinrelLaws.Examples.diff_not_comm`](../Rasso/Laws/FinrelExamples.lean#L46-L47), [`Rasso.FinrelLaws.Examples.diff_not_assoc`](../Rasso/Laws/FinrelExamples.lean#L109-L111), [`Rasso.FinrelLaws.Examples.join_assoc_gap`](../Rasso/Laws/FinrelExamples.lean#L86-L89), [`Rasso.FinrelLaws.Examples.join_union_gap`](../Rasso/Laws/FinrelExamples.lean#L120-L121), [`Rasso.FinrelLaws.Examples.select_comm_gap`](../Rasso/Laws/FinrelExamples.lean#L98-L100), [`Rasso.FinrelLaws.Examples.select_diff_gap`](../Rasso/Laws/FinrelExamples.lean#L105-L106), [`Rasso.FinrelLaws.Examples.project_cascade_gap`](../Rasso/Laws/FinrelExamples.lean#L130-L131), [`Rasso.FinrelLaws.Examples.project_union_gap`](../Rasso/Laws/FinrelExamples.lean#L126-L127), [`Rasso.FinrelLaws.Examples.project_diff_fails`](../Rasso/Laws/FinrelExamples.lean#L57-L59), [`Rasso.FinrelLaws.Examples.project_inter_fails`](../Rasso/Laws/FinrelExamples.lean#L62-L64), [`Rasso.FinrelLaws.Examples.project_join_fails`](../Rasso/Laws/FinrelExamples.lean#L67-L68), [`Rasso.FinrelLaws.Examples.rename_join_gap`](../Rasso/Laws/FinrelExamples.lean#L134-L136).

| **Group** | **Law** | **Status** | **Lean** | **Definedness** |
|---|---|---|---|---|
| constants | DEE, DUM, $`\emptyset`$ over a heading | Definition | `FinrelLaws.dee`, `FinrelLaws.dum`, `FinrelLaws.empty` | — |
| constants | every WF nullary relation is DEE or DUM | Proved | `FinrelLaws.nullary_dee_or_dum` | — |
| congruence | $`\cup`$, $`-`$, $`\sigma`$, $`\pi`$, $`\rho`$, $`\bowtie`$, $`\gamma`$ respect equal bodies | By construction: a body is a quotient, so every operator respects it by construction | — | — |
| congruence | reordering an operand’s heading | Open | — | — |
| heading check | `SameHeading` transitive | Proved | `FinrelLaws.SameHeading.trans` | — |
| heading check | `SameHeading` reflexive, symmetric (no attribute twice) | Proved | `FinrelLaws.SameHeading.refl`, `FinrelLaws.SameHeading.symm` | gap without it: `FinrelLaws.Examples.union_self_gap` |
| $`\cup`$ | commutative | Proved | `FinrelLaws.union_comm`, heading `FinrelLaws.union_comm_heading` | both refuse (WF): `FinrelLaws.union_comm_ok` |
| $`\cup`$ | commutative as Lean `=` | Fails (heading order) | `FinrelLaws.Examples.union_not_eq_comm` | — |
| $`\cup`$ | associative | Proved | `FinrelLaws.union_assoc` | — |
| $`\cup`$ | idempotent | Proved | `FinrelLaws.union_idem` | — |
| $`\cup`$ | identity $`\emptyset`$ | Proved | `FinrelLaws.union_empty` | — |
| $`\cap`$ | commutative, associative, idempotent | Proved | `FinrelLaws.inter_comm`, `FinrelLaws.inter_assoc`, `FinrelLaws.inter_idem` | — |
| $`\cap`$ | $`\bowtie`$ on one heading is $`\cap`$ | Proved (WF) | `FinrelLaws.join_same_heading` | — |
| $`\cap`$ | r $`-`$ (r $`-`$ s) is $`\cap`$ | Proved | `FinrelLaws.inter_eq_diff_diff` | — |
| $`\cap`$ | absorption, both ways | Proved | `FinrelLaws.union_inter_absorb`, `FinrelLaws.inter_union_absorb` | gap: `FinrelLaws.Examples.absorb_gap` |
| $`\cap`$ | distributivity, both ways | Proved | `FinrelLaws.union_inter_distrib`, `FinrelLaws.inter_union_distrib` | — |
| $`-`$ | r $`-`$ r = $`\emptyset`$ | Proved | `FinrelLaws.diff_self` | — |
| $`-`$ | r $`-`$ $`\emptyset`$ = r; $`\emptyset`$ $`-`$ r = $`\emptyset`$ | Proved | `FinrelLaws.diff_empty`, `FinrelLaws.empty_diff` | — |
| $`-`$ | De Morgan r $`-`$ (s $`\cup`$ u) = (r $`-`$ s) $`-`$ u | Proved | `FinrelLaws.diff_union` | — |
| $`-`$ | (r $`\cup`$ s) $`-`$ u = (r $`-`$ u) $`\cup`$ (s $`-`$ u) | Proved | `FinrelLaws.union_diff` | — |
| $`-`$ | commutative | Fails | `FinrelLaws.Examples.diff_not_comm` | — |
| $`-`$ | associative | Fails | `FinrelLaws.Examples.diff_not_assoc` | — |
| $`-`$ | top and complement | Argued: a top exists exactly when every domain of the heading lists its values (`Domain.values?`) or some domain is empty, as in the paper’s argument | — | — |
| $`\bowtie`$ | commutative (bodies) | Proved (WF) | `Finrel.join_comm` | — |
| $`\bowtie`$ | commutative (headings: same attributes, same domain members) | Proved, for headings with no attribute twice | `FinrelLaws.join_comm_heading` | — |
| $`\bowtie`$ | associative | Proved (WF) | `Finrel.join_assoc` | gap: `FinrelLaws.Examples.join_assoc_gap` |
| $`\bowtie`$ | idempotent | Proved (WF) | `FinrelLaws.join_idem` | — |
| $`\bowtie`$ | identity DEE, both sides | Proved (WF) | `FinrelLaws.join_dee`, `FinrelLaws.dee_join` | — |
| $`\bowtie`$ | DUM gives $`\emptyset`$, both sides | Proved | `FinrelLaws.join_dum`, `FinrelLaws.dum_join` | — |
| $`\bowtie`$ | $`\emptyset`$ gives $`\emptyset`$, any headings (when the heading check passes) | Proved | `FinrelLaws.join_empty_left`, `FinrelLaws.join_empty_right` | — |
| $`\bowtie`$ | over $`\cup`$ | Proved | `FinrelLaws.join_union` | gap: `FinrelLaws.Examples.join_union_gap` |
| $`\bowtie`$ | over $`-`$ | Proved (WF) | `FinrelLaws.join_diff` | gap: as over $`\cup`$ |
| $`\times`$ | $`\times`$ is $`\bowtie`$ on headings with no shared attribute | Proved | `FinrelLaws.product_eq_join`, `FinrelLaws.product_ok_disjoint` | $`\times`$ refuses shared attributes |
| $`\sigma`$ | commutative | Proved | `FinrelLaws.select_comm` | gap: `FinrelLaws.Examples.select_comm_gap` |
| $`\sigma`$ | idempotent | Proved (as Lean `=`) | `FinrelLaws.select_idem` | both refuse: `FinrelLaws.select_idem_ok` |
| $`\sigma`$ | cascade $`\sigma _{\mathit{p}}`$ $`\sigma _{\mathit{q}}`$ = $`\sigma`$\_(q then p) | Proved | `FinrelLaws.select_cascade` | both refuse: `FinrelLaws.select_cascade_ok` |
| $`\sigma`$ | over $`\cup`$ | Proved | `Finrel.select_union` | both refuse: `FinrelLaws.select_union_ok` |
| $`\sigma`$ | over $`-`$ ($`\sigma _{\mathit{p}}`$(r $`-`$ s) = $`\sigma _{\mathit{p}}`$ r $`-`$ s) | Proved | `FinrelLaws.select_diff` | gap: `FinrelLaws.Examples.select_diff_gap` |
| $`\sigma`$ | over $`\cap`$ | Proved | `FinrelLaws.select_inter` | gap: as over $`-`$ |
| $`\sigma`$ | constant true, constant false | Proved | `FinrelLaws.select_true`, `FinrelLaws.select_false` | never refuses: `FinrelLaws.select_const_ok` |
| $`\sigma`$ | through $`\bowtie`$ (test reads only one side) | Proved, with "reads only one side" as a hypothesis | `Finrel.select_join` | gap: $`\sigma`$ tests fewer tuples on one side |
| $`\pi`$ | onto all attributes | Proved (WF) | `FinrelLaws.project_self` | — |
| $`\pi`$ | cascade | Proved, when the inner list holds the outer | `FinrelLaws.project_project` | gap: `FinrelLaws.Examples.project_cascade_gap` |
| $`\pi`$ | over $`\cup`$ | Proved | `FinrelLaws.project_union` | gap: `FinrelLaws.Examples.project_union_gap` |
| $`\pi`$ | of $`\emptyset`$ | Proved | `FinrelLaws.project_empty` | — |
| $`\pi`$ | monotone (by membership) | Proved | `FinrelLaws.project_mono` | — |
| $`\pi`$ | onto no attributes: DEE or DUM | Proved | `FinrelLaws.project_nil_dee`, `FinrelLaws.project_nil_dum` | — |
| $`\pi`$ | semijoin bound (by membership) | Proved (WF) | `FinrelLaws.project_join_sub` | — |
| $`\pi`$ | over $`-`$ | Fails | `FinrelLaws.Examples.project_diff_fails` | — |
| $`\pi`$ | over $`\cap`$ | Fails | `FinrelLaws.Examples.project_inter_fails` | — |
| $`\pi`$ | undoes $`\bowtie`$ | Fails (it is the semijoin) | `FinrelLaws.Examples.project_join_fails` | — |
| $`\pi`$ | through $`\bowtie`$ | Argued (standard) | — | — |
| $`\rho`$ | identity | Proved (WF) | `FinrelLaws.rename_nil` | — |
| $`\rho`$ | over $`\cup`$ | Proved | `FinrelLaws.rename_union` | — |
| $`\rho`$ | over $`-`$, over $`\cap`$ | Proved (WF) | `FinrelLaws.rename_diff`, `FinrelLaws.rename_inter` | — |
| $`\rho`$ | over $`\bowtie`$ | Argued: holds with the renaming split per operand; as written it can refuse on one side | — | gap: `FinrelLaws.Examples.rename_join_gap` |
| $`\rho`$ | composition | Argued | — | — |
| $`\gamma`$, extend | (only congruence in the earlier list) | By construction (as congruence) | — | — |

<a id="sec-r2-laws-unrestricted"></a>
## B.3 Unrestricted relations

An unrestricted relation is a heading and a term (Chapter [7](unrestricted.md)). Relations given by constraints and closed under the algebra are the constraint databases of Kanellakis, Kuper and Revesz [[40](references.md#kanellakis_1995_constraint.query.languages)], with an algebra by Goldin and Kanellakis [[31](references.md#goldin_1996_constraint.query.algebras)]. Their closure includes projection, by quantifier elimination. Rasso has $`\pi`$ on an unrestricted relation only for the classes it recognises.

For one heading, the total unrestricted relations satisfy the laws of a Boolean algebra; that they form one also needs the operators to respect equivalence, which is argued. The finite relations are then its ideal of finite elements.

<a id="proposition-B-3"></a>

**Proposition B.3 (Proved laws of unrestricted relations).** ✓

> The laws marked Proved in the table below.

Lean: [`Rasso.UnrelLaws.empty`](../Rasso/Laws/Unrel.lean#L42-L43), [`Rasso.UnrelLaws.dee`](../Rasso/Laws/Unrel.lean#L53-L54), [`Rasso.UnrelLaws.dum`](../Rasso/Laws/Unrel.lean#L55), [`Rasso.UnrelLaws.nullary_dee_or_dum`](../Rasso/Laws/Unrel.lean#L68-L83), [`Rasso.UnrelLaws.union_comm`](../Rasso/Laws/Unrel.lean#L87-L89), [`Rasso.UnrelLaws.union_assoc`](../Rasso/Laws/Unrel.lean#L91-L95), [`Rasso.UnrelLaws.union_idem`](../Rasso/Laws/Unrel.lean#L97-L98), [`Rasso.UnrelLaws.union_empty`](../Rasso/Laws/Unrel.lean#L100-L103), [`Rasso.UnrelLaws.union_top`](../Rasso/Laws/Unrel.lean#L105-L108), [`Rasso.UnrelLaws.inter_comm`](../Rasso/Laws/Unrel.lean#L112-L113), [`Rasso.UnrelLaws.inter_assoc`](../Rasso/Laws/Unrel.lean#L115-L118), [`Rasso.UnrelLaws.inter_idem`](../Rasso/Laws/Unrel.lean#L120-L121), [`Rasso.UnrelLaws.inter_top`](../Rasso/Laws/Unrel.lean#L123-L124), [`Rasso.UnrelLaws.join_eq_inter`](../Rasso/Laws/Unrel.lean#L319-L323), [`Rasso.UnrelLaws.inter_eq_diff_diff`](../Rasso/Laws/Unrel.lean#L176-L183), [`Rasso.UnrelLaws.union_inter_absorb`](../Rasso/Laws/Unrel.lean#L126-L129), [`Rasso.UnrelLaws.inter_union_absorb`](../Rasso/Laws/Unrel.lean#L131-L134), [`Rasso.UnrelLaws.union_inter_distrib`](../Rasso/Laws/Unrel.lean#L136-L140), [`Rasso.UnrelLaws.inter_union_distrib`](../Rasso/Laws/Unrel.lean#L142-L146), [`Rasso.UnrelLaws.diff_self`](../Rasso/Laws/Unrel.lean#L150-L153), [`Rasso.UnrelLaws.diff_empty`](../Rasso/Laws/Unrel.lean#L155-L157), [`Rasso.UnrelLaws.empty_diff`](../Rasso/Laws/Unrel.lean#L159-L162), [`Rasso.UnrelLaws.diff_union`](../Rasso/Laws/Unrel.lean#L164-L168), [`Rasso.UnrelLaws.union_diff`](../Rasso/Laws/Unrel.lean#L170-L174), [`Rasso.UnrelLaws.union_compl`](../Rasso/Laws/Unrel.lean#L187-L195), [`Rasso.UnrelLaws.inter_compl`](../Rasso/Laws/Unrel.lean#L197-L200), [`Rasso.UnrelLaws.compl_compl`](../Rasso/Laws/Unrel.lean#L202-L207), [`Rasso.UnrelLaws.join_comm`](../Rasso/Laws/Unrel.lean#L256-L264), [`Rasso.UnrelLaws.join_assoc`](../Rasso/Laws/Unrel.lean#L266-L293), [`Rasso.UnrelLaws.join_idem`](../Rasso/Laws/Unrel.lean#L335-L340), [`Rasso.UnrelLaws.join_dee`](../Rasso/Laws/Unrel.lean#L342-L353), [`Rasso.UnrelLaws.join_top`](../Rasso/Laws/Unrel.lean#L364-L370), [`Rasso.UnrelLaws.join_empty`](../Rasso/Laws/Unrel.lean#L355-L358), [`Rasso.UnrelLaws.empty_join`](../Rasso/Laws/Unrel.lean#L360-L362), [`Rasso.UnrelLaws.join_union`](../Rasso/Laws/Unrel.lean#L372-L406), [`Rasso.UnrelLaws.join_holds'`](../Rasso/Laws/Unrel.lean#L244-L254), [`Rasso.UnrelLaws.select_eq_join`](../Rasso/Laws/Unrel.lean#L325-L333), [`Rasso.UnrelLaws.select_comm`](../Rasso/Laws/Unrel.lean#L410-L414), [`Rasso.UnrelLaws.select_idem`](../Rasso/Laws/Unrel.lean#L416-L418), [`Rasso.UnrelLaws.select_union`](../Rasso/Laws/Unrel.lean#L420-L427), [`Rasso.UnrelLaws.select_diff`](../Rasso/Laws/Unrel.lean#L429-L433), [`Rasso.UnrelLaws.rename_union`](../Rasso/Laws/Unrel.lean#L437-L457), [`Rasso.FiniteClass.project_ok`](../Rasso/Classes.lean#L587-L592), [`Rasso.DenseClass.project_ok`](../Rasso/DenseClosure.lean#L359-L363), [`Rasso.EqClass.project_ok`](../Rasso/EqClosure.lean#L341-L345), [`Rasso.LinClass.project_ok`](../Rasso/LinClosure.lean#L587-L591), [`Rasso.project_sound`](../Rasso/Classes.lean#L485-L545), [`Rasso.UnrelLaws.project_union`](../Rasso/Laws/Unrel.lean#L461-L477), [`Rasso.UnrelLaws.toUnrel_union`](../Rasso/Laws/Unrel.lean#L481-L488), [`Rasso.UnrelLaws.toUnrel_diff`](../Rasso/Laws/Unrel.lean#L490-L496).

<a id="example-B-4"></a>

**Example B.4 (Examples).** ✓

> The examples named in the table below, each checked by `#guard`.

Lean: [`Rasso.UnrelLaws.Examples.congruence_needs_total`](../Rasso/Laws/UnrelExamples.lean#L49-L52), [`Rasso.UnrelLaws.Examples.union_top_needs_total`](../Rasso/Laws/UnrelExamples.lean#L44-L46), [`Rasso.UnrelLaws.Examples.absorb_needs_total`](../Rasso/Laws/UnrelExamples.lean#L60-L63), [`Rasso.UnrelLaws.Examples.union_compl_needs_total`](../Rasso/Laws/UnrelExamples.lean#L55-L57), [`Rasso.UnrelLaws.Examples.join_assoc_gap`](../Rasso/Laws/UnrelExamples.lean#L84-L85), [`Rasso.UnrelLaws.Examples.select_join_gap`](../Rasso/Laws/UnrelExamples.lean#L69-L70), [`Rasso.UnrelLaws.Examples.finite_select_gap`](../Rasso/Laws/UnrelExamples.lean#L77).

| **Group** | **Law** | **Status** | **Lean** | **Definedness / notes** |
|---|---|---|---|---|
| constants | $`\emptyset`$ over a heading (term `false`), $`\top`$ = `omega`, DEE, DUM | Definition | `UnrelLaws.empty`, `Unrel.omega`, `UnrelLaws.dee`, `UnrelLaws.dum` | — |
| constants | every total nullary relation is DEE or DUM (a two-element algebra) | Proved | `UnrelLaws.nullary_dee_or_dum` | — |
| congruence | $`\cup`$, $`-`$, $`\sigma`$, $`\bowtie`$ respect Same | Argued for total operands (every law below is stated by Same); Fails without totality | — | `UnrelLaws.Examples.congruence_needs_total` |
| $`\cup`$ | commutative, associative, idempotent | Proved (Total) | `UnrelLaws.union_comm`, `UnrelLaws.union_assoc`, `UnrelLaws.union_idem` | — |
| $`\cup`$ | identity $`\emptyset`$ | Proved (Total) | `UnrelLaws.union_empty` | — |
| $`\cup`$ | $`\cup`$ $`\top`$ = $`\top`$ | Proved (Total) | `UnrelLaws.union_top` | `UnrelLaws.Examples.union_top_needs_total` |
| $`\cap`$ | commutative, associative, idempotent | Proved | `UnrelLaws.inter_comm`, `UnrelLaws.inter_assoc`, `UnrelLaws.inter_idem` | — |
| $`\cap`$ | $`\cap`$ $`\top`$ is identity | Proved | `UnrelLaws.inter_top` | — |
| $`\cap`$ | $`\bowtie`$ on one heading is $`\cap`$ | Proved, as Lean equality of the two `Except` results | `UnrelLaws.join_eq_inter` | — |
| $`\cap`$ | r $`-`$ (r $`-`$ s) is $`\cap`$ | Proved (Total) | `UnrelLaws.inter_eq_diff_diff` | — |
| $`\cap`$ | absorption both ways | Proved (Total) | `UnrelLaws.union_inter_absorb`, `UnrelLaws.inter_union_absorb` | `UnrelLaws.Examples.absorb_needs_total` |
| $`\cap`$ | distributivity both ways | Proved (Total) | `UnrelLaws.union_inter_distrib`, `UnrelLaws.inter_union_distrib` | fails without totality, as absorption |
| $`-`$ | r $`-`$ r = $`\emptyset`$; r $`-`$ $`\emptyset`$ = r; $`\emptyset`$ $`-`$ r = $`\emptyset`$ | Proved (Total) | `UnrelLaws.diff_self`, `UnrelLaws.diff_empty`, `UnrelLaws.empty_diff` | r $`-`$ $`\emptyset`$ = r holds without totality (`UnrelLaws.diff_empty`) |
| $`-`$ | De Morgan; (r $`\cup`$ s) $`-`$ u | Proved (Total) | `UnrelLaws.diff_union`, `UnrelLaws.union_diff` | — |
| complement | u $`\cup`$ ($`\top`$ $`-`$ u) = $`\top`$; u $`\cap`$ ($`\top`$ $`-`$ u) = $`\emptyset`$; $`\top`$ $`-`$ ($`\top`$ $`-`$ u) = u | Proved (Total) | `UnrelLaws.union_compl`, `UnrelLaws.inter_compl`, `UnrelLaws.compl_compl` | `UnrelLaws.Examples.union_compl_needs_total` |
| lattice | per heading, total relations form a Boolean algebra: bottom $`\emptyset`$, top $`\top`$, the laws above | Follows from the rows above, with congruence (Argued) | — | not a law of its own: a summary of the rows above |
| lattice | $`\subseteq`$ is the lattice order | Argued | — | p $`\subseteq`$ q exactly when p $`\cap`$ q is the same as p; with $`\cap`$ as meet and $`\cup`$ as join, absorption (above) makes it the order of the lattice |
| $`\bowtie`$ | commutative (same tuples; headings with the same attributes and domain members) | Proved | `UnrelLaws.join_comm` (no attribute twice) | — |
| $`\bowtie`$ | associative | Proved | `UnrelLaws.join_assoc` (no attribute twice) | `UnrelLaws.Examples.join_assoc_gap` |
| $`\bowtie`$ | idempotent | Proved, for a heading with no attribute twice | `UnrelLaws.join_idem` | — |
| $`\bowtie`$ | identity DEE | Proved, for a heading with no attribute twice | `UnrelLaws.join_dee` | — |
| $`\bowtie`$ | r $`\bowtie`$ $`\top`$ = r on one heading | Proved, for a heading with no attribute twice | `UnrelLaws.join_top` | — |
| $`\bowtie`$ | $`\emptyset`$ and DUM give $`\emptyset`$, either side, any headings | Proved | `UnrelLaws.join_empty`, `UnrelLaws.empty_join` | DUM is `empty []` |
| $`\bowtie`$ | over $`\cup`$ | Proved (WF, Total) | `UnrelLaws.join_union` | — |
| $`\bowtie`$ | over $`-`$ | Argued: as over $`\cup`$, with `diff_holds` | — | — |
| $`\bowtie`$ | read off its term (no WF needed) | Proved | `UnrelLaws.join_holds'` | — |
| $`\sigma`$ | $`\sigma`$ is $`\bowtie`$ with an atom | Proved, as Lean equality (no attribute twice) | `UnrelLaws.select_eq_join` | `UnrelLaws.Examples.select_join_gap` |
| $`\sigma`$ | commutative, idempotent | Proved | `UnrelLaws.select_comm`, `UnrelLaws.select_idem` | — |
| $`\sigma`$ | over $`\cup`$ | Proved (Total, test total) | `UnrelLaws.select_union` | — |
| $`\sigma`$ | over $`-`$ | Proved (Total) | `UnrelLaws.select_diff` | — |
| $`\rho`$ | over $`\cup`$ | Proved (WF, Total) | `UnrelLaws.rename_union` | — |
| $`\rho`$ | over $`\cap`$, $`-`$; identity | Argued: as over $`\cup`$, through `rename_holds` and `rename_onto` | — | — |
| $`\rho`$ | over $`\bowtie`$ | Argued, as for finite relations | — | as finite |
| $`\pi`$ | "not an operation of Unrel" (earlier list) | Proved (the earlier "not an operation" is outdated): $`\pi`$ exists for relations in a recognised class | `FiniteClass.project_ok`, `DenseClass.project_ok`, `EqClass.project_ok`, `LinClass.project_ok`, `project_sound` | — |
| $`\pi`$ | over $`\cup`$ | Proved (WF, Total), when every operation succeeds | `UnrelLaws.project_union` | Open: which class accepts depends on the term |
| $`\pi`$ | cascade | Argued from `project_sound` | — | Open, as over $`\cup`$ |
| finite into unrestricted | `toUnrel` of $`\cup`$ and $`-`$ | Proved (WF, unmixed) | `UnrelLaws.toUnrel_union`, `UnrelLaws.toUnrel_diff` | — |
| finite into unrestricted | `toUnrel` of $`\cap`$, $`\bowtie`$ | Argued ($`\bowtie`$ needs `Domain.inter` to keep unmixed) | — | — |
| finite into unrestricted | `toUnrel` of $`\sigma`$ | Argued, when the finite $`\sigma`$ succeeds | — | `UnrelLaws.Examples.finite_select_gap` |
| finite ideal | finite extensions are closed under $`\cup`$ and downwards; $`\top`$ is finite exactly when every domain lists its values or some domain is empty | Argued | — | a subset of a finite relation holds at most its tuples, and a union of two finite relations holds theirs; $`\top`$ holds every tuple that fits, which is a finite list exactly when each domain lists its values, or none when some domain is empty |

<a id="sec-r2-laws-unrestricted-the-order-of-relations"></a>
**The order of relations.**

These facts are about the order $`\subseteq`$ on one heading, and about the *relational lattice* across headings of Spight and Tropashko [[67](references.md#spight_2006_first.steps.in.relational.lattice)], studied by Litak, Mikulás and Hidders [[47](references.md#litak_2014_relational.lattices.databases.universal.algebra)]. Inner union is $`\pi _{H_r \cap H_s} r \cup \pi _{H_r \cap H_s} s`$. It is not a Rasso operator.

| **Group** | **Law** | **Status** | **Lean** | **Notes** |
|---|---|---|---|---|
| one heading | atoms are one-tuple relations, so the algebra is atomic; atoms finite, coatoms cofinite | Argued | — | — |
| one heading | the unrestricted relations are more than the finite-or-cofinite ones (x $`{\lt}`$ y over two `int` attributes) | Argued | — | — |
| one heading | not a complete lattice: there are countably many terms, and an infinite heading has uncountably many sets of tuples, so some unions of atoms are not unrestricted relations | Argued | — | the evens are not a witness in Rasso: $`\omega`$\[x : int\] where x % 2 = 0 is an unrestricted relation |
| across headings | the relational lattice: r $`\le`$ s $`\Leftrightarrow`$ r $`\bowtie`$ s = r; meet $`\bowtie`$, join inner union $`\pi _{\mathit{H_r\, ∩\, H_s}}`$ r $`\cup`$ $`\pi _{\mathit{H_r\, ∩\, H_s}}`$ s (Spight and Tropashko; Litak, Mikulás and Hidders) | Argued, from $`\bowtie`$ comm, assoc, idem, identity DEE (finite: step 1) | — | inner union is not a Rasso operator; written with $`\pi`$ and $`\cup`$ |
| across headings | $`\top`$ is DEE; $`\bot`$ (the empty relation over all attributes) does not exist, as attribute names are unbounded | Argued | — | — |
| across headings | the empty relations form an upside-down copy of the headings: $`\emptyset _{\mathit{H}}`$ $`\le`$ $`\emptyset _{\mathit{K}}`$ iff K $`\subseteq`$ H | Argued from `join_empty_left/right` | — | — |
| across headings | DUM $`{\lt}`$ DEE with nothing between; r $`\le`$ DUM iff r is empty | Argued from `join_dum` | — | — |
| across headings | each per-heading Boolean algebra is the interval \[$`\emptyset _{\mathit{H}}`$, $`\top _{\mathit{H}}`$\] | Argued | — | — |
| across headings | finite relations are closed under $`\bowtie`$ and inner union | Argued ($`\pi`$, $`\cup`$ total on finite relations, up to refusals) | — | — |
| across headings | unrestricted relations: closed under $`\bowtie`$; inner union only where $`\pi`$ accepts the class | Argued | — | the earlier "meet-semilattice only" changes: Rasso’s $`\pi`$ succeeds on recognised classes |

<a id="sec-r2-laws-sol"></a>
## B.4 Solution sets

The solution-set operators are those of the Rasso paper [[58](references.md#pratten_2025_relational.algebras.subset.selection.optimisation)], in Rasso’s form (Chapter [9](sol.md)). The laws of exponents and why they matter are in Chapter [10](fspace.md).

<a id="sec-B-4-1"></a>
### B.4.1 Selection on a list of candidates

<a id="proposition-B-5"></a>

**Proposition B.5 (Selection on a list of candidates).** ✓

> The laws marked Proved in the table below.

Lean: [`Rasso.SolLaws.select_eq`](../Rasso/Laws/Sol.lean#L73-L76), [`Rasso.SolLaws.select_ok`](../Rasso/Laws/Sol.lean#L78-L82), [`Rasso.SolLaws.select_comm`](../Rasso/Laws/Sol.lean#L84-L90), [`Rasso.SolLaws.select_comm_ok`](../Rasso/Laws/Sol.lean#L140-L149), [`Rasso.SolLaws.select_idem`](../Rasso/Laws/Sol.lean#L92-L98), [`Rasso.SolLaws.select_cascade`](../Rasso/Laws/Sol.lean#L100-L119), [`Rasso.SolLaws.cond_and_two`](../Rasso/Laws/Sol.lean#L155-L171), [`Rasso.SolLaws.solTest_and`](../Rasso/Laws/Sol.lean#L173-L177), [`Rasso.SolLaws.msolTest_and`](../Rasso/Laws/Sol.lean#L179-L181), [`Rasso.SolLaws.select_sublist`](../Rasso/Laws/Sol.lean#L121-L124), [`Rasso.SolLaws.select_nodup`](../Rasso/Laws/Sol.lean#L126-L129), [`Rasso.SolLaws.select_true`](../Rasso/Laws/Sol.lean#L131-L133), [`Rasso.SolLaws.select_false`](../Rasso/Laws/Sol.lean#L135-L138), [`Rasso.sigmaSol_order`](../Rasso/FSpace.lean#L666-L673), [`Rasso.sigmaMsol_order`](../Rasso/FSpace.lean#L774-L778), [`Rasso.sigmaSol_meaning`](../Rasso/FSpace.lean#L651-L664), [`Rasso.sigmaMsol_meaning`](../Rasso/FSpace.lean#L762-L772).

<a id="example-B-6"></a>

**Example B.6 (Examples).** ✓

> The examples named in the table below, each checked by `#guard`.

Lean: [`Rasso.SolLaws.Examples.select_comm_gap`](../Rasso/Laws/SolExamples.lean#L42-L45), [`Rasso.SolLaws.Examples.nullary_tests_refused`](../Rasso/Laws/SolExamples.lean#L53-L57).

| **Group** | **Law** | **Status** | **Lean** | **Definedness / notes** |
|---|---|---|---|---|
| $`\sigma`$ | keeps the passing items, in the operand’s order | Proved | `SolLaws.select_eq` | — |
| $`\sigma`$ | refused exactly when the test refuses on some item | Proved | `SolLaws.select_ok` | $`\sigma _{\mathrm{sol}}`$ can also refuse before filtering: `has_subset` heading checks (`Cond.checkSubsets`) |
| $`\sigma`$ | commutative (Lean `=` of lists when both orders succeed) | Proved | `SolLaws.select_comm` | one order can succeed alone: `SolLaws.Examples.select_comm_gap`; when the second test is total on the operand, both succeed (`SolLaws.select_comm_ok`) |
| $`\sigma`$ | idempotent | Proved: if $`\sigma`$ succeeds, $`\sigma`$$`\sigma`$ gives the same list | `SolLaws.select_idem` | the converse ($`\sigma`$$`\sigma`$ succeeds, so $`\sigma`$ does) is immediate: the inner $`\sigma`$ is evaluated first |
| $`\sigma`$ | cascade: $`\sigma _{\mathit{p}}`$ $`\sigma _{\mathit{q}}`$ = $`\sigma _{\mathit{andThen\, q\, p}}`$ | Proved, both refused together | `SolLaws.select_cascade` | — |
| $`\sigma`$ | written `and [c, d]` is `andThen` of the two tests | Proved (`List.allM` stops at the first false) | `SolLaws.cond_and_two`, `SolLaws.solTest_and`, `SolLaws.msolTest_and` | — |
| $`\sigma`$ | decreasing; adds no repeats | Proved | `SolLaws.select_sublist`, `SolLaws.select_nodup` | — |
| $`\sigma`$ | identity (always true), zero (always false) | Proved | `SolLaws.select_true`, `SolLaws.select_false` | — |
| $`\sigma`$ | DEE test is identity, DUM test is zero (earlier list) | Not carried over: a written condition must give one value | — | refused: `SolLaws.Examples.nullary_tests_refused` |
| $`\sigma`$ | restrictions as DEE/DUM (earlier list, `Restr`) | Not carried over: Rasso has no `Restr`; a condition is a Rasso form | — | — |
| $`\sigma`$ | sees only which candidates there are, not their order | Proved | `sigmaSol_order`, `sigmaMsol_order` | — |
| $`\sigma`$ | $`\sigma`$ is $`\cap`$ with a restriction (earlier list) | Restated without $`\cap`$: $`\sigma`$ adds its test to the set meaning | `sigmaSol_meaning`, `sigmaMsol_meaning` | — |

<a id="sec-B-4-2"></a>
### B.4.2 Selections on written forms

<a id="proposition-B-7"></a>

**Proposition B.7 (Selections on written forms).** ✓

> The laws marked Proved in the table below.

Lean: [`Rasso.SolLaws.sigmaSol_keeps`](../Rasso/Laws/Sol.lean#L185-L192), [`Rasso.SolLaws.sigmaMsol_keeps`](../Rasso/Laws/Sol.lean#L200-L207), [`Rasso.SolLaws.sigmaMsol_comm`](../Rasso/Laws/Sol.lean#L209-L225), [`Rasso.SolLaws.sigmaMsol_idem`](../Rasso/Laws/Sol.lean#L227-L241), [`Rasso.SolLaws.sigmaMsol_cascade`](../Rasso/Laws/Sol.lean#L243-L280), [`Rasso.sigmaMsol_meaning`](../Rasso/FSpace.lean#L762-L772), [`Rasso.mem_filterM`](../Rasso/FSpace.lean#L108-L111), [`Rasso.SolLaws.omegaMsol_some`](../Rasso/Laws/Sol.lean#L282-L326).

| **Group** | **Law** | **Status** | **Lean** | **Definedness / notes** |
|---|---|---|---|---|
| $`\sigma _{\mathrm{sol}}`$ | keeps the data and the heading; keeps a sublist of candidates | Proved | `SolLaws.sigmaSol_keeps` | — |
| $`\sigma _{\mathrm{sol}}`$ | commutative, idempotent, cascade on written forms | Argued from the abstract laws: a condition names its candidate by repeating its operand’s form, so the swapped forms are other conditions | — | — |
| $`\sigma _{\mathrm{msol}}`$ | keeps the members; keeps a sublist of databases | Proved | `SolLaws.sigmaMsol_keeps` | — |
| $`\sigma _{\mathrm{msol}}`$ | commutative, as written forms | Proved | `SolLaws.sigmaMsol_comm` | as for $`\sigma`$ on lists |
| $`\sigma _{\mathrm{msol}}`$ | idempotent, as written forms | Proved: if $`\sigma _{\mathrm{msol}}`$ succeeds, so does $`\sigma _{\mathrm{msol}}`$ $`\sigma _{\mathrm{msol}}`$, with the same result | `SolLaws.sigmaMsol_idem` | the converse is immediate, as on lists |
| $`\sigma _{\mathrm{msol}}`$ | cascade into `and [c, d]`, as written forms | Proved | `SolLaws.sigmaMsol_cascade` | refused together |
| $`\sigma _{\mathrm{msol}}`$ | $`\sigma`$ is a conjunct: a database is kept iff it is in the operand and passes (earlier list) | Proved | `sigmaMsol_meaning`, `mem_filterM` | — |
| $`\omega _{\mathrm{msol}}`$ | with a condition = $`\sigma _{\mathrm{msol}}`$ of $`\omega _{\mathrm{msol}}`$ without one, as written forms (earlier list "$`\sigma`$ on $`\omega`$") | Proved | `SolLaws.omegaMsol_some` | refused together |

<a id="sec-B-4-3"></a>
### B.4.3 The exponent laws

<a id="proposition-B-8"></a>

**Proposition B.8 (The exponent laws on candidates).** ✓

> The laws marked Proved in the table below.

Lean: [`Rasso.mem_omegaSolCandidates`](../Rasso/FSpace.lean#L534-L551), [`Rasso.length_omegaSolCandidates`](../Rasso/FSpace.lean#L553-L560), [`Rasso.nodup_omegaSolCandidates`](../Rasso/FSpace.lean#L615-L635), [`Rasso.SolLaws.omegaSolCandidates_no_rows`](../Rasso/Laws/Sol.lean#L330-L332), [`Rasso.SolLaws.omegaSolCandidates_no_picks`](../Rasso/Laws/Sol.lean#L334-L341), [`Rasso.SolLaws.length_omegaSolCandidates_one`](../Rasso/Laws/Sol.lean#L343-L346), [`Rasso.SolLaws.length_omegaSolCandidates_append`](../Rasso/Laws/Sol.lean#L348-L352), [`Rasso.SolLaws.omegaSolCandidates_append_split`](../Rasso/Laws/Sol.lean#L371-L389), [`Rasso.SolLaws.omegaSolCandidates_append_join`](../Rasso/Laws/Sol.lean#L391-L417), [`Rasso.SolLaws.length_omegaSolCandidates_product`](../Rasso/Laws/Sol.lean#L354-L360), [`Rasso.SolLaws.length_omegaSolCandidates_curry`](../Rasso/Laws/Sol.lean#L362-L367), [`Rasso.eval_omegaSol_meaning`](../Rasso/Bridge/Sol.lean#L113-L125), [`Rasso.eval_sigmaSol_meaning`](../Rasso/Bridge/Sol.lean#L152-L165).

<a id="example-B-9"></a>

**Example B.9 (Examples).** ✓

> The examples named in the table below, each checked by `#guard`.

Lean: [`Rasso.SolLaws.Examples.sum_needs_disjoint`](../Rasso/Laws/SolExamples.lean#L62-L66), [`Rasso.SolJoinLaws.Examples.join_same_data_product`](../Rasso/Laws/SolJoinExamples.lean#L123-L128), [`Rasso.SolJoinLaws.Examples.join_not_product`](../Rasso/Laws/SolJoinExamples.lean#L114-L120), [`Rasso.SolJoinLaws.Examples.join_shared_data_refused`](../Rasso/Laws/SolJoinExamples.lean#L131-L136), [`Rasso.SolLaws.Examples.curry_not_expressible`](../Rasso/Laws/SolExamples.lean#L69-L72).

| **Group** | **Law** | **Status** | **Lean** | **Definedness / notes** |
|---|---|---|---|---|
| $`\omega _{\mathrm{sol}}`$ | candidates are the graphs of total functions; \|X\|^\|D\| of them; none twice | Proved, for distinct data tuples; none twice also for distinct, well-formed decision tuples | `mem_omegaSolCandidates`, `length_omegaSolCandidates`, `nodup_omegaSolCandidates` | $`\omega _{\mathrm{sol}}`$ refuses an attribute in both data and decision |
| $`\omega _{\mathrm{sol}}`$ | D^$`\emptyset`$ = 1: the empty relation is the only candidate | Proved (Lean `=` of lists) | `SolLaws.omegaSolCandidates_no_rows` | — |
| $`\omega _{\mathrm{sol}}`$ | 0^A = 0 when A has a tuple | Proved | `SolLaws.omegaSolCandidates_no_picks` | — |
| $`\omega _{\mathrm{sol}}`$ | 1^A = 1 | Proved | `SolLaws.length_omegaSolCandidates_one` | — |
| $`\omega _{\mathrm{sol}}`$ | sum law X^(A $`\uplus`$ B) $`\cong`$ X^A $`\times`$ X^B, as a count | Proved, as a count on the list A ++ B | `SolLaws.length_omegaSolCandidates_append` | for Rasso data (a set) A and B must be disjoint: `SolLaws.Examples.sum_needs_disjoint` |
| $`\omega _{\mathrm{sol}}`$ | sum law on candidates, A and B disjoint | Proved, both ways | `SolLaws.omegaSolCandidates_append_split`, `SolLaws.omegaSolCandidates_append_join` | needs disjoint data: `SolLaws.Examples.sum_needs_disjoint` |
| $`\omega _{\mathrm{sol}}`$ | product law (X $`\times`$ Y)^A $`\cong`$ X^A $`\times`$ Y^A, as a count | Proved, given X $`\times`$ Y has \|X\|$`\cdot`$\|Y\| tuples (a hypothesis) | `SolLaws.length_omegaSolCandidates_product` | type level: `FunctionSpace.prodIso` |
| $`\omega _{\mathrm{sol}}`$ | product law as $`\omega`$\[A, X\] $`\bowtie _{\mathrm{sol}}`$ $`\omega`$\[A, Y\] = $`\omega`$\[A, X $`\times`$ Y\] (same data) | Checked (36 members each, same members) | `SolJoinLaws.Examples.join_same_data_product` | — |
| $`\omega _{\mathrm{sol}}`$ | X^A $`\bowtie _{\mathrm{sol}}`$ Y^B = X^A $`\times`$ Y^B (disjoint data) | Fails: the left side is (X $`\times`$ Y)^(A $`\times`$ B), 256 members, not 4 $`\cdot`$ 4 | `SolJoinLaws.Examples.join_not_product` | $`\times _{\mathrm{sol}}`$ is refused: No operator for the right side |
| $`\omega _{\mathrm{sol}}`$ | X^A $`\bowtie _{\mathrm{sol}}`$ Y^B = (X $`\bowtie`$ Y)^(A $`\bowtie`$ B) with shared data attributes (earlier list: Fails, 0 members, not 4) | Refused in Rasso on the earlier list’s data: the shared values do not all match, so the joined data does not hold each side’s data whole | `SolJoinLaws.Examples.join_shared_data_refused` | refused, not a wrong result |
| $`\omega _{\mathrm{sol}}`$ | currying (X^B)^A $`\cong`$ X^(A $`\times`$ B), as a count | Proved, given A $`\times`$ B has \|A\|$`\cdot`$\|B\| tuples | `SolLaws.length_omegaSolCandidates_curry` | — |
| $`\omega _{\mathrm{sol}}`$ | currying as solution sets | Not carried over: not expressible ($`\omega _{\mathrm{sol}}`$’s decision is a relation) | — | `SolLaws.Examples.curry_not_expressible` |
| $`\omega _{\mathrm{sol}}`$ | relative top: every candidate of U is in $`\omega`$\[Data\_U, Decision\_U\] | Proved for $`\omega _{\mathrm{sol}}`$ and $`\sigma _{\mathrm{sol}}`$ (`SolMeaning`) | `eval_omegaSol_meaning`, `eval_sigmaSol_meaning` | complement needs $`-_{\mathrm{sol}}`$: not defined |
| membership | respects $`\approx`$ of candidates | By construction: a candidate’s body is a quotient | — | — |

<a id="sec-r2-laws-msol"></a>
## B.5 Multi-solution sets

<a id="proposition-B-10"></a>

**Proposition B.10 (Multi-solution sets).** ✓

> The laws marked Proved in the table below.

Lean: [`Rasso.mem_omegaMsolDbs`](../Rasso/FSpace.lean#L708-L711), [`Rasso.length_omegaMsolDbs`](../Rasso/FSpace.lean#L713-L719), [`Rasso.SolLaws.omegaMsolDbs_one`](../Rasso/Laws/Sol.lean#L421-L427), [`Rasso.SolLaws.length_omegaMsolDbs_perm`](../Rasso/Laws/Sol.lean#L437-L441).

<a id="example-B-11"></a>

**Example B.11 (Examples).** ✓

> The examples named in the table below, each checked by `#guard`.

Lean: [`Rasso.SolLaws.Examples.omegaMsol_no_members`](../Rasso/Laws/SolExamples.lean#L77-L79), [`Rasso.SolLaws.Examples.omegaMsol_duplicate_names`](../Rasso/Laws/SolExamples.lean#L82-L85).

| **Group** | **Law** | **Status** | **Lean** | **Definedness / notes** |
|---|---|---|---|---|
| $`\omega _{\mathrm{msol}}`$ | databases = one candidate per member; count = product | Proved | `mem_omegaMsolDbs`, `length_omegaMsolDbs` | refused with no members: `SolLaws.Examples.omegaMsol_no_members` |
| $`\omega _{\mathrm{msol}}`$ | one member: its candidates, each named | Proved (Lean `=`) | `SolLaws.omegaMsolDbs_one` | — |
| $`\omega _{\mathrm{msol}}`$ | reordering the members keeps the count | Proved | `SolLaws.length_omegaMsolDbs_perm` | — |
| $`\omega _{\mathrm{msol}}`$ | member names are distinct | Checked: the evaluator refuses two members with one name, as the Racket implementation does | — | `SolLaws.Examples.omegaMsol_duplicate_names`; `CandOf.lookup` relies on it |

<a id="sec-r2-laws-boundary"></a>
## B.6 The boundary

The boundary operators are $`\mathcal{E}`$, $`\mathcal{E}_\mathrm{sol}`$, $`\mathcal{E}_{\mathrm{msol}}`$, `forget`, `lift`, `flatten` and `flatten_msol`. Their laws state what $`\mathcal{E}`$ returns: members of its operand, at most $`k`$ of them, in key order. They do not say which candidates $`\mathcal{E}`$ keeps when there are more than $`k`$. Rasso states a problem. How a solver finds its candidates is outside the algebra.

<a id="proposition-B-12"></a>

**Proposition B.12 (The boundary).** ✓

> The laws marked Proved in the table below.

Lean: [`Rasso.sortTake_spec`](../Rasso/Bridge/Sol.lean#L181-L192), [`Rasso.eval_enumSol_meaning`](../Rasso/Bridge/Sol.lean#L219-L233), [`Rasso.eval_enumMsol_meaning`](../Rasso/Bridge/Sol.lean#L453-L466), [`Rasso.SolLaws.eval_enum_finrel`](../Rasso/Laws/Sol.lean#L496-L515), [`Rasso.eval_enumSol`](../Rasso/Bridge/Sol.lean#L194-L217), [`Rasso.eval_enumMsol`](../Rasso/Bridge/Sol.lean#L430-L451), [`Rasso.SolLaws.sortTake_sorted`](../Rasso/Laws/Sol.lean#L469-L479), [`Rasso.SolLaws.mergeSort_pairwise_on`](../Rasso/Laws/Sol.lean#L457-L467), [`Rasso.SolLaws.sortTake_prefix`](../Rasso/Laws/Sol.lean#L445-L450), [`Rasso.SolLaws.enum_prefix`](../Rasso/Laws/Sol.lean#L517-L530), [`Rasso.SolLaws.sortTake_zero`](../Rasso/Laws/Sol.lean#L452-L455), [`Rasso.SolLaws.forget_enum_sub`](../Rasso/Laws/Sol.lean#L550-L566), [`Rasso.SolLaws.forget_enum_all`](../Rasso/Laws/Sol.lean#L568-L582), [`Rasso.eval_flatten_none`](../Rasso/Bridge/Sol.lean#L237-L265), [`Rasso.eval_flatten_some`](../Rasso/Bridge/Sol.lean#L267-L298), [`Rasso.eval_flattenMsol`](../Rasso/Bridge/Sol.lean#L480-L511).

<a id="example-B-13"></a>

**Example B.13 (Examples).** ✓

> The examples named in the table below, each checked by `#guard`.

Lean: [`Rasso.SolLaws.Examples.enum_prefix_example`](../Rasso/Laws/SolExamples.lean#L96-L101), [`Rasso.SolLaws.Examples.enum_zero`](../Rasso/Laws/SolExamples.lean#L104-L106), [`Rasso.SolLaws.Examples.flatten_rank_clash`](../Rasso/Laws/SolExamples.lean#L109-L114).

| **Group** | **Law** | **Status** | **Lean** | **Definedness / notes** |
|---|---|---|---|---|
| $`\mathcal{E}`$, $`\mathcal{E}_{\mathrm{sol}}`$, $`\mathcal{E}_{\mathrm{msol}}`$ | every item returned is in the operand; min(k, n) of them; all (a permutation) when k $`\ge`$ n | Proved | `sortTake_spec`, `eval_enumSol_meaning`, `eval_enumMsol_meaning` | stated on `Count.toNat` (`all` is 2^63 $`-`$ 1; a negative count is 0) |
| $`\mathcal{E}`$ (all) | in key order, when the key comparison is transitive and total on the items present | Proved on `sortTake`; with `SolLaws.eval_enum_finrel`, `eval_enumSol`, `eval_enumMsol` it applies to the evaluated $`\mathcal{E}`$, $`\mathcal{E}_{\mathrm{sol}}`$, $`\mathcal{E}_{\mathrm{msol}}`$ | `SolLaws.sortTake_sorted`, `SolLaws.mergeSort_pairwise_on` | says nothing about which items are kept when there are more than k; the hypotheses are not discharged for `cmpKeys` in general (it is not transitive across key lists of different lengths) |
| $`\mathcal{E}`$ (all) | prefix law: $`\mathcal{E}_{\mathit{m}}`$ is the first m of $`\mathcal{E}_{\mathit{n}}`$ for m $`\le`$ n | Proved on `sortTake` | `SolLaws.sortTake_prefix` | — |
| $`\mathcal{E}`$ | prefix law on written forms (finite operand) | Proved, when both sides succeed | `SolLaws.enum_prefix`, `SolLaws.eval_enum_finrel` | refused together: Argued (the keys are evaluated whatever k is); `SolLaws.Examples.enum_prefix_example` |
| $`\mathcal{E}_{\mathrm{sol}}`$, $`\mathcal{E}_{\mathrm{msol}}`$ | prefix law on written forms | Argued: keys are evaluated with the same bindings and targets whatever k is | — | — |
| $`\mathcal{E}`$ (all) | $`\mathcal{E}_{\mathit{0}}`$ is empty, when defined | Proved | `SolLaws.sortTake_zero` | `SolLaws.Examples.enum_zero` |
| forget $`\circ`$ $`\mathcal{E}`$ | decreasing, for every k | Proved | `SolLaws.forget_enum_sub` | can be refused by a key |
| forget $`\circ`$ $`\mathcal{E}`$ | identity on bodies when k $`\ge`$ size | Proved | `SolLaws.forget_enum_all` | can be refused by a key |
| lift | of a finite relation is `toUnrel`; of a sequence it is lift $`\circ`$ forget | Definition (`Expr.eval`) | — | step 2’s `toUnrel` rows apply |
| flatten | no rank: \[\] gives no tuples; one relation gives its tuples; more refuses; with a rank: the candidates’ union, ranked | Proved | `eval_flatten_none`, `eval_flatten_some` | refuses a rank attribute the heading has |
| flatten\_msol | as flatten, per member | Proved | `eval_flattenMsol` | refuses a rank attribute a member already has, as flatten does: `SolLaws.Examples.flatten_rank_clash` |

<a id="sec-r2-laws-soljoin"></a>
## B.7 The join and renaming of solution sets

Each candidate of $`U \bowtie _\mathrm{sol}V`$ is a function on $`J = \mathit{Data}_U \bowtie \mathit{Data}_V`$ whose slices along the data attributes that the other side adds are candidates of that side (David’s decision, 2026-11-13: the meaning the Latin square needs). $`\rho _\mathrm{sol}`$ renames the data, the heading and every candidate. The laws of $`\rho _\mathrm{sol}`$, the shape of $`\bowtie _\mathrm{sol}`$, its refusals and its membership theorem are theorems. Its algebraic laws (commutativity, associativity, idempotence, the unit) are checked on programs: the Latin square ladder, powers, and the unit.

<a id="proposition-B-14"></a>

**Proposition B.14 (The join and renaming of solution sets).** ✓

> The laws marked Proved in the table below.

Lean: [`Rasso.SolJoinLaws.rename_ok`](../Rasso/Laws/SolJoin.lean#L20-L47), [`Rasso.SolJoinLaws.rename_eq`](../Rasso/Laws/SolJoin.lean#L49-L77), [`Rasso.SolJoinLaws.renameMember`](../Rasso/Laws/SolJoin.lean#L16-L18), [`Rasso.SolJoinLaws.mem_renameMember`](../Rasso/Laws/SolJoin.lean#L84-L88), [`Rasso.SolJoinLaws.rename_length`](../Rasso/Laws/SolJoin.lean#L79-L82), [`Rasso.SolJoinLaws.rename_nil_members`](../Rasso/Laws/SolJoin.lean#L90-L101), [`Rasso.SolJoinLaws.join_shape`](../Rasso/Laws/SolJoin.lean#L105-L128), [`Rasso.SolJoinLaws.join_refuses_data_decision`](../Rasso/Laws/SolJoin.lean#L149-L185), [`Rasso.SolJoinLaws.forIn_steps_ok`](../Rasso/Laws/SolJoin.lean#L130-L147), [`Rasso.Sol.MembersOk`](../Rasso/Laws/SolJoinMembers.lean#L17-L24), [`Rasso.Tuple.Exactly`](../Rasso/Laws/SolJoinMembers.lean#L13-L15), [`Rasso.SolJoinLaws.sigmaSol_membersOk`](../Rasso/Laws/SolJoinMembers.lean#L41-L51), [`Rasso.SolJoinLaws.membersOk_of_sublist`](../Rasso/Laws/SolJoinMembers.lean#L30-L39), [`Rasso.SolJoinLaws.omegaSol_membersOk`](../Rasso/Laws/SolJoinMembers.lean#L76-L105), [`Rasso.SolJoinLaws.decision_omegaSol`](../Rasso/Laws/SolJoinMembers.lean#L58-L74), [`Rasso.SolJoinLaws.rename_membersOk`](../Rasso/Laws/SolRenameMembers.lean#L123-L258), [`Rasso.renameTuple_merge`](../Rasso/Laws/SolRenameMembers.lean#L100-L117), [`Rasso.renameTuple_inj`](../Rasso/Laws/SolRenameMembers.lean#L79-L86), [`Rasso.SolJoinLaws.join_w3`](../Rasso/Laws/SolJoinPicks.lean#L96-L105), [`Rasso.SolJoinLaws.join_whole`](../Rasso/Laws/SolJoinPicks.lean#L61-L87), [`Rasso.SolJoinLaws.checkWhole_ok`](../Rasso/Laws/SolJoinPicks.lean#L18-L59), [`Rasso.SolJoinLaws.join_q2`](../Rasso/Laws/SolJoinPicks.lean#L89-L94), [`Rasso.SolJoinLaws.join_candidates_picks`](../Rasso/Laws/SolJoinPicks.lean#L297-L303), [`Rasso.SolJoinLaws.joinLoop_picks`](../Rasso/Laws/SolJoinPicks.lean#L189-L295), [`Rasso.SolJoinLaws.allM_ok_all`](../Rasso/Laws/SolJoinPicks.lean#L141-L158), [`Rasso.SolJoinLaws.mapM_ok_map`](../Rasso/Laws/SolJoinPicks.lean#L160-L178), [`Rasso.SolJoinLaws.mem_join_picks`](../Rasso/Laws/SolJoinPicks.lean#L356-L373), [`Rasso.SolJoinLaws.picks_map_iff`](../Rasso/Laws/SolJoinPicks.lean#L314-L338), [`Rasso.SolJoinLaws.choices_tag`](../Rasso/Laws/SolJoinPicks.lean#L305-L312), [`Rasso.SolJoinLaws.slice_glue_U`](../Rasso/Laws/SolJoinSlices.lean#L486-L595), [`Rasso.SolJoinLaws.slice_glue_V`](../Rasso/Laws/SolJoinSlices.lean#L609-L737), [`Rasso.SolJoinLaws.sliceU`](../Rasso/Laws/SolJoinSlices.lean#L445-L448), [`Rasso.SolJoinLaws.sliceV`](../Rasso/Laws/SolJoinSlices.lean#L450-L452), [`Rasso.SolJoinLaws.mem_join_sound`](../Rasso/Laws/SolJoinSlices.lean#L741-L754), [`Rasso.SolJoinLaws.mem_join_complete`](../Rasso/Laws/SolJoinComplete.lean#L334-L440), [`Rasso.SolJoinLaws.decisionAt_of_sliceU`](../Rasso/Laws/SolJoinComplete.lean#L140-L235), [`Rasso.SolJoinLaws.decisionAt_of_sliceV`](../Rasso/Laws/SolJoinComplete.lean#L237-L332), [`Rasso.SolJoinLaws.lookup_zip_map`](../Rasso/Laws/SolJoinComplete.lean#L114-L123), [`Rasso.SolJoinLaws.mem_join`](../Rasso/Laws/SolJoinComplete.lean#L442-L457), [`Rasso.SolJoinLaws.nodup_join`](../Rasso/Laws/SolJoinSlices.lean#L886-L939), [`Rasso.SolJoinLaws.join_candidates_pairs`](../Rasso/Laws/SolJoinSlices.lean#L875-L884), [`Rasso.SolJoinLaws.nodup_flatMap_tag`](../Rasso/Laws/SolJoinSlices.lean#L850-L865), [`Rasso.SolJoinLaws.join_membersOk`](../Rasso/Laws/SolJoinSlices.lean#L758-L829), [`Rasso.SolJoinLaws.foldlM_join_membersOk`](../Rasso/Laws/SolRenameMembers.lean#L260-L274), [`Rasso.SolJoinLaws.join_data_tuple`](../Rasso/Laws/SolJoinSlices.lean#L278-L309), [`Rasso.SolJoinLaws.joinHeading_attrs`](../Rasso/Laws/SolJoinSlices.lean#L140-L181), [`Rasso.SolJoinLaws.length_join`](../Rasso/Laws/SolJoin.lean#L435-L443), [`Rasso.SolJoinLaws.length_joinLoop`](../Rasso/Laws/SolJoin.lean#L348-L432), [`Rasso.SolJoinLaws.join_candidates_eq`](../Rasso/Laws/SolJoin.lean#L225-L249), [`Rasso.SolJoinLaws.forIn_append_ok`](../Rasso/Laws/SolJoin.lean#L251-L269), [`Rasso.FunctionSpace.curryIso`](../Rasso/FunctionSpace.lean#L278-L285).

<a id="example-B-15"></a>

**Example B.15 (Examples).** ✓

> The examples named in the table below, each checked by `#guard`.

Lean: [`Rasso.SolJoinLaws.Examples.rename_rename`](../Rasso/Laws/SolJoinExamples.lean#L166-L169), [`Rasso.SolJoinLaws.Examples.rename_inverse`](../Rasso/Laws/SolJoinExamples.lean#L172-L174), [`Rasso.SolJoinLaws.Examples.rename_join`](../Rasso/Laws/SolJoinExamples.lean#L177-L181), [`Rasso.SolJoinLaws.Examples.rename_select`](../Rasso/Laws/SolJoinExamples.lean#L184-L190), [`Rasso.SolJoinLaws.Examples.join_shared_data_refused`](../Rasso/Laws/SolJoinExamples.lean#L131-L136), [`Rasso.SolJoinLaws.Examples.join_unit_empty_data_refused`](../Rasso/Laws/SolJoinExamples.lean#L97-L100), [`Rasso.SolJoinLaws.Examples.join_needs_members_ok`](../Rasso/Laws/SolJoinExamples.lean#L212-L215), [`Rasso.SolJoinLaws.Examples.join_picks_latin`](../Rasso/Laws/SolJoinExamples.lean#L233-L241), [`Rasso.SolJoinLaws.Examples.join_nodup`](../Rasso/Laws/SolJoinExamples.lean#L159-L161), [`Rasso.SolJoinLaws.Examples.join_omega_omega`](../Rasso/Laws/SolJoinExamples.lean#L105-L111), [`Rasso.SolJoinLaws.Examples.join_comm_powers`](../Rasso/Laws/SolJoinExamples.lean#L44), [`Rasso.SolJoinLaws.Examples.join_comm_latin`](../Rasso/Laws/SolJoinExamples.lean#L47-L48), [`Rasso.SolJoinLaws.Examples.join_assoc_latin`](../Rasso/Laws/SolJoinExamples.lean#L51-L53), [`Rasso.SolJoinLaws.Examples.join_idem`](../Rasso/Laws/SolJoinExamples.lean#L58-L60), [`Rasso.SolJoinLaws.Examples.join_idem_empty_data`](../Rasso/Laws/SolJoinExamples.lean#L63-L71), [`Rasso.SolJoinLaws.Examples.join_unit`](../Rasso/Laws/SolJoinExamples.lean#L91-L94), [`Rasso.SolJoinLaws.Examples.join_empty_data_one_member`](../Rasso/Laws/SolJoinExamples.lean#L74-L84), [`Rasso.SolJoinLaws.Examples.join_not_distributive`](../Rasso/Laws/SolJoinExamples.lean#L143-L149).

| **Group** | **Law** | **Status** | **Lean** | **Definedness / notes** |
|---|---|---|---|---|
| $`\rho _{\mathrm{sol}}`$ | refused exactly when $`\rho`$ is refused on the heading or on the data | Proved | `SolJoinLaws.rename_ok` | the two checks are separate: nothing in a solution set ties its data attributes to its heading |
| $`\rho _{\mathrm{sol}}`$ | the members of $`\rho`$(U) are U’s members renamed, one for one, in order; the data is $`\rho`$ of U’s data; the heading is renamed | Proved | `SolJoinLaws.rename_eq`, `SolJoinLaws.renameMember`, `SolJoinLaws.mem_renameMember`, `SolJoinLaws.rename_length` | — |
| $`\rho _{\mathrm{sol}}`$ | the empty renaming keeps every member’s body | Proved, for members well formed over the heading | `SolJoinLaws.rename_nil_members` | — |
| $`\rho _{\mathrm{sol}}`$ | $`\rho`$$`\circ`$$`\rho`$ is $`\rho`$ of the composed renaming | Checked | `SolJoinLaws.Examples.rename_rename` | — |
| $`\rho _{\mathrm{sol}}`$ | $`\rho`$ with the inverse renaming gives U back (earlier list "Renaming") | Checked | `SolJoinLaws.Examples.rename_inverse` | — |
| $`\rho _{\mathrm{sol}}`$ | $`\rho`$ distributes over $`\bowtie _{\mathrm{sol}}`$, for a renaming injective on both headings | Checked, on member sets | `SolJoinLaws.Examples.rename_join` | renaming can change the order of J’s tuples, so of the members |
| $`\rho _{\mathrm{sol}}`$ | commutes with $`\sigma _{\mathrm{sol}}`$ (earlier list "Renaming") | Checked on a program; Argued in general | `SolJoinLaws.Examples.rename_select` | the condition names its operand’s form, so the two programs write different conditions |
| $`\bowtie _{\mathrm{sol}}`$ | data is Data\_U $`\bowtie`$ Data\_V; heading is that data’s heading followed by the join of the decision headings | Proved | `SolJoinLaws.join_shape` | — |
| $`\bowtie _{\mathrm{sol}}`$ | refused when an attribute is data on one side and decided on the other | Proved | `SolJoinLaws.join_refuses_data_decision`, `SolJoinLaws.forIn_steps_ok` | also refused when the joined data does not hold a side’s data whole in every group: `SolJoinLaws.Examples.join_shared_data_refused`, `SolJoinLaws.Examples.join_unit_empty_data_refused` |
| members | `Sol.MembersOk`: each member is the graph of a function on the data whose values have exactly the decision’s attributes | Definition | `Sol.MembersOk`, `Tuple.Exactly` | a hypothesis of membership: without it a member is not kept whole (`SolJoinLaws.Examples.join_needs_members_ok`) |
| members | $`\sigma _{\mathrm{sol}}`$ keeps `MembersOk` | Proved | `SolJoinLaws.sigmaSol_membersOk`, `SolJoinLaws.membersOk_of_sublist` | — |
| members | $`\omega _{\mathrm{sol}}`$ gives `MembersOk`, for well-formed data and a decision heading with no attribute twice | Proved | `SolJoinLaws.omegaSol_membersOk`, `SolJoinLaws.decision_omegaSol` | the two premises are not proved for every program (`Rasso/WF.lean` does not cover $`\omega`$) |
| members | $`\rho _{\mathrm{sol}}`$ keeps `MembersOk` | Proved | `SolJoinLaws.rename_membersOk`, `renameTuple_merge`, `renameTuple_inj` | $`\rho _{\mathrm{sol}}`$ refuses a renaming that is not one-to-one on the heading, so renaming is one-to-one on every tuple over it |
| $`\bowtie _{\mathrm{sol}}`$ | its conditions read back: when $`\bowtie _{\mathrm{sol}}`$ succeeds, each group of J holds each side’s data whole (J empty only with both data empty), and no attribute is data on one side and decided on the other | Proved | `SolJoinLaws.join_w3`, `SolJoinLaws.join_whole`, `SolJoinLaws.checkWhole_ok`, `SolJoinLaws.join_q2` | — |
| $`\bowtie _{\mathrm{sol}}`$ | members as a list: for each U-pick (a member of U per U-group) and each choice of V members (one per V-group) agreeing with it at every tuple of their group, the glued member, in that order | Proved, whenever $`\bowtie _{\mathrm{sol}}`$ succeeds (no hypothesis on the members) | `SolJoinLaws.join_candidates_picks`, `SolJoinLaws.joinLoop_picks`, `SolJoinLaws.allM_ok_all`, `SolJoinLaws.mapM_ok_map` | checked on the 3 $`\times`$ 3 Latin square: `SolJoinLaws.Examples.join_picks_latin` |
| $`\bowtie _{\mathrm{sol}}`$ | membership as picks: a member is a U-pick and an agreeing V-pick, glued | Proved | `SolJoinLaws.mem_join_picks`, `SolJoinLaws.picks_map_iff`, `SolJoinLaws.choices_tag` | the picks are the code’s own; the slice form below reads them off a member |
| $`\bowtie _{\mathrm{sol}}`$ | a glued member’s U-slices are its U-picks and its V-slices its V-picks (by body) | Proved, for operands with `MembersOk` | `SolJoinLaws.slice_glue_U`, `SolJoinLaws.slice_glue_V`, `SolJoinLaws.sliceU`, `SolJoinLaws.sliceV` | the core of membership and of no member twice |
| $`\bowtie _{\mathrm{sol}}`$ | membership (`mem_join`), "$`\to`$": every member’s U-slices are members of U and its V-slices members of V | Proved, for operands with `MembersOk` | `SolJoinLaws.mem_join_sound` | — |
| $`\bowtie _{\mathrm{sol}}`$ | membership (`mem_join`), "←": a function on J, with values exactly over the decision, whose slices are members of their sides is a member | Proved, for operands with `MembersOk` | `SolJoinLaws.mem_join_complete`, `SolJoinLaws.decisionAt_of_sliceU`, `SolJoinLaws.decisionAt_of_sliceV`, `SolJoinLaws.lookup_zip_map` | the picks are read off the slices |
| $`\bowtie _{\mathrm{sol}}`$ | membership (`mem_join`), both ways: a function on J is a member exactly when each slice is a member of its side | Proved, for operands with `MembersOk` | `SolJoinLaws.mem_join` | checked too on the Latin square ladder: 2, 12 squares; 2 cubes |
| $`\bowtie _{\mathrm{sol}}`$ | gives no member twice (by body), when neither operand does | Proved, for operands with `MembersOk` | `SolJoinLaws.nodup_join`, `SolJoinLaws.join_candidates_pairs`, `SolJoinLaws.nodup_flatMap_tag` | checked too: `SolJoinLaws.Examples.join_nodup` |
| members | $`\bowtie _{\mathrm{sol}}`$ keeps `MembersOk`, so the theorems reach n-ary joins | Proved, also for the left fold of an n-ary $`\bowtie _{\mathrm{sol}}`$ | `SolJoinLaws.join_membersOk`, `SolJoinLaws.foldlM_join_membersOk`, `SolJoinLaws.join_data_tuple`, `SolJoinLaws.joinHeading_attrs` | with $`\rho _{\mathrm{sol}}`$, $`\sigma _{\mathrm{sol}}`$ and $`\omega _{\mathrm{sol}}`$, the theorems reach the Latin square and cube, given $`\omega _{\mathrm{sol}}`$’s premises (well-formed data, no decision attribute twice), which are not proved for every program; $`\rho _{\mathrm{sol}}`$ and n-ary $`\bowtie _{\mathrm{sol}}`$ are stated on solution sets, not on the evaluator |
| $`\bowtie _{\mathrm{sol}}`$ | $`\omega`$\[A, X\] $`\bowtie _{\mathrm{sol}}`$ $`\omega`$\[B, Y\] = $`\omega`$\[A $`\bowtie`$ B, X $`\bowtie`$ Y\] (disjoint data and decisions) | Checked (256 members, the same members) | `SolJoinLaws.Examples.join_omega_omega` | — |
| $`\bowtie _{\mathrm{sol}}`$ | commutative, up to heading order | Checked | `SolJoinLaws.Examples.join_comm_powers`, `SolJoinLaws.Examples.join_comm_latin` | the left operand’s attributes come first in the heading |
| $`\bowtie _{\mathrm{sol}}`$ | associative, up to heading order | Checked | `SolJoinLaws.Examples.join_assoc_latin` | whether the whole-data condition in one bracketing gives it in the other is Open; the headings also need `Domain.inter` associative |
| $`\bowtie _{\mathrm{sol}}`$ | idempotent: U $`\bowtie _{\mathrm{sol}}`$ U = U | Checked | `SolJoinLaws.Examples.join_idem` | — |
| $`\bowtie _{\mathrm{sol}}`$ | idempotent with empty data (earlier list: Fails) | Checked: holds in Rasso (one member, or none) | `SolJoinLaws.Examples.join_idem_empty_data` | with no data the only function is the empty one, and a $`\sigma _{\mathrm{sol}}`$ that keeps none gives none |
| $`\bowtie _{\mathrm{sol}}`$ | unit $`\omega`$\[DEE, DEE\], on either side, when U’s data has a tuple | Checked | `SolJoinLaws.Examples.join_unit` | refused when U’s data is empty: `SolJoinLaws.Examples.join_unit_empty_data_refused` |
| $`\bowtie _{\mathrm{sol}}`$ | count \|U\|^g\_U $`\cdot`$ \|V\|^g\_V for disjoint decisions, g = the number of groups `joinGroups` gives | Proved, whenever $`\bowtie _{\mathrm{sol}}`$ succeeds (no hypothesis on the members) | `SolJoinLaws.length_join`, `SolJoinLaws.length_joinLoop`, `SolJoinLaws.join_candidates_eq`, `SolJoinLaws.forIn_append_ok` | checked too: 256, 144, 27 (`Rasso/Examples/SolJoin.lean`) |
| $`\bowtie _{\mathrm{sol}}`$ | slicing is currying: the members of $`\omega _{\mathrm{sol}}`$(A $`\bowtie`$ B, X), for A and B with no attribute in common, are one for one the choices of a member of $`\omega _{\mathrm{sol}}`$(A, X) for each tuple of B, as X^(A$`\times`$B) $`\cong`$ (X^A)^B; so a slice is the curried function’s value at a tuple of B | Open | — (for functions: `FunctionSpace.curryIso`) | the slice condition of $`\bowtie _{\mathrm{sol}}`$ rests on it; not yet stated on solution sets |
| $`\bowtie _{\mathrm{sol}}`$ | with empty data on both sides, each adding a data attribute: one member, whatever the members | Checked (0^0 $`\cdot`$ 0^0 = 1) | `SolJoinLaws.Examples.join_empty_data_one_member` | a consequence of the count: no groups on either side |
| $`\bowtie _{\mathrm{sol}}`$ | distributes over a union of members | Fails: U $`\bowtie`$ V3 has 16 members while U $`\bowtie`$ V1 and U $`\bowtie`$ V2 have 4 each, though V3’s members are V1’s and V2’s | `SolJoinLaws.Examples.join_not_distributive` | (u + v)^b $`\ne`$ u^b + v^b; Rasso has no $`\cup _{\mathrm{sol}}`$ |

<a id="sec-r2-laws-other"></a>
## B.8 Constructs with no listed law

| **Construct** | **Status** |
|---|---|
| a name | Definition: it evaluates to its binding |
| $`\omega`$, $`\omega`$ with rows, $`\omega`$ with a condition | Definition: the constructors of relations; their laws are the rows on $`\top`$, DEE, DUM and $`\sigma`$ |
| $`\gamma`$, `extend` | Open: no law is stated beyond congruence (By construction, in the table of finite relations) |
| `lateral` | Open: the evaluator refuses it (not evaluated yet), so no law is stated |
| $`\times`$ on unrestricted relations | Open: no law is stated; on finite relations $`\times`$ is $`\bowtie`$ with disjoint headings |
| the reference to a member of a database | Definition: it gives the member’s relation |
| $`\cup _\mathrm{sol}`$, $`-_\mathrm{sol}`$, $`\cap _\mathrm{sol}`$; $`\cup`$, $`-`$, $`\cap`$, $`\bowtie`$ on multi-solution sets | No operator |
