<a id="chap-r2-validation"></a>
# 14 Validation

Two implementations of Rasso were used in the preparation of this report. The Racket implementation reads Rasso programs, evaluates them, and can give a search problem to a constraint solver. RassoLean is the Lean rendering that this report describes.

The Racket implementation is the reference. It provides *conformance services*: one entry point that answers questions about Rasso at two levels, the surface text and the rassoAST form. Each service gives the Racket implementation’s own result for an input. Given another implementation’s result for the same input, it gives a *verdict*: agree, disagree, or could not check, the last for the service’s own limits. Every output carries a *stamp*: the Racket commit, its release, and whether the checkout was clean, so a check of RassoLean is against a named version of the reference.

<a id="sec-14-1"></a>
## 14.1 What is compared

- **The listings of this report.** For each listing, the correspondence of its $`\rho \alpha`$ and RassoLean versions is checked through rassoAST: the two are the same program.
- **Reading and writing rassoAST.** The Racket implementation generates rassoAST documents at random, each a program in JSON, together with faulty documents and broken JSON texts that it refuses. RassoLean must read each document as the same program, write it back unchanged, and refuse each faulty one at the place where the Racket implementation refuses it.
- **Answers.** Random programs, over finite relations, solution sets and multi-solution sets, and versions of the cakes and SAT examples and of the programs that the construction of Chapter [12](eso.md) writes: RassoLean evaluates each statement, and the service judges its answer.
- **$`\Phi`$.** On a fixed set of random programs with solution sets, wherever both implementations give a flat relation, RassoLean’s and the Racket implementation’s agree, up to a renaming of the cells (Section [13.8](phi.md#sec-r2-phi-racket)).

The comparisons have found faults on both sides. In RassoLean, they found set operators that did not check their operands’ domains, a comparison of an integer with a float, and a reader that took a form the language does not have. In the Racket implementation, they found a fault in $`\Phi`$’s translation of `has_subset`, and a listing of this report that the Racket implementation could not run.

<a id="sec-14-2"></a>
## 14.2 Where the two implementations differ

Some differences remain. The two order values of different kinds differently. Some term operators differ: RassoLean has no division and does not compute with floats, and the two differ on which comparisons they refuse. RassoLean refuses a program that writes a domain mixing symbols and strings, which the Racket implementation accepts.
