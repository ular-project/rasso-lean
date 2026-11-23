# RassoLean

RassoLean renders Rasso, a relational language for data transformation and combinatorial
search, in Lean 4.35.0, core only (no Mathlib). It is also an evaluator: given a Rasso program, it computes the value
of each statement.

**[Read the report (PDF)](blueprint/rasso-lean.pdf)**, or
**[read it in this repository](blueprint/README.md)**, where each Lean name links to its
definition.

*Relational Algebras for Subset Selection and Optimisation: Formalised in Lean*, by David R. Pratten and Luke Mathieson. Draft v0.1.4, 23 November 2026.

## Abstract

Rasso is a relational language for data transformation and combinatorial search: a database states what is, and a search problem what could be, and which possibility is best. Earlier algebras state search problems by guessing a relation or a function. Rasso instead makes the space of candidate solutions, the function space Decision^Data, an operand, and lifts Codd's operators to act on it: selection keeps candidates, and join combines two search spaces into one. They stay within it, so search problems compose as queries do, one level up, and an order on the candidates states an objective. Rasso's values are finite relations, unrestricted relations, solution sets (sets of candidate relations) and multi-solution sets (sets of candidate databases).

This report introduces the language bottom up and renders each construct in RassoLean, a library in core Lean 4 without Mathlib, which is also an evaluator. It is checked against a reference implementation in Racket, with which it shares no code. Lean proofs show three results. The candidates of Decision^Data are exactly the graphs of the functions from the data to the decision. A named subalgebra, selection on Boolean function spaces, states exactly the properties that existential second-order logic defines, on structures whose universe is unmixed; by Fagin's theorem, which is cited, these are the NP properties. And Φ, which translates a solution set too large to list into one constraint to be searched, keeps its meaning: RassoLean's Φ, which takes decisions over finite domains, is proved faithful wherever it gives a result. An appendix lists the algebraic laws of the four algebras, each with its status: Lean proves 128 of them, and for 8 a counterexample, checked in Lean, shows that the law fails. This report is a draft; new versions will follow as the research progresses, and we invite comments.

## Quick start

You need [elan](https://github.com/leanprover/elan), which installs the Lean version
named in `lean-toolchain`.

    git clone https://github.com/ular-project/rasso-lean
    cd rasso-lean
    lake build
    lake exe rasso-lean examples/cakes/program.json

The first `lake build` compiles the whole library: a few minutes, and about 2 GB of
memory. It prints little while it works.

`rasso-lean` reads a program in rassoAST, Rasso's JSON form, and prints the value of each
definition. [`examples/`](examples/README.md) has three programs, each in Rasso text,
rassoSQL and rassoAST, with its expected answer.

`bash tools/check.sh` runs the checks this repository's CI runs: the build, the axiom
audit, the examples against their expected answers, the links in `blueprint/`, and the
version.

## Using the library

Your project needs the same Lean version, v4.35.0, in its `lean-toolchain`. Add the
library to your `lakefile.toml`:

    [[require]]
    name = "rasso-lean"
    git = "https://github.com/ular-project/rasso-lean"
    rev = "v0.1.3"

Run `lake update` to fetch it. Then `import Rasso`, and `import ConstraintDB` or
`import Coddstheorem` for those results. `rev` pins the latest release, v0.1.3; `main` may be newer. A later tag gives a later version.

## Licence

The Lean code and the scripts are under the Apache License 2.0 (the [`LICENSE`](LICENSE)
file). The report's text, the PDF and everything in `blueprint/`, is under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

## Citing

[`CITATION.cff`](CITATION.cff) says how to cite the report. Its DOI, [10.5281/zenodo.24461259](https://doi.org/10.5281/zenodo.24461259), names every version. For the ideas of
Rasso, cite the paper: D. R. Pratten, F. Ramezani, L. Mathieson. Relational algebras for subset selection and optimisation. arXiv:2509.06439v1 [cs.DB], 8 September 2025.

## This repository is generated

The files here are written by a release script from the upstream sources, so a change
made here would be overwritten. Issues are welcome, and changes are made upstream.
