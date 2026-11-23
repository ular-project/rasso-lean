# Examples

Three key examples of the blueprint, each in three forms: Rasso text, rassoSQL and
rassoAST.

| Example | What it solves | Answer |
| --- | --- | --- |
| [`cakes/`](cakes/) | Choose how many of each cake to bake, with no ingredient overused, for the largest profit | two banana and two chocolate cakes, profit 1700, out of 12 feasible batches |
| [`facility-location/`](facility-location/) | Choose which sites to open and give each customer one open site, at the least opening plus assignment cost | open `s2` only, every customer at `s2`, cost 10, out of 10 feasible plans |
| [`sat/`](sat/) | Is a formula in conjunctive normal form satisfiable? The formula is data, and the truth assignment is a solution set | 3 satisfying assignments of `x1 ∧ (x2 ∨ ¬x3)` |

Each folder holds:

| File | What it is |
| --- | --- |
| `program.rasso` | the program in Rasso text |
| `program.rassosql` | the same program in rassoSQL |
| `data.md` | the data both text forms read, as the database `D` (`db_ref[Cakes](D)`, `D.Cakes`) |
| `program.json` | the same program as a rassoAST document, with the data of `data.md` written into it |
| `expected.json` | the expected answer, a relation (`"kind": "relation"`): the final relation's `columns` and `rows`, the `objective` and the `count` |

## Running the rassoAST form

`rasso-lean` reads a rassoAST document. After `lake build`, from the repository's root:

    lake exe rasso-lean examples/cakes/program.json
    lake exe rasso-lean examples/facility-location/program.json
    lake exe rasso-lean examples/sat/program.json

It prints a JSON object with every definition's value, in program order. The last
definition is the answer. Compare it with `expected.json`:

- **rows:** the last definition's rows, at the expected columns, as a set. For cakes,
  `LetsMakeBatch` also carries `price`, which the expected answer leaves out.
- **objective:** the first key of the best item that `enum_sol` or `enum_msol` ranks
  (`ProfitableBatch`, `Best`).
- **count:** the number of candidates of the set that it ranks (`MakableBatches`, `Plan`).

SAT gives its answer as rows, the number `n` of satisfying assignments, so it has no
objective and no count.

## Where the forms come from, and what is checked here

The Rasso text form, the rassoSQL form, the data and the expected answer come from the
Racket implementation's library of examples, unchanged, but for SAT's expected answer,
which leaves out the library's empty `objective` and `count`. They were checked there: the
Racket implementation reads the text and rassoSQL forms as the same program, and both
give the expected rows. The rassoAST form was matched to the text form once, by the Racket
implementation's own reader and printer, with the data of `data.md` in place of `D`.

Only the rassoAST form is checked in this repository: `rasso-lean`, RassoLean's evaluator, runs
it, and its answer is compared with `expected.json`. The text forms are here to be read.
`rasso-lean` does not read them.
