import Rasso.ESO.Logic
import Rasso.ESO.ToProgram
import Rasso.ESO.ToProgramG
import Rasso.ESO.Examples
import Rasso.ESO.Capture
import Rasso.ESO.Converse
import Rasso.ESO.SentenceQuery
import Rasso.ESO.Program
import Rasso.ESO.BoolSelection
import Rasso.ESO.Recognise

/-!
# Rasso.ESO: ESO and selection on Boolean function spaces

* `Rasso.ESO.Logic`: structures, first-order formulas, ESO sentences, `Holds`.
* `Rasso.ESO.ToProgram`: a sentence and a structure give a Rasso program whose
  multi solution set `eso` is meant to have a candidate exactly when the sentence holds.
* `Rasso.ESO.ToProgramG`, a second version: the same, in the fragment Racket's
  conditions read (γ, extend, join), so the programs run in Racket too.
* `Rasso.ESO.Examples`: SAT and graph examples, run through the evaluator.
* `Rasso.ESO.SentenceQuery`: every sentence is a BoolSelection query, so the two
  directions meet in one class (`eso_iff_query`).
* `Rasso.ESO.Program`: the program `toProgram`, with the data in named statements,
  expresses every ESO sentence (`toProgram_expresses`); the structure enters only as data
  (`toProgram_eq`).
* `Rasso.ESO.BoolSelection`: selection on Boolean function spaces (`BoolSelection`), a set of
  Rasso statements that depend only on the query. On it, Rasso programs state exactly the
  ESO properties (`boolSelection_definable_in_ESO`, `eso_iff_boolSelection`). Full Rasso says
  more (objectives, `enumerate`, order, arithmetic, γ); that is outside this result.
* `Rasso.ESO.Recognise`: a recogniser `isBoolSelection` that decides membership in the
  fragment (`isBoolSelection_iff`, `DecidablePred BoolSelection`), using the decidable equality
  of forms in `Rasso.FormEq`.
-/
