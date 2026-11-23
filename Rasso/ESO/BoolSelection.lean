import Rasso.ESO.SentenceQuery
import Rasso.ESO.Program
import Rasso.ESO.Examples

/-!
# Selection on Boolean function spaces

Full Rasso says more than existential second-order logic (ESO). It has objectives and
`enumerate`, order comparisons, arithmetic and γ. So "Rasso is exactly ESO" is not a
claim about the whole language. This file names the part of Rasso of which it is
true, selection on Boolean function spaces, and states the result for Rasso programs, with the structure's data in named
statements.

## The fragment

A **BoolSelection statement** is a Rasso form `Q.stmt` for a well-formed `Query` `Q`.
`Q.stmt` names the data: it reads the universe as `univ` and symbol `i` at arity `n` as
`rel_i_n`. So it does not depend on the structure; the structure enters only through
the data statements before it. `BoolSelection r` says that the form `r` is such a statement.
In Rasso's own terms, a BoolSelection statement is:

* a multi solution set `ω_msol[member_R₁ U₁, …, member_Rₘ Uₘ](c)`, where each member
  `Uⱼ = ω_sol(univ^kⱼ, ω[holds bool])` is the Boolean function space `𝔹^(univ^kⱼ)`: a
  candidate gives each `kⱼ`-tuple of the universe `true` or `false`, a set of tuples;
* a condition `c` built with `and`, `or` and `not` from tests "this relation has a
  tuple" (γ with `bool_or` of `true`);
* relations built from three atoms (a symbol on variables, a member on variables, and
  `x = y`), each written as Codd's gadget, with `join`, `union`, `except` (both sides on
  the same variables), `except` from the universe on the same variables, and `pi` that
  drops one variable.

Every attribute in it is `x_v` for a variable `v`, `c0, c1, …`, `holds` or `e`, and every
attribute of a variable has the universe as its domain.

## The results

* `boolSelection_definable_in_ESO`: for every BoolSelection statement `r` there is an ESO
  sentence `ψ` such that, on every well-formed structure `A` whose universe does not mix
  integers and floats, the program "the data statements of `A`, then `eso := r`" runs, and
  `eso` has a candidate exactly when `ψ` holds on `A`.
* `Sentence.toQuery_stmt_expresses`: every ESO sentence has a BoolSelection statement
  with the same meaning.
* `eso_iff_boolSelection`: so a property of such structures is defined by an ESO sentence
  exactly when a BoolSelection program states it. With Fagin's theorem (cited, not
  proved here) these are the NP properties.

## Conventions

* **The fragment is defined by its grammar,** as the image of `Query.stmt`.
  `Rasso.ESO.Recognise` decides membership (`isBoolSelection_iff`).
* **Fixed names.** The fragment uses the names `univ`, `rel_i_n`, `member_R`, `x_v`, `c0…`,
  `holds` and `e`. A program that renames them is not in the fragment, although it states
  the same property. Closing the fragment under renaming is open.
* **The data statements** are `dataFor S A`: `univ`, then `rel_i_n` for each listed symbol
  and arity. The converse uses the symbols the statement reads.
* **Optimisation is outside this result.** Objectives, `enumerate` and decisions other than
  `bool` are not in the fragment. NP optimisation problems are a later question.
-/

namespace Rasso.ESO

open Rasso

/-! ## Expressions and conditions, with the universe and the data as parameters -/

namespace QE

/-- The Rasso form of an expression, with the universe given by `U` and symbol `i` at
arity `n` given by `R i n`. -/
def toExprP (U : Expr) (R : String → Nat → Expr) (ar : List (String × Nat)) : QE → Expr
  | rel i args => compileP U R ar (.rel i args)
  | member j args => compileP U R ar (.gvar j args)
  | eq x y => compileP U R ar (.eq x y)
  | join a b => .nary .join [a.toExprP U R ar, b.toExprP U R ar]
  | union a b => .nary .union [a.toExprP U R ar, b.toExprP U R ar]
  | diff a b => .nary .except [a.toExprP U R ar, b.toExprP U R ar]
  | proj x a => .project ((a.hdr.filter (· != x)).map varAttr) (a.toExprP U R ar)
  | not a => .nary .except [domOfP U a.hdr, a.toExprP U R ar]

theorem toExpr_eq_toExprP (A : Str) (ar : List (String × Nat)) :
    ∀ e : QE, e.toExpr A ar = e.toExprP (univLit A) (relLit A) ar := by
  intro e
  induction e with
  | rel => rfl
  | member => rfl
  | eq => rfl
  | join a b iha ihb => simp only [toExpr, toExprP, iha, ihb]
  | union a b iha ihb => simp only [toExpr, toExprP, iha, ihb]
  | diff a b iha ihb => simp only [toExpr, toExprP, iha, ihb]
  | proj x a ih => simp only [toExpr, toExprP, ih]
  | not a ih => simp only [toExpr, toExprP, ih]

theorem rels_proj (x : String) (a : QE) : (QE.proj x a).toFO.rels = a.toFO.rels := by
  simp only [toFO]; split <;> rfl

end QE

namespace QC

/-- The condition, with the universe given by `U` and the data by `R`. -/
def toCondP (U : Expr) (R : String → Nat → Expr) (ar : List (String × Nat)) : QC → Cond
  | some e => nonEmpty (e.close.toExprP U R ar)
  | not c => .not (c.toCondP U R ar)
  | and c d => .and [c.toCondP U R ar, d.toCondP U R ar]
  | or c d => .or [c.toCondP U R ar, d.toCondP U R ar]

theorem toCond_eq_toCondP (A : Str) (ar : List (String × Nat)) :
    ∀ c : QC, c.toCond A ar = c.toCondP (univLit A) (relLit A) ar := by
  intro c
  induction c with
  | some e => simp only [toCond, toCondP, QE.toExpr_eq_toExprP]
  | not c ih => simp only [toCond, toCondP, ih]
  | and c d ihc ihd => simp only [toCond, toCondP, ihc, ihd]
  | or c d ihc ihd => simp only [toCond, toCondP, ihc, ihd]

end QC

/-- The multi solution set of a query, with the universe given by `U` and the data by
`R`. -/
def Query.formP (Q : Query) (U : Expr) (R : String → Nat → Expr) : Expr :=
  .omegaMsol (membersP U Q.ar) (some (Q.cond.toCondP U R Q.ar))

theorem Query.form_eq_formP (Q : Query) (A : Str) :
    Q.form A = Q.formP (univLit A) (relLit A) := by
  simp only [Query.form, Query.formP, QC.toCond_eq_toCondP]

/-! ## The fragment -/

/-- **The BoolSelection statement of a query.** It reads the universe as `univ` and the
data as `rel_i_n`, so it depends only on the query, not on the structure. -/
def Query.stmt (Q : Query) : Expr := Q.formP (.name univName) RelN

/-- The symbols, with arities, that a query reads. -/
def Query.syms (Q : Query) : List (String × Nat) := Q.cond.toFO.rels

/-- **selection on Boolean function spaces.** A Rasso form is in the fragment when it is
the BoolSelection statement of a well-formed query. -/
def BoolSelection (r : Expr) : Prop := ∃ Q : Query, Q.WF ∧ Q.stmt = r

/-- The data statements of structure `A` for the symbols `S`: `univ`, then `rel_i_n` for
each symbol `i` at arity `n`. -/
def dataFor (S : List (String × Nat)) (A : Str) : List (String × Expr) :=
  (univName, univLit A) :: S.eraseDups.map fun (i, n) => relStatement A i n

theorem dataStmts_eq_dataFor (ψ : Sentence) (A : Str) : dataStmts ψ A = dataFor ψ.φ.rels A := rfl

/-- Run the data statements `D`, then `eso := r`, and answer: does `eso` have a
candidate? -/
def runEso (D : List (String × Expr)) (r : Expr) : Except String Bool := do
  let env ← runProgram (D ++ [(esoName, r)])
  match env.lookup esoName with
  | some (.msol m) => return !m.candidates.isEmpty
  | _ => throw "eso is not a multi solution set"

/-- The program `toProgram` is its data statements, then `eso`. -/
theorem decide_eq_runEso (ψ : Sentence) (A : Str) :
    ToProgram.decide ψ A = runEso (dataStmts ψ A) (esoStmt ψ).2 := by
  unfold ToProgram.decide runEso; rw [toProgram_eq]; rfl

/-! ## Named data and data in place agree -/

section Named

variable {A : Str}

theorem toExprP_congr {E E' : Env} {S : List (String × Nat)} (hE : DataEnv A S E E')
    (ar : List (String × Nat)) :
    ∀ e : QE, (∀ p ∈ e.toFO.rels, p ∈ S) →
      EvEq E E' (e.toExprP (.name univName) RelN ar) (e.toExprP (univLit A) (relLit A) ar)
  | .rel i args, hs => compileP_congr hE ar (.rel i args) hs
  | .member j args, hs => compileP_congr hE ar (.gvar j args) hs
  | .eq x y, hs => compileP_congr hE ar (.eq x y) hs
  | .join a b, hs => nary_congr
      (.cons (toExprP_congr hE ar a fun p hp => hs p (List.mem_append_left _ hp))
        (.cons (toExprP_congr hE ar b fun p hp => hs p (List.mem_append_right _ hp)) .nil))
  | .union a b, hs => nary_congr
      (.cons (toExprP_congr hE ar a fun p hp => hs p (List.mem_append_left _ hp))
        (.cons (toExprP_congr hE ar b fun p hp => hs p (List.mem_append_right _ hp)) .nil))
  | .diff a b, hs => nary_congr
      (.cons (toExprP_congr hE ar a fun p hp => hs p (List.mem_append_left _ hp))
        (.cons (toExprP_congr hE ar b fun p hp => hs p (List.mem_append_right _ hp)) .nil))
  | .proj x a, hs => project_congr (toExprP_congr hE ar a fun p hp => hs p (by rw [QE.rels_proj]; exact hp))
  | .not a, hs => nary_congr
      (.cons (domOfP_congr hE.univ _) (.cons (toExprP_congr hE ar a hs) .nil))

theorem rels_projs : ∀ (xs : List String) (e : QE), (QE.projs xs e).toFO.rels = e.toFO.rels
  | [], _ => rfl
  | x :: xs, e => by rw [QE.projs, rels_projs xs, QE.rels_proj]

theorem toCondP_congr {E E' : Env} {S : List (String × Nat)} (hE : DataEnv A S E E')
    (ar : List (String × Nat)) :
    ∀ c : QC, (∀ p ∈ c.toFO.rels, p ∈ S) →
      Cond.eval E [] (c.toCondP (.name univName) RelN ar) =
        Cond.eval E' [] (c.toCondP (univLit A) (relLit A) ar)
  | .some e, hs => nonEmpty_congr hE.cond
      (toExprP_congr hE ar e.close fun p hp => hs p hp)
  | .not c, hs => by
    simp only [QC.toCondP, Cond.eval, toCondP_congr hE ar c hs]
  | .and c d, hs => by
    simp only [QC.toCondP, Cond.eval, List.attach, List.attachWith, List.pmap, List.allM,
      toCondP_congr hE ar c fun p hp => hs p (List.mem_append_left _ hp),
      toCondP_congr hE ar d fun p hp => hs p (List.mem_append_right _ hp)]
  | .or c d, hs => by
    simp only [QC.toCondP, Cond.eval, List.attach, List.attachWith, List.pmap, List.anyM,
      toCondP_congr hE ar c fun p hp => hs p (List.mem_append_left _ hp),
      toCondP_congr hE ar d fun p hp => hs p (List.mem_append_right _ hp)]

/-- In the program's environment, the BoolSelection statement has the value of the
multi solution set with the data in place. -/
theorem query_stmt {Q : Query} {E0 : Env} (hP : ProgEnv A Q.syms E0) :
    EvEq E0 [] Q.stmt (Q.form A) := by
  rw [Query.form_eq_formP]
  unfold Query.stmt Query.formP
  refine omegaMsol_congr (membersP_congr hP.univ _) fun sols hs db hdb => ?_
  exact toCondP_congr (dataEnv_cond hP db (db_memberNames hs hdb)) _ _ fun p hp => hp

end Named

/-! ## The program of a BoolSelection statement -/

theorem runEso_of {D : List (String × Expr)} (hD : Lits D) {r : Expr} {m : Msol}
    (hr : Expr.eval ((D.map fun s => (s.1, litVal s.2)).reverse) [] r = .ok (.msol m))
    (hn : ∀ s ∈ D, s.1 ≠ esoName) :
    runEso D r = .ok (!m.candidates.isEmpty) := by
  unfold runEso runProgram
  rw [List.foldlM_append, foldlM_lits _ _ hD]
  simp only [List.nil_append, bind, Except.bind, List.foldlM_cons, List.foldlM_nil, hr]
  have hl : ((D.map fun s => (s.1, litVal s.2)) ++ [(esoName, Val.msol m)]).lookup esoName =
      some (.msol m) := by
    refine lookup_unique (List.mem_append_right _ (List.mem_singleton_self _)) fun p hp e => ?_
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
      exact absurd e (hn s hs)
    · rw [List.mem_singleton.mp hp]
  simp only [pure, Except.pure] at hl ⊢
  rw [hl]

theorem dataFor_names (S : List (String × Nat)) (A : Str) : ∀ s ∈ dataFor S A, s.1 ≠ esoName := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact univName_ne_esoName
  · obtain ⟨⟨i, n⟩, -, rfl⟩ := List.mem_map.mp hs
    exact relName_ne_esoName _ _

/-- **A BoolSelection program is an ESO sentence.** Run the data statements of `A`, then
`eso := Q.stmt`: on every well-formed structure that does not mix integers and floats, the
program is not refused, and `eso` has a candidate exactly when the query's sentence holds. -/
theorem Query.stmt_expresses (Q : Query) (w : Q.WF) (A : Str) (hA : A.WF) (hC : A.Comparable) :
    ∃ b, runEso (dataFor Q.syms A) Q.stmt = .ok b ∧ (b = true ↔ (Q.toSentence w).Holds A) := by
  obtain ⟨m, hm, hiff⟩ := Q.form_expresses w A hA hC
  have hP : ProgEnv A Q.syms (progEnv (Q.toSentence w) A) := progEnv_spec (Q.toSentence w) hA
  have he := (query_stmt hP).trans hm
  refine ⟨!m.candidates.isEmpty, ?_, ?_⟩
  · exact runEso_of (lits_dataStmts (Q.toSentence w) hA) he (dataFor_names _ A)
  · rw [← hiff]
    cases h : m.candidates with
    | nil => simp
    | cons db _ => simp

/-- **The converse, for Rasso programs.** Every BoolSelection statement `r` is defined by
one ESO sentence `ψ`, for all well-formed structures that do not mix integers and floats:
the program "the data statements of `A` for the symbols `ψ` reads, then `eso := r`" runs,
and `eso` has a candidate exactly when `ψ` holds on `A`. -/
theorem boolSelection_definable_in_ESO {r : Expr} (h : BoolSelection r) :
    ∃ ψ : Sentence, ∀ A : Str, A.WF → A.Comparable →
      ∃ b, runEso (dataFor ψ.φ.rels A) r = .ok b ∧ (b = true ↔ ψ.Holds A) := by
  obtain ⟨Q, w, rfl⟩ := h
  exact ⟨Q.toSentence w, Q.stmt_expresses w⟩

/-- **Every ESO sentence has a BoolSelection statement** with the same meaning. -/
theorem Sentence.toQuery_stmt_expresses (ψ : Sentence) (A : Str) (hA : A.WF) (hC : A.Comparable) :
    BoolSelection ψ.toQuery.stmt ∧
      ∃ b, runEso (dataFor ψ.toQuery.syms A) ψ.toQuery.stmt = .ok b ∧ (b = true ↔ ψ.Holds A) := by
  refine ⟨⟨ψ.toQuery, ψ.toQuery_wf, rfl⟩, ?_⟩
  obtain ⟨b, hb, hiff⟩ := ψ.toQuery.stmt_expresses ψ.toQuery_wf A hA hC
  exact ⟨b, hb, hiff.trans (ψ.toQuery_holds A)⟩

/-- **ESO is selection on Boolean function spaces.** On well-formed structures that do not
mix integers and floats, a property is defined by an ESO sentence exactly when a
BoolSelection program states it: some BoolSelection statement, run after the
data statements, has a candidate exactly on the structures with the property. -/
theorem eso_iff_boolSelection (P : Str → Prop) :
    (∃ ψ : Sentence, ∀ A, A.WF → A.Comparable → (P A ↔ ψ.Holds A)) ↔
      (∃ (Q : Query) (_ : Q.WF), ∀ A, A.WF → A.Comparable →
        ∃ b, runEso (dataFor Q.syms A) Q.stmt = .ok b ∧ (P A ↔ b = true)) := by
  constructor
  · rintro ⟨ψ, h⟩
    refine ⟨ψ.toQuery, ψ.toQuery_wf, fun A hA hC => ?_⟩
    obtain ⟨-, b, hb, hiff⟩ := ψ.toQuery_stmt_expresses A hA hC
    exact ⟨b, hb, (h A hA hC).trans hiff.symm⟩
  · rintro ⟨Q, w, h⟩
    refine ⟨Q.toSentence w, fun A hA hC => ?_⟩
    obtain ⟨b, hb, hP⟩ := h A hA hC
    obtain ⟨b', hb', hiff⟩ := Q.stmt_expresses w A hA hC
    rw [hb] at hb'
    cases hb'
    exact hP.trans hiff

/-! ## Examples: BoolSelection programs, run

A test, not a proof. Each `#guard` runs a BoolSelection program (data statements, then
`eso := Q.stmt`) with Rasso's evaluator. -/

namespace Examples

open Rasso.ESO.Examples

-- The query "some edge ends in a vertex of R" as a Rasso program.
#guard (runEso (dataFor edgeIntoMember.syms path3) edgeIntoMember.stmt).toOption == some true
#guard (runEso (dataFor edgeIntoMember.syms oneBare) edgeIntoMember.stmt).toOption == some false

-- SAT, Fagin style, as the BoolSelection statement of its sentence.
#guard (runEso (dataFor satSentence.toQuery.syms cnfYes) satSentence.toQuery.stmt).toOption == some true
#guard (runEso (dataFor satSentence.toQuery.syms cnfNo) satSentence.toQuery.stmt).toOption == some false

-- 2-colouring: a path (yes) and a triangle (no).
#guard (runEso (dataFor twoColour.toQuery.syms path3) twoColour.toQuery.stmt).toOption == some true
#guard (runEso (dataFor twoColour.toQuery.syms triangle) twoColour.toQuery.stmt).toOption == some false

end Examples

end Rasso.ESO
