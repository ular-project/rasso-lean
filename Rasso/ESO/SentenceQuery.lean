import Rasso.ESO.Converse

/-!
# ESO: every sentence is a BoolSelection query

The forward theorem (`Rasso.ESO.Capture`) and the converse (`Rasso.ESO.Converse`) are
about two shapes of multi solution set. This file makes them meet: every ESO
sentence is a `Query` whose read-back sentence holds on exactly the same structures.
So the properties that BoolSelection multi solution sets decide are exactly the
ESO-definable ones (`eso_iff_query`).

The translation `ofFO` is Codd's, written as a `QE`:

* atoms are atoms; `and` is ⋈; `not` is `QE.not` (every assignment minus the relation);
* `or` joins each side with `x = x` for each variable that only the other side has, so
  both sides have the same variables, then takes ∪;
* `∃ x φ` joins with `x = x` (so `x` is always there, which makes `∃ x φ` false on an
  empty universe when `x` is not free in `φ`), then drops `x`;
* `∀ x φ` is `not ∃ x not φ`.

Conventions:

* `x = x` stands for "every value of `x`": its relation is the universe once.
-/

namespace Rasso.ESO

open Rasso

namespace QE

/-- Join `e` with `y = y` for each `y` in `ys`. -/
def pad (e : QE) : List String → QE
  | [] => e
  | y :: ys => pad (.join e (.eq y y)) ys

end QE

/-- Codd's translation of a formula into a BoolSelection expression. -/
def ofFO : FO → QE
  | .rel i args => .rel i args
  | .gvar j args => .member j args
  | .eq x y => .eq x y
  | .not φ => .not (ofFO φ)
  | .and φ ψ => .join (ofFO φ) (ofFO ψ)
  | .or φ ψ => .union (QE.pad (ofFO φ) ψ.fv) (QE.pad (ofFO ψ) φ.fv)
  | .ex x φ => .proj x (QE.pad (ofFO φ) [x])
  | .all x φ => .not (.proj x (QE.pad (.not (ofFO φ)) [x]))

open Converse

theorem mem_hdr_pad : ∀ {e : QE} {ys : List String} {y : String},
    y ∈ (e.pad ys).hdr ↔ y ∈ e.hdr ∨ y ∈ ys
  | e, [], y => by simp [QE.pad]
  | e, z :: ys, y => by
    rw [QE.pad, mem_hdr_pad, mem_hdr_join]
    simp [QE.hdr, List.mem_eraseDups]
    constructor
    · rintro ((h | h) | h)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h

theorem wf_pad : ∀ {e : QE} {ys : List String}, e.WF → (e.pad ys).WF
  | _, [], w => w
  | _, _ :: _, w => wf_pad (e := .join _ _) ⟨w, trivial⟩

theorem sat_pad {A : Str} {G : Guess} : ∀ {e : QE} {ys : List String} {ρ : String → Value},
    (e.pad ys).toFO.Sat A G ρ ↔ e.toFO.Sat A G ρ
  | _, [], _ => Iff.rfl
  | e, y :: ys, ρ => by
    rw [QE.pad, sat_pad]
    simp [QE.toFO, FO.Sat]

theorem mem_hdr_ofFO : ∀ (φ : FO) (y : String), y ∈ (ofFO φ).hdr ↔ y ∈ φ.fv
  | .rel i args, y => List.mem_eraseDups
  | .gvar j args, y => List.mem_eraseDups
  | .eq x z, y => List.mem_eraseDups
  | .not φ, y => mem_hdr_ofFO φ y
  | .and φ ψ, y => by
    rw [ofFO, mem_hdr_join, mem_hdr_ofFO φ, mem_hdr_ofFO ψ]; simp [FO.fv]
  | .or φ ψ, y => by
    simp only [ofFO, QE.hdr]
    rw [mem_hdr_pad, mem_hdr_ofFO φ]; simp [FO.fv]
  | .ex x φ, y => by
    rw [ofFO, mem_hdr_proj, mem_hdr_pad, mem_hdr_ofFO φ]
    simp only [FO.fv, List.mem_filter, List.mem_singleton, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact ⟨h, by simpa using h'⟩
      · exact absurd h h'
    · rintro ⟨h, h'⟩; exact ⟨.inl h, by simpa using h'⟩
  | .all x φ, y => by
    show y ∈ (QE.proj x (QE.pad (.not (ofFO φ)) [x])).hdr ↔ _
    rw [mem_hdr_proj, mem_hdr_pad]
    show (y ∈ (ofFO φ).hdr ∨ _) ∧ _ ↔ _
    rw [mem_hdr_ofFO φ]
    simp only [FO.fv, List.mem_filter, List.mem_singleton, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact ⟨h, by simpa using h'⟩
      · exact absurd h h'
    · rintro ⟨h, h'⟩; exact ⟨.inl h, by simpa using h'⟩

theorem wf_ofFO : ∀ φ : FO, (ofFO φ).WF
  | .rel .. | .gvar .. | .eq .. => trivial
  | .not φ => wf_ofFO φ
  | .and φ ψ => ⟨wf_ofFO φ, wf_ofFO ψ⟩
  | .or φ ψ => ⟨wf_pad (wf_ofFO φ), wf_pad (wf_ofFO ψ), fun y => by
      rw [mem_hdr_pad, mem_hdr_pad, mem_hdr_ofFO, mem_hdr_ofFO]
      constructor <;> rintro (h | h) <;> first | exact .inl h | exact .inr h⟩
  | .ex x φ => wf_pad (wf_ofFO φ)
  | .all x φ => wf_pad (e := .not _) (wf_ofFO φ)

theorem sat_ofFO {A : Str} {G : Guess} : ∀ (φ : FO) (ρ : String → Value),
    (ofFO φ).toFO.Sat A G ρ ↔ φ.Sat A G ρ
  | .rel .., _ | .gvar .., _ | .eq .., _ => Iff.rfl
  | .not φ, ρ => not_congr (sat_ofFO φ ρ)
  | .and φ ψ, ρ => and_congr (sat_ofFO φ ρ) (sat_ofFO ψ ρ)
  | .or φ ψ, ρ => by
    simp only [ofFO, QE.toFO, FO.Sat]
    rw [sat_pad, sat_pad, sat_ofFO φ, sat_ofFO ψ]
  | .ex x φ, ρ => by
    have hx : (QE.pad (ofFO φ) [x]).hdr.contains x = true :=
      List.contains_iff_mem.mpr (mem_hdr_pad.mpr (.inr (List.mem_singleton_self x)))
    simp only [ofFO, QE.toFO, hx, ite_true, FO.Sat]
    exact ⟨fun ⟨a, ha, h⟩ => ⟨a, ha, (sat_ofFO φ _).mp (sat_pad.mp h)⟩,
      fun ⟨a, ha, h⟩ => ⟨a, ha, sat_pad.mpr ((sat_ofFO φ _).mpr h)⟩⟩
  | .all x φ, ρ => by
    have hx : (QE.pad (QE.not (ofFO φ)) [x]).hdr.contains x = true :=
      List.contains_iff_mem.mpr (mem_hdr_pad.mpr (.inr (List.mem_singleton_self x)))
    simp only [ofFO, QE.toFO, hx, ite_true, FO.Sat]
    constructor
    · intro h a ha
      exact Decidable.byContradiction fun hn =>
        h ⟨a, ha, sat_pad.mpr (show ¬ _ from fun h' => hn ((sat_ofFO φ _).mp h'))⟩
    · rintro h ⟨a, ha, h'⟩
      exact (show ¬ _ from sat_pad.mp h') ((sat_ofFO φ _).mpr (h a ha))

/-- The BoolSelection query of a sentence. -/
def Sentence.toQuery (ψ : Sentence) : Query := ⟨ψ.ar, .some (ofFO ψ.φ)⟩

theorem Sentence.toQuery_wf (ψ : Sentence) : ψ.toQuery.WF := wf_ofFO ψ.φ

/-- **Every ESO sentence is a BoolSelection query**: the query's sentence holds on
exactly the structures where `ψ` holds. -/
theorem Sentence.toQuery_holds (ψ : Sentence) (A : Str) :
    (ψ.toQuery.toSentence ψ.toQuery_wf).Holds A ↔ ψ.Holds A := by
  have hnil : (ofFO ψ.φ).hdr = [] := by
    match h : (ofFO ψ.φ).hdr with
    | [] => rfl
    | y :: _ =>
      have := (mem_hdr_ofFO ψ.φ y).mp (by rw [h]; exact List.mem_cons_self ..)
      have hc := ψ.closed
      rw [List.isEmpty_iff] at hc
      rw [hc] at this; cases this
  have hclose : (ofFO ψ.φ).close = ofFO ψ.φ := by
    rw [QE.close, hnil]; rfl
  simp only [Sentence.Holds, Query.toSentence, Sentence.toQuery, QC.toFO, hclose]
  exact ⟨fun ⟨G, hG, h⟩ => ⟨G, hG, (sat_ofFO _ _).mp h⟩,
    fun ⟨G, hG, h⟩ => ⟨G, hG, (sat_ofFO _ _).mpr h⟩⟩

/-- **Capture.** On well-formed structures that do not mix ints and floats, a property is
defined by an ESO sentence exactly when it is decided by a BoolSelection multi
solution set ("it has a candidate"). -/
theorem eso_iff_query (P : Str → Prop) :
    (∃ ψ : Sentence, ∀ A, A.WF → A.Comparable → (P A ↔ ψ.Holds A)) ↔
      (∃ (Q : Query) (_ : Q.WF), ∀ A, A.WF → A.Comparable →
        ∃ m, Expr.eval [] [] (Q.form A) = .ok (.msol m) ∧ (P A ↔ ∃ db, db ∈ m.candidates)) := by
  constructor
  · rintro ⟨ψ, h⟩
    refine ⟨ψ.toQuery, ψ.toQuery_wf, fun A hA hC => ?_⟩
    obtain ⟨m, hm, hiff⟩ := ψ.toQuery.form_expresses ψ.toQuery_wf A hA hC
    exact ⟨m, hm, (h A hA hC).trans ((ψ.toQuery_holds A).symm.trans hiff.symm)⟩
  · rintro ⟨Q, w, h⟩
    refine ⟨Q.toSentence w, fun A hA hC => ?_⟩
    obtain ⟨m, hm, hP⟩ := h A hA hC
    obtain ⟨m', hm', hiff⟩ := Q.form_expresses w A hA hC
    rw [hm] at hm'
    cases hm'
    exact hP.trans hiff

end Rasso.ESO
