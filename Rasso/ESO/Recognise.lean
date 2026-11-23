import Rasso.FormEq
import Rasso.ESO.BoolSelection

/-!
# A recogniser for selection on Boolean function spaces

`isBoolSelection r` decides whether the Rasso form `r` is in selection on Boolean function spaces
(`BoolSelection r`: `r` is the statement `Q.stmt` of some well-formed query `Q`).
`isBoolSelection_iff` proves that it returns `true` exactly on the fragment, and the
`DecidablePred BoolSelection` instance follows.

## How it works

1. **Read back.** `queryCands r` reads `r` back as a short list of candidate queries. It
   undoes the rendering of `Query.stmt` node by node: the members give the arities, γ with
   no grouping gives a test "has a tuple", the atom gadgets give atoms (the names
   `x_v`, `rel_i_n` and `member_R` are decoded), and `join`, `union`, `except` and `pi` give
   the operators.
2. **Check.** `isBoolSelection r` keeps a candidate `Q` when `Q` is well formed (`Query.wfb`)
   and `Q.stmt = r` (decidable equality of forms, `Rasso.FormEq`).

**Soundness** (`true` → in the fragment) is the check. **Completeness** (in the fragment →
`true`) is the work of this file: for every well-formed query `Q`, the read-back of
`Q.stmt` has a candidate `Q'` with `Q'.stmt = Q.stmt` (`queryCands_complete`). It need
not be `Q` itself, because the rendering forgets some things. Three places forget:

* a member that is not listed at its arity renders as the empty relation, without its name
  (the read-back invents a fresh name);
* a projection of a variable that is not there renders as the identity projection,
  without the variable (the read-back invents a fresh variable);
* a difference from the universe can be a `not` or a `diff` with an atom `x = x` (the
  read-back keeps both readings).

## Membership and equivalence

Membership in the fragment is a question about syntax, and it is decidable. Whether a
Rasso program *states the same property as* some BoolSelection program is a question
about meaning. This file says nothing about it. (Already for two BoolSelection programs
with no members, it asks whether two first-order sentences agree on all finite structures,
which Trakhtenbrot's theorem makes undecidable; that argument is in the blueprint, not in
Lean.)

## Conventions

* The recogniser is about the fragment as defined: fixed names (`univ`, `rel_i_n`,
  `member_R`, `x_v`). A renamed copy of a BoolSelection statement is rejected.
* No claim about speed. The read-back can return several candidates at each `except`
  and each projection; the number is finite and small on the examples.
-/

namespace Rasso.ESO

open Rasso

namespace Recognise

/-! ## Decoding names -/

/-- `x_v` ↦ `v`. -/
def unVar (s : String) : Option String :=
  match s.toList with
  | 'x' :: '_' :: rest => some (String.ofList rest)
  | _ => none

/-- `member_R` ↦ `R`. -/
def unMember (s : String) : Option String :=
  match s.toList with
  | 'm' :: 'e' :: 'm' :: 'b' :: 'e' :: 'r' :: '_' :: rest => some (String.ofList rest)
  | _ => none

/-- `rel_i_n` ↦ `i`, given the arity `n`. -/
def unRel (s : String) (n : Nat) : Option String :=
  match s.toList with
  | 'r' :: 'e' :: 'l' :: '_' :: rest =>
    some (String.ofList (rest.take (rest.length - ((Nat.toDigits 10 n).length + 1))))
  | _ => none

theorem unVar_varAttr (x : String) : unVar (varAttr x) = some x := by
  simp [unVar, varAttr, String.toList_append]

theorem unMember_memberName (j : String) : unMember (memberName j) = some j := by
  simp [unMember, memberName, String.toList_append]

theorem unRel_relName (i : String) (n : Nat) : unRel (relName i n) n = some i := by
  simp only [unRel, relName_toList]
  have : (i.toList ++ '_' :: Nat.toDigits 10 n).length - ((Nat.toDigits 10 n).length + 1) =
      i.toList.length := by
    simp only [List.length_append, List.length_cons]; omega
  rw [this, List.take_left' rfl]
  simp

/-! ## Fresh names -/

/-- A name longer than every name in `l`. -/
def fresh (l : List String) : String :=
  String.ofList (List.replicate (l.foldr (fun s m => max s.length m) 0 + 1) 'z')

theorem le_foldr_max : ∀ {l : List String} {s : String}, s ∈ l →
    s.length ≤ l.foldr (fun s m => max s.length m) 0
  | _ :: _, _, .head _ => by simp only [List.foldr_cons]; exact Nat.le_max_left _ _
  | _ :: _, _, .tail _ h => by simp only [List.foldr_cons]; exact Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

theorem fresh_not_mem (l : List String) : fresh l ∉ l := fun h => by
  have := le_foldr_max h
  simp [fresh] at this
  omega

/-! ## Lists -/

theorem mapM_map_some {α β γ : Type} (f : α → β) (g : β → Option γ) (k : α → γ)
    (h : ∀ a, g (f a) = some (k a)) : ∀ l : List α, (l.map f).mapM g = some (l.map k)
  | [] => rfl
  | a :: l => by simp [List.mapM_cons, h, mapM_map_some f g k h l]

theorem eraseDups_of_nodup : ∀ {l : List String}, l.Nodup → l.eraseDups = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.eraseDups_cons]
    have ha : a ∉ l := (List.nodup_cons.mp h).1
    have hf : l.filter (fun b => !b == a) = l :=
      List.filter_eq_self.mpr fun b hb => by
        have : b ≠ a := fun e => ha (e ▸ hb)
        simpa using this
    rw [hf, eraseDups_of_nodup (List.nodup_cons.mp h).2]

theorem eraseDups_idem (l : List String) : l.eraseDups.eraseDups = l.eraseDups :=
  eraseDups_of_nodup (Converse.nodup_eraseDups l)

/-! ## Reading back the building blocks -/

/-- The variables of `domOfP univ xs`. -/
def unDom : Expr → Option (List String)
  | .omegaRows [] [[]] => some []
  | .rename [(_, a)] (.name _) => (unVar a).map ([·])
  | .nary .join rs => rs.mapM fun
    | .rename [(_, a)] (.name _) => unVar a
    | _ => none
  | _ => none

/-- The number of copies in `univPowP univ f as`. -/
def countOf : Expr → Option Nat
  | .omegaRows [] [[]] => some 0
  | .rename _ _ => some 1
  | .nary .join rs => some rs.length
  | _ => none

abbrev U : Expr := .name univName

theorem unDom_domOfP (xs : List String) : unDom (domOfP U xs) = some xs := by
  unfold domOfP univPowP
  match xs with
  | [] => rfl
  | [x] => simp [joinAll, unDom, unVar_varAttr]
  | x :: y :: rest =>
    simp only [List.map_cons, joinAll, unDom]
    have := mapM_map_some (fun a => Expr.rename [(univAttr, varAttr a)] U)
      (fun | .rename [(_, a)] (.name _) => unVar a | _ => none) id
      (fun a => by simp [unVar_varAttr]) (x :: y :: rest)
    simpa using this

theorem countOf_univPowP (f : String → String) (as : List String) :
    countOf (univPowP U f as) = some as.length := by
  unfold univPowP
  match as with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: rest => simp [joinAll, countOf]

/-- The arities of the members. -/
def decMembers (ms : List (String × Expr)) : Option (List (String × Nat)) :=
  ms.mapM fun p => match unMember p.1, p.2 with
    | some j, .omegaSol d _ => (countOf d).map (j, ·)
    | _, _ => none

theorem decMembers_membersP (ar : List (String × Nat)) :
    decMembers (membersP U ar) = some (memsOf ar) := by
  rw [membersP_eq]
  unfold decMembers
  have := mapM_map_some (fun (p : String × Nat) => boolMemberP U p.1 p.2)
    (fun p => match unMember p.1, p.2 with
      | some j, .omegaSol d _ => (countOf d).map (j, ·)
      | _, _ => none) id
    (fun p => by simp [boolMemberP, unMember_memberName, countOf_univPowP, cols]) (memsOf ar)
  simpa using this

/-- The tests an atom's selection may be the conjunction of. -/
def termLists (t : Term) : List (List Term) :=
  [[], [t]] ++ match t with
    | .call "and" ts => [ts]
    | _ => []

theorem mem_termLists_conj (L : List Term) : L ∈ termLists (conj L) := by
  match L with
  | [] => simp [termLists]
  | [t] => simp [termLists, conj]
  | a :: b :: rest => simp [termLists, conj]

/-- The variables an atom's tests compare its columns with. -/
def argsOf (ts : List Term) : Option (List String) :=
  ts.mapM fun
    | .call "=" [.attr _, .attr a] => unVar a
    | _ => none

theorem argsOf_eqs (n : Nat) (args : List String) (h : args.length = n) :
    argsOf (((cols n).zip args).map fun p => eqT p.1 (varAttr p.2)) = some args := by
  unfold argsOf
  have := mapM_map_some (fun (p : String × String) => eqT p.1 (varAttr p.2))
    (fun | .call "=" [.attr _, .attr a] => unVar a | _ => none) Prod.snd
    (fun p => by simp [eqT, unVar_varAttr]) ((cols n).zip args)
  rw [List.map_snd_zip (by simp [cols, h])] at this
  simpa using this

/-! ## Reading back expressions -/

/-- Atoms: a symbol or a member on variables. -/
def atomCands : Expr → List QE
  | .project _ (.select t (.nary .join [.name s, _])) =>
    (termLists t).flatMap fun ts =>
      (match argsOf ts with
        | some args => (unRel s args.length).toList.map (QE.rel · args)
        | none => []) ++
      (match ts with
        | _ :: rest =>
          match argsOf rest, unMember s with
          | some args, some j => [QE.member j args]
          | _, _ => []
        | [] => [])
  | _ => []

/-- Atoms: equality of variables. -/
def eqCands : Expr → List QE
  | .rename [(_, a)] (.name _) => (unVar a).toList.map fun x => QE.eq x x
  | .select (.call "=" [.attr a, .attr b]) _ =>
    match unVar a, unVar b with
    | some x, some y => [QE.eq x y]
    | _, _ => []
  | _ => []

/-- A member not listed at its arity: the empty relation, with a fresh name. -/
def freshCands (ar : List (String × Nat)) : Expr → List QE
  | .nary .except [d, _] => (unDom d).toList.map (QE.member (fresh (ar.map (·.1))))
  | _ => []

/-- The variables a projection may drop: one that the attributes leave out, or a fresh one. -/
def projVars (a : QE) (attrs : List String) : List String :=
  a.hdr.filter (fun y => !attrs.contains (varAttr y)) ++ [fresh a.hdr]

/-- The candidate expressions whose rendering may be `r`. -/
def cands (ar : List (String × Nat)) (r : Expr) : List QE :=
  atomCands r ++ eqCands r ++ freshCands ar r ++
  match r with
  | .nary .join [a, b] => (cands ar a).flatMap fun x => (cands ar b).map (QE.join x)
  | .nary .union [a, b] => (cands ar a).flatMap fun x => (cands ar b).map (QE.union x)
  | .nary .except [a, b] =>
    ((cands ar a).flatMap fun x => (cands ar b).map (QE.diff x)) ++ (cands ar b).map QE.not
  | .project attrs a => (cands ar a).flatMap fun x => (projVars x attrs).map (QE.proj · x)
  | _ => []

/-- The candidate conditions whose rendering may be `c`. -/
def condCands (ar : List (String × Nat)) : Cond → List QC
  | .expr (.gamma [] _ none x) => (cands ar x).map QC.some
  | .not c => (condCands ar c).map QC.not
  | .and [c, d] => (condCands ar c).flatMap fun x => (condCands ar d).map (QC.and x)
  | .or [c, d] => (condCands ar c).flatMap fun x => (condCands ar d).map (QC.or x)
  | _ => []

/-- The candidate queries whose statement may be `r`. -/
def queryCands : Expr → List Query
  | .omegaMsol ms (some c) =>
    match decMembers ms with
    | some ar => [ar, []].flatMap fun a => (condCands a c).map (Query.mk a)
    | none => []
  | _ => []

end Recognise

/-! ## Well-formedness, as a Boolean -/

namespace QE

def wfb : QE → Bool
  | join a b => a.wfb && b.wfb
  | union a b => a.wfb && b.wfb && a.hdr.all (b.hdr.contains ·) && b.hdr.all (a.hdr.contains ·)
  | diff a b => a.wfb && b.wfb && a.hdr.all (b.hdr.contains ·) && b.hdr.all (a.hdr.contains ·)
  | proj _ a => a.wfb
  | not a => a.wfb
  | _ => true

theorem sameVars_iff (a b : List String) :
    (a.all (b.contains ·) && b.all (a.contains ·)) = true ↔ ∀ y, y ∈ a ↔ y ∈ b := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  exact ⟨fun ⟨h1, h2⟩ y => ⟨h1 y, h2 y⟩, fun h => ⟨fun y => (h y).1, fun y => (h y).2⟩⟩

theorem wfb_iff : ∀ e : QE, e.wfb = true ↔ e.WF
  | .rel .. | .member .. | .eq .. => by simp [wfb, WF]
  | .join a b => by simp [wfb, WF, wfb_iff a, wfb_iff b]
  | .union a b => by
    rw [wfb, WF, Bool.and_assoc, Bool.and_eq_true, Bool.and_eq_true, sameVars_iff, wfb_iff a, wfb_iff b]
    exact and_assoc
  | .diff a b => by
    rw [wfb, WF, Bool.and_assoc, Bool.and_eq_true, Bool.and_eq_true, sameVars_iff, wfb_iff a, wfb_iff b]
    exact and_assoc
  | .proj _ a => by simp [wfb, WF, wfb_iff a]
  | .not a => by simp [wfb, WF, wfb_iff a]

end QE

def QC.wfb : QC → Bool
  | .some e => e.wfb
  | .not c => c.wfb
  | .and c d => c.wfb && d.wfb
  | .or c d => c.wfb && d.wfb

theorem QC.wfb_iff : ∀ c : QC, c.wfb = true ↔ c.WF
  | .some e => QE.wfb_iff e
  | .not c => QC.wfb_iff c
  | .and c d => by simp [QC.wfb, QC.WF, QC.wfb_iff c, QC.wfb_iff d]
  | .or c d => by simp [QC.wfb, QC.WF, QC.wfb_iff c, QC.wfb_iff d]

instance (Q : Query) : Decidable Q.WF := decidable_of_iff _ (QC.wfb_iff Q.cond)

/-! ## The recogniser -/

/-- **The recogniser.** Read `r` back as candidate queries; accept when one of them is well
formed and has `r` as its statement. -/
def isBoolSelection (r : Expr) : Bool :=
  (Recognise.queryCands r).any fun Q => decide Q.WF && decide (Q.stmt = r)

/-! ## Completeness -/

namespace Recognise

/-! ### The rendering depends on the arities only through `lookup` -/

theorem compileP_ar {ar ar' : List (String × Nat)} (h : ∀ j, ar.lookup j = ar'.lookup j)
    (V : Expr) (R : String → Nat → Expr) : ∀ φ : FO, compileP V R ar φ = compileP V R ar' φ
  | .rel .. | .eq .. => rfl
  | .gvar j args => by simp only [compileP, h j]
  | .not φ => by simp only [compileP, compileP_ar h V R φ]
  | .and φ ψ | .or φ ψ => by simp only [compileP, compileP_ar h V R φ, compileP_ar h V R ψ]
  | .ex x φ | .all x φ => by simp only [compileP, compileP_ar h V R φ]

theorem toExprP_ar {ar ar' : List (String × Nat)} (h : ∀ j, ar.lookup j = ar'.lookup j)
    (V : Expr) (R : String → Nat → Expr) : ∀ e : QE, e.toExprP V R ar = e.toExprP V R ar'
  | .rel .. | .member .. | .eq .. => compileP_ar h V R _
  | .join a b | .union a b | .diff a b => by
    simp only [QE.toExprP, toExprP_ar h V R a, toExprP_ar h V R b]
  | .proj _ a | .not a => by simp only [QE.toExprP, toExprP_ar h V R a]

theorem toCondP_ar {ar ar' : List (String × Nat)} (h : ∀ j, ar.lookup j = ar'.lookup j)
    (V : Expr) (R : String → Nat → Expr) : ∀ c : QC, c.toCondP V R ar = c.toCondP V R ar'
  | .some e => by simp only [QC.toCondP, toExprP_ar h V R]
  | .not c => by simp only [QC.toCondP, toCondP_ar h V R c]
  | .and c d | .or c d => by simp only [QC.toCondP, toCondP_ar h V R c, toCondP_ar h V R d]

/-! ### Members -/

theorem lookup_iff_mem : ∀ {l : List (String × Nat)}, (l.map (·.1)).Nodup →
    ∀ j k, l.lookup j = some k ↔ (j, k) ∈ l
  | [], _, _, _ => by simp [List.lookup]
  | (a, b) :: l, hn, j, k => by
    have ha : a ∉ l.map (·.1) := (List.nodup_cons.mp hn).1
    by_cases e : j = a
    · subst e
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq, List.mem_cons, Prod.mk.injEq,
        true_and]
      constructor
      · intro h; exact .inl h.symm
      · rintro (h | h)
        · exact h.symm
        · exact absurd (List.mem_map_of_mem (f := (·.1)) h) ha
    · have : (j == a) = false := by simpa using e
      simp only [List.lookup, this, List.mem_cons, Prod.mk.injEq, e, false_and, false_or]
      exact lookup_iff_mem (List.nodup_cons.mp hn).2 j k

theorem lookup_members (ar : List (String × Nat)) (j : String) :
    (members ar).lookup j = ar.lookup j := by
  cases h : ar.lookup j with
  | some k => exact (lookup_iff_mem (nodup_members ar) j k).mpr (mem_members.mpr h)
  | none =>
    cases h' : (members ar).lookup j with
    | none => rfl
    | some k =>
      have := mem_members.mp ((lookup_iff_mem (nodup_members ar) j k).mp h')
      rw [h] at this; cases this

theorem foldl_members_nodup : ∀ (l acc : List (String × Nat)), ((acc ++ l).map (·.1)).Nodup →
    l.foldl (fun acc (j, k) => if acc.any (·.1 == j) then acc else acc ++ [(j, k)]) acc = acc ++ l
  | [], acc, _ => by simp
  | (j, k) :: l, acc, hn => by
    simp only [List.foldl_cons]
    have hj : acc.any (·.1 == j) = false := by
      cases h : acc.any (·.1 == j)
      · rfl
      · have hm := any_fst_iff.mp h
        rw [List.map_append, List.nodup_append] at hn
        exact absurd rfl (hn.2.2 j hm j (by simp))
    simp only [hj, Bool.false_eq_true, ite_false]
    rw [foldl_members_nodup l (acc ++ [(j, k)]) (by simpa using hn)]
    simp

theorem members_members (ar : List (String × Nat)) : members (members ar) = members ar := by
  have := foldl_members_nodup (members ar) [] (by simpa using nodup_members ar)
  simpa [members] using this

theorem members_ne_nil {ar : List (String × Nat)} (h : ar ≠ []) : members ar ≠ [] := by
  match ar, h with
  | (j, k) :: l, _ =>
    intro e
    have := mem_members (ar := (j, k) :: l) (j := j) (k := k)
    rw [e] at this
    simp [List.lookup] at this

/-- Arities with the same members and the same lookups as `ar`, among the read-back's
two choices. -/
theorem ar_choice (ar : List (String × Nat)) :
    ∃ a ∈ [memsOf ar, []], membersP U a = membersP U ar ∧ ∀ j, a.lookup j = ar.lookup j := by
  cases hm : members ar with
  | nil =>
    have : ar = [] := by
      by_cases h : ar = []
      · exact h
      · exact absurd hm (members_ne_nil h)
    subst this
    exact ⟨[], by simp, rfl, fun _ => rfl⟩
  | cons p ps =>
    have hmo : memsOf ar = p :: ps := by unfold memsOf; rw [hm]
    refine ⟨p :: ps, by simp [hmo], ?_, fun j => by rw [← hm, lookup_members]⟩
    rw [membersP_eq, membersP_eq, hmo]
    unfold memsOf
    rw [← hm, members_members, hm]

/-! ### Expressions -/

abbrev rend (ar : List (String × Nat)) (e : QE) : Expr := e.toExprP U RelN ar

theorem mem_cands_atom {ar r e} (h : e ∈ atomCands r) : e ∈ cands ar r := by
  rw [cands.eq_def]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))
theorem mem_cands_eq {ar r e} (h : e ∈ eqCands r) : e ∈ cands ar r := by
  rw [cands.eq_def]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))
theorem mem_cands_fresh {ar r e} (h : e ∈ freshCands ar r) : e ∈ cands ar r := by
  rw [cands.eq_def]
  exact List.mem_append_left _ (List.mem_append_right _ h)

theorem mem_cands_join {ar a b x y} (hx : x ∈ cands ar a) (hy : y ∈ cands ar b) :
    QE.join x y ∈ cands ar (.nary .join [a, b]) := by
  rw [cands.eq_def]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩)
theorem mem_cands_union {ar a b x y} (hx : x ∈ cands ar a) (hy : y ∈ cands ar b) :
    QE.union x y ∈ cands ar (.nary .union [a, b]) := by
  rw [cands.eq_def]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩)
theorem mem_cands_diff {ar a b x y} (hx : x ∈ cands ar a) (hy : y ∈ cands ar b) :
    QE.diff x y ∈ cands ar (.nary .except [a, b]) := by
  rw [cands.eq_def]
  exact List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩))
theorem mem_cands_not {ar a b y} (hy : y ∈ cands ar b) :
    QE.not y ∈ cands ar (.nary .except [a, b]) := by
  rw [cands.eq_def]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_map.mpr ⟨y, hy, rfl⟩))
theorem mem_cands_proj {ar attrs a x z} (hx : x ∈ cands ar a) (hz : z ∈ projVars x attrs) :
    QE.proj z x ∈ cands ar (.project attrs a) := by
  rw [cands.eq_def]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨z, hz, rfl⟩⟩)

/-- What a candidate must keep: well-formedness, the variables, and the rendering. -/
abbrev Good (ar : List (String × Nat)) (e e' : QE) : Prop :=
  e'.WF ∧ e'.hdr = e.hdr ∧ rend ar e' = rend ar e

theorem cands_complete (ar : List (String × Nat)) :
    ∀ e : QE, e.WF → ∃ e' ∈ cands ar (rend ar e), Good ar e e'
  | .rel i args, _ => by
    refine ⟨.rel i args, mem_cands_atom ?_, trivial, rfl, rfl⟩
    simp only [rend, QE.toExprP, compileP, atomP, List.nil_append, atomCands, List.mem_flatMap]
    refine ⟨_, mem_termLists_conj _, ?_⟩
    simp [argsOf_eqs args.length args rfl, unRel_relName]
  | .member j args, _ => by
    by_cases hl : ar.lookup j = some args.length
    · refine ⟨.member j args, mem_cands_atom ?_, trivial, rfl, rfl⟩
      simp only [rend, QE.toExprP, compileP, hl, ite_true, atomP, atomCands, List.mem_flatMap,
        List.singleton_append]
      refine ⟨_, mem_termLists_conj _, ?_⟩
      simp [argsOf_eqs args.length args rfl, unMember_memberName]
    · have hf : ar.lookup (fresh (ar.map (·.1))) = none :=
        lookup_none_of_not_mem (fresh_not_mem _)
      refine ⟨.member (fresh (ar.map (·.1))) args.eraseDups, mem_cands_fresh ?_, trivial, ?_, ?_⟩
      · simp only [rend, QE.toExprP, compileP, hl, ite_false, emptyOnP, freshCands, unDom_domOfP]
        simp
      · simp only [QE.hdr, eraseDups_idem]
      · simp only [rend, QE.toExprP, compileP, hl, hf, ite_false, eraseDups_idem, reduceCtorEq]
  | .eq x y, _ => by
    by_cases e : x = y
    · subst e
      refine ⟨.eq x x, mem_cands_eq ?_, trivial, rfl, rfl⟩
      simp [rend, QE.toExprP, compileP, domOfP, univPowP, joinAll, eqCands, unVar_varAttr]
    · refine ⟨.eq x y, mem_cands_eq ?_, trivial, rfl, rfl⟩
      simp [rend, QE.toExprP, compileP, e, eqT, eqCands, unVar_varAttr]
  | .join a b, w => by
    obtain ⟨a', ha, wa, ha1, ha2⟩ := cands_complete ar a w.1
    obtain ⟨b', hb, wb, hb1, hb2⟩ := cands_complete ar b w.2
    refine ⟨.join a' b', ?_, ⟨wa, wb⟩, by simp [QE.hdr, ha1, hb1], by
      simp only [rend, QE.toExprP] at ha2 hb2 ⊢; rw [ha2, hb2]⟩
    exact mem_cands_join ha hb
  | .union a b, w => by
    obtain ⟨a', ha, wa, ha1, ha2⟩ := cands_complete ar a w.1
    obtain ⟨b', hb, wb, hb1, hb2⟩ := cands_complete ar b w.2.1
    refine ⟨.union a' b', ?_, ⟨wa, wb, by rw [ha1, hb1]; exact w.2.2⟩, by simp [QE.hdr, ha1], by
      simp only [rend, QE.toExprP] at ha2 hb2 ⊢; rw [ha2, hb2]⟩
    exact mem_cands_union ha hb
  | .diff a b, w => by
    obtain ⟨a', ha, wa, ha1, ha2⟩ := cands_complete ar a w.1
    obtain ⟨b', hb, wb, hb1, hb2⟩ := cands_complete ar b w.2.1
    refine ⟨.diff a' b', ?_, ⟨wa, wb, by rw [ha1, hb1]; exact w.2.2⟩, by simp [QE.hdr, ha1], by
      simp only [rend, QE.toExprP] at ha2 hb2 ⊢; rw [ha2, hb2]⟩
    exact mem_cands_diff ha hb
  | .not a, w => by
    obtain ⟨a', ha, wa, ha1, ha2⟩ := cands_complete ar a w
    refine ⟨.not a', ?_, wa, by simp [QE.hdr, ha1], by
      simp only [rend, QE.toExprP] at ha2 ⊢; rw [ha2, ha1]⟩
    exact mem_cands_not ha
  | .proj x a, w => by
    obtain ⟨a', ha, wa, ha1, ha2⟩ := cands_complete ar a w
    have mem_proj : ∀ z, z ∈ projVars a' ((a.hdr.filter (· != x)).map varAttr) →
        QE.proj z a' ∈ cands ar (rend ar (.proj x a)) := fun z hz => mem_cands_proj ha hz
    by_cases hx : x ∈ a.hdr
    · refine ⟨.proj x a', mem_proj x ?_, wa, by simp [QE.hdr, ha1], by
        simp only [rend, QE.toExprP] at ha2 ⊢; rw [ha2, ha1]⟩
      unfold projVars
      refine List.mem_append_left _ (List.mem_filter.mpr ⟨ha1 ▸ hx, ?_⟩)
      have : varAttr x ∉ (a.hdr.filter (· != x)).map varAttr := fun hm => by
        obtain ⟨y, hy, e⟩ := List.mem_map.mp hm
        have := varAttr_inj e; subst this; simp at hy
      simpa using this
    · have hf : fresh a.hdr ∉ a.hdr := fresh_not_mem a.hdr
      have keep : ∀ z, z ∉ a.hdr → a.hdr.filter (· != z) = a.hdr := fun z hz =>
        List.filter_eq_self.mpr fun b hb => by
          have : b ≠ z := fun e => hz (e ▸ hb)
          simpa using this
      refine ⟨.proj (fresh a'.hdr) a', mem_proj _ (by simp [projVars]), wa, ?_, ?_⟩
      · simp only [QE.hdr, ha1, keep _ hx, keep _ hf]
      · simp only [rend, QE.toExprP] at ha2 ⊢; rw [ha2]; simp only [ha1, keep _ hx, keep _ hf]

/-! ### Conditions and queries -/

theorem condCands_complete (ar : List (String × Nat)) :
    ∀ c : QC, c.WF → ∃ c' ∈ condCands ar (c.toCondP U RelN ar),
      c'.WF ∧ c'.toCondP U RelN ar = c.toCondP U RelN ar
  | .some e, w => by
    obtain ⟨c0, h0, w0, h1, h2⟩ := cands_complete ar e.close (Converse.wf_projs _ w)
    refine ⟨.some c0, ?_, w0, ?_⟩
    · simp only [QC.toCondP, nonEmpty, condCands, List.mem_map]
      exact ⟨c0, h0, rfl⟩
    · have hc : c0.close = c0 := by
        rw [QE.close, h1, Converse.hdr_close]; rfl
      simp only [QC.toCondP, hc]
      exact congrArg nonEmpty h2
  | .not c, w => by
    obtain ⟨c', h, w', e⟩ := condCands_complete ar c w
    exact ⟨.not c', by simp only [QC.toCondP, condCands, List.mem_map]; exact ⟨c', h, rfl⟩, w',
      by simp only [QC.toCondP, e]⟩
  | .and c d, w => by
    obtain ⟨c', h, w', e⟩ := condCands_complete ar c w.1
    obtain ⟨d', h', w'', e'⟩ := condCands_complete ar d w.2
    exact ⟨.and c' d', by
      simp only [QC.toCondP, condCands, List.mem_flatMap, List.mem_map]; exact ⟨c', h, d', h', rfl⟩,
      ⟨w', w''⟩, by simp only [QC.toCondP, e, e']⟩
  | .or c d, w => by
    obtain ⟨c', h, w', e⟩ := condCands_complete ar c w.1
    obtain ⟨d', h', w'', e'⟩ := condCands_complete ar d w.2
    exact ⟨.or c' d', by
      simp only [QC.toCondP, condCands, List.mem_flatMap, List.mem_map]; exact ⟨c', h, d', h', rfl⟩,
      ⟨w', w''⟩, by simp only [QC.toCondP, e, e']⟩

/-- **Completeness of the read-back.** For every well-formed query `Q`, some candidate read
back from `Q.stmt` is well formed and has the same statement. -/
theorem queryCands_complete (Q : Query) (w : Q.WF) :
    ∃ Q' ∈ queryCands Q.stmt, Q'.WF ∧ Q'.stmt = Q.stmt := by
  obtain ⟨a, ha, hm, hl⟩ := ar_choice Q.ar
  have hc : Q.cond.toCondP U RelN Q.ar = Q.cond.toCondP U RelN a :=
    toCondP_ar (fun j => (hl j).symm) U RelN Q.cond
  obtain ⟨c', hc', w', e'⟩ := condCands_complete a Q.cond w
  refine ⟨⟨a, c'⟩, ?_, w', ?_⟩
  · simp only [Query.stmt, Query.formP, queryCands, decMembers_membersP, List.mem_flatMap,
      List.mem_map]
    exact ⟨a, ha, c', by rw [hc]; exact hc', rfl⟩
  · simp only [Query.stmt, Query.formP, hm, e', hc]

end Recognise

/-! ## The recogniser decides the fragment -/

/-- **The recogniser is correct.** `isBoolSelection r` is `true` exactly when `r` is a
BoolSelection statement. -/
theorem isBoolSelection_iff (r : Expr) : isBoolSelection r = true ↔ BoolSelection r := by
  unfold isBoolSelection
  constructor
  · intro h
    obtain ⟨Q, -, hQ⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hQ
    exact ⟨Q, hQ.1, hQ.2⟩
  · rintro ⟨Q, w, rfl⟩
    obtain ⟨Q', hQ', w', e⟩ := Recognise.queryCands_complete Q w
    exact List.any_eq_true.mpr ⟨Q', hQ', by simp [w', e]⟩

/-- Membership in selection on Boolean function spaces is decidable. -/
instance : DecidablePred BoolSelection := fun r => decidable_of_iff _ (isBoolSelection_iff r)

/-! ## Examples

A test, not a proof. -/

namespace Examples

open Rasso.ESO.Examples

#guard isBoolSelection edgeIntoMember.stmt
#guard isBoolSelection satSentence.toQuery.stmt
#guard isBoolSelection twoColour.toQuery.stmt
#guard decide (BoolSelection twoColour.toQuery.stmt)
-- Not in the fragment: a name, and an `omega_msol` with no condition.
#guard !isBoolSelection (.name "eso")
#guard !isBoolSelection (.omegaMsol (membersP (.name univName) [("R", 1)]) none)
-- Renaming `univ` takes a statement out of the fragment.
#guard !isBoolSelection (edgeIntoMember.formP (.name "universe") RelN)

end Examples

end Rasso.ESO
