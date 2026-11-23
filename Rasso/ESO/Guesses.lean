import Rasso.ESO.Blocks
import Rasso.Bridge.Sol

/-!
# ESO: the members of the multi solution set are the guesses

Each member of `esoForm` is `ω_sol(U^k, holds: bool)`: a candidate gives every `k`-tuple of
the universe `true` or `false`, which is a guess for a second-order variable of arity `k`.
This file says that the candidates of the multi solution set are exactly the fitting
guesses, and that the condition sees each member's candidate under the member's name.

How the proof goes, in plain words:

* Each member `ω_sol(U^k, holds: bool)` evaluates to `solOf A k`, whose candidates are
  the graphs of functions from the tuples of `U^k` to `holds` values (`member_spec`,
  from `Rasso.FSpace` and `Rasso.Bridge.Sol`).
* A candidate database gives a guess (`guessOf`): for each listed variable, the rows
  its relation holds with `holds = true`. That guess fits, and the database's
  environment represents it (`rep_rowsTrue`, `guessOf_fits`).
* A fitting guess gives a database (`dbOf`): each member gets the graph of the
  indicator function of its guess (`guessCand`, `rep_guessCand`).
* The members are named apart (`memberName_inj`, `nodup_memsOf`), so each name in the
  environment finds its own member's relation.

It uses `eval_univPow`, `DD_mem` and `nodup_cols` from `Rasso.ESO.Blocks`.
-/

set_option linter.unusedSimpArgs false

namespace Rasso.ESO

open Rasso

/-- The heading of a guess relation of arity `k`: the columns, and `holds`. -/
def gH (A : Str) (k : Nat) : Heading := colsH A k ++ [(holdsAttr, .kind .bool)]

/-- The environment `E` gives each listed second-order variable `j` a relation that is
the guess `G j`: a tuple has `holds = true` exactly when its row is in `G j`. -/
def GuessEnv (A : Str) (ar : List (String × Nat)) (G : Guess) (E : Env) : Prop :=
  ∀ j k, ar.lookup j = some k → ∃ r, E.lookup (memberName j) = some (.finrel r) ∧
    Rep (gH A k) (fun t => t.get? holdsAttr = some (.bool true) ↔ rowOf (cols k) t ∈ G j) r

/-! ## Names -/

theorem memberName_ne_cond (j : String) : memberName j ≠ inConditionName := by
  intro h
  have := congrArg String.toList h
  simp [memberName, inConditionName, String.toList_append] at this

theorem memberName_ne_leaf (j : String) : memberName j ≠ leafName := by
  intro h
  have := congrArg String.toList h
  simp [memberName, leafName, String.toList_append] at this

theorem memberName_inj {j j' : String} (h : memberName j = memberName j') : j = j' := by
  have := congrArg String.toList h
  simp only [memberName, String.toList_append, List.append_cancel_left_eq] at this
  exact String.toList_inj.mp this

theorem memberName_ne_I (j : String) : (memberName j == "I") = false := by
  cases h : memberName j == "I"
  · rfl
  · have := congrArg String.toList (beq_iff_eq.mp h)
    simp [memberName, String.toList_append] at this

theorem holds_not_mem_cols (k : Nat) : holdsAttr ∉ cols k := by
  intro h
  obtain ⟨m, -, e⟩ := List.mem_map.mp h
  have := congrArg String.toList e
  simp only [colAttr, holdsAttr, String.toList_append] at this
  rw [show toString "c" = "c" from rfl] at this
  simp at this

/-! ## The members: one per second-order variable -/

theorem any_fst_iff {j : String} {acc : List (String × Nat)} :
    acc.any (·.1 == j) = true ↔ j ∈ acc.map (·.1) := by
  simp only [List.any_eq_true, beq_iff_eq, List.mem_map]

theorem foldl_members : ∀ (l acc : List (String × Nat)), (acc.map (·.1)).Nodup →
    ((l.foldl (fun acc (j, k) => if acc.any (·.1 == j) then acc else acc ++ [(j, k)]) acc).map
        (·.1)).Nodup ∧
      ∀ j k, (j, k) ∈ l.foldl (fun acc (j, k) => if acc.any (·.1 == j) then acc else acc ++ [(j, k)]) acc ↔
        (j, k) ∈ acc ∨ (j ∉ acc.map (·.1) ∧ l.lookup j = some k)
  | [], acc, hn => ⟨hn, fun j k => by simp [List.lookup]⟩
  | (j₀, k₀) :: l, acc, hn => by
    simp only [List.foldl_cons]
    by_cases hj : acc.any (·.1 == j₀) = true
    · simp only [hj, ite_true]
      obtain ⟨h1, h2⟩ := foldl_members l acc hn
      refine ⟨h1, fun j k => ?_⟩
      rw [h2]
      have hj' := any_fst_iff.mp hj
      by_cases e : j = j₀
      · subst e; simp [hj']
      · have : (j == j₀) = false := by simpa using e
        simp [List.lookup, this]
    · simp only [hj, Bool.false_eq_true, ite_false]
      have hj' : j₀ ∉ acc.map (·.1) := fun h => hj (any_fst_iff.mpr h)
      have hn' : ((acc ++ [(j₀, k₀)]).map (·.1)).Nodup := by
        rw [List.map_append, List.nodup_append]
        exact ⟨hn, by simp, fun a ha b hb e => by
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
          subst hb; subst e; exact hj' ha⟩
      obtain ⟨h1, h2⟩ := foldl_members l _ hn'
      refine ⟨h1, fun j k => ?_⟩
      rw [h2]
      by_cases e : j = j₀
      · subst e
        have hnot : ∀ k', (j, k') ∉ acc := fun k' hm => hj' (List.mem_map_of_mem (f := (·.1)) hm)
        simp [List.lookup, hnot, hj', eq_comm]
      · have : (j == j₀) = false := by simpa using e
        simp [List.lookup, this, e]

theorem mem_members {ar : List (String × Nat)} {j : String} {k : Nat} :
    (j, k) ∈ members ar ↔ ar.lookup j = some k := by
  unfold members
  rw [(foldl_members ar [] List.nodup_nil).2]
  simp

theorem nodup_members (ar : List (String × Nat)) : ((members ar).map (·.1)).Nodup :=
  (foldl_members ar [] List.nodup_nil).1

/-- The (name, arity) pairs `membersP` makes members of. -/
def memsOf (ar : List (String × Nat)) : List (String × Nat) :=
  match members ar with
  | [] => [("", 0)]
  | ms => ms

theorem membersP_eq (U : Expr) (ar : List (String × Nat)) :
    membersP U ar = (memsOf ar).map fun (j, k) => boolMemberP U j k := by
  unfold membersP memsOf
  cases members ar <;> rfl

theorem memsOf_ne_nil (ar : List (String × Nat)) : memsOf ar ≠ [] := by
  unfold memsOf; cases members ar <;> simp

theorem nodup_memsOf (ar : List (String × Nat)) : ((memsOf ar).map (·.1)).Nodup := by
  have := nodup_members ar
  unfold memsOf
  cases h : members ar with
  | nil => simp
  | cons a l => rw [h] at this; exact this

theorem mem_memsOf {ar : List (String × Nat)} {j : String} {k : Nat}
    (h : ar.lookup j = some k) : (j, k) ∈ memsOf ar := by
  have hm := mem_members.mpr h
  unfold memsOf
  cases e : members ar with
  | nil => rw [e] at hm; cases hm
  | cons a l => rw [e] at hm; exact hm

/-! ## Guess tuples: the columns and `holds` -/

/-- The heading of a member's candidates: the data's heading, then `holds`. -/
def hdOf (r : Finrel) : Heading := r.heading ++ [(holdsAttr, .kind .bool)]

/-- The decision tuple `holds = b`. -/
def hb (b : Bool) : Tuple := [(holdsAttr, .bool b)]

theorem colsH_attrs_g (A : Str) (k : Nat) : (colsH A k).attrs = cols k := by
  simp [colsH, Heading.attrs, List.map_map, Function.comp_def]

theorem gH_attrs_g (A : Str) (k : Nat) : (gH A k).attrs = cols k ++ [holdsAttr] := by
  simp [gH, Heading.attrs, colsH_attrs_g, ← colsH_attrs_g A k]

theorem lookup_map_const_mem {D : Domain} {c : String} :
    ∀ {l : List String}, c ∈ l → (l.map fun c => (c, D)).lookup c = some D
  | [], h => by cases h
  | x :: l, h => by
    by_cases e : c = x
    · subst e; simp [List.lookup]
    · have : (c == x) = false := by simpa using e
      simp only [List.map_cons, List.lookup, this]
      exact lookup_map_const_mem (List.mem_of_ne_of_mem e h)

theorem lookup_none_of_not_mem {β : Type} {a : String} {l : List (String × β)}
    (h : a ∉ l.map (·.1)) : l.lookup a = none := by
  cases e : l.lookup a with
  | none => rfl
  | some d => exact absurd (List.mem_map_of_mem (f := (·.1)) (lookup_mem e)) h

theorem holds_not_mem_colsH (A : Str) (k : Nat) : holdsAttr ∉ (colsH A k).attrs := by
  rw [colsH_attrs_g]; exact holds_not_mem_cols k

theorem lookup_gH_or (A : Str) (k : Nat) (a : String) :
    (gH A k).lookup a = ((colsH A k).lookup a).or (List.lookup a [(holdsAttr, Domain.kind .bool)]) := by
  simp only [gH, List.lookup_append]

theorem lookup_gH_holds (A : Str) (k : Nat) : (gH A k).lookup holdsAttr = some (.kind .bool) := by
  rw [lookup_gH_or, lookup_none_of_not_mem (holds_not_mem_colsH A k)]
  simp [hb, List.lookup]

theorem lookup_gH_ne {A : Str} {k : Nat} {a : String} (h : a ≠ holdsAttr) :
    (gH A k).lookup a = (colsH A k).lookup a := by
  rw [lookup_gH_or]
  have : (a == holdsAttr) = false := by simpa using h
  simp [hb, List.lookup, this]

theorem sorted_hb (b : Bool) : Tuple.Sorted (hb b) := List.pairwise_singleton _ _

theorem get?_hb (b : Bool) (a : String) :
    Tuple.get? (hb b) a = if a = holdsAttr then some (.bool b) else none := by
  by_cases e : a = holdsAttr
  · subst e; simp [hb, Tuple.get?, List.lookup]
  · have : (a == holdsAttr) = false := by simpa using e
    simp [hb, Tuple.get?, List.lookup, this, e]

theorem sorted_merge {t u : Tuple} (ht : Tuple.Sorted t) (hu : Tuple.Sorted u) :
    Tuple.Sorted (t.merge u) :=
  ofPairs_sorted (mergeList_nodup (Tuple.nodup_keys ht) (Tuple.nodup_keys hu))

theorem get?_merge_hb {A : Str} {k : Nat} {t : Tuple} (ht : t.Fits (colsH A k)) (b : Bool)
    (a : String) : Tuple.get? (t.merge (hb b)) a =
      if a = holdsAttr then some (.bool b) else Tuple.get? t a := by
  rw [Tuple.get?_merge ht.sorted (sorted_hb b), get?_hb]
  by_cases e : a = holdsAttr
  · subst e; rw [ht.get?_none (holds_not_mem_colsH A k)]; simp
  · simp [e]

theorem restrict_merge_hb {A : Str} {k : Nat} {t : Tuple} (ht : t.Fits (colsH A k)) (b : Bool) :
    (t.merge (hb b)).restrict (cols k) = t := by
  refine Tuple.ext_get? (sorted_restrict (sorted_merge ht.sorted (sorted_hb b))) ht.sorted
    fun a => ?_
  rw [get?_restrict, get?_merge_hb ht]
  by_cases hc : a ∈ cols k
  · have : a ≠ holdsAttr := fun e => holds_not_mem_cols k (e ▸ hc)
    simp [hc, this]
  · rw [ht.get?_none (by rw [colsH_attrs_g]; exact hc)]; simp [hc]

theorem fits_merge_hb {A : Str} {k : Nat} {t : Tuple} (ht : t.Fits (colsH A k)) (b : Bool) :
    (t.merge (hb b)).Fits (gH A k) where
  sorted := sorted_merge ht.sorted (sorted_hb b)
  attrs a := by
    rw [Tuple.attrs, ← Finrel.lookup_isSome, gH_attrs_g, List.mem_append, List.mem_singleton]
    have := get?_merge_hb ht b a
    simp only [Tuple.get?] at this
    rw [this]
    by_cases e : a = holdsAttr
    · simp [e]
    · have h1 := ht.get?_isSome a
      rw [colsH_attrs_g] at h1
      simp only [Tuple.get?] at h1
      simp [e, h1]
  dom p hp d hd := by
    have hn := Tuple.nodup_keys (sorted_merge ht.sorted (sorted_hb b))
    have hg : Tuple.get? (t.merge (hb b)) p.1 = some p.2 := mem_lookup hn hp
    rw [get?_merge_hb ht] at hg
    by_cases e : p.1 = holdsAttr
    · simp only [e, ite_true, Option.some.injEq] at hg
      rw [e, lookup_gH_holds, Option.some.injEq] at hd
      rw [← hd, ← hg]; rfl
    · simp only [e, ite_false] at hg
      rw [lookup_gH_ne e] at hd
      exact ht.dom (p.1, p.2) (lookup_mem hg) d hd

theorem fits_holds {A : Str} {k : Nat} {x : Tuple} (hx : x.Fits (gH A k)) :
    ∃ b, Tuple.get? x holdsAttr = some (.bool b) := by
  have hs := (hx.get?_isSome holdsAttr).mpr (by rw [gH_attrs_g]; simp)
  cases hv : Tuple.get? x holdsAttr with
  | none => rw [hv] at hs; cases hs
  | some v =>
    have := hx.dom (holdsAttr, v) (lookup_mem hv) _ (lookup_gH_holds A k)
    cases v <;> first | exact ⟨_, rfl⟩ | cases this

theorem fits_restrict {A : Str} {k : Nat} {x : Tuple} (hx : x.Fits (gH A k)) :
    (x.restrict (cols k)).Fits (colsH A k) := by
  have := hx.restrict (H := colsH A k) fun a d h => by
    rw [lookup_gH_or, h]; rfl
  rwa [colsH_attrs_g] at this

theorem eq_merge_restrict {A : Str} {k : Nat} {x : Tuple} (hx : x.Fits (gH A k)) {b : Bool}
    (hb' : Tuple.get? x holdsAttr = some (.bool b)) : x = (x.restrict (cols k)).merge (hb b) := by
  have hr := fits_restrict hx
  refine Tuple.ext_get? hx.sorted (sorted_merge hr.sorted (sorted_hb b)) fun a => ?_
  rw [get?_merge_hb hr, get?_restrict]
  by_cases e : a = holdsAttr
  · simp [e, ← hb']
  · by_cases hc : a ∈ cols k
    · simp [e, hc]
    · rw [hx.get?_none (by rw [gH_attrs_g]; simp [hc, e])]; simp [e, hc]

theorem rowOf_restrict_cols {k : Nat} (x : Tuple) :
    rowOf (cols k) (x.restrict (cols k)) = rowOf (cols k) x :=
  List.map_congr_left fun c hc => by rw [get?_restrict]; simp [hc]

/-! ## A member's candidates as guess relations -/

/-- A candidate built from `b`: each data tuple `t` merged with `holds = b t`. -/
theorem mem_graph_hb {A : Str} {k : Nat} {r : Finrel} (hr : Rep (colsH A k) (fun _ => True) r)
    (b : Tuple → Bool) (x : Tuple) :
    x ∈ (graph (hdOf r) r.tuples fun t => hb (b t)).tuples ↔
      x.Fits (gH A k) ∧ Tuple.get? x holdsAttr = some (.bool (b (x.restrict (cols k)))) := by
  rw [mem_graph]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ft := hr.mem_fits ht
    refine ⟨fits_merge_hb ft (b t), ?_⟩
    rw [restrict_merge_hb ft, get?_merge_hb ft]; simp
  · rintro ⟨hx, hh⟩
    exact ⟨_, (hr.mem _).mpr ⟨fits_restrict hx, trivial⟩, eq_merge_restrict hx hh⟩

theorem lookup_hdOf {A : Str} {k : Nat} {r : Finrel} (hr : Rep (colsH A k) (fun _ => True) r)
    (a : String) : (hdOf r).lookup a = (gH A k).lookup a := by
  simp only [hdOf, gH, List.lookup_append, hr.head a]

theorem rep_graph_hb {A : Str} {k : Nat} {r : Finrel} (hr : Rep (colsH A k) (fun _ => True) r)
    (b : Tuple → Bool) {P : Tuple → Prop}
    (hP : ∀ x, x.Fits (gH A k) →
      (Tuple.get? x holdsAttr = some (.bool (b (x.restrict (cols k)))) ↔ P x)) :
    Rep (gH A k) P (graph (hdOf r) r.tuples fun t => hb (b t)) where
  wf := {
    nodup := by
      show (hdOf r).attrs.Nodup
      simp only [hdOf, Heading.attrs, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨hr.wf.nodup, by simp, fun a ha c hc e => ?_⟩
      simp only [List.mem_singleton] at hc
      subst hc
      exact holds_not_mem_colsH A k ((attrs_congr hr.head _).mp (e ▸ ha))
    fits := fun t ht => by
      have := ((mem_graph_hb hr b t).mp ht).1
      exact this.congr fun a => (lookup_hdOf hr a).symm }
  head a := lookup_hdOf hr a
  mem x := by
    rw [mem_graph_hb hr]
    exact ⟨fun ⟨f, h⟩ => ⟨f, (hP x f).mp h⟩, fun ⟨f, h⟩ => ⟨f, (hP x f).mpr h⟩⟩

/-! ## A member's solution set -/

/-- The form of the member for arity `k`. -/
def memberForm (A : Str) (k : Nat) : Expr :=
  .omegaSol (univPowP (univLit A) id (cols k)) (.omega [(holdsAttr, .kind .bool)])

/-- The relation of `holds` values. -/
def holdsU : Unrel := Unrel.omega [(holdsAttr, .kind .bool)]

/-- The solution set the member for arity `k` evaluates to. -/
def solOf (A : Str) (k : Nat) : Sol :=
  match Expr.eval [] [] (memberForm A k) with
  | .ok (.sol s) => s
  | _ => default

theorem eval_holdsU : Expr.eval [] [] (.omega [(holdsAttr, .kind .bool)]) = .ok (.unrel holdsU) := by
  rw [Expr.eval]
  simp [evalHeading, DomExpr.eval, bind, Except.bind, pure, Except.pure, holdsU]

theorem holds_tt (t : Tuple) : Term.holds t Unrel.tt = .ok true := by
  simp [Term.holds, Unrel.tt, Term.eval, asBool, bind, Except.bind]

theorem holdsU_tuples : ∃ picks, holdsU.tuples = .ok picks ∧ ∀ p, p ∈ picks ↔ ∃ b, p = hb b := by
  obtain ⟨picks, hp⟩ := Unrel.tuples_ok (u := holdsU)
    (by simp [holdsU, Unrel.omega, Domain.values?]) (fun ps _ => ⟨true, holds_tt _⟩)
  refine ⟨picks, hp, fun p => ?_⟩
  rw [Unrel.mem_tuples hp]
  simp only [holdsU, Unrel.omega, holds_tt, and_true]
  constructor
  · rintro ⟨ps, hps, rfl⟩
    cases hps with
    | cons hd hv hrest =>
      cases hrest
      simp only [Domain.values?, Option.some.injEq] at hd
      subst hd
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨false, by simp [Tuple.ofPairs, hb]⟩
      · exact ⟨true, by simp [Tuple.ofPairs, hb]⟩
  · rintro ⟨b, rfl⟩
    refine ⟨[(holdsAttr, .bool b)], .cons (vs := [.bool false, .bool true]) rfl (by cases b <;> simp) .nil, ?_⟩
    simp [Tuple.ofPairs, hb]

/-- **A member's solution set.** Its data is `U^k` (a relation representing every tuple
over the columns), its heading adds `holds`, and its candidates are the graphs of the
functions from `U^k` to `holds` values. -/
theorem member_spec (A : Str) (k : Nat) :
    ∃ r picks, Rep (colsH A k) (fun _ => True) r ∧ (∀ p, p ∈ picks ↔ ∃ b, p = hb b) ∧
      solOf A k = ⟨r, hdOf r, omegaSolCandidates (hdOf r) r.tuples picks⟩ ∧
      Expr.eval [] [] (memberForm A k) = .ok (.sol (solOf A k)) := by
  have hn : ((cols k).map id).Nodup := by simpa using nodup_cols k
  obtain ⟨r, hre, hr⟩ := eval_univPow A [] hn
  have hr' : Rep (colsH A k) (fun _ => True) r := hr
  obtain ⟨picks, hp, hpm⟩ := holdsU_tuples
  have hdx : ∀ a ∈ holdsU.heading.attrs, a ∉ r.attrs := by
    intro a ha har
    simp [holdsU, Unrel.omega, Heading.attrs] at ha
    subst ha
    exact holds_not_mem_colsH A k ((attrs_congr hr'.head _).mp har)
  obtain ⟨v, hv⟩ := eval_omegaSol_ok (env := []) (tg := []) rfl hre eval_holdsU rfl hdx hp
  obtain ⟨data, u, picks', hd, ⟨w, hw, hu⟩, -, hp', hval⟩ := eval_omegaSol rfl hv
  rw [hre] at hd; cases hd
  rw [eval_holdsU] at hw; cases hw
  cases hu
  rw [hp] at hp'; cases hp'
  have he : Expr.eval [] [] (memberForm A k) = .ok (.sol ⟨r, hdOf r, omegaSolCandidates (hdOf r) r.tuples picks⟩) := by
    rw [memberForm, hv, hval]; rfl
  have hs : solOf A k = ⟨r, hdOf r, omegaSolCandidates (hdOf r) r.tuples picks⟩ := by
    unfold solOf; rw [he]
  exact ⟨r, picks, hr', hpm, hs, hs ▸ he⟩

/-- The members evaluate to `solOf` of their arities. -/
theorem membersEval_eq (A : Str) : ∀ (l : List (String × Nat)) {sols : List (String × Sol)},
    MembersEval [] [] (l.map fun (j, k) => boolMemberP (univLit A) j k) sols →
      sols = l.map fun (j, k) => (memberName j, solOf A k)
  | [], sols, h => by cases h; rfl
  | (j, k) :: l, sols, h => by
    simp only [List.map_cons] at h
    cases h with
    | cons _ he hrest =>
      obtain ⟨-, -, -, -, -, hk⟩ := member_spec A k
      have : Expr.eval [] [] (memberForm A k) = _ := he
      rw [hk] at this
      cases this
      rw [membersEval_eq A l hrest]; rfl

theorem nodup_memberNames {β : Type} (F : String → Nat → β) {l : List (String × Nat)}
    (hn : (l.map (·.1)).Nodup) : ((l.map fun (j, k) => (memberName j, F j k)).map (·.1)).Nodup := by
  have e : ((l.map fun (j, k) => (memberName j, F j k)).map (·.1)) = (l.map (·.1)).map memberName := by
    simp only [List.map_map]; rfl
  rw [e]
  exact nodup_map_of_inj hn fun _ _ _ _ h => memberName_inj h

theorem lookup_env_member (db : Db) (j : String) :
    (inCondition (bindDb db [])).lookup (memberName j) = (db.lookup (memberName j)).map Val.finrel := by
  have hne : (memberName j == inConditionName) = false := by simpa using memberName_ne_cond j
  simp only [inCondition, List.lookup, hne, bindDb, List.append_nil]
  have hl : (memberName j == leafName) = false := by simpa using memberName_ne_leaf j
  induction db with
  | nil => simp [List.lookup, hl]
  | cons p db ih =>
    obtain ⟨n, r⟩ := p
    by_cases e : memberName j = n
    · subst e; simp [List.lookup]
    · have : (memberName j == n) = false := by simpa using e
      simp only [List.map_cons, List.cons_append, List.lookup, this]; exact ih

/-! ## A candidate database gives a guess -/

/-- The rows of a candidate with `holds = true`. -/
def rowsTrue (k : Nat) (R : Finrel) : List (List Value) :=
  (R.tuples.filter fun x => Tuple.get? x holdsAttr == some (.bool true)).map (rowOf (cols k))

/-- The guess a database gives: for each listed variable, the rows its relation holds
with `holds = true`. -/
def guessOf (ar : List (String × Nat)) (db : Db) : Guess := fun j =>
  match ar.lookup j with
  | some k => match db.lookup (memberName j) with
    | some R => rowsTrue k R
    | none => []
  | none => []

/-- Every candidate of a member is the graph of some `holds` function. -/
theorem cand_graph {A : Str} {k : Nat} {R : Finrel} (hR : R ∈ (solOf A k).candidates) :
    ∃ r, Rep (colsH A k) (fun _ => True) r ∧ ∃ b : Tuple → Bool,
      R = graph (hdOf r) r.tuples fun t => hb (b t) := by
  obtain ⟨r, picks, hr, hpm, hs, -⟩ := member_spec A k
  rw [hs] at hR
  obtain ⟨f, hf, rfl⟩ := (mem_omegaSolCandidates (Finrel.nodup_tuples r) R).mp hR
  refine ⟨r, hr, fun t => decide (f t = hb true), ?_⟩
  unfold graph
  congr 1
  refine List.map_congr_left fun t ht => ?_
  obtain ⟨b, hb'⟩ := (hpm _).mp (hf t ht)
  simp only [hb']
  cases b <;> simp [hb]

theorem rowOf_eq_restrict {A : Str} {k : Nat} {x y : Tuple} (hx : x.Fits (gH A k))
    (hy : y.Fits (gH A k)) (h : rowOf (cols k) x = rowOf (cols k) y) :
    x.restrict (cols k) = y.restrict (cols k) := by
  have fx := fits_restrict hx
  have fy := fits_restrict hy
  refine Tuple.ext_get? fx.sorted fy.sorted fun a => ?_
  rw [get?_restrict, get?_restrict]
  by_cases hc : a ∈ cols k
  · simp only [hc, ite_true]
    have := (List.map_inj_left.mp h) a hc
    have sx := (hx.get?_isSome a).mpr (by rw [gH_attrs_g]; simp [hc])
    have sy := (hy.get?_isSome a).mpr (by rw [gH_attrs_g]; simp [hc])
    cases ex : Tuple.get? x a with
    | none => rw [ex] at sx; cases sx
    | some v =>
      cases ey : Tuple.get? y a with
      | none => rw [ey] at sy; cases sy
      | some w => rw [ex, ey] at this; simp at this; rw [this]
  · simp [hc]

/-- **A candidate represents its guess.** -/
theorem rep_rowsTrue {A : Str} {k : Nat} {R : Finrel} (hR : R ∈ (solOf A k).candidates) :
    Rep (gH A k) (fun x => Tuple.get? x holdsAttr = some (.bool true) ↔
      rowOf (cols k) x ∈ rowsTrue k R) R := by
  obtain ⟨r, hr, b, rfl⟩ := cand_graph hR
  refine rep_graph_hb hr b fun x hx => ?_
  have key : rowOf (cols k) x ∈ rowsTrue k (graph (hdOf r) r.tuples fun t => hb (b t)) ↔
      b (x.restrict (cols k)) = true := by
    unfold rowsTrue
    rw [List.mem_map]
    constructor
    · rintro ⟨y, hy, hrow⟩
      obtain ⟨hy, ht⟩ := List.mem_filter.mp hy
      obtain ⟨fy, hgy⟩ := (mem_graph_hb hr b y).mp hy
      have ht' : Tuple.get? y holdsAttr = some (.bool true) := by simpa using ht
      rw [ht', Option.some.injEq, Value.bool.injEq] at hgy
      rw [← rowOf_eq_restrict fy hx hrow]; exact hgy.symm
    · intro hbx
      have fr := fits_restrict hx
      refine ⟨(x.restrict (cols k)).merge (hb true), List.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · refine (mem_graph_hb hr b _).mpr ⟨fits_merge_hb fr true, ?_⟩
        rw [restrict_merge_hb fr, get?_merge_hb fr, hbx]; simp
      · rw [get?_merge_hb fr]; simp
      · rw [← rowOf_restrict_cols, restrict_merge_hb fr, rowOf_restrict_cols]
  rw [key]
  obtain ⟨b', hb'⟩ := fits_holds hx
  rw [hb']
  cases b' <;> cases b (x.restrict (cols k)) <;> simp

/-- The guess of a candidate database fits the arities. -/
theorem guessOf_fits {A : Str} {ar : List (String × Nat)} {db : Db}
    (hdb : ∀ j k R, ar.lookup j = some k → db.lookup (memberName j) = some R → R ∈ (solOf A k).candidates) :
    (guessOf ar db).Fits A ar := by
  intro j t ht
  unfold guessOf at ht
  cases hj : ar.lookup j with
  | none => rw [hj] at ht; cases ht
  | some k =>
    rw [hj] at ht
    cases hR : db.lookup (memberName j) with
    | none => rw [hR] at ht; cases ht
    | some R =>
      rw [hR] at ht
      refine ⟨k, rfl, ?_⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
      have fy := (rep_rowsTrue (hdb j k R hj hR)).mem_fits (List.mem_filter.mp hy).1
      refine ⟨by simp [rowOf, cols], fun v hv => ?_⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
      have sc := (fy.get?_isSome c).mpr (by rw [gH_attrs_g]; simp [hc])
      cases ec : Tuple.get? y c with
      | none => rw [ec] at sc; cases sc
      | some w =>
        simp only [Option.getD_some]
        have hc' : c ≠ holdsAttr := fun e => holds_not_mem_cols k (e ▸ hc)
        have hd := fy.dom (c, w) (lookup_mem ec) (DD A)
          (by rw [lookup_gH_ne hc', colsH]; exact lookup_map_const_mem hc)
        exact (DD_mem A w).mp hd

/-! ## A fitting guess gives a candidate database -/

/-- The candidate of the member for `j` (arity `k`) that holds the guess `G j`. -/
def guessCand (A : Str) (G : Guess) (j : String) (k : Nat) : Finrel :=
  graph (hdOf (solOf A k).data) (solOf A k).data.tuples
    fun t => hb (decide (rowOf (cols k) t ∈ G j))

/-- The database that gives each member its guess. -/
def dbOf (A : Str) (ar : List (String × Nat)) (G : Guess) : Db :=
  (memsOf ar).map fun (j, k) => (memberName j, guessCand A G j k)

theorem guessCand_mem (A : Str) (G : Guess) (j : String) (k : Nat) :
    guessCand A G j k ∈ (solOf A k).candidates := by
  obtain ⟨r, picks, -, hpm, hs, -⟩ := member_spec A k
  unfold guessCand
  rw [hs]
  exact (mem_omegaSolCandidates (Finrel.nodup_tuples r) _).mpr
    ⟨_, fun t _ => (hpm _).mpr ⟨_, rfl⟩, rfl⟩

theorem rep_guessCand (A : Str) (G : Guess) (j : String) (k : Nat) :
    Rep (gH A k) (fun x => Tuple.get? x holdsAttr = some (.bool true) ↔
      rowOf (cols k) x ∈ G j) (guessCand A G j k) := by
  obtain ⟨r, picks, hr, -, hs, -⟩ := member_spec A k
  unfold guessCand
  rw [hs]
  refine rep_graph_hb hr _ fun x hx => ?_
  rw [rowOf_restrict_cols]
  obtain ⟨b', hb'⟩ := fits_holds hx
  rw [hb']
  cases b' <;> by_cases h : rowOf (cols k) x ∈ G j <;> simp [h]

theorem candOf_dbOf (A : Str) (G : Guess) : ∀ (l : List (String × Nat)),
    CandOf (l.map fun (j, k) => (memberName j, solOf A k))
      (l.map fun (j, k) => (memberName j, guessCand A G j k))
  | [] => .nil
  | (j, k) :: l => .cons (guessCand_mem A G j k) (candOf_dbOf A G l)

theorem guessEnv_dbOf (A : Str) (ar : List (String × Nat)) (G : Guess) :
    GuessEnv A ar G (inCondition (bindDb (dbOf A ar G) [])) := by
  intro j k hj
  refine ⟨guessCand A G j k, ?_, rep_guessCand A G j k⟩
  rw [lookup_env_member]
  have hm : (memberName j, guessCand A G j k) ∈ dbOf A ar G :=
    List.mem_map_of_mem (f := fun (j, k) => (memberName j, guessCand A G j k)) (mem_memsOf hj)
  have hn : ((dbOf A ar G).map (·.1)).Nodup := nodup_memberNames (guessCand A G) (nodup_memsOf ar)
  rw [mem_lookup hn hm]
  rfl

/-! ## The theorem -/

/-- The multi solution set of the guesses, with a condition whose value depends only
on the guess: it is not refused, and it has a candidate exactly when some fitting guess
passes the condition. -/
theorem eval_esoMsol (A : Str) (ar : List (String × Nat)) (c : Cond) (val : Guess → Bool)
    (hval : ∀ G E, G.Fits A ar → GuessEnv A ar G (inCondition E) →
      Cond.eval (inCondition E) [] c = .ok (val G)) :
    ∃ m, Expr.eval [] [] (.omegaMsol (membersP (univLit A) ar) (some c)) = .ok (.msol m) ∧
      ((∃ db, db ∈ m.candidates) ↔ ∃ G, G.Fits A ar ∧ val G = true) := by
  -- the members' solution sets, and the guess each candidate database gives
  let sols := (memsOf ar).map fun (j, k) => (memberName j, solOf A k)
  have hnames : (sols.map (·.1)).Nodup := nodup_memberNames (fun _ k => solOf A k) (nodup_memsOf ar)
  have hsols : ∀ sols', MembersEval [] [] (membersP (univLit A) ar) sols' → sols' = sols := by
    rw [membersP_eq]; exact fun sols' h => membersEval_eq A _ h
  have core : ∀ db, CandOf sols db →
      (guessOf ar db).Fits A ar ∧ GuessEnv A ar (guessOf ar db) (inCondition (bindDb db [])) := by
    intro db hdb
    have hlk : ∀ j k, ar.lookup j = some k →
        ∃ R ∈ (solOf A k).candidates, db.lookup (memberName j) = some R := fun j k hj =>
      hdb.lookup hnames (List.mem_map_of_mem (f := fun (j, k) => (memberName j, solOf A k))
        (mem_memsOf hj))
    refine ⟨guessOf_fits fun j k R hj hR => ?_, fun j k hj => ?_⟩
    · obtain ⟨R', hR', e⟩ := hlk j k hj
      rw [hR] at e; cases e; exact hR'
    · obtain ⟨R, hR, e⟩ := hlk j k hj
      refine ⟨R, by rw [lookup_env_member, e]; rfl, ?_⟩
      have hG : guessOf ar db j = rowsTrue k R := by simp only [guessOf, hj, e]
      rw [hG]; exact rep_rowsTrue hR
  -- the multi solution set is not refused
  have hms : ∀ ne ∈ membersP (univLit A) ar,
      (ne.1 == "I") = false ∧ ∃ s, Expr.eval [] [] ne.2 = .ok (.sol s) := by
    rw [membersP_eq]
    intro ne hne
    obtain ⟨⟨j, k⟩, -, rfl⟩ := List.mem_map.mp hne
    obtain ⟨-, -, -, -, -, he⟩ := member_spec A k
    exact ⟨memberName_ne_I j, _, he⟩
  have hne : membersP (univLit A) ar ≠ [] := by
    rw [membersP_eq]; simpa using memsOf_ne_nil ar
  have hc : ∀ sols', MembersEval [] [] (membersP (univLit A) ar) sols' → ∀ cond, some c = some cond →
      ∀ db, CandOf sols' db → ∃ b, msolTest [] [] cond db = .ok b := by
    intro sols' hme cond hcond db hdb
    cases hcond
    rw [hsols sols' hme] at hdb
    obtain ⟨hf, he⟩ := core db hdb
    exact ⟨_, hval _ _ hf he⟩
  have hnd : ((membersP (univLit A) ar).map (·.1)).Nodup := by
    rw [membersP_eq]
    exact nodup_memberNames (fun j k => (boolMemberP (univLit A) j k).2) (nodup_memsOf ar)
  obtain ⟨v, hv⟩ := eval_omegaMsol_ok rfl hne hnd hms hc
  obtain ⟨sols', m, hme, rfl, -, hmem⟩ := eval_omegaMsol_meaning rfl hv
  have := hsols sols' hme
  subst this
  refine ⟨m, hv, ⟨fun ⟨db, hdb⟩ => ?_, fun ⟨G, hG, hvG⟩ => ?_⟩⟩
  · obtain ⟨hcand, hconds⟩ := (hmem db).mp hdb
    obtain ⟨hf, he⟩ := core db hcand
    have h1 : msolTest [] [] c db = .ok true := hconds _ (by simp [msolConds])
    have h2 : msolTest [] [] c db = .ok (val (guessOf ar db)) := hval _ _ hf he
    rw [h1] at h2
    exact ⟨_, hf, (Except.ok.inj h2).symm⟩
  · refine ⟨dbOf A ar G, (hmem _).mpr ⟨candOf_dbOf A G _, fun p hp => ?_⟩⟩
    simp only [msolConds, List.mem_singleton] at hp
    subst hp
    show Cond.eval (inCondition (bindDb (dbOf A ar G) [])) [] c = .ok true
    rw [hval G _ hG (guessEnv_dbOf A ar G), hvG]

end Rasso.ESO
