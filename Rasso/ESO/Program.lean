import Rasso.ESO.Capture

/-!
# ESO: the program `toProgram`, with its data in named statements

`esoForm_expresses` is about `esoForm`, the multi solution set with the structure's
data written in place. The program a user runs is `toProgram ψ A`: statements `univ` and
`rel_i_n` hold the data, and the last statement, `eso`, names them. This file shows that
the two agree, so the forward theorem holds for the program (`toProgram_expresses`).

The argument is congruence: each form that the construction uses evaluates to a value
that depends only on the values of its parts. Where `eso` reads `univ` or `rel_i_n`, the
environment gives the same value as the literal does.
-/

namespace Rasso.ESO

open Rasso


/-! ## Congruence of evaluation

`EvEq E E' a b`: form `a` in environment `E` has the value of form `b` in `E'`. -/

section Congr

variable {E E' : Env}

abbrev EvEq (E E' : Env) (a b : Expr) : Prop := Expr.eval E [] a = Expr.eval E' [] b

theorem name_congr {n : String} (h : E.lookup n = E'.lookup n) : EvEq E E' (.name n) (.name n) := by
  unfold EvEq; rw [Expr.eval, Expr.eval]; simp only [List.any_nil, Bool.false_eq_true, ite_false]; rw [h]

theorem rename_congr {ren} {a b : Expr} (h : EvEq E E' a b) : EvEq E E' (.rename ren a) (.rename ren b) := by
  unfold EvEq at *; rw [Expr.eval, Expr.eval]; simp only [List.any_nil, Bool.false_eq_true, ite_false]; rw [h]

theorem select_congr {p} {a b : Expr} (h : EvEq E E' a b) : EvEq E E' (.select p a) (.select p b) := by
  unfold EvEq at *; rw [Expr.eval, Expr.eval]; simp only [List.any_nil, Bool.false_eq_true, ite_false]; rw [h]

theorem project_congr {as} {a b : Expr} (h : EvEq E E' a b) : EvEq E E' (.project as a) (.project as b) := by
  unfold EvEq at *; rw [Expr.eval, Expr.eval]; simp only [List.any_nil, Bool.false_eq_true, ite_false]; rw [h]

theorem gamma_congr {by_ ag res} {a b : Expr} (hag : ag.hasSub = false)
    (hc : (E.lookup inConditionName).isNone = (E'.lookup inConditionName).isNone)
    (h : EvEq E E' a b) : EvEq E E' (.gamma by_ ag res a) (.gamma by_ ag res b) := by
  unfold EvEq at *; rw [Expr.eval, Expr.eval]
  simp only [List.any_nil, Bool.false_eq_true, ite_false, hag]
  rw [h, hc]

theorem omegaSol_congr {d d' x x' : Expr} (h : EvEq E E' d d') (hx : EvEq E E' x x') :
    EvEq E E' (.omegaSol d x) (.omegaSol d' x') := by
  unfold EvEq at *; rw [Expr.eval, Expr.eval]; simp only [List.any_nil, Bool.false_eq_true, ite_false]
  rw [h, hx]

/-- Lists of forms whose members evaluate the same. -/
inductive EvEqs (E E' : Env) : List Expr → List Expr → Prop
  | nil : EvEqs E E' [] []
  | cons {a b as bs} : EvEq E E' a b → EvEqs E E' as bs → EvEqs E E' (a :: as) (b :: bs)

theorem mapM_congr : ∀ {as bs : List Expr}, EvEqs E E' as bs →
    as.mapM (·.eval E []) = bs.mapM (·.eval E' [])
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.mapM_cons]; rw [show Expr.eval E [] _ = _ from h, mapM_congr hs]

theorem nary_congr {op} {as bs : List Expr} (h : EvEqs E E' as bs) :
    EvEq E E' (.nary op as) (.nary op bs) := by
  unfold EvEq; rw [Expr.eval, Expr.eval]; simp only [List.any_nil, Bool.false_eq_true, ite_false]
  rw [mapM_congr h]

theorem evEqs_map {α : Type} {g g' : α → Expr} (h : ∀ a, EvEq E E' (g a) (g' a)) :
    ∀ l : List α, EvEqs E E' (l.map g) (l.map g')
  | [] => .nil
  | a :: l => .cons (h a) (evEqs_map h l)

/-- A domain that names no relation, so its value does not depend on the environment. -/
def domClosed : DomExpr → Bool
  | .in_ _ => false
  | _ => true

theorem evalHeading_indep : ∀ {hd : List (String × DomExpr)}, (∀ p ∈ hd, domClosed p.2 = true) →
    evalHeading E [] hd = evalHeading E' [] hd
  | [], _ => by rw [evalHeading, evalHeading]
  | (a, d) :: hd, h => by
    rw [evalHeading, evalHeading, evalHeading_indep (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    have hd' := h (a, d) (List.mem_cons_self ..)
    have : DomExpr.eval E [] d = DomExpr.eval E' [] d := by
      cases d with
      | in_ _ => simp [domClosed] at hd'
      | _ => rw [DomExpr.eval, DomExpr.eval]
    rw [this]

theorem omegaRows_indep {hd rows} (h : ∀ p ∈ hd, domClosed p.2 = true) :
    EvEq E E' (.omegaRows hd rows) (.omegaRows hd rows) := by
  unfold EvEq; rw [Expr.eval, Expr.eval]; simp only [List.any_nil, Bool.false_eq_true, ite_false]
  rw [evalHeading_indep h]

theorem omega_indep {hd} (h : ∀ p ∈ hd, domClosed p.2 = true) : EvEq E E' (.omega hd) (.omega hd) := by
  unfold EvEq; rw [Expr.eval, Expr.eval]; simp only [List.any_nil, Bool.false_eq_true, ite_false]
  rw [evalHeading_indep h]

theorem joinAll_congr {α : Type} {g g' : α → Expr} (h : ∀ a, EvEq E E' (g a) (g' a)) :
    ∀ l : List α, EvEq E E' (joinAll (l.map g)) (joinAll (l.map g'))
  | [] => omegaRows_indep (by simp)
  | [a] => h a
  | a :: b :: l => nary_congr (evEqs_map h (a :: b :: l))

theorem filterAuxM_congr {f g : Db → Except String Bool} :
    ∀ {l acc : List Db}, (∀ x ∈ l, f x = g x) → l.filterAuxM f acc = l.filterAuxM g acc
  | [], _, _ => rfl
  | y :: l, acc, h => by
    simp only [List.filterAuxM]
    rw [h y (List.mem_cons_self ..)]
    congr 1; funext b
    exact filterAuxM_congr fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem filterM_congr {f g : Db → Except String Bool} {l : List Db} (h : ∀ x ∈ l, f x = g x) :
    l.filterM f = l.filterM g := by
  simp only [List.filterM]; rw [filterAuxM_congr h]

end Congr

/-! ## The data is literal -/

section Lit

variable {E E' : Env}

theorem univLit_indep (A : Str) : EvEq E E' (univLit A) (univLit A) :=
  omegaRows_indep (by simp [univDom, domClosed])

theorem relLit_indep (A : Str) (i : String) (n : Nat) : EvEq E E' (relLit A i n) (relLit A i n) :=
  omegaRows_indep (by simp [univDom, domClosed])

theorem holdsDec_indep : EvEq E E' (.omega [(holdsAttr, .kind .bool)]) (.omega [(holdsAttr, .kind .bool)]) :=
  omega_indep (by simp [domClosed])

end Lit

/-! ## The construction, with names or with literals -/

section Named

variable (A : Str)

/-- The named data: `univ`, and `rel_i_n` for each symbol at each arity. -/
abbrev RelN : String → Nat → Expr := fun i n => .name (relName i n)

/-- Environments `E` (with the data named) and `E'` (with the data written in place)
that agree on the data, on the guesses and on whether a condition is being evaluated. -/
structure DataEnv (S : List (String × Nat)) (E E' : Env) : Prop where
  univ : EvEq E E' (.name univName) (univLit A)
  rel : ∀ p ∈ S, EvEq E E' (.name (relName p.1 p.2)) (relLit A p.1 p.2)
  guess : ∀ j, EvEq E E' (.name (memberName j)) (.name (memberName j))
  cond : (E.lookup inConditionName).isNone = (E'.lookup inConditionName).isNone

variable {A}

theorem univPowP_congr {E E' : Env} {U U' : Expr} (h : EvEq E E' U U') (f : String → String)
    (as : List String) : EvEq E E' (univPowP U f as) (univPowP U' f as) :=
  joinAll_congr (fun _ => rename_congr h) as

theorem domOfP_congr {E E' : Env} {U U' : Expr} (h : EvEq E E' U U') (xs : List String) :
    EvEq E E' (domOfP U xs) (domOfP U' xs) := univPowP_congr h _ xs

theorem padP_congr {E E' : Env} {U U' r r' : Expr} (h : EvEq E E' U U') (hr : EvEq E E' r r')
    (xs : List String) : EvEq E E' (padP U r xs) (padP U' r' xs) := by
  unfold padP; split
  · exact hr
  · exact nary_congr (.cons hr (.cons (domOfP_congr h xs) .nil))

theorem atomP_congr {E E' : Env} {U U' b b' : Expr} (h : EvEq E E' U U') (hb : EvEq E E' b b')
    (cs extra args) : EvEq E E' (atomP U b cs extra args) (atomP U' b' cs extra args) :=
  project_congr (select_congr (nary_congr (.cons hb (.cons (domOfP_congr h _) .nil))))

theorem compileP_congr {E E' : Env} {S : List (String × Nat)} (hE : DataEnv A S E E')
    (ar : List (String × Nat)) :
    ∀ φ : FO, (∀ p ∈ φ.rels, p ∈ S) →
      EvEq E E' (compileP (.name univName) RelN ar φ) (compileP (univLit A) (relLit A) ar φ)
  | .rel i args, hs => atomP_congr hE.univ (hE.rel _ (hs _ (List.mem_singleton_self _))) _ _ _
  | .gvar j args, _ => by
    simp only [compileP]; split
    · exact atomP_congr hE.univ (hE.guess j) _ _ _
    · exact nary_congr (.cons (domOfP_congr hE.univ _) (.cons (domOfP_congr hE.univ _) .nil))
  | .eq x y, _ => by
    simp only [compileP]; split
    · exact domOfP_congr hE.univ _
    · exact select_congr (domOfP_congr hE.univ _)
  | .not φ, hs => nary_congr (.cons (domOfP_congr hE.univ _) (.cons (compileP_congr hE ar φ hs) .nil))
  | .and φ ψ, hs => nary_congr
      (.cons (compileP_congr hE ar φ fun p hp => hs p (List.mem_append_left _ hp))
        (.cons (compileP_congr hE ar ψ fun p hp => hs p (List.mem_append_right _ hp)) .nil))
  | .or φ ψ, hs => nary_congr
      (.cons (padP_congr hE.univ (compileP_congr hE ar φ fun p hp => hs p (List.mem_append_left _ hp)) _)
        (.cons (padP_congr hE.univ (compileP_congr hE ar ψ fun p hp => hs p (List.mem_append_right _ hp)) _) .nil))
  | .ex x φ, hs => project_congr (padP_congr hE.univ (compileP_congr hE ar φ hs) _)
  | .all x φ, hs => nary_congr (.cons (domOfP_congr hE.univ _) (.cons (project_congr (nary_congr
      (.cons (domOfP_congr hE.univ _) (.cons (padP_congr hE.univ (compileP_congr hE ar φ hs) _) .nil)))) .nil))

/-! ## The condition, the members, and the multi solution set -/

theorem nonEmpty_congr {E E' : Env} {a b : Expr}
    (hc : (E.lookup inConditionName).isNone = (E'.lookup inConditionName).isNone)
    (h : EvEq E E' a b) : Cond.eval E [] (nonEmpty a) = Cond.eval E' [] (nonEmpty b) := by
  unfold nonEmpty; rw [Cond.eval, Cond.eval, gamma_congr (Agg.hasSub_agg _ _) hc h]

theorem evalMembers_congr {E E' : Env} : ∀ {ms ms' : List (String × Expr)},
    ms.map (·.1) = ms'.map (·.1) → EvEqs E E' (ms.map (·.2)) (ms'.map (·.2)) →
      evalMembers E [] ms = evalMembers E' [] ms'
  | [], [], _, _ => by rw [evalMembers, evalMembers]
  | (n, e) :: ms, (n', e') :: ms', hn, .cons h hs => by
    simp only [List.map_cons, List.cons.injEq] at hn
    obtain ⟨rfl, hn⟩ := hn
    rw [evalMembers, evalMembers, show Expr.eval E [] e = _ from h, evalMembers_congr hn hs]

theorem membersP_congr {E E' : Env} {U U' : Expr} (h : EvEq E E' U U') (ar : List (String × Nat)) :
    evalMembers E [] (membersP U ar) = evalMembers E' [] (membersP U' ar) := by
  rw [membersP_eq, membersP_eq]
  apply evalMembers_congr
  · simp only [List.map_map]; rfl
  · simp only [List.map_map]
    exact evEqs_map (g := fun (p : String × Nat) => (boolMemberP U p.1 p.2).2)
      (g' := fun (p : String × Nat) => (boolMemberP U' p.1 p.2).2)
      (fun _ => omegaSol_congr (univPowP_congr h _ _) holdsDec_indep) _

theorem omegaMsol_congr {E E' : Env} {ms ms' : List (String × Expr)} {c c' : Cond}
    (hm : evalMembers E [] ms = evalMembers E' [] ms')
    (hc : ∀ sols, evalMembers E' [] ms' = .ok sols →
      ∀ db ∈ choices (sols.map fun (n, s) => s.candidates.map (n, ·)),
        Cond.eval (inCondition (bindDb db E)) [] c = Cond.eval (inCondition (bindDb db E')) [] c') :
    EvEq E E' (.omegaMsol ms (some c)) (.omegaMsol ms' (some c')) := by
  unfold EvEq; rw [Expr.eval, Expr.eval]; simp only [List.any_nil, Bool.false_eq_true, ite_false]
  rw [hm]
  cases h : evalMembers E' [] ms' with
  | error e => rfl
  | ok sols =>
    simp only [bind, Except.bind]
    split
    · rfl
    · simp only [evalMsolCond]
      rw [filterM_congr (hc sols h)]

end Named

/-! ## Names

The names of the program's statements are different from one another, from the guesses'
names and from the name that marks a condition. -/

theorem toString_string (s : String) : toString s = s := rfl
theorem relName_toList (i : String) (n : Nat) :
    (relName i n).toList = 'r' :: 'e' :: 'l' :: '_' :: (i.toList ++ '_' :: Nat.toDigits 10 n) := by
  simp [relName, String.toList_append, toString_string]
theorem split_last : ∀ {a a' b b' : List Char}, '_' ∉ b → '_' ∉ b' →
    a ++ '_' :: b = a' ++ '_' :: b' → a = a' ∧ b = b'
  | [], [], _, _, _, _, h => by simpa using h
  | [], c :: a', b, b', hb, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.2 ▸ List.mem_append_right _ (List.mem_cons_self ..)) hb
  | c :: a, [], b, b', _, hb', h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.2 ▸ List.mem_append_right _ (List.mem_cons_self ..)) hb'
  | c :: a, c' :: a', b, b', hb, hb', h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := split_last hb hb' h
    exact ⟨rfl, rfl⟩

theorem relName_inj {i i' : String} {n n' : Nat} (h : relName i n = relName i' n') : i = i' ∧ n = n' := by
  have := congrArg String.toList h
  rw [relName_toList, relName_toList] at this
  simp only [List.cons.injEq, true_and] at this
  obtain ⟨h1, h2⟩ := split_last Nat.underscore_not_in_toDigits Nat.underscore_not_in_toDigits this
  refine ⟨String.toList_inj.mp h1, ?_⟩
  have := congrArg (Nat.ofDigitChars 10 · 0) h2
  simpa using this
theorem relName_ne_memberName (i j : String) (n : Nat) : relName i n ≠ memberName j := by
  intro h; have := congrArg String.toList h; rw [relName_toList] at this
  simp [memberName, String.toList_append] at this

theorem relName_ne_univName (i : String) (n : Nat) : relName i n ≠ univName := by
  intro h; have := congrArg String.toList h; rw [relName_toList] at this; simp [univName] at this

theorem relName_ne_esoName (i : String) (n : Nat) : relName i n ≠ esoName := by
  intro h; have := congrArg String.toList h; rw [relName_toList] at this; simp [esoName] at this

theorem relName_ne_cond (i : String) (n : Nat) : relName i n ≠ inConditionName := by
  intro h; have := congrArg String.toList h; rw [relName_toList] at this
  simp [inConditionName] at this

theorem univName_ne_memberName (j : String) : univName ≠ memberName j := by
  intro h; have := congrArg String.toList h; simp [univName, memberName, String.toList_append] at this

theorem univName_ne_cond : univName ≠ inConditionName := by decide

theorem univName_ne_leaf : univName ≠ leafName := by decide

theorem relName_ne_leaf (i : String) (n : Nat) : relName i n ≠ leafName := by
  intro h; have := congrArg String.toList h; rw [relName_toList] at this
  simp [leafName] at this

theorem univName_ne_esoName : univName ≠ esoName := by decide

/-! ## Environments -/

theorem lookup_unique {β : Type} : ∀ {l : List (String × β)} {k : String} {v : β},
    (k, v) ∈ l → (∀ p ∈ l, p.1 = k → p.2 = v) → l.lookup k = some v
  | [], _, _, h, _ => by cases h
  | (a, w) :: l, k, v, hm, hu => by
    by_cases e : k = a
    · subst e
      simp only [List.lookup, beq_self_eq_true]
      exact congrArg some (hu (k, w) (List.mem_cons_self ..) rfl)
    · have hne : (k == a) = false := by simpa using e
      simp only [List.lookup, hne]
      rcases List.mem_cons.mp hm with h | h
      · cases h; exact absurd rfl e
      · exact lookup_unique h fun p hp => hu p (List.mem_cons_of_mem _ hp)

theorem lookup_bindDb (db : Db) (E : Env) {k : String} (hk : k ≠ leafName) :
    (bindDb db E).lookup k = ((db.lookup k).map Val.finrel).or (E.lookup k) := by
  have hl : (k == leafName) = false := by simpa using hk
  induction db with
  | nil => simp [bindDb, List.lookup, hl]
  | cons p db ih =>
    obtain ⟨n, r⟩ := p
    by_cases e : k = n
    · subst e; simp [bindDb, List.lookup]
    · have hne : (k == n) = false := by simpa using e
      simp only [bindDb, List.map_cons, List.cons_append, List.lookup, hne] at ih ⊢
      exact ih

theorem lookup_inCondition {E : Env} {k : String} (h : k ≠ inConditionName) :
    (inCondition E).lookup k = E.lookup k := by
  have hne : (k == inConditionName) = false := by simpa using h
  simp only [inCondition, List.lookup, hne]

theorem cond_inCondition (E : Env) : ((inCondition E).lookup inConditionName).isNone = false := by
  simp [inCondition]

/-- The environment in which the program evaluates `eso`: it gives `univ` and `rel_i_n` the
literals' values, and it has no guess and no condition. -/
structure ProgEnv (A : Str) (S : List (String × Nat)) (E0 : Env) : Prop where
  univ : EvEq E0 [] (.name univName) (univLit A)
  rel : ∀ p ∈ S, EvEq E0 [] (.name (relName p.1 p.2)) (relLit A p.1 p.2)
  guess : ∀ j, E0.lookup (memberName j) = none
  cond : E0.lookup inConditionName = none

theorem dataEnv_cond {A : Str} {S : List (String × Nat)} {E0 : Env} (hP : ProgEnv A S E0)
    (db : Db) (hdb : ∀ p ∈ db, ∃ j, p.1 = memberName j) :
    DataEnv A S (inCondition (bindDb db E0)) (inCondition (bindDb db [])) := by
  have none_of : ∀ k, (∀ j, k ≠ memberName j) → db.lookup k = none := fun k hk =>
    lookup_none_of_not_mem fun hm => by
      obtain ⟨p, hp, e⟩ := List.mem_map.mp hm
      obtain ⟨j, hj⟩ := hdb p hp
      exact hk j (e ▸ hj)
  refine ⟨?_, fun p hp => ?_, fun j => ?_, by rw [cond_inCondition, cond_inCondition]⟩
  · have hl : (inCondition (bindDb db E0)).lookup univName = E0.lookup univName := by
      rw [lookup_inCondition univName_ne_cond, lookup_bindDb _ _ univName_ne_leaf, none_of _ univName_ne_memberName]; rfl
    exact (name_congr hl).trans (hP.univ.trans (univLit_indep A))
  · have hl : (inCondition (bindDb db E0)).lookup (relName p.1 p.2) = E0.lookup (relName p.1 p.2) := by
      rw [lookup_inCondition (relName_ne_cond _ _), lookup_bindDb _ _ (relName_ne_leaf _ _),
        none_of _ (relName_ne_memberName _ · _)]; rfl
    exact (name_congr hl).trans ((hP.rel p hp).trans (relLit_indep A _ _))
  · apply name_congr
    rw [lookup_inCondition (memberName_ne_cond j), lookup_inCondition (memberName_ne_cond j),
      lookup_bindDb _ _ (memberName_ne_leaf j), lookup_bindDb _ _ (memberName_ne_leaf j), hP.guess]; rfl

/-! ## The candidate databases name only guesses -/

theorem names_membersEval {env : Env} {tg : List Expr} : ∀ {ms : List (String × Expr)}
    {sols : List (String × Sol)}, MembersEval env tg ms sols → sols.map (·.1) = ms.map (·.1)
  | _, _, .nil => rfl
  | _, _, .cons _ _ h => by simp only [List.map_cons, names_membersEval h]

theorem mem_of_picks {α : Type} : ∀ {db : List α} {L : List (List α)}, Picks db L →
    ∀ p ∈ db, ∃ l ∈ L, p ∈ l
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hx hp, p, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hx⟩
    · obtain ⟨l, hl, hpl⟩ := mem_of_picks hp p h
      exact ⟨l, List.mem_cons_of_mem _ hl, hpl⟩

theorem db_memberNames {A : Str} {ar : List (String × Nat)} {sols : List (String × Sol)}
    (hs : evalMembers [] [] (membersP (univLit A) ar) = .ok sols) {db : Db}
    (hdb : db ∈ choices (sols.map fun (n, s) => s.candidates.map (n, ·))) :
    ∀ p ∈ db, ∃ j, p.1 = memberName j := by
  intro p hp
  obtain ⟨l, hl, hpl⟩ := mem_of_picks (mem_choices.mp hdb) p hp
  obtain ⟨⟨n, s⟩, hns, rfl⟩ := List.mem_map.mp hl
  obtain ⟨R, -, rfl⟩ := List.mem_map.mp hpl
  have hn : n ∈ (membersP (univLit A) ar).map (·.1) := by
    rw [← names_membersEval (evalMembers_ok hs)]
    exact List.mem_map_of_mem (f := (·.1)) hns
  rw [membersP_eq, List.map_map] at hn
  obtain ⟨⟨j, k⟩, -, e⟩ := List.mem_map.mp hn
  exact ⟨j, e.symm⟩

/-! ## The `eso` statement -/

/-- In the program's environment, the `eso` statement has the value of `esoForm`. -/
theorem eso_stmt {A : Str} {ψ : Sentence} {E0 : Env} (hP : ProgEnv A ψ.φ.rels E0) :
    EvEq E0 [] (.omegaMsol (membersP (.name univName) ψ.ar)
      (some (nonEmpty (compileP (.name univName) RelN ψ.ar ψ.φ)))) (esoForm ψ A) := by
  unfold esoForm
  refine omegaMsol_congr (membersP_congr hP.univ _) fun sols hs db hdb => ?_
  exact nonEmpty_congr (by rw [cond_inCondition, cond_inCondition])
    (compileP_congr (dataEnv_cond hP db (db_memberNames hs hdb)) _ _ fun p hp => hp)

/-! ## Running the program -/

/-- The value of a literal statement (it is evaluated before any other statement). -/
def litVal (r : Expr) : Val :=
  match Expr.eval [] [] r with
  | .ok v => v
  | .error _ => default

theorem litVal_eq {r : Expr} {v : Val} (h : Expr.eval [] [] r = .ok v) : litVal r = v := by
  simp [litVal, h]

/-- Statements whose values do not depend on the environment, and are not refused. -/
def Lits (D : List (String × Expr)) : Prop :=
  ∀ s ∈ D, (∀ E, Expr.eval E [] s.2 = Expr.eval [] [] s.2) ∧ ∃ v, Expr.eval [] [] s.2 = .ok v

theorem foldlM_lits : ∀ (D : List (String × Expr)) (env0 : Env), Lits D →
    D.foldlM (fun env (n, e) => do return env ++ [(n, ← e.eval env.reverse [])]) env0 =
      .ok (env0 ++ D.map fun s => (s.1, litVal s.2))
  | [], env0, _ => by simp [List.foldlM, pure, Except.pure]
  | (n, e) :: D, env0, h => by
    obtain ⟨hi, v, hv⟩ := h (n, e) (List.mem_cons_self ..)
    simp only at hi hv
    rw [List.foldlM_cons]; simp only; rw [hi, hv]
    refine (foldlM_lits D (env0 ++ [(n, v)]) (fun t ht => h t (List.mem_cons_of_mem _ ht))).trans ?_
    simp only [List.map_cons, litVal_eq hv, List.append_assoc, List.singleton_append]

/-- The program's data statements: `univ`, then `rel_i_n` for each symbol and arity. -/
def dataStmts (ψ : Sentence) (A : Str) : List (String × Expr) :=
  (univName, univLit A) :: ψ.φ.rels.eraseDups.map fun (i, n) => relStatement A i n

/-- The environment in which the program evaluates `eso`. -/
def progEnv (ψ : Sentence) (A : Str) : Env :=
  ((dataStmts ψ A).map fun s => (s.1, litVal s.2)).reverse

/-- The program's last statement. It names the data and does not depend on the structure. -/
def esoStmt (ψ : Sentence) : String × Expr :=
  (esoName, .omegaMsol (membersP (.name univName) ψ.ar)
    (some (nonEmpty (compileP (.name univName) RelN ψ.ar ψ.φ))))

/-- **The structure enters only as data.** The program is the data statements of `A`,
then a statement that depends only on the sentence. -/
theorem toProgram_eq (ψ : Sentence) (A : Str) : toProgram ψ A = dataStmts ψ A ++ [esoStmt ψ] := by
  unfold toProgram dataStmts esoStmt
  rw [compile_eq_compileP]
  rfl

theorem lits_dataStmts (ψ : Sentence) {A : Str} (hA : A.WF) : Lits (dataStmts ψ A) := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · obtain ⟨r, hr, -⟩ := eval_univLit A []
    exact ⟨fun E => univLit_indep A, _, hr⟩
  · obtain ⟨⟨i, n⟩, -, rfl⟩ := List.mem_map.mp hs
    obtain ⟨r, hr, -⟩ := eval_relLit A hA [] i n
    exact ⟨fun E => relLit_indep A i n, _, hr⟩

theorem mem_progEnv {ψ : Sentence} {A : Str} {p : String × Val} (hp : p ∈ progEnv ψ A) :
    p = (univName, litVal (univLit A)) ∨
      ∃ q : String × Nat, p = (relName q.1 q.2, litVal (relLit A q.1 q.2)) := by
  unfold progEnv at hp
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hp)
  rcases List.mem_cons.mp hs with rfl | hs
  · exact .inl rfl
  · obtain ⟨⟨i, n⟩, -, rfl⟩ := List.mem_map.mp hs
    exact .inr ⟨(i, n), rfl⟩

theorem progEnv_spec (ψ : Sentence) {A : Str} (hA : A.WF) : ProgEnv A ψ.φ.rels (progEnv ψ A) := by
  have hl := lits_dataStmts ψ hA
  have hval : ∀ s ∈ dataStmts ψ A, Expr.eval [] [] s.2 = .ok (litVal s.2) := fun s hs => by
    obtain ⟨-, v, hv⟩ := hl s hs; rw [hv, litVal_eq hv]
  have hmem : ∀ s ∈ dataStmts ψ A, (s.1, litVal s.2) ∈ progEnv ψ A := fun s hs =>
    List.mem_reverse.mpr (List.mem_map_of_mem (f := fun s => (s.1, litVal s.2)) hs)
  have names : ∀ p ∈ progEnv ψ A, p.1 = univName ∨ ∃ q : String × Nat, p.1 = relName q.1 q.2 :=
    fun p hp => by
      rcases mem_progEnv hp with rfl | ⟨q, rfl⟩
      · exact .inl rfl
      · exact .inr ⟨q, rfl⟩
  have absent : ∀ k, k ≠ univName → (∀ q : String × Nat, k ≠ relName q.1 q.2) →
      (progEnv ψ A).lookup k = none := fun k h1 h2 =>
    lookup_none_of_not_mem fun hm => by
      obtain ⟨p, hp, e⟩ := List.mem_map.mp hm
      rcases names p hp with h | ⟨q, h⟩
      · exact h1 (e ▸ h)
      · exact h2 q (e ▸ h)
  refine ⟨?_, fun q hq => ?_, fun j => ?_, ?_⟩
  · have hu : (progEnv ψ A).lookup univName = some (litVal (univLit A)) := by
      refine lookup_unique (hmem _ (List.mem_cons_self ..)) fun p hp e => ?_
      rcases mem_progEnv hp with rfl | ⟨q, rfl⟩
      · rfl
      · exact absurd e (relName_ne_univName _ _)
    unfold EvEq; rw [Expr.eval, hval _ (List.mem_cons_self ..)]
    simp only [List.any_nil, Bool.false_eq_true, ite_false, hu]
  · have hs : relStatement A q.1 q.2 ∈ dataStmts ψ A :=
      List.mem_cons_of_mem _ (List.mem_map_of_mem (f := fun (q : String × Nat) => relStatement A q.1 q.2)
        (List.mem_eraseDups.mpr hq))
    have hu : (progEnv ψ A).lookup (relName q.1 q.2) = some (litVal (relLit A q.1 q.2)) := by
      refine lookup_unique (hmem _ hs) fun p hp e => ?_
      rcases mem_progEnv hp with rfl | ⟨q', rfl⟩
      · exact absurd e.symm (relName_ne_univName _ _)
      · obtain ⟨h1, h2⟩ := relName_inj e
        show litVal (relLit A q'.1 q'.2) = _
        rw [h1, h2]
    unfold EvEq; rw [Expr.eval, show relLit A q.1 q.2 = (relStatement A q.1 q.2).2 from rfl, hval _ hs]
    simp only [List.any_nil, Bool.false_eq_true, ite_false, hu]; rfl
  · exact absent _ (univName_ne_memberName j).symm fun q h => relName_ne_memberName _ _ _ h.symm
  · exact absent _ univName_ne_cond.symm fun q h => relName_ne_cond _ _ h.symm

/-- The program runs: it gives each data statement its literal's value and `eso` the
value of `esoForm`. -/
theorem run_toProgram (ψ : Sentence) {A : Str} (hA : A.WF) {v : Val}
    (hv : Expr.eval [] [] (esoForm ψ A) = .ok v) :
    runProgram (toProgram ψ A) =
      .ok ((dataStmts ψ A).map (fun s => (s.1, litVal s.2)) ++ [(esoName, v)]) := by
  unfold runProgram
  rw [toProgram_eq, List.foldlM_append, foldlM_lits _ _ (lits_dataStmts ψ hA)]
  simp only [esoStmt, List.nil_append, bind, Except.bind, List.foldlM_cons, List.foldlM_nil]
  have he := (eso_stmt (progEnv_spec ψ hA)).trans hv
  unfold progEnv at he
  rw [he]
  rfl

/-- **The program expresses every ESO sentence.** Run `toProgram ψ A`, with the structure's data in named
statements: it is not refused, and `eso` has a candidate exactly when `ψ` holds on `A`. -/
theorem toProgram_expresses (ψ : Sentence) (A : Str) (hA : A.WF) (hC : A.Comparable) :
    ∃ b, ToProgram.decide ψ A = .ok b ∧ (b = true ↔ ψ.Holds A) := by
  obtain ⟨m, hm, hiff⟩ := esoForm_expresses ψ A hA hC
  have hl : ((dataStmts ψ A).map (fun s => (s.1, litVal s.2)) ++ [(esoName, Val.msol m)]).lookup esoName =
      some (.msol m) := by
    refine lookup_unique (List.mem_append_right _ (List.mem_singleton_self _)) fun p hp e => ?_
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
      rcases List.mem_cons.mp hs with rfl | hs
      · exact absurd e univName_ne_esoName
      · obtain ⟨⟨i, n⟩, -, rfl⟩ := List.mem_map.mp hs
        exact absurd e (relName_ne_esoName _ _)
    · rw [List.mem_singleton.mp hp]
  refine ⟨!m.candidates.isEmpty, ?_, ?_⟩
  · unfold ToProgram.decide
    rw [run_toProgram ψ hA hm]
    simp only [bind, Except.bind, hl]; rfl
  · rw [← hiff]
    cases h : m.candidates with
    | nil => simp
    | cons db _ => simp

end Rasso.ESO
