import Rasso.Mem

/-!
# Rasso: solution sets are function spaces

Theorems `thm:r2-sol-meaning` and `thm:r2-fspace-graph` of the Rasso blueprint.

In plain words, this file proves:

* **C2, Dom^n.** `Unrel.assignments h` lists exactly the tuples that give each attribute
  of `h` one value from its domain (`Unrel.mem_assignments`), and is refused exactly when
  some domain's values can't be listed (`Unrel.assignments_ok_iff`). The tuples of an
  unrestricted relation are the assignments where its term holds (`Unrel.mem_tuples`).
* **C3, ω_sol is a function space.** A candidate of ω_sol(D, X) is the graph of a total
  function from the tuples of D to the tuples of X, and every such graph is a candidate
  (`mem_omegaSolCandidates`). There are |X|^|D| of them (`length_omegaSolCandidates`), a graph
  determines its function (`graph_inj`), so each function is listed once
  (`nodup_omegaSolCandidates`).
* **C4, σ_sol picks a subset.** σ_sol keeps the candidates that pass its condition
  (`sigmaSol_meaning`), and what it keeps does not depend on the order or the repeats of
  the candidate list (`sigmaSol_order`).
* **C5, the set meaning of a multi solution set.** A database "is in" a multi
  solution set when it binds each member's name to one of that member's candidates and
  passes every condition (`MsolMeaning`). ω_msol and σ_msol give exactly these databases
  (`mem_omegaMsolDbs`, `omegaMsol_meaning`, `sigmaMsol_meaning`); the count is the
  product of the members' counts (`length_omegaMsolDbs`).

Nothing here says which candidate is best: Rasso states problems, and finding optimal
candidates is outside the algebra.

Conventions:

* The lemmas are about the expressions the `omegaSol`, `sigmaSol`, `omegaMsol`
  (with `evalMsolCond`) and `sigmaMsol` cases of `Expr.eval` compute, copied word for
  word (`omegaSolCandidates`, `omegaMsolDbs`, and `List.filterM` with the condition as an
  abstract test `p`). `Expr.eval` is total, and `Rasso.Bridge.Sol` states these lemmas
  about `Expr.eval` itself.
* "Function from the tuples of D" means a Lean function `Tuple → Tuple`; only its values
  on D's tuples matter (`graph` reads nothing else). Two functions that agree on D's
  tuples are the same candidate.
* Well-formedness is a hypothesis where it is needed (`Tuple.Over`: attributes strictly
  increasing, all from a given list). That every `Finrel` the operators build is well
  formed is proved in `Rasso.WF`. Decision tuples from an unrestricted relation
  are well formed when its heading names no attribute twice (`Fits.over`).
* "Each once" needs the decision tuples listed without repeats; whether
  `Unrel.tuples` can repeat (a domain listing a value twice) is left open.
* The ω_msol lemmas take the member list as already evaluated (`List (String × Sol)`);
  the refusals for no members and for a member named `I` are not restated.
* Axioms: the lemmas about the filtering steps (σ_sol order, σ_msol, ω_msol's
  databases) use only `propext` and `Quot.sound`. The others also show
  `Classical.choice`, inherited from definitions they mention (`Domain.values?`,
  `Tuple.ofPairs` through `List.mergeSort`) and from core's `String` order lemmas.
-/

namespace Rasso

/-! ## Filtering in `Except`, for any kind of item -/

/-- The test passed: it gave `true` and was not refused. -/
def passed {ε : Type} : Except ε Bool → Bool
  | .ok true => true
  | _ => false

/-- The test was not refused. -/
def Succeeds {ε α : Type} : Except ε α → Prop
  | .ok _ => True
  | .error _ => False

theorem filterAuxM_ok_iff {ε α : Type} {p : α → Except ε Bool} :
    ∀ {l acc res : List α}, List.filterAuxM p l acc = .ok res ↔
      (∀ x ∈ l, Succeeds (p x)) ∧ res = (l.filter fun x => passed (p x)).reverse ++ acc
  | [], acc, res => by
    simp only [List.filterAuxM, pure, Except.pure, Except.ok.injEq, List.not_mem_nil,
      false_implies, implies_true, List.filter_nil, List.reverse_nil, List.nil_append, true_and]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  | y :: l, acc, res => by
    simp only [List.filterAuxM, bind, Except.bind]
    cases hy : p y with
    | error e =>
      simp [hy, Succeeds]
    | ok b =>
      simp only [filterAuxM_ok_iff, List.mem_cons, forall_eq_or_imp, hy, Succeeds,
        true_and, List.filter_cons]
      cases b <;> simp [passed]

theorem filterM_ok_iff {ε α : Type} {p : α → Except ε Bool} {l res : List α} :
    l.filterM p = .ok res ↔ (∀ x ∈ l, Succeeds (p x)) ∧ res = l.filter fun x => passed (p x) := by
  simp only [List.filterM, bind, Except.bind]
  cases ha : List.filterAuxM p l [] with
  | error e =>
    simp only [reduceCtorEq, false_iff, not_and]
    intro hok
    have := (filterAuxM_ok_iff (acc := []) (res := (l.filter fun x => passed (p x)).reverse)).mpr
      ⟨hok, by simp⟩
    rw [ha] at this; cases this
  | ok r =>
    have := (filterAuxM_ok_iff (p := p) (l := l) (acc := []) (res := r)).mp ha
    simp only [pure, Except.pure, Except.ok.injEq, List.append_nil] at this ⊢
    obtain ⟨hok, rfl⟩ := this
    simp only [List.reverse_reverse]
    exact ⟨fun h => ⟨hok, h.symm⟩, fun h => h.2.symm⟩

theorem passed_iff {ε : Type} {e : Except ε Bool} : passed e = true ↔ e = .ok true := by
  cases e with
  | error => simp [passed]
  | ok b => cases b <;> simp [passed]

theorem mem_filterM {ε α : Type} {p : α → Except ε Bool} {l res : List α}
    (h : l.filterM p = .ok res) (x : α) : x ∈ res ↔ x ∈ l ∧ p x = .ok true := by
  obtain ⟨_, rfl⟩ := filterM_ok_iff.mp h
  rw [List.mem_filter, passed_iff]

/-- Filtering sees only which items there are: two lists with the same members (in any
order, with any repeats) are refused together, and otherwise give results with the
same members. -/
theorem filterM_sameMembers {ε α : Type} {p : α → Except ε Bool} {l l' res : List α}
    (hl : ∀ x, x ∈ l ↔ x ∈ l') (h : l.filterM p = .ok res) :
    ∃ res', l'.filterM p = .ok res' ∧ ∀ x, x ∈ res ↔ x ∈ res' := by
  obtain ⟨hok, rfl⟩ := filterM_ok_iff.mp h
  refine ⟨_, filterM_ok_iff.mpr ⟨fun x hx => hok x ((hl x).mpr hx), rfl⟩, fun x => ?_⟩
  simp only [List.mem_filter, hl x]

/-! ## Tuples: looking attributes up -/

/-- A well-formed tuple: its attributes strictly increase, so it is sorted and has no
attribute twice. `Tuple.ofPairs` gives such tuples when no attribute is given twice. -/
def Tuple.Sorted (t : Tuple) : Prop := t.Pairwise fun p q => p.1 < q.1

/-- A well-formed tuple whose attributes all come from `as`. -/
def Tuple.Over (as : List String) (t : Tuple) : Prop :=
  Tuple.Sorted t ∧ ∀ q ∈ t, q.1 ∈ as

theorem lookup_cons_self {a : String} {v : Value} {l : List (String × Value)} :
    ((a, v) :: l).lookup a = some v := by simp [List.lookup]

theorem lookup_cons_ne {a b : String} {v : Value} {l : List (String × Value)} (h : a ≠ b) :
    ((b, v) :: l).lookup a = l.lookup a := by
  have : (a == b) = false := by simpa using h
  simp [List.lookup, this]

theorem lookup_eq_none {a : String} : ∀ {l : List (String × Value)},
    (∀ q ∈ l, q.1 ≠ a) → l.lookup a = none
  | [], _ => rfl
  | (b, v) :: l, h => by
    rw [lookup_cons_ne (fun e => h (b, v) (List.mem_cons_self) e.symm)]
    exact lookup_eq_none fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem Tuple.get?_eq_none_of_over {as : List String} {t : Tuple} {a : String}
    (ht : Tuple.Over as t) (ha : a ∉ as) : Tuple.get? t a = none :=
  lookup_eq_none fun q hq e => ha (e ▸ ht.2 q hq)

theorem Tuple.nodup_keys {t : Tuple} (ht : Tuple.Sorted t) : (t.map (·.1)).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  exact ht.imp fun {p q} h (e : p.1 = q.1) => String.lt_irrefl q.1 (e ▸ h)

/-- Two well-formed tuples that give the same value for every attribute are equal. -/
theorem Tuple.ext_get? : ∀ {t u : Tuple}, Tuple.Sorted t → Tuple.Sorted u →
    (∀ a, Tuple.get? t a = Tuple.get? u a) → t = u
  | [], [], _, _, _ => rfl
  | [], (b, w) :: _, _, _, h => by
    have := h b; simp [Tuple.get?] at this
  | (a, v) :: _, [], _, _, h => by
    have := h a; simp [Tuple.get?] at this
  | (a, v) :: t, (b, w) :: u, ht, hu, h => by
    have ht' : Tuple.Sorted t := (List.pairwise_cons.mp ht).2
    have hu' : Tuple.Sorted u := (List.pairwise_cons.mp hu).2
    have hta : ∀ q ∈ t, a < q.1 := (List.pairwise_cons.mp ht).1
    have hub : ∀ q ∈ u, b < q.1 := (List.pairwise_cons.mp hu).1
    have none_t : ∀ c, c < a ∨ c = a → Tuple.get? t c = none := fun c hc =>
      lookup_eq_none fun q hq e => by
        have h1 := hta q hq
        rw [e] at h1
        rcases hc with hc | hc
        · exact String.lt_asymm hc h1
        · subst hc; exact String.lt_irrefl _ h1
    have none_u : ∀ c, c < b ∨ c = b → Tuple.get? u c = none := fun c hc =>
      lookup_eq_none fun q hq e => by
        have h1 := hub q hq
        rw [e] at h1
        rcases hc with hc | hc
        · exact String.lt_asymm hc h1
        · subst hc; exact String.lt_irrefl _ h1
    -- the first attributes are the same
    have hab : a = b := by
      rcases String.le_total a b with hle | hle
      · by_cases hlt : a < b
        · have := h a
          simp only [Tuple.get?] at this
          rw [lookup_cons_self, lookup_cons_ne (fun (e : a = b) => String.lt_irrefl a (by rw [e] at hlt ⊢; exact hlt)),
            show u.lookup a = none from none_u a (Or.inl hlt)] at this
          cases this
        · exact String.le_antisymm hle (String.not_lt.mp hlt)
      · by_cases hlt : b < a
        · have := h b
          simp only [Tuple.get?] at this
          rw [lookup_cons_self, lookup_cons_ne (fun (e : b = a) => String.lt_irrefl b (by rw [e] at hlt ⊢; exact hlt)),
            show t.lookup b = none from none_t b (Or.inl hlt)] at this
          cases this
        · exact (String.le_antisymm hle (String.not_lt.mp hlt)).symm
    subst hab
    have hvw : v = w := by
      have := h a; simp only [Tuple.get?, lookup_cons_self, Option.some.injEq] at this; exact this
    subst hvw
    have rest : t = u := Tuple.ext_get? ht' hu' fun c => by
      by_cases hc : c = a
      · rw [none_t c (Or.inr hc), none_u c (Or.inr hc)]
      · have := h c
        simp only [Tuple.get?] at this
        rwa [lookup_cons_ne hc, lookup_cons_ne hc] at this
    rw [rest]

/-! ## Merging two tuples -/

theorem lookup_mem_val {a : String} {v : Value} : ∀ {l : List (String × Value)},
    l.lookup a = some v → (a, v) ∈ l
  | [], h => by cases h
  | (b, w) :: l, h => by
    by_cases hab : a = b
    · subst hab; rw [lookup_cons_self] at h; cases h; exact List.mem_cons_self
    · rw [lookup_cons_ne hab] at h; exact List.mem_cons_of_mem _ (lookup_mem_val h)

theorem lookup_of_mem {a : String} {v : Value} : ∀ {l : List (String × Value)},
    (l.map (·.1)).Nodup → (a, v) ∈ l → l.lookup a = some v
  | [], _, h => by cases h
  | (b, w) :: l, hn, h => by
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_cons.mp h with e | e
    · cases e; exact lookup_cons_self
    · have hab : a ≠ b := fun e' => hn'.1 (e' ▸ List.mem_map_of_mem (f := (·.1)) e)
      rw [lookup_cons_ne hab]; exact lookup_of_mem hn'.2 e

/-- Reordering a list with no attribute twice does not change what it looks up. -/
theorem lookup_perm {a : String} {l l' : List (String × Value)} (hp : l.Perm l')
    (hn : (l.map (·.1)).Nodup) : l.lookup a = l'.lookup a := by
  have hn' : (l'.map (·.1)).Nodup := ((hp.map _).nodup_iff).mp hn
  cases h : l.lookup a with
  | none =>
    cases h' : l'.lookup a with
    | none => rfl
    | some v =>
      have := lookup_of_mem hn (hp.mem_iff.mpr (lookup_mem_val h'))
      rw [h] at this; cases this
  | some v => exact (lookup_of_mem hn' (hp.mem_iff.mp (lookup_mem_val h))).symm

theorem Tuple.get?_ofPairs {ps : List (String × Value)} (hn : (ps.map (·.1)).Nodup)
    (a : String) : Tuple.get? (Tuple.ofPairs ps) a = ps.lookup a :=
  lookup_perm (List.mergeSort_perm _ _) (((List.mergeSort_perm _ _).map _).nodup_iff.mpr hn)

theorem lookup_filter_get? {a : String} {t : Tuple} :
    ∀ (u : Tuple), (t.lookup a).isNone = true →
      (u.filter fun p => (Tuple.get? t p.1).isNone).lookup a = u.lookup a
  | [], _ => rfl
  | (b, w) :: u, ha => by
    rw [List.filter_cons]
    by_cases hab : a = b
    · subst hab
      simp only [Tuple.get?, ha, ite_true, lookup_cons_self]
    · split
      · rw [lookup_cons_ne hab, lookup_cons_ne hab, lookup_filter_get? u ha]
      · rw [lookup_cons_ne hab, lookup_filter_get? u ha]

/-- The value of an attribute in a merge: the left tuple's, else the right's. -/
theorem Tuple.get?_merge {t u : Tuple} (ht : Tuple.Sorted t) (hu : Tuple.Sorted u) (a : String) :
    Tuple.get? (Tuple.merge t u) a = (Tuple.get? t a).or (Tuple.get? u a) := by
  have hn : ((t ++ u.filter fun p => (Tuple.get? t p.1).isNone).map (·.1)).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨Tuple.nodup_keys ht, ?_, ?_⟩
    · have := Tuple.nodup_keys hu
      exact (List.filter_sublist.map _).nodup this
    · intro x hx y hy e
      subst e
      obtain ⟨⟨_, v⟩, hq, rfl⟩ := List.mem_map.mp hx
      obtain ⟨⟨_, w⟩, hq', e⟩ := List.mem_map.mp hy
      simp only at e; subst e
      have hnone := (List.mem_filter.mp hq').2
      have hsome : Tuple.get? t _ = some v := lookup_of_mem (Tuple.nodup_keys ht) hq
      rw [hsome] at hnone; cases hnone
  unfold Tuple.merge
  rw [Tuple.get?_ofPairs hn, List.lookup_append]
  cases h : t.lookup a with
  | some v => simp [Tuple.get?, h]
  | none =>
    simp only [Tuple.get?, h, Option.none_or]
    exact lookup_filter_get? u (by simp [h])

/-- A merge of a tuple over `D` with a tuple over `X`, where no attribute is in both,
gives back both parts. -/
theorem Tuple.merge_inj {D X : List String} (hdx : ∀ a ∈ D, a ∉ X)
    {t t' p p' : Tuple} (ht : Tuple.Over D t) (ht' : Tuple.Over D t') (hp : Tuple.Over X p) (hp' : Tuple.Over X p')
    (h : Tuple.merge t p = Tuple.merge t' p') : t = t' ∧ p = p' := by
  have hg : ∀ a, (Tuple.get? t a).or (Tuple.get? p a) = (Tuple.get? t' a).or (Tuple.get? p' a) := fun a => by
    rw [← Tuple.get?_merge ht.1 hp.1, ← Tuple.get?_merge ht'.1 hp'.1, h]
  constructor
  · refine Tuple.ext_get? ht.1 ht'.1 fun a => ?_
    by_cases ha : a ∈ D
    · have := hg a
      rwa [Tuple.get?_eq_none_of_over hp (hdx a ha), Tuple.get?_eq_none_of_over hp' (hdx a ha),
        Option.or_none, Option.or_none] at this
    · rw [Tuple.get?_eq_none_of_over ht ha, Tuple.get?_eq_none_of_over ht' ha]
  · refine Tuple.ext_get? hp.1 hp'.1 fun a => ?_
    by_cases ha : a ∈ D
    · rw [Tuple.get?_eq_none_of_over hp (hdx a ha), Tuple.get?_eq_none_of_over hp' (hdx a ha)]
    · have := hg a
      rwa [Tuple.get?_eq_none_of_over ht ha, Tuple.get?_eq_none_of_over ht' ha,
        Option.none_or, Option.none_or] at this

/-! ## The tuples of an unrestricted relation -/

/-- `Fits h ps`: `ps` gives each attribute of the heading `h`, in order, one value from
its domain (whose values can be listed). -/
inductive Fits : Heading → List (String × Value) → Prop
  | nil : Fits [] []
  | cons {a : String} {d : Domain} {vs : List Value} {v : Value} {h : Heading}
      {ps : List (String × Value)} :
      d.values? = some vs → v ∈ vs → Fits h ps → Fits ((a, d) :: h) ((a, v) :: ps)

/-- What one round of the loop in `Unrel.assignments` does. -/
def AssignStep (F : String × Domain → List Tuple → Except String (ForInStep (List Tuple))) :
    Prop :=
  ∀ a d acc, (∀ vs, d.values? = some vs →
      F (a, d) acc = .ok (.yield (acc.flatMap fun t => vs.map fun v => (a, v) :: t))) ∧
    (d.values? = none → ∃ e, F (a, d) acc = .error e)

theorem assignStep_loop {F : String × Domain → List Tuple → Except String (ForInStep (List Tuple))}
    (hF : AssignStep F) : ∀ (h : Heading) (acc res : List Tuple), forIn h acc F = .ok res →
      ∀ t, t ∈ res ↔ ∃ s ∈ acc, ∃ ps, Fits h ps ∧ t = ps.reverse ++ s
  | [], acc, res, hr, t => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hr
    subst hr
    constructor
    · intro ht; exact ⟨t, ht, [], .nil, rfl⟩
    · rintro ⟨s, hs, ps, hps, rfl⟩; cases hps; exact hs
  | (a, d) :: h, acc, res, hr, t => by
    rw [List.forIn_cons] at hr
    cases hv : d.values? with
    | none =>
      obtain ⟨e, he⟩ := (hF a d acc).2 hv
      rw [he] at hr; cases hr
    | some vs =>
      rw [(hF a d acc).1 vs hv] at hr
      simp only [bind, Except.bind] at hr
      rw [assignStep_loop hF h _ res hr t]
      constructor
      · rintro ⟨s', hs', ps, hps, rfl⟩
        obtain ⟨s, hs, hs'⟩ := List.mem_flatMap.mp hs'
        obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hs'
        exact ⟨s, hs, (a, v) :: ps, .cons hv hv' hps, by rw [List.reverse_cons, List.append_assoc]; rfl⟩
      · rintro ⟨s, hs, ps, hps, rfl⟩
        cases hps with
        | cons hd hv' hps =>
          rw [hv] at hd; cases hd
          exact ⟨_, List.mem_flatMap.mpr ⟨s, hs, List.mem_map.mpr ⟨_, hv', rfl⟩⟩, _, hps,
            by rw [List.reverse_cons, List.append_assoc]; rfl⟩

theorem assignStep_loop_ok {F : String × Domain → List Tuple → Except String (ForInStep (List Tuple))}
    (hF : AssignStep F) : ∀ (h : Heading) (acc : List Tuple),
      (∃ res, forIn h acc F = .ok res) ↔ ∀ p ∈ h, (p.2.values?).isSome
  | [], acc => by simp [List.forIn_nil, pure, Except.pure]
  | (a, d) :: h, acc => by
    rw [List.forIn_cons]
    cases hv : d.values? with
    | none =>
      obtain ⟨e, he⟩ := (hF a d acc).2 hv
      rw [he]
      simp only [bind, Except.bind, reduceCtorEq, exists_false, false_iff]
      intro hall
      have := hall (a, d) List.mem_cons_self
      simp [hv] at this
    | some vs =>
      rw [(hF a d acc).1 vs hv]
      simp only [bind, Except.bind, assignStep_loop_ok hF h, List.mem_cons, forall_eq_or_imp, hv,
        Option.isSome_some, true_and]

theorem forIn_ne_error {F : String × Domain → List Tuple → Except String (ForInStep (List Tuple))}
    (hF : AssignStep F) {h : Heading} {acc : List Tuple} (hall : ∀ p ∈ h, (p.2.values?).isSome)
    {e : String} : forIn h acc F ≠ .error e := by
  obtain ⟨res, hres⟩ := (assignStep_loop_ok hF h acc).mpr hall
  rw [hres]; exact fun h => by cases h

/-- The loop in `Unrel.assignments` is an `AssignStep` loop. -/
theorem assignStep_of_values {F : String × Domain → List Tuple → Except String (ForInStep (List Tuple))}
    (h1 : ∀ a d acc vs, d.values? = some vs →
      F (a, d) acc = .ok (.yield (acc.flatMap fun t => vs.map fun v => (a, v) :: t)))
    (h2 : ∀ a d acc, d.values? = none → ∃ e, F (a, d) acc = .error e) : AssignStep F :=
  fun a d acc => ⟨h1 a d acc, h2 a d acc⟩

/-- **Dom^n.** The assignments over a heading are exactly the tuples that give each
attribute one value from its domain. (The pairs are built last attribute first, hence
`reverse`; `Tuple.ofPairs` then sorts them by attribute name.) -/
theorem Unrel.mem_assignments {h : Heading} {ts : List Tuple}
    (hr : Unrel.assignments h = .ok ts) (t : Tuple) :
    t ∈ ts ↔ ∃ ps, Fits h ps ∧ t = Tuple.ofPairs ps.reverse := by
  unfold Unrel.assignments at hr
  simp only [bind, Except.bind] at hr
  split at hr
  · cases hr
  · rename_i res hres
    simp only [pure, Except.pure, Except.ok.injEq] at hr
    subst hr
    refine (fun key => ?_) (assignStep_loop (assignStep_of_values ?s1 ?s2) h [[]] res hres)
    case s1 => intro a d acc vs hv; simp only [hv]; rfl
    case s2 => intro a d acc hv; simp only [hv]; exact ⟨_, rfl⟩
    simp only [List.mem_map, key, List.mem_singleton]
    constructor
    · rintro ⟨_, ⟨_, rfl, ps, hps, rfl⟩, rfl⟩; exact ⟨ps, hps, by simp⟩
    · rintro ⟨ps, hps, rfl⟩; exact ⟨_, ⟨_, rfl, ps, hps, rfl⟩, by simp⟩

/-- The assignments are refused exactly when some domain's values can't be listed. -/
theorem Unrel.assignments_ok_iff (h : Heading) :
    (∃ ts, Unrel.assignments h = .ok ts) ↔ ∀ p ∈ h, (p.2.values?).isSome := by
  unfold Unrel.assignments
  simp only [bind, Except.bind]
  constructor
  · rintro ⟨ts, hts⟩
    split at hts
    · cases hts
    · rename_i res hres
      refine (assignStep_loop_ok (assignStep_of_values ?s1 ?s2) h [[]]).mp ⟨res, hres⟩
      case s1 => intro a d acc vs hv; simp only [hv]; rfl
      case s2 => intro a d acc hv; simp only [hv]; exact ⟨_, rfl⟩
  · intro hall
    split
    · rename_i e he
      refine absurd he (forIn_ne_error (assignStep_of_values ?s1 ?s2) hall)
      case s1 => intro a d acc vs hv; simp only [hv]; rfl
      case s2 => intro a d acc hv; simp only [hv]; exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- **Subsets of Dom^n.** The tuples of an unrestricted relation are the assignments
for which its term holds. -/
theorem Unrel.mem_tuples {u : Unrel} {ts : List Tuple} (hr : u.tuples = .ok ts) (t : Tuple) :
    t ∈ ts ↔ (∃ ps, Fits u.heading ps ∧ t = Tuple.ofPairs ps.reverse) ∧
      u.term.holds t = .ok true := by
  unfold Unrel.tuples at hr
  simp only [bind, Except.bind] at hr
  split at hr
  · cases hr
  · rename_i as has
    rw [mem_filterM hr, Unrel.mem_assignments has]

/-- The tuples `Tuple.ofPairs` builds are well formed when no attribute is given twice. -/
theorem Tuple.sorted_ofPairs {ps : List (String × Value)} (hn : (ps.map (·.1)).Nodup) :
    Tuple.Sorted (Tuple.ofPairs ps) := by
  have hp := List.mergeSort_perm ps fun p q => decide (p.1 ≤ q.1)
  have hle := List.pairwise_mergeSort (le := fun p q : String × Value => decide (p.1 ≤ q.1))
    (fun a b c h₁ h₂ => by simp only [decide_eq_true_eq] at *; exact String.le_trans h₁ h₂)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact String.le_total _ _) ps
  have hne : (ps.mergeSort fun p q => decide (p.1 ≤ q.1)).Pairwise fun p q => p.1 ≠ q.1 := by
    have := ((hp.map (·.1)).nodup_iff).mpr hn
    unfold List.Nodup at this; rwa [List.pairwise_map] at this
  refine (hle.and hne).imp fun {p q} ⟨h₁, h₂⟩ => ?_
  simp only [decide_eq_true_eq] at h₁
  rcases Decidable.em (p.1 < q.1) with h | h
  · exact h
  · exact absurd (String.le_antisymm h₁ (String.not_lt.mp h)) h₂

theorem Fits.keys {h : Heading} {ps : List (String × Value)} (hf : Fits h ps) :
    ps.map (·.1) = h.attrs := by
  induction hf with
  | nil => rfl
  | cons _ _ _ ih => simp [Heading.attrs] at *; exact ih

/-- An assignment over a heading with no attribute twice is a well-formed tuple over
the heading's attributes. -/
theorem Fits.over {h : Heading} {ps : List (String × Value)} (hf : Fits h ps)
    (hn : h.attrs.Nodup) : Tuple.Over h.attrs (Tuple.ofPairs ps.reverse) := by
  have hk : (ps.reverse.map (·.1)).Nodup := by
    rw [List.map_reverse, hf.keys]; unfold List.Nodup; rw [List.pairwise_reverse]; exact hn.imp Ne.symm
  refine ⟨Tuple.sorted_ofPairs hk, fun q hq => ?_⟩
  have := (List.mergeSort_perm ps.reverse _).mem_iff.mp hq
  rw [List.mem_reverse] at this
  rw [← hf.keys]; exact List.mem_map_of_mem this

/-! ## ω_sol: the candidates are the total functions -/

/-- The candidates ω_sol(D, X) builds: this is, word for word, the expression in the
`omegaSol` case of `Expr.eval`, with `rows` the tuples of D, `picks` the tuples of X and
`h` the heading of D then X. Each choice of one decision tuple per data tuple gives one
candidate: the data tuples, each merged with its decision. -/
def omegaSolCandidates (h : Heading) (rows picks : List Tuple) : List Finrel :=
  (choices (rows.map fun _ => picks)).map fun ps =>
    Finrel.ofTuples h ((rows.zip ps).map fun (t, p) => t.merge p)

/-- The graph of a function `f` on the data's tuples: each data tuple merged with its
value. -/
def graph (h : Heading) (rows : List Tuple) (f : Tuple → Tuple) : Finrel :=
  Finrel.ofTuples h (rows.map fun t => t.merge (f t))

theorem picks_replicate {α β : Type} {X : List α} : ∀ {rows : List β} {ps : List α},
    Picks ps (rows.map fun _ => X) ↔ ps.length = rows.length ∧ ∀ p ∈ ps, p ∈ X
  | [], ps => by
    simp only [List.map_nil, List.length_nil]
    constructor
    · intro h; cases h; simp
    · rintro ⟨h, -⟩; rw [List.length_eq_zero_iff.mp h]; exact .nil
  | r :: rows, ps => by
    simp only [List.map_cons, List.length_cons]
    constructor
    · intro h
      cases h with
      | cons hx hp =>
        obtain ⟨h1, h2⟩ := picks_replicate.mp hp
        exact ⟨by simp [h1], by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨hx, h2⟩⟩
    · rintro ⟨h1, h2⟩
      match ps, h1 with
      | p :: ps, h1 =>
        exact .cons (h2 p List.mem_cons_self)
          (picks_replicate.mpr ⟨by simpa using h1, fun q hq => h2 q (List.mem_cons_of_mem _ hq)⟩)

/-- A list as long as a list with no repeats is the list's image under some function. -/
theorem exists_map_eq {α β : Type} [DecidableEq α] [Inhabited β] : ∀ {rows : List α} {ps : List β},
    rows.Nodup → ps.length = rows.length → ∃ f : α → β, rows.map f = ps
  | [], [], _, _ => ⟨fun _ => default, rfl⟩
  | r :: rows, p :: ps, hn, hl => by
    obtain ⟨f, hf⟩ := exists_map_eq (List.nodup_cons.mp hn).2 (by simpa using hl)
    refine ⟨fun t => if t = r then p else f t, ?_⟩
    simp only [List.map_cons, ite_true, List.cons.injEq, true_and]
    rw [← hf]
    exact List.map_congr_left fun t ht => by
      have : t ≠ r := fun e => (List.nodup_cons.mp hn).1 (e ▸ ht)
      simp [this]

theorem zip_map_merge {f : Tuple → Tuple} : ∀ (rows : List Tuple),
    ((rows.zip (rows.map f)).map fun (t, p) => t.merge p) = rows.map fun t => t.merge (f t)
  | [] => rfl
  | r :: rows => by simp only [List.map_cons, List.zip_cons_cons, zip_map_merge rows]

theorem Finrel.nodup_tuples (r : Finrel) : r.tuples.Nodup := by
  unfold Finrel.tuples
  induction r.body using Quotient.ind with
  | _ l => exact ((List.mergeSort_perm _ _).nodup_iff).mpr (nodup_dedup l)

/-- **The candidates of ω_sol(D, X) are the graphs of the total functions from the
tuples of D to the tuples of X.** -/
theorem mem_omegaSolCandidates {h : Heading} {rows picks : List Tuple} (hn : rows.Nodup)
    (c : Finrel) : c ∈ omegaSolCandidates h rows picks ↔
      ∃ f : Tuple → Tuple, (∀ t ∈ rows, f t ∈ picks) ∧ c = graph h rows f := by
  unfold omegaSolCandidates
  rw [List.mem_map]
  constructor
  · rintro ⟨ps, hps, rfl⟩
    obtain ⟨hl, hm⟩ := picks_replicate.mp (mem_choices.mp hps)
    obtain ⟨f, rfl⟩ := exists_map_eq hn hl
    exact ⟨f, fun t ht => hm _ (List.mem_map_of_mem ht), by rw [zip_map_merge]; rfl⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨rows.map f, mem_choices.mpr (picks_replicate.mpr ⟨by simp, ?_⟩), ?_⟩
    · intro p hp
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
      exact hf t ht
    · rw [zip_map_merge]; rfl

/-- There are |X|^|D| candidates in the list. -/
theorem length_omegaSolCandidates (h : Heading) (rows picks : List Tuple) :
    (omegaSolCandidates h rows picks).length = picks.length ^ rows.length := by
  unfold omegaSolCandidates
  rw [List.length_map, length_choices, List.map_map]
  induction rows with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, Function.comp, List.foldr_cons] at *; rw [ih, List.length_cons, Nat.pow_succ, Nat.mul_comm]

theorem mem_graph {h : Heading} {rows : List Tuple} {f : Tuple → Tuple} (m : Tuple) :
    m ∈ (graph h rows f).tuples ↔ ∃ t ∈ rows, m = t.merge (f t) := by
  unfold graph
  rw [Finrel.mem_ofTuples, List.mem_map]
  exact ⟨fun ⟨t, ht, e⟩ => ⟨t, ht, e.symm⟩, fun ⟨t, ht, e⟩ => ⟨t, ht, e.symm⟩⟩

/-- **A graph determines its function.** Two functions with the same graph agree on
every data tuple. The hypotheses are well-formedness: data tuples over the data
attributes `D`, decisions over the decision attributes `X`, and no attribute in both
(ω_sol refuses a heading where an attribute is in both). -/
theorem graph_inj {h : Heading} {D X : List String} (hdx : ∀ a ∈ D, a ∉ X)
    {rows : List Tuple} (hrows : ∀ t ∈ rows, Tuple.Over D t) {f g : Tuple → Tuple}
    (hf : ∀ t ∈ rows, Tuple.Over X (f t)) (hg : ∀ t ∈ rows, Tuple.Over X (g t))
    (e : graph h rows f = graph h rows g) : ∀ t ∈ rows, f t = g t := by
  intro t ht
  have hm : t.merge (f t) ∈ (graph h rows g).tuples := by
    rw [← e, mem_graph]; exact ⟨t, ht, rfl⟩
  obtain ⟨t', ht', e'⟩ := (mem_graph _).mp hm
  obtain ⟨rfl, hfg⟩ := Tuple.merge_inj hdx (hrows t ht) (hrows t' ht') (hf t ht) (hg t' ht') e'
  exact hfg

theorem nodup_map_on {α β : Type} {f : α → β} : ∀ {l : List α},
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hi, hn => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_on (fun x hx y hy => hi x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy)) (List.nodup_cons.mp hn).2⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hm
    exact (List.nodup_cons.mp hn).1
      (hi a List.mem_cons_self b (List.mem_cons_of_mem _ hb) e.symm ▸ hb)

theorem nodup_choices {α : Type} : ∀ {xss : List (List α)},
    (∀ xs ∈ xss, xs.Nodup) → (choices xss).Nodup
  | [], _ => by simp [choices]
  | xs :: xss, hn => by
    have hrest := nodup_choices fun ys hy => hn ys (List.mem_cons_of_mem _ hy)
    have hxs := hn xs List.mem_cons_self
    simp only [choices]
    clear hn
    induction xs with
    | nil => exact List.nodup_nil
    | cons x xs ih =>
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨nodup_map_on (fun a _ b _ e => List.cons.inj e |>.2) hrest,
        ih (List.nodup_cons.mp hxs).2, ?_⟩
      intro a ha b hb e
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, hb⟩ := List.mem_flatMap.mp hb
      obtain ⟨l', -, rfl⟩ := List.mem_map.mp hb
      cases e
      exact (List.nodup_cons.mp hxs).1 hy

/-- **Each function once.** When the data and the decision tuples are well formed and
listed without repeats, no candidate is listed twice: the list holds exactly the
|X|^|D| graphs. -/
theorem nodup_omegaSolCandidates {h : Heading} {D X : List String} (hdx : ∀ a ∈ D, a ∉ X)
    {rows picks : List Tuple} (hn : rows.Nodup) (hp : picks.Nodup)
    (hrows : ∀ t ∈ rows, Tuple.Over D t) (hpicks : ∀ p ∈ picks, Tuple.Over X p) :
    (omegaSolCandidates h rows picks).Nodup := by
  unfold omegaSolCandidates
  refine nodup_map_on ?_ (nodup_choices ?_)
  · intro ps hps qs hqs e
    obtain ⟨hl, hm⟩ := picks_replicate.mp (mem_choices.mp hps)
    obtain ⟨hl', hm'⟩ := picks_replicate.mp (mem_choices.mp hqs)
    obtain ⟨f, rfl⟩ := exists_map_eq hn hl
    obtain ⟨g, rfl⟩ := exists_map_eq hn hl'
    rw [zip_map_merge, zip_map_merge] at e
    exact List.map_congr_left (graph_inj (h := h) hdx hrows
      (fun t ht => hpicks _ (hm _ (List.mem_map_of_mem ht)))
      (fun t ht => hpicks _ (hm' _ (List.mem_map_of_mem ht))) e)
  · intro xs hxs
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hxs
    exact hp

/-! ## σ_sol: a condition picks a subset -/

/-- **The set meaning of a solution set**: the graphs of the total functions from the
data's tuples (`rows`) to the decision tuples (`picks`) that pass every condition in
`conds`. ω_sol gives it with no conditions; each σ_sol adds one. -/
def SolMeaning (h : Heading) (rows picks : List Tuple)
    (conds : List (Finrel → Except String Bool)) (c : Finrel) : Prop :=
  (∃ f : Tuple → Tuple, (∀ t ∈ rows, f t ∈ picks) ∧ c = graph h rows f) ∧
    ∀ p ∈ conds, p c = .ok true

theorem omegaSolCandidates_meaning {h : Heading} {rows picks : List Tuple} (hn : rows.Nodup)
    (c : Finrel) : c ∈ omegaSolCandidates h rows picks ↔ SolMeaning h rows picks [] c := by
  simp [SolMeaning, mem_omegaSolCandidates hn]

/-- σ_sol keeps the candidates that pass its condition (`p`, the condition evaluated
with the candidate bound, as in the `sigmaSol` case of `Expr.eval`). If the candidates
had the set meaning with conditions `conds`, the result has it with `p` added. -/
theorem sigmaSol_meaning {h : Heading} {rows picks : List Tuple}
    {conds : List (Finrel → Except String Bool)} {p : Finrel → Except String Bool}
    {cands res : List Finrel} (hc : ∀ c, c ∈ cands ↔ SolMeaning h rows picks conds c)
    (hr : cands.filterM p = .ok res) (c : Finrel) :
    c ∈ res ↔ SolMeaning h rows picks (p :: conds) c := by
  rw [mem_filterM hr, hc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun q hq => (List.mem_cons.mp hq).elim (fun e => e ▸ h3) (h2 q)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun q hq => h2 q (List.mem_cons_of_mem _ hq)⟩, h2 p List.mem_cons_self⟩

/-- **Independent of candidate order.** σ_sol on two candidate lists with the same
members (in any order, with any repeats) is refused for both or neither, and otherwise
keeps the same candidates. Inside a candidate there is no order to see: a `Finrel`'s
body is a quotient. -/
theorem sigmaSol_order {p : Finrel → Except String Bool} {cands cands' res : List Finrel}
    (hl : ∀ c, c ∈ cands ↔ c ∈ cands') (hr : cands.filterM p = .ok res) :
    ∃ res', cands'.filterM p = .ok res' ∧ ∀ c, c ∈ res ↔ c ∈ res' :=
  filterM_sameMembers hl hr

/-! ## ω_msol and σ_msol: multi solution sets as sets of databases -/

/-- `CandOf sols db`: the database `db` binds each member's name, in order, to one of
that member's candidates. -/
inductive CandOf : List (String × Sol) → Db → Prop
  | nil : CandOf [] []
  | cons {n : String} {s : Sol} {r : Finrel} {sols : List (String × Sol)} {db : Db} :
      r ∈ s.candidates → CandOf sols db → CandOf ((n, s) :: sols) ((n, r) :: db)

/-- The databases ω_msol builds before its condition: word for word the expression in
the `omegaMsol` case of `Expr.eval`. -/
def omegaMsolDbs (sols : List (String × Sol)) : List Db :=
  choices (sols.map fun (n, s) => s.candidates.map (n, ·))

theorem picks_candOf : ∀ {sols : List (String × Sol)} {db : Db},
    Picks db (sols.map fun (n, s) => s.candidates.map (n, ·)) ↔ CandOf sols db
  | [], db => by
    simp only [List.map_nil]
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; exact .nil
  | (n, s) :: sols, db => by
    simp only [List.map_cons]
    constructor
    · intro h
      cases h with
      | cons hx hp =>
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
        exact .cons hr (picks_candOf.mp hp)
    · intro h
      cases h with
      | cons hr hc => exact .cons (List.mem_map_of_mem hr) (picks_candOf.mpr hc)

/-- ω_msol's databases are exactly the ways to pick one candidate per member. -/
theorem mem_omegaMsolDbs {sols : List (String × Sol)} (db : Db) :
    db ∈ omegaMsolDbs sols ↔ CandOf sols db := by
  unfold omegaMsolDbs; rw [mem_choices, picks_candOf]

/-- There are as many as the product of the members' candidate counts. -/
theorem length_omegaMsolDbs (sols : List (String × Sol)) :
    (omegaMsolDbs sols).length = (sols.map fun ns => ns.2.candidates.length).foldr (· * ·) 1 := by
  unfold omegaMsolDbs
  rw [length_choices, List.map_map]
  congr 1
  exact List.map_congr_left fun ⟨n, s⟩ _ => by simp

theorem CandOf.names {sols : List (String × Sol)} {db : Db} (h : CandOf sols db) :
    db.map (·.1) = sols.map (·.1) := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- In a candidate database, each member's name looks up one of that member's
candidates (member names are distinct, which ω_msol's forms have). -/
theorem CandOf.lookup {sols : List (String × Sol)} {db : Db} (h : CandOf sols db)
    (hn : (sols.map (·.1)).Nodup) {n : String} {s : Sol} (hs : (n, s) ∈ sols) :
    ∃ r ∈ s.candidates, db.lookup n = some r := by
  induction h with
  | nil => cases hs
  | @cons m s' r sols db hr _ ih =>
    rcases List.mem_cons.mp hs with e | e
    · cases e; exact ⟨r, hr, by simp [List.lookup]⟩
    · have hnm : n ≠ m := fun e' =>
        (List.nodup_cons.mp hn).1 (e' ▸ List.mem_map_of_mem (f := (·.1)) e)
      obtain ⟨r', hr', hl⟩ := ih (List.nodup_cons.mp hn).2 e
      have : (n == m) = false := by simpa using hnm
      exact ⟨r', hr', by simp [List.lookup, this, hl]⟩

/-- **The set meaning of a multi solution set**: the databases that bind each
member's name to one of that member's candidates and pass every condition. A database
"is in" the multi solution set exactly when this holds. -/
def MsolMeaning (sols : List (String × Sol)) (conds : List (Db → Except String Bool))
    (db : Db) : Prop :=
  CandOf sols db ∧ ∀ p ∈ conds, p db = .ok true

/-- ω_msol with a condition `p` (evaluated with the database bound, as in `Expr.eval`). -/
theorem omegaMsol_meaning {sols : List (String × Sol)} {p : Db → Except String Bool}
    {res : List Db} (hr : (omegaMsolDbs sols).filterM p = .ok res) (db : Db) :
    db ∈ res ↔ MsolMeaning sols [p] db := by
  rw [mem_filterM hr, mem_omegaMsolDbs]
  simp [MsolMeaning]

/-- ω_msol with no condition. -/
theorem omegaMsol_meaning_none {sols : List (String × Sol)} (db : Db) :
    db ∈ omegaMsolDbs sols ↔ MsolMeaning sols [] db := by
  simp [MsolMeaning, mem_omegaMsolDbs]

/-- σ_msol adds its condition to the set meaning. -/
theorem sigmaMsol_meaning {sols : List (String × Sol)} {conds : List (Db → Except String Bool)}
    {p : Db → Except String Bool} {dbs res : List Db}
    (hc : ∀ db, db ∈ dbs ↔ MsolMeaning sols conds db) (hr : dbs.filterM p = .ok res)
    (db : Db) : db ∈ res ↔ MsolMeaning sols (p :: conds) db := by
  rw [mem_filterM hr, hc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun q hq => (List.mem_cons.mp hq).elim (fun e => e ▸ h3) (h2 q)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun q hq => h2 q (List.mem_cons_of_mem _ hq)⟩, h2 p List.mem_cons_self⟩

/-- σ_msol, like σ_sol, sees only which databases there are, not their order. -/
theorem sigmaMsol_order {p : Db → Except String Bool} {dbs dbs' res : List Db}
    (hl : ∀ db, db ∈ dbs ↔ db ∈ dbs') (hr : dbs.filterM p = .ok res) :
    ∃ res', dbs'.filterM p = .ok res' ∧ ∀ db, db ∈ res ↔ db ∈ res' :=
  filterM_sameMembers hl hr

end Rasso
