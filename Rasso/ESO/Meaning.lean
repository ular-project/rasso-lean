import Rasso.ESO.Guesses

/-!
# ESO: what the formula translation means

In an environment where each second-order variable names its guess (`GuessEnv`), the
translation of a first-order formula `φ` evaluates to the relation of the assignments that
satisfy `φ`: one attribute `x_x` per free variable `x`, and a tuple for each assignment of
elements that makes `φ` true. This is Codd's theorem for the construction, proved formula by
formula.
-/

namespace Rasso.ESO

open Rasso

set_option linter.unusedSimpArgs false

/-! ## Relations of assignments -/

/-- `Q` depends only on the variables `xs`. -/
def Dep (xs : List String) (Q : (String → Value) → Prop) : Prop :=
  ∀ ρ ρ', (∀ x ∈ xs, ρ x = ρ' x) → (Q ρ ↔ Q ρ')

/-- `r` is the relation of the assignments to `xs` (as `x_…` attributes, each over the
universe) that satisfy `Q`. -/
abbrev RepV (A : Str) (xs : List String) (Q : (String → Value) → Prop) (r : Finrel) : Prop :=
  Rep (VH A xs) (fun t => Q (asg t)) r

theorem varAttr_inj {x y : String} (h : varAttr x = varAttr y) : x = y :=
  (String.append_right_inj "x_").mp h

theorem lookup_map_pair {β : Type} (f : String → String) (D : β) :
    ∀ (xs : List String) (a : String),
      (xs.map fun x => (f x, D)).lookup a = if a ∈ xs.map f then some D else none
  | [], a => by simp [List.lookup]
  | x :: xs, a => by
    simp only [List.map_cons, List.lookup, List.mem_cons]
    by_cases h : a = f x
    · subst h; simp
    · have hne : (a == f x) = false := by simpa using h
      rw [hne, lookup_map_pair f D xs a]
      by_cases h' : a ∈ xs.map f
      · rw [ite_eq_left h', ite_eq_left (Or.inr h')]
      · rw [ite_eq_right h', ite_eq_right (fun h'' => h''.elim h h')]

theorem lookup_VH (A : Str) (xs : List String) (a : String) :
    (VH A xs).lookup a = if a ∈ xs.map varAttr then some (DD A) else none :=
  lookup_map_pair varAttr (DD A) xs a

theorem VH_attrs (A : Str) (xs : List String) : (VH A xs).attrs = xs.map varAttr := by
  simp [VH, Heading.attrs, List.map_map]

theorem VH_congr (A : Str) {xs ys : List String} (h : ∀ x, x ∈ xs ↔ x ∈ ys) (a : String) :
    (VH A xs).lookup a = (VH A ys).lookup a := by
  rw [lookup_VH, lookup_VH]
  have : a ∈ xs.map varAttr ↔ a ∈ ys.map varAttr := by
    simp only [List.mem_map]
    exact ⟨fun ⟨x, hx, e⟩ => ⟨x, (h x).mp hx, e⟩, fun ⟨x, hx, e⟩ => ⟨x, (h x).mpr hx, e⟩⟩
  by_cases ha : a ∈ xs.map varAttr
  · rw [ite_eq_left ha, ite_eq_left (this.mp ha)]
  · rw [ite_eq_right ha, ite_eq_right (fun h' => ha (this.mpr h'))]

theorem _root_.Rasso.Rep.congrH {H H' : Heading} {P P' : Tuple → Prop} {r : Finrel} (hr : Rep H P r)
    (e : ∀ a, H.lookup a = H'.lookup a) (hp : ∀ t, t.Fits H' → (P t ↔ P' t)) : Rep H' P' r where
  wf := hr.wf
  head a := (hr.head a).trans (e a)
  mem t := by
    rw [hr.mem, fits_congr e]
    exact ⟨fun ⟨f, h⟩ => ⟨f, (hp t f).mp h⟩, fun ⟨f, h⟩ => ⟨f, (hp t f).mpr h⟩⟩

theorem RepV.congr {A : Str} {xs ys : List String} {Q Q' : (String → Value) → Prop} {r : Finrel}
    (hr : RepV A xs Q r) (hm : ∀ x, x ∈ xs ↔ x ∈ ys) (hq : ∀ t, t.Fits (VH A ys) → (Q (asg t) ↔ Q' (asg t))) :
    RepV A ys Q' r :=
  hr.congrH (VH_congr A hm) hq

/-- The value a fitting tuple gives a variable is there, and is an element. -/
theorem fits_var {A : Str} {xs : List String} {t : Tuple} (f : t.Fits (VH A xs)) {x : String}
    (hx : x ∈ xs) : t.get? (varAttr x) = some (asg t x) ∧ asg t x ∈ A.univ := by
  have hin : varAttr x ∈ (VH A xs).attrs := by rw [VH_attrs]; exact List.mem_map_of_mem hx
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((f.get?_isSome _).mpr hin)
  have hasg : asg t x = v := by simp [asg, hv]
  refine ⟨by rw [hv, hasg], ?_⟩
  rw [hasg, ← DD_mem]
  apply f.dom (varAttr x, v) (lookup_mem_val hv)
  rw [lookup_VH, ite_eq_left (by exact List.mem_map_of_mem hx)]

theorem asg_restrict {xs : List String} {t : Tuple} {x : String} (hx : x ∈ xs) :
    asg (t.restrict (xs.map varAttr)) x = asg t x := by
  simp only [asg]
  rw [get?_restrict, ite_eq_left (List.mem_map_of_mem hx)]

/-! ## ⋈, ∪ and − on relations of assignments -/

theorem repV_join {A : Str} {xs ys : List String} {Q Q' : (String → Value) → Prop} {r s : Finrel}
    (hr : RepV A xs Q r) (hs : RepV A ys Q' s) (hQ : Dep xs Q) (hQ' : Dep ys Q') :
    ∃ q, r.join s = .ok q ∧ RepV A (xs ++ ys) (fun ρ => Q ρ ∧ Q' ρ) q := by
  obtain ⟨q, hq, hrep⟩ := rep_join hr hs fun a d e hd he => by
    rw [lookup_VH] at hd he
    split at hd <;> split at he <;> simp_all
  refine ⟨q, hq, hrep.congrH (fun a => ?_) fun t _ => ?_⟩
  · rw [lookup_joinH, lookup_VH, lookup_VH, lookup_VH, List.map_append]
    by_cases h1 : a ∈ xs.map varAttr
    · rw [ite_eq_left h1, ite_eq_left (List.mem_append_left _ h1)]; rfl
    · rw [ite_eq_right h1]
      by_cases h2 : a ∈ ys.map varAttr
      · rw [ite_eq_left h2, ite_eq_left (List.mem_append_right _ h2)]; rfl
      · rw [ite_eq_right h2, ite_eq_right (fun h => (List.mem_append.mp h).elim h1 h2)]; rfl
  · rw [VH_attrs, VH_attrs]
    exact and_congr (hQ _ _ fun x hx => asg_restrict hx) (hQ' _ _ fun x hx => asg_restrict hx)

theorem repV_union {A : Str} {xs : List String} {Q Q' : (String → Value) → Prop} {r s : Finrel}
    (hr : RepV A xs Q r) (hs : RepV A xs Q' s) :
    ∃ q, r.union s = .ok q ∧ RepV A xs (fun ρ => Q ρ ∨ Q' ρ) q :=
  rep_union hr hs

theorem repV_diff {A : Str} {xs : List String} {Q Q' : (String → Value) → Prop} {r s : Finrel}
    (hr : RepV A xs Q r) (hs : RepV A xs Q' s) :
    ∃ q, r.diff s = .ok q ∧ RepV A xs (fun ρ => Q ρ ∧ ¬ Q' ρ) q :=
  rep_diff hr hs

theorem Dep.mono {xs ys : List String} {Q : (String → Value) → Prop} (h : Dep xs Q)
    (hs : ∀ x ∈ xs, x ∈ ys) : Dep ys Q :=
  fun ρ ρ' e => h ρ ρ' fun x hx => e x (hs x hx)

/-! ## σ with an equality, U^xs, and ∃ as π -/

theorem comparable_pair {A : Str} (hC : A.Comparable) {v w : Value} (hv : v ∈ A.univ)
    (hw : w ∈ A.univ) :
    ¬ (v.isExact = true ∧ w.isFloat = true) ∧ ¬ (v.isFloat = true ∧ w.isExact = true) ∧
      ¬ (v.isSymbol = true ∧ w.isString = true) ∧ ¬ (v.isString = true ∧ w.isSymbol = true) :=
  ⟨(hC v hv w hw).1, fun h => (hC w hw v hv).1 ⟨h.2, h.1⟩,
    (hC v hv w hw).2, fun h => (hC w hw v hv).2 ⟨h.2, h.1⟩⟩

theorem repV_select_eq {A : Str} (hC : A.Comparable) {xs : List String}
    {Q : (String → Value) → Prop} {r : Finrel} {x y : String} (hr : RepV A xs Q r)
    (hx : x ∈ xs) (hy : y ∈ xs) :
    ∃ s, r.select (eqT (varAttr x) (varAttr y)).holds = .ok s ∧
      RepV A xs (fun ρ => Q ρ ∧ ρ x = ρ y) s := by
  have key : ∀ t, t.Fits (VH A xs) →
      Term.holds t (eqT (varAttr x) (varAttr y)) = .ok (decide (asg t x = asg t y)) := by
    intro t f
    obtain ⟨gx, ux⟩ := fits_var f hx
    obtain ⟨gy, uy⟩ := fits_var f hy
    exact holds_eqT gx gy (comparable_pair hC ux uy)
  obtain ⟨s, hs⟩ := select_succeeds (p := (eqT (varAttr x) (varAttr y)).holds)
    fun t ht => ⟨_, key t (hr.mem_fits ht)⟩
  refine ⟨s, hs, (rep_select hr hs).congrH (fun _ => rfl) fun t f => ?_⟩
  rw [key t f]
  simp

theorem repV_domOf (A : Str) (env : Env) {xs : List String} (hn : xs.Nodup) :
    ∃ r, Expr.eval env [] (domOfP (univLit A) xs) = .ok (.finrel r) ∧ RepV A xs (fun _ => True) r :=
  eval_univPow A env (nodup_vars_map hn)

theorem fits_cons {A : Str} {zs ys : List String} {x : String} {a : Value} {t : Tuple}
    (f : t.Fits (VH A zs)) (hxz : x ∉ zs) (hys : ∀ y, y ∈ ys ↔ y = x ∨ y ∈ zs)
    (ha : a ∈ A.univ) :
    (Tuple.ofPairs ((varAttr x, a) :: t)).Fits (VH A ys) ∧
      ∀ b, (Tuple.ofPairs ((varAttr x, a) :: t)).get? b = ((varAttr x, a) :: t).lookup b := by
  have hnot : varAttr x ∉ t.attrs := by
    intro h
    rw [f.attrs, VH_attrs] at h
    obtain ⟨z, hz, e⟩ := List.mem_map.mp h
    exact hxz (varAttr_inj e ▸ hz)
  have hn : (((varAttr x, a) :: t).map (·.1)).Nodup := by
    rw [List.map_cons, List.nodup_cons]
    exact ⟨hnot, f.nodup⟩
  have hp := List.mergeSort_perm ((varAttr x, a) :: t) fun p q => decide (p.1 ≤ q.1)
  have hget := Tuple.get?_ofPairs hn
  refine ⟨⟨Tuple.sorted_ofPairs hn, fun b => ?_, fun p hp' d hd => ?_⟩, hget⟩
  · rw [VH_attrs]
    have : b ∈ (Tuple.ofPairs ((varAttr x, a) :: t)).attrs ↔ b ∈ ((varAttr x, a) :: t).map (·.1) :=
      (hp.map (·.1)).mem_iff
    rw [this, List.map_cons, List.mem_cons]
    show b = varAttr x ∨ b ∈ t.attrs ↔ _
    rw [f.attrs, VH_attrs, List.mem_map, List.mem_map]
    constructor
    · rintro (rfl | ⟨z, hz, rfl⟩)
      · exact ⟨x, (hys x).mpr (Or.inl rfl), rfl⟩
      · exact ⟨z, (hys z).mpr (Or.inr hz), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rcases (hys y).mp hy with rfl | hz
      · exact Or.inl rfl
      · exact Or.inr ⟨y, hz, rfl⟩
  · have hm : p ∈ (varAttr x, a) :: t := hp.mem_iff.mp hp'
    rw [lookup_VH] at hd
    split at hd
    · cases hd
      rcases List.mem_cons.mp hm with rfl | hm
      · exact (DD_mem A a).mpr ha
      · exact f.dom p hm (DD A) (by
          rw [lookup_VH, ite_eq_left (by rw [← VH_attrs]; exact (f.attrs p.1).mp (List.mem_map_of_mem hm))])
    · cases hd

theorem repV_exists {A : Str} {ys zs : List String} {x : String} {Q : (String → Value) → Prop}
    {r : Finrel} (hr : RepV A ys Q r) (hz : ∀ z, z ∈ zs ↔ z ∈ ys ∧ z ≠ x) (hx : x ∈ ys)
    (hzn : zs.Nodup) (hQ : Dep ys Q) :
    ∃ s, r.project (zs.map varAttr) = .ok s ∧
      RepV A zs (fun ρ => ∃ a ∈ A.univ, Q (upd ρ x a)) s := by
  obtain ⟨s, hs, hrep⟩ := rep_project hr
    (fun a ha => by
      obtain ⟨z, hz', rfl⟩ := List.mem_map.mp ha
      rw [VH_attrs]; exact List.mem_map_of_mem ((hz z).mp hz').1)
    (nodup_vars_map hzn)
  refine ⟨s, hs, hrep.congrH (fun a => ?_) fun t ft => ?_⟩
  · rw [lookup_restrictH, lookup_VH, lookup_VH]
    by_cases ha : a ∈ zs.map varAttr
    · rw [ite_eq_left ha, ite_eq_left ha]
      obtain ⟨z, hz', rfl⟩ := List.mem_map.mp ha
      rw [ite_eq_left (List.mem_map_of_mem ((hz z).mp hz').1)]
    · rw [ite_eq_right ha, ite_eq_right ha]
  · constructor
    · rintro ⟨u, fu, hq, rfl⟩
      obtain ⟨_, ua⟩ := fits_var fu hx
      refine ⟨asg u x, ua, (hQ _ _ fun y hy => ?_).mpr hq⟩
      by_cases hyx : y = x
      · subst hyx; rw [upd_same]
      · rw [upd_other hyx, asg_restrict ((hz y).mpr ⟨hy, hyx⟩)]
    · rintro ⟨a, ha, hq⟩
      have hxz : x ∉ zs := fun h => ((hz x).mp h).2 rfl
      have hys : ∀ y, y ∈ ys ↔ y = x ∨ y ∈ zs := fun y => by
        rw [hz]
        by_cases hyx : y = x
        · subst hyx; exact ⟨fun _ => Or.inl rfl, fun _ => hx⟩
        · exact ⟨fun h => Or.inr ⟨h, hyx⟩, fun h => h.elim (fun e => absurd e hyx) (·.1)⟩
      obtain ⟨fu, hget⟩ := fits_cons ft hxz hys ha
      refine ⟨_, fu, (hQ _ _ fun y hy => ?_).mp hq, ?_⟩
      · by_cases hyx : y = x
        · subst hyx; rw [upd_same]; simp [asg, hget, List.lookup]
        · rw [upd_other hyx]
          have hne : (varAttr y == varAttr x) = false := by
            simpa using fun e => hyx (varAttr_inj e)
          simp only [asg, hget, List.lookup, hne]; rfl
      · refine Tuple.ext_get? (sorted_restrict fu.sorted) ft.sorted fun b => ?_
        rw [get?_restrict, hget]
        by_cases hb : b ∈ zs.map varAttr
        · rw [ite_eq_left hb]
          have hne : (b == varAttr x) = false := by
            obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hb
            simpa using fun e => hxz (by rw [← varAttr_inj e]; exact hz')
          simp only [List.lookup, hne]; rfl
        · rw [ite_eq_right hb, ft.get?_none (by rw [VH_attrs]; exact hb)]

/-! ## The formula's variables -/

theorem nodup_eraseDups' : ∀ l : List String, l.eraseDups.Nodup
  | [] => List.nodup_nil
  | a :: as => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨fun h => ?_, nodup_eraseDups' _⟩
    rw [List.mem_eraseDups, List.mem_filter] at h
    simp at h
termination_by l => l.length
decreasing_by simp_wf; exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem mem_vars {φ : FO} {x : String} : x ∈ φ.vars ↔ x ∈ φ.fv := List.mem_eraseDups

theorem nodup_vars (φ : FO) : φ.vars.Nodup := nodup_eraseDups' _

theorem dep_sat (A : Str) (G : Guess) (φ : FO) : Dep φ.vars (φ.Sat A G) :=
  fun _ _ h => FO.Sat_congr φ fun x hx => h x (mem_vars.mpr hx)

theorem mem_append_filter {xs ys : List String} {x : String} :
    x ∈ xs ++ ys.filter (fun y => !xs.contains y) ↔ x ∈ xs ∨ x ∈ ys := by
  rw [List.mem_append, List.mem_filter]
  by_cases h : x ∈ xs
  · exact ⟨fun _ => Or.inl h, fun _ => Or.inl h⟩
  · have : (!xs.contains x) = true := by simpa using h
    exact ⟨fun h' => h'.elim Or.inl fun h'' => Or.inr h''.1,
      fun h' => h'.elim Or.inl fun h'' => Or.inr ⟨h'', this⟩⟩

/-- The variables padded with `x` when it is missing. -/
def withVar (xs : List String) (x : String) : List String := if xs.contains x then [] else [x]

theorem mem_withVar {xs : List String} {x z : String} : z ∈ xs ++ withVar xs x ↔ z ∈ xs ∨ z = x := by
  unfold withVar
  split
  · next h =>
    have hx : x ∈ xs := by simpa using h
    rw [List.append_nil]
    exact ⟨Or.inl, fun h' => h'.elim id fun e => e ▸ hx⟩
  · simp

theorem nodup_withVar {xs : List String} (_hn : xs.Nodup) (x : String) :
    (withVar xs x).Nodup := by
  unfold withVar; split <;> simp

/-- Join a relation of assignments with the universe for some more variables. -/
theorem repV_pad (A : Str) {env : Env} {e : Expr} {xs ys : List String}
    {Q : (String → Value) → Prop} {r : Finrel}
    (he : Expr.eval env [] e = .ok (.finrel r)) (hr : RepV A xs Q r) (hQ : Dep xs Q)
    (hys : ys.Nodup) :
    ∃ s, Expr.eval env [] (padP (univLit A) e ys) = .ok (.finrel s) ∧ RepV A (xs ++ ys) Q s := by
  unfold padP
  split
  · next h =>
    rw [List.isEmpty_iff] at h; subst h
    exact ⟨r, he, by simpa using hr⟩
  · obtain ⟨d, hd, hdr⟩ := repV_domOf A env hys
    obtain ⟨q, hq, hrep⟩ := repV_join hr hdr hQ (fun _ _ _ => Iff.rfl)
    exact ⟨q, eval_join2 he hd hq, hrep.congr (fun _ => Iff.rfl) fun t _ => ⟨And.left, fun h => ⟨h, trivial⟩⟩⟩

/-! ## Atoms -/

theorem colAttr_ne_varAttr (m : Nat) (x : String) : colAttr m ≠ varAttr x := by
  intro h
  have := congrArg String.toList h
  simp [colAttr, varAttr] at this
  have e : (toString "c").toList = ['c'] := by decide
  rw [e] at this
  simp at this

theorem holds_ne_varAttr (x : String) : holdsAttr ≠ varAttr x := by
  intro h
  have := congrArg String.toList h
  simp [holdsAttr, varAttr] at this

theorem holds_ne_colAttr (m : Nat) : holdsAttr ≠ colAttr m := by
  intro h
  have := congrArg String.toList h
  simp [holdsAttr, colAttr] at this
  have e : (toString "c").toList = ['c'] := by decide
  rw [e] at this
  simp at this

theorem mem_cols {c : String} {n : Nat} (h : c ∈ cols n) : ∃ m, c = colAttr m := by
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp h; exact ⟨m, rfl⟩

/-- Pairs with names all different make a tuple that fits a heading with the same names,
when each value is in its domain. -/
theorem fits_ofPairs {H : Heading} {ps : List (String × Value)} (hn : (ps.map (·.1)).Nodup)
    (ha : ∀ a, a ∈ ps.map (·.1) ↔ a ∈ H.attrs)
    (hd : ∀ p ∈ ps, ∀ d, H.lookup p.1 = some d → d.mem p.2 = true) :
    (Tuple.ofPairs ps).Fits H where
  sorted := Tuple.sorted_ofPairs hn
  attrs a := by
    have hp := List.mergeSort_perm ps fun p q => decide (p.1 ≤ q.1)
    rw [← ha]; exact (hp.map (·.1)).mem_iff
  dom p hp d hd' := hd p ((List.mergeSort_perm ps _).mem_iff.mp hp) d hd'

theorem lookup_zip_map' : ∀ {cs : List String} {vs : List Value}, cs.Nodup → cs.length = vs.length →
    ∀ rest : List (String × Value), cs.map (fun c => ((cs.zip vs ++ rest).lookup c).getD default) = vs
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by cases h
  | _ :: _, [], _, h, _ => by cases h
  | c :: cs, v :: vs, hn, hl, rest => by
    have ⟨hc, hn'⟩ := List.nodup_cons.mp hn
    simp only [List.zip_cons_cons, List.cons_append, List.map_cons, lookup_cons_self, Option.getD_some]
    congr 1
    refine (List.map_congr_left fun c' hc' => ?_).trans (lookup_zip_map' hn' (vs := vs) (by simpa using hl) rest)
    rw [lookup_cons_ne (fun (e : c' = c) => hc (e ▸ hc'))]

theorem zip_eq_map {β γ : Type} {f : String → γ} {g : β → γ} :
    ∀ {cs : List String} {as : List β}, cs.length = as.length →
      ((∀ p ∈ cs.zip as, f p.1 = g p.2) ↔ cs.map f = as.map g)
  | [], [], _ => by simp
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | c :: cs, a :: as, h => by
    simp only [List.zip_cons_cons, List.mem_cons, List.map_cons, List.cons.injEq]
    rw [← zip_eq_map (by simpa using h)]
    constructor
    · intro h'; exact ⟨h' _ (Or.inl rfl), fun p hp => h' p (Or.inr hp)⟩
    · rintro ⟨h1, h2⟩ p (rfl | hp)
      · exact h1
      · exact h2 p hp

theorem conj_true {t : Tuple} {ts : List Term} (hok : ∀ e ∈ ts, ∃ b, Term.holds t e = .ok b) :
    (∃ b, Term.holds t (conj ts) = .ok b) ∧
      (Term.holds t (conj ts) = .ok true ↔ ∀ e ∈ ts, Term.holds t e = .ok true) := by
  let p : Term → Bool := fun e => match Term.holds t e with | .ok b => b | .error _ => false
  have hp : ∀ e ∈ ts, Term.holds t e = .ok (p e) := fun e he => by
    obtain ⟨b, hb⟩ := hok e he; simp only [p, hb]
  rw [holds_conj hp]
  refine ⟨⟨_, rfl⟩, ?_⟩
  constructor
  · intro h e he
    have h' : ts.all p = true := by injection h
    rw [hp e he, List.all_eq_true.mp h' e he]
  · intro h
    have : ts.all p = true := List.all_eq_true.mpr fun e he => by
      have := (hp e he).symm.trans (h e he); injection this
    rw [this]

theorem rowOf_restrict' {cs as : List String} {u : Tuple} (h : ∀ c ∈ cs, c ∈ as) :
    rowOf cs (u.restrict as) = rowOf cs u :=
  List.map_congr_left fun c hc => by rw [get?_restrict, ite_eq_left (h c hc)]

theorem args_restrict {args xs : List String} {u : Tuple} (h : ∀ x ∈ args, x ∈ xs) :
    args.map (asg (u.restrict (xs.map varAttr))) = args.map (asg u) :=
  List.map_congr_left fun x hx => asg_restrict (h x hx)

/-- A value a fitting tuple gives an attribute over the universe is there, and is an element. -/
theorem fits_get {A : Str} {J : Heading} {u : Tuple} (f : u.Fits J) {a : String}
    (h : J.lookup a = some (DD A)) :
    u.get? a = some ((u.get? a).getD default) ∧ (u.get? a).getD default ∈ A.univ := by
  have hin : a ∈ J.attrs := Finrel.mem_attrs_iff.mpr (by rw [h]; rfl)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((f.get?_isSome _).mpr hin)
  rw [hv]
  exact ⟨rfl, (DD_mem A v).mp (f.dom (a, v) (lookup_mem_val hv) _ h)⟩

/-- An attribute a conjunction reads is read by one of its tests. -/
theorem attrs_conj {ts : List Term} {a : String} (h : a ∈ (conj ts).attrs) :
    ∃ e ∈ ts, a ∈ e.attrs := by
  match ts, h with
  | [], h => simp [conj, Term.attrs] at h
  | [t], h => exact ⟨t, List.mem_singleton_self t, h⟩
  | t :: u :: rest, h =>
    simp only [conj, Term.attrs, List.mem_flatMap] at h
    obtain ⟨e, he, ha⟩ := h
    exact ⟨e, he, ha⟩

/-- An atom: the base relation (a symbol's data, or a guess) joined with the universe for
the atom's variables, the tests, then the projection onto the variables. -/
theorem meaning_atom (A : Str) (hC : A.Comparable) {env : Env} {base : Expr} {H : Heading}
    {Pb : Tuple → Prop} {b : Finrel} (n : Nat) (extra : List Term) (Pe : Tuple → Prop)
    (R : List Value → Prop) (args : List String) (hlen : args.length = n)
    (hb : Expr.eval env [] base = .ok (.finrel b)) (hbr : Rep H Pb b)
    (hHx : ∀ a ∈ H.attrs, ∀ x, a ≠ varAttr x)
    (hcs : ∀ c ∈ cols n, H.lookup c = some (DD A))
    (hextA : ∀ e ∈ extra, ∀ a ∈ e.attrs, a ∈ H.attrs)
    (hext : ∀ u : Tuple, (u.restrict H.attrs).Fits H →
      (∀ e ∈ extra, ∃ bo, Term.holds u e = .ok bo) ∧
        ((∀ e ∈ extra, Term.holds u e = .ok true) ↔ Pe (u.restrict H.attrs)))
    (hR : ∀ b', b'.Fits H → Pb b' → Pe b' → R (rowOf (cols n) b'))
    (hR' : ∀ vs : List Value, vs.length = n → (∀ v ∈ vs, v ∈ A.univ) → R vs →
      ∃ b', b'.Fits H ∧ rowOf (cols n) b' = vs ∧ Pb b' ∧ Pe b') :
    ∃ r, Expr.eval env [] (atomP (univLit A) base (cols n) extra args) = .ok (.finrel r) ∧
      RepV A args.eraseDups (fun ρ => R (args.map ρ)) r := by
  have hxn : args.eraseDups.Nodup := nodup_eraseDups' args
  have hax : ∀ x ∈ args, x ∈ args.eraseDups := fun x hx => List.mem_eraseDups.mpr hx
  obtain ⟨d, hd, hdr⟩ := repV_domOf A env hxn
  have hHnone : ∀ x, H.lookup (varAttr x) = none := fun x => by
    cases h : H.lookup (varAttr x) with
    | none => rfl
    | some _ => exact absurd rfl (hHx _ (Finrel.mem_attrs_iff.mpr (by rw [h]; rfl)) x)
  obtain ⟨q, hq, hqr⟩ := rep_join hbr hdr fun a d e hd he => by
    exfalso
    rw [lookup_VH] at he
    split at he
    · next h =>
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp h
      rw [hHnone] at hd; cases hd
    · cases he
  -- the heading of the join
  have hJH : ∀ a d, H.lookup a = some d → (joinH H (VH A args.eraseDups)).lookup a = some d :=
    fun a d h => by rw [lookup_joinH, h]; rfl
  have hJx : ∀ x ∈ args.eraseDups, (joinH H (VH A args.eraseDups)).lookup (varAttr x) = some (DD A) :=
    fun x hx => by
      rw [lookup_joinH, hHnone, Option.none_or, lookup_VH, ite_eq_left (List.mem_map_of_mem hx)]
  -- the tests
  let ts := extra ++ ((cols n).zip args).map fun (c, x) => eqT c (varAttr x)
  have htests : ∀ u, u.Fits (joinH H (VH A args.eraseDups)) →
      (∃ bo, Term.holds u (conj ts) = .ok bo) ∧
      (Term.holds u (conj ts) = .ok true ↔
        Pe (u.restrict H.attrs) ∧ rowOf (cols n) u = args.map (asg u)) := by
    intro u fu
    have fH := fu.restrict hJH
    obtain ⟨hok1, hiff1⟩ := hext u fH
    have heq : ∀ p ∈ (cols n).zip args, Term.holds u (eqT p.1 (varAttr p.2)) =
        .ok (decide ((u.get? p.1).getD default = asg u p.2)) := by
      intro p hp
      have hc := hcs p.1 (List.of_mem_zip hp).1
      obtain ⟨g1, u1⟩ := fits_get fu (hJH _ _ hc)
      obtain ⟨g2, u2⟩ := fits_get fu (hJx p.2 (hax _ (List.of_mem_zip hp).2))
      exact holds_eqT g1 g2 (comparable_pair hC u1 u2)
    have hok : ∀ e ∈ ts, ∃ bo, Term.holds u e = .ok bo := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hok1 e he
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
        exact ⟨_, heq p hp⟩
    obtain ⟨hex, hiff⟩ := conj_true hok
    refine ⟨hex, hiff.trans ?_⟩
    rw [← hiff1]
    have hz : (∀ p ∈ (cols n).zip args, (u.get? p.1).getD default = asg u p.2) ↔
        rowOf (cols n) u = args.map (asg u) :=
      zip_eq_map (cs := cols n) (as := args) (f := fun c => (u.get? c).getD default) (g := asg u)
        (by simp [cols, hlen])
    rw [← hz]
    constructor
    · intro h
      refine ⟨fun e he => h e (List.mem_append_left _ he), fun p hp => ?_⟩
      have := h _ (List.mem_append_right _ (List.mem_map_of_mem (f := fun (c, x) => eqT c (varAttr x)) hp))
      rw [heq p hp] at this
      simpa using this
    · rintro ⟨h1, h2⟩ e he
      rcases List.mem_append.mp he with he | he
      · exact h1 e he
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
        rw [heq p hp]; simpa using h2 p hp
  obtain ⟨s, hs⟩ := select_succeeds (p := fun u => Term.holds u (conj ts))
    fun u hu => (htests u (hqr.mem_fits hu)).1
  have hsr := rep_select hqr hs
  obtain ⟨r, hr, hrr⟩ := rep_project hsr (as := args.eraseDups.map varAttr)
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact Finrel.mem_attrs_iff.mpr (by rw [hJx x hx]; rfl))
    (nodup_vars_map hxn)
  -- the tests read only attributes of the join
  have hscoped : ∀ a ∈ (conj ts).attrs, a ∈ q.heading.attrs := by
    intro a ha
    rw [attrs_congr hqr.head]
    obtain ⟨e, he, hae⟩ := attrs_conj ha
    rcases List.mem_append.mp he with he | he
    · obtain ⟨d, hd'⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp (hextA e he a hae))
      exact Finrel.mem_attrs_iff.mpr (by rw [hJH a d hd']; rfl)
    · obtain ⟨⟨c, x⟩, hp, rfl⟩ := List.mem_map.mp he
      simp only [eqT, Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append, List.mem_singleton] at hae
      rcases hae with rfl | rfl
      · exact Finrel.mem_attrs_iff.mpr (by rw [hJH _ _ (hcs _ (List.of_mem_zip hp).1)]; rfl)
      · exact Finrel.mem_attrs_iff.mpr (by rw [hJx x (hax _ (List.of_mem_zip hp).2)]; rfl)
  refine ⟨r, eval_project (eval_select (eval_join2 hb hd hq) hs hscoped) hr, hrr.congrH (fun a => ?_) fun t ft => ?_⟩
  · rw [lookup_restrictH, lookup_VH]
    split
    · next h => obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h; exact hJx x hx
    · rfl
  · have hcH : ∀ c ∈ cols n, c ∈ H.attrs := fun c hc =>
      Finrel.mem_attrs_iff.mpr (by rw [hcs c hc]; rfl)
    constructor
    · rintro ⟨u, fu, ⟨⟨hpb, _⟩, hτ⟩, rfl⟩
      obtain ⟨hpe, hrow⟩ := (htests u fu).2.mp hτ
      have := hR _ (fu.restrict hJH) hpb hpe
      rwa [rowOf_restrict' hcH, hrow, ← args_restrict hax] at this
    · intro hRt
      obtain ⟨b', fb, hrow, hpb, hpe⟩ := hR' (args.map (asg t)) (by simp [hlen])
        (fun v hv => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
          exact (fits_var ft (hax x hx)).2) hRt
      -- the joined tuple
      have hdisj : ∀ a, a ∈ b'.attrs → a ∉ t.attrs := fun a ha ha' => by
        rw [ft.attrs, VH_attrs] at ha'
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha'
        exact hHx _ ((fb.attrs _).mp ha) x rfl
      have hn : ((b' ++ t).map (·.1)).Nodup := by
        rw [List.map_append]
        exact List.nodup_append.mpr ⟨fb.nodup, ft.nodup, fun a ha a' ha' e => hdisj a ha (e ▸ ha')⟩
      have hget := Tuple.get?_ofPairs hn
      have fu : (Tuple.ofPairs (b' ++ t)).Fits (joinH H (VH A args.eraseDups)) := by
        refine fits_ofPairs hn (fun a => ?_) fun p hp d hd => ?_
        · rw [List.map_append, List.mem_append, Finrel.mem_attrs_iff, lookup_joinH]
          show a ∈ b'.attrs ∨ a ∈ t.attrs ↔ _
          rw [fb.attrs, ft.attrs, Finrel.mem_attrs_iff, Finrel.mem_attrs_iff]
          cases H.lookup a <;> simp
        · rw [lookup_joinH] at hd
          rcases List.mem_append.mp hp with hp | hp
          · have : p.1 ∈ H.attrs := (fb.attrs _).mp (List.mem_map_of_mem hp)
            obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp this)
            rw [hd'] at hd; cases hd
            exact fb.dom p hp _ hd'
          · have : p.1 ∈ (VH A args.eraseDups).attrs := (ft.attrs _).mp (List.mem_map_of_mem hp)
            rw [VH_attrs] at this
            obtain ⟨x, _, hx⟩ := List.mem_map.mp this
            have hnone : H.lookup p.1 = none := hx ▸ hHnone x
            rw [hnone, Option.none_or] at hd
            exact ft.dom _ hp _ hd
      have hgetb : ∀ a, (b' ++ t).lookup a = (b'.lookup a).or (t.lookup a) := fun _ => List.lookup_append
      have hresH : (Tuple.ofPairs (b' ++ t)).restrict H.attrs = b' := by
        refine Tuple.ext_get? (sorted_restrict fu.sorted) fb.sorted fun a => ?_
        rw [get?_restrict, hget, hgetb]
        split
        · next ha =>
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((fb.get?_isSome a).mpr ha)
          simp only [Tuple.get?] at hv ⊢; rw [hv]; rfl
        · next ha => exact (fb.get?_none ha).symm
      have hresV : (Tuple.ofPairs (b' ++ t)).restrict (args.eraseDups.map varAttr) = t := by
        refine Tuple.ext_get? (sorted_restrict fu.sorted) ft.sorted fun a => ?_
        rw [get?_restrict, hget, hgetb]
        split
        · next ha =>
          obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
          have : Tuple.get? b' (varAttr x) = none := fb.get?_none fun h => hHx _ h x rfl
          simp only [Tuple.get?] at this ⊢; rw [this]; rfl
        · next ha => exact (ft.get?_none (by rw [VH_attrs]; exact ha)).symm
      refine ⟨_, fu, ⟨⟨by rw [hresH]; exact hpb, trivial⟩, (htests _ fu).2.mpr ⟨by rw [hresH]; exact hpe, ?_⟩⟩, hresV⟩
      have e1 := args_restrict (u := Tuple.ofPairs (b' ++ t)) hax
      rw [hresV] at e1
      rw [← rowOf_restrict' hcH, hresH, hrow, e1]

/-! ## Codd's theorem for the construction -/

/-! ## The two kinds of atom -/

theorem colsH_attrs' (A : Str) (n : Nat) : (colsH A n).attrs = cols n := by
  unfold colsH Heading.attrs; rw [List.map_map]; exact List.map_id' _

theorem lookup_colsH (A : Str) (n : Nat) (c : String) :
    (colsH A n).lookup c = if c ∈ cols n then some (DD A) else none := by
  have := lookup_map_pair id (DD A) (cols n) c
  simpa [colsH] using this

theorem lookup_gH' (A : Str) (n : Nat) (a : String) :
    (gH A n).lookup a = ((colsH A n).lookup a).or ([(holdsAttr, Domain.kind .bool)].lookup a) :=
  List.lookup_append

theorem gH_attrs' (A : Str) (n : Nat) : (gH A n).attrs = cols n ++ [holdsAttr] := by
  have := colsH_attrs' A n
  unfold gH; unfold Heading.attrs at this ⊢; rw [List.map_append, this]; rfl

theorem holds_not_cols (n : Nat) : holdsAttr ∉ cols n := fun h => by
  obtain ⟨m, e⟩ := mem_cols h; exact holds_ne_colAttr m e

theorem map_fst_zip_cols {n : Nat} {vs : List Value} (hl : vs.length = n) :
    ((cols n).zip vs).map (·.1) = cols n :=
  List.map_fst_zip (by simp [cols, hl])

theorem rowOf_zip' {n : Nat} {vs : List Value} (hl : vs.length = n) (rest : List (String × Value))
    (hn : (((cols n).zip vs ++ rest).map (·.1)).Nodup) :
    rowOf (cols n) (Tuple.ofPairs ((cols n).zip vs ++ rest)) = vs := by
  simp only [rowOf, Tuple.get?_ofPairs hn]
  exact lookup_zip_map' (nodup_cols n) (by simp [cols, hl]) rest

/-- A row over the universe, as a tuple of a symbol's data. -/
theorem row_fits (A : Str) {n : Nat} {vs : List Value} (hl : vs.length = n)
    (hv : ∀ v ∈ vs, v ∈ A.univ) :
    (Tuple.ofPairs ((cols n).zip vs ++ [])).Fits (colsH A n) ∧
      rowOf (cols n) (Tuple.ofPairs ((cols n).zip vs ++ [])) = vs := by
  have hm := map_fst_zip_cols hl
  have hn : (((cols n).zip vs ++ ([] : List (String × Value))).map (·.1)).Nodup := by
    rw [List.append_nil, hm]; exact nodup_cols n
  refine ⟨fits_ofPairs hn (fun a => by rw [List.append_nil, hm, colsH_attrs']) fun p hp d hd => ?_,
    rowOf_zip' hl [] hn⟩
  rw [List.append_nil] at hp
  rw [lookup_colsH, ite_eq_left (List.of_mem_zip hp).1] at hd
  cases hd; exact (DD_mem A _).mpr (hv _ (List.of_mem_zip hp).2)

/-- A row over the universe, as a tuple of a guess, with `holds` true. -/
theorem grow_fits (A : Str) {n : Nat} {vs : List Value} (hl : vs.length = n)
    (hv : ∀ v ∈ vs, v ∈ A.univ) :
    (Tuple.ofPairs ((cols n).zip vs ++ [(holdsAttr, .bool true)])).Fits (gH A n) ∧
      rowOf (cols n) (Tuple.ofPairs ((cols n).zip vs ++ [(holdsAttr, .bool true)])) = vs ∧
      (Tuple.ofPairs ((cols n).zip vs ++ [(holdsAttr, .bool true)])).get? holdsAttr = some (.bool true) := by
  have hm := map_fst_zip_cols hl
  have hn : (((cols n).zip vs ++ [(holdsAttr, Value.bool true)]).map (·.1)).Nodup := by
    rw [List.map_append, hm]
    refine List.nodup_append.mpr ⟨nodup_cols n, by simp, fun a ha b hb e => ?_⟩
    have hb' : b = holdsAttr := List.mem_singleton.mp hb
    subst hb'
    exact holds_not_cols n (e ▸ ha)
  refine ⟨fits_ofPairs hn (fun a => by rw [List.map_append, hm, gH_attrs']; rfl) fun p hp d hd => ?_,
    rowOf_zip' hl _ hn, ?_⟩
  · rw [lookup_gH'] at hd
    rcases List.mem_append.mp hp with hp | hp
    · rw [lookup_colsH, ite_eq_left (List.of_mem_zip hp).1] at hd
      cases hd; exact (DD_mem A _).mpr (hv _ (List.of_mem_zip hp).2)
    · rw [List.mem_singleton.mp hp] at hd ⊢
      rw [lookup_colsH, ite_eq_right (holds_not_cols n)] at hd
      simp [List.lookup] at hd
      subst hd; rfl
  · rw [Tuple.get?_ofPairs hn, List.lookup_append,
      lookup_eq_none (fun q hq e => holds_not_cols n (by rw [← e]; exact (List.of_mem_zip hq).1))]
    simp [List.lookup]

theorem meaning_rel (A : Str) (hA : A.WF) (hC : A.Comparable) (ar : List (String × Nat))
    (G : Guess) (E : Env) (i : String) (args : List String) :
    ∃ r, Expr.eval (inCondition E) [] (compileP (univLit A) (relLit A) ar (.rel i args)) = .ok (.finrel r) ∧
      RepV A (FO.rel i args).vars ((FO.rel i args).Sat A G) r := by
  obtain ⟨b, hb, hbr⟩ := eval_relLit A hA (inCondition E) i args.length
  exact meaning_atom A hC args.length [] (fun _ => True) (fun vs => vs ∈ A.rel i) args rfl hb hbr
    (fun a ha x => by
      rw [colsH_attrs'] at ha; obtain ⟨m, rfl⟩ := mem_cols ha; exact colAttr_ne_varAttr m x)
    (fun c hc => by rw [lookup_colsH, ite_eq_left hc])
    (fun _ he => by cases he)
    (fun _ _ => ⟨by simp, by simp⟩)
    (fun _ _ h _ => h)
    (fun vs hl hv h => ⟨_, (row_fits A hl hv).1, (row_fits A hl hv).2, by rw [(row_fits A hl hv).2]; exact h, trivial⟩)

theorem meaning_gvar (A : Str) (hC : A.Comparable) (ar : List (String × Nat))
    (G : Guess) (hG : G.Fits A ar) (E : Env) (hE : GuessEnv A ar G (inCondition E))
    (j : String) (args : List String) :
    ∃ r, Expr.eval (inCondition E) [] (compileP (univLit A) (relLit A) ar (.gvar j args)) = .ok (.finrel r) ∧
      RepV A (FO.gvar j args).vars ((FO.gvar j args).Sat A G) r := by
  simp only [compileP]
  split
  · next h =>
    obtain ⟨g, hg, hgr⟩ := hE j _ h
    have hmem : holdsAttr ∈ (gH A args.length).attrs := by rw [gH_attrs']; simp
    exact meaning_atom A hC args.length [.call "=" [.attr holdsAttr, .val (.bool true)]]
      (fun t => t.get? holdsAttr = some (.bool true)) (fun vs => vs ∈ G j) args rfl (eval_name hg) hgr
      (fun a ha x => by
        rw [gH_attrs', List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · obtain ⟨m, rfl⟩ := mem_cols ha; exact colAttr_ne_varAttr m x
        · exact holds_ne_varAttr x)
      (fun c hc => by rw [lookup_gH', lookup_colsH, ite_eq_left hc]; rfl)
      (fun e he a ha => by
        rw [List.mem_singleton.mp he] at ha
        simp [Term.attrs] at ha; rw [ha]; exact hmem)
      (fun u fu => by
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((fu.get?_isSome holdsAttr).mpr hmem)
        have hd := fu.dom (holdsAttr, v) (lookup_mem_val hv) (.kind .bool)
          (by rw [lookup_gH', lookup_colsH, ite_eq_right (holds_not_cols _)]; simp [List.lookup])
        obtain ⟨bo, rfl⟩ : ∃ bo, v = .bool bo := by
          cases v <;> simp [Domain.mem, Kind.has] at hd; exact ⟨_, rfl⟩
        have hu : u.get? holdsAttr = some (.bool bo) := by
          rw [get?_restrict, ite_eq_left hmem] at hv; exact hv
        refine ⟨fun e he => ⟨bo, by rw [List.mem_singleton.mp he]; exact holds_holdsTrue hu⟩, ?_⟩
        rw [hv]
        simp [holds_holdsTrue hu])
      (fun _ _ hpb hpe => hpb.mp hpe)
      (fun vs hl hv hm => by
        obtain ⟨f, e, hh⟩ := grow_fits A hl hv
        exact ⟨_, f, e, ⟨fun _ => by rw [e]; exact hm, fun _ => hh⟩, hh⟩)
  · next h =>
    obtain ⟨d, hd, hdr⟩ := repV_domOf A (inCondition E) (nodup_eraseDups' args)
    obtain ⟨q, hq, hqr⟩ := repV_diff hdr hdr
    refine ⟨q, eval_except2 hd hd hq, hqr.congr (fun _ => Iff.rfl) fun t _ => ?_⟩
    show True ∧ ¬ True ↔ args.map (asg t) ∈ G j
    constructor
    · rintro ⟨_, h'⟩; exact absurd trivial h'
    · intro hm
      obtain ⟨k, hk, hl, _⟩ := hG j _ hm
      rw [List.length_map] at hl
      exact absurd (hl ▸ hk) h

theorem compile_meaning (A : Str) (hA : A.WF) (hC : A.Comparable) (ar : List (String × Nat))
    (G : Guess) (hG : G.Fits A ar) (E : Env) (hE : GuessEnv A ar G (inCondition E)) :
    ∀ φ : FO, ∃ r, Expr.eval (inCondition E) [] (compileP (univLit A) (relLit A) ar φ) = .ok (.finrel r) ∧
      Rep (VH A φ.vars) (fun t => φ.Sat A G (asg t)) r
  | .rel i args => meaning_rel A hA hC ar G E i args
  | .gvar j args => meaning_gvar A hC ar G hG E hE j args
  | .eq x y => by
    if hxy : x = y then
      subst hxy
      obtain ⟨r, hr, hrep⟩ := repV_domOf A (inCondition E) (List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩ : [x].Nodup)
      refine ⟨r, by simp only [compileP, ite_eq_left rfl]; exact hr, hrep.congr (fun z => ?_) fun t _ => ?_⟩
      · rw [mem_vars]; simp [FO.fv]
      · simp [FO.Sat]
    else
      have hn : [x, y].Nodup := by simp [hxy]
      obtain ⟨d, hd, hdr⟩ := repV_domOf A (inCondition E) hn
      obtain ⟨s, hs, hsr⟩ := repV_select_eq (x := x) (y := y) hC hdr (by simp) (by simp)
      refine ⟨s, by simp only [compileP, ite_eq_right hxy]; exact eval_select hd hs (fun a ha => by
          rw [attrs_congr hdr.head]
          simp only [eqT, Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            List.mem_append, List.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact Finrel.mem_attrs_iff.mpr (by rw [lookup_VH, ite_eq_left (by simp)]; rfl)
          · exact Finrel.mem_attrs_iff.mpr (by rw [lookup_VH, ite_eq_left (by simp)]; rfl)),
        hsr.congr (fun z => ?_) fun t _ => ?_⟩
      · rw [mem_vars]; simp [FO.fv]
      · simp [FO.Sat]
  | .not φ => by
    obtain ⟨r, hr, hrep⟩ := compile_meaning A hA hC ar G hG E hE φ
    obtain ⟨d, hd, hdr⟩ := repV_domOf A (inCondition E) (nodup_vars φ)
    obtain ⟨q, hq, hqr⟩ := repV_diff hdr hrep
    exact ⟨q, eval_except2 hd hr hq, hqr.congr (fun _ => Iff.rfl) fun t _ => by simp [FO.Sat]⟩
  | .and φ ψ => by
    obtain ⟨r, hr, hrep⟩ := compile_meaning A hA hC ar G hG E hE φ
    obtain ⟨s, hs, hsrep⟩ := compile_meaning A hA hC ar G hG E hE ψ
    obtain ⟨q, hq, hqr⟩ := repV_join hrep hsrep (dep_sat A G φ) (dep_sat A G ψ)
    exact ⟨q, eval_join2 hr hs hq, hqr.congr (fun z => by rw [mem_vars]; simp [FO.fv, mem_vars])
      fun t _ => Iff.rfl⟩
  | .or φ ψ => by
    obtain ⟨r, hr, hrep⟩ := compile_meaning A hA hC ar G hG E hE φ
    obtain ⟨s, hs, hsrep⟩ := compile_meaning A hA hC ar G hG E hE ψ
    obtain ⟨r', hr', hrep'⟩ := repV_pad A hr hrep (dep_sat A G φ) ((nodup_vars ψ).filter _)
    obtain ⟨s', hs', hsrep'⟩ := repV_pad A hs hsrep (dep_sat A G ψ) ((nodup_vars φ).filter _)
    have h1 := hrep'.congr (ys := (FO.or φ ψ).vars) (Q' := φ.Sat A G)
      (fun z => by rw [mem_append_filter, mem_vars, mem_vars, mem_vars]; simp [FO.fv]) fun _ _ => Iff.rfl
    have h2 := hsrep'.congr (ys := (FO.or φ ψ).vars) (Q' := ψ.Sat A G)
      (fun z => by rw [mem_append_filter, mem_vars, mem_vars, mem_vars]; simp [FO.fv, or_comm])
      fun _ _ => Iff.rfl
    obtain ⟨q, hq, hqr⟩ := repV_union h1 h2
    exact ⟨q, eval_union2 hr' hs' hq, hqr⟩
  | .ex x φ => by
    obtain ⟨r, hr, hrep⟩ := compile_meaning A hA hC ar G hG E hE φ
    obtain ⟨p, hp, hprep⟩ := repV_pad A hr hrep (dep_sat A G φ) (nodup_withVar (nodup_vars φ) x)
    obtain ⟨s, hs, hsrep⟩ := repV_exists (zs := (FO.ex x φ).vars) (x := x) hprep
      (fun z => by
        rw [mem_withVar, mem_vars, mem_vars]
        simp only [FO.fv, List.mem_filter, bne_iff_ne, ne_eq, decide_eq_true_eq]
        exact ⟨fun ⟨h, h'⟩ => ⟨Or.inl h, h'⟩, fun ⟨h, h'⟩ => ⟨h.resolve_right h', h'⟩⟩)
      (mem_withVar.mpr (Or.inr rfl)) (nodup_vars _)
      ((dep_sat A G φ).mono fun _ h => List.mem_append_left _ h)
    exact ⟨s, by simp only [compileP]; exact eval_project hp hs, hsrep⟩
  | .all x φ => by
    obtain ⟨r, hr, hrep⟩ := compile_meaning A hA hC ar G hG E hE φ
    obtain ⟨p, hp, hprep⟩ := repV_pad A hr hrep (dep_sat A G φ) (nodup_withVar (nodup_vars φ) x)
    have hys : ∀ z, z ∈ (if φ.vars.contains x then φ.vars else φ.vars ++ [x]) ↔ z ∈ φ.vars ∨ z = x := by
      intro z; rw [← mem_withVar]; unfold withVar; split <;> simp
    have hyn : (if φ.vars.contains x then φ.vars else φ.vars ++ [x]).Nodup := by
      split
      · exact nodup_vars φ
      · next h =>
        have hx : x ∉ φ.vars := by simpa using h
        refine List.nodup_append.mpr ⟨nodup_vars φ, by simp, fun a ha b hb => ?_⟩
        rw [List.mem_singleton] at hb; subst hb
        exact fun e => hx (e ▸ ha)
    have hp' := hprep.congr (ys := if φ.vars.contains x then φ.vars else φ.vars ++ [x])
      (Q' := φ.Sat A G) (fun z => by rw [mem_withVar, hys]) fun _ _ => Iff.rfl
    obtain ⟨d, hd, hdr⟩ := repV_domOf A (inCondition E) hyn
    obtain ⟨n, hn, hnr⟩ := repV_diff hdr hp'
    have hdep : Dep (if φ.vars.contains x then φ.vars else φ.vars ++ [x])
        (fun ρ => True ∧ ¬ φ.Sat A G ρ) := fun ρ ρ' h =>
      and_congr Iff.rfl (not_congr ((dep_sat A G φ).mono (fun z hz => (hys z).mpr (Or.inl hz)) ρ ρ' h))
    obtain ⟨s, hs, hsrep⟩ := repV_exists (zs := (FO.all x φ).vars) (x := x) hnr
      (fun z => by
        rw [hys, mem_vars, mem_vars]
        simp only [FO.fv, List.mem_filter, bne_iff_ne, ne_eq, decide_eq_true_eq]
        exact ⟨fun ⟨h, h'⟩ => ⟨Or.inl h, h'⟩, fun ⟨h, h'⟩ => ⟨h.resolve_right h', h'⟩⟩)
      ((hys x).mpr (Or.inr rfl)) (nodup_vars _) hdep
    obtain ⟨d', hd', hdr'⟩ := repV_domOf A (inCondition E) (nodup_vars (FO.all x φ))
    obtain ⟨q, hq, hqr⟩ := repV_diff hdr' hsrep
    refine ⟨q, by simp only [compileP]; exact eval_except2 hd' (eval_project (eval_except2 hd hp hn) hs) hq,
      hqr.congr (fun _ => Iff.rfl) fun t _ => ?_⟩
    show (True ∧ ¬ ∃ a ∈ A.univ, True ∧ ¬ φ.Sat A G (upd (asg t) x a)) ↔ ∀ a ∈ A.univ, φ.Sat A G (upd (asg t) x a)
    exact ⟨fun ⟨_, h⟩ a ha => Decidable.byContradiction fun hn => h ⟨a, ha, trivial, hn⟩,
      fun h => ⟨trivial, fun ⟨a, ha, _, hn⟩ => hn (h a ha)⟩⟩

/-- The condition of `esoForm` is "the sentence holds under the guess". -/
theorem cond_meaning (A : Str) (hA : A.WF) (hC : A.Comparable) (ψ : Sentence)
    (G : Guess) (hG : G.Fits A ψ.ar) (E : Env) (hE : GuessEnv A ψ.ar G (inCondition E)) :
    Cond.eval (inCondition E) [] (nonEmpty (compileP (univLit A) (relLit A) ψ.ar ψ.φ)) =
      .ok (decide (ψ.φ.Sat A G (fun _ => default))) := by
  obtain ⟨r, hr, hrep⟩ := compile_meaning A hA hC ψ.ar G hG E hE ψ.φ
  rw [eval_nonEmpty hr]
  have hv : ψ.φ.vars = [] := by
    have := ψ.closed
    rw [List.isEmpty_iff] at this
    simp [FO.vars, this]
  rw [hv] at hrep
  have hfit : ∀ t : Tuple, t.Fits (VH A []) ↔ t = [] := by
    intro t
    constructor
    · intro f
      cases t with
      | nil => rfl
      | cons p t => exact absurd ((f.attrs p.1).mp (List.mem_cons_self ..)) (by simp [VH, Heading.attrs])
    · rintro rfl
      exact ⟨List.Pairwise.nil, fun a => by simp [Tuple.attrs, VH, Heading.attrs], fun p hp => by cases hp⟩
  have key : (∃ t, t ∈ r.tuples) ↔ ψ.φ.Sat A G (fun _ => default) := by
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨f, hs⟩ := (hrep.mem t).mp ht
      exact (ψ.sat_any _ _).mp hs
    · intro h
      exact ⟨[], (hrep.mem []).mpr ⟨(hfit []).mpr rfl, (ψ.sat_any _ _).mp h⟩⟩
  congr 1
  by_cases h : ψ.φ.Sat A G (fun _ => default)
  · rw [decide_eq_true h]
    obtain ⟨t, ht⟩ := key.mpr h
    cases hr' : r.tuples with
    | nil => rw [hr'] at ht; cases ht
    | cons _ _ => rfl
  · rw [decide_eq_false h]
    cases hr' : r.tuples with
    | nil => rfl
    | cons t _ => exact absurd (key.mp ⟨t, by rw [hr']; exact List.mem_cons_self ..⟩) h

end Rasso.ESO
