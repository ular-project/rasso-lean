import Rasso.ESO.Construction
import Rasso.Rep
import Rasso.Bridge.Finrel
import Std.Data.String.ToNat

/-!
# ESO: the building blocks of the construction

What the pieces of `esoForm` evaluate to: the universe, its powers, the data of a symbol,
the tests of an atom, and the condition "has a tuple". The formula translation
(`Rasso.ESO.Meaning`) is built from these.

Conventions:

* Every attribute of the construction has the domain `DD A`, the universe as a finite
  set, except a guess's `holds`, which is `bool`.
* `Str.Comparable`: no element is an exact number (an int or a rat) while another is a
  float, and no element is a symbol while another is a string. Rasso's `=` refuses to
  compare an int or a rat with a float, and a symbol with a string, so on such a universe
  the construction is refused. Rat elements are allowed.
-/

namespace Rasso.ESO

open Rasso

/-- The domain of every attribute in the construction: the universe as a finite set. -/
def DD (A : Str) : Domain := .set (racketSorted A.univ)

/-- The heading of the relation for some variables. -/
def VH (A : Str) (xs : List String) : Heading := xs.map fun x => (varAttr x, DD A)

/-- The heading of a symbol's data at arity `n`. -/
def colsH (A : Str) (n : Nat) : Heading := (cols n).map fun c => (c, DD A)

/-- The values of some attributes of a tuple, in order. -/
def rowOf (cs : List String) (t : Tuple) : List Value := cs.map fun c => (t.get? c).getD default

/-- The assignment a tuple of variables gives. -/
def asg (t : Tuple) : String → Value := fun x => (t.get? (varAttr x)).getD default

/-- No element is an exact number (an int or a rat) while another is a float, and no
element is a symbol while another is a string. -/
def Str.Comparable (A : Str) : Prop :=
  ∀ v ∈ A.univ, ∀ w ∈ A.univ,
    ¬ (v.isExact = true ∧ w.isFloat = true) ∧ ¬ (v.isSymbol = true ∧ w.isString = true)

theorem DD_mem (A : Str) (v : Value) : (DD A).mem v = true ↔ v ∈ A.univ := by
  simp only [DD, Domain.mem, List.contains_iff_mem, racketSorted, List.mem_mergeSort,
    List.mem_eraseDups]

theorem nodup_vars_map {xs : List String} (hn : xs.Nodup) : (xs.map varAttr).Nodup := by
  exact nodup_map_of_inj hn fun x _ y _ e => (String.append_right_inj "x_").mp e

theorem nodup_cols (n : Nat) : (cols n).Nodup := by
  refine nodup_map_of_inj List.nodup_range fun m _ n _ e => ?_
  simp only [colAttr] at e
  exact Nat.repr_injective (by simpa using e)

theorem forIn_ok_of_all {α : Type} {f : α → PUnit → Except String (ForInStep PUnit)} :
    ∀ {l : List α}, (∀ x ∈ l, f x PUnit.unit = .ok (.yield PUnit.unit)) →
      forIn l PUnit.unit f = .ok PUnit.unit
  | [], _ => rfl
  | x :: l, h => by
    rw [List.forIn_cons, h x List.mem_cons_self]
    exact forIn_ok_of_all fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem mapM_eq_map {α β ε : Type} {f : α → Except ε β} (g : α → β) :
    ∀ {l : List α}, (∀ x ∈ l, f x = .ok (g x)) → l.mapM f = .ok (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x List.mem_cons_self,
      mapM_eq_map g fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

/-- The heading `cs` with every attribute's domain `DD A`. -/
def cH (A : Str) (cs : List String) : Heading := cs.map fun c => (c, DD A)

theorem cH_attrs (A : Str) (cs : List String) : (cH A cs).attrs = cs := by
  simp only [cH, Heading.attrs, List.map_map]; exact List.map_id' _

theorem lookup_cH {A : Str} {cs : List String} {c : String} {d : Domain}
    (h : (cH A cs).lookup c = some d) : d = DD A := by
  have hm := lookup_mem h
  simp only [cH, List.mem_map] at hm
  obtain ⟨_, _, e⟩ := hm
  cases e; rfl

theorem evalHeading_cH (A : Str) (env : Env) :
    ∀ (cs : List String), evalHeading env [] (cs.map (·, univDom A)) = .ok (cH A cs)
  | [] => by rw [evalHeading.eq_def]; rfl
  | c :: cs => by
    have ih := evalHeading_cH A env cs
    simp only [univDom] at ih
    rw [List.map_cons, evalHeading.eq_def]
    simp [ih, univDom, DomExpr.eval, DD, cH, bind, Except.bind, pure, Except.pure]

/-- Rows over the universe, each as long as the heading. -/
def RowsOver (A : Str) (cs : List String) (rows : List (List Value)) : Prop :=
  ∀ row ∈ rows, row.length = cs.length ∧ ∀ v ∈ row, v ∈ A.univ

/-- ω with rows over the universe evaluates to its rows as tuples. -/
theorem eval_rowsLit_eq (A : Str) (env : Env) (cs : List String) (rows : List (List Value))
    (hrows : RowsOver A cs rows) :
    Expr.eval env [] (.omegaRows (cs.map (·, univDom A)) rows) =
      .ok (.finrel (Finrel.ofTuples (cH A cs) (rows.map fun row => Tuple.ofPairs (cs.zip row)))) := by
  rw [Expr.eval]
  simp only [List.any_nil, Bool.false_eq_true, ite_false]
  simp only [evalHeading_cH, bind, Except.bind]
  have hlen : (cH A cs).length = cs.length := by simp [cH]
  rw [mapM_eq_map (fun row => Tuple.ofPairs (cs.zip row))]
  · rfl
  intro row hrow
  obtain ⟨hl₀, hu⟩ := hrows row hrow
  have hl : (row.length != List.length (cH A cs)) = false := by simp [hlen, hl₀]
  rw [ite_eq_right (by rw [hl]; exact Bool.false_ne_true)]
  rw [forIn_ok_of_all]
  · simp [cH_attrs, pure, Except.pure]
  intro x hx
  obtain ⟨⟨c, d⟩, v⟩ := x
  have hd : d = DD A := by
    have h1 := (List.of_mem_zip hx).1
    simp only [cH, List.mem_map] at h1
    obtain ⟨_, _, e⟩ := h1
    cases e; rfl
  have hm : d.mem v = true := by rw [hd, DD_mem]; exact hu v (List.of_mem_zip hx).2
  simp [hm, pure, Except.pure]

theorem lookup_zip_map {g : String → Value} {a : String} :
    ∀ {cs : List String}, cs.Nodup →
      (cs.zip (cs.map g)).lookup a = if a ∈ cs then some (g a) else none
  | [], _ => by simp
  | c :: cs, hn => by
    rw [List.map_cons, List.zip_cons_cons]
    by_cases e : a = c
    · subst e; rw [lookup_cons_self]; simp
    · rw [lookup_cons_ne e, lookup_zip_map (List.nodup_cons.mp hn).2]
      simp [e]

theorem rowOf_zip : ∀ {cs : List String} {row : List Value}, cs.Nodup → row.length = cs.length →
    cs.map (fun c => ((cs.zip row).lookup c).getD default) = row
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | c :: cs, v :: row, hn, hl => by
    have hn' := List.nodup_cons.mp hn
    rw [List.zip_cons_cons, List.map_cons, lookup_cons_self]
    congr 1
    have : ∀ c' ∈ cs, (((c, v) :: cs.zip row).lookup c').getD default =
        ((cs.zip row).lookup c').getD default := fun c' hc' => by
      rw [lookup_cons_ne (fun (e : c' = c) => hn'.1 (e ▸ hc'))]
    rw [List.map_congr_left this]
    exact rowOf_zip hn'.2 (by simpa using hl)

theorem keys_zip {cs : List String} {row : List Value} (hl : row.length = cs.length) :
    (cs.zip row).map (·.1) = cs := List.map_fst_zip (by omega)

theorem fits_rowTuple (A : Str) {cs : List String} (hn : cs.Nodup) {row : List Value}
    (hl : row.length = cs.length) (hu : ∀ v ∈ row, v ∈ A.univ) :
    (Tuple.ofPairs (cs.zip row)).Fits (cH A cs) := by
  have hk := keys_zip hl
  refine ⟨ofPairs_sorted (by rw [hk]; exact hn), fun a => ?_, fun p hp d hd => ?_⟩
  · rw [attrs_ofPairs, hk, cH_attrs]
  · rw [lookup_cH hd]
    exact (DD_mem A _).mpr (hu _ (List.of_mem_zip (mem_ofPairs.mp hp)).2)

theorem rowOf_rowTuple {cs : List String} (hn : cs.Nodup) {row : List Value}
    (hl : row.length = cs.length) : rowOf cs (Tuple.ofPairs (cs.zip row)) = row := by
  unfold rowOf
  simp only [Tuple.get?_ofPairs (by rw [keys_zip hl]; exact hn)]
  exact rowOf_zip hn hl

/-- A tuple that fits `cH A cs` is the row of its values. -/
theorem rowOf_fits {A : Str} {cs : List String} (hn : cs.Nodup) {t : Tuple}
    (ft : t.Fits (cH A cs)) :
    (rowOf cs t).length = cs.length ∧ (∀ v ∈ rowOf cs t, v ∈ A.univ) ∧
      Tuple.ofPairs (cs.zip (rowOf cs t)) = t := by
  have hnH : (cH A cs).attrs.Nodup := by rw [cH_attrs]; exact hn
  refine ⟨by simp [rowOf], fun v hv => ?_, ?_⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
    have hct : c ∈ t.attrs := (ft.attrs c).mpr (by rw [cH_attrs]; exact hc)
    obtain ⟨⟨c', w⟩, hw, e⟩ := List.mem_map.mp hct
    simp only at e; subst e
    rw [show Tuple.get? t c' = some w from lookup_of_mem ft.nodup hw]
    exact (DD_mem A w).mp (ft.dom _ hw (DD A) (mem_lookup hnH (List.mem_map.mpr ⟨c', hc, rfl⟩)))
  · have hk := keys_zip (cs := cs) (row := rowOf cs t) (by simp [rowOf])
    refine Tuple.ext_get? (Tuple.sorted_ofPairs (by rw [hk]; exact hn)) ft.sorted fun a => ?_
    rw [Tuple.get?_ofPairs (by rw [hk]; exact hn), rowOf, lookup_zip_map hn]
    by_cases ha : a ∈ cs
    · rw [ite_eq_left ha]
      have hat : a ∈ t.attrs := (ft.attrs a).mpr (by rw [cH_attrs]; exact ha)
      obtain ⟨⟨a', w⟩, hw, e⟩ := List.mem_map.mp hat
      simp only at e; subst e
      rw [show Tuple.get? t a' = some w from lookup_of_mem ft.nodup hw]; rfl
    · rw [ite_eq_right ha]
      cases hg : Tuple.get? t a with
      | none => rfl
      | some w =>
        have := (ft.attrs a).mp (List.mem_map_of_mem (f := (·.1)) (lookup_mem hg))
        rw [cH_attrs] at this; exact absurd this ha

/-- What ω with rows over the universe represents: the tuples whose row is listed. -/
theorem rep_rowsLit (A : Str) {cs : List String} (hn : cs.Nodup) {rows : List (List Value)}
    (hrows : RowsOver A cs rows) :
    Rep (cH A cs) (fun t => rowOf cs t ∈ rows)
      (Finrel.ofTuples (cH A cs) (rows.map fun row => Tuple.ofPairs (cs.zip row))) := by
  refine ⟨Finrel.wf_ofTuples (by rw [cH_attrs]; exact hn) fun t ht => ?_, fun a => rfl, fun t => ?_⟩
  · obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp ht
    exact fits_rowTuple A hn (hrows row hrow).1 (hrows row hrow).2
  · rw [Finrel.mem_ofTuples, List.mem_map]
    constructor
    · rintro ⟨row, hrow, rfl⟩
      refine ⟨fits_rowTuple A hn (hrows row hrow).1 (hrows row hrow).2, ?_⟩
      rw [rowOf_rowTuple hn (hrows row hrow).1]; exact hrow
    · rintro ⟨ft, hi⟩
      exact ⟨_, hi, (rowOf_fits hn ft).2.2⟩

/-- `Rep` depends on the heading only through its lookups, and on the predicate only on
fitting tuples. -/
theorem _root_.Rasso.Rep.congr {H H' : Heading} {P Q : Tuple → Prop} {r : Finrel} (hr : Rep H P r)
    (hH : ∀ a, H.lookup a = H'.lookup a) (hP : ∀ t, t.Fits H → (P t ↔ Q t)) : Rep H' Q r where
  wf := hr.wf
  head a := (hr.head a).trans (hH a)
  mem t := by
    rw [hr.mem]
    constructor
    · rintro ⟨f, p⟩; exact ⟨f.congr hH, (hP t f).mp p⟩
    · rintro ⟨f, q⟩
      have f' := f.congr fun a => (hH a).symm
      exact ⟨f', (hP t f').mpr q⟩

/-- A symbol's data: the tuples of `A.rel i` of length `n`. -/
theorem eval_relLit (A : Str) (_hA : A.WF) (env : Env) (i : String) (n : Nat) :
    ∃ r, Expr.eval env [] (relLit A i n) = .ok (.finrel r) ∧
      Rep (colsH A n) (fun t => rowOf (cols n) t ∈ A.rel i) r := by
  -- `A.WF` is not needed: `relStatement` keeps only the rows over the universe.
  have hlc : (cols n).length = n := by simp [cols]
  have hrows : ∀ row, row ∈ ((A.rel i).filter fun t => t.length == n && t.all A.univ.contains).eraseDups ↔
      row ∈ A.rel i ∧ row.length = n ∧ ∀ v ∈ row, v ∈ A.univ := by
    intro row
    simp [List.mem_eraseDups, List.mem_filter, List.all_eq_true]
  have hover : RowsOver A (cols n)
      ((A.rel i).filter fun t => t.length == n && t.all A.univ.contains).eraseDups :=
    fun row hrow => by
      obtain ⟨_, hl, hu⟩ := (hrows row).mp hrow
      exact ⟨by rw [hl, hlc], hu⟩
  refine ⟨_, eval_rowsLit_eq A env (cols n) _ hover,
    (rep_rowsLit A (nodup_cols n) hover).congr (fun _ => rfl) fun t ft => ?_⟩
  obtain ⟨hl, hu, _⟩ := rowOf_fits (nodup_cols n) ft
  rw [hrows]
  exact ⟨fun h => h.1, fun h => ⟨h, by rw [hl, hlc], hu⟩⟩

theorem heading_single {h : Heading} {a : String} {d : Domain} (hn : h.attrs.Nodup)
    (hl : ∀ x, h.lookup x = [(a, d)].lookup x) : h = [(a, d)] := by
  match h, hn, hl with
  | [], _, hl => have := hl a; simp [List.lookup] at this
  | [(c, e)], _, hl =>
    have := hl c
    by_cases hc : c = a
    · subst hc; simp [List.lookup] at this; rw [this]
    · have hb : (c == a) = false := by simpa using hc
      simp [List.lookup, hb] at this
  | (c, e) :: (c', e') :: rest, hn, hl =>
    have h1 := hl c
    have h2 := hl c'
    have hne : c' ≠ c := by
      intro e; simp [Heading.attrs] at hn; exact hn.1.1 e.symm
    have hne' : (c' == c) = false := by simpa using hne
    simp only [List.lookup, beq_self_eq_true, hne'] at h1 h2
    by_cases hc : c = a
    · subst hc
      have : (c' == c) = false := hne'
      simp [this] at h2
    · have : (c == a) = false := by simpa using hc
      simp [this] at h1

theorem fits_single {t : Tuple} {a : String} {d : Domain} :
    t.Fits [(a, d)] ↔ ∃ v, t = [(a, v)] ∧ d.mem v = true := by
  constructor
  · intro f
    have hat := fun x => f.attrs x
    simp only [Heading.attrs, List.map_cons, List.map_nil, List.mem_singleton] at hat
    match t, f, hat with
    | [], _, hat => exact absurd ((hat a).mpr rfl) (by simp [Tuple.attrs])
    | [(c, v)], f, hat =>
      have hc : c = a := (hat c).mp (by simp [Tuple.attrs])
      subst hc
      exact ⟨v, rfl, f.dom _ List.mem_cons_self d (by simp [List.lookup])⟩
    | (c, v) :: (c', v') :: rest, f, hat =>
      have h1 : c = a := (hat c).mp (by simp [Tuple.attrs])
      have h2 : c' = a := (hat c').mp (by simp [Tuple.attrs])
      have := f.nodup
      simp [Tuple.attrs, h1, h2] at this
  · rintro ⟨v, rfl, hv⟩
    refine ⟨List.pairwise_singleton _ _, fun x => by simp [Tuple.attrs, Heading.attrs], ?_⟩
    intro p hp e he
    simp at hp; subst hp
    simp [List.lookup] at he; subst he; exact hv

theorem rep_rename1 {a b : String} {d : Domain} {r : Finrel}
    (hr : Rep [(a, d)] (fun _ => True) r) :
    ∃ s, r.rename [(a, b)] = .ok s ∧ Rep [(b, d)] (fun _ => True) s := by
  have hh : r.heading = [(a, d)] := heading_single hr.wf.nodup hr.head
  have hren : Finrel.renameHeading [(a, b)] r.heading = [(b, d)] := by
    rw [hh]; simp [Finrel.renameHeading, Finrel.renameAttr, List.lookup]
  obtain ⟨s, hs⟩ := (Finrel.rename_ok (ren := [(a, b)]) (r := r)).mpr ⟨fun p hp => by
      simp at hp; subst hp; simp [Finrel.attrs, hh, Heading.attrs],
    by rw [hren]; simp [Heading.attrs]⟩
  refine ⟨s, hs, Finrel.rename_wf hs hr.wf, fun x => by rw [Finrel.rename_heading hs, hren], fun t => ?_⟩
  rw [Finrel.mem_rename hs, fits_single]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨v, rfl, hv⟩ := fits_single.mp ((hr.mem u).mp hu).1
    refine ⟨⟨v, ?_, hv⟩, trivial⟩
    simp [Finrel.renameTuple, Finrel.renameAttr, List.lookup, Tuple.ofPairs]
  · rintro ⟨⟨v, rfl, hv⟩, -⟩
    refine ⟨[(a, v)], (hr.mem _).mpr ⟨fits_single.mpr ⟨v, rfl, hv⟩, trivial⟩, ?_⟩
    simp [Finrel.renameTuple, Finrel.renameAttr, List.lookup, Tuple.ofPairs]


theorem mem_racketSorted {vs : List Value} {v : Value} : v ∈ racketSorted vs ↔ v ∈ vs := by
  simp [racketSorted, List.mem_mergeSort, List.mem_eraseDups]

theorem eval_univLit (A : Str) (env : Env) :
    ∃ r, Expr.eval env [] (univLit A) = .ok (.finrel r) ∧ Rep [(univAttr, DD A)] (fun _ => True) r := by
  have hover : RowsOver A [univAttr] ((racketSorted A.univ).map ([·])) := by
    intro row hrow
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hrow
    exact ⟨rfl, fun w hw => by simp at hw; subst hw; exact mem_racketSorted.mp hv⟩
  refine ⟨_, eval_rowsLit_eq A env [univAttr] _ hover,
    (rep_rowsLit A (by simp : [univAttr].Nodup) hover).congr (fun _ => rfl) fun t ft => ?_⟩
  obtain ⟨hl, hu, _⟩ := rowOf_fits (by simp : [univAttr].Nodup) ft
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  match h : rowOf [univAttr] t, hl, hu with
  | [v], _, hu => exact List.mem_map.mpr ⟨v, mem_racketSorted.mpr (hu v (by simp)), rfl⟩

theorem eval_copy (A : Str) (env : Env) (b : String) :
    ∃ r, Expr.eval env [] (.rename [(univAttr, b)] (univLit A)) = .ok (.finrel r) ∧
      Rep [(b, DD A)] (fun _ => True) r := by
  obtain ⟨u, hu, hr⟩ := eval_univLit A env
  obtain ⟨s, hs, hrs⟩ := rep_rename1 (b := b) hr
  exact ⟨s, eval_rename hu hs, hrs⟩

/-- n-ary ⋈ of finite relations is the left fold of the binary join. -/
theorem eval_joinN {env : Env} {e : Expr} {es : List Expr} {r q : Finrel} {rs : List Finrel}
    (h₀ : Expr.eval env [] e = .ok (.finrel r))
    (hs : Forall2 (fun e r => Expr.eval env [] e = .ok (.finrel r)) es rs)
    (hq : rs.foldlM (fun acc w => acc.join w) r = .ok q) :
    Expr.eval env [] (.nary .join (e :: es)) = .ok (.finrel q) := by
  have hm : (e :: es).mapM (fun x => Expr.eval env [] x) = .ok ((r :: rs).map Val.finrel) := by
    refine mapM_ok.mpr (.cons h₀ ?_)
    clear hq h₀
    induction hs with
    | nil => exact .nil
    | cons h _ ih => exact .cons h ih
  have hf : ∀ (l : List Finrel) (acc : Finrel),
      (l.map Val.finrel).foldlM (fun acc w => do acc.join (← w.asFinrel "join")) acc =
        l.foldlM (fun acc w => acc.join w) acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons x l ih =>
      intro acc
      simp only [List.map_cons, List.foldlM_cons, Val.asFinrel, bind, Except.bind]
      cases acc.join x with
      | error _ => rfl
      | ok a => exact ih a
  simp only [bind, Except.bind, Val.asFinrel] at hf
  rw [Expr.eval]
  simp only [List.any_nil, Bool.false_eq_true, ite_false, bind, Except.bind]
  rw [hm]
  simp [hf, hq, Val.asFinrel, pure, Except.pure]

theorem foldRep (A : Str) (env : Env) (f : String → String) :
    ∀ (xs : List String) (rs : List Finrel) (acc : Finrel) (H : Heading),
      Rep H (fun _ => True) acc → (H.attrs ++ xs.map f).Nodup →
      Forall2 (fun x r => Rep [(f x, DD A)] (fun _ => True) r) xs rs →
      ∃ q, rs.foldlM (fun acc w => acc.join w) acc = .ok q ∧
        Rep (H ++ xs.map fun x => (f x, DD A)) (fun _ => True) q
  | [], [], acc, H, hacc, _, _ => ⟨acc, rfl, by simpa using hacc⟩
  | x :: xs, r :: rs, acc, H, hacc, hn, .cons hr hrs => by
    have hfx : f x ∉ H.attrs := by
      intro h; rw [List.map_cons, List.nodup_append] at hn
      exact hn.2.2 _ h _ List.mem_cons_self rfl
    have hHx : H.lookup (f x) = none := by
      cases hl : H.lookup (f x) with
      | none => rfl
      | some _ => exact absurd (List.mem_map_of_mem (f := (·.1)) (lookup_mem hl)) hfx
    obtain ⟨q, hq, hrq⟩ := rep_join hacc hr fun a d e h1 h2 => by
      have : a = f x := by
        by_cases ha : a = f x
        · exact ha
        · have : (a == f x) = false := by simpa using ha
          simp [List.lookup, this] at h2
      subst this; rw [hHx] at h1; cases h1
    have hj : ∀ a, (joinH H [(f x, DD A)]).lookup a = (H ++ [(f x, DD A)]).lookup a := by
      intro a; rw [lookup_joinH, List.lookup_append]
    have hrq' := hrq.congr hj fun _ _ => ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩
    have hn' : ((H ++ [(f x, DD A)]).attrs ++ xs.map f).Nodup := by
      simpa [Heading.attrs, List.map_cons, List.append_assoc] using hn
    obtain ⟨q', hq', hr'⟩ := foldRep A env f xs rs q _ hrq' hn' hrs
    refine ⟨q', ?_, by simpa [List.append_assoc] using hr'⟩
    simp only [List.foldlM_cons, bind, Except.bind, hq]
    exact hq'

/-- `U` to the power of some attributes: every assignment of elements to them. -/
theorem eval_univPow (A : Str) (env : Env) {f : String → String} {as : List String}
    (hn : (as.map f).Nodup) :
    ∃ r, Expr.eval env [] (univPowP (univLit A) f as) = .ok (.finrel r) ∧
      Rep (as.map fun a => (f a, DD A)) (fun _ => True) r := by
  match as, hn with
  | [], _ =>
    have hover : RowsOver A [] [[]] := fun row hrow => by simp at hrow; subst hrow; simp
    refine ⟨_, eval_rowsLit_eq A env [] [[]] hover,
      (rep_rowsLit A List.nodup_nil hover).congr (fun _ => rfl) fun t _ => ?_⟩
    simp [rowOf]
  | [a], _ => exact eval_copy A env (f a)
  | a :: b :: rest, hn =>
    obtain ⟨r, hr, hra⟩ := eval_copy A env (f a)
    have hall : ∀ x ∈ b :: rest, ∃ s, Expr.eval env [] (.rename [(univAttr, f x)] (univLit A)) =
        .ok (.finrel s) ∧ Rep [(f x, DD A)] (fun _ => True) s := fun x _ => eval_copy A env (f x)
    obtain ⟨rs, hrs⟩ := Forall2.of_forall hall
    have hev : Forall2 (fun e r => Expr.eval env [] e = .ok (.finrel r))
        ((b :: rest).map fun x => Expr.rename [(univAttr, f x)] (univLit A)) rs := by
      clear hall
      generalize b :: rest = xs at hrs
      induction hrs with
      | nil => exact .nil
      | cons h _ ih => exact .cons h.1 ih
    have hrep : Forall2 (fun x r => Rep [(f x, DD A)] (fun _ => True) r) (b :: rest) rs :=
      hrs.imp fun _ _ h => h.2
    have hn' : (Heading.attrs [(f a, DD A)] ++ (b :: rest).map f).Nodup := by
      simpa [Heading.attrs] using hn
    obtain ⟨q, hq, hrq⟩ := foldRep A env f (b :: rest) rs r _ hra hn' hrep
    refine ⟨q, ?_, by simpa using hrq⟩
    exact eval_joinN hr hev hq

/-- An equality test between two attributes whose values are comparable. -/
theorem holds_eqT {t : Tuple} {a b : String} {v w : Value}
    (ha : t.get? a = some v) (hb : t.get? b = some w)
    (hc : ¬ (v.isExact = true ∧ w.isFloat = true) ∧ ¬ (v.isFloat = true ∧ w.isExact = true) ∧
      ¬ (v.isSymbol = true ∧ w.isString = true) ∧ ¬ (v.isString = true ∧ w.isSymbol = true)) :
    Term.holds t (eqT a b) = .ok (decide (v = w)) := by
  have he : applyOp "=" [v, w] = .ok (.bool (v == w)) := by
    cases v <;> cases w <;> first
      | rfl
      | (exfalso; simp [Value.isExact, Value.exact?, Value.isFloat, Value.isSymbol,
          Value.isString] at hc)
  simp only [Term.holds, eqT, Term.eval, ha, hb, List.mapM_cons, List.mapM_nil, bind,
    Except.bind, pure, Except.pure, he, asBool]
  rfl

/-- The test `holds = true` on a guess tuple. -/
theorem holds_holdsTrue {t : Tuple} {b : Bool} (h : t.get? holdsAttr = some (.bool b)) :
    Term.holds t (.call "=" [.attr holdsAttr, .val (.bool true)]) = .ok b := by
  have he : applyOp "=" [.bool b, .bool true] = .ok (.bool (Value.bool b == .bool true)) := rfl
  simp only [Term.holds, Term.eval, h, List.mapM_cons, List.mapM_nil, bind,
    Except.bind, pure, Except.pure, he, asBool]
  cases b <;> rfl

/-- A conjunction of tests that all evaluate. -/
theorem holds_conj {t : Tuple} {p : Term → Bool} :
    ∀ {ts : List Term}, (∀ e ∈ ts, Term.holds t e = .ok (p e)) →
      Term.holds t (conj ts) = .ok (ts.all p) := by
  intro ts h
  have hev : ∀ e ∈ ts, Term.eval t e = .ok (.bool (p e)) := by
    intro e he
    have := h e he
    simp only [Term.holds, bind, Except.bind] at this
    cases hv : Term.eval t e with
    | error _ => rw [hv] at this; cases this
    | ok v =>
      rw [hv] at this
      cases v <;> simp only [asBool] at this <;> try cases this
      rfl
  match ts, h, hev with
  | [], _, _ => simp only [conj, Term.holds, Term.eval, bind, Except.bind, asBool, List.all_nil]
  | [e], h, _ => simpa [conj] using h e List.mem_cons_self
  | e₁ :: e₂ :: es, _, hev =>
    have hm : ∀ {l : List Term}, (∀ e ∈ l, Term.eval t e = .ok (.bool (p e))) →
        l.mapM (Term.eval t) = .ok (l.map fun e => .bool (p e)) := by
      intro l hl
      induction l with
      | nil => rfl
      | cons x l ih =>
        simp only [List.mapM_cons, hl x List.mem_cons_self, bind, Except.bind,
          ih fun e he => hl e (List.mem_cons_of_mem _ he), pure, Except.pure, List.map_cons]
    have hb : ∀ (l : List Term), (l.map fun e => Value.bool (p e)).mapM (asBool "and") =
        .ok (l.map p) := by
      intro l
      induction l with
      | nil => rfl
      | cons x l ih =>
        simp only [List.map_cons, List.mapM_cons, asBool, bind, Except.bind, ih, pure,
          Except.pure]
    have hall : ∀ (l : List Term), (l.map p).all id = l.all p := by
      intro l; induction l with
      | nil => rfl
      | cons x l ih => simp [List.all_cons, ih]
    simp only [conj, Term.holds, Term.eval, hm hev, bind, Except.bind]
    have : applyOp "and" ((e₁ :: e₂ :: es).map fun e => Value.bool (p e)) =
        .ok (.bool ((e₁ :: e₂ :: es).all p)) := by
      simp only [applyOp, hb, bind, Except.bind, pure, Except.pure, hall]
    rw [this]; rfl

theorem gamma_boolOr (res : String) (r : Finrel) :
    r.gamma [] (.agg "bool_or" (.val (.bool true))) res =
      .ok (Finrel.ofTuples [(res, .kind .bool)] [Tuple.ofPairs [(res, .bool !r.tuples.isEmpty)]]) := by
  have hm : ∀ (l : List Tuple), l.mapM (fun t => Term.eval t (.val (.bool true))) = .ok (l.map fun _ => .bool true) := by
    intro l; induction l with
    | nil => rfl
    | cons x l ih =>
      simp only [List.mapM_cons, Term.eval] at ih ⊢
      simp only [ih, bind, Except.bind, pure, Except.pure, List.map_cons]
  have hb : ∀ (l : List Tuple), (l.map fun _ => Value.bool true).mapM (asBool "bool_or") = .ok (l.map fun _ => true) := by
    intro l; induction l with
    | nil => rfl
    | cons x l ih => simp only [List.map_cons, List.mapM_cons, asBool, ih, bind, Except.bind, pure, Except.pure]
  have hany : ∀ (l : List Tuple), (l.map fun _ => true).any id = !l.isEmpty := by
    intro l; cases l <;> simp
  have hf : r.tuples.filter (fun t => (t.restrict []).isEmpty) = r.tuples := by
    apply List.filter_eq_self.mpr; intro t _; simp [Tuple.restrict]
  simp [Finrel.gamma, Finrel.gammaKeys, Agg.domain, Agg.bareAttrs, aggName, Agg.eval, aggregate, hm, hb, hany, hf, bind, Except.bind, pure, Except.pure, forIn]

theorem scalar_single (a : String) (d : Domain) (v : Value) :
    scalar (.finrel (Finrel.ofTuples [(a, d)] [Tuple.ofPairs [(a, v)]])) = .ok v := by
  have ht : (Finrel.ofTuples [(a, d)] [Tuple.ofPairs [(a, v)]]).tuples = [[(a, v)]] := by
    simp [Finrel.ofTuples, Finrel.tuples, Body.toList, Body.ofList, canon, dedup, Tuple.ofPairs,
      Quotient.lift, Quotient.mk]
  have ha : (Finrel.ofTuples [(a, d)] [Tuple.ofPairs [(a, v)]]).attrs = [a] := rfl
  simp only [scalar, Val.asFinrel, bind, Except.bind]
  rw [ha, ht]
  simp [Tuple.get?, pure, Except.pure]

/-- "Has a tuple", in a condition (where γ may leave its result unnamed). -/
theorem eval_nonEmpty {E : Env} {e : Expr} {r : Finrel}
    (he : Expr.eval (inCondition E) [] e = .ok (.finrel r)) :
    Cond.eval (inCondition E) [] (nonEmpty e) = .ok (!r.tuples.isEmpty) := by
  rw [nonEmpty, Cond.eval, Expr.eval]
  have hl : (inCondition E).lookup inConditionName = some (.db []) := by simp [inCondition]
  simp [he, hl, gamma_boolOr, scalar_single, Val.asFinrel, bind, Except.bind, pure, Except.pure, asBool]

end Rasso.ESO
