import ConstraintDB.Examples
import Rasso

/-!
# Dense-order generalized relations over ℚ, and Rasso's unrestricted relations

KKR's dense-order generalized relations over `Rat` translate into Rasso
unrestricted relations with rat headings. This file imports Rasso; Rasso knows nothing of
it. The name lemmas it uses (`GRel.names`, `GRel.sat_congr`) are in
`ConstraintDB/Dense.lean`.

Results, for a heading `h` of rat attributes with distinct names, and a relation `r` whose
names are all simple names of attributes of `h` (`RScoped h r`):

* `toUnrel_holds` (**faithful**): on a tuple `t` that fits `h`, `toUnrel h r` holds `t`
  exactly when `r` holds at `valOf t`, the valuation that reads `t`.
* `sat_iff_holds_tupleOf`: the converse: `r` holds at a valuation `v` exactly when
  `toUnrel h r` holds the tuple of `v`'s values on `h`.
* `toUnrel_dense`: the translation is in Rasso's dense-order class, so π never refuses it.
* `ofDense_sat`, `image` (**the image, up to points**): every relation in Rasso's
  dense-order class has the points of some translated relation.
* `projection_agrees`: Rasso's π of the translation holds exactly the points of GK's
  projection `GRel.elimAll`.

Names: ConstraintDB's attribute names are `Lean.Name`, Rasso's are `String`. A name is written as
the attribute `str n`; on simple names `str` and `Name.mkSimple` are inverse.
-/

namespace ConstraintDB.ToRasso

open Lean (Name)

/-! ## The translation -/

/-- A name as a Rasso attribute: a simple name is its string. -/
def str : Name → String
  | .str .anonymous s => s
  | n => n.toString

theorem str_mkSimple (b : String) : str (Name.mkSimple b) = b := rfl

def tTerm : ConstraintDB.Term Rat → Rasso.Term
  | .var n => .attr (str n)
  | .const q => .val (Rasso.Value.ofRat q)

def cmpRel : Cmp → Rasso.Dense.XRel
  | .lt => .lt | .le => .le | .eq => .eq

def tAtom (a : Atom Rat) : Rasso.Term := .call (cmpRel a.cmp).op [tTerm a.l, tTerm a.r]

def tTuple (g : GTuple (Atom Rat)) : Rasso.Term := .call "and" (g.map tAtom)

/-- A generalized relation as a Rasso term: an `or` of `and`s of comparisons. -/
def toTerm (r : GRel (Atom Rat)) : Rasso.Term := .call "or" (r.map tTuple)

/-- A generalized relation as a Rasso unrestricted relation over the heading `h`. -/
def toUnrel (h : Rasso.Heading) (r : GRel (Atom Rat)) : Rasso.Unrel := ⟨h, toTerm r⟩

/-- The valuation that reads a tuple: each name is the number at its attribute. -/
def valOf (t : Rasso.Tuple) : Val Rat := fun n => Rasso.Linear.sig t (str n)

/-- Every name `r` mentions is the simple name of an attribute of `h`. -/
def RScoped (h : Rasso.Heading) (r : GRel (Atom Rat)) : Prop :=
  ∀ n ∈ r.names, ∃ b ∈ h.attrs, n = Name.mkSimple b

/-! ## Faithful -/

section Faithful

variable {h : Rasso.Heading} {t : Rasso.Tuple}

theorem tTerm_eval (hr : h.AllRat) (f : t.Fits h) {x : ConstraintDB.Term Rat}
    (hx : ∀ n ∈ x.names, ∃ b ∈ h.attrs, n = Name.mkSimple b) :
    (tTerm x).eval t = .ok (Rasso.Value.ofRat (x.val (valOf t))) := by
  cases x with
  | var n =>
    obtain ⟨b, hb, rfl⟩ := hx n (by simp [Term.names])
    simp [tTerm, Rasso.Term.eval, str_mkSimple, Rasso.get_sig_rat hr f hb, ConstraintDB.Term.val, valOf]
  | const q => simp [tTerm, Rasso.Term.eval, ConstraintDB.Term.val]

theorem cmp_test (c : Cmp) (q q' : Rat) : (cmpRel c).test q q' = true ↔ c.holds q q' := by
  cases c <;> simp only [cmpRel, Rasso.Dense.XRel.test, Cmp.holds, decide_eq_true_eq] <;> grind

/-- The truth of an atom at a valuation, as a Boolean. -/
def abool (v : Val Rat) (a : Atom Rat) : Bool := (cmpRel a.cmp).test (a.l.val v) (a.r.val v)

theorem abool_iff (v : Val Rat) (a : Atom Rat) : abool v a = true ↔ Constraint.sat a v := by
  rw [abool, cmp_test, sat_def]

/-- The truth of a generalized relation at a valuation, as a Boolean. -/
def rbool (v : Val Rat) (r : GRel (Atom Rat)) : Bool := r.any fun g => g.all (abool v)

theorem rbool_iff (v : Val Rat) (r : GRel (Atom Rat)) : rbool v r = true ↔ GRel.Sat r v := by
  simp only [rbool, List.any_eq_true, List.all_eq_true, abool_iff, GRel.Sat, GTuple.Sat]

theorem atom_holds (hr : h.AllRat) (f : t.Fits h) {a : Atom Rat}
    (ha : ∀ n ∈ a.names, ∃ b ∈ h.attrs, n = Name.mkSimple b) :
    (tAtom a).holds t = .ok (abool (valOf t) a) :=
  Rasso.holds_cmp (cmpRel a.cmp)
    (tTerm_eval hr f fun n hn => ha n (by simp [Atom.names, hn]))
    (Rasso.Value.exact?_ofRat _)
    (tTerm_eval hr f fun n hn => ha n (by simp [Atom.names, hn]))
    (Rasso.Value.exact?_ofRat _)

theorem toTerm_holds (hr : h.AllRat) (f : t.Fits h) {r : GRel (Atom Rat)} (sc : RScoped h r) :
    (toTerm r).holds t = .ok (rbool (valOf t) r) := by
  have hg : ∀ g ∈ r, ∀ a ∈ g, ∀ n ∈ a.names, ∃ b ∈ h.attrs, n = Name.mkSimple b :=
    fun g hg a ha n hn => sc n (List.mem_flatMap.2 ⟨g, hg, List.mem_flatMap.2 ⟨a, ha, hn⟩⟩)
  have hT : ∀ g ∈ r, (tTuple g).holds t = .ok (g.all (abool (valOf t))) := by
    intro g hgr
    have hb : ∀ a ∈ g, Rasso.NF.bv t (tAtom a) = abool (valOf t) a :=
      fun a ha => Rasso.NF.bv_eq (atom_holds hr f (hg g hgr a ha))
    have hA : ∀ e ∈ g.map tAtom, e.holds t = .ok (Rasso.NF.bv t e) := by
      intro e he
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      rw [hb a ha]; exact atom_holds hr f (hg g hgr a ha)
    rw [tTuple, Rasso.holds_andN hA]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_map, List.all_eq_true, Function.comp_apply]
    exact ⟨fun H a ha => hb a ha ▸ H a ha, fun H a ha => (hb a ha).symm ▸ H a ha⟩
  have hb : ∀ g ∈ r, Rasso.NF.bv t (tTuple g) = g.all (abool (valOf t)) :=
    fun g hg => Rasso.NF.bv_eq (hT g hg)
  have hO : ∀ e ∈ r.map tTuple, e.holds t = .ok (Rasso.NF.bv t e) := by
    intro e he
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp he
    rw [hb g hg]; exact hT g hg
  rw [toTerm, Rasso.holds_orN hO]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [rbool, List.any_map, List.any_eq_true, Function.comp_apply]
  exact ⟨fun ⟨g, hg, H⟩ => ⟨g, hg, hb g hg ▸ H⟩, fun ⟨g, hg, H⟩ => ⟨g, hg, (hb g hg).symm ▸ H⟩⟩

/-- **Faithful.** On a tuple that fits the heading, the translation holds it exactly when
the generalized relation holds at the valuation that reads it. -/
theorem toUnrel_holds (hr : h.AllRat) (f : t.Fits h) {r : GRel (Atom Rat)} (sc : RScoped h r) :
    (toUnrel h r).Holds t ↔ GRel.Sat r (valOf t) := by
  simp only [Rasso.Unrel.Holds, toUnrel, toTerm_holds hr f sc, Except.ok.injEq, rbool_iff]
  exact ⟨fun h' => h'.2, fun h' => ⟨f, h'⟩⟩

end Faithful


/-! ## The class: π never refuses a translation -/

theorem tTerm_attrs {h : Rasso.Heading} {x : ConstraintDB.Term Rat}
    (hx : ∀ n ∈ x.names, ∃ b ∈ h.attrs, n = Name.mkSimple b) :
    ∀ b ∈ (tTerm x).attrs, b ∈ h.attrs := by
  intro b hb
  cases x with
  | var n =>
    obtain ⟨c, hc, rfl⟩ := hx n (by simp [Term.names])
    simp only [tTerm, Rasso.Term.attrs, str_mkSimple, List.mem_singleton] at hb
    subst hb; exact hc
  | const q => simp [tTerm, Rasso.Term.attrs] at hb

theorem tTerm_atomic (x : ConstraintDB.Term Rat) : Rasso.Atomic (tTerm x) := by
  cases x with
  | var n => exact .inl ⟨_, rfl⟩
  | const q => exact .inr ⟨_, rfl, by simp [Rasso.Value.exact?_ofRat]⟩

theorem toTerm_dense (r : GRel (Atom Rat)) : Rasso.DenseShaped (toTerm r) := by
  refine .or fun e he => ?_
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp he
  refine .and fun e he => ?_
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
  exact .cmp (Rasso.XRel.ofOp_op _) (tTerm_atomic _) (tTerm_atomic _)

/-- The translation of a scoped relation is in Rasso's dense-order class. -/
theorem toUnrel_dense {h : Rasso.Heading} (hn : h.attrs.Nodup) (hr : h.AllRat)
    {r : GRel (Atom Rat)} (sc : RScoped h r) : Rasso.DenseClass (toUnrel h r) := by
  refine ⟨⟨hn, fun b hb => ?_⟩, hr, toTerm_dense r⟩
  simp only [toUnrel, toTerm, tTuple, tAtom, Rasso.Term.attrs, List.flatMap_map,
    List.mem_flatMap, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hb
  obtain ⟨g, hg, a, ha, hb⟩ := hb
  have hs : ∀ n ∈ a.names, ∃ b ∈ h.attrs, n = Name.mkSimple b :=
    fun n hn => sc n (List.mem_flatMap.2 ⟨g, hg, List.mem_flatMap.2 ⟨a, ha, hn⟩⟩)
  rcases hb with hb | hb
  · exact tTerm_attrs (fun n hn' => hs n (by simp [Atom.names, hn'])) b hb
  · exact tTerm_attrs (fun n hn' => hs n (by simp [Atom.names, hn'])) b hb

/-! ## The tuple of a valuation -/

/-- The tuple over `h` that takes its numbers from `g`. -/
def tupleOf (h : Rasso.Heading) (g : String → Rat) : Rasso.Tuple :=
  Rasso.Tuple.ofPairs (h.map fun p => (p.1, Rasso.Value.ofRat (g p.1)))

theorem keys (h : Rasso.Heading) (g : String → Rat) :
    ((h.map fun p => (p.1, Rasso.Value.ofRat (g p.1))).map (·.1)) = h.attrs := by
  simp [Rasso.Heading.attrs, List.map_map, Function.comp_def]

theorem lookup_map (g : String → Rat) (a : String) : ∀ h : Rasso.Heading,
    (h.map fun p => (p.1, Rasso.Value.ofRat (g p.1))).lookup a =
      if a ∈ h.attrs then some (Rasso.Value.ofRat (g a)) else none
  | [] => by simp [Rasso.Heading.attrs]
  | (b, d) :: h => by
    by_cases e : a = b
    · subst e; simp [Rasso.Heading.attrs]
    · have := lookup_map g a h
      have hb : (a == b) = false := by simpa using e
      simp only [List.map_cons, List.lookup, Rasso.Heading.attrs, hb, List.mem_cons, e,
        false_or] at this ⊢
      exact this

theorem get?_tupleOf {h : Rasso.Heading} (hn : h.attrs.Nodup) (g : String → Rat) (a : String) :
    (tupleOf h g).get? a = if a ∈ h.attrs then some (Rasso.Value.ofRat (g a)) else none := by
  rw [tupleOf, Rasso.Tuple.get?_ofPairs (by rw [keys]; exact hn), lookup_map]

theorem tupleOf_fits {h : Rasso.Heading} (hn : h.attrs.Nodup) (hr : h.AllRat) (g : String → Rat) :
    (tupleOf h g).Fits h :=
  Rasso.Tuple.Fits.ofPairs (by rw [keys]; exact hn) (by intro a; rw [keys]) (by
    intro p hp d hd
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
    rw [hr.lookup hd]; exact Rasso.Dense.rat_has_ofRat _)

theorem sig_tupleOf {h : Rasso.Heading} (hn : h.attrs.Nodup) (g : String → Rat) {a : String}
    (ha : a ∈ h.attrs) : Rasso.Linear.sig (tupleOf h g) a = g a := by
  simp [Rasso.Linear.sig, get?_tupleOf hn, ha, Rasso.Value.exact?_ofRat]

/-- The restriction to `k` of the tuple of `g` on `h` is `t`, when `g` reads `t` on `k`. -/
theorem restrict_tupleOf {h k : Rasso.Heading} (hn : h.attrs.Nodup) {t : Rasso.Tuple}
    (ft : t.Fits k) (hk : ∀ a ∈ k.attrs, a ∈ h.attrs) (g : String → Rat)
    (hg : ∀ a ∈ k.attrs, (t.get? a).bind Rasso.Value.exact? = some (g a)) :
    (tupleOf h g).restrict k.attrs = t := by
  have hs : Rasso.Tuple.Sorted (tupleOf h g) := Rasso.Tuple.sorted_ofPairs (by rw [keys]; exact hn)
  refine Rasso.Tuple.ext_get? (Rasso.sorted_restrict hs) ft.sorted fun a => ?_
  rw [Rasso.get?_restrict, get?_tupleOf hn]
  by_cases ha : a ∈ k.attrs
  · rw [ite_eq_left ha, ite_eq_left (hk a ha)]
    have := hg a ha
    cases e : t.get? a with
    | none => rw [e] at this; cases this
    | some v =>
      rw [e] at this
      exact congrArg some (Rasso.Value.eq_ofRat this).symm
  · rw [ite_eq_right ha, ft.get?_none ha]

/-- The converse of faithfulness: `r` holds at `v` exactly when the translation holds the
tuple of `v`'s numbers on the heading. -/
theorem sat_iff_holds_tupleOf {h : Rasso.Heading} (hn : h.attrs.Nodup) (hr : h.AllRat)
    {r : GRel (Atom Rat)} (sc : RScoped h r) (v : Val Rat) :
    GRel.Sat r v ↔ (toUnrel h r).Holds (tupleOf h fun b => v (Name.mkSimple b)) := by
  rw [toUnrel_holds hr (tupleOf_fits hn hr _) sc]
  apply GRel.sat_congr
  intro n hn'
  obtain ⟨b, hb, rfl⟩ := sc n hn'
  simp only [valOf, str_mkSimple, sig_tupleOf hn _ hb]

/-! ## Projection agrees -/

theorem existsAll_iff_agree (U : Val Rat → Prop) :
    ∀ (zs : List Name) (v : Val Rat),
      existsAll zs U v ↔ ∃ w : Val Rat, (∀ n, n ∉ zs → w n = v n) ∧ U w
  | [], v => by
    simp only [existsAll]
    constructor
    · intro h; exact ⟨v, fun _ _ => rfl, h⟩
    · rintro ⟨w, hw, hu⟩
      have : w = v := funext fun n => hw n (by simp)
      exact this ▸ hu
  | z :: zs, v => by
    simp only [existsAll]
    constructor
    · rintro ⟨d, hd⟩
      obtain ⟨w, hw, hu⟩ := (existsAll_iff_agree U zs _).1 hd
      refine ⟨w, fun n hn => ?_, hu⟩
      have hz : n ≠ z := fun e => hn (e ▸ List.mem_cons_self)
      have hzs : n ∉ zs := fun h => hn (List.mem_cons_of_mem _ h)
      rw [hw n hzs]; simp [Val.upd, hz]
    · rintro ⟨w, hw, hu⟩
      refine ⟨w z, (existsAll_iff_agree U zs _).2 ⟨w, fun n hn => ?_, hu⟩⟩
      by_cases hz : n = z
      · subst hz; simp [Val.upd]
      · simp only [Val.upd, hz, ite_false]
        exact hw n (by simp [hz, hn])

/-- The names GK's projection removes: the simple names of the attributes π drops. -/
def dropped (h : Rasso.Heading) (as : List String) : List Name :=
  (h.attrs.filter (· ∉ as)).map Name.mkSimple

theorem mem_dropped {h : Rasso.Heading} {as : List String} {b : String} (hb : b ∈ h.attrs) :
    Name.mkSimple b ∈ dropped h as ↔ b ∉ as := by
  simp only [dropped, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨c, ⟨_, hc⟩, e⟩
    have : c = b := by simpa [Name.mkSimple] using e
    exact this ▸ hc
  · intro h'; exact ⟨b, ⟨hb, h'⟩, rfl⟩

/-- **Projection agrees.** π of the translation succeeds, and its result holds exactly the
points of GK's projection `GRel.elimAll`: the same points, not the same syntax. -/
theorem projection_agrees {h : Rasso.Heading} (hn : h.attrs.Nodup) (hr : h.AllRat)
    {r : GRel (Atom Rat)} (sc : RScoped h r) {as : List String} (hnd : as.Nodup)
    (hin : ∀ a ∈ as, a ∈ h.attrs) :
    ∃ w, (toUnrel h r).project as = .ok w ∧
      ∀ t, w.Holds t ↔ t.Fits w.heading ∧ GRel.Sat (GRel.elimAll (dropped h as) r) (valOf t) := by
  have hu := toUnrel_dense hn hr sc
  obtain ⟨w, hw⟩ := hu.project_ok hnd hin
  refine ⟨w, hw, fun t => ?_⟩
  obtain ⟨_, _, hsound⟩ := Rasso.project_sound hw hu.wf hu.total
  have hwr := (hu.project hw).rat
  have hk : w.heading.attrs = as := Rasso.Heading.pick_attrs (Rasso.project_pick hw)
  rw [GRel.sat_elimAll, existsAll_iff_agree]
  constructor
  · intro hwt
    refine ⟨hwt.1, ?_⟩
    obtain ⟨s, hs, hst⟩ := (hsound t).mp hwt
    have hsat := (toUnrel_holds hr hs.1 sc).mp hs
    refine ⟨fun n => if n ∈ dropped h as then valOf s n else valOf t n, fun n hn' => by
      simp [hn'], (GRel.sat_congr fun n hn' => ?_).mp hsat⟩
    obtain ⟨b, hb, rfl⟩ := sc n hn'
    by_cases hd : Name.mkSimple b ∈ dropped h as
    · simp [hd]
    · simp only [hd, ite_false, valOf, str_mkSimple, Rasso.Linear.sig]
      have hba : b ∈ as := Classical.byContradiction fun h' => hd ((mem_dropped hb).mpr h')
      rw [← hst, Rasso.get?_restrict, ite_eq_left hba]
  · rintro ⟨ft, v', hv', hsat⟩
    let g : String → Rat := fun b => if b ∈ as then Rasso.Linear.sig t b else v' (Name.mkSimple b)
    have hs : (toUnrel h r).Holds (tupleOf h g) := by
      rw [toUnrel_holds hr (tupleOf_fits hn hr g) sc]
      refine (GRel.sat_congr fun n hn' => ?_).mp hsat
      obtain ⟨b, hb, rfl⟩ := sc n hn'
      simp only [valOf, str_mkSimple, sig_tupleOf hn g hb, g]
      by_cases hba : b ∈ as
      · rw [ite_eq_left hba, hv' _ (fun h' => (mem_dropped hb).mp h' hba)]
        rfl
      · rw [ite_eq_right hba]
    refine (hsound t).mpr ⟨tupleOf h g, hs, ?_⟩
    rw [← hk]
    refine restrict_tupleOf hn ft (fun a ha => hin a (hk ▸ ha)) g fun a ha => ?_
    have hga : g a = Rasso.Linear.sig t a := by simp [g, hk ▸ ha]
    rw [hga, Rasso.get_sig_rat hwr ft ha]
    simp [Rasso.Value.exact?_ofRat]

/-! ## The image: every dense-order relation, up to points -/

/-- An operand of a dense-shaped comparison as a ConstraintDB term. -/
def tOp : Rasso.Term → Option (ConstraintDB.Term Rat)
  | .attr b => some (.var (Name.mkSimple b))
  | .val v => v.exact?.map .const
  | _ => none

/-- A comparison of two operands as a generalized relation. -/
def cmpOf (op : String) (es : List Rasso.Term) : GRel (Atom Rat) :=
  match Rasso.Dense.XRel.ofOp op, es with
  | some r, [l, r'] =>
    match tOp l, tOp r' with
    | some a, some b =>
      match r with
      | .lt => [[⟨.lt, a, b⟩]] | .le => [[⟨.le, a, b⟩]] | .eq => [[⟨.eq, a, b⟩]]
      | .ge => [[⟨.le, b, a⟩]] | .gt => [[⟨.lt, b, a⟩]]
    | _, _ => GRel.bot
  | _, _ => GRel.bot

mutual
/-- A dense-shaped Rasso term as a generalized relation (DNF). -/
def ofDense : Rasso.Term → GRel (Atom Rat)
  | .val (.bool b) => if b then GRel.top else GRel.bot
  | .call op es =>
    if op = "and" then interAll es
    else if op = "or" then unionAll es
    else if op = "not" then notOf es
    else cmpOf op es
  | _ => GRel.bot

def interAll : List Rasso.Term → GRel (Atom Rat)
  | [] => GRel.top
  | e :: es => GRel.inter (ofDense e) (interAll es)

def unionAll : List Rasso.Term → GRel (Atom Rat)
  | [] => GRel.bot
  | e :: es => GRel.union (ofDense e) (unionAll es)

def notOf : List Rasso.Term → GRel (Atom Rat)
  | [e] => GRel.compl (ofDense e)
  | _ => GRel.bot
end

/-- Every atom of a generalized relation has the property `Q`. -/
def AllAtoms (Q : Atom Rat → Prop) (r : GRel (Atom Rat)) : Prop := ∀ g ∈ r, ∀ a ∈ g, Q a

section AllAtoms

variable {Q : Atom Rat → Prop}

theorem allAtoms_top : AllAtoms Q GRel.top := by simp [AllAtoms, GRel.top]
theorem allAtoms_bot : AllAtoms Q GRel.bot := by simp [AllAtoms, GRel.bot]

theorem allAtoms_union {r s : GRel (Atom Rat)} (hr : AllAtoms Q r) (hs : AllAtoms Q s) :
    AllAtoms Q (GRel.union r s) := by
  intro g hg a ha
  rcases List.mem_append.mp hg with hg | hg
  · exact hr g hg a ha
  · exact hs g hg a ha

theorem allAtoms_inter {r s : GRel (Atom Rat)} (hr : AllAtoms Q r) (hs : AllAtoms Q s) :
    AllAtoms Q (GRel.inter r s) := by
  intro g hg a ha
  obtain ⟨g₁, h₁, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨g₂, h₂, rfl⟩ := List.mem_map.mp hg
  rcases List.mem_append.mp ha with ha | ha
  · exact hr g₁ h₁ a ha
  · exact hs g₂ h₂ a ha

theorem allAtoms_compl (hneg : ∀ a, Q a → AllAtoms Q (NegDNF.neg (P := Val Rat) a)) :
    ∀ {r : GRel (Atom Rat)}, AllAtoms Q r → AllAtoms Q (GRel.compl r)
  | [], _ => allAtoms_top
  | g :: r, h => by
    refine allAtoms_inter ?_ (allAtoms_compl hneg fun g' hg' => h g' (by simp [hg']))
    intro g' hg' a ha
    obtain ⟨b, hb, hg'⟩ := List.mem_flatMap.mp hg'
    exact hneg b (h g (by simp) b hb) g' hg' a ha

end AllAtoms

/-- The names of an atom are simple names of attributes in `S`. -/
def NamesIn (S : List String) (a : Atom Rat) : Prop :=
  ∀ n ∈ a.names, ∃ b ∈ S, n = Name.mkSimple b

theorem namesIn_neg {S : List String} (a : Atom Rat) (ha : NamesIn S a) :
    AllAtoms (NamesIn S) (NegDNF.neg (P := Val Rat) a) := by
  obtain ⟨c, l, r⟩ := a
  have sw : ∀ (c' : Cmp), NamesIn S ⟨c', r, l⟩ := fun c' n hn =>
    ha n (by simp only [Atom.names, List.mem_append] at hn ⊢; exact hn.symm)
  have same : ∀ (c' : Cmp), NamesIn S ⟨c', l, r⟩ := fun c' n hn => ha n hn
  intro g hg a' ha'
  cases c <;> simp [NegDNF.neg] at hg <;>
    (try rcases hg with rfl | rfl) <;> (try subst hg) <;> simp at ha' <;> subst ha' <;>
    first | exact sw _ | exact same _

theorem allAtoms_scoped {h : Rasso.Heading} {r : GRel (Atom Rat)}
    (hr : AllAtoms (NamesIn h.attrs) r) : RScoped h r := by
  intro n hn
  obtain ⟨g, hg, hn⟩ := List.mem_flatMap.mp hn
  obtain ⟨a, ha, hn⟩ := List.mem_flatMap.mp hn
  exact hr g hg a ha n hn

section Image

variable {h : Rasso.Heading} {t : Rasso.Tuple}

theorem tOp_atomic {o : Rasso.Term} (ho : Rasso.Atomic o) : ∃ x, tOp o = some x := by
  rcases ho with ⟨b, rfl⟩ | ⟨v, rfl, hv⟩
  · exact ⟨_, rfl⟩
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hv
    exact ⟨.const q, by simp [tOp, hq]⟩

theorem tOp_names {o : Rasso.Term} {x : ConstraintDB.Term Rat} (hx : tOp o = some x)
    (hR : ∀ b ∈ o.attrs, b ∈ h.attrs) : ∀ n ∈ x.names, ∃ b ∈ h.attrs, n = Name.mkSimple b := by
  intro n hn
  cases o with
  | attr b =>
    simp only [tOp, Option.some.injEq] at hx; subst hx
    simp only [Term.names, List.mem_singleton] at hn; subst hn
    exact ⟨b, hR b (by simp [Rasso.Term.attrs]), rfl⟩
  | val v =>
    simp only [tOp, Option.map_eq_some_iff] at hx
    obtain ⟨q, _, rfl⟩ := hx
    simp [Term.names] at hn
  | _ => simp [tOp] at hx

theorem tOp_eval (hr : h.AllRat) (f : t.Fits h) {o : Rasso.Term} {x : ConstraintDB.Term Rat}
    (hx : tOp o = some x) (hR : ∀ b ∈ o.attrs, b ∈ h.attrs) :
    ∃ v, o.eval t = .ok v ∧ v.exact? = some (x.val (valOf t)) := by
  cases o with
  | attr b =>
    simp only [tOp, Option.some.injEq] at hx; subst hx
    refine ⟨Rasso.Value.ofRat (Rasso.Linear.sig t b),
      by simp [Rasso.Term.eval, Rasso.get_sig_rat hr f (hR b (by simp [Rasso.Term.attrs]))], ?_⟩
    simp [Rasso.Value.exact?_ofRat, ConstraintDB.Term.val, valOf, str_mkSimple]
  | val v =>
    simp only [tOp, Option.map_eq_some_iff] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨v, by simp [Rasso.Term.eval], by simp [hq, ConstraintDB.Term.val]⟩
  | _ => simp [tOp] at hx

theorem sat_single (a : Atom Rat) (v : Val Rat) : GRel.Sat [[a]] v ↔ Constraint.sat a v := by
  simp [GRel.Sat, GTuple.Sat]

/-- What the image needs of a dense-shaped term: its translation has the term's truth value,
and reads only simple names of the heading. -/
theorem ofDense_sat (hr : h.AllRat) (f : t.Fits h) :
    ∀ {e : Rasso.Term}, Rasso.DenseShaped e → (∀ b ∈ e.attrs, b ∈ h.attrs) →
      (GRel.Sat (ofDense e) (valOf t) ↔ e.holds t = .ok true) ∧
        AllAtoms (NamesIn h.attrs) (ofDense e) := by
  intro e he
  induction he with
  | const b =>
    intro _
    have hb : (Rasso.Term.val (.bool b)).holds t = .ok b :=
      Rasso.Term.holds_ok.mpr (by simp [Rasso.Term.eval])
    cases b
    · simp only [ofDense, Bool.false_eq_true, ite_false, hb]
      exact ⟨⟨fun h' => absurd h' (GRel.sat_bot _), fun h' => by simp at h'⟩, allAtoms_bot⟩
    · simp only [ofDense, ite_true, hb]
      exact ⟨⟨fun _ => by simp, fun _ => GRel.sat_top _⟩, allAtoms_top⟩
  | @and es hes ih =>
    intro hR
    have hall : ∀ l ⊆ es, (GRel.Sat (interAll l) (valOf t) ↔ ∀ x ∈ l, x.holds t = .ok true) ∧
        AllAtoms (NamesIn h.attrs) (interAll l) := by
      intro l
      induction l with
      | nil =>
        intro _
        exact ⟨⟨fun _ x hx => absurd hx List.not_mem_nil, fun _ => GRel.sat_top _⟩, allAtoms_top⟩
      | cons x l ihl =>
        intro hl
        have hx : x ∈ es := hl List.mem_cons_self
        obtain ⟨h1, h2⟩ := ih x hx (Rasso.NF.attrs_sub_call hx hR)
        obtain ⟨h3, h4⟩ := ihl fun y hy => hl (List.mem_cons_of_mem _ hy)
        refine ⟨?_, allAtoms_inter h2 h4⟩
        simp only [interAll, GRel.sat_inter, h1, h3, List.mem_cons, forall_eq_or_imp]
    obtain ⟨h1, h2⟩ := hall es (fun _ hx => hx)
    have hg : ∀ x ∈ es, x.holds t = .ok (Rasso.NF.bv t x) := fun x hx => by
      obtain ⟨b, hb⟩ := (hes x hx).total hr f (Rasso.NF.attrs_sub_call hx hR)
      rw [hb, Rasso.NF.bv_eq hb]
    simp only [ofDense, ite_true, Rasso.holds_andN hg, Except.ok.injEq, List.all_eq_true]
    refine ⟨h1.trans ⟨fun H x hx => ?_, fun H x hx => ?_⟩, h2⟩
    · have := H x hx; rw [hg x hx] at this; exact Except.ok.inj this
    · rw [hg x hx, H x hx]
  | @or es hes ih =>
    intro hR
    have hall : ∀ l ⊆ es, (GRel.Sat (unionAll l) (valOf t) ↔ ∃ x ∈ l, x.holds t = .ok true) ∧
        AllAtoms (NamesIn h.attrs) (unionAll l) := by
      intro l
      induction l with
      | nil =>
        intro _
        exact ⟨⟨fun h' => absurd h' (GRel.sat_bot _),
          fun ⟨_, hx, _⟩ => absurd hx List.not_mem_nil⟩, allAtoms_bot⟩
      | cons x l ihl =>
        intro hl
        have hx : x ∈ es := hl List.mem_cons_self
        obtain ⟨h1, h2⟩ := ih x hx (Rasso.NF.attrs_sub_call hx hR)
        obtain ⟨h3, h4⟩ := ihl fun y hy => hl (List.mem_cons_of_mem _ hy)
        refine ⟨?_, allAtoms_union h2 h4⟩
        simp only [unionAll, GRel.sat_union, h1, h3, List.mem_cons, exists_eq_or_imp]
    obtain ⟨h1, h2⟩ := hall es (fun _ hx => hx)
    have hg : ∀ x ∈ es, x.holds t = .ok (Rasso.NF.bv t x) := fun x hx => by
      obtain ⟨b, hb⟩ := (hes x hx).total hr f (Rasso.NF.attrs_sub_call hx hR)
      rw [hb, Rasso.NF.bv_eq hb]
    have hor : ("or" = "and") = False := by decide
    simp only [ofDense, hor, ite_false, ite_true, Rasso.holds_orN hg, Except.ok.injEq,
      List.any_eq_true]
    refine ⟨h1.trans ⟨fun ⟨x, hx, H⟩ => ⟨x, hx, ?_⟩, fun ⟨x, hx, H⟩ => ⟨x, hx, ?_⟩⟩, h2⟩
    · rw [hg x hx] at H; exact Except.ok.inj H
    · rw [hg x hx, H]
  | @not e he ih =>
    intro hR
    obtain ⟨h1, h2⟩ := ih (Rasso.NF.attrs_sub_call List.mem_cons_self hR)
    obtain ⟨b, hb⟩ := he.total hr f (Rasso.NF.attrs_sub_call List.mem_cons_self hR)
    have hn : (Rasso.Term.call "not" [e]).holds t = .ok (!b) :=
      Rasso.holds_not1.mpr ⟨b, hb, rfl⟩
    have h1' : ("not" = "and") = False := by decide
    have h2' : ("not" = "or") = False := by decide
    simp only [ofDense, h1', h2', ite_false, ite_true, notOf, hn]
    refine ⟨?_, allAtoms_compl namesIn_neg h2⟩
    rw [GRel.sat_compl, h1, hb]
    cases b <;> simp
  | @cmp op r l r' hop hl hr' =>
    intro hR
    have hRl : ∀ b ∈ l.attrs, b ∈ h.attrs := Rasso.NF.attrs_sub_call List.mem_cons_self hR
    have hRr : ∀ b ∈ r'.attrs, b ∈ h.attrs :=
      Rasso.NF.attrs_sub_call (List.mem_cons_of_mem _ List.mem_cons_self) hR
    obtain ⟨x, hx⟩ := tOp_atomic hl
    obtain ⟨y, hy⟩ := tOp_atomic hr'
    obtain ⟨v, hv, hq⟩ := tOp_eval hr f hx hRl
    obtain ⟨w, hw, hq'⟩ := tOp_eval hr f hy hRr
    obtain ⟨n1, n2, n3⟩ := Rasso.Dense.XRel.ofOp_ne hop
    have hop' := Rasso.Dense.XRel.ofOp_some hop
    have hc : ofDense (.call op [l, r']) = cmpOf op [l, r'] := by simp [ofDense, n1, n2, n3]
    have hxn := tOp_names hx hRl
    have hyn := tOp_names hy hRr
    have nm : ∀ (c : Cmp) (p q : ConstraintDB.Term Rat), (∀ n ∈ p.names, ∃ b ∈ h.attrs, n = Name.mkSimple b) →
        (∀ n ∈ q.names, ∃ b ∈ h.attrs, n = Name.mkSimple b) →
        AllAtoms (NamesIn h.attrs) [[⟨c, p, q⟩]] := by
      intro c p q hp hq g hg a ha n hn
      simp only [List.mem_singleton] at hg; subst hg
      simp only [List.mem_singleton] at ha; subst ha
      simp only [Atom.names, List.mem_append] at hn
      exact hn.elim (hp n) (hq n)
    rw [hc]
    simp only [cmpOf, hop, hx, hy]
    rw [hop', Rasso.holds_cmp r hv hq hw hq']
    cases r <;> simp only [sat_single, sat_def, Cmp.holds, Rasso.Dense.XRel.test, Except.ok.injEq,
      decide_eq_true_eq]
    · exact ⟨by first | trivial | exact Iff.rfl | grind, nm _ _ _ hxn hyn⟩
    · exact ⟨by first | trivial | exact Iff.rfl | grind, nm _ _ _ hxn hyn⟩
    · exact ⟨by first | trivial | exact Iff.rfl | grind, nm _ _ _ hxn hyn⟩
    · exact ⟨by first | trivial | exact Iff.rfl | grind, nm _ _ _ hyn hxn⟩
    · exact ⟨by first | trivial | exact Iff.rfl | grind, nm _ _ _ hyn hxn⟩

end Image

theorem ofDense_names {h : Rasso.Heading} :
    ∀ {e : Rasso.Term}, Rasso.DenseShaped e → (∀ b ∈ e.attrs, b ∈ h.attrs) →
      AllAtoms (NamesIn h.attrs) (ofDense e) := by
  intro e he
  induction he with
  | const b => intro _; cases b <;> simp only [ofDense] <;> first | exact allAtoms_top | exact allAtoms_bot
  | @and es _ ih =>
    intro hR
    have : ∀ l ⊆ es, AllAtoms (NamesIn h.attrs) (interAll l) := by
      intro l; induction l with
      | nil => intro _; exact allAtoms_top
      | cons x l ihl =>
        intro hl
        exact allAtoms_inter (ih x (hl List.mem_cons_self)
          (Rasso.NF.attrs_sub_call (hl List.mem_cons_self) hR))
          (ihl fun y hy => hl (List.mem_cons_of_mem _ hy))
    simp only [ofDense, ite_true]; exact this es (fun _ h => h)
  | @or es _ ih =>
    intro hR
    have : ∀ l ⊆ es, AllAtoms (NamesIn h.attrs) (unionAll l) := by
      intro l; induction l with
      | nil => intro _; exact allAtoms_bot
      | cons x l ihl =>
        intro hl
        exact allAtoms_union (ih x (hl List.mem_cons_self)
          (Rasso.NF.attrs_sub_call (hl List.mem_cons_self) hR))
          (ihl fun y hy => hl (List.mem_cons_of_mem _ hy))
    have hor : ("or" = "and") = False := by decide
    simp only [ofDense, hor, ite_false, ite_true]; exact this es (fun _ h => h)
  | @not e _ ih =>
    intro hR
    have h1' : ("not" = "and") = False := by decide
    have h2' : ("not" = "or") = False := by decide
    simp only [ofDense, h1', h2', ite_false, ite_true, notOf]
    exact allAtoms_compl namesIn_neg (ih (Rasso.NF.attrs_sub_call List.mem_cons_self hR))
  | @cmp op r l r' hop hl hr' =>
    intro hR
    obtain ⟨x, hx⟩ := tOp_atomic hl
    obtain ⟨y, hy⟩ := tOp_atomic hr'
    have hxn := tOp_names hx (Rasso.NF.attrs_sub_call List.mem_cons_self hR)
    have hyn := tOp_names hy (Rasso.NF.attrs_sub_call (List.mem_cons_of_mem _ List.mem_cons_self) hR)
    obtain ⟨n1, n2, n3⟩ := Rasso.Dense.XRel.ofOp_ne hop
    have nm : ∀ (c : Cmp) (p q : ConstraintDB.Term Rat), (∀ n ∈ p.names, ∃ b ∈ h.attrs, n = Name.mkSimple b) →
        (∀ n ∈ q.names, ∃ b ∈ h.attrs, n = Name.mkSimple b) →
        AllAtoms (NamesIn h.attrs) [[⟨c, p, q⟩]] := by
      intro c p q hp hq g hg a ha n hn
      simp only [List.mem_singleton] at hg; subst hg
      simp only [List.mem_singleton] at ha; subst ha
      simp only [Atom.names, List.mem_append] at hn
      exact hn.elim (hp n) (hq n)
    simp only [ofDense, n1, n2, n3, ite_false, cmpOf, hop, hx, hy]
    cases r
    · exact nm _ _ _ hxn hyn
    · exact nm _ _ _ hxn hyn
    · exact nm _ _ _ hxn hyn
    · exact nm _ _ _ hyn hxn
    · exact nm _ _ _ hyn hxn

/-- **The image, up to points.** Every relation in Rasso's dense-order class has the points
of the translation of a generalized relation: `ofDense` of its term. -/
theorem image {u : Rasso.Unrel} (hu : Rasso.DenseClass u) :
    RScoped u.heading (ofDense u.term) ∧
      ∀ t, u.Holds t ↔ (toUnrel u.heading (ofDense u.term)).Holds t := by
  have sc0 : RScoped u.heading (ofDense u.term) :=
    allAtoms_scoped (ofDense_names hu.shaped hu.wf.reads)
  refine ⟨sc0, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · rw [toUnrel_holds hu.rat ht.1 sc0]
    exact (ofDense_sat hu.rat ht.1 hu.shaped hu.wf.reads).1.mpr ht.2
  · have f : t.Fits u.heading := ht.1
    rw [toUnrel_holds hu.rat f sc0] at ht
    exact ⟨f, (ofDense_sat hu.rat f hu.shaped hu.wf.reads).1.mp ht⟩

/-! ## Examples

Each `#guard` runs when the file is built. `between` is `x < z ∧ z < y`. Its translation
holds the same test tuples as the generalized relation, and π of it, keeping `x` and `y`,
holds the same test tuples as GK's projection `GRel.elimAll [`z]`. -/

section Examples

private def hxyz : Rasso.Heading := [("x", .kind .rat), ("y", .kind .rat), ("z", .kind .rat)]

private def between : GRel (Atom Rat) := [[⟨.lt, .var `x, .var `z⟩, ⟨.lt, .var `z, .var `y⟩]]

private def tup (x y z : Rat) : Rasso.Tuple :=
  [("x", Rasso.Value.ofRat x), ("y", Rasso.Value.ofRat y), ("z", Rasso.Value.ofRat z)]

private def tup2 (x y : Rat) : Rasso.Tuple := [("x", Rasso.Value.ofRat x), ("y", Rasso.Value.ofRat y)]

private def okIs : Except String Bool → Bool → Bool
  | .ok a, b => a == b
  | .error _, _ => false

private def tests : List (Rat × Rat × Rat) :=
  [(0, 1, 1/2), (0, 1, 2), (1, 0, 1/2), (0, 0, 0), (-1, 3, 0), (2, 2, 2), (0, 1/100, 1/200)]

-- The translation: an `or` of one `and` of two comparisons.
#guard toTerm between == .call "or" [.call "and"
  [.call "<" [.attr "x", .attr "z"], .call "<" [.attr "z", .attr "y"]]]

-- Faithful on the test tuples.
#guard tests.all fun (x, y, z) =>
  okIs ((toTerm between).holds (tup x y z)) (rbool (valOf (tup x y z)) between)

-- π keeping `x` and `y` succeeds, and holds the test tuples that GK's projection holds.
#guard match (toUnrel hxyz between).project ["x", "y"] with
  | .ok w => tests.all fun (x, y, _) =>
      okIs (w.term.holds (tup2 x y)) (rbool (valOf (tup2 x y)) (GRel.elimAll [`z] between))
  | .error _ => false

-- GK's projection is `x < y`; at `(0, 1)` both hold, at `(1, 0)` neither does.
#guard GRel.elimAll [`z] between == [[⟨.lt, .var `x, .var `y⟩]]

end Examples

end ConstraintDB.ToRasso
