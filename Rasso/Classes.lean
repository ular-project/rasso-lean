import Rasso.Subst
import Rasso.Dense
import Rasso.Equality
import Rasso.Linear

/-!
# Rasso: the classes, the recogniser and π, proved

The executable part is `Rasso.Project`. This module proves:

* `Term.eval_subst`: substitution is evaluation at the updated tuple.
* For each class, its specification `Class.Accepts`, the test's `iff` lemma, and the
  soundness of its removal (`Class.elimTerm_sound`): the one obligation a new class meets.
* `recognise_ok_iff`: the recogniser returns the first class whose specification holds.
* **Agreement** (`project_ok_iff`): π on an unrestricted relation succeeds exactly when
  its checks pass and every removal finds a class.
* **Soundness** (`project_sound`): on a well-formed, total operand, π's result is well
  formed and total, and holds exactly the restrictions of what the operand holds.
* The finite class as a global class (`FiniteClass`): kept by σ, ρ, ⋈, ∪, ∩, − and π.

Conventions:

* Soundness is for total operands. π does not check totality.
* The recogniser is sound, not complete: a relation in no class
  may still have a projection, and π refuses it.
-/

namespace Rasso

/-! ## The classes -/

/-- What each class needs of a relation and a dropped attribute. -/
def Class.Accepts : Class → Unrel → String → Prop
  | .finite, u, a => ∃ d vs, u.heading.lookup a = some d ∧ d.values? = some vs
  | .dense, u, a => u.heading.lookup a = some (.kind .rat) ∧ Dense.DenseIn u.heading a u.term
  | .equality, u, a => ∃ d, u.heading.lookup a = some d ∧ Equality.infinite? d = true ∧
      Equality.EqIn u.heading a d u.term
  | .linear, u, a => u.heading.lookup a = some (.kind .rat) ∧ Linear.LinIn u.heading a u.term

theorem Class.accepts?_iff {c : Class} {u : Unrel} {a : String} :
    c.accepts? u a = true ↔ c.Accepts u a := by
  cases c
  case dense =>
    simp only [Class.accepts?, Class.Accepts, Bool.and_eq_true, beq_iff_eq, Dense.accepts_iff]
  case equality =>
    simp only [Class.accepts?, Class.Accepts]
    cases hd : u.heading.lookup a with
    | none => simp
    | some d =>
      simp only [Bool.and_eq_true, Equality.accepts_iff, Option.some.injEq, exists_eq_left']
  case linear =>
    simp only [Class.accepts?, Class.Accepts, Bool.and_eq_true, beq_iff_eq, Linear.accepts_iff]
  simp only [Class.accepts?, Class.Accepts, Unrel.values?, Option.isSome_iff_exists,
    Option.bind_eq_some_iff]
  constructor
  · rintro ⟨vs, d, hd, hv⟩; exact ⟨d, vs, hd, hv⟩
  · rintro ⟨d, vs, hd, hv⟩; exact ⟨vs, d, hd, hv⟩

/-- `c` is the first class of `l` whose specification holds. -/
def Class.FirstIn : List Class → Unrel → String → Class → Prop
  | [], _, _, _ => False
  | c' :: l, u, a, c => (c'.Accepts u a ∧ c = c') ∨ (¬ c'.Accepts u a ∧ Class.FirstIn l u a c)

theorem find?_firstIn {u : Unrel} {a : String} {c : Class} :
    ∀ (l : List Class), l.find? (·.accepts? u a) = some c ↔ Class.FirstIn l u a c
  | [] => by simp [Class.FirstIn]
  | c' :: l => by
    simp only [List.find?_cons, Class.FirstIn]
    cases h : c'.accepts? u a
    · have hn : ¬ c'.Accepts u a := fun h' => by rw [Class.accepts?_iff.mpr h'] at h; cases h
      simp only [hn, false_and, not_false_eq_true, true_and, false_or]
      exact find?_firstIn l
    · have hy : c'.Accepts u a := Class.accepts?_iff.mp h
      simp only [hy, true_and, not_true_eq_false, false_and, or_false]
      exact ⟨fun e => (Option.some.inj e).symm, fun e => e ▸ rfl⟩

/-- The recogniser returns the first class, in the order of `Class.all`, whose
specification holds; it refuses exactly when none holds. -/
theorem recognise_ok_iff {u : Unrel} {a : String} {c : Class} :
    recognise u a = .ok c ↔ Class.FirstIn Class.all u a c := by
  rw [← find?_firstIn]
  unfold recognise
  split
  · rename_i c' hc'
    rw [hc']
    exact ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩
  · rename_i hn
    rw [hn]
    simp

theorem Class.FirstIn.accepts {l : List Class} {u : Unrel} {a : String} {c : Class} :
    Class.FirstIn l u a c → c.Accepts u a := by
  induction l with
  | nil => intro h; cases h
  | cons c' l ih =>
    rintro (⟨h, rfl⟩ | ⟨_, h⟩)
    · exact h
    · exact ih h

/-- Some class accepts exactly when the recogniser returns one. -/
theorem recognise_ok_exists {u : Unrel} {a : String} :
    (∃ c, recognise u a = .ok c) ↔ ∃ c ∈ Class.all, c.Accepts u a := by
  simp only [recognise_ok_iff]
  constructor
  · rintro ⟨c, h⟩
    refine ⟨c, ?_, h.accepts⟩
    have : ∀ l : List Class, Class.FirstIn l u a c → c ∈ l := by
      intro l; induction l with
      | nil => intro h; cases h
      | cons c' l ih =>
        rintro (⟨_, rfl⟩ | ⟨_, h⟩)
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h)
    exact this _ h
  · rintro ⟨c, hc, ha⟩
    have : ∀ l : List Class, c ∈ l → ∃ c', Class.FirstIn l u a c' := by
      intro l; induction l with
      | nil => intro h; cases h
      | cons c' l ih =>
        intro hm
        by_cases h' : c'.Accepts u a
        · exact ⟨c', .inl ⟨h', rfl⟩⟩
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact absurd ha h'
          · obtain ⟨c'', h''⟩ := ih hm; exact ⟨c'', .inr ⟨h', h''⟩⟩
    exact this _ hc

/-! ## The finite class is sound -/

/-- The soundness of a class's removal: the obligation each class meets. The removed
relation reads only its own attributes, is total, and holds a tuple exactly when the
operand holds it with some value for the removed attribute. -/
theorem Class.elimTerm_sound {c : Class} {u : Unrel} {a : String} (hc : c.Accepts u a)
    (hu : u.WF) (tu : u.Total) :
    (∀ x ∈ (u.dropOne a c).term.attrs, x ∈ (u.dropOne a c).heading.attrs) ∧
      (u.dropOne a c).Total ∧
      ∀ t, t.Fits (u.dropOne a c).heading →
        ((u.dropOne a c).Holds t ↔ ∃ v, u.Holds (t.set a v)) := by
  cases c
  case dense => exact Dense.elim_sound hc.1 hc.2 hu tu
  case equality =>
    obtain ⟨d, hd, hinf, hin⟩ := hc
    exact Equality.elim_sound hd hinf hin hu tu
  case linear => exact Linear.elim_sound hc.1 hc.2 hu tu
  obtain ⟨d, vs, hd, hvs⟩ := hc
  have hval : u.values? a = some vs := by simp [Unrel.values?, hd, hvs]
  have hfa : ∀ y, y ∈ Heading.attrs (u.heading.filter (·.1 ≠ a)) ↔ y ∈ u.heading.attrs ∧ y ≠ a := by
    intro y; simp [Heading.attrs, List.mem_filter]
  -- each copy, on a tuple without `a`, is the term on the tuple with `a` set
  have hcopy : ∀ t, Tuple.Sorted t → ∀ v,
      (u.term.subst a (.val v)).holds t = u.term.holds (t.set a v) := by
    intro t ht v
    simp only [Term.holds, Term.eval_subst ht (τ := .val v) (v := v) (by simp [Term.eval])]
  refine ⟨fun x hx => ?_, fun t f => ?_, fun t f => ?_⟩
  · simp only [Unrel.dropOne, Class.elimTerm, hval, Option.getD_some, Term.attrs,
      List.flatMap_map, List.mem_flatMap] at hx
    obtain ⟨v, _, hx⟩ := hx
    rcases Term.attrs_subst u.term hx with ⟨h1, h2⟩ | h1
    · exact (hfa x).mpr ⟨hu.reads x h1, h2⟩
    · simp [Term.attrs] at h1
  · -- every copy gives a Boolean
    let p : Term → Bool := fun e => match e.holds t with | .ok b => b | .error _ => false
    have hall : ∀ e ∈ vs.map (fun v => u.term.subst a (.val v)), e.holds t = .ok (p e) := by
      intro e he
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
      obtain ⟨b, hb⟩ := tu _ (f.set hd (Domain.values?_complete hvs hv))
      simp only [p, hcopy t f.sorted v, hb]
    exact ⟨_, by simp only [Unrel.dropOne, Class.elimTerm, hval, Option.getD_some]; exact holds_orN hall⟩
  · let p : Term → Bool := fun e => match e.holds t with | .ok b => b | .error _ => false
    have hall : ∀ e ∈ vs.map (fun v => u.term.subst a (.val v)), e.holds t = .ok (p e) := by
      intro e he
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
      obtain ⟨b, hb⟩ := tu _ (f.set hd (Domain.values?_complete hvs hv))
      simp only [p, hcopy t f.sorted v, hb]
    simp only [Unrel.Holds, Unrel.dropOne, Class.elimTerm, hval, Option.getD_some,
      holds_orN hall, Except.ok.injEq, List.any_eq_true, List.mem_map]
    constructor
    · rintro ⟨_, e, ⟨v, hv, rfl⟩, he⟩
      refine ⟨v, f.set hd (Domain.values?_complete hvs hv), ?_⟩
      simp only [p, hcopy t f.sorted v] at he
      split at he
      · rename_i b hb; rw [hb, he]
      · cases he
    · rintro ⟨v, fs, hs⟩
      refine ⟨f, _, ⟨v, ?_, rfl⟩, ?_⟩
      · refine Domain.values?_sound hvs (fs.dom (a, v) ?_ d hd)
        have : (t.set a v).get? a = some v := by rw [Tuple.get?_set f.sorted]; simp
        exact lookup_mem this
      · simp only [p, hcopy t f.sorted v, hs]

/-- Each class needs the dropped attribute in the heading. -/
theorem Class.Accepts.lookup {c : Class} {u : Unrel} {a : String} (h : c.Accepts u a) :
    ∃ d, u.heading.lookup a = some d := by
  cases c
  case dense => exact ⟨_, h.1⟩
  case equality => obtain ⟨d, hd, _⟩ := h; exact ⟨d, hd⟩
  case linear => exact ⟨_, h.1⟩
  obtain ⟨d, _, hd, _⟩ := h
  exact ⟨d, hd⟩

/-! ## The frame: removing a list of attributes -/

theorem lookup_filter_some {β : Type} {c : String → Bool} {a : String} {d : β}
    {l : List (String × β)} (h : (l.filter fun p => c p.1).lookup a = some d) :
    l.lookup a = some d ∧ c a = true := by
  cases hc : c a
  · rw [lookup_filter_key_false hc] at h; cases h
  · rw [lookup_filter_key hc] at h; exact ⟨h, rfl⟩

theorem mem_attrs_filter {c : String → Bool} {h : Heading} {x : String} :
    x ∈ Heading.attrs (h.filter fun p => c p.1) ↔ x ∈ h.attrs ∧ c x = true := by
  simp only [Heading.attrs, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hc⟩, rfl⟩; exact ⟨⟨p, hp, rfl⟩, hc⟩
  · rintro ⟨⟨p, hp, rfl⟩, hc⟩; exact ⟨p, ⟨hp, hc⟩, rfl⟩

theorem dropOne_attrs {u : Unrel} {a : String} {c : Class} {x : String} :
    x ∈ (u.dropOne a c).heading.attrs ↔ x ∈ u.heading.attrs ∧ x ≠ a :=
  (mem_attrs_filter (c := fun x => decide (x ≠ a))).trans (by simp)

/-- Removal keeps the heading's other attributes, with their domains, in order. -/
theorem eliminate_heading : ∀ {u w : Unrel} {l : List String}, u.eliminate l = .ok w →
    w.heading = u.heading.filter fun p => !l.contains p.1
  | u, w, [], h => by
    simp only [Unrel.eliminate, Except.ok.injEq] at h
    subst h; simp; exact (List.filter_eq_self.mpr fun _ _ => rfl).symm
  | u, w, a :: rest, h => by
    simp only [Unrel.eliminate, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i c _
      rw [eliminate_heading h]
      simp only [Unrel.dropOne, List.filter_filter]
      apply List.filter_congr
      intro p _
      simp only [List.contains_cons, Bool.not_or, Bool.and_comm]
      by_cases e : p.1 = a
      · simp [e]
      · simp [e, Ne]

/-- A relation with one attribute removed is well formed and total. -/
theorem dropOne_wf {c : Class} {u : Unrel} {a : String} (hc : c.Accepts u a) (hu : u.WF)
    (tu : u.Total) : (u.dropOne a c).WF ∧ (u.dropOne a c).Total := by
  obtain ⟨hr, ht, _⟩ := Class.elimTerm_sound hc hu tu
  refine ⟨⟨?_, hr⟩, ht⟩
  exact hu.nodup.sublist (List.filter_sublist.map _)

/-- Restricting twice is restricting to the smaller list. -/
theorem restrict_restrict {t : Tuple} {l₁ l₂ : List String} (hs : ∀ x ∈ l₂, x ∈ l₁) :
    (t.restrict l₁).restrict l₂ = t.restrict l₂ := by
  unfold Tuple.restrict
  rw [List.filter_filter]
  apply List.filter_congr
  intro p _
  by_cases h : p.1 ∈ l₂
  · simp [h, hs _ h]
  · simp [h]

/-- **Soundness of the frame.** Removing the attributes of `l` from a well-formed, total
relation, one class at a time, gives a well-formed, total relation that holds exactly the
restrictions of the tuples the operand holds. -/
theorem eliminate_sound : ∀ {u w : Unrel} {l : List String}, u.eliminate l = .ok w →
    u.WF → u.Total →
    w.WF ∧ w.Total ∧ ∀ t, w.Holds t ↔ ∃ s, u.Holds s ∧ s.restrict w.heading.attrs = t
  | u, w, [], h, hu, tu => by
    simp only [Unrel.eliminate, Except.ok.injEq] at h
    subst h
    refine ⟨hu, tu, fun t => ⟨fun ht => ⟨t, ht, ht.1.restrict_self⟩, ?_⟩⟩
    rintro ⟨s, hs, rfl⟩
    rw [hs.1.restrict_self]; exact hs
  | u, w, a :: rest, h, hu, tu => by
    have h' := h
    simp only [Unrel.eliminate, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i c hrc
      have hacc : c.Accepts u a := (recognise_ok_iff.mp hrc).accepts
      obtain ⟨d, hd⟩ := hacc.lookup
      obtain ⟨hu', tu'⟩ := dropOne_wf hacc hu tu
      obtain ⟨_, _, hiff⟩ := Class.elimTerm_sound hacc hu tu
      obtain ⟨hw, tw, ih⟩ := eliminate_sound h hu' tu'
      refine ⟨hw, tw, fun t => (ih t).trans ?_⟩
      -- the attributes of `w` are among those of the dropped relation, without `a`
      have hwh := eliminate_heading h
      have hwsub : ∀ x ∈ w.heading.attrs, x ∈ (u.dropOne a c).heading.attrs := by
        intro x hx; rw [hwh] at hx
        exact (mem_attrs_filter (c := fun x => !rest.contains x)).mp hx |>.1
      have hwa : a ∉ w.heading.attrs := fun hx => (dropOne_attrs.mp (hwsub a hx)).2 rfl
      constructor
      · rintro ⟨s', hs', rfl⟩
        obtain ⟨v, hv⟩ := (hiff s' hs'.1).mp hs'
        refine ⟨s'.set a v, hv, ?_⟩
        refine Tuple.ext_get? (sorted_restrict hv.1.sorted) (sorted_restrict hs'.1.sorted)
          fun x => ?_
        rw [get?_restrict, get?_restrict, Tuple.get?_set hs'.1.sorted]
        by_cases hx : x ∈ w.heading.attrs
        · have : x ≠ a := fun e => hwa (e ▸ hx)
          simp [hx, this]
        · simp [hx]
      · rintro ⟨s, hs, rfl⟩
        have hsub : ∀ x e, (u.dropOne a c).heading.lookup x = some e →
            u.heading.lookup x = some e := fun x e he =>
          (lookup_filter_some (c := fun x => decide (x ≠ a)) he).1
        have fs' := hs.1.restrict hsub
        obtain ⟨v, hv⟩ : ∃ v, s.get? a = some v :=
          Option.isSome_iff_exists.mp ((hs.1.get?_isSome a).mpr
            (Finrel.mem_attrs_iff.mpr (by rw [hd]; rfl)))
        have hset : (s.restrict (u.dropOne a c).heading.attrs).set a v = s := by
          refine Tuple.ext_get? (fs'.set hd ?_).sorted hs.1.sorted fun x => ?_
          · exact hs.1.dom (a, v) (lookup_mem hv) d hd
          rw [Tuple.get?_set fs'.sorted, get?_restrict]
          by_cases e : x = a
          · subst e; simp [hv]
          · simp only [e, ite_false]
            by_cases hx : x ∈ u.heading.attrs
            · have : x ∈ (u.dropOne a c).heading.attrs := dropOne_attrs.mpr ⟨hx, e⟩
              simp [this]
            · have : x ∉ (u.dropOne a c).heading.attrs := fun h' => hx (dropOne_attrs.mp h').1
              simp [this, hs.1.get?_none hx]
        refine ⟨_, (hiff _ fs').mpr ⟨v, by rw [hset]; exact hs⟩, restrict_restrict hwsub⟩

/-! ## Agreement: when π succeeds -/

/-- Every removal, in order, finds a class: the first class of `Class.all` that accepts
the relation as it is at that point. -/
def AllAccepted : Unrel → List String → Prop
  | _, [] => True
  | u, a :: rest => ∃ c, Class.FirstIn Class.all u a c ∧ AllAccepted (u.dropOne a c) rest

theorem eliminate_ok_iff : ∀ {u : Unrel} {l : List String},
    (∃ w, u.eliminate l = .ok w) ↔ AllAccepted u l
  | u, [] => by simp [Unrel.eliminate, AllAccepted]
  | u, a :: rest => by
    simp only [Unrel.eliminate, bind, Except.bind, AllAccepted]
    constructor
    · rintro ⟨w, h⟩
      split at h
      · cases h
      · rename_i c hc
        exact ⟨c, recognise_ok_iff.mp hc, eliminate_ok_iff.mp ⟨w, h⟩⟩
    · rintro ⟨c, hc, hr⟩
      rw [recognise_ok_iff.mpr hc]
      exact eliminate_ok_iff.mpr hr

theorem Heading.pick_attrs {h : Heading} : ∀ {as : List String} {k : Heading},
    h.pick as = .ok k → k.attrs = as
  | [], k, e => by simp only [Heading.pick, Except.ok.injEq] at e; subst e; rfl
  | a :: as, k, e => by
    simp only [Heading.pick] at e
    split at e
    · simp only [bind, Except.bind] at e
      split at e
      · cases e
      · rename_i k' hk'
        simp only [pure, Except.pure, Except.ok.injEq] at e
        subst e
        simp [Heading.attrs, ← Heading.pick_attrs hk']
    · cases e

theorem Heading.pick_lookup {h : Heading} : ∀ {as : List String} {k : Heading},
    h.pick as = .ok k → ∀ a d, k.lookup a = some d → h.lookup a = some d
  | [], k, e => by
    simp only [Heading.pick, Except.ok.injEq] at e; subst e; intro a d hd; cases hd
  | b :: as, k, e => by
    simp only [Heading.pick] at e
    split at e
    · rename_i d' hd'
      simp only [bind, Except.bind] at e
      split at e
      · cases e
      · rename_i k' hk'
        simp only [pure, Except.pure, Except.ok.injEq] at e
        subst e
        intro a d hd
        by_cases hab : a = b
        · subst hab; simp [List.lookup] at hd; subst hd; exact hd'
        · have : (a == b) = false := by simpa using hab
          simp only [List.lookup, this] at hd; exact Heading.pick_lookup hk' a d hd
    · cases e

theorem Heading.pick_ok {h : Heading} : ∀ {as : List String},
    (∃ k, h.pick as = .ok k) ↔ ∀ a ∈ as, a ∈ h.attrs
  | [] => by simp [Heading.pick]
  | b :: as => by
    simp only [Heading.pick, List.mem_cons, forall_eq_or_imp]
    split
    · rename_i d hd
      simp only [bind, Except.bind]
      have hb : b ∈ h.attrs := Finrel.mem_attrs_iff.mpr (by rw [hd]; rfl)
      rw [← Heading.pick_ok (as := as)]
      constructor
      · rintro ⟨k, e⟩
        split at e
        · cases e
        · rename_i k' hk'; exact ⟨hb, k', hk'⟩
      · rintro ⟨_, k', hk'⟩
        rw [hk']; exact ⟨_, rfl⟩
    · rename_i hd
      have hb : b ∉ h.attrs := fun hb => by
        have := Finrel.mem_attrs_iff.mp hb
        rw [hd] at this; cases this
      constructor
      · rintro ⟨_, e⟩; cases e
      · rintro ⟨hb', _⟩; exact absurd hb' hb

theorem mem_dropOrder {h : Heading} {as : List String} {x : String} :
    x ∈ dropOrder h as ↔ x ∈ h.attrs ∧ x ∉ as := by
  simp only [dropOrder, List.mem_append, List.mem_filter]
  constructor
  · rintro (⟨⟨hx, hn⟩, _⟩ | ⟨⟨hx, hn⟩, _⟩) <;> exact ⟨hx, by simpa using hn⟩
  · rintro ⟨hx, hn⟩
    have hn' : (!as.contains x) = true := by simpa using hn
    cases hh : (h.lookup x).bind Domain.values?
    · exact .inl ⟨⟨hx, hn'⟩, by simp⟩
    · exact .inr ⟨⟨hx, hn'⟩, by simp⟩

theorem dropOrder_nodup {h : Heading} {as : List String} (hn : h.attrs.Nodup) :
    (dropOrder h as).Nodup := by
  simp only [dropOrder]
  have hd := hn.filter (fun a => !as.contains a)
  rw [List.nodup_append]
  refine ⟨hd.filter _, hd.filter _, ?_⟩
  intro x hx y hy e
  subst e
  simp only [List.mem_filter] at hx hy
  cases hh : (h.lookup x).bind Domain.values? <;> simp_all

theorem project_eq (as : List String) (u : Unrel) :
    u.project as = if as.eraseDups.length != as.length
      then .error s!"π: {as} names an attribute twice"
      else (do
        let h ← u.heading.pick as
        let w ← u.eliminate (dropOrder u.heading as)
        return ⟨h, w.term⟩) := by
  unfold Unrel.project
  split <;> rfl

/-- **Agreement.** π on an unrestricted relation succeeds exactly when it names attributes
of the heading, none twice, and each attribute it drops, in the order they are removed
(infinite domains first, then finite ones, each in heading order), is accepted by a class. -/
theorem project_ok_iff {as : List String} {u : Unrel} :
    (∃ w, u.project as = .ok w) ↔
      as.Nodup ∧ (∀ a ∈ as, a ∈ u.heading.attrs) ∧ AllAccepted u (dropOrder u.heading as) := by
  rw [project_eq]
  by_cases hn : as.Nodup
  · have : as.eraseDups.length = as.length := (length_eraseDups_eq as).mpr hn
    simp only [this, bne_self_eq_false, Bool.false_eq_true, ite_false, hn, true_and,
      bind, Except.bind]
    rw [← Heading.pick_ok, ← eliminate_ok_iff]
    constructor
    · rintro ⟨w, e⟩
      split at e
      · cases e
      · rename_i k hk
        split at e
        · cases e
        · rename_i w' hw'; exact ⟨⟨k, hk⟩, w', hw'⟩
    · rintro ⟨⟨k, hk⟩, w', hw'⟩
      rw [hk]; simp only; rw [hw']; exact ⟨_, rfl⟩
  · have : as.eraseDups.length ≠ as.length := fun e => hn ((length_eraseDups_eq as).mp e)
    simp only [hn, false_and, iff_false]
    rintro ⟨w, e⟩
    have hb : (as.eraseDups.length != as.length) = true := by simpa using this
    simp only [hb, ite_true] at e
    cases e

/-! ## Soundness of π -/

/-- π's heading is the attributes `as`, with their domains, in the order of `as`. -/
theorem project_pick {as : List String} {u w : Unrel} (h : u.project as = .ok w) :
    u.heading.pick as = .ok w.heading := by
  rw [project_eq] at h
  split at h
  · cases h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i k hk
  split at h
  · cases h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact hk

/-- **Soundness.** On a well-formed, total operand, π's result is well formed and total,
and holds exactly the restrictions to `as` of the tuples the operand holds. -/
theorem project_sound {as : List String} {u w : Unrel} (h : u.project as = .ok w)
    (hu : u.WF) (tu : u.Total) :
    w.WF ∧ w.Total ∧ ∀ t, w.Holds t ↔ ∃ s, u.Holds s ∧ s.restrict as = t := by
  obtain ⟨hn, hin, _⟩ := project_ok_iff.mp ⟨w, h⟩
  rw [project_eq] at h
  have : as.eraseDups.length = as.length := (length_eraseDups_eq as).mpr hn
  simp only [this, bne_self_eq_false, Bool.false_eq_true, ite_false, bind, Except.bind] at h
  split at h
  · cases h
  rename_i k hk
  split at h
  · cases h
  rename_i w' hw'
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  obtain ⟨hw, tw, hiff⟩ := eliminate_sound hw' hu tu
  have hwh := eliminate_heading hw'
  -- the attributes of `w'` are those of `as`
  have hattr : ∀ x, x ∈ w'.heading.attrs ↔ x ∈ as := by
    intro x
    rw [hwh, mem_attrs_filter (c := fun x => !(dropOrder u.heading as).contains x)]
    constructor
    · rintro ⟨hx, hc⟩
      have hc' : x ∉ dropOrder u.heading as := by simpa using hc
      exact Classical.byContradiction fun hxa => hc' (mem_dropOrder.mpr ⟨hx, hxa⟩)
    · intro hx; exact ⟨hin x hx, by simp [mem_dropOrder, hx]⟩
  have hka : ∀ x, x ∈ k.attrs ↔ x ∈ as := by intro x; rw [Heading.pick_attrs hk]
  have hlook : ∀ x d, k.lookup x = some d ↔ w'.heading.lookup x = some d := by
    intro x d
    have hkey : ∀ y, y ∈ as → (!(dropOrder u.heading as).contains y) = true := by
      intro y hy; simp [mem_dropOrder, hy]
    constructor
    · intro hd
      have hx : x ∈ as := (hka x).mp (Finrel.mem_attrs_iff.mpr (by rw [hd]; rfl))
      rw [hwh, lookup_filter_key (c := fun y => !(dropOrder u.heading as).contains y) (hkey x hx)]
      exact Heading.pick_lookup hk x d hd
    · intro hd
      have hx : x ∈ as := (hattr x).mp (Finrel.mem_attrs_iff.mpr (by rw [hd]; rfl))
      rw [hwh, lookup_filter_key (c := fun y => !(dropOrder u.heading as).contains y) (hkey x hx)] at hd
      obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.mp
        (Finrel.mem_attrs_iff.mp ((hka x).mpr hx))
      obtain rfl := Option.some.inj ((Heading.pick_lookup hk x d' hd').symm.trans hd)
      exact hd'
  have hfits : ∀ t : Tuple, t.Fits k ↔ t.Fits w'.heading := fun t =>
    ⟨fun f => f.transfer (fun x => (hka x).trans (hattr x).symm) (fun x d hd => (hlook x d).mpr hd),
     fun f => f.transfer (fun x => (hattr x).trans (hka x).symm) (fun x d hd => (hlook x d).mp hd)⟩
  refine ⟨⟨?_, fun x hx => (hka x).mpr ((hattr x).mp (hw.reads x hx))⟩,
    fun t f => tw t ((hfits t).mp f), fun t => ?_⟩
  · rw [Heading.pick_attrs hk]; exact hn
  · have : (⟨k, w'.term⟩ : Unrel).Holds t ↔ w'.Holds t := by
      simp only [Unrel.Holds, hfits t]
    rw [this, hiff t]
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s, hs, Tuple.restrict_congr fun x hx => ?_⟩
      exact (hattr x).symm
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s, hs, Tuple.restrict_congr fun x hx => ?_⟩
      exact hattr x

/-! ## The finite class alone -/

/-- With the finite class, every removal finds a class when every dropped attribute has a
finite domain. -/
theorem allAccepted_of_finite : ∀ {u : Unrel} {l : List String}, l.Nodup →
    (∀ a ∈ l, ((u.heading.lookup a).bind Domain.values?).isSome) → AllAccepted u l
  | _, [], _, _ => trivial
  | u, a :: rest, hn, hf => by
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hf a List.mem_cons_self)
    obtain ⟨d', hd', hv⟩ := Option.bind_eq_some_iff.mp hd
    have hacc : Class.Accepts .finite u a := ⟨d', d, hd', hv⟩
    refine ⟨.finite, .inl ⟨hacc, rfl⟩, allAccepted_of_finite (List.nodup_cons.mp hn).2 ?_⟩
    intro b hb
    have hba : b ≠ a := fun e => (List.nodup_cons.mp hn).1 (e ▸ hb)
    have : (u.dropOne a .finite).heading.lookup b = u.heading.lookup b :=
      lookup_filter_key (c := fun x => decide (x ≠ a)) (by simpa using hba) _
    rw [this]
    exact hf b (List.mem_cons_of_mem _ hb)

/-- With the finite class, π succeeds when it names attributes of the heading, none twice,
and every attribute it drops has a finite domain. -/
theorem project_ok_of_finite {as : List String} {u : Unrel} (hu : u.heading.attrs.Nodup)
    (hn : as.Nodup) (hin : ∀ a ∈ as, a ∈ u.heading.attrs)
    (hf : ∀ a ∈ u.heading.attrs, a ∉ as → ((u.heading.lookup a).bind Domain.values?).isSome) :
    ∃ w, u.project as = .ok w :=
  project_ok_iff.mpr ⟨hn, hin, allAccepted_of_finite (dropOrder_nodup hu)
    fun a ha => hf a (mem_dropOrder.mp ha).1 (mem_dropOrder.mp ha).2⟩

/-! ## The finite class as a global class -/

/-- Every domain of the heading is finite. -/
def Heading.Finite (h : Heading) : Prop := ∀ p ∈ h, p.2.values?.isSome

/-- A relation in the finite class: well formed, total, and every domain finite. π succeeds
on it for any attribute list that passes the checks, and its tuples can be listed. -/
structure FiniteClass (u : Unrel) : Prop where
  wf : u.WF
  total : u.Total
  finite : u.heading.Finite

theorem FiniteClass.project_ok {u : Unrel} {as : List String} (hu : FiniteClass u)
    (hn : as.Nodup) (hin : ∀ a ∈ as, a ∈ u.heading.attrs) : ∃ w, u.project as = .ok w :=
  project_ok_of_finite hu.wf.nodup hn hin fun a _ _ => by
    cases hl : u.heading.lookup a with
    | none => simp_all [Finrel.mem_attrs_iff]
    | some d => simpa using hu.finite _ (lookup_mem hl)

theorem Domain.inter_finite {a b f : Domain} (h : a.inter b = .ok f)
    (hab : a.values?.isSome ∨ b.values?.isSome) : f.values?.isSome := by
  unfold Domain.inter at h
  split at h
  · cases h; rename_i e; subst e; simpa using hab
  · split at h <;> (try (cases h; first | rfl | (split <;> rfl) | (simp_all [Domain.values?])))
    all_goals (split at h <;> cases h <;> simp_all [Domain.ofValues, Domain.values?])

theorem FiniteClass.select {u w : Unrel} {p : Term} (hu : FiniteClass u)
    (h : u.select p = .ok w) (hp : ∀ t, t.Fits u.heading → ∃ b, p.holds t = .ok b) :
    FiniteClass w := by
  obtain ⟨hh, _⟩ := Unrel.select_heading h
  exact ⟨Unrel.select_wf h hu.wf, Unrel.select_total h hu.total hp, hh ▸ hu.finite⟩

theorem FiniteClass.union {u v w : Unrel} (hu : FiniteClass u) (hv : FiniteClass v)
    (h : u.union v = .ok w) : FiniteClass w := by
  obtain ⟨_, hh, _⟩ := Unrel.union_heading h
  exact ⟨Unrel.union_wf h hu.wf hv.wf, Unrel.union_total h hu.total hv.total, hh ▸ hu.finite⟩

theorem FiniteClass.inter {u v w : Unrel} (hu : FiniteClass u) (hv : FiniteClass v)
    (h : u.inter v = .ok w) : FiniteClass w := by
  obtain ⟨_, hh, _⟩ := Unrel.inter_heading h
  exact ⟨Unrel.inter_wf h hu.wf hv.wf, Unrel.inter_total h hu.total hv.total, hh ▸ hu.finite⟩

theorem FiniteClass.diff {u v w : Unrel} (hu : FiniteClass u) (hv : FiniteClass v)
    (h : u.diff v = .ok w) : FiniteClass w := by
  obtain ⟨_, hh, _⟩ := Unrel.diff_heading h
  exact ⟨Unrel.diff_wf h hu.wf hv.wf, Unrel.diff_total h hu.total hv.total, hh ▸ hu.finite⟩

theorem FiniteClass.join {u v w : Unrel} (hu : FiniteClass u) (hv : FiniteClass v)
    (h : u.join v = .ok w) : FiniteClass w := by
  have hw := Unrel.join_wf h hu.wf hv.wf
  refine ⟨hw, Unrel.join_total h hu.wf hv.wf hu.total hv.total, fun p hp => ?_⟩
  obtain ⟨hj, _⟩ := Unrel.join_heading h
  obtain ⟨_, _, hl⟩ := Finrel.joinHeading_spec hj hu.wf.nodup hv.wf.nodup
  rcases hl p.1 p.2 (mem_lookup hw.nodup hp) with
    ⟨d, hd, (⟨_, e⟩ | ⟨e, he, hi⟩)⟩ | ⟨_, hk⟩
  · rw [e]; exact hu.finite _ hd
  · exact Domain.inter_finite hi (.inl (hu.finite _ hd))
  · exact hv.finite _ (lookup_mem hk)

theorem FiniteClass.rename {u w : Unrel} {ren : List (String × String)} (hu : FiniteClass u)
    (h : u.rename ren = .ok w) : FiniteClass w := by
  refine ⟨Unrel.rename_wf h hu.wf, Unrel.rename_total h hu.wf hu.total, fun p hp => ?_⟩
  obtain ⟨_, rfl⟩ := Unrel.rename_eq h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hu.finite q hq

theorem FiniteClass.project {u w : Unrel} {as : List String} (hu : FiniteClass u)
    (h : u.project as = .ok w) : FiniteClass w := by
  obtain ⟨hw, tw, _⟩ := project_sound h hu.wf hu.total
  refine ⟨hw, tw, fun p hp => ?_⟩
  have hl := Heading.pick_lookup (project_pick h) p.1 p.2 (mem_lookup hw.nodup hp)
  exact hu.finite _ (lookup_mem hl)

end Rasso
