import Rasso.Rep

/-!
# Rasso: what an unrestricted relation means

An unrestricted relation `u` is a heading and one Boolean term. Its **meaning** is a set
of tuples: `u.Holds t` when `t` fits the heading and the term is true on `t`. A term can
also refuse (`1 + true`, an int compared with a float), so two more properties say when
the meaning is clean:

* `u.Total`: on every tuple that fits the heading, the term gives a Boolean; it never
  refuses there.
* `u.WF` (well formed): the heading names no attribute twice, and the term reads only
  attributes of the heading (it is *scoped*).

For each operator on unrestricted relations (σ, ⋈, ×, ∪, ∩, −) this module proves which
tuples the result holds, and that WF and Total are kept. Lift (`Finrel.toUnrel`, a
finite relation as a term) holds exactly the finite relation's tuples. π's agreement
and soundness are stated against this meaning (`Rasso.Project`).

Conventions:

* The meaning is two-valued: a tuple on which the term refuses is not held. Totality is
  the hypothesis that this never happens, and the ∪ and − lemmas need it, because
  `or` and `not` pass a refusal on.
* Lift's lemma needs every domain of the heading to be *unmixed*: no float together
  with an exact number. The form check refuses such a set when it is written.
-/

namespace Rasso

/-! ## A term reads only its attributes -/

theorem mapM_congr_ok {α β : Type} {f g : α → Except String β} : ∀ (l : List α),
    (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons, h x List.mem_cons_self,
      mapM_congr_ok xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Two tuples that agree on the attributes a term reads give it the same value. -/
theorem Term.eval_congr {t t' : Tuple} : ∀ (e : Term),
    (∀ a ∈ e.attrs, t.get? a = t'.get? a) → e.eval t = e.eval t'
  | .attr a, h => by
      have := h a (by simp [Term.attrs])
      simp only [Term.eval, this]
  | .val v, _ => by simp [Term.eval]
  | .call op args, h => by
      have : args.mapM (Term.eval t) = args.mapM (Term.eval t') := by
        apply mapM_congr_ok
        intro e he
        exact Term.eval_congr e (fun a ha => h a (by
          simp only [Term.attrs, List.mem_flatMap]; exact ⟨e, he, ha⟩))
      simp only [Term.eval, this]

theorem Term.holds_congr {t t' : Tuple} {e : Term}
    (h : ∀ a ∈ e.attrs, t.get? a = t'.get? a) : e.holds t = e.holds t' := by
  simp only [Term.holds, e.eval_congr h]

/-! ## Truth of `and`, `or`, `not` -/

theorem Term.holds_ok {t : Tuple} {e : Term} {b : Bool} :
    e.holds t = .ok b ↔ e.eval t = .ok (.bool b) := by
  simp only [Term.holds, bind, Except.bind]
  cases e.eval t with
  | error _ => simp
  | ok v => cases v <;> simp [asBool]

/-- The value of a term that holds or fails, as a Boolean. -/
theorem Term.eval_of_holds {t : Tuple} {e : Term} {b : Bool} (h : e.holds t = .ok b) :
    e.eval t = .ok (.bool b) := Term.holds_ok.mp h

/-- When a term does not give a Boolean, `holds` refuses. -/
theorem Term.holds_cases (t : Tuple) (e : Term) :
    (∃ b, e.holds t = .ok b) ∨ ∃ m, e.holds t = .error m := by
  cases h : e.holds t with
  | ok b => exact .inl ⟨b, rfl⟩
  | error m => exact .inr ⟨m, rfl⟩

theorem holds_and2 {t : Tuple} {a b : Term} {x : Bool} :
    (Term.call "and" [a, b]).holds t = .ok x ↔
      ∃ p q, a.holds t = .ok p ∧ b.holds t = .ok q ∧ x = (p && q) := by
  simp only [Term.holds_ok]
  simp only [Term.eval, List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure]
  cases ha : a.eval t with
  | error _ => simp
  | ok va =>
    cases hb : b.eval t with
    | error _ => simp
    | ok vb =>
      cases va <;> cases vb <;> simp [applyOp, asBool, bind, Except.bind, pure, Except.pure] <;>
        constructor <;> intro h <;> simp_all

theorem holds_or2 {t : Tuple} {a b : Term} {x : Bool} :
    (Term.call "or" [a, b]).holds t = .ok x ↔
      ∃ p q, a.holds t = .ok p ∧ b.holds t = .ok q ∧ x = (p || q) := by
  simp only [Term.holds_ok]
  simp only [Term.eval, List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure]
  cases ha : a.eval t with
  | error _ => simp
  | ok va =>
    cases hb : b.eval t with
    | error _ => simp
    | ok vb =>
      cases va <;> cases vb <;> simp [applyOp, asBool, bind, Except.bind, pure, Except.pure] <;>
        constructor <;> intro h <;> simp_all

theorem holds_not1 {t : Tuple} {a : Term} {x : Bool} :
    (Term.call "not" [a]).holds t = .ok x ↔ ∃ p, a.holds t = .ok p ∧ x = !p := by
  simp only [Term.holds_ok]
  simp only [Term.eval, List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure]
  cases ha : a.eval t with
  | error _ => simp
  | ok va =>
    cases va <;> simp [applyOp, asBool, bind, Except.bind, pure, Except.pure] <;>
      constructor <;> intro h <;> simp_all


/-! ## Domains -/

/-- Every value a finite domain lists is in the domain (the converse of
`Domain.values?_sound`). -/
theorem Domain.values?_complete {a : Domain} {va : List Value} (h : a.values? = some va)
    {x : Value} (hx : x ∈ va) : a.mem x = true := by
  match a, h with
  | .kind .bool, h =>
    simp only [Domain.values?, Option.some.injEq] at h; subst h
    simp at hx; rcases hx with rfl | rfl <;> rfl
  | .range lo hi, h =>
    simp only [Domain.values?, Option.some.injEq] at h; subst h
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [Domain.mem, Bool.and_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast]; omega
  | .set vs, h =>
    simp only [Domain.values?, Option.some.injEq] at h; subst h
    simp only [Domain.mem, List.contains_iff_mem]; exact List.mem_mergeSort.mp hx
  | .kind .int, h | .kind .symbol, h | .kind .string, h | .kind .float, h | .kind .rat, h =>
    simp [Domain.values?] at h

/-- A value of the intersection of two domains is in both (the converse of
`Domain.inter_sound`). -/
theorem Domain.inter_complete {a b f : Domain} (h : a.inter b = .ok f) {x : Value}
    (hf : f.mem x = true) : a.mem x = true ∧ b.mem x = true := by
  unfold Domain.inter at h
  split at h
  · cases h; rename_i e; subst e; exact ⟨hf, hf⟩
  · split at h
    · rename_i l₁ h₁ l₂ h₂ _
      cases h
      split at hf
      · match x with
        | .int n =>
          simp only [Domain.mem, Bool.and_eq_true, decide_eq_true_eq] at hf ⊢; omega
        | .bool _ | .symbol _ | .string _ | .float _ | .rat _ _ => simp [Domain.mem] at hf
      · simp [Domain.mem] at hf
    all_goals first
      | (cases h; match x with
          | .int n => simp_all [Domain.mem, Kind.has]
          | .bool _ | .symbol _ | .string _ | .float _ | .rat _ _ => simp_all [Domain.mem, Kind.has])
      | skip
    · split at h
      · rename_i va _ hva; cases h
        have := List.mem_filter.mp (Domain.mem_ofValues.mp hf)
        exact ⟨Domain.values?_complete hva this.1, this.2⟩
      · rename_i vb hvb _; cases h
        have := List.mem_filter.mp (Domain.mem_ofValues.mp hf)
        exact ⟨this.2, Domain.values?_complete hvb this.1⟩
      · cases h

/-- A domain is *unmixed* when it does not hold both a float and an exact number, nor both
a symbol and a string: the pairs `=` refuses to compare. As no Lean type holds both, no
domain does: the form check refuses a set that mixes them. -/
def Domain.Unmixed (d : Domain) : Prop :=
  ∀ v w, d.mem v = true → d.mem w = true →
    ¬ (v.isExact = true ∧ w.isFloat = true) ∧ ¬ (v.isSymbol = true ∧ w.isString = true)

def Heading.Unmixed (h : Heading) : Prop := ∀ p ∈ h, p.2.Unmixed

theorem Domain.unmixed_kind (k : Kind) : (Domain.kind k).Unmixed := by
  intro v w hv hw
  cases k <;> cases v <;> cases w <;>
    simp_all [Domain.mem, Kind.has, Value.isExact, Value.exact?, Value.isFloat, Value.isSymbol,
      Value.isString]

theorem Domain.unmixed_range (lo hi : Int) : (Domain.range lo hi).Unmixed := by
  intro v w _ hw
  cases w <;> simp_all [Domain.mem, Value.isFloat, Value.isString]

/-- A set domain the form check accepts is unmixed. -/
theorem Domain.unmixed_set {vs : List Value}
    (h : ¬ (vs.any Value.isFloat = true ∧ vs.any Value.isExact = true))
    (h' : ¬ (vs.any Value.isString = true ∧ vs.any Value.isSymbol = true)) :
    (Domain.set vs).Unmixed := by
  intro v w hv hw
  simp only [Domain.mem, List.contains_iff_mem] at hv hw
  exact ⟨fun ⟨he, hf⟩ => h ⟨List.any_eq_true.mpr ⟨w, hw, hf⟩, List.any_eq_true.mpr ⟨v, hv, he⟩⟩,
    fun ⟨he, hf⟩ => h' ⟨List.any_eq_true.mpr ⟨w, hw, hf⟩, List.any_eq_true.mpr ⟨v, hv, he⟩⟩⟩

/-- `=` between two values of an unmixed domain is equality of values. -/
theorem applyOp_eq_unmixed {d : Domain} (hd : d.Unmixed) {v w : Value} (hv : d.mem v = true)
    (hw : d.mem w = true) : applyOp "=" [v, w] = .ok (.bool (v == w)) := by
  have h1 := hd v w hv hw
  have h2 := hd w v hw hv
  cases v <;> cases w <;> first
    | rfl
    | (exfalso; simp [Value.isExact, Value.exact?, Value.isFloat, Value.isSymbol,
        Value.isString] at h1 h2)

/-! ## n-ary `and` and `or` -/

theorem eval_all_bool {t : Tuple} {p : Term → Bool} :
    ∀ {l : List Term}, (∀ e ∈ l, e.holds t = .ok (p e)) →
      l.mapM (Term.eval t) = .ok (l.map fun e => .bool (p e))
  | [], _ => rfl
  | x :: l, hl => by
    simp only [List.mapM_cons, Term.eval_of_holds (hl x List.mem_cons_self), bind, Except.bind,
      eval_all_bool fun e he => hl e (List.mem_cons_of_mem _ he), pure, Except.pure,
      List.map_cons]

theorem mapM_asBool_map {who : String} {p : Term → Bool} : ∀ (l : List Term),
    (l.map fun e => Value.bool (p e)).mapM (asBool who) = .ok (l.map p)
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, List.mapM_cons, asBool, bind, Except.bind, mapM_asBool_map l, pure,
      Except.pure]

theorem holds_andN {t : Tuple} {p : Term → Bool} {l : List Term}
    (h : ∀ e ∈ l, e.holds t = .ok (p e)) : (Term.call "and" l).holds t = .ok (l.all p) := by
  rw [Term.holds_ok]
  simp only [Term.eval, eval_all_bool h, bind, Except.bind, applyOp, mapM_asBool_map, pure,
    Except.pure, List.all_map]
  rfl

theorem holds_orN {t : Tuple} {p : Term → Bool} {l : List Term}
    (h : ∀ e ∈ l, e.holds t = .ok (p e)) : (Term.call "or" l).holds t = .ok (l.any p) := by
  rw [Term.holds_ok]
  simp only [Term.eval, eval_all_bool h, bind, Except.bind, applyOp, mapM_asBool_map, pure,
    Except.pure, List.any_map]
  rfl

/-! ## The same heading -/

/-- What `Heading.same` checks: the same attributes, each with the same domain. -/
def Heading.Same (h k : Heading) : Prop :=
  h.attrs.mergeSort (· ≤ ·) = k.attrs.mergeSort (· ≤ ·) ∧ ∀ p ∈ h, k.lookup p.1 = some p.2

theorem Heading.same_ok {who : String} {h k : Heading} :
    Heading.same who h k = .ok () ↔ Heading.Same h k := by
  unfold Heading.same Heading.Same
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hc
    exact ⟨fun _ => ⟨hc.1, fun p hp => hc.2 p hp⟩, fun _ => rfl⟩
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hc
    exact ⟨fun h => (by cases h), fun ⟨h1, h2⟩ => absurd ⟨h1, fun p hp => h2 p hp⟩ hc⟩

theorem Heading.Same.attrs {h k : Heading} (hs : Heading.Same h k) (a : String) :
    a ∈ h.attrs ↔ a ∈ k.attrs := by
  have := congrArg (a ∈ ·) hs.1
  simp only [List.mem_mergeSort] at this
  exact propext_iff.mp this

theorem Heading.Same.lookup {h k : Heading} (hs : Heading.Same h k) (a : String) :
    h.lookup a = k.lookup a := by
  cases hh : h.lookup a with
  | some d => exact (hs.2 _ (lookup_mem hh)).symm
  | none =>
    cases hk : k.lookup a with
    | none => rfl
    | some e =>
      have : a ∈ h.attrs := (hs.attrs a).mpr (Finrel.mem_attrs_iff.mpr (by rw [hk]; rfl))
      rw [Finrel.mem_attrs_iff, hh] at this; cases this

/-- Tuples that fit one of two same headings fit the other. -/
theorem Heading.Same.fits {h k : Heading} (hs : Heading.Same h k) {t : Tuple} :
    t.Fits h ↔ t.Fits k :=
  ⟨fun f => f.transfer hs.attrs (fun a d hk => by rw [hs.lookup]; exact hk),
   fun f => f.transfer (fun a => (hs.attrs a).symm) (fun a d hh => by rw [← hs.lookup]; exact hh)⟩

/-! ## The meaning -/

namespace Unrel

/-- `u` holds `t`: `t` fits the heading and the term is true on it. -/
def Holds (u : Unrel) (t : Tuple) : Prop := t.Fits u.heading ∧ u.term.holds t = .ok true

/-- The term never refuses on a tuple that fits the heading. -/
def Total (u : Unrel) : Prop := ∀ t, t.Fits u.heading → ∃ b, u.term.holds t = .ok b

/-- No attribute twice in the heading, and the term reads only attributes of the heading. -/
structure WF (u : Unrel) : Prop where
  nodup : u.heading.attrs.Nodup
  reads : ∀ a ∈ u.term.attrs, a ∈ u.heading.attrs

/-! ### ω -/

theorem omega_term_holds (h : Heading) (t : Tuple) : (omega h).term.holds t = .ok true := by
  simp [omega, tt, Term.holds, Term.eval, asBool, bind, Except.bind]

theorem omega_holds (h : Heading) (t : Tuple) : (omega h).Holds t ↔ t.Fits h :=
  ⟨fun h => h.1, fun f => ⟨f, omega_term_holds h t⟩⟩

theorem omega_total (h : Heading) : (omega h).Total := fun t _ => ⟨true, omega_term_holds h t⟩

theorem omega_wf {h : Heading} (hn : h.attrs.Nodup) : (omega h).WF :=
  ⟨hn, fun a ha => by simp [omega, tt, Term.attrs] at ha⟩

/-! ### σ -/

theorem select_heading {p : Term} {u w : Unrel} (h : u.select p = .ok w) :
    w.heading = u.heading ∧ w.term = .call "and" [u.term, p] := by
  simp only [select, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

theorem select_scoped {p : Term} {u w : Unrel} (h : u.select p = .ok w) :
    ∀ a ∈ p.attrs, a ∈ u.heading.attrs := by
  simp only [select, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i hs; exact Heading.scoped_ok.mp hs

/-- σ holds the tuples `u` holds on which `p` is true. Rasso's `and` refuses when an
operand refuses, so this needs no totality. -/
theorem select_holds {p : Term} {u w : Unrel} (h : u.select p = .ok w) (t : Tuple) :
    w.Holds t ↔ u.Holds t ∧ p.holds t = .ok true := by
  obtain ⟨hh, ht⟩ := select_heading h
  simp only [Holds, hh, ht, holds_and2]
  constructor
  · rintro ⟨f, a, b, ha, hb, e⟩
    have : a = true ∧ b = true := by simpa using e.symm
    rw [this.1] at ha; rw [this.2] at hb
    exact ⟨⟨f, ha⟩, hb⟩
  · rintro ⟨⟨f, ha⟩, hb⟩; exact ⟨f, true, true, ha, hb, rfl⟩

theorem select_wf {p : Term} {u w : Unrel} (h : u.select p = .ok w) (hu : u.WF) : w.WF := by
  obtain ⟨hh, ht⟩ := select_heading h
  refine ⟨hh ▸ hu.nodup, fun a ha => ?_⟩
  rw [ht] at ha; rw [hh]
  simp only [Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append] at ha
  rcases ha with ha | ha
  · exact hu.reads a ha
  · exact select_scoped h a ha

theorem select_total {p : Term} {u w : Unrel} (h : u.select p = .ok w) (hu : u.Total)
    (hp : ∀ t, t.Fits u.heading → ∃ b, p.holds t = .ok b) : w.Total := by
  obtain ⟨hh, ht⟩ := select_heading h
  intro t f
  rw [hh] at f
  obtain ⟨a, ha⟩ := hu t f
  obtain ⟨b, hb⟩ := hp t f
  exact ⟨a && b, by rw [ht, holds_and2]; exact ⟨a, b, ha, hb, rfl⟩⟩

/-! ### ∪, ∩, − -/

theorem setop_heading {who : String} {u v w : Unrel} {f : Term → Term → Term}
    (h : (do Heading.same who u.heading v.heading; return ⟨u.heading, f u.term v.term⟩ :
      Except String Unrel) = .ok w) :
    Heading.Same u.heading v.heading ∧ w.heading = u.heading ∧ w.term = f u.term v.term := by
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i hs
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨Heading.same_ok.mp hs, rfl, rfl⟩

theorem union_heading {u v w : Unrel} (h : u.union v = .ok w) :
    Heading.Same u.heading v.heading ∧ w.heading = u.heading ∧
      w.term = .call "or" [u.term, v.term] := by
  unfold union at h; exact setop_heading (f := fun a b => .call "or" [a, b]) h

theorem inter_heading {u v w : Unrel} (h : u.inter v = .ok w) :
    Heading.Same u.heading v.heading ∧ w.heading = u.heading ∧
      w.term = .call "and" [u.term, v.term] := by
  unfold inter at h; exact setop_heading (f := fun a b => .call "and" [a, b]) h

theorem diff_heading {u v w : Unrel} (h : u.diff v = .ok w) :
    Heading.Same u.heading v.heading ∧ w.heading = u.heading ∧
      w.term = .call "and" [u.term, .call "not" [v.term]] := by
  unfold diff at h
  exact setop_heading (f := fun a b => .call "and" [a, .call "not" [b]]) h

/-- ∪ holds what either operand holds, when neither term refuses (`or` evaluates both). -/
theorem union_holds {u v w : Unrel} (h : u.union v = .ok w) (hu : u.Total) (hv : v.Total)
    (t : Tuple) : w.Holds t ↔ u.Holds t ∨ v.Holds t := by
  obtain ⟨hs, hh, ht⟩ := union_heading h
  simp only [Holds, hh, ht, holds_or2]
  constructor
  · rintro ⟨f, a, b, ha, hb, e⟩
    cases a
    · cases b
      · cases e
      · exact .inr ⟨hs.fits.mp f, hb⟩
    · exact .inl ⟨f, ha⟩
  · intro hor
    have f : t.Fits u.heading := by
      rcases hor with ⟨f, _⟩ | ⟨f, _⟩
      · exact f
      · exact hs.fits.mpr f
    obtain ⟨a, ha⟩ := hu t f
    obtain ⟨b, hb⟩ := hv t (hs.fits.mp f)
    refine ⟨f, a, b, ha, hb, ?_⟩
    rcases hor with ⟨_, ha'⟩ | ⟨_, hb'⟩
    · rw [ha] at ha'; cases ha'; simp
    · rw [hb] at hb'; cases hb'; simp

theorem union_total {u v w : Unrel} (h : u.union v = .ok w) (hu : u.Total) (hv : v.Total) :
    w.Total := by
  obtain ⟨hs, hh, ht⟩ := union_heading h
  intro t f
  rw [hh] at f
  obtain ⟨a, ha⟩ := hu t f
  obtain ⟨b, hb⟩ := hv t (hs.fits.mp f)
  exact ⟨a || b, by rw [ht, holds_or2]; exact ⟨a, b, ha, hb, rfl⟩⟩

theorem union_wf {u v w : Unrel} (h : u.union v = .ok w) (hu : u.WF) (hv : v.WF) : w.WF := by
  obtain ⟨hs, hh, ht⟩ := union_heading h
  refine ⟨hh ▸ hu.nodup, fun a ha => ?_⟩
  rw [ht] at ha; rw [hh]
  simp only [Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append] at ha
  rcases ha with ha | ha
  · exact hu.reads a ha
  · exact (hs.attrs a).mpr (hv.reads a ha)

/-- ∩ holds what both operands hold. -/
theorem inter_holds {u v w : Unrel} (h : u.inter v = .ok w) (t : Tuple) :
    w.Holds t ↔ u.Holds t ∧ v.Holds t := by
  obtain ⟨hs, hh, ht⟩ := inter_heading h
  simp only [Holds, hh, ht, holds_and2]
  constructor
  · rintro ⟨f, a, b, ha, hb, e⟩
    have : a = true ∧ b = true := by simpa using e.symm
    rw [this.1] at ha; rw [this.2] at hb
    exact ⟨⟨f, ha⟩, hs.fits.mp f, hb⟩
  · rintro ⟨⟨f, ha⟩, _, hb⟩; exact ⟨f, true, true, ha, hb, rfl⟩

theorem inter_total {u v w : Unrel} (h : u.inter v = .ok w) (hu : u.Total) (hv : v.Total) :
    w.Total := by
  obtain ⟨hs, hh, ht⟩ := inter_heading h
  intro t f
  rw [hh] at f
  obtain ⟨a, ha⟩ := hu t f
  obtain ⟨b, hb⟩ := hv t (hs.fits.mp f)
  exact ⟨a && b, by rw [ht, holds_and2]; exact ⟨a, b, ha, hb, rfl⟩⟩

theorem inter_wf {u v w : Unrel} (h : u.inter v = .ok w) (hu : u.WF) (hv : v.WF) : w.WF := by
  obtain ⟨hs, hh, ht⟩ := inter_heading h
  refine ⟨hh ▸ hu.nodup, fun a ha => ?_⟩
  rw [ht] at ha; rw [hh]
  simp only [Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append] at ha
  rcases ha with ha | ha
  · exact hu.reads a ha
  · exact (hs.attrs a).mpr (hv.reads a ha)

/-- − holds what `u` holds and `v` does not, when `v`'s term never refuses. -/
theorem diff_holds {u v w : Unrel} (h : u.diff v = .ok w) (hv : v.Total) (t : Tuple) :
    w.Holds t ↔ u.Holds t ∧ ¬ v.Holds t := by
  obtain ⟨hs, hh, ht⟩ := diff_heading h
  simp only [Holds, hh, ht, holds_and2, holds_not1]
  constructor
  · rintro ⟨f, a, b, ha, ⟨c, hc, rfl⟩, e⟩
    have : a = true ∧ c = false := by simpa using e.symm
    rw [this.1] at ha; rw [this.2] at hc
    refine ⟨⟨f, ha⟩, fun ⟨_, hc'⟩ => ?_⟩
    rw [hc] at hc'; cases hc'
  · rintro ⟨⟨f, ha⟩, hn⟩
    obtain ⟨c, hc⟩ := hv t (hs.fits.mp f)
    cases c
    · exact ⟨f, true, true, ha, ⟨false, hc, rfl⟩, rfl⟩
    · exact absurd ⟨hs.fits.mp f, hc⟩ hn

theorem diff_total {u v w : Unrel} (h : u.diff v = .ok w) (hu : u.Total) (hv : v.Total) :
    w.Total := by
  obtain ⟨hs, hh, ht⟩ := diff_heading h
  intro t f
  rw [hh] at f
  obtain ⟨a, ha⟩ := hu t f
  obtain ⟨b, hb⟩ := hv t (hs.fits.mp f)
  exact ⟨a && !b, by rw [ht, holds_and2]; exact ⟨a, !b, ha, holds_not1.mpr ⟨b, hb, rfl⟩, rfl⟩⟩

theorem diff_wf {u v w : Unrel} (h : u.diff v = .ok w) (hu : u.WF) (hv : v.WF) : w.WF := by
  obtain ⟨hs, hh, ht⟩ := diff_heading h
  refine ⟨hh ▸ hu.nodup, fun a ha => ?_⟩
  rw [ht] at ha; rw [hh]
  simp only [Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append] at ha
  rcases ha with ha | ha
  · exact hu.reads a ha
  · exact (hs.attrs a).mpr (hv.reads a ha)

/-! ### ⋈ and × -/

theorem join_heading {u v w : Unrel} (h : u.join v = .ok w) :
    Finrel.joinHeading u.heading v.heading = .ok w.heading ∧
      w.term = .call "and" [u.term, v.term] := by
  simp only [join, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i j hj
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨hj, rfl⟩

/-- A tuple that fits the heading of a join restricts to one that fits the left heading. -/
theorem fits_restrict_left {h k j : Heading} (hj : Finrel.joinHeading h k = .ok j)
    (hh : h.attrs.Nodup) (hk : k.attrs.Nodup) {t : Tuple} (f : t.Fits j) :
    (t.restrict h.attrs).Fits h := by
  obtain ⟨_, hjattrs, hjlook⟩ := Finrel.joinHeading_spec hj hh hk
  refine ⟨sorted_restrict f.sorted, fun a => ?_, fun p hp d hd => ?_⟩
  · constructor
    · intro ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      exact (mem_restrict.mp hq).2
    · intro ha
      obtain ⟨q, hq, e⟩ := List.mem_map.mp ((f.attrs a).mpr ((hjattrs a).mpr (.inl ha)))
      exact List.mem_map.mpr ⟨q, mem_restrict.mpr ⟨hq, e ▸ ha⟩, e⟩
  · have hp' := mem_restrict.mp hp
    have hin : p.1 ∈ j.attrs := (hjattrs _).mpr (.inl hp'.2)
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp hin)
    have hm := f.dom p hp'.1 g hg
    rcases hjlook _ g hg with ⟨d', hd', (⟨_, rfl⟩ | ⟨e, _, hi⟩)⟩ | ⟨hna, _⟩
    · rw [mem_lookup hh hd'] at hd; cases hd; exact hm
    · rw [mem_lookup hh hd'] at hd; cases hd; exact (Domain.inter_complete hi hm).1
    · exact absurd hp'.2 hna

/-- A tuple that fits the heading of a join restricts to one that fits the right heading. -/
theorem fits_restrict_right {h k j : Heading} (hj : Finrel.joinHeading h k = .ok j)
    (hh : h.attrs.Nodup) (hk : k.attrs.Nodup) {t : Tuple} (f : t.Fits j) :
    (t.restrict k.attrs).Fits k := by
  obtain ⟨_, hjattrs, hjlook⟩ := Finrel.joinHeading_spec hj hh hk
  refine ⟨sorted_restrict f.sorted, fun a => ?_, fun p hp d hd => ?_⟩
  · constructor
    · intro ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      exact (mem_restrict.mp hq).2
    · intro ha
      obtain ⟨q, hq, e⟩ := List.mem_map.mp ((f.attrs a).mpr ((hjattrs a).mpr (.inr ha)))
      exact List.mem_map.mpr ⟨q, mem_restrict.mpr ⟨hq, e ▸ ha⟩, e⟩
  · have hp' := mem_restrict.mp hp
    have hin : p.1 ∈ j.attrs := (hjattrs _).mpr (.inr hp'.2)
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp hin)
    have hm := f.dom p hp'.1 g hg
    rcases hjlook _ g hg with ⟨d', _, (⟨hn, _⟩ | ⟨e, he, hi⟩)⟩ | ⟨_, hk'⟩
    · rw [hn] at hd; cases hd
    · rw [he] at hd; cases hd; exact (Domain.inter_complete hi hm).2
    · rw [hk'] at hd; cases hd; exact hm

/-- A scoped term has the same truth on a tuple and on its restriction to the heading. -/
theorem WF.holds_restrict {u : Unrel} (hu : u.WF) (t : Tuple) :
    u.term.holds (t.restrict u.heading.attrs) = u.term.holds t :=
  Term.holds_congr fun a ha => by rw [get?_restrict]; simp [hu.reads a ha]

/-- ⋈ holds the tuples over the joined heading whose restrictions each operand holds. -/
theorem join_holds {u v w : Unrel} (h : u.join v = .ok w) (hu : u.WF) (hv : v.WF)
    (t : Tuple) :
    w.Holds t ↔ t.Fits w.heading ∧ u.Holds (t.restrict u.heading.attrs) ∧
      v.Holds (t.restrict v.heading.attrs) := by
  obtain ⟨hj, ht⟩ := join_heading h
  simp only [Holds, ht, holds_and2, hu.holds_restrict, hv.holds_restrict]
  constructor
  · rintro ⟨f, a, b, ha, hb, e⟩
    have : a = true ∧ b = true := by simpa using e.symm
    rw [this.1] at ha; rw [this.2] at hb
    exact ⟨f, ⟨fits_restrict_left hj hu.nodup hv.nodup f, ha⟩,
      ⟨fits_restrict_right hj hu.nodup hv.nodup f, hb⟩⟩
  · rintro ⟨f, ⟨_, ha⟩, ⟨_, hb⟩⟩; exact ⟨f, true, true, ha, hb, rfl⟩

theorem join_wf {u v w : Unrel} (h : u.join v = .ok w) (hu : u.WF) (hv : v.WF) : w.WF := by
  obtain ⟨hj, ht⟩ := join_heading h
  obtain ⟨hn, hjattrs, _⟩ := Finrel.joinHeading_spec hj hu.nodup hv.nodup
  refine ⟨hn, fun a ha => ?_⟩
  rw [ht] at ha
  simp only [Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append] at ha
  rcases ha with ha | ha
  · exact (hjattrs a).mpr (.inl (hu.reads a ha))
  · exact (hjattrs a).mpr (.inr (hv.reads a ha))

theorem join_total {u v w : Unrel} (h : u.join v = .ok w) (hu : u.WF) (hv : v.WF)
    (tu : u.Total) (tv : v.Total) : w.Total := by
  obtain ⟨hj, ht⟩ := join_heading h
  intro t f
  obtain ⟨a, ha⟩ := tu _ (fits_restrict_left hj hu.nodup hv.nodup f)
  obtain ⟨b, hb⟩ := tv _ (fits_restrict_right hj hu.nodup hv.nodup f)
  rw [hu.holds_restrict] at ha; rw [hv.holds_restrict] at hb
  exact ⟨a && b, by rw [ht, holds_and2]; exact ⟨a, b, ha, hb, rfl⟩⟩

theorem disjoint_ok {who : String} {h k : Heading} :
    Heading.disjoint who h k = .ok () ↔ ∀ a ∈ h.attrs, a ∉ k.attrs := by
  unfold Heading.disjoint
  simp only
  split
  · rename_i hc
    rw [List.isEmpty_iff, List.filter_eq_nil_iff] at hc
    exact ⟨fun _ a ha hk => by simpa [hk] using hc a ha, fun _ => rfl⟩
  · rename_i hc
    refine ⟨fun h => (by cases h), fun hall => absurd ?_ hc⟩
    rw [List.isEmpty_iff, List.filter_eq_nil_iff]
    intro a ha; simp [hall a ha]

/-- × is ⋈ of operands that share no attribute. -/
theorem product_ok {u v w : Unrel} :
    u.product v = .ok w ↔ (∀ a ∈ u.heading.attrs, a ∉ v.heading.attrs) ∧ u.join v = .ok w := by
  simp only [product, bind, Except.bind]
  split
  · rename_i m hm
    refine ⟨fun h => (by cases h), fun ⟨hd, _⟩ => ?_⟩
    rw [disjoint_ok.mpr hd] at hm; cases hm
  · rename_i hd
    exact ⟨fun h => ⟨disjoint_ok.mp hd, h⟩, fun h => h.2⟩

/-- × refuses operands that share an attribute. -/
theorem product_refuses_shared {u v : Unrel} {a : String} (hu : a ∈ u.heading.attrs)
    (hv : a ∈ v.heading.attrs) : ∃ m, u.product v = .error m := by
  cases h : u.product v with
  | error m => exact ⟨m, rfl⟩
  | ok w => exact absurd hv ((product_ok.mp h).1 a hu)

end Unrel

/-- × on finite relations refuses operands that share an attribute. -/
theorem Finrel.product_refuses_shared {r s : Finrel} {a : String} (hr : a ∈ r.heading.attrs)
    (hs : a ∈ s.heading.attrs) : ∃ m, r.product s = .error m := by
  simp only [Finrel.product, bind, Except.bind]
  split
  · rename_i m _; exact ⟨m, rfl⟩
  · rename_i hd; exact absurd hs (Unrel.disjoint_ok.mp hd a hr)

theorem Finrel.product_ok {r s q : Finrel} :
    r.product s = .ok q ↔ (∀ a ∈ r.heading.attrs, a ∉ s.heading.attrs) ∧ r.join s = .ok q := by
  simp only [Finrel.product, bind, Except.bind]
  split
  · rename_i m hm
    refine ⟨fun h => (by cases h), fun ⟨hd, _⟩ => ?_⟩
    rw [Unrel.disjoint_ok.mpr hd] at hm; cases hm
  · rename_i hd
    exact ⟨fun h => ⟨Unrel.disjoint_ok.mp hd, h⟩, fun h => h.2⟩

/-- × on finite relations gives a well-formed relation: it is ⋈ on operands that share no
attribute. -/
theorem Finrel.product_wf {r s q : Finrel} (h : r.product s = .ok q) (hr : r.WF)
    (hs : s.WF) : q.WF :=
  Finrel.join_wf (Finrel.product_ok.mp h).2 hr hs


/-! ## ρ -/

section Rename
open Finrel

theorem Tuple.Fits.ofPairs {H : Heading} {ps : List (String × Value)} (hn : (ps.map (·.1)).Nodup)
    (ha : ∀ a, a ∈ ps.map (·.1) ↔ a ∈ H.attrs)
    (hd : ∀ p ∈ ps, ∀ d, H.lookup p.1 = some d → d.mem p.2 = true) :
    (Tuple.ofPairs ps).Fits H where
  sorted := Tuple.sorted_ofPairs hn
  attrs a := by
    have hp := List.mergeSort_perm ps fun p q => decide (p.1 ≤ q.1)
    rw [← ha]; exact (hp.map (·.1)).mem_iff
  dom p hp d hd' := hd p ((List.mergeSort_perm ps _).mem_iff.mp hp) d hd'

/-- Looking up a renamed key, when the renaming is injective on the keys. -/
theorem lookup_map_inj {β : Type} {a : String} {f : String → String} :
    ∀ (l : List (String × β)), a ∈ l.map (·.1) →
      (∀ x ∈ l.map (·.1), ∀ y ∈ l.map (·.1), f x = f y → x = y) →
      (l.map fun (p : String × β) => (f p.1, p.2)).lookup (f a) = l.lookup a
  | [], h, _ => by cases h
  | (b, v) :: l, h, hi => by
    simp only [List.map_cons, List.lookup]
    by_cases e : a = b
    · subst e; simp
    · have hne : f a ≠ f b := fun h' => e (hi a h b (by simp) h')
      have ha : a ∈ l.map (·.1) := by simpa [e] using h
      have h1 : (a == b) = false := by simp [e]
      have h2 : (f a == f b) = false := by simp [hne]
      simp only [h1, h2]
      simpa using lookup_map_inj l ha (fun x hx y hy => hi x (by simp [hx]) y (by simp [hy]))

theorem get?_renameTuple {ren : List (String × String)} {s : Tuple}
    (hn : s.attrs.Nodup)
    (hi : ∀ x ∈ s.attrs, ∀ y ∈ s.attrs, renameAttr ren x = renameAttr ren y → x = y)
    {a : String} (ha : a ∈ s.attrs) :
    (renameTuple ren s).get? (renameAttr ren a) = s.get? a := by
  have hk : ((s.map fun (p : String × Value) => (renameAttr ren p.1, p.2)).map (·.1)) =
      s.attrs.map (renameAttr ren) := by simp [Tuple.attrs]
  rw [renameTuple, Tuple.get?_ofPairs (hk ▸ nodup_map_of_inj hn hi)]
  exact lookup_map_inj s ha hi

/-- A renamed term on a renamed tuple has the value the term has on the tuple, when the
term reads only the tuple's attributes and the renaming is injective on them. -/
theorem Term.eval_rename {ren : List (String × String)} {s : Tuple} (hn : s.attrs.Nodup)
    (hi : ∀ x ∈ s.attrs, ∀ y ∈ s.attrs, renameAttr ren x = renameAttr ren y → x = y) :
    ∀ (e : Term), (∀ a ∈ e.attrs, a ∈ s.attrs) →
      (e.rename ren).eval (renameTuple ren s) = e.eval s
  | .attr a, h => by
    simp only [Term.rename, Term.eval, get?_renameTuple hn hi (h a (by simp [Term.attrs]))]
    have ha := h a (by simp [Term.attrs])
    cases hg : s.get? a with
    | some v => rfl
    | none =>
      exfalso
      have : (s.lookup a).isSome := by
        rw [Finrel.lookup_isSome]; exact ha
      simp only [Tuple.get?] at hg; rw [hg] at this; cases this
  | .val v, _ => by simp [Term.rename, Term.eval]
  | .call op args, h => by
    have : (args.map (Term.rename ren)).mapM (Term.eval (renameTuple ren s)) =
        args.mapM (Term.eval s) := by
      rw [List.mapM_map]
      apply mapM_congr_ok
      intro e he
      exact Term.eval_rename hn hi e (fun a ha => h a (by
          simp only [Term.attrs, List.mem_flatMap]; exact ⟨e, he, ha⟩))
    simp only [Term.rename, Term.eval, this]

/-- A renamed term reads only renamed attributes of the term. -/
theorem Term.attrs_rename {ren : List (String × String)} :
    ∀ (e : Term) {a : String}, a ∈ (e.rename ren).attrs → ∃ b ∈ e.attrs, a = renameAttr ren b
  | .attr x, a, h => by simp [Term.rename, Term.attrs] at h; exact ⟨x, by simp [Term.attrs], h⟩
  | .val _, a, h => by simp [Term.rename, Term.attrs] at h
  | .call op args, a, h => by
    simp only [Term.rename, Term.attrs, List.flatMap_map, List.mem_flatMap] at h
    obtain ⟨e, he, ha⟩ := h
    obtain ⟨b, hb, rfl⟩ := Term.attrs_rename e ha
    exact ⟨b, by simp only [Term.attrs, List.mem_flatMap]; exact ⟨e, he, hb⟩, rfl⟩

theorem renameHeading_attrs (ren : List (String × String)) (h : Heading) :
    (renameHeading ren h).attrs = h.attrs.map (renameAttr ren) := by
  simp [renameHeading, Heading.attrs]

namespace Unrel

theorem rename_eq {ren : List (String × String)} {u w : Unrel} (h : u.rename ren = .ok w) :
    ((∀ p ∈ ren, p.1 ∈ u.heading.attrs) ∧ (renameHeading ren u.heading).attrs.Nodup) ∧
      w = ⟨renameHeading ren u.heading, u.term.rename ren⟩ := by
  simp only [rename, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i hc
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨Heading.renameCheck_ok.mp hc, h.symm⟩

/-- After ρ's check, the renaming is injective on the heading's attributes. -/
theorem rename_inj {ren : List (String × String)} {h : Heading}
    (hn : (renameHeading ren h).attrs.Nodup) :
    ∀ x ∈ h.attrs, ∀ y ∈ h.attrs, renameAttr ren x = renameAttr ren y → x = y := by
  rw [renameHeading_attrs] at hn
  exact inj_of_nodup_map hn

/-- A tuple that fits a heading, renamed, fits the renamed heading. -/
theorem fits_renameTuple {ren : List (String × String)} {h : Heading} {s : Tuple}
    (hn : (renameHeading ren h).attrs.Nodup) (f : s.Fits h) :
    (renameTuple ren s).Fits (renameHeading ren h) := by
  have hi := rename_inj hn
  have hs : ∀ x ∈ s.attrs, ∀ y ∈ s.attrs, renameAttr ren x = renameAttr ren y → x = y :=
    fun x hx y hy => hi x ((f.attrs x).mp hx) y ((f.attrs y).mp hy)
  have hk : ((s.map fun (p : String × Value) => (renameAttr ren p.1, p.2)).map (·.1)) =
      s.attrs.map (renameAttr ren) := by simp [Tuple.attrs]
  refine Tuple.Fits.ofPairs (hk ▸ nodup_map_of_inj f.nodup hs) (fun a => ?_) (fun p hp d hd => ?_)
  · rw [hk, renameHeading_attrs, List.mem_map, List.mem_map]
    exact ⟨fun ⟨b, hb, e⟩ => ⟨b, (f.attrs b).mp hb, e⟩, fun ⟨b, hb, e⟩ => ⟨b, (f.attrs b).mpr hb, e⟩⟩
  · obtain ⟨⟨b, v⟩, hbv, rfl⟩ := List.mem_map.mp hp
    have hb : b ∈ h.attrs := (f.attrs b).mp (List.mem_map_of_mem (f := (·.1)) hbv)
    have : (renameHeading ren h).lookup (renameAttr ren b) = h.lookup b :=
      lookup_map_inj h hb hi
    rw [this] at hd
    exact f.dom _ hbv d hd

/-- ρ holds the renamed tuples of what `u` holds. -/
theorem rename_holds {ren : List (String × String)} {u w : Unrel} (h : u.rename ren = .ok w)
    (hu : u.WF) {s : Tuple} (f : s.Fits u.heading) :
    w.Holds (renameTuple ren s) ↔ u.Holds s := by
  obtain ⟨⟨_, hn⟩, rfl⟩ := rename_eq h
  have hi := rename_inj hn
  have hs : ∀ x ∈ s.attrs, ∀ y ∈ s.attrs, renameAttr ren x = renameAttr ren y → x = y :=
    fun x hx y hy => hi x ((f.attrs x).mp hx) y ((f.attrs y).mp hy)
  have he : (u.term.rename ren).holds (renameTuple ren s) = u.term.holds s := by
    simp only [Term.holds, Term.eval_rename f.nodup hs u.term
      (fun a ha => (f.attrs a).mpr (hu.reads a ha))]
  simp only [Holds, he]
  exact ⟨fun ⟨_, ht⟩ => ⟨f, ht⟩, fun ⟨_, ht⟩ => ⟨fits_renameTuple hn f, ht⟩⟩

/-- Every tuple that fits the renamed heading is a renamed tuple that fits the heading. -/
theorem rename_onto {ren : List (String × String)} {u w : Unrel} (h : u.rename ren = .ok w)
    (hu : u.WF) {t : Tuple} (f : t.Fits w.heading) :
    ∃ s, s.Fits u.heading ∧ t = renameTuple ren s := by
  obtain ⟨⟨_, hn⟩, rfl⟩ := rename_eq h
  have hi := rename_inj hn
  let ps : List (String × Value) :=
    u.heading.map fun (a, _) => (a, (t.get? (renameAttr ren a)).getD default)
  have hpk : ps.map (·.1) = u.heading.attrs := by simp [ps, Heading.attrs]
  have hget : ∀ a ∈ u.heading.attrs, t.get? (renameAttr ren a) =
      some ((t.get? (renameAttr ren a)).getD default) := by
    intro a ha
    have : renameAttr ren a ∈ (renameHeading ren u.heading).attrs := by
      rw [renameHeading_attrs]; exact List.mem_map_of_mem ha
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((f.get?_isSome _).mpr this)
    rw [hv]; rfl
  have fs : (Tuple.ofPairs ps).Fits u.heading := by
    refine Tuple.Fits.ofPairs (hpk ▸ hu.nodup) (fun a => by rw [hpk]) (fun p hp d hd => ?_)
    obtain ⟨⟨a, e⟩, hae, rfl⟩ := List.mem_map.mp hp
    have ha : a ∈ u.heading.attrs := List.mem_map_of_mem (f := (·.1)) hae
    have hrl : (renameHeading ren u.heading).lookup (renameAttr ren a) = u.heading.lookup a :=
      lookup_map_inj u.heading ha hi
    have hd' : (renameHeading ren u.heading).lookup (renameAttr ren a) = some d := by
      rw [hrl]; exact hd
    have := f.dom (renameAttr ren a, (t.get? (renameAttr ren a)).getD default)
      (lookup_mem (hget a ha)) d hd'
    exact this
  refine ⟨_, fs, Tuple.ext_get? f.sorted (fits_renameTuple hn fs).sorted fun c => ?_⟩
  have hsi : ∀ x ∈ (Tuple.ofPairs ps).attrs, ∀ y ∈ (Tuple.ofPairs ps).attrs,
      renameAttr ren x = renameAttr ren y → x = y :=
    fun x hx y hy => hi x ((fs.attrs x).mp hx) y ((fs.attrs y).mp hy)
  by_cases hc : c ∈ (renameHeading ren u.heading).attrs
  · rw [renameHeading_attrs] at hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    rw [get?_renameTuple fs.nodup hsi ((fs.attrs a).mpr ha),
      Tuple.get?_ofPairs (hpk ▸ hu.nodup), hget a ha]
    have hl : ps.lookup a = some ((t.get? (renameAttr ren a)).getD default) := by
      apply mem_lookup (hpk ▸ hu.nodup)
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      exact List.mem_map.mpr ⟨q, hq, rfl⟩
    rw [hl]
  · rw [f.get?_none hc, (fits_renameTuple hn fs).get?_none hc]

theorem rename_wf {ren : List (String × String)} {u w : Unrel} (h : u.rename ren = .ok w)
    (hu : u.WF) : w.WF := by
  obtain ⟨⟨_, hn⟩, rfl⟩ := rename_eq h
  refine ⟨hn, fun a ha => ?_⟩
  obtain ⟨b, hb, rfl⟩ := Term.attrs_rename u.term ha
  rw [renameHeading_attrs]
  exact List.mem_map_of_mem (hu.reads b hb)

theorem rename_total {ren : List (String × String)} {u w : Unrel} (h : u.rename ren = .ok w)
    (hu : u.WF) (tu : u.Total) : w.Total := by
  intro t f
  obtain ⟨s, fs, rfl⟩ := rename_onto h hu f
  obtain ⟨⟨_, hn⟩, rfl⟩ := rename_eq h
  have hi := rename_inj hn
  have hs : ∀ x ∈ s.attrs, ∀ y ∈ s.attrs, renameAttr ren x = renameAttr ren y → x = y :=
    fun x hx y hy => hi x ((fs.attrs x).mp hx) y ((fs.attrs y).mp hy)
  obtain ⟨b, hb⟩ := tu s fs
  refine ⟨b, ?_⟩
  simp only [Term.holds, Term.eval_rename fs.nodup hs u.term
    (fun a ha => (fs.attrs a).mpr (hu.reads a ha))]
  exact hb

end Unrel

end Rename

/-! ## Lift: a finite relation as an unrestricted one -/

/-- One tuple of a finite relation as a test: `and` of `a = v` for each of its pairs. -/
theorem holds_tupleTest {h : Heading} (hm : h.Unmixed) {t u : Tuple} (ft : t.Fits h)
    (fu : u.Fits h) :
    (Term.call "and" (u.map fun (a, v) => Term.call "=" [.attr a, .val v])).holds t =
      .ok (decide (t = u)) := by
  -- each pair's test is `t.get? a == some v`
  have hpair : ∀ q ∈ u, (Term.call "=" [.attr q.1, .val q.2]).holds t =
      .ok (decide (t.get? q.1 = some q.2)) := by
    intro q hq
    have hqa : q.1 ∈ h.attrs := (fu.attrs q.1).mp (List.mem_map_of_mem hq)
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp hqa)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((ft.get?_isSome q.1).mpr hqa)
    have hxm : d.mem x = true := ft.dom (q.1, x) (lookup_mem hx) d hd
    have hqm : d.mem q.2 = true := fu.dom q hq d hd
    have he := applyOp_eq_unmixed (hm _ (lookup_mem hd)) hxm hqm
    rw [Term.holds_ok]
    simp only [Term.eval, hx, List.mapM_cons, List.mapM_nil, bind, Except.bind, pure,
      Except.pure, he]
    cases hxq : x == q.2 <;> simp_all
  let p : Term → Bool := fun e => match e.holds t with | .ok b => b | .error _ => false
  have hall : ∀ e ∈ u.map (fun (a, v) => Term.call "=" [.attr a, .val v]),
      e.holds t = .ok (p e) := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
    simp only [p, hpair q hq]
  rw [holds_andN hall]
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq]
  have hp : ∀ q ∈ u, p (Term.call "=" [.attr q.1, .val q.2]) = decide (t.get? q.1 = some q.2) :=
    fun q hq => by simp only [p, hpair q hq]
  simp only [List.mem_map]
  constructor
  · intro hq
    refine Tuple.ext_get? ft.sorted fu.sorted fun a => ?_
    by_cases ha : a ∈ h.attrs
    · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp ((fu.get?_isSome a).mpr ha)
      have := hq _ ⟨(a, y), lookup_mem hy, rfl⟩
      rw [hp _ (lookup_mem hy), decide_eq_true_eq] at this
      rw [this, hy]
    · rw [ft.get?_none ha, fu.get?_none ha]
  · rintro rfl e ⟨q, hq, rfl⟩
    rw [hp q hq, decide_eq_true_eq]
    exact mem_lookup (Tuple.nodup_keys fu.sorted) hq

/-- Lift holds exactly the tuples of the finite relation. -/
theorem Finrel.toUnrel_holds {r : Finrel} (hr : r.WF) (hm : r.heading.Unmixed) (t : Tuple) :
    r.toUnrel.Holds t ↔ t ∈ r.tuples := by
  let p : Term → Bool := fun e => match e.holds t with | .ok b => b | .error _ => false
  have key : t.Fits r.heading → r.toUnrel.term.holds t = .ok (decide (t ∈ r.tuples)) := by
    intro ft
    have hall : ∀ e ∈ r.tuples.map (fun u => Term.call "and"
        (u.map fun (a, v) => Term.call "=" [.attr a, .val v])), e.holds t = .ok (p e) := by
      intro e he
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
      simp only [p, holds_tupleTest hm ft (hr.fits u hu)]
    simp only [Finrel.toUnrel]
    rw [holds_orN hall]
    congr 1
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
    simp only [List.mem_map]
    constructor
    · rintro ⟨e, ⟨u, hu, rfl⟩, he⟩
      simp only [p, holds_tupleTest hm ft (hr.fits u hu), decide_eq_true_eq] at he
      exact he ▸ hu
    · intro ht
      exact ⟨_, ⟨t, ht, rfl⟩, by simp [p, holds_tupleTest hm ft (hr.fits t ht)]⟩
  constructor
  · rintro ⟨ft, h⟩
    rw [key ft] at h
    simpa using h
  · intro ht
    have ft := hr.fits t ht
    exact ⟨ft, by rw [key ft]; simp [ht]⟩

theorem Finrel.toUnrel_total {r : Finrel} (hr : r.WF) (hm : r.heading.Unmixed) :
    r.toUnrel.Total := by
  intro t ft
  by_cases ht : t ∈ r.tuples
  · exact ⟨true, ((Finrel.toUnrel_holds hr hm t).mpr ht).2⟩
  · -- every test evaluates, so the `or` does
    have hall : ∀ e ∈ r.tuples.map (fun u => Term.call "and"
        (u.map fun (a, v) => Term.call "=" [.attr a, .val v])),
        e.holds t = .ok (match e.holds t with | .ok b => b | .error _ => false) := by
      intro e he
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp he
      simp only [holds_tupleTest hm ft (hr.fits u hu)]
    exact ⟨_, holds_orN hall⟩

theorem Finrel.toUnrel_wf {r : Finrel} (hr : r.WF) : r.toUnrel.WF := by
  refine ⟨hr.nodup, fun a ha => ?_⟩
  simp only [Finrel.toUnrel, Term.attrs, List.flatMap_map, List.mem_flatMap] at ha
  obtain ⟨u, hu, q, hq, ha⟩ := ha
  obtain ⟨e, he, hae⟩ := ha
  have : a = q.1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [Term.attrs] at hae; exact hae
  subst this
  exact ((hr.fits u hu).attrs q.1).mp (List.mem_map_of_mem hq)

end Rasso
