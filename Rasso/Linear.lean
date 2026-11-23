import Rasso.LinRead

/-!
# Rasso: removing an attribute by linear arithmetic, proved

The executable part is `Rasso.LinElim`; reading terms as forms is proved in `Rasso.LinRead`.

* The specification `LinIn`: the shared normal form's `NF.In`, with the leaf a comparison
  `= < <= > >=` of two operands, each read as a linear form.
* `leaf_sem`: a comparison is its row `c·x + L ⋈ 0`; with `c ≠ 0` the row is the bound
  `x ⋈ −L/c` (`test_row`), flipped when `c < 0`; with `c = 0` it is `L ⋈ 0`, without `x`.
* `xpart_sem`: Fourier's step of dense order (`Dense.xpart_sem_num`), on the rendered bounds.
* `elim_sound`: removal by linear arithmetic is sound, an instance of `NF.elim_sound` with
  the rationals as the values of `a`.
* `accepts_iff`: the test decides the specification.
-/

namespace Rasso.Linear

open Dense (XRel qOf NumOn)

/-! ## Rows and bounds -/

theorem mul_sign {c y : Rat} (hc : 0 < c) : (c * y < 0 ↔ y < 0) ∧ (c * y = 0 ↔ y = 0) := by
  refine ⟨Rat.mul_neg_iff_of_pos_left hc, ?_⟩
  rw [Rat.mul_eq_zero]; constructor
  · rintro (h | h)
    · exact absurd h (Rat.ne_of_gt hc)
    · exact h
  · exact .inr

/-- `c·d + l ⋈ 0`, with `c ≠ 0`, is a bound on `d`: `d ⋈ -l/c`, with `⋈` flipped when `c < 0`. -/
theorem test_row (r : XRel) {c : Rat} (hc : c ≠ 0) (d l : Rat) :
    r.test (c * d + l) 0 = (if 0 < c then r else r.flip).test d ((-1 / c) * l) := by
  have hq : c * ((-1 / c) * l) = -l := by
    have := Rat.mul_inv_cancel c hc
    rw [Rat.div_def]; grind
  have he : c * d + l = c * (d - (-1 / c) * l) := by
    grind
  rw [he]
  generalize (-1 / c) * l = q
  by_cases hp : 0 < c
  · obtain ⟨h1, h2⟩ := mul_sign (y := d - q) hp
    simp only [hp, ↓reduceIte]
    cases r <;> simp only [XRel.test, decide_eq_decide] <;> grind
  · have hn : 0 < -c := by grind
    obtain ⟨h1, h2⟩ := mul_sign (y := d - q) hn
    have e : -c * (d - q) = -(c * (d - q)) := Rat.neg_mul _ _
    simp only [hp, ↓reduceIte]
    cases r <;> simp only [XRel.test, XRel.flip, decide_eq_decide] <;> grind

theorem test_sub (r : XRel) (q q' : Rat) : r.test q q' = r.test (q - q') 0 := by
  cases r <;> simp only [XRel.test, decide_eq_decide] <;> grind

/-! ## The specification -/

/-- The leaves the class accepts: a comparison of two operands, each read as a linear form. -/
def LinOk (h : Heading) (a : String) (op : String) (es : List Term) : Prop :=
  ∃ r l r' Ll Lr, XRel.ofOp op = some r ∧ es = [l, r'] ∧
    Lin.ofTerm? (okAttr h a) l = some Ll ∧ Lin.ofTerm? (okAttr h a) r' = some Lr

/-- `e` is a term in which every comparison that mentions `a` compares two linear terms, in
a Boolean skeleton of `and`, `or` and `not`. A part that does not mention `a` may be anything. -/
abbrev LinIn (h : Heading) (a : String) : Term → Prop := NF.In (LinOk h a) a

/-! ## The values of the attributes -/

/-- The number each attribute is on `t` (0 when it is not a number). -/
def sig (t : Tuple) (b : String) : Rat := ((t.get? b).bind Value.exact?).getD 0

/-- The numbers on `t` with `a` set to `d`. -/
def sigSet (t : Tuple) (a : String) (d : Rat) (b : String) : Rat := if b = a then d else sig t b

variable {h : Heading} {a : String} {t : Tuple} {d : Rat}

/-- An attribute that a linear term may read, other than `a`, is an exact number on a tuple
that fits the heading without `a`. -/
theorem get_sig (f : t.Fits (h.filter (·.1 ≠ a))) {b : String} (hb : okAttr h a b = true)
    (hba : b ≠ a) : t.get? b = some (Value.ofRat (sig t b)) := by
  have hn : Dense.numOperand? h a (.attr b) = true := by
    simp only [okAttr, Bool.or_eq_true, beq_iff_eq, hba, false_or] at hb
    simp [Dense.numOperand?, hba, hb]
  obtain ⟨v, hv, hq⟩ := Dense.numOperand_eval hn f
  have hg : t.get? b = some v := by
    simp only [Term.eval] at hv
    split at hv
    · rename_i w hw; cases hv; exact hw
    · cases hv
  have hs : sig t b = qOf t (.attr b) := by simp [sig, hg, hq]
  rw [hg, hs, ← Value.eq_ofRat hq]

theorem get_sigSet (ht : Tuple.Sorted t) (f : t.Fits (h.filter (·.1 ≠ a))) {b : String}
    (hb : okAttr h a b = true) :
    (t.set a (Value.ofRat d)).get? b = some (Value.ofRat (sigSet t a d b)) := by
  rw [Tuple.get?_set ht]
  by_cases e : b = a
  · simp [sigSet, e]
  · simp [sigSet, e, get_sig f hb e]

/-- The row of a comparison reads only attributes of the comparison, never `a`, each one a
linear term may read. -/
theorem row_attrs {l r' : Term} {Ll Lr : Lin} {op : String}
    (hl : Lin.ofTerm? (okAttr h a) l = some Ll) (hr : Lin.ofTerm? (okAttr h a) r' = some Lr) :
    ∀ y ∈ ((Ll.sub Lr).drop a).attrs,
      y ∈ (Term.call op [l, r']).attrs ∧ y ≠ a ∧ okAttr h a y = true := by
  intro y hy
  obtain ⟨hy, hya⟩ := Lin.attrs_drop hy
  obtain ⟨ok1, at1⟩ := Lin.ofTerm?_attrs l Ll hl
  obtain ⟨ok2, at2⟩ := Lin.ofTerm?_attrs r' Lr hr
  rcases Lin.attrs_sub.mp hy with hy | hy
  · exact ⟨by simp [Term.attrs, at1 y hy], hya, ok1 y (at1 y hy)⟩
  · exact ⟨by simp [Term.attrs, at2 y hy], hya, ok2 y (at2 y hy)⟩

/-! ## The class's leaves, for the shared normal form -/

/-- A bound `x ⋈ B` is true on `t` when `x` is `d`. -/
def XSem (t : Tuple) (d : Rat) (x : XRel × Lin) : Prop := x.1.test d (x.2.eval (sig t)) = true

/-- What the normal form promises of a bound: its form reads only `R`, never `a`, and only
attributes that are numbers on `t`. -/
def XGood (a : String) (t : Tuple) (R : List String) (x : XRel × Lin) : Prop :=
  ∀ y ∈ x.2.attrs, y ∈ R ∧ y ≠ a ∧ t.get? y = some (Value.ofRat (sig t y))

theorem leaf_eq {p : Bool} {r : XRel} {l r' : Term} {Ll Lr : Lin}
    (hr : XRel.ofOp r.op = some r) (hl : Lin.ofTerm? (okAttr h a) l = some Ll)
    (hr' : Lin.ofTerm? (okAttr h a) r' = some Lr) :
    leaf h a p r.op [l, r'] = row p r ((Ll.sub Lr).coeff a) ((Ll.sub Lr).drop a) := by
  simp [leaf, hr, hl, hr']

open NF in
/-- The class's leaf is right: a comparison of two linear terms, under a sign, has a normal
form that means it. -/
theorem leaf_sem (ht : Tuple.Sorted t) (f : t.Fits (h.filter (·.1 ≠ a))) :
    ∀ {op : String} {es : List Term}, op ≠ "and" → op ≠ "or" → op ≠ "not" → LinOk h a op es →
      a ∈ (Term.call op es).attrs → ∀ {R : List String}, (∀ x ∈ (Term.call op es).attrs, x ∈ R) →
      ∀ (p b : Bool), (Term.call op es).holds (t.set a (Value.ofRat d)) = .ok b →
      NF.DnfOk (XSem t d) (XGood a t) a t R p b (leaf h a p op es) := by
  intro op es _ _ _ hA _ R hR p b hb
  obtain ⟨r, l, r', Ll, Lr, hr, rfl, hl, hr'⟩ := hA
  have hop := Dense.XRel.ofOp_some hr
  subst hop
  rw [leaf_eq hr hl hr']
  obtain ⟨ok1, _⟩ := Lin.ofTerm?_attrs l Ll hl
  obtain ⟨ok2, _⟩ := Lin.ofTerm?_attrs r' Lr hr'
  have el := Lin.ofTerm?_eval l Ll (fun y hy => get_sigSet (d := d) ht f (ok1 y hy)) hl
  have er := Lin.ofTerm?_eval r' Lr (fun y hy => get_sigSet (d := d) ht f (ok2 y hy)) hr'
  rw [holds_cmp r el (Value.exact?_ofRat _) er (Value.exact?_ofRat _)] at hb
  cases hb
  have hra := row_attrs (op := r.op) hl hr'
  have hD : r.test (Ll.eval (sigSet t a d)) (Lr.eval (sigSet t a d)) =
      r.test ((Ll.sub Lr).coeff a * d + ((Ll.sub Lr).drop a).eval (sig t)) 0 := by
    rw [test_sub, ← Lin.eval_sub, Lin.eval_split (sigSet t a d) a (Ll.sub Lr)]
    have e1 : sigSet t a d a = d := by simp [sigSet]
    rw [e1, Lin.eval_congr (τ := sig t) ((Ll.sub Lr).drop a)
      (fun y hy => by simp [sigSet, (Lin.attrs_drop hy).2])]
  rw [hD]
  generalize (Ll.sub Lr).coeff a = c at *
  generalize (Ll.sub Lr).drop a = L at *
  have hLg : ∀ y ∈ L.attrs, t.get? y = some (Value.ofRat (sig t y)) :=
    fun y hy => get_sig f (hra y hy).2.2 (hra y hy).2.1
  unfold row
  split
  · rename_i hc
    subst hc
    have hh : (Term.call r.op [L.render, .val (.int 0)]).holds t =
        .ok (r.test (L.eval (sig t)) 0) :=
      holds_cmp r (Lin.render_eval L hLg) (Value.exact?_ofRat _)
        (w := .int 0) (q' := 0) (by simp [Term.eval]) (by simp [Value.exact?])
    have hat : ∀ y ∈ (Term.call r.op [L.render, .val (.int 0)]).attrs,
        y ∈ R ∧ y ≠ a := by
      intro y hy
      simp only [Term.attrs, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        ] at hy
      have := hra y (Lin.attrs_render.mp hy)
      exact ⟨hR y this.1, this.2.1⟩
    refine ⟨fun c hc l hl => ?_, ?_⟩
    · simp only [List.mem_singleton] at hc; subst hc
      simp only [List.mem_singleton] at hl; subst hl
      exact ⟨fun hy => (hat a hy).2 rfl, ⟨_, hh⟩, fun y hy => (hat y hy).1⟩
    · simp only [List.mem_singleton, exists_eq_left, forall_eq, Lit.Sem, hh, Except.ok.injEq,
        Rat.zero_mul, Rat.zero_add]
  · rename_i hc
    have key : ∀ s : XRel, (if 0 < c then s else s.flip).test d ((L.scale (-1 / c)).eval (sig t)) =
        s.test (c * d + L.eval (sig t)) 0 := by
      intro s; rw [Lin.eval_scale, test_row s hc]
    refine ⟨fun c' hc' l hl => ?_, ?_⟩
    · obtain ⟨s, _, rfl⟩ := List.mem_map.mp hc'
      simp only [List.mem_singleton] at hl; subst hl
      intro y hy
      have hy := Lin.attrs_scale.mp hy
      exact ⟨hR y (hra y hy).1, (hra y hy).2.1, hLg y hy⟩
    · simp only [List.mem_map]
      constructor
      · rintro ⟨_, ⟨s, hs, rfl⟩, hl⟩
        have := hl _ List.mem_cons_self
        simp only [Lit.Sem, XSem, key] at this
        cases p
        · simp only [Bool.false_eq_true, ↓reduceIte] at hs
          exact (Dense.XRel.test_neg r _ _).mp ⟨s, hs, this⟩
        · simp only [↓reduceIte, List.mem_singleton] at hs; subst hs; exact this
      · intro hp
        cases p
        · obtain ⟨s, hs, hst⟩ := (Dense.XRel.test_neg r _ _).mpr hp
          exact ⟨_, ⟨s, by simpa using hs, rfl⟩, by simpa [Lit.Sem, XSem, key] using hst⟩
        · exact ⟨_, ⟨r, by simp, rfl⟩, by simpa [Lit.Sem, XSem, key] using hp⟩

/-! ## One conjunction: Fourier's step on the bounds -/

theorem xpart_sem {R : List String} {xs : List (XRel × Lin)} (hx : ∀ x ∈ xs, XGood a t R x) :
    (∀ e ∈ xpart xs, (∃ b, e.holds t = .ok b) ∧ ∀ x ∈ e.attrs, x ∈ R) ∧
      ((∀ e ∈ xpart xs, e.holds t = .ok true) ↔ ∃ d, ∀ x ∈ xs, XSem t d x) := by
  have hev : ∀ x ∈ xs, x.2.render.eval t = .ok (Value.ofRat (x.2.eval (sig t))) :=
    fun x hx' => Lin.render_eval x.2 (fun y hy => (hx x hx' y hy).2.2)
  have hq : ∀ x ∈ xs, qOf t x.2.render = x.2.eval (sig t) :=
    fun x hx' => Dense.eval_qOf (hev x hx') (Value.exact?_ofRat _)
  have := Dense.xpart_sem_num (t := t) (R := R) (xs := xs.map fun x => (x.1, x.2.render))
    (fun p hp => by
      obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hp
      exact ⟨⟨_, hev x hx', by rw [Value.exact?_ofRat, hq x hx']⟩,
        fun y hy => (hx x hx' y (Lin.attrs_render.mp hy)).1⟩)
  refine ⟨this.1, this.2.trans ?_⟩
  simp only [List.mem_map, forall_exists_index, and_imp, XSem]
  constructor
  · rintro ⟨d, hd⟩; exact ⟨d, fun x hx' => by rw [← hq x hx']; exact hd _ x hx' rfl⟩
  · rintro ⟨d, hd⟩; exact ⟨d, fun _ x hx' e => by subst e; rw [hq x hx']; exact hd x hx'⟩

/-! ## What the new term reads -/

theorem leaf_attrs :
    ∀ {op : String} {es : List Term}, LinOk h a op es → a ∈ (Term.call op es).attrs →
      ∀ (p : Bool), ∀ c ∈ leaf h a p op es, ∀ l ∈ c, ∀ x ∈ l.attrs (fun y : XRel × Lin => y.2.attrs),
        x ∈ (Term.call op es).attrs ∧ x ≠ a := by
  intro op es hA _ p c hc l hl x hx
  obtain ⟨r, l', r', Ll, Lr, hr, rfl, hl', hr'⟩ := hA
  have hop := Dense.XRel.ofOp_some hr
  subst hop
  rw [leaf_eq hr hl' hr'] at hc
  have hra := row_attrs (op := r.op) hl' hr'
  unfold row at hc
  split at hc
  · simp only [List.mem_singleton] at hc; subst hc
    simp only [List.mem_singleton] at hl; subst hl
    simp only [NF.Lit.attrs, Term.attrs, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at hx
    have := hra x (Lin.attrs_render.mp hx)
    exact ⟨this.1, this.2.1⟩
  · obtain ⟨s, _, rfl⟩ := List.mem_map.mp hc
    simp only [List.mem_singleton] at hl; subst hl
    have := hra x (Lin.attrs_scale.mp hx)
    exact ⟨this.1, this.2.1⟩

theorem xpart_attrs (xs : List (XRel × Lin)) (e : Term) (he : e ∈ xpart xs) :
    ∀ x ∈ e.attrs, ∃ l ∈ xs, x ∈ l.2.attrs := by
  intro x hx
  obtain ⟨p, hp, hx'⟩ := Dense.xpart_attrs _ e he x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
  exact ⟨l, hl, Lin.attrs_render.mp hx'⟩

/-! ## The class obligation -/

/-- **Removal by linear arithmetic is sound.** With `a`'s domain the rat kind and every
comparison that mentions `a` a comparison of linear terms, the new term reads only the
remaining attributes, never refuses on a fitting tuple, and holds `t` exactly when some
value of `a` makes the old term hold. An instance of `NF.elim_sound`. -/
theorem elim_sound {u : Unrel} {a : String} (hd : u.heading.lookup a = some (.kind .rat))
    (hacc : LinIn u.heading a u.term) (hu : u.WF) (tu : u.Total) :
    let w : Unrel := ⟨u.heading.filter (·.1 ≠ a), elim u.heading a u.term⟩
    (∀ x ∈ w.term.attrs, x ∈ w.heading.attrs) ∧ w.Total ∧
      ∀ t, t.Fits w.heading → (w.Holds t ↔ ∃ v, u.Holds (t.set a v)) :=
  NF.elim_sound (at' := fun y : XRel × Lin => y.2.attrs) hd Value.ofRat
    (fun q => by simp [Domain.mem, Dense.rat_has_ofRat])
    (fun v hv => by
      obtain ⟨q, hq⟩ := Dense.rat_has (by simpa [Domain.mem] using hv)
      exact ⟨q, Value.eq_ofRat hq⟩)
    (0 : Rat) (fun t d => XSem t d) (fun t => XGood a t) hacc hu tu
    (fun _ f _ => leaf_sem f.sorted f) (fun _ f _ _ hx => xpart_sem hx) leaf_attrs xpart_attrs

/-! ## The test decides the specification -/

theorem leafOk_sound {op : String} {es : List Term} (hok : leafOk h a op es = true) :
    LinOk h a op es := by
  unfold leafOk at hok
  split at hok
  · rename_i r l r' hr
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hok
    obtain ⟨⟨Ll, hl⟩, ⟨Lr, hr'⟩⟩ := hok
    exact ⟨r, l, r', Ll, Lr, hr, rfl, hl, hr'⟩
  · cases hok

theorem leafOk_complete {op : String} {es : List Term} (hA : LinOk h a op es) :
    leafOk h a op es = true := by
  obtain ⟨r, l, r', Ll, Lr, hr, rfl, hl, hr'⟩ := hA
  simp [leafOk, hr, hl, hr']

theorem accepts_iff {e : Term} : accepts? h a e = true ↔ LinIn h a e :=
  ⟨fun hacc => NF.accepts_sound (fun _ _ _ => leafOk_sound) e hacc,
   fun he => NF.accepts_complete leafOk_complete he⟩

end Rasso.Linear
