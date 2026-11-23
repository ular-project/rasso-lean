import Rasso.Subst
import Rasso.NormalForm

/-!
# Rasso: the shared normal form means the term

The proofs for `Rasso.NormalForm`, generic in the class's literals:

* `NF.In A a e`: the specification of a term whose leaves that mention `a` satisfy `A`;
* `NF.accepts_iff`: the test decides it, when the class's leaf test decides `A`;
* `NF.dnf_sem`: on a tuple with `a` set, the normal form has an `and` of true literals iff the
  term holds the sign, when the class's `leaf` is right on each leaf;
* `NF.dnf_attrs`: the literals read only what the term reads, and not `a`.

Each class instantiates these with its own literal meaning `S` and promise `G`.
-/

namespace Rasso

/-! ## Facts about terms the classes share -/

theorem asBool_ok {who : String} {v : Value} {b : Bool} (h : asBool who v = .ok b) :
    v = .bool b := by
  cases v <;> simp_all [asBool]

/-- Every operand of `and` or `or` that holds a Boolean holds a Boolean. -/
theorem holds_call_children {t : Tuple} {op : String} {es : List Term} {b : Bool}
    (hop : op = "and" ∨ op = "or") (h : (Term.call op es).holds t = .ok b) :
    ∀ e ∈ es, ∃ b', e.holds t = .ok b' := by
  intro e he
  rw [Term.holds_ok] at h
  simp only [Term.eval, bind, Except.bind] at h
  split at h
  · cases h
  rename_i vs hvs
  obtain ⟨v, hv, hev⟩ := (mapM_ok.mp hvs).mem_left he
  have hb : ∃ b', asBool "x" v = .ok b' := by
    rcases hop with rfl | rfl <;>
    · simp only [applyOp, bind, Except.bind] at h
      split at h
      · cases h
      rename_i bs hbs
      obtain ⟨b', _, hb'⟩ := (mapM_ok.mp hbs).mem_left hv
      exact ⟨b', by rw [asBool_ok hb']; rfl⟩
  obtain ⟨b', hb'⟩ := hb
  exact ⟨b', by rw [Term.holds_ok, hev, asBool_ok hb']⟩

theorem Term.eval_set_of_not_mem {t : Tuple} (ht : Tuple.Sorted t) {a : String} {v : Value}
    {e : Term} (h : a ∉ e.attrs) : e.eval (t.set a v) = e.eval t :=
  e.eval_congr fun x hx => by
    rw [Tuple.get?_set ht]
    have : x ≠ a := fun e => h (e ▸ hx)
    simp [this]

theorem Term.holds_set_of_not_mem {t : Tuple} (ht : Tuple.Sorted t) {a : String} {v : Value}
    {e : Term} (h : a ∉ e.attrs) : e.holds (t.set a v) = e.holds t := by
  simp only [Term.holds, Term.eval_set_of_not_mem ht h]

theorem eval_attr_set {t : Tuple} (ht : Tuple.Sorted t) (a : String) (v : Value) :
    (Term.attr a).eval (t.set a v) = .ok v := by
  simp [Term.eval, Tuple.get?_set ht]

namespace NF

theorem isAttr_iff {a : String} {e : Term} : isAttr a e = true ↔ e = .attr a := by
  cases e <;> simp [isAttr]

theorem foldr_attach {α β : Type} (l : List α) (g : α → β → β) (z : β) :
    l.attach.foldr (fun x acc => g x.1 acc) z = l.foldr g z := by
  rw [← List.foldr_map (f := Subtype.val) (g := g), List.attach_map_subtype_val]

theorem flatMap_attach {α β : Type} (l : List α) (g : α → List β) :
    l.attach.flatMap (fun x => g x.1) = l.flatMap g := by
  rw [← List.flatMap_map (f := Subtype.val) (g := g), List.attach_map_subtype_val]

theorem attrs_sub_call {op : String} {es : List Term} {x : Term} (hx : x ∈ es) {R : List String}
    (hR : ∀ y ∈ (Term.call op es).attrs, y ∈ R) : ∀ y ∈ x.attrs, y ∈ R :=
  fun y hy => hR y (by simp only [Term.attrs, List.mem_flatMap]; exact ⟨x, hx, hy⟩)

/-- The truth value an operand of `and`/`or` holds (it holds a Boolean). -/
def bv (s : Tuple) (x : Term) : Bool :=
  match x.holds s with
  | .ok b => b
  | .error _ => false

theorem bv_eq {s : Tuple} {x : Term} {b : Bool} (h : x.holds s = .ok b) : bv s x = b := by
  simp [bv, h]

/-! ## The specification -/

/-- The term is a Boolean skeleton of `and`, `or` and `not` (one operand), whose parts either
do not mention `a`, or are leaves `op es` that the class accepts (`A op es`). -/
inductive In (A : String → List Term → Prop) (a : String) : Term → Prop
  | opq {e : Term} : a ∉ e.attrs → In A a e
  | and {es : List Term} : (∀ e ∈ es, In A a e) → In A a (.call "and" es)
  | or {es : List Term} : (∀ e ∈ es, In A a e) → In A a (.call "or" es)
  | not {e : Term} : In A a e → In A a (.call "not" [e])
  | leaf {op : String} {es : List Term} : op ≠ "and" → op ≠ "or" → op ≠ "not" → A op es →
      In A a (.call op es)

/-! ## The normal form, unfolded -/

section Unfold

variable {α : Type} {leaf : Bool → String → List Term → List (List (Lit α))} {a : String}
  {p : Bool}

theorem dnf_opq {e : Term} (h : a ∉ e.attrs) : dnf leaf a p e = [[.opq p e]] := by
  have : (!e.attrs.contains a) = true := by simpa using h
  cases e <;> (unfold dnf; simp_all)

theorem dnf_and {es : List Term} (h : a ∈ (Term.call "and" es).attrs) :
    dnf leaf a p (.call "and" es) =
      if p then es.foldr (fun x acc => conj (dnf leaf a p x) acc) [[]]
      else es.flatMap (dnf leaf a p) := by
  have : (Term.call "and" es).attrs.contains a = true := by simpa using h
  conv => lhs; unfold dnf
  simp only [this, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases p
  · simp
  · simp

theorem dnf_or {es : List Term} (h : a ∈ (Term.call "or" es).attrs) :
    dnf leaf a p (.call "or" es) =
      if p then es.flatMap (dnf leaf a p)
      else es.foldr (fun x acc => conj (dnf leaf a p x) acc) [[]] := by
  have : (Term.call "or" es).attrs.contains a = true := by simpa using h
  conv => lhs; unfold dnf
  simp only [this, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hne : ("or" = "and") = False := by simp
  simp only [hne, ↓reduceIte]
  cases p
  · simp
  · simp

theorem dnf_not {e : Term} (h : a ∈ (Term.call "not" [e]).attrs) :
    dnf leaf a p (.call "not" [e]) = dnf leaf a (!p) e := by
  have : (Term.call "not" [e]).attrs.contains a = true := by simpa using h
  conv => lhs; unfold dnf
  simp only [this]
  simp

theorem dnf_leaf {op : String} {es : List Term} (h1 : op ≠ "and") (h2 : op ≠ "or")
    (h3 : op ≠ "not") (h : a ∈ (Term.call op es).attrs) :
    dnf leaf a p (.call op es) = leaf p op es := by
  have : (Term.call op es).attrs.contains a = true := by simpa using h
  conv => lhs; unfold dnf
  simp [h1, h2, h3]
  exact fun hn => absurd h hn

end Unfold

/-! ## Conjunction and disjunction of normal forms -/

section Conj

variable {α : Type}

theorem conj_exists {P : Lit α → Prop} {d₁ d₂ : List (List (Lit α))} :
    (∃ c ∈ conj d₁ d₂, ∀ l ∈ c, P l) ↔
      (∃ c ∈ d₁, ∀ l ∈ c, P l) ∧ (∃ c ∈ d₂, ∀ l ∈ c, P l) := by
  simp only [conj, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨c₁, h₁, c₂, h₂, rfl⟩, hc⟩
    exact ⟨⟨c₁, h₁, fun l hl => hc l (List.mem_append_left _ hl)⟩,
      ⟨c₂, h₂, fun l hl => hc l (List.mem_append_right _ hl)⟩⟩
  · rintro ⟨⟨c₁, h₁, hc₁⟩, ⟨c₂, h₂, hc₂⟩⟩
    refine ⟨c₁ ++ c₂, ⟨c₁, h₁, c₂, h₂, rfl⟩, fun l hl => ?_⟩
    rcases List.mem_append.mp hl with hl | hl
    · exact hc₁ l hl
    · exact hc₂ l hl

theorem conj_all {P : Lit α → Prop} {d₁ d₂ : List (List (Lit α))}
    (h₁ : ∀ c ∈ d₁, ∀ l ∈ c, P l) (h₂ : ∀ c ∈ d₂, ∀ l ∈ c, P l) :
    ∀ c ∈ conj d₁ d₂, ∀ l ∈ c, P l := by
  simp only [conj, List.mem_flatMap, List.mem_map]
  rintro _ ⟨c₁, hc₁, c₂, hc₂, rfl⟩ l hl
  rcases List.mem_append.mp hl with hl | hl
  · exact h₁ c₁ hc₁ l hl
  · exact h₂ c₂ hc₂ l hl

theorem foldr_conj_exists {P : Lit α → Prop} {g : Term → List (List (Lit α))} :
    ∀ es : List Term, (∃ c ∈ es.foldr (fun x acc => conj (g x) acc) [[]], ∀ l ∈ c, P l) ↔
      ∀ x ∈ es, ∃ c ∈ g x, ∀ l ∈ c, P l
  | [] => by simp
  | x :: es => by
    simp only [List.foldr_cons, conj_exists, foldr_conj_exists es, List.mem_cons,
      forall_eq_or_imp]

theorem foldr_conj_all {P : Lit α → Prop} {g : Term → List (List (Lit α))} :
    ∀ es : List Term, (∀ x ∈ es, ∀ c ∈ g x, ∀ l ∈ c, P l) →
      ∀ c ∈ es.foldr (fun x acc => conj (g x) acc) [[]], ∀ l ∈ c, P l
  | [], _ => by simp
  | x :: es, h => by
    simp only [List.foldr_cons]
    exact conj_all (h x List.mem_cons_self)
      (foldr_conj_all es fun y hy => h y (List.mem_cons_of_mem _ hy))

end Conj

/-! ## The meaning of a literal -/

section Sem

variable {α : Type}

/-- A literal is true on `t` (the tuple without `x`), when the class's literals mean `S`. -/
def Lit.Sem (S : α → Prop) (t : Tuple) : Lit α → Prop
  | .opq p e => e.holds t = .ok p
  | .atom l => S l
  | .const b => b = true

/-- What the normal form promises of a literal: an opaque part does not mention `a`, holds a
Boolean on `t`, and reads only `R`; a literal of the class satisfies `G R`. -/
def Lit.Good (G : List String → α → Prop) (a : String) (t : Tuple) (R : List String) :
    Lit α → Prop
  | .opq _ e => a ∉ e.attrs ∧ (∃ b, e.holds t = .ok b) ∧ ∀ x ∈ e.attrs, x ∈ R
  | .atom l => G R l
  | .const _ => True

/-- The conclusion of `dnf_sem`: every literal is good, and some `and` of the normal form is
all true iff the term holds `p`, where `b` is what the term holds. -/
def DnfOk (S : α → Prop) (G : List String → α → Prop) (a : String) (t : Tuple)
    (R : List String) (p b : Bool) (D : List (List (Lit α))) : Prop :=
  (∀ c ∈ D, ∀ l ∈ c, Lit.Good G a t R l) ∧ ((∃ c ∈ D, ∀ l ∈ c, Lit.Sem S t l) ↔ b = p)

variable {leaf : Bool → String → List Term → List (List (Lit α))} {a : String} {t : Tuple}
  {v : Value} {S : α → Prop} {G : List String → α → Prop}

theorem dnfOk_opq (ht : Tuple.Sorted t) {e : Term} (hna : a ∉ e.attrs) {R : List String}
    (hR : ∀ x ∈ e.attrs, x ∈ R) (p b : Bool) (hb : e.holds (t.set a v) = .ok b) :
    DnfOk S G a t R p b (dnf leaf a p e) := by
  rw [dnf_opq hna]
  have hb' : e.holds t = .ok b := by rw [← Term.holds_set_of_not_mem ht hna]; exact hb
  refine ⟨fun c hc l hl => ?_, ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc
    simp only [List.mem_singleton] at hl; subst hl
    exact ⟨hna, ⟨b, hb'⟩, hR⟩
  · simp only [List.mem_singleton, exists_eq_left, forall_eq, Lit.Sem, hb', Except.ok.injEq]

/-- The normal form means the term: on `t` with `a` set to `v`, given that the class's `leaf`
is right on each leaf it accepts. -/
theorem dnf_sem {A : String → List Term → Prop} (ht : Tuple.Sorted t)
    (hleaf : ∀ {op : String} {es : List Term}, op ≠ "and" → op ≠ "or" → op ≠ "not" → A op es →
      a ∈ (Term.call op es).attrs → ∀ {R : List String}, (∀ x ∈ (Term.call op es).attrs, x ∈ R) →
      ∀ (p b : Bool), (Term.call op es).holds (t.set a v) = .ok b →
      DnfOk S G a t R p b (leaf p op es)) :
    ∀ {e : Term}, In A a e → ∀ {R : List String}, (∀ x ∈ e.attrs, x ∈ R) →
      ∀ (p b : Bool), e.holds (t.set a v) = .ok b → DnfOk S G a t R p b (dnf leaf a p e) := by
  intro e he
  induction he with
  | opq hna => exact dnfOk_opq ht hna
  | @and es _ ih =>
    intro R hR p b hb
    by_cases hc : a ∈ (Term.call "and" es).attrs
    case neg => exact dnfOk_opq ht hc hR p b hb
    rw [dnf_and hc]
    have hch := holds_call_children (.inl rfl) hb
    have hg : ∀ x ∈ es, x.holds (t.set a v) = .ok (bv _ x) := fun x hx => by
      obtain ⟨b', hb'⟩ := hch x hx; rw [hb', bv_eq hb']
    have hbv : b = es.all (bv (t.set a v)) := by
      have := holds_andN hg; rw [this] at hb; cases hb; rfl
    have ihx := fun x hx q => ih x hx (attrs_sub_call hx hR) q _ (hg x hx)
    cases p
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨fun c hc l hl => ?_, ?_⟩
      · obtain ⟨x, hx, hc⟩ := List.mem_flatMap.mp hc
        exact (ihx x hx false).1 c hc l hl
      · simp only [List.mem_flatMap, hbv]
        constructor
        · rintro ⟨c, ⟨x, hx, hc⟩, hl⟩
          have := (ihx x hx false).2.mp ⟨c, hc, hl⟩
          simp only [List.all_eq_false]; exact ⟨x, hx, by simp [this]⟩
        · intro he'
          obtain ⟨x, hx, hfx⟩ := List.all_eq_false.mp he'
          obtain ⟨c, hc, hl⟩ := (ihx x hx false).2.mpr (by simpa using hfx)
          exact ⟨c, ⟨x, hx, hc⟩, hl⟩
    · simp only [↓reduceIte]
      refine ⟨foldr_conj_all es fun x hx => (ihx x hx true).1, ?_⟩
      rw [foldr_conj_exists, hbv, List.all_eq_true]
      exact forall₂_congr fun x hx => (ihx x hx true).2
  | @or es _ ih =>
    intro R hR p b hb
    by_cases hc : a ∈ (Term.call "or" es).attrs
    case neg => exact dnfOk_opq ht hc hR p b hb
    rw [dnf_or hc]
    have hch := holds_call_children (.inr rfl) hb
    have hg : ∀ x ∈ es, x.holds (t.set a v) = .ok (bv _ x) := fun x hx => by
      obtain ⟨b', hb'⟩ := hch x hx; rw [hb', bv_eq hb']
    have hbv : b = es.any (bv (t.set a v)) := by
      have := holds_orN hg; rw [this] at hb; cases hb; rfl
    have ihx := fun x hx q => ih x hx (attrs_sub_call hx hR) q _ (hg x hx)
    cases p
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨foldr_conj_all es fun x hx => (ihx x hx false).1, ?_⟩
      rw [foldr_conj_exists, hbv]
      simp only [List.any_eq_false]
      exact forall₂_congr fun x hx => ((ihx x hx false).2).trans (by simp)
    · simp only [↓reduceIte]
      refine ⟨fun c hc l hl => ?_, ?_⟩
      · obtain ⟨x, hx, hc⟩ := List.mem_flatMap.mp hc
        exact (ihx x hx true).1 c hc l hl
      · simp only [List.mem_flatMap, hbv, List.any_eq_true]
        constructor
        · rintro ⟨c, ⟨x, hx, hc⟩, hl⟩
          exact ⟨x, hx, (ihx x hx true).2.mp ⟨c, hc, hl⟩⟩
        · rintro ⟨x, hx, hfx⟩
          obtain ⟨c, hc, hl⟩ := (ihx x hx true).2.mpr hfx
          exact ⟨c, ⟨x, hx, hc⟩, hl⟩
  | @not e _ ih =>
    intro R hR p b hb
    by_cases hc : a ∈ (Term.call "not" [e]).attrs
    case neg => exact dnfOk_opq ht hc hR p b hb
    rw [dnf_not hc]
    obtain ⟨b', hb', rfl⟩ := holds_not1.mp hb
    have := ih (attrs_sub_call List.mem_cons_self hR) (!p) b' hb'
    refine ⟨this.1, this.2.trans ?_⟩
    cases b' <;> cases p <;> simp
  | @leaf op es h1 h2 h3 hA =>
    intro R hR p b hb
    by_cases hc : a ∈ (Term.call op es).attrs
    case neg => exact dnfOk_opq ht hc hR p b hb
    rw [dnf_leaf h1 h2 h3 hc]
    exact hleaf h1 h2 h3 hA hc hR p b hb

end Sem

/-! ## What the literals read -/

section Attrs

variable {α : Type}

/-- The attributes a literal's terms read, when the class's literals read `at`. -/
def Lit.attrs (at' : α → List String) : Lit α → List String
  | .opq _ e => e.attrs
  | .atom l => at' l
  | .const _ => []

variable {leaf : Bool → String → List Term → List (List (Lit α))} {a : String}
  {at' : α → List String}

/-- Every literal of the normal form reads only attributes of the term, and not `a`. -/
theorem dnf_attrs {A : String → List Term → Prop}
    (hleaf : ∀ {op : String} {es : List Term}, A op es → a ∈ (Term.call op es).attrs →
      ∀ (p : Bool), ∀ c ∈ leaf p op es, ∀ l ∈ c, ∀ x ∈ l.attrs at',
        x ∈ (Term.call op es).attrs ∧ x ≠ a) :
    ∀ {e : Term}, In A a e → ∀ (p : Bool), ∀ c ∈ dnf leaf a p e, ∀ l ∈ c, ∀ x ∈ l.attrs at',
      x ∈ e.attrs ∧ x ≠ a := by
  have opq : ∀ {e : Term}, a ∉ e.attrs → ∀ (p : Bool), ∀ c ∈ dnf leaf a p e, ∀ l ∈ c,
      ∀ x ∈ l.attrs at', x ∈ e.attrs ∧ x ≠ a := by
    intro e hna p c hc l hl x hx
    rw [dnf_opq hna] at hc
    simp only [List.mem_singleton] at hc; subst hc
    simp only [List.mem_singleton] at hl; subst hl
    exact ⟨hx, fun e => hna (e ▸ hx)⟩
  intro e he
  induction he with
  | opq hna => exact opq hna
  | @and es _ ih =>
    intro p c hc l hl x hx
    by_cases hca : a ∈ (Term.call "and" es).attrs
    case neg => exact opq hca p c hc l hl x hx
    rw [dnf_and hca] at hc
    have key : ∀ y ∈ es, ∀ c ∈ dnf leaf a p y, ∀ l ∈ c, ∀ x ∈ l.attrs at',
        x ∈ (Term.call "and" es).attrs ∧ x ≠ a := fun y hy c hc l hl x hx =>
      let r := ih y hy p c hc l hl x hx
      ⟨by simp only [Term.attrs, List.mem_flatMap]; exact ⟨y, hy, r.1⟩, r.2⟩
    cases p
    · simp only [Bool.false_eq_true, ↓reduceIte] at hc
      obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
      exact key y hy c hc l hl x hx
    · simp only [↓reduceIte] at hc
      exact foldr_conj_all
        (P := fun l => ∀ x ∈ l.attrs at', x ∈ (Term.call "and" es).attrs ∧ x ≠ a)
        es (fun y hy c hc l hl => key y hy c hc l hl) c hc l hl x hx
  | @or es _ ih =>
    intro p c hc l hl x hx
    by_cases hca : a ∈ (Term.call "or" es).attrs
    case neg => exact opq hca p c hc l hl x hx
    rw [dnf_or hca] at hc
    have key : ∀ y ∈ es, ∀ c ∈ dnf leaf a p y, ∀ l ∈ c, ∀ x ∈ l.attrs at',
        x ∈ (Term.call "or" es).attrs ∧ x ≠ a := fun y hy c hc l hl x hx =>
      let r := ih y hy p c hc l hl x hx
      ⟨by simp only [Term.attrs, List.mem_flatMap]; exact ⟨y, hy, r.1⟩, r.2⟩
    cases p
    · simp only [Bool.false_eq_true, ↓reduceIte] at hc
      exact foldr_conj_all
        (P := fun l => ∀ x ∈ l.attrs at', x ∈ (Term.call "or" es).attrs ∧ x ≠ a)
        es (fun y hy c hc l hl => key y hy c hc l hl) c hc l hl x hx
    · simp only [↓reduceIte] at hc
      obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
      exact key y hy c hc l hl x hx
  | @not e _ ih =>
    intro p c hc l hl x hx
    by_cases hca : a ∈ (Term.call "not" [e]).attrs
    case neg => exact opq hca p c hc l hl x hx
    rw [dnf_not hca] at hc
    have r := ih (!p) c hc l hl x hx
    exact ⟨by simpa [Term.attrs] using r.1, r.2⟩
  | @leaf op es h1 h2 h3 hA =>
    intro p c hc l hl x hx
    by_cases hca : a ∈ (Term.call op es).attrs
    case neg => exact opq hca p c hc l hl x hx
    rw [dnf_leaf h1 h2 h3 hca] at hc
    exact hleaf hA hca p c hc l hl x hx

/-- A term of `elimConj` reads only what the literals read, when `part` reads only what its
literals read. -/
theorem elimConj_attrs {part : List α → List Term}
    (hpart : ∀ (xs : List α) (e : Term), e ∈ part xs → ∀ x ∈ e.attrs, ∃ l ∈ xs, x ∈ at' l)
    {c : List (Lit α)} {e : Term} (he : e ∈ elimConj part c) {x : String} (hx : x ∈ e.attrs) :
    ∃ l ∈ c, x ∈ l.attrs at' := by
  rcases List.mem_append.mp he with he | he
  · obtain ⟨l, hl, he⟩ := List.mem_filterMap.mp he
    refine ⟨l, hl, ?_⟩
    cases l with
    | opq p e' =>
      simp only [Lit.rest, Option.some.injEq] at he; subst he
      cases p <;> simp_all [Lit.attrs, Term.attrs]
    | const b =>
      simp only [Lit.rest, Option.some.injEq] at he; subst he; simp [Term.attrs] at hx
    | atom _ => simp [Lit.rest] at he
  · obtain ⟨l, hl, hxl⟩ := hpart _ e he x hx
    obtain ⟨l', hl', hl'e⟩ := List.mem_filterMap.mp hl
    refine ⟨l', hl', ?_⟩
    cases l' with
    | atom l'' => simp only [Lit.atom?, Option.some.injEq] at hl'e; subst hl'e; exact hxl
    | opq _ _ => simp [Lit.atom?] at hl'e
    | const _ => simp [Lit.atom?] at hl'e

end Attrs

/-! ## What every literal of the normal form is -/

section Lits

variable {α : Type} {leaf : Bool → String → List Term → List (List (Lit α))} {a : String}

/-- A property `P` of every literal of the normal form, from a property `Q` of the term that
its Boolean skeleton passes down: an opaque part has `Q` and does not mention `a`, and a leaf
that mentions `a` has `Q`. The closure proofs of each class use this with `Q` a shape. -/
theorem dnf_lits {Q : Term → Prop} {P : Lit α → Prop}
    (hand : ∀ {es : List Term}, Q (.call "and" es) → ∀ e ∈ es, Q e)
    (hor : ∀ {es : List Term}, Q (.call "or" es) → ∀ e ∈ es, Q e)
    (hnot : ∀ {es : List Term}, Q (.call "not" es) → ∀ e ∈ es, Q e)
    (hopq : ∀ (q : Bool) {e : Term}, a ∉ e.attrs → Q e → P (.opq q e))
    (hleaf : ∀ {op : String} {es : List Term}, op ≠ "and" → op ≠ "or" → op ≠ "not" →
      a ∈ (Term.call op es).attrs → Q (.call op es) →
      ∀ (p : Bool), ∀ c ∈ leaf p op es, ∀ l ∈ c, P l) :
    ∀ (e : Term), Q e → ∀ (p : Bool), ∀ c ∈ dnf leaf a p e, ∀ l ∈ c, P l
  | e, hq, p, c, hc, l, hl => by
    by_cases hca : a ∈ e.attrs
    case neg =>
      rw [dnf_opq hca] at hc
      simp only [List.mem_singleton] at hc; subst hc
      simp only [List.mem_singleton] at hl; subst hl
      exact hopq p hca hq
    match e, hq, hca, hc with
    | .call op es, hq, hca, hc =>
      by_cases h1 : op = "and"
      · subst h1
        rw [dnf_and hca] at hc
        have key : ∀ y ∈ es, ∀ c ∈ dnf leaf a p y, ∀ l ∈ c, P l := fun y hy =>
          dnf_lits hand hor hnot hopq hleaf y (hand hq y hy) p
        cases p
        · simp only [Bool.false_eq_true, ↓reduceIte] at hc
          obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
          exact key y hy c hc l hl
        · simp only [↓reduceIte] at hc
          exact foldr_conj_all es key c hc l hl
      by_cases h2 : op = "or"
      · subst h2
        rw [dnf_or hca] at hc
        have key : ∀ y ∈ es, ∀ c ∈ dnf leaf a p y, ∀ l ∈ c, P l := fun y hy =>
          dnf_lits hand hor hnot hopq hleaf y (hor hq y hy) p
        cases p
        · simp only [Bool.false_eq_true, ↓reduceIte] at hc
          exact foldr_conj_all es key c hc l hl
        · simp only [↓reduceIte] at hc
          obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
          exact key y hy c hc l hl
      by_cases h3 : op = "not"
      · subst h3
        match hes : es with
        | [x] =>
          have hx : x ∈ es := by rw [hes]; exact List.mem_cons_self
          rw [dnf_not hca] at hc
          exact dnf_lits hand hor hnot hopq hleaf x (hnot hq x (by simp)) (!p) c hc l hl
        | [] => unfold dnf at hc; simp_all
        | _ :: _ :: _ => unfold dnf at hc; simp_all
      rw [dnf_leaf h1 h2 h3 hca] at hc
      exact hleaf h1 h2 h3 hca hq p c hc l hl
    | .attr b, _, hca, hc => unfold dnf at hc; simp_all
    | .val v, _, hca, hc => unfold dnf at hc; simp_all
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ es›; omega)
    | (simp; omega)
    | omega

end Lits

/-! ## The literals of one `and` -/

section Split

variable {α : Type}

theorem mem_atoms {c : List (Lit α)} {l : α} : l ∈ c.filterMap Lit.atom? ↔ .atom l ∈ c := by
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨l', hl', he⟩
    cases l' <;> simp_all [Lit.atom?]
  · intro h; exact ⟨_, h, rfl⟩

/-- An `and` of literals is the `and` of its rests and its literals of the class. -/
theorem lit_split {c : List (Lit α)} {P : Lit α → Prop} :
    (∀ l ∈ c, P l) ↔ (∀ l ∈ c, l.atom? = none → P l) ∧ ∀ l ∈ c.filterMap Lit.atom?, P (.atom l) := by
  constructor
  · intro h; exact ⟨fun l hl _ => h l hl, fun l hl => h _ (mem_atoms.mp hl)⟩
  · rintro ⟨h₁, h₂⟩ l hl
    cases l with
    | atom l' => exact h₂ l' (mem_atoms.mpr hl)
    | opq _ _ => exact h₁ _ hl rfl
    | const _ => exact h₁ _ hl rfl

end Split

/-! ## One `and`, with `x` removed -/

section Conj1

variable {α β : Type} {a : String} {t : Tuple} {G : List String → α → Prop}

/-- A literal that does not mention `x` means the same for every value of `x`, and its term
holds a Boolean. -/
theorem rest_sem {S : α → Prop} {R : List String} {l : Lit α} {e : Term}
    (hg : Lit.Good G a t R l) (hl : l.rest = some e) :
    (∃ b, e.holds t = .ok b) ∧ (∀ x ∈ e.attrs, x ∈ R) ∧ (e.holds t = .ok true ↔ Lit.Sem S t l) := by
  cases l with
  | opq p e' =>
    simp only [Lit.rest, Option.some.injEq] at hl; subst hl
    obtain ⟨_, ⟨b, hb⟩, hR⟩ := hg
    cases p
    · refine ⟨⟨!b, holds_not1.mpr ⟨b, hb, rfl⟩⟩, ?_, ?_⟩
      · intro x hx; simp only [Bool.false_eq_true, ↓reduceIte, Term.attrs, List.flatMap_cons,
          List.flatMap_nil, List.append_nil] at hx; exact hR x hx
      · simp only [Bool.false_eq_true, ↓reduceIte, Lit.Sem, hb, Except.ok.injEq, holds_not1]
        constructor
        · rintro ⟨p, e, e'⟩; rw [e]; cases p <;> simp at e' ⊢
        · intro e; exact ⟨b, rfl, by simp [e]⟩
    · exact ⟨⟨b, by simpa using hb⟩, by simpa using hR, by simp [Lit.Sem]⟩
  | const b =>
    simp only [Lit.rest, Option.some.injEq] at hl; subst hl
    have : (Term.val (.bool b)).holds t = .ok b := Term.holds_ok.mpr (by simp [Term.eval])
    exact ⟨⟨b, this⟩, by simp [Term.attrs], by simp [this, Lit.Sem]⟩
  | atom _ => simp [Lit.rest] at hl

/-- **One `and`.** When the class's `part` is right on its literals, the terms `elimConj`
gives each hold a Boolean, read only `R`, and all hold exactly when some value `q` of `x`
makes every literal true. -/
theorem elimConj_sem {S : β → α → Prop} {part : List α → List Term} {R : List String}
    (hpart : ∀ xs : List α, (∀ x ∈ xs, G R x) →
      (∀ e ∈ part xs, (∃ b, e.holds t = .ok b) ∧ ∀ x ∈ e.attrs, x ∈ R) ∧
        ((∀ e ∈ part xs, e.holds t = .ok true) ↔ ∃ q, ∀ x ∈ xs, S q x))
    {c : List (Lit α)} (hg : ∀ l ∈ c, Lit.Good G a t R l) :
    (∀ e ∈ elimConj part c, (∃ b, e.holds t = .ok b) ∧ ∀ x ∈ e.attrs, x ∈ R) ∧
      ((∀ e ∈ elimConj part c, e.holds t = .ok true) ↔ ∃ q, ∀ l ∈ c, Lit.Sem (S q) t l) := by
  have hx : ∀ x ∈ c.filterMap Lit.atom?, G R x := fun x hx => hg _ (mem_atoms.mp hx)
  have hrest : ∀ e ∈ c.filterMap Lit.rest, (∃ b, e.holds t = .ok b) ∧ ∀ x ∈ e.attrs, x ∈ R := by
    intro e he
    obtain ⟨l, hl, he⟩ := List.mem_filterMap.mp he
    have := rest_sem (S := fun _ => True) (hg l hl) he
    exact ⟨this.1, this.2.1⟩
  have hrs : ∀ q, (∀ e ∈ c.filterMap Lit.rest, e.holds t = .ok true) ↔
      ∀ l ∈ c, l.atom? = none → Lit.Sem (S q) t l := by
    intro q
    simp only [List.mem_filterMap]
    constructor
    · intro hc l hl hn
      cases hr : l.rest with
      | none => cases l <;> simp_all [Lit.rest, Lit.atom?]
      | some e => exact ((rest_sem (hg l hl) hr).2.2).mp (hc e ⟨l, hl, hr⟩)
    · rintro hc e ⟨l, hl, he⟩
      have hn : l.atom? = none := by cases l <;> simp_all [Lit.rest, Lit.atom?]
      exact ((rest_sem (hg l hl) he).2.2).mpr (hc l hl hn)
  obtain ⟨hX1, hX2⟩ := hpart _ hx
  refine ⟨fun e he => ?_, ?_⟩
  · rcases List.mem_append.mp he with he | he
    · exact hrest e he
    · exact hX1 e he
  have hsplit : (∀ e ∈ elimConj part c, e.holds t = .ok true) ↔
      (∀ e ∈ c.filterMap Lit.rest, e.holds t = .ok true) ∧
        ∀ e ∈ part (c.filterMap Lit.atom?), e.holds t = .ok true :=
    ⟨fun h' => ⟨fun e he => h' e (List.mem_append_left _ he),
      fun e he => h' e (List.mem_append_right _ he)⟩,
     fun ⟨h₁, h₂⟩ e he => (List.mem_append.mp he).elim (h₁ e) (h₂ e)⟩
  rw [hsplit, hX2]
  constructor
  · rintro ⟨hr, q, hq⟩
    exact ⟨q, lit_split.mpr ⟨(hrs q).mp hr, hq⟩⟩
  · rintro ⟨q, hc⟩
    obtain ⟨hr, hq⟩ := lit_split.mp hc
    exact ⟨(hrs q).mpr hr, q, hq⟩

end Conj1

/-! ## The class obligation, generic -/

/-- **Removal through the normal form is sound.** A class that removes `a` through the normal
form gives: values `val q` that are exactly the values of `a`'s domain; a `leaf` that is right
on each leaf it accepts (meaning `S t q`, promise `G t`); and a `part` that is right on one
`and`'s literals. Then the new term reads only the remaining attributes, never refuses on a
fitting tuple, and holds `t` exactly when some value of `a` makes the old term hold. -/
theorem elim_sound {α β : Type} {leaf : Bool → String → List Term → List (List (Lit α))}
    {part : List α → List Term} {A : String → List Term → Prop} {at' : α → List String}
    {u : Unrel} {a : String} {dₐ : Domain} (hd : u.heading.lookup a = some dₐ)
    (val : β → Value) (hval : ∀ q, dₐ.mem (val q) = true)
    (hsurj : ∀ v, dₐ.mem v = true → ∃ q, v = val q) (q₀ : β)
    (S : Tuple → β → α → Prop) (G : Tuple → List String → α → Prop)
    (hin : In A a u.term) (hu : u.WF) (tu : u.Total)
    (hleaf : ∀ t : Tuple, t.Fits (u.heading.filter (·.1 ≠ a)) → ∀ q : β,
      ∀ {op : String} {es : List Term}, op ≠ "and" → op ≠ "or" → op ≠ "not" → A op es →
      a ∈ (Term.call op es).attrs → ∀ {R : List String}, (∀ x ∈ (Term.call op es).attrs, x ∈ R) →
      ∀ (p b : Bool), (Term.call op es).holds (t.set a (val q)) = .ok b →
      DnfOk (S t q) (G t) a t R p b (leaf p op es))
    (hpart : ∀ t : Tuple, t.Fits (u.heading.filter (·.1 ≠ a)) → ∀ R xs, (∀ x ∈ xs, G t R x) →
      (∀ e ∈ part xs, (∃ b, e.holds t = .ok b) ∧ ∀ x ∈ e.attrs, x ∈ R) ∧
        ((∀ e ∈ part xs, e.holds t = .ok true) ↔ ∃ q, ∀ x ∈ xs, S t q x))
    (hleafAttrs : ∀ {op : String} {es : List Term}, A op es → a ∈ (Term.call op es).attrs →
      ∀ (p : Bool), ∀ c ∈ leaf p op es, ∀ l ∈ c, ∀ x ∈ l.attrs at',
        x ∈ (Term.call op es).attrs ∧ x ≠ a)
    (hpartAttrs : ∀ (xs : List α) (e : Term), e ∈ part xs → ∀ x ∈ e.attrs, ∃ l ∈ xs, x ∈ at' l) :
    let w : Unrel := ⟨u.heading.filter (·.1 ≠ a), elim leaf part a u.term⟩
    (∀ x ∈ w.term.attrs, x ∈ w.heading.attrs) ∧ w.Total ∧
      ∀ t, t.Fits w.heading → (w.Holds t ↔ ∃ v, u.Holds (t.set a v)) := by
  intro w
  have hfa : ∀ y, y ∈ Heading.attrs (u.heading.filter (·.1 ≠ a)) ↔ y ∈ u.heading.attrs ∧ y ≠ a := by
    intro y; simp [Heading.attrs, List.mem_filter]
  let D := dnf leaf a true u.term
  have hsets : ∀ t : Tuple, t.Fits w.heading → ∀ q : β, (t.set a (val q)).Fits u.heading :=
    fun t f q => f.set hd (hval q)
  have hdnf : ∀ (t : Tuple) (f : t.Fits w.heading) (q : β),
      ∃ b, u.term.holds (t.set a (val q)) = .ok b ∧
        DnfOk (S t q) (G t) a t u.term.attrs true b D := by
    intro t f q
    obtain ⟨b, hb'⟩ := tu _ (hsets t f q)
    exact ⟨b, hb', dnf_sem f.sorted (hleaf t f q) hin (fun _ hx => hx) true b hb'⟩
  have hconj : ∀ (t : Tuple) (f : t.Fits w.heading), ∀ c ∈ D,
      (∀ e ∈ elimConj part c, (∃ b, e.holds t = .ok b) ∧ ∀ x ∈ e.attrs, x ∈ u.term.attrs) ∧
        ((∀ e ∈ elimConj part c, e.holds t = .ok true) ↔
          ∃ q, ∀ l ∈ c, Lit.Sem (S t q) t l) := by
    intro t f c hc
    obtain ⟨_, _, hok⟩ := hdnf t f q₀
    exact elimConj_sem (hpart t f u.term.attrs) (hok.1 c hc)
  have hvalue : ∀ (t : Tuple) (f : t.Fits w.heading),
      w.term.holds t = .ok (D.any fun c => (elimConj part c).all (bv t)) := by
    intro t f
    have hand : ∀ c ∈ D, (Term.call "and" (elimConj part c)).holds t =
        .ok ((elimConj part c).all (bv t)) :=
      fun c hc => holds_andN fun e he => by
        obtain ⟨b, hb'⟩ := ((hconj t f c hc).1 e he).1; rw [hb', bv_eq hb']
    have := holds_orN (p := fun x => bv t x) (l := D.map fun c => Term.call "and" (elimConj part c))
      (fun x hx => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        rw [hand c hc, bv_eq (hand c hc)])
    show (Term.call "or" (D.map fun c => Term.call "and" (elimConj part c))).holds t = _
    rw [this, List.any_map]
    congr 1
    have key : ∀ L : List (List (Lit α)),
        (∀ c ∈ L, bv t (Term.call "and" (elimConj part c)) = (elimConj part c).all (bv t)) →
        L.any ((fun x => bv t x) ∘ fun c => Term.call "and" (elimConj part c)) =
          L.any fun c => (elimConj part c).all (bv t) := by
      intro L hL
      induction L with
      | nil => rfl
      | cons c L ih =>
        simp only [List.any_cons, Function.comp_apply]
        rw [hL c List.mem_cons_self, ih fun c hc => hL c (List.mem_cons_of_mem _ hc)]
    exact key D fun c hc => bv_eq (hand c hc)
  refine ⟨fun x hx => ?_, fun t f => ⟨_, hvalue t f⟩, fun t f => ?_⟩
  · show x ∈ Heading.attrs (u.heading.filter (·.1 ≠ a))
    simp only [w, elim, Term.attrs, List.flatMap_map, List.mem_flatMap] at hx
    obtain ⟨c, hc, e, he, hx⟩ := hx
    obtain ⟨l, hl, hxl⟩ := elimConj_attrs hpartAttrs he hx
    obtain ⟨hx1, hx2⟩ := dnf_attrs hleafAttrs hin true c hc l hl x hxl
    exact (hfa x).mpr ⟨hu.reads x hx1, hx2⟩
  · simp only [Unrel.Holds, hvalue t f, Except.ok.injEq, List.any_eq_true, List.all_eq_true]
    have hbvt : ∀ c ∈ D, (∀ e ∈ elimConj part c, bv t e = true) ↔
        ∃ q, ∀ l ∈ c, Lit.Sem (S t q) t l := by
      intro c hc
      rw [← (hconj t f c hc).2]
      refine forall₂_congr fun e he => ?_
      obtain ⟨b, hb'⟩ := ((hconj t f c hc).1 e he).1
      rw [hb', bv_eq hb', Except.ok.injEq]
    constructor
    · rintro ⟨_, c, hc, hall⟩
      obtain ⟨q, hq⟩ := (hbvt c hc).mp hall
      obtain ⟨b, hb', hok⟩ := hdnf t f q
      have : b = true := hok.2.mp ⟨c, hc, hq⟩
      subst this
      exact ⟨_, hsets t f q, hb'⟩
    · rintro ⟨v, fs, hs⟩
      have hav : (t.set a v).get? a = some v := by rw [Tuple.get?_set f.sorted]; simp
      have hmem := fs.dom (a, v) (lookup_mem hav) _ hd
      obtain ⟨q, rfl⟩ := hsurj v hmem
      obtain ⟨b, hb', hok⟩ := hdnf t f q
      rw [hs] at hb'; cases hb'
      obtain ⟨c, hc, hsem⟩ := hok.2.mpr rfl
      exact ⟨f, c, hc, (hbvt c hc).mpr ⟨q, hsem⟩⟩

/-! ## The test decides the specification -/

section Accepts

variable {leafOk : String → List Term → Bool} {A : String → List Term → Prop} {a : String}

theorem accepts_opq {e : Term} (hna : a ∉ e.attrs) : accepts? leafOk a e = true := by
  have : (!e.attrs.contains a) = true := by simpa using hna
  cases e <;> (unfold accepts?; simp_all)

theorem accepts_sound
    (hok : ∀ {op : String} {es : List Term}, op ≠ "and" → op ≠ "or" → op ≠ "not" →
      leafOk op es = true → A op es) :
    ∀ (e : Term), accepts? leafOk a e = true → In A a e
  | .call op es, hacc => by
    by_cases hna : a ∈ (Term.call op es).attrs
    case neg => exact .opq hna
    have hc : (Term.call op es).attrs.contains a = true := by simpa using hna
    unfold accepts? at hacc
    simp only [hc, Bool.not_true, Bool.false_or] at hacc
    by_cases hand : op = "and"
    · subst hand
      simp only [true_or, ↓reduceIte, List.all_eq_true] at hacc
      exact .and fun x hx => accepts_sound hok x (hacc ⟨x, hx⟩ (List.mem_attach _ _))
    by_cases hor : op = "or"
    · subst hor
      simp only [or_true, ↓reduceIte, List.all_eq_true] at hacc
      exact .or fun x hx => accepts_sound hok x (hacc ⟨x, hx⟩ (List.mem_attach _ _))
    simp only [hand, hor, or_self, ↓reduceIte] at hacc
    by_cases hnot : op = "not"
    · subst hnot
      simp only [↓reduceIte] at hacc
      match hes : es with
      | [x] =>
        have hx : x ∈ es := by rw [hes]; exact List.mem_cons_self
        exact .not (accepts_sound hok x (by simpa [hes] using hacc))
      | [] => simp at hacc
      | _ :: _ :: _ => simp at hacc
    simp only [hnot, ↓reduceIte] at hacc
    exact .leaf hand hor hnot (hok hand hor hnot hacc)
  | .attr b, hacc => .opq (by unfold accepts? at hacc; simpa using hacc)
  | .val v, hacc => .opq (by unfold accepts? at hacc; simpa using hacc)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ es›; omega)
    | (simp; omega)
    | omega

theorem accepts_complete (hok : ∀ {op : String} {es : List Term}, A op es → leafOk op es = true)
    {e : Term} (he : In A a e) : accepts? leafOk a e = true := by
  induction he with
  | opq hna => exact accepts_opq hna
  | @and es _ ih =>
    unfold accepts?
    simp only [Bool.or_eq_true, true_or, ↓reduceIte, List.all_eq_true]
    exact .inr fun ⟨x, hx⟩ _ => ih x hx
  | @or es _ ih =>
    unfold accepts?
    simp only [Bool.or_eq_true, or_true, ↓reduceIte, List.all_eq_true]
    exact .inr fun ⟨x, hx⟩ _ => ih x hx
  | @not e _ ih =>
    unfold accepts?
    simp [ih]
  | @leaf op es h1 h2 h3 hA =>
    unfold accepts?
    simp [h1, h2, h3, hok hA]

end Accepts

end NF

end Rasso
