import Rasso.DenseClosure

/-!
# Rasso: the linear class as a global class

A relation is in the linear class when it is well formed, every domain of its heading is the
rat kind, and its term is *linear-shaped*: `and`, `or`, `not` with one operand, Boolean
constants, and comparisons `= < <= > >=` of two linear terms (`LinTerm`). `LinTerm` is
syntactic: attributes, exact numbers, `+`, `-` with at least one operand, and `*` in which
every factor but one reads no attribute.

Such a term never refuses on a fitting tuple, so the relation is total. σ with a
linear-shaped term, ⋈, ∪, ∩, −, ρ and π keep the class. π removes each attribute by dense
order when the term is order-only there, and by linear arithmetic otherwise; both give
linear-shaped terms. π never refuses a relation in the class except for its two checks on
the attribute list.
-/

namespace Rasso

open Dense (XRel)
open NF (attrs_sub_call bv bv_eq foldr_conj_all)

/-- A linear term, read syntactically. -/
inductive LinTerm : Term → Prop
  | attr (b : String) : LinTerm (.attr b)
  | val {v : Value} : v.exact?.isSome → LinTerm (.val v)
  | add {es : List Term} : (∀ e ∈ es, LinTerm e) → LinTerm (.call "+" es)
  | sub {e : Term} {es : List Term} : LinTerm e → (∀ x ∈ es, LinTerm x) →
      LinTerm (.call "-" (e :: es))
  | mul {c d : List Term} {e : Term} : (∀ x ∈ c, LinTerm x) → (∀ x ∈ c, x.attrs = []) →
      LinTerm e → (∀ x ∈ d, LinTerm x) → (∀ x ∈ d, x.attrs = []) →
      LinTerm (.call "*" (c ++ e :: d))
  | mulc {es : List Term} : (∀ x ∈ es, LinTerm x) → (∀ x ∈ es, x.attrs = []) →
      LinTerm (.call "*" es)

/-- A term of the linear class's global shape. -/
inductive LinShaped : Term → Prop
  | const (b : Bool) : LinShaped (.val (.bool b))
  | and {es : List Term} : (∀ e ∈ es, LinShaped e) → LinShaped (.call "and" es)
  | or {es : List Term} : (∀ e ∈ es, LinShaped e) → LinShaped (.call "or" es)
  | not {e : Term} : LinShaped e → LinShaped (.call "not" [e])
  | cmp {op : String} {r : XRel} {l r' : Term} : XRel.ofOp op = some r → LinTerm l →
      LinTerm r' → LinShaped (.call op [l, r'])

/-- A relation in the linear class. -/
structure LinClass (u : Unrel) : Prop where
  wf : u.WF
  rat : u.heading.AllRat
  shaped : LinShaped u.term

/-! ## A linear term reads as a form -/

namespace Lin

theorem isConst_of_attrs {L : Lin} (h : ∀ b ∈ L.attrs, False) : L.isConst = true := by
  obtain ⟨ts, k⟩ := L
  cases ts with
  | nil => rfl
  | cons p ts => exact absurd (h p.1 (by simp [attrs])) id

theorem isConst_scale {k : Rat} {L : Lin} (h : L.isConst = true) : (L.scale k).isConst = true := by
  obtain ⟨ts, c⟩ := L
  simp only [isConst, List.isEmpty_iff] at h; subst h; rfl

theorem mul?_const {M L : Lin} (hL : L.isConst = true) : ∃ N, mul? M L = some N := by
  unfold mul?; split
  · exact ⟨_, rfl⟩
  · simp

theorem foldlM_const : ∀ (Ls : List Lin), (∀ L ∈ Ls, L.isConst = true) → ∀ M : Lin,
    ∃ N, Ls.foldlM mul? M = some N
  | [], _, M => ⟨M, rfl⟩
  | L :: Ls, h, M => by
    obtain ⟨P, hP⟩ := mul?_const (M := M) (h L (by simp))
    obtain ⟨N, hN⟩ := foldlM_const Ls (fun L hL => h L (by simp [hL])) P
    exact ⟨N, by simp [List.foldlM_cons, hP, hN]⟩

theorem foldlM_const_const : ∀ (Ls : List Lin), (∀ L ∈ Ls, L.isConst = true) → ∀ M : Lin,
    M.isConst = true → ∃ N, Ls.foldlM mul? M = some N ∧ N.isConst = true
  | [], _, M, hM => ⟨M, rfl, hM⟩
  | L :: Ls, h, M, hM => by
    have hP : mul? M L = some (L.scale M.const) := by simp [mul?, hM]
    obtain ⟨N, hN, hc⟩ := foldlM_const_const Ls (fun L hL => h L (by simp [hL])) (L.scale M.const)
      (isConst_scale (h L (by simp)))
    exact ⟨N, by simp [List.foldlM_cons, hP, hN], hc⟩

theorem ofTerms?_append {ok : String → Bool} : ∀ {xs ys : List Term} {Xs Ys : List Lin},
    ofTerms? ok xs = some Xs → ofTerms? ok ys = some Ys → ofTerms? ok (xs ++ ys) = some (Xs ++ Ys)
  | [], ys, Xs, Ys, hx, hy => by simp [ofTerms?] at hx; subst hx; simpa using hy
  | x :: xs, ys, Xs, Ys, hx, hy => by
    obtain ⟨L, Ms, hL, hM, rfl⟩ := ofTerms?_cons hx
    simp [ofTerms?, hL, ofTerms?_append hM hy]

theorem ofTerms?_all {ok : String → Bool} {P : Lin → Prop} : ∀ {es : List Term},
    (∀ e ∈ es, ∃ L, ofTerm? ok e = some L ∧ P L) → ∃ Ls, ofTerms? ok es = some Ls ∧ ∀ L ∈ Ls, P L
  | [], _ => ⟨[], rfl, by simp⟩
  | e :: es, h => by
    obtain ⟨L, hL, hP⟩ := h e (by simp)
    obtain ⟨Ls, hLs, hPs⟩ := ofTerms?_all (es := es) (fun x hx => h x (by simp [hx]))
    refine ⟨L :: Ls, by simp [ofTerms?, hL, hLs], ?_⟩
    intro M hM; simp only [List.mem_cons] at hM
    rcases hM with rfl | hM
    · exact hP
    · exact hPs M hM

end Lin

/-- In a heading of rat attributes, a linear term reads as a form, for every dropped attribute. -/
theorem LinTerm.read {h : Heading} (hr : h.AllRat) (a : String) :
    ∀ {e : Term}, LinTerm e → (∀ x ∈ e.attrs, x ∈ h.attrs) →
      ∃ L, Lin.ofTerm? (Linear.okAttr h a) e = some L := by
  -- a constant factor reads as a constant form
  have konst : ∀ {x : Term} {L : Lin}, x.attrs = [] → Lin.ofTerm? (Linear.okAttr h a) x = some L →
      L.isConst = true := fun hx hL =>
    Lin.isConst_of_attrs fun b hb => by
      have := (Lin.ofTerm?_attrs _ _ hL).2 b hb; rw [hx] at this; simp at this
  intro e he
  induction he with
  | attr b =>
    intro hR
    have hb : b ∈ h.attrs := hR b (by simp [Term.attrs])
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp hb)
    have := hr.lookup hd; subst this
    exact ⟨Lin.ofAttr b, by simp [Lin.ofTerm?, Linear.okAttr, hd, Domain.numeric]⟩
  | @val v hv =>
    intro _
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hv
    exact ⟨Lin.ofConst q, by simp [Lin.ofTerm?, hq]⟩
  | @add es _ ih =>
    intro hR
    obtain ⟨Ls, hLs, _⟩ := Lin.ofTerms?_all (P := fun _ => True) (ok := Linear.okAttr h a)
      (es := es) fun x hx => (ih x hx (attrs_sub_call hx hR)).elim fun L hL => ⟨L, hL, trivial⟩
    exact ⟨Ls.foldl Lin.add (Lin.ofConst 0), by simp [Lin.ofTerm?, hLs, Lin.combine]⟩
  | @sub e es _ _ ih ihs =>
    intro hR
    obtain ⟨L, hL⟩ := ih (attrs_sub_call List.mem_cons_self hR)
    obtain ⟨Ls, hLs, _⟩ := Lin.ofTerms?_all (P := fun _ => True) (ok := Linear.okAttr h a)
      (es := es) fun x hx => (ihs x hx (attrs_sub_call (List.mem_cons_of_mem _ hx) hR)).elim
        fun L hL => ⟨L, hL, trivial⟩
    have h2 : Lin.ofTerms? (Linear.okAttr h a) (e :: es) = some (L :: Ls) := by
      simp [Lin.ofTerms?, hL, hLs]
    cases Ls with
    | nil => exact ⟨L.neg, by simp [Lin.ofTerm?, h2, Lin.combine]⟩
    | cons M Ms => exact ⟨(M :: Ms).foldl Lin.sub L, by simp [Lin.ofTerm?, h2, Lin.combine]⟩
  | @mul c d e _ hc _ _ hd ihc ih ihd =>
    intro hR
    have hR' : ∀ x ∈ c ++ e :: d, ∀ y ∈ x.attrs, y ∈ h.attrs := fun x hx => attrs_sub_call hx hR
    obtain ⟨Cs, hCs, kC⟩ := Lin.ofTerms?_all (P := fun L => L.isConst = true)
      (ok := Linear.okAttr h a) (es := c) fun x hx =>
        (ihc x hx (hR' x (by simp [hx]))).elim fun L hL => ⟨L, hL, konst (hc x hx) hL⟩
    obtain ⟨E, hE⟩ := ih (hR' e (by simp))
    obtain ⟨Ds, hDs, kD⟩ := Lin.ofTerms?_all (P := fun L => L.isConst = true)
      (ok := Linear.okAttr h a) (es := d) fun x hx =>
        (ihd x hx (hR' x (by simp [hx]))).elim fun L hL => ⟨L, hL, konst (hd x hx) hL⟩
    have hall := Lin.ofTerms?_append hCs (show Lin.ofTerms? _ (e :: d) = some (E :: Ds) by
      simp [Lin.ofTerms?, hE, hDs])
    obtain ⟨N₁, hN₁, kN₁⟩ := Lin.foldlM_const_const Cs kC (Lin.ofConst 1) rfl
    have hP : Lin.mul? N₁ E = some (E.scale N₁.const) := by simp [Lin.mul?, kN₁]
    obtain ⟨N, hN⟩ := Lin.foldlM_const Ds kD (E.scale N₁.const)
    exact ⟨N, by simp [Lin.ofTerm?, hall, Lin.combine, List.foldlM_append, hN₁,
      List.foldlM_cons, hP, hN]⟩
  | @mulc es _ hes ih =>
    intro hR
    obtain ⟨Ls, hLs, kL⟩ := Lin.ofTerms?_all (P := fun L => L.isConst = true)
      (ok := Linear.okAttr h a) (es := es) fun x hx =>
        (ih x hx (attrs_sub_call hx hR)).elim fun L hL => ⟨L, hL, konst (hes x hx) hL⟩
    obtain ⟨N, hN⟩ := Lin.foldlM_const Ls kL (Lin.ofConst 1)
    exact ⟨N, by simp [Lin.ofTerm?, hLs, Lin.combine, hN]⟩

/-! ## A linear-shaped term never refuses -/

/-- An attribute of a heading of rat attributes is an exact number on a fitting tuple. -/
theorem get_sig_rat {h : Heading} (hr : h.AllRat) {t : Tuple} (f : t.Fits h) {b : String}
    (hb : b ∈ h.attrs) : t.get? b = some (Value.ofRat (Linear.sig t b)) := by
  obtain ⟨v, q, hv, hq⟩ := atomic_eval hr f (.inl ⟨b, rfl⟩) (fun x hx => by
    simp [Term.attrs] at hx; subst hx; exact hb)
  have hg : t.get? b = some v := by
    simp only [Term.eval] at hv
    split at hv
    · rename_i w hw; cases hv; exact hw
    · cases hv
  have hs : Linear.sig t b = q := by simp [Linear.sig, hg, hq]
  rw [hg, hs, ← Value.eq_ofRat hq]

theorem LinTerm.eval {h : Heading} (hr : h.AllRat) {t : Tuple} (f : t.Fits h) {o : Term}
    (ho : LinTerm o) (hR : ∀ x ∈ o.attrs, x ∈ h.attrs) :
    ∃ v q, o.eval t = .ok v ∧ v.exact? = some q := by
  obtain ⟨L, hL⟩ := ho.read hr "" hR
  exact ⟨_, _, Lin.ofTerm?_eval o L (fun b hb => get_sig_rat hr f (hR b hb)) hL,
    Value.exact?_ofRat _⟩

theorem LinShaped.total {h : Heading} (hr : h.AllRat) {t : Tuple} (f : t.Fits h) :
    ∀ {e : Term}, LinShaped e → (∀ x ∈ e.attrs, x ∈ h.attrs) → ∃ b, e.holds t = .ok b := by
  intro e he
  induction he with
  | const b => intro _; exact ⟨b, Term.holds_ok.mpr (by simp [Term.eval])⟩
  | @and es _ ih =>
    intro hR
    have hg : ∀ x ∈ es, x.holds t = .ok (bv t x) := fun x hx => by
      obtain ⟨b, hb⟩ := ih x hx (attrs_sub_call hx hR); rw [hb, bv_eq hb]
    exact ⟨_, holds_andN hg⟩
  | @or es _ ih =>
    intro hR
    have hg : ∀ x ∈ es, x.holds t = .ok (bv t x) := fun x hx => by
      obtain ⟨b, hb⟩ := ih x hx (attrs_sub_call hx hR); rw [hb, bv_eq hb]
    exact ⟨_, holds_orN hg⟩
  | @not e _ ih =>
    intro hR
    obtain ⟨b, hb⟩ := ih (attrs_sub_call List.mem_cons_self hR)
    exact ⟨!b, holds_not1.mpr ⟨b, hb, rfl⟩⟩
  | @cmp op r l r' hop hl hr' =>
    intro hR
    have hop := Dense.XRel.ofOp_some hop
    subst hop
    obtain ⟨v, q, hv, hq⟩ := hl.eval hr f (attrs_sub_call List.mem_cons_self hR)
    obtain ⟨w, q', hw, hq'⟩ := hr'.eval hr f
      (attrs_sub_call (List.mem_cons_of_mem _ List.mem_cons_self) hR)
    exact ⟨_, holds_cmp r hv hq hw hq'⟩

theorem LinClass.total {u : Unrel} (hu : LinClass u) : u.Total :=
  fun _ f => hu.shaped.total hu.rat f hu.wf.reads

/-! ## σ, ∪, ∩, −, ⋈ and ρ keep the class -/

theorem lin_pair {op : String} {x y : Term} (hop : op = "and" ∨ op = "or")
    (hx : LinShaped x) (hy : LinShaped y) : LinShaped (.call op [x, y]) := by
  have : ∀ e ∈ [x, y], LinShaped e := by
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> assumption
  rcases hop with rfl | rfl
  · exact .and this
  · exact .or this

theorem LinClass.select {u w : Unrel} {p : Term} (hu : LinClass u) (hp : LinShaped p)
    (h : u.select p = .ok w) : LinClass w := by
  obtain ⟨hh, ht⟩ := Unrel.select_heading h
  exact ⟨Unrel.select_wf h hu.wf, hh ▸ hu.rat, ht ▸ lin_pair (.inl rfl) hu.shaped hp⟩

theorem LinClass.union {u v w : Unrel} (hu : LinClass u) (hv : LinClass v)
    (h : u.union v = .ok w) : LinClass w := by
  obtain ⟨_, hh, ht⟩ := Unrel.union_heading h
  exact ⟨Unrel.union_wf h hu.wf hv.wf, hh ▸ hu.rat, ht ▸ lin_pair (.inr rfl) hu.shaped hv.shaped⟩

theorem LinClass.inter {u v w : Unrel} (hu : LinClass u) (hv : LinClass v)
    (h : u.inter v = .ok w) : LinClass w := by
  obtain ⟨_, hh, ht⟩ := Unrel.inter_heading h
  exact ⟨Unrel.inter_wf h hu.wf hv.wf, hh ▸ hu.rat, ht ▸ lin_pair (.inl rfl) hu.shaped hv.shaped⟩

theorem LinClass.diff {u v w : Unrel} (hu : LinClass u) (hv : LinClass v)
    (h : u.diff v = .ok w) : LinClass w := by
  obtain ⟨_, hh, ht⟩ := Unrel.diff_heading h
  exact ⟨Unrel.diff_wf h hu.wf hv.wf, hh ▸ hu.rat,
    ht ▸ lin_pair (.inl rfl) hu.shaped (.not hv.shaped)⟩

theorem LinClass.join {u v w : Unrel} (hu : LinClass u) (hv : LinClass v)
    (h : u.join v = .ok w) : LinClass w := by
  have hw := Unrel.join_wf h hu.wf hv.wf
  obtain ⟨hj, ht⟩ := Unrel.join_heading h
  refine ⟨hw, fun p hp => ?_, ht ▸ lin_pair (.inl rfl) hu.shaped hv.shaped⟩
  obtain ⟨_, _, hl⟩ := Finrel.joinHeading_spec hj hu.wf.nodup hv.wf.nodup
  rcases hl p.1 p.2 (mem_lookup hw.nodup hp) with
    ⟨d, hd, (⟨_, e⟩ | ⟨e, he, hi⟩)⟩ | ⟨_, hk⟩
  · rw [e]; exact hu.rat _ hd
  · have h1 : d = .kind .rat := hu.rat _ hd
    have h2 : e = .kind .rat := hv.rat.lookup he
    subst h1; subst h2
    simp [Domain.inter] at hi
    exact hi.symm
  · exact hv.rat.lookup hk

theorem attrs_nil_rename {ren : List (String × String)} {x : Term} (hx : x.attrs = []) :
    (x.rename ren).attrs = [] := by
  cases e : (x.rename ren).attrs with
  | nil => rfl
  | cons y ys =>
    obtain ⟨b, hb, _⟩ := Term.attrs_rename x (a := y) (by rw [e]; exact List.mem_cons_self)
    rw [hx] at hb; cases hb

theorem LinTerm.rename (ren : List (String × String)) :
    ∀ {e : Term}, LinTerm e → LinTerm (e.rename ren) := by
  intro e he
  induction he with
  | attr b => simp only [Term.rename]; exact .attr _
  | @val v hv => simp only [Term.rename]; exact .val hv
  | @add es _ ih =>
    simp only [Term.rename]
    exact .add fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact ih y hy
  | @sub e es _ _ ih ihs =>
    simp only [Term.rename, List.map_cons]
    exact .sub ih fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact ihs y hy
  | @mul c d e _ hc _ _ hd ihc ih ihd =>
    simp only [Term.rename, List.map_append, List.map_cons]
    exact .mul (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact ihc y hy)
      (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact attrs_nil_rename (hc y hy))
      ih (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact ihd y hy)
      (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact attrs_nil_rename (hd y hy))
  | @mulc es _ hes ih =>
    simp only [Term.rename]
    exact .mulc (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact ih y hy)
      (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact attrs_nil_rename (hes y hy))

theorem LinShaped.rename (ren : List (String × String)) :
    ∀ {e : Term}, LinShaped e → LinShaped (e.rename ren) := by
  intro e he
  induction he with
  | const b => simp only [Term.rename]; exact .const b
  | @and es _ ih =>
    simp only [Term.rename]
    exact .and fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact ih y hy
  | @or es _ ih =>
    simp only [Term.rename]
    exact .or fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact ih y hy
  | @not e _ ih => simp only [Term.rename, List.map_cons, List.map_nil]; exact .not ih
  | @cmp op r l r' hop hl hr =>
    simp only [Term.rename, List.map_cons, List.map_nil]
    exact .cmp hop (hl.rename ren) (hr.rename ren)

theorem LinClass.rename {u w : Unrel} {ren : List (String × String)} (hu : LinClass u)
    (h : u.rename ren = .ok w) : LinClass w := by
  have hw := Unrel.rename_wf h hu.wf
  obtain ⟨_, rfl⟩ := Unrel.rename_eq h
  refine ⟨hw, fun p hp => ?_, hu.shaped.rename ren⟩
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hu.rat q hq

/-! ## π keeps the class -/

/-- In a heading of rat attributes, a linear-shaped term is accepted by the linear class for
every attribute. -/
theorem LinShaped.linIn {h : Heading} (hr : h.AllRat) (a : String) :
    ∀ {e : Term}, LinShaped e → (∀ x ∈ e.attrs, x ∈ h.attrs) → Linear.LinIn h a e := by
  intro e he
  induction he with
  | const b => intro _; exact .opq (by simp [Term.attrs])
  | @and es _ ih => intro hR; exact .and fun x hx => ih x hx (attrs_sub_call hx hR)
  | @or es _ ih => intro hR; exact .or fun x hx => ih x hx (attrs_sub_call hx hR)
  | @not e _ ih => intro hR; exact .not (ih (attrs_sub_call List.mem_cons_self hR))
  | @cmp op r l r' hop hl hr' =>
    intro hR
    obtain ⟨Ll, hLl⟩ := hl.read hr a (attrs_sub_call List.mem_cons_self hR)
    obtain ⟨Lr, hLr⟩ := hr'.read hr a (attrs_sub_call (List.mem_cons_of_mem _ List.mem_cons_self) hR)
    obtain ⟨h1, h2, h3⟩ := Dense.XRel.ofOp_ne hop
    exact .leaf h1 h2 h3 ⟨r, l, r', Ll, Lr, hop, rfl, hLl, hLr⟩

/-- A rendered form is a linear term. -/
theorem LinTerm.render (L : Lin) : LinTerm L.render := by
  refine .add fun x hx => ?_
  simp only [List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨p, _, rfl⟩
  · exact .val (by simp [Value.exact?_ofRat])
  · exact .mul (c := [.val (Value.ofRat p.2)]) (d := [])
      (fun x hx => by simp at hx; subst hx; exact .val (by simp [Value.exact?_ofRat]))
      (fun x hx => by simp at hx; subst hx; simp [Term.attrs]) (.attr _) (by simp) (by simp)

/-! ### Removal by dense order keeps linear shape -/

theorem dense_dnf_lin (a : String) :
    ∀ {e : Term}, LinShaped e → ∀ (p : Bool), ∀ c ∈ Dense.dnf a p e, ∀ l ∈ c,
      LitShapedG LinShaped LinTerm l := by
  have opq : ∀ {e : Term} (p : Bool), LinShaped e → a ∉ e.attrs →
      ∀ c ∈ Dense.dnf a p e, ∀ l ∈ c, LitShapedG LinShaped LinTerm l := by
    intro e p he hna c hc l hl
    rw [Dense.dnf, NF.dnf_opq hna] at hc
    simp only [List.mem_singleton] at hc; subst hc
    simp only [List.mem_singleton] at hl; subst hl
    exact he
  intro e he
  induction he with
  | const b => intro p; exact opq p (.const b) (by simp [Term.attrs])
  | @and es hes ih =>
    intro p
    by_cases hca : a ∈ (Term.call "and" es).attrs
    case neg => exact opq p (.and hes) hca
    rw [Dense.dnf, NF.dnf_and hca]
    cases p
    · intro c hc l hl
      obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
      exact ih y hy false c hc l hl
    · exact foldr_conj_all es fun y hy => ih y hy true
  | @or es hes ih =>
    intro p
    by_cases hca : a ∈ (Term.call "or" es).attrs
    case neg => exact opq p (.or hes) hca
    rw [Dense.dnf, NF.dnf_or hca]
    cases p
    · exact foldr_conj_all es fun y hy => ih y hy false
    · intro c hc l hl
      obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
      exact ih y hy true c hc l hl
  | @not e he ih =>
    intro p
    by_cases hca : a ∈ (Term.call "not" [e]).attrs
    case neg => exact opq p (.not he) hca
    rw [Dense.dnf, NF.dnf_not hca]
    exact ih (!p)
  | @cmp op r l' r' hop hl hr =>
    intro p
    by_cases hca : a ∈ (Term.call op [l', r']).attrs
    case neg => exact opq p (.cmp hop hl hr) hca
    obtain ⟨h1, h2, h3⟩ := Dense.XRel.ofOp_ne hop
    rw [Dense.dnf, NF.dnf_leaf h1 h2 h3 hca, Dense.leaf_cmp hop]
    intro c hc l hl'
    unfold Dense.atom at hc
    by_cases il : Dense.isAttr a l' = true
    · by_cases ir : Dense.isAttr a r' = true
      · simp only [il, ir, ↓reduceIte, List.mem_singleton] at hc; subst hc
        simp only [List.mem_singleton] at hl'; subst hl'; trivial
      · simp only [il, ir, ↓reduceIte, Bool.false_eq_true] at hc
        obtain ⟨s', _, rfl⟩ := List.mem_map.mp hc
        simp only [List.mem_singleton] at hl'; subst hl'; exact hr
    · simp only [il, ↓reduceIte, Bool.false_eq_true] at hc
      obtain ⟨s', _, rfl⟩ := List.mem_map.mp hc
      simp only [List.mem_singleton] at hl'; subst hl'; exact hl

theorem lin_cmp (r : XRel) {l r' : Term} (hl : LinTerm l) (hr : LinTerm r') :
    LinShaped (.call r.op [l, r']) := .cmp (XRel.ofOp_op r) hl hr

theorem dense_elim_lin (a : String) {e : Term} (he : LinShaped e) :
    LinShaped (Dense.elim a e) := by
  unfold Dense.elim NF.elim
  refine .or fun x hx => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact .and (elimConj_shapedG (Sh := LinShaped) (At := LinTerm) .const .not
    (fun r _ _ hl hr => lin_cmp r hl hr) (dense_dnf_lin a he true c hc))

/-! ### Removal by linear arithmetic keeps linear shape -/

/-- What the linear normal form of a linear-shaped term holds. -/
def LinLit : Linear.Lit → Prop
  | .opq _ e => LinShaped e
  | .atom _ => True
  | .const _ => True

theorem lin_dnf (h : Heading) (a : String) :
    ∀ {e : Term}, LinShaped e → ∀ (p : Bool), ∀ c ∈ NF.dnf (Linear.leaf h a) a p e, ∀ l ∈ c,
      LinLit l := by
  have opq : ∀ {e : Term} (p : Bool), LinShaped e → a ∉ e.attrs →
      ∀ c ∈ NF.dnf (Linear.leaf h a) a p e, ∀ l ∈ c, LinLit l := by
    intro e p he hna c hc l hl
    rw [NF.dnf_opq hna] at hc
    simp only [List.mem_singleton] at hc; subst hc
    simp only [List.mem_singleton] at hl; subst hl
    exact he
  intro e he
  induction he with
  | const b => intro p; exact opq p (.const b) (by simp [Term.attrs])
  | @and es hes ih =>
    intro p
    by_cases hca : a ∈ (Term.call "and" es).attrs
    case neg => exact opq p (.and hes) hca
    rw [NF.dnf_and hca]
    cases p
    · intro c hc l hl
      obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
      exact ih y hy false c hc l hl
    · exact foldr_conj_all es fun y hy => ih y hy true
  | @or es hes ih =>
    intro p
    by_cases hca : a ∈ (Term.call "or" es).attrs
    case neg => exact opq p (.or hes) hca
    rw [NF.dnf_or hca]
    cases p
    · exact foldr_conj_all es fun y hy => ih y hy false
    · intro c hc l hl
      obtain ⟨y, hy, hc⟩ := List.mem_flatMap.mp hc
      exact ih y hy true c hc l hl
  | @not e he ih =>
    intro p
    by_cases hca : a ∈ (Term.call "not" [e]).attrs
    case neg => exact opq p (.not he) hca
    rw [NF.dnf_not hca]
    exact ih (!p)
  | @cmp op r l' r' hop hl hr =>
    intro p
    by_cases hca : a ∈ (Term.call op [l', r']).attrs
    case neg => exact opq p (.cmp hop hl hr) hca
    obtain ⟨h1, h2, h3⟩ := Dense.XRel.ofOp_ne hop
    rw [NF.dnf_leaf h1 h2 h3 hca]
    intro c hc l hl'
    have hop' := Dense.XRel.ofOp_some hop
    subst hop'
    simp only [Linear.leaf, hop] at hc
    split at hc
    · unfold Linear.row at hc
      split at hc
      · simp only [List.mem_singleton] at hc; subst hc
        simp only [List.mem_singleton] at hl'; subst hl'
        exact lin_cmp r (.render _) (.val (by simp [Value.exact?]))
      · obtain ⟨s', _, rfl⟩ := List.mem_map.mp hc
        simp only [List.mem_singleton] at hl'; subst hl'; trivial
    · simp at hc

theorem lin_elim (h : Heading) (a : String) {e : Term} (he : LinShaped e) :
    LinShaped (Linear.elim h a e) := by
  unfold Linear.elim NF.elim
  refine .or fun x hx => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  have hl := lin_dnf h a he true c hc
  refine .and fun e he' => ?_
  simp only [NF.elimConj] at he'
  rcases List.mem_append.mp he' with he' | he'
  · obtain ⟨l, hlc, he'⟩ := List.mem_filterMap.mp he'
    have hs := hl l hlc
    cases l with
    | opq p e' =>
      simp only [NF.Lit.rest, Option.some.injEq] at he'; subst he'
      cases p
      · exact .not hs
      · exact hs
    | const b =>
      simp only [NF.Lit.rest, Option.some.injEq] at he'; subst he'; exact .const b
    | atom _ => simp [NF.Lit.rest] at he'
  · unfold Linear.xpart at he'
    exact xpart_shaped (Sh := LinShaped) (At := LinTerm) (fun r _ _ hl hr => lin_cmp r hl hr)
      (fun hm => by
        obtain ⟨x, _, hx⟩ := List.mem_map.mp hm
        cases hx; exact .render _) e he'

/-! ### The class π picks, and the result -/

/-- The class π picks for a relation in the linear class: dense order when it accepts,
linear arithmetic otherwise. -/
def LinClass.pick (u : Unrel) (a : String) : Class :=
  if Class.accepts? .dense u a then .dense else .linear

theorem LinClass.accepts {u : Unrel} (hu : LinClass u) {a : String}
    (ha : a ∈ u.heading.attrs) : Class.Accepts .linear u a := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp ha)
  have := hu.rat.lookup hd
  subst this
  exact ⟨hd, hu.shaped.linIn hu.rat a hu.wf.reads⟩

theorem LinClass.pick_accepts {u : Unrel} (hu : LinClass u) {a : String}
    (ha : a ∈ u.heading.attrs) : (LinClass.pick u a).Accepts u a := by
  unfold LinClass.pick
  split
  · exact Class.accepts?_iff.mp ‹_›
  · exact hu.accepts ha

theorem LinClass.firstIn {u : Unrel} (hu : LinClass u) {a : String}
    (ha : a ∈ u.heading.attrs) : Class.FirstIn Class.all u a (LinClass.pick u a) := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (Finrel.mem_attrs_iff.mp ha)
  have hdr := hu.rat.lookup hd
  subst hdr
  have hnf : ¬ Class.Accepts .finite u a := by
    rintro ⟨d, vs, hd', hvs⟩
    rw [hu.rat.lookup hd'] at hvs
    simp [Domain.values?] at hvs
  have hne : ¬ Class.Accepts .equality u a := by
    rintro ⟨d, hd', hinf, _⟩
    rw [hd] at hd'; cases hd'
    simp [Equality.infinite?] at hinf
  unfold LinClass.pick
  split
  · exact .inr ⟨hnf, .inl ⟨Class.accepts?_iff.mp ‹_›, rfl⟩⟩
  · rename_i hnd
    exact .inr ⟨hnf, .inr ⟨fun h => hnd (Class.accepts?_iff.mpr h),
      .inr ⟨hne, .inl ⟨hu.accepts (by exact ha), rfl⟩⟩⟩⟩

theorem LinClass.dropOne {u : Unrel} (hu : LinClass u) {a : String}
    (ha : a ∈ u.heading.attrs) : LinClass (u.dropOne a (LinClass.pick u a)) := by
  obtain ⟨hw, _⟩ := dropOne_wf (hu.pick_accepts ha) hu.wf hu.total
  refine ⟨hw, fun p hp => hu.rat p (List.mem_filter.mp hp).1, ?_⟩
  simp only [Unrel.dropOne, LinClass.pick]
  split
  · exact dense_elim_lin a hu.shaped
  · exact lin_elim u.heading a hu.shaped

theorem LinClass.eliminate : ∀ {u : Unrel} {l : List String}, LinClass u → l.Nodup →
    (∀ x ∈ l, x ∈ u.heading.attrs) →
    AllAccepted u l ∧ ∀ w, u.eliminate l = .ok w → LinClass w
  | u, [], hu, _, _ => by
    refine ⟨trivial, fun w h => ?_⟩
    simp only [Unrel.eliminate, Except.ok.injEq] at h; subst h; exact hu
  | u, a :: rest, hu, hn, hl => by
    have ha := hl a List.mem_cons_self
    have hrest : ∀ x ∈ rest, x ∈ (u.dropOne a (LinClass.pick u a)).heading.attrs := fun x hx =>
      dropOne_attrs.mpr ⟨hl x (List.mem_cons_of_mem _ hx),
        fun e => (List.nodup_cons.mp hn).1 (e ▸ hx)⟩
    obtain ⟨hacc, hel⟩ := LinClass.eliminate (hu.dropOne ha) (List.nodup_cons.mp hn).2 hrest
    refine ⟨⟨LinClass.pick u a, hu.firstIn ha, hacc⟩, fun w h => ?_⟩
    have hr : recognise u a = .ok (LinClass.pick u a) := recognise_ok_iff.mpr (hu.firstIn ha)
    simp only [Unrel.eliminate, hr, bind, Except.bind] at h
    exact hel w h

/-- π never refuses a relation in the linear class, except for its checks on the list. -/
theorem LinClass.project_ok {u : Unrel} {as : List String} (hu : LinClass u)
    (hn : as.Nodup) (hin : ∀ a ∈ as, a ∈ u.heading.attrs) : ∃ w, u.project as = .ok w :=
  project_ok_iff.mpr ⟨hn, hin,
    (LinClass.eliminate hu (dropOrder_nodup hu.wf.nodup) dropOrder_sub).1⟩

theorem LinClass.project {u w : Unrel} {as : List String} (hu : LinClass u)
    (h : u.project as = .ok w) : LinClass w := by
  obtain ⟨hw, _, _⟩ := project_sound h hu.wf hu.total
  have hpk := project_pick h
  refine ⟨hw, fun p hp => ?_, ?_⟩
  · exact hu.rat.lookup (Heading.pick_lookup hpk p.1 p.2 (mem_lookup hw.nodup hp))
  · rw [project_eq] at h
    split at h
    · cases h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    split at h
    · cases h
    rename_i w' hw'
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ((LinClass.eliminate hu (dropOrder_nodup hu.wf.nodup) dropOrder_sub).2 w' hw').shaped

end Rasso
