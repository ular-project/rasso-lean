import Rasso.Dense
import Rasso.LinElim

/-!
# Rasso: reading terms as linear forms, proved

The definitions are in `Rasso.LinElim`:

* `Lin.ofTerm? ok e` reads the term `e` as a linear form: exact constants, attributes that
  `ok` allows, `+`, `-` with at least one operand, and `*` in which every factor but one is a
  constant. Anything else (including `sum`, and `-` with no operands) is not read.
* `Lin.render L` writes a form back as a term: `k + c₁ * b₁ + …`.

Proved: on a tuple whose attributes are the numbers `σ` gives, a term read as `L`
evaluates to `Value.ofRat (L.eval σ)` (`ofTerm?_eval`), and so does `L.render`
(`render_eval`). The arithmetic of exact values is `arith_exact`: on ints and rats,
`+ - *` give `Value.ofRat` of the rational result, because the cast from `Int` to `Rat`
commutes with them.
-/

namespace Rasso

/-! ## Arithmetic on exact values -/

theorem allInts_exact : ∀ {vs : List Value} {ns : List Int} {qs : List Rat},
    allInts vs = some ns → vs.mapM Value.exact? = some qs → qs = ns.map (fun n : Int => (n : Rat))
  | [], ns, qs, h1, h2 => by simp [allInts] at h1 h2; subst h1; subst h2; rfl
  | v :: vs, ns, qs, h1, h2 => by
    cases v <;> simp [allInts, List.mapM_cons, Value.exact?] at h1 h2
    case int n =>
      obtain ⟨ns', e1, h1'⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨qs', e2, h2'⟩ := Option.bind_eq_some_iff.mp h2
      cases h1'; cases h2'
      simp [allInts_exact (by simpa [allInts] using e1) e2]

theorem asExact_mapM : ∀ {vs : List Value} {qs : List Rat} (who : String),
    vs.mapM Value.exact? = some qs → vs.mapM (asExact who) = .ok qs
  | [], qs, _, h => by simp at h; subst h; rfl
  | v :: vs, qs, who, h => by
    cases e2 : List.mapM Value.exact? vs <;>
      cases v <;> simp [List.mapM_cons, Value.exact?, e2] at h
    all_goals subst h; simp [List.mapM_cons, asExact, asExact_mapM who e2]; rfl

theorem arith_exact {who : String} {onInt : List Int → Int} {onRat : List Rat → Rat}
    (hc : ∀ ns : List Int, ((onInt ns : Int) : Rat) = onRat (ns.map fun n : Int => (n : Rat)))
    {vs : List Value} {qs : List Rat} (h : vs.mapM Value.exact? = some qs) :
    arith who onInt onRat vs = .ok (Value.ofRat (onRat qs)) := by
  unfold arith
  cases hi : allInts vs with
  | some ns =>
    rw [allInts_exact hi h, ← hc]
    simp only [pure, Except.pure]
    rw [← Value.eq_ofRat (v := .int (onInt ns)) rfl]
  | none =>
    simp only [asExact_mapM who h, bind, Except.bind, pure, Except.pure]

namespace Lin
open Lin


variable (σ : String → Rat)

theorem eval_const {L : Lin} (h : L.isConst = true) : L.eval σ = L.const := by
  obtain ⟨ts, k⟩ := L
  simp only [isConst, List.isEmpty_iff] at h; subst h
  simp [eval, evalTerms, Rat.zero_add]

theorem eval_mul? {L M N : Lin} (h : mul? L M = some N) : N.eval σ = L.eval σ * M.eval σ := by
  unfold mul? at h
  split at h
  · rename_i hc; cases h; rw [eval_scale, eval_const σ hc]
  · split at h
    · rename_i hc; cases h; rw [eval_scale, eval_const σ hc]; grind
    · cases h

theorem eval_foldl_add : ∀ (Ls : List Lin) (M : Lin),
    (Ls.foldl add M).eval σ = (Ls.map (eval σ)).foldl (· + ·) (M.eval σ)
  | [], _ => rfl
  | L :: Ls, M => by simp only [List.foldl_cons, List.map_cons, eval_foldl_add Ls, eval_add]

theorem eval_foldl_sub : ∀ (Ls : List Lin) (M : Lin),
    (Ls.foldl sub M).eval σ = (Ls.map (eval σ)).foldl (· - ·) (M.eval σ)
  | [], _ => rfl
  | L :: Ls, M => by simp only [List.foldl_cons, List.map_cons, eval_foldl_sub Ls, eval_sub]

theorem eval_foldlM_mul : ∀ (Ls : List Lin) (M N : Lin), Ls.foldlM mul? M = some N →
    N.eval σ = (Ls.map (eval σ)).foldl (· * ·) (M.eval σ)
  | [], M, N, h => by simp at h; subst h; rfl
  | L :: Ls, M, N, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨P, hP, h⟩ := Option.bind_eq_some_iff.mp h
    rw [eval_foldlM_mul Ls P N h, eval_mul? σ hP]; rfl

end Lin

theorem cast_foldl_add : ∀ (ns : List Int) (k : Int),
    ((ns.foldl (· + ·) k : Int) : Rat) = (ns.map fun n : Int => (n : Rat)).foldl (· + ·) (k : Rat)
  | [], _ => rfl
  | n :: ns, k => by simp only [List.foldl_cons, List.map_cons, cast_foldl_add ns, Rat.intCast_add]

theorem cast_foldl_mul : ∀ (ns : List Int) (k : Int),
    ((ns.foldl (· * ·) k : Int) : Rat) = (ns.map fun n : Int => (n : Rat)).foldl (· * ·) (k : Rat)
  | [], _ => rfl
  | n :: ns, k => by simp only [List.foldl_cons, List.map_cons, cast_foldl_mul ns, Rat.intCast_mul]

theorem cast_foldl_sub : ∀ (ns : List Int) (k : Int),
    ((ns.foldl (· - ·) k : Int) : Rat) = (ns.map fun n : Int => (n : Rat)).foldl (· - ·) (k : Rat)
  | [], _ => rfl
  | n :: ns, k => by simp only [List.foldl_cons, List.map_cons, cast_foldl_sub ns, Rat.intCast_sub]

theorem exact_map_ofRat (qs : List Rat) : (qs.map Value.ofRat).mapM Value.exact? = some qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [List.mapM_cons, Value.exact?_ofRat, ih]

namespace Lin

theorem combine_eval (σ : String → Rat) {op : String} {Ls : List Lin} {L : Lin}
    (h : combine op Ls = some L) :
    applyOp op (Ls.map fun M => Value.ofRat (M.eval σ)) = .ok (Value.ofRat (L.eval σ)) := by
  have hx : (Ls.map fun M => Value.ofRat (M.eval σ)).mapM Value.exact? = some (Ls.map (eval σ)) := by
    rw [← exact_map_ofRat]; simp [List.map_map]; rfl
  unfold combine at h
  split at h
  · cases h
    simp only [applyOp]
    rw [arith_exact (fun ns => by rw [cast_foldl_add]; rfl) hx]
    simp [eval_foldl_add, eval_ofConst]
  · rename_i M; cases h
    simp only [List.map_cons, List.map_nil, applyOp]
    rw [arith_exact (onRat := fun qs => - qs.headD 0) (fun ns => by cases ns <;> simp) (vs := [_])
      (qs := [M.eval σ]) (by simp [Value.exact?_ofRat])]
    simp [eval_neg]
  · rename_i M Ms hne; cases h
    cases Ms with
    | nil => exact absurd rfl hne
    | cons N Ns =>
      simp only [List.map_cons, applyOp]
      rw [arith_exact (onRat := fun qs => qs.tail.foldl (· - ·) (qs.headD 0))
        (fun ns => by cases ns <;> simp [cast_foldl_sub]) (vs := _ :: _ :: _)
        (qs := (M :: N :: Ns).map (eval σ)) (by rw [← hx]; rfl)]
      simp [eval_foldl_sub, eval_sub]
  · cases ho : Ls.foldlM mul? (ofConst 1) <;> rw [ho] at h <;> cases h
    simp only [applyOp]
    rw [arith_exact (fun ns => by rw [cast_foldl_mul]; rfl) hx]
    simp [eval_foldlM_mul σ Ls _ _ ho, eval_ofConst]
  · cases h
end Lin

namespace Lin

theorem ofTerm?_call {ok : String → Bool} {op : String} {es : List Term} {L : Lin}
    (h : ofTerm? ok (.call op es) = some L) :
    ∃ Ls, ofTerms? ok es = some Ls ∧ combine op Ls = some L := by
  simp only [ofTerm?] at h
  exact Option.bind_eq_some_iff.mp h

theorem ofTerms?_cons {ok : String → Bool} {e : Term} {es : List Term} {Ls : List Lin}
    (h : ofTerms? ok (e :: es) = some Ls) :
    ∃ L Ms, ofTerm? ok e = some L ∧ ofTerms? ok es = some Ms ∧ Ls = L :: Ms := by
  simp only [ofTerms?] at h
  obtain ⟨L, hL, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Ms, hM, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨L, Ms, hL, hM, rfl⟩

variable {t : Tuple} {σ : String → Rat} {ok : String → Bool}

mutual
/-- A term that reads as a form evaluates to the form's value, on a tuple whose attributes
are the numbers `σ` gives. -/
theorem ofTerm?_eval : ∀ (e : Term) (L : Lin),
    (∀ b ∈ e.attrs, t.get? b = some (Value.ofRat (σ b))) → ofTerm? ok e = some L →
    e.eval t = .ok (Value.ofRat (L.eval σ))
  | .attr b, L, hσ, h => by
    simp only [ofTerm?] at h
    split at h
    · cases h; simp [Term.eval, hσ b (by simp [Term.attrs]), eval_ofAttr]
    · cases h
  | .val v, L, _, h => by
    simp only [ofTerm?] at h
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [Term.eval, eval_ofConst, ← Value.eq_ofRat hq]
  | .call op es, L, hσ, h => by
    obtain ⟨Ls, hLs, hc⟩ := ofTerm?_call h
    have := ofTerms?_eval es Ls (fun b hb => hσ b (by simpa [Term.attrs] using hb)) hLs
    simp only [Term.eval, this, bind, Except.bind]
    exact combine_eval σ hc

theorem ofTerms?_eval : ∀ (es : List Term) (Ls : List Lin),
    (∀ b ∈ es.flatMap Term.attrs, t.get? b = some (Value.ofRat (σ b))) → ofTerms? ok es = some Ls →
    es.mapM (Term.eval t) = .ok (Ls.map fun L => Value.ofRat (L.eval σ))
  | [], Ls, _, h => by simp [ofTerms?] at h; subst h; rfl
  | e :: es, Ls, hσ, h => by
    obtain ⟨L, Ms, hL, hM, rfl⟩ := ofTerms?_cons h
    have h1 := ofTerm?_eval e L (fun b hb => hσ b (by simp [hb])) hL
    have h2 := ofTerms?_eval es Ms (fun b hb => hσ b (by simp_all)) hM
    simp [List.mapM_cons, h1, h2, bind, Except.bind, pure, Except.pure]
end

end Lin

namespace Lin


theorem ofTerm?_pairTerm (ok : String → Bool) (p : String × Rat) (hp : ok p.1 = true) :
    ofTerm? ok (pairTerm p) = some ((ofAttr p.1).scale (1 * p.2)) := by
  simp [pairTerm, ofTerm?, ofTerms?, hp, Value.exact?_ofRat, combine, mul?, isConst, ofConst,
    scale, List.foldlM_cons]

theorem ofTerms?_pairs (ok : String → Bool) : ∀ (l : List (String × Rat)), (∀ p ∈ l, ok p.1 = true) →
    ofTerms? ok (l.map pairTerm) = some (l.map fun p => (ofAttr p.1).scale (1 * p.2))
  | [], _ => rfl
  | p :: l, h => by
    simp only [List.map_cons, ofTerms?, ofTerm?_pairTerm ok p (h p (by simp)),
      ofTerms?_pairs ok l (fun q hq => h q (by simp [hq]))]
    rfl

theorem foldl_pairs (σ : String → Rat) : ∀ (l : List (String × Rat)) (a : Rat),
    ((l.map fun p => (ofAttr p.1).scale (1 * p.2)).map (eval σ)).foldl (· + ·) a = a + evalTerms σ l
  | [], a => by simp [evalTerms, Rat.add_zero]
  | p :: l, a => by
    simp only [List.map_cons, List.foldl_cons, foldl_pairs σ l, evalTerms, eval_scale, eval_ofAttr]
    grind

theorem attrs_render {L : Lin} {b : String} : b ∈ L.render.attrs ↔ b ∈ L.attrs := by
  simp only [render, Term.attrs, pairTerm, attrs, List.flatMap_cons, List.flatMap_map,
    List.nil_append, List.mem_flatMap, List.flatMap_nil, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

/-- The rendered form reads back as a form with the same value. -/
theorem ofTerm?_render (ok : String → Bool) (L : Lin) (h : ∀ b ∈ L.attrs, ok b = true) :
    ∃ M, ofTerm? ok L.render = some M ∧ ∀ σ, M.eval σ = L.eval σ := by
  refine ⟨(ofConst L.const :: L.terms.map fun p => (ofAttr p.1).scale (1 * p.2)).foldl add
    (ofConst 0), ?_, fun σ => ?_⟩
  · simp only [render, ofTerm?, ofTerms?, Value.exact?_ofRat, Option.map_some,
      ofTerms?_pairs ok L.terms (fun p hp => h p.1 (by simp [attrs]; exact ⟨p.2, hp⟩)),
      Option.bind_some, combine]
  · rw [eval_foldl_add]
    simp only [List.map_cons, List.foldl_cons, eval_ofConst]
    rw [foldl_pairs]; simp only [eval]; grind

/-- The rendered form evaluates to the form's value. -/
theorem render_eval {t : Tuple} {σ : String → Rat} (L : Lin)
    (hσ : ∀ b ∈ L.attrs, t.get? b = some (Value.ofRat (σ b))) :
    L.render.eval t = .ok (Value.ofRat (L.eval σ)) := by
  obtain ⟨M, hM, he⟩ := ofTerm?_render (fun _ => true) L (fun _ _ => rfl)
  rw [ofTerm?_eval (ok := fun _ => true) _ M (fun b hb => hσ b (attrs_render.mp hb)) hM, he]

end Lin

namespace Lin

theorem attrs_ofConst {k : Rat} {b : String} : b ∉ (ofConst k).attrs := by simp [attrs, ofConst]

theorem attrs_foldl_add {b : String} : ∀ (Ls : List Lin) (M : Lin), b ∈ (Ls.foldl add M).attrs →
    b ∈ M.attrs ∨ ∃ N ∈ Ls, b ∈ N.attrs
  | [], _, h => .inl h
  | L :: Ls, M, h => by
    rcases attrs_foldl_add Ls _ h with h | ⟨N, hN, hb⟩
    · rcases attrs_add.mp h with h | h
      · exact .inl h
      · exact .inr ⟨L, by simp, h⟩
    · exact .inr ⟨N, by simp [hN], hb⟩

theorem attrs_foldl_sub {b : String} : ∀ (Ls : List Lin) (M : Lin), b ∈ (Ls.foldl sub M).attrs →
    b ∈ M.attrs ∨ ∃ N ∈ Ls, b ∈ N.attrs
  | [], _, h => .inl h
  | L :: Ls, M, h => by
    rcases attrs_foldl_sub Ls _ h with h | ⟨N, hN, hb⟩
    · rcases attrs_sub.mp h with h | h
      · exact .inl h
      · exact .inr ⟨L, by simp, h⟩
    · exact .inr ⟨N, by simp [hN], hb⟩

theorem attrs_mul? {L M N : Lin} {b : String} (h : mul? L M = some N) (hb : b ∈ N.attrs) :
    b ∈ L.attrs ∨ b ∈ M.attrs := by
  unfold mul? at h
  split at h
  · cases h; exact .inr (attrs_scale.mp hb)
  · split at h
    · cases h; exact .inl (attrs_scale.mp hb)
    · cases h

theorem attrs_foldlM_mul {b : String} : ∀ (Ls : List Lin) (M N : Lin), Ls.foldlM mul? M = some N →
    b ∈ N.attrs → b ∈ M.attrs ∨ ∃ P ∈ Ls, b ∈ P.attrs
  | [], M, N, h, hb => by simp at h; subst h; exact .inl hb
  | L :: Ls, M, N, h, hb => by
    simp only [List.foldlM_cons] at h
    obtain ⟨P, hP, h⟩ := Option.bind_eq_some_iff.mp h
    rcases attrs_foldlM_mul Ls P N h hb with h | ⟨Q, hQ, hq⟩
    · rcases attrs_mul? hP h with h | h
      · exact .inl h
      · exact .inr ⟨L, by simp, h⟩
    · exact .inr ⟨Q, by simp [hQ], hq⟩

theorem attrs_combine {op : String} {Ls : List Lin} {L : Lin} {b : String}
    (h : combine op Ls = some L) (hb : b ∈ L.attrs) : ∃ M ∈ Ls, b ∈ M.attrs := by
  unfold combine at h
  split at h
  · cases h
    rcases attrs_foldl_add _ _ hb with h | h
    · exact absurd h attrs_ofConst
    · exact h
  · rename_i M; cases h; exact ⟨M, by simp, attrs_neg.mp hb⟩
  · rename_i M Ms _; cases h
    rcases attrs_foldl_sub _ _ hb with h | ⟨N, hN, h⟩
    · exact ⟨M, by simp, h⟩
    · exact ⟨N, by simp [hN], h⟩
  · rcases attrs_foldlM_mul _ _ _ h hb with h | h
    · exact absurd h attrs_ofConst
    · exact h
  · cases h

variable {ok : String → Bool}

mutual
/-- A form reads only attributes of its term, each one that `ok` allows. -/
theorem ofTerm?_attrs : ∀ (e : Term) (L : Lin), ofTerm? ok e = some L →
    (∀ b ∈ e.attrs, ok b = true) ∧ (∀ b ∈ L.attrs, b ∈ e.attrs)
  | .attr b, L, h => by
    simp only [ofTerm?] at h
    split at h
    · cases h
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · simp [Term.attrs] at hc; subst hc; assumption
      · simpa [Term.attrs, attrs, ofAttr] using hc
    · cases h
  | .val v, L, h => by
    simp only [ofTerm?] at h
    obtain ⟨q, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨fun _ hc => by simp [Term.attrs] at hc, fun _ hc => absurd hc attrs_ofConst⟩
  | .call op es, L, h => by
    obtain ⟨Ls, hLs, hc⟩ := ofTerm?_call h
    obtain ⟨h1, h2⟩ := ofTerms?_attrs es Ls hLs
    refine ⟨fun b hb => h1 b (by simpa [Term.attrs] using hb), fun b hb => ?_⟩
    obtain ⟨M, hM, hb⟩ := attrs_combine hc hb
    simpa [Term.attrs] using h2 M hM b hb

theorem ofTerms?_attrs : ∀ (es : List Term) (Ls : List Lin), ofTerms? ok es = some Ls →
    (∀ b ∈ es.flatMap Term.attrs, ok b = true) ∧
      (∀ M ∈ Ls, ∀ b ∈ M.attrs, b ∈ es.flatMap Term.attrs)
  | [], Ls, h => by simp [ofTerms?] at h; subst h; simp
  | e :: es, Ls, h => by
    obtain ⟨L, Ms, hL, hM, rfl⟩ := ofTerms?_cons h
    obtain ⟨a1, a2⟩ := ofTerm?_attrs e L hL
    obtain ⟨b1, b2⟩ := ofTerms?_attrs es Ms hM
    refine ⟨fun b hb => ?_, fun M hM b hb => ?_⟩
    · simp only [List.flatMap_cons, List.mem_append] at hb
      exact hb.elim (a1 b) (b1 b)
    · simp only [List.mem_cons] at hM
      simp only [List.flatMap_cons, List.mem_append]
      rcases hM with rfl | hM
      · exact .inl (a2 b hb)
      · exact .inr (b2 M hM b hb)
end

end Lin
end Rasso
