import Coddstheorem.AlgebraToCalculus
import Coddstheorem.Encode

/-!
# Codd's theorem for Rasso: from the calculus to the algebra (theorem B)

In plain words: each calculus query `q` is translated into an algebra query `q.toRA`
(Codd 1972; Abiteboul, Hull and Vianu 1995, Lemma 5.3.12, whose sketch gives the active
domain and the cases for atoms, `=`, `∨` and `¬` as below). The
translation computes the active domain itself: a union of every stored column, renamed
to one attribute, and of the query's constants. Each subformula `φ` becomes an
expression whose attributes are `φ`'s free variables, encoded as Rasso names (`enc`),
holding the assignments from the active domain that make `φ` true:

* an atom selects, projects and renames its stored relation;
* `x = y` is σ on two copies of the active domain; `x = c` is the constant `c`;
* `¬` is "the active domain to the power of the variables, minus"; `∧` is ⋈; `∨` is ∪
  after padding both sides to the same variables; `∃` is π; `∀` is `¬ ∃ ¬`.

The ESO capture (`Rasso.ESO.compile`) is the precedent; here the names are the
database's, the domain is the schema's `D`, and there are constants.

`calculus_to_algebra` proves that `q.toRA` is well typed (so theorem A applies to it)
and that Rasso's evaluator runs it on any database of the schema, without refusing,
giving exactly the active-domain answers of `q`.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Coddstheorem

open Rasso Formula

/-! ## The translation -/

/-- The free variables, each once, in order of first occurrence. -/
def V (φ : Formula) : List String := φ.fv.eraseDups

/-- `ys` without the members of `xs`. -/
def diffL (ys xs : List String) : List String := ys.filter fun y => !xs.contains y

/-- Column `b` of stored relation `n`, renamed to `a`. -/
def colE (a n b : String) : CRA := .ren [(b, a)] (.proj [b] (.rel n))

/-- The active domain, as a relation with the one attribute `a`: every stored column and
the constants `C`. It starts from two constant relations so that it is a union even for
an empty schema. -/
def adE (S : Schema) (C : List Value) (a : String) : CRA :=
  (S.flatMap fun p => p.2.map fun b => colE a p.1 b).foldl .union
    (.union (.lit [a] []) (.lit [a] (C.map ([·]))))

/-- The active domain to the power of the variables `xs` (encoded). -/
def adV (S : Schema) (C : List Value) : List String → CRA
  | [] => .lit [] [[]]
  | x :: xs => .prod (adE S C (enc x)) (adV S C xs)

/-- `e` with the variables `ys` added, ranging over the active domain. -/
def pad (S : Schema) (C : List Value) (e : CRA) (ys : List String) : CRA := .prod e (adV S C ys)

/-- The first attribute of an atom whose variable is `x`. -/
def firstAttr (as xs : List String) (x : String) : String := ((xs.zip as).lookup x).getD ""

/-- An atom `n(xs)`: σ makes the attributes of a repeated variable equal, π keeps the
first attribute of each variable, ρ names it after the variable. -/
def atomE (S : Schema) (n : String) (xs : List String) : CRA :=
  let as := S.attrsOf n
  let fa := firstAttr as xs
  let tests := (as.zip xs).map fun p => Test.eqA p.1 (fa p.2)
  .ren (xs.eraseDups.map fun x => (fa x, enc x))
    (.proj (xs.eraseDups.map fa) (tests.foldr .sel (.rel n)))

/-- The variables `∃ x` or `∀ x` adds when `x` is not free in its body (none otherwise). -/
def extra (x : String) (φ : Formula) : List String := if x ∈ V φ then [] else [x]

/-- The algebra expression of a formula, over the constants `C`. -/
def ra (S : Schema) (C : List Value) : Formula → CRA
  | .rel n xs => atomE S n xs
  | .eqv x y =>
    if x = y then adE S C (enc x)
    else .sel (.eqA (enc x) (enc y)) (.prod (adE S C (enc x)) (adE S C (enc y)))
  | .eqc x c => .lit [enc x] [[c]]
  | .cmpv o x y =>
    if x = y then .sel (.cmpA o (enc x) (enc x)) (adE S C (enc x))
    else .sel (.cmpA o (enc x) (enc y)) (.prod (adE S C (enc x)) (adE S C (enc y)))
  | .cmpc o x c => .sel (.cmpC o (enc x) c) (adE S C (enc x))
  | .not φ => .diff (adV S C (V φ)) (ra S C φ)
  | .and φ ψ => .join (ra S C φ) (ra S C ψ)
  | .or φ ψ =>
    .union (pad S C (ra S C φ) (diffL (V ψ) (V φ))) (pad S C (ra S C ψ) (diffL (V φ) (V ψ)))
  | .ex x φ => .proj ((V (.ex x φ)).map enc) (pad S C (ra S C φ) (extra x φ))
  | .all x φ =>
    .diff (adV S C (V (.all x φ)))
      (.proj ((V (.all x φ)).map enc)
        (.diff (adV S C (V φ ++ extra x φ)) (pad S C (ra S C φ) (extra x φ))))

/-- Adds, for the `i`-th output pair `(a, x)`, a column `cpy i` equal to `x`'s. -/
def copies (S : Schema) (C : List Value) : Nat → List (String × String) → CRA → CRA
  | _, [], e => e
  | i, (_, x) :: ps, e => copies S C (i + 1) ps (.sel (.eqA (cpy i) (enc x)) (.prod e (adE S C (cpy i))))

/-- The copies' names, from `cpy i` on, each with the output attribute it becomes. -/
def cpyL : Nat → List (String × String) → List (String × String)
  | _, [] => []
  | i, (a, _) :: ps => (cpy i, a) :: cpyL (i + 1) ps

/-- The copies' names, from `cpy i` on, each with the variable it copies. -/
def cpyX : Nat → List (String × String) → List (String × String)
  | _, [] => []
  | i, (_, x) :: ps => (cpy i, x) :: cpyX (i + 1) ps

/-- The algebra query of a calculus query. -/
def Query.toRA (S : Schema) (q : Query) : CRA :=
  let C := q.body.consts
  .ren (cpyL 0 q.out)
    (.proj ((cpyL 0 q.out).map (·.1))
      (copies S C 0 q.out (pad S C (ra S C q.body) (diffL q.vars.eraseDups (V q.body)))))

/-! ## Lists of variables -/

theorem mem_V {φ : Formula} {x : String} : x ∈ V φ ↔ x ∈ φ.fv := List.mem_eraseDups

theorem nodup_eraseDups : ∀ l : List String, l.eraseDups.Nodup
  | [] => List.nodup_nil
  | a :: as => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨fun h => ?_, nodup_eraseDups _⟩
    rw [List.mem_eraseDups, List.mem_filter] at h
    simp at h
termination_by l => l.length
decreasing_by simp_wf; exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem nodup_V (φ : Formula) : (V φ).Nodup := nodup_eraseDups _

theorem mem_diffL {ys xs : List String} {y : String} : y ∈ diffL ys xs ↔ y ∈ ys ∧ y ∉ xs := by
  simp [diffL, List.contains_iff_mem]

theorem nodup_diffL {ys xs : List String} (h : ys.Nodup) : (diffL ys xs).Nodup := h.filter _

theorem nodup_map_enc {xs : List String} (h : xs.Nodup) : (xs.map enc).Nodup :=
  nodup_map_of_inj h fun _ _ _ _ e => enc_inj e

theorem mem_map_enc {xs : List String} {x : String} : enc x ∈ xs.map enc ↔ x ∈ xs := by
  constructor
  · intro h; obtain ⟨y, hy, e⟩ := List.mem_map.mp h; rw [← enc_inj e]; exact hy
  · exact List.mem_map_of_mem

theorem mem_extra {x y : String} {φ : Formula} : y ∈ extra x φ ↔ y = x ∧ x ∉ V φ := by
  unfold extra; split <;> simp_all

/-! ## The translation is well typed -/

section Check
variable {S : Schema} {D : Domain} {C : List Value}

theorem schema_lookup (hS : S.WF) {p : String × List String} (hp : p ∈ S) :
    S.lookup p.1 = some p.2 := by
  have hn := hS.1
  induction S with
  | nil => cases hp
  | cons q S ih =>
    obtain ⟨k, v⟩ := q
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp [List.lookup]
    · have hne : (p.1 == k) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro e
        exact (List.nodup_cons.mp hn).1 (e ▸ List.mem_map_of_mem (f := (·.1)) hp')
      simp only [List.lookup, hne]
      exact ih ⟨(List.nodup_cons.mp hn).2, fun r hr => hS.2 r (List.mem_cons_of_mem _ hr)⟩ hp'
        (List.nodup_cons.mp hn).2

theorem check_lit1 {a : String} (ha : isAttribute a = true) {rows : List (List Value)}
    (hr : ∀ row ∈ rows, row.length = 1 ∧ ∀ v ∈ row, D.mem v = true) :
    (CRA.lit [a] rows).check S D = some [a] := by
  simp only [CRA.check]
  rw [if_pos]
  refine ⟨by simp, by simp [ha], ?_, ?_⟩
  · exact List.all_eq_true.mpr fun row h => by simp [(hr row h).1]
  · exact List.all_eq_true.mpr fun row h => List.all_eq_true.mpr (hr row h).2

theorem check_union_same {e f : CRA} {as : List String} (he : e.check S D = some as)
    (hf : f.check S D = some as) : (CRA.union e f).check S D = some as := by
  simp [CRA.check, he, hf, List.all_eq_true, List.contains_iff_mem]

theorem check_colE (hS : S.WF) {a : String} (ha : isAttribute a = true)
    {p : String × List String} (hp : p ∈ S) {b : String} (hb : b ∈ p.2) :
    (colE a p.1 b).check S D = some [a] := by
  simp only [colE, CRA.check, schema_lookup hS hp, bind, Option.bind_some]
  rw [if_pos ⟨by simp, by simp [List.contains_iff_mem, hb]⟩]
  simp only [Option.bind_some]
  rw [if_pos]
  · simp [CRA.renamed]
  · simp [CRA.renamed, ha]

theorem check_adE (hS : S.WF) {a : String} (ha : isAttribute a = true)
    (hC : ∀ c ∈ C, D.mem c = true) : (adE S C a).check S D = some [a] := by
  unfold adE
  have h0 : (CRA.union (.lit [a] []) (.lit [a] (C.map ([·])))).check S D = some [a] :=
    check_union_same (check_lit1 ha (by simp)) (check_lit1 ha (by
      intro row hrow
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrow
      simp [hC c hc]))
  have hcol : ∀ e ∈ S.flatMap (fun p => p.2.map fun b => colE a p.1 b), e.check S D = some [a] := by
    intro e he
    simp only [List.mem_flatMap, List.mem_map] at he
    obtain ⟨p, hp, b, hb, rfl⟩ := he
    exact check_colE hS ha hp hb
  generalize S.flatMap (fun p => p.2.map fun b => colE a p.1 b) = l at hcol
  generalize CRA.union (.lit [a] []) (.lit [a] (C.map ([·]))) = acc at h0
  induction l generalizing acc with
  | nil => exact h0
  | cons e l ih =>
    simp only [List.foldl_cons]
    exact ih (fun e' h => hcol e' (List.mem_cons_of_mem _ h)) _
      (check_union_same h0 (hcol e List.mem_cons_self))

theorem check_adV (hS : S.WF) (hC : ∀ c ∈ C, D.mem c = true) :
    ∀ {xs : List String}, xs.Nodup → (adV S C xs).check S D = some (xs.map enc)
  | [], _ => by
    simp only [adV, CRA.check]; rw [if_pos (by simp)]; rfl
  | x :: xs, hn => by
    have ih := check_adV hS hC (List.nodup_cons.mp hn).2
    simp only [adV, CRA.check, check_adE hS (isAttribute_enc x) hC, ih, bind, Option.bind_some]
    rw [if_pos]
    · rfl
    · simp only [List.all_eq_true, Bool.not_eq_true']
      intro b hb
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_eq_false_iff_ne, ne_eq]
      intro e
      rw [e] at hb
      exact (List.nodup_cons.mp hn).1 (mem_map_enc.mp hb)

theorem check_prod {e f : CRA} {as bs : List String} (he : e.check S D = some as)
    (hf : f.check S D = some bs) (hd : ∀ b ∈ bs, b ∉ as) :
    (CRA.prod e f).check S D = some (as ++ bs) := by
  simp only [CRA.check, he, hf, bind, Option.bind_some]
  rw [if_pos]
  exact List.all_eq_true.mpr fun b hb => by simp [List.contains_iff_mem, hd b hb]

theorem check_join {e f : CRA} {as bs : List String} (he : e.check S D = some as)
    (hf : f.check S D = some bs) :
    (CRA.join e f).check S D = some (as ++ bs.filter fun b => !as.contains b) := by
  simp [CRA.check, he, hf]

theorem check_same {e f : CRA} {as bs : List String} (he : e.check S D = some as)
    (hf : f.check S D = some bs) (hs : ∀ a, a ∈ as ↔ a ∈ bs) :
    (CRA.union e f).check S D = some as ∧ (CRA.diff e f).check S D = some as := by
  have : as.all bs.contains = true ∧ bs.all as.contains = true :=
    ⟨List.all_eq_true.mpr fun a ha => List.contains_iff_mem.mpr ((hs a).mp ha),
     List.all_eq_true.mpr fun a ha => List.contains_iff_mem.mpr ((hs a).mpr ha)⟩
  simp only [CRA.check, he, hf, bind, Option.bind_some]
  exact ⟨if_pos this, if_pos this⟩

theorem check_proj {e : CRA} {as bs : List String} (he : e.check S D = some as)
    (hn : bs.Nodup) (hs : ∀ b ∈ bs, b ∈ as) : (CRA.proj bs e).check S D = some bs := by
  simp only [CRA.check, he, bind, Option.bind_some]
  exact if_pos ⟨hn, List.all_eq_true.mpr fun b hb => List.contains_iff_mem.mpr (hs b hb)⟩

theorem check_selA {e : CRA} {as : List String} (he : e.check S D = some as) {a b : String}
    (ha : a ∈ as) (hb : b ∈ as) : (CRA.sel (.eqA a b) e).check S D = some as := by
  simp only [CRA.check, he, bind, Option.bind_some]
  rw [if_pos]
  simp [Test.attrs, Test.consts, List.contains_iff_mem, ha, hb]

theorem check_selCmpA {e : CRA} {as : List String} (he : e.check S D = some as) (o : Cmp)
    {a b : String} (ha : a ∈ as) (hb : b ∈ as) : (CRA.sel (.cmpA o a b) e).check S D = some as := by
  simp only [CRA.check, he, bind, Option.bind_some]
  rw [if_pos]
  simp [Test.attrs, Test.consts, List.contains_iff_mem, ha, hb]

theorem check_selCmpC {e : CRA} {as : List String} (he : e.check S D = some as) (o : Cmp)
    {a : String} {c : Value} (ha : a ∈ as) (hc : D.mem c = true) :
    (CRA.sel (.cmpC o a c) e).check S D = some as := by
  simp only [CRA.check, he, bind, Option.bind_some]
  rw [if_pos]
  simp [Test.attrs, Test.consts, List.contains_iff_mem, ha, hc]

/-- The attributes of `ra φ`: the free variables, encoded, in some order, each once. -/
def ChecksTo (S : Schema) (D : Domain) (e : CRA) (φ : Formula) : Prop :=
  ∃ W : List String, e.check S D = some (W.map enc) ∧ W.Nodup ∧ ∀ x, x ∈ W ↔ x ∈ φ.fv

theorem enc_filter (as bs : List String) :
    (bs.map enc).filter (fun b => !(as.map enc).contains b) = (bs.filter fun b => !as.contains b).map enc := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro b _
  simp only [Function.comp_def]
  congr 1
  cases h : as.contains b
  · apply Bool.eq_false_iff.mpr
    intro h'
    exact Bool.false_ne_true (h ▸ List.contains_iff_mem.mpr (mem_map_enc.mp (List.contains_iff_mem.mp h')))
  · exact List.contains_iff_mem.mpr (List.mem_map_of_mem (List.contains_iff_mem.mp h))

theorem nodup_append_of {as bs : List String} (ha : as.Nodup) (hb : bs.Nodup)
    (hd : ∀ b ∈ bs, b ∉ as) : (as ++ bs).Nodup :=
  List.nodup_append.mpr ⟨ha, hb, fun _ h1 b h2 e => hd b h2 (e ▸ h1)⟩

theorem checksTo_pad (hS : S.WF) (hC : ∀ c ∈ C, D.mem c = true) {e : CRA} {W ys : List String}
    (he : e.check S D = some (W.map enc)) (hW : W.Nodup) (hy : ys.Nodup) (hd : ∀ y ∈ ys, y ∉ W) :
    (pad S C e ys).check S D = some ((W ++ ys).map enc) ∧ (W ++ ys).Nodup := by
  refine ⟨?_, nodup_append_of hW hy hd⟩
  rw [List.map_append]
  exact check_prod he (check_adV hS hC hy) fun b hb hbW => by
    obtain ⟨y, hy', rfl⟩ := List.mem_map.mp hb
    exact hd y hy' (mem_map_enc.mp hbW)

theorem check_ren {e : CRA} {as : List String} (he : e.check S D = some as)
    {r : List (String × String)}
    (h : (r.map (·.1)).Nodup ∧ (r.map (·.1)).all as.contains = true ∧
      (r.map (·.2)).all isAttribute = true ∧ (CRA.renamed r as).Nodup) :
    (CRA.ren r e).check S D = some (CRA.renamed r as) := by
  simp only [CRA.check, he, bind, Option.bind_some]
  exact if_pos h

/-! ### Atoms -/

theorem lookup_zip_isSome : ∀ {xs as : List String}, xs.length ≤ as.length → ∀ {x}, x ∈ xs →
    ∃ a, (xs.zip as).lookup x = some a
  | [], _, _, _, h => by cases h
  | _ :: _, [], hl, _, _ => by simp at hl
  | y :: xs, b :: as, hl, x, hx => by
    simp only [List.zip_cons_cons, List.lookup_cons]
    by_cases e : x = y
    · subst e; exact ⟨b, by simp⟩
    · have : (x == y) = false := by simp [e]
      rw [this]
      exact lookup_zip_isSome (by simp at hl; omega) (by simpa [e] using hx)

theorem zip_inj_snd : ∀ {xs as : List String}, as.Nodup → ∀ {x y a : String},
    (x, a) ∈ xs.zip as → (y, a) ∈ xs.zip as → x = y
  | [], _, _, _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, _, h, _ => by cases h
  | z :: xs, b :: as, hn, x, y, a, hx, hy => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hx hy
    have hn' := List.nodup_cons.mp hn
    rcases hx with ⟨rfl, rfl⟩ | hx <;> rcases hy with ⟨rfl, e⟩ | hy
    · rfl
    · exact absurd (List.of_mem_zip hy).2 hn'.1
    · exact absurd (e ▸ (List.of_mem_zip hx).2) hn'.1
    · exact zip_inj_snd hn'.2 hx hy

theorem firstAttr_mem {as xs : List String} (hl : xs.length = as.length) {x : String}
    (hx : x ∈ xs) : (x, firstAttr as xs x) ∈ xs.zip as := by
  obtain ⟨a, ha⟩ := lookup_zip_isSome (Nat.le_of_eq hl) hx
  simp only [firstAttr, ha, Option.getD_some]
  exact lookup_mem ha

theorem firstAttr_inj {as xs : List String} (hl : xs.length = as.length) (hn : as.Nodup)
    {x y : String} (hx : x ∈ xs) (hy : y ∈ xs) (e : firstAttr as xs x = firstAttr as xs y) :
    x = y :=
  zip_inj_snd hn (firstAttr_mem hl hx) (e ▸ firstAttr_mem hl hy)

theorem lookup_map_inj {f g : String → String} {x : String} :
    ∀ {vs : List String}, x ∈ vs → (∀ y ∈ vs, f y = f x → y = x) →
      (vs.map fun y => (f y, g y)).lookup (f x) = some (g x)
  | [], h, _ => by cases h
  | y :: vs, hx, hi => by
    simp only [List.map_cons, List.lookup_cons]
    by_cases e : f x = f y
    · have : y = x := hi y List.mem_cons_self e.symm
      subst this; simp
    · have : (f x == f y) = false := by simp [e]
      rw [this]
      have hx' : x ∈ vs := by
        rcases List.mem_cons.mp hx with rfl | h
        · exact absurd rfl e
        · exact h
      exact lookup_map_inj hx' fun z hz => hi z (List.mem_cons_of_mem _ hz)

theorem check_sels {e : CRA} {as : List String} (he : e.check S D = some as) :
    ∀ {ps : List (String × String)}, (∀ p ∈ ps, p.1 ∈ as ∧ p.2 ∈ as) →
      ((ps.map fun p => Test.eqA p.1 p.2).foldr .sel e).check S D = some as
  | [], _ => he
  | p :: ps, h => by
    simp only [List.map_cons, List.foldr_cons]
    exact check_selA (check_sels he fun q hq => h q (List.mem_cons_of_mem _ hq))
      (h p List.mem_cons_self).1 (h p List.mem_cons_self).2

/-- The attributes of the atom's relation, and the facts about them the proofs use. -/
theorem atom_attrs (hS : S.WF) {n : String} {xs : List String}
    (hwt : (Formula.rel n xs).WT S = true) :
    ∃ as, S.lookup n = some as ∧ S.attrsOf n = as ∧ as.Nodup ∧ xs.length = as.length := by
  simp only [Formula.WT, Bool.and_eq_true, beq_iff_eq] at hwt
  obtain ⟨as, has⟩ := Option.isSome_iff_exists.mp hwt.1
  have hat : S.attrsOf n = as := by simp [Schema.attrsOf, has]
  exact ⟨as, has, hat, (hS.2 _ (lookup_mem has)).1, hat ▸ hwt.2⟩

theorem checksTo_atom (hS : S.WF) {n : String} {xs : List String}
    (hwt : (Formula.rel n xs).WT S = true) : ChecksTo S D (atomE S n xs) (.rel n xs) := by
  obtain ⟨as, has, hat, hn, hl⟩ := atom_attrs hS hwt
  have hsel : (((as.zip xs).map fun p => Test.eqA p.1 (firstAttr as xs p.2)).foldr .sel
      (CRA.rel n)).check S D = some as := by
    have := check_sels (S := S) (D := D) (e := .rel n) (as := as) (by simp [CRA.check, has])
      (ps := (as.zip xs).map fun p => (p.1, firstAttr as xs p.2)) (by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact ⟨(List.of_mem_zip hq).1,
          (List.of_mem_zip (firstAttr_mem hl (List.of_mem_zip hq).2)).2⟩)
    simpa [List.map_map, Function.comp_def] using this
  have hvs := nodup_eraseDups xs
  have hmem : ∀ x ∈ xs.eraseDups, x ∈ xs := fun x h => List.mem_eraseDups.mp h
  have hinj : ∀ x ∈ xs.eraseDups, ∀ y ∈ xs.eraseDups,
      firstAttr as xs y = firstAttr as xs x → y = x := fun x hx y hy e =>
    firstAttr_inj hl hn (hmem y hy) (hmem x hx) e
  have hfa : (xs.eraseDups.map (firstAttr as xs)).Nodup :=
    nodup_map_of_inj hvs fun x hx y hy e => hinj y hy x hx e
  have hproj := check_proj (S := S) (D := D) hsel hfa (fun b hb => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact (List.of_mem_zip (firstAttr_mem hl (hmem x hx))).2)
  have hren : CRA.renamed (xs.eraseDups.map fun x => (firstAttr as xs x, enc x))
      (xs.eraseDups.map (firstAttr as xs)) = xs.eraseDups.map enc := by
    simp only [CRA.renamed, List.map_map]
    apply List.map_congr_left
    intro x hx
    simp only [Function.comp_def]
    rw [lookup_map_inj hx (hinj x hx)]; rfl
  refine ⟨xs.eraseDups, ?_, hvs, fun x => ?_⟩
  · simp only [atomE, hat]
    rw [← hren]
    apply check_ren hproj
    refine ⟨by simpa [List.map_map, Function.comp_def] using hfa, ?_, ?_, ?_⟩
    · exact List.all_eq_true.mpr fun b hb => by
        simp only [List.map_map, Function.comp_def] at hb
        exact List.contains_iff_mem.mpr hb
    · exact List.all_eq_true.mpr fun b hb => by
        simp only [List.map_map, Function.comp_def, List.mem_map] at hb
        obtain ⟨x, _, rfl⟩ := hb
        exact isAttribute_enc x
    · rw [hren]; exact nodup_map_enc hvs
  · simp [Formula.fv, List.mem_eraseDups]

/-! ### Every formula -/

theorem checksTo_ra (hS : S.WF) (hC : ∀ c ∈ C, D.mem c = true) :
    (φ : Formula) → φ.WT S = true → (∀ c ∈ φ.consts, c ∈ C) → ChecksTo S D (ra S C φ) φ
  | .rel n xs, hwt, _ => checksTo_atom hS hwt
  | .eqv x y, _, _ => by
    by_cases e : x = y
    · subst e
      refine ⟨[x], by simp only [ra, if_pos rfl]; exact check_adE hS (isAttribute_enc x) hC,
        by simp, fun z => by simp [Formula.fv]⟩
    · have hp := check_prod (S := S) (D := D) (check_adE hS (isAttribute_enc x) hC)
        (check_adE hS (isAttribute_enc y) hC) (by
          intro b hb hb'; simp only [List.mem_singleton] at hb hb'
          exact e (enc_inj (hb'.symm.trans hb)))
      refine ⟨[x, y], ?_, by simp [e], fun z => by simp [Formula.fv]⟩
      simp only [ra, if_neg e]
      exact check_selA hp (by simp) (by simp)
  | .eqc x c, _, hc => by
    refine ⟨[x], ?_, by simp, fun z => by simp [Formula.fv]⟩
    simp only [ra]
    exact check_lit1 (isAttribute_enc x) (by
      intro row hrow; simp only [List.mem_singleton] at hrow; subst hrow
      simp [hC c (hc c (by simp [Formula.consts]))])
  | .cmpv o x y, _, _ => by
    by_cases e : x = y
    · subst e
      refine ⟨[x], ?_, by simp, fun z => by simp [Formula.fv]⟩
      simp only [ra, if_pos rfl]
      exact check_selCmpA (check_adE hS (isAttribute_enc x) hC) o (by simp) (by simp)
    · have hp := check_prod (S := S) (D := D) (check_adE hS (isAttribute_enc x) hC)
        (check_adE hS (isAttribute_enc y) hC) (by
          intro b hb hb'; simp only [List.mem_singleton] at hb hb'
          exact e (enc_inj (hb'.symm.trans hb)))
      refine ⟨[x, y], ?_, by simp [e], fun z => by simp [Formula.fv]⟩
      simp only [ra, if_neg e]
      exact check_selCmpA hp o (by simp) (by simp)
  | .cmpc o x c, _, hc => by
    refine ⟨[x], ?_, by simp, fun z => by simp [Formula.fv]⟩
    simp only [ra]
    exact check_selCmpC (check_adE hS (isAttribute_enc x) hC) o (by simp)
      (hC c (hc c (by simp [Formula.consts])))
  | .not φ, hwt, hc => by
    obtain ⟨W, hW, hn, hs⟩ := checksTo_ra hS hC φ hwt hc
    refine ⟨V φ, ?_, nodup_V φ, fun x => by simp [Formula.fv, mem_V]⟩
    exact (check_same (check_adV hS hC (nodup_V φ)) hW fun a => by
      constructor
      · intro h; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
        exact List.mem_map_of_mem ((hs x).mpr (mem_V.mp hx))
      · intro h; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
        exact List.mem_map_of_mem (mem_V.mpr ((hs x).mp hx))).2
  | .and φ ψ, hwt, hc => by
    simp only [Formula.WT, Bool.and_eq_true] at hwt
    obtain ⟨W, hW, hn, hs⟩ := checksTo_ra hS hC φ hwt.1 fun c h => hc c (by simp [Formula.consts, h])
    obtain ⟨W', hW', hn', hs'⟩ := checksTo_ra hS hC ψ hwt.2 fun c h => hc c (by simp [Formula.consts, h])
    refine ⟨W ++ W'.filter fun b => !W.contains b, ?_, ?_, fun x => ?_⟩
    · simp only [ra]
      rw [List.map_append, ← enc_filter]
      exact check_join hW hW'
    · exact nodup_append_of hn (hn'.filter _) fun b hb hbW => by
        simp [List.mem_filter, List.contains_iff_mem, hbW] at hb
    · simp only [List.mem_append, List.mem_filter, hs, hs', Formula.fv, List.contains_iff_mem]
      by_cases h : x ∈ φ.fv <;> simp [h, hs]
  | .or φ ψ, hwt, hc => by
    simp only [Formula.WT, Bool.and_eq_true] at hwt
    obtain ⟨W, hW, hn, hs⟩ := checksTo_ra hS hC φ hwt.1 fun c h => hc c (by simp [Formula.consts, h])
    obtain ⟨W', hW', hn', hs'⟩ := checksTo_ra hS hC ψ hwt.2 fun c h => hc c (by simp [Formula.consts, h])
    obtain ⟨h1, hn1⟩ := checksTo_pad hS hC hW hn (nodup_diffL (nodup_V ψ)) (ys := diffL (V ψ) (V φ))
      fun y hy hyW => (mem_diffL.mp hy).2 (mem_V.mpr ((hs y).mp hyW))
    obtain ⟨h2, hn2⟩ := checksTo_pad hS hC hW' hn' (nodup_diffL (nodup_V φ)) (ys := diffL (V φ) (V ψ))
      fun y hy hyW => (mem_diffL.mp hy).2 (mem_V.mpr ((hs' y).mp hyW))
    have hset : ∀ x, x ∈ W ++ diffL (V ψ) (V φ) ↔ x ∈ φ.fv ∨ x ∈ ψ.fv := fun x => by
      simp only [List.mem_append, mem_diffL, mem_V, hs]; by_cases h : x ∈ φ.fv <;> simp [h]
    have hset' : ∀ x, x ∈ W' ++ diffL (V φ) (V ψ) ↔ x ∈ φ.fv ∨ x ∈ ψ.fv := fun x => by
      simp only [List.mem_append, mem_diffL, mem_V, hs']; by_cases h : x ∈ ψ.fv <;> simp [h]
    refine ⟨W ++ diffL (V ψ) (V φ), ?_, hn1, fun x => by simp only [Formula.fv, List.mem_append, hset]⟩
    simp only [ra]
    exact (check_same h1 h2 fun a => by
      constructor
      · intro h; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
        exact List.mem_map_of_mem ((hset' x).mpr ((hset x).mp hx))
      · intro h; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
        exact List.mem_map_of_mem ((hset x).mpr ((hset' x).mp hx))).1
  | .ex x φ, hwt, hc => by
    obtain ⟨W, hW, hn, hs⟩ := checksTo_ra hS hC φ hwt hc
    obtain ⟨h1, _⟩ := checksTo_pad hS hC hW hn (ys := extra x φ) (by unfold extra; split <;> simp)
      fun y hy hyW => (mem_extra.mp hy).2 (by rw [(mem_extra.mp hy).1] at hyW; exact mem_V.mpr ((hs x).mp hyW))
    refine ⟨V (.ex x φ), ?_, nodup_V _, fun y => mem_V⟩
    simp only [ra]
    refine check_proj h1 (nodup_map_enc (nodup_V _)) fun b hb => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    simp only [mem_V, Formula.fv, List.mem_filter, bne_iff_ne, ne_eq] at hy
    exact List.mem_map_of_mem (List.mem_append_left _ ((hs y).mpr hy.1))
  | .all x φ, hwt, hc => by
    obtain ⟨W, hW, hn, hs⟩ := checksTo_ra hS hC φ hwt hc
    have hex : (extra x φ).Nodup := by unfold extra; split <;> simp
    have hdx : ∀ y ∈ extra x φ, y ∉ W := fun y hy hyW =>
      (mem_extra.mp hy).2 (by rw [(mem_extra.mp hy).1] at hyW; exact mem_V.mpr ((hs x).mp hyW))
    obtain ⟨h1, _⟩ := checksTo_pad hS hC hW hn hex hdx
    have hn2 : (V φ ++ extra x φ).Nodup := nodup_append_of (nodup_V φ) hex fun y hy hyV =>
      (mem_extra.mp hy).2 ((mem_extra.mp hy).1 ▸ hyV)
    have hd := (check_same (check_adV hS hC hn2) h1 fun a => by
      constructor
      · intro h; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
        refine List.mem_map_of_mem ?_
        rcases List.mem_append.mp hy with hy | hy
        · exact List.mem_append_left _ ((hs y).mpr (mem_V.mp hy))
        · exact List.mem_append_right _ hy
      · intro h; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
        refine List.mem_map_of_mem ?_
        rcases List.mem_append.mp hy with hy | hy
        · exact List.mem_append_left _ (mem_V.mpr ((hs y).mp hy))
        · exact List.mem_append_right _ hy).2
    have hp := check_proj (bs := (V (.all x φ)).map enc) hd (nodup_map_enc (nodup_V _)) fun b hb => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      simp only [mem_V, Formula.fv, List.mem_filter, bne_iff_ne, ne_eq] at hy
      exact List.mem_map_of_mem (List.mem_append_left _ (mem_V.mpr hy.1))
    refine ⟨V (.all x φ), ?_, nodup_V _, fun y => mem_V⟩
    simp only [ra]
    exact (check_same (check_adV hS hC (nodup_V _)) hp fun _ => Iff.rfl).2

/-! ### The output heading -/

theorem lookup_of_mem' {β : Type} {a : String} {v : β} : ∀ {l : List (String × β)},
    (l.map (·.1)).Nodup → (a, v) ∈ l → l.lookup a = some v
  | [], _, h => by cases h
  | (b, w) :: l, hn, h => by
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_cons.mp h with e | e
    · cases e; simp
    · have hab : a ≠ b := fun e' => hn'.1 (e' ▸ List.mem_map_of_mem (f := (·.1)) e)
      have : (a == b) = false := by simp [hab]
      simp only [List.lookup_cons, this]
      exact lookup_of_mem' hn'.2 e

theorem renamed_self {l : List (String × String)} (hn : (l.map (·.1)).Nodup) :
    CRA.renamed l (l.map (·.1)) = l.map (·.2) := by
  simp only [CRA.renamed, List.map_map]
  apply List.map_congr_left
  intro p hp
  simp [lookup_of_mem' hn hp]

theorem mem_cpyL_fst : ∀ {i : Nat} {ps : List (String × String)} {c : String},
    c ∈ (cpyL i ps).map (·.1) → ∃ j, i ≤ j ∧ c = cpy j
  | _, [], _, h => by cases h
  | i, (a, x) :: ps, c, h => by
    simp only [cpyL, List.map_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨i, Nat.le_refl _, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := mem_cpyL_fst h
      exact ⟨j, by omega, rfl⟩

theorem nodup_cpyL : ∀ {i : Nat} {ps : List (String × String)}, ((cpyL i ps).map (·.1)).Nodup
  | _, [] => List.nodup_nil
  | i, (a, x) :: ps => by
    simp only [cpyL, List.map_cons]
    refine List.nodup_cons.mpr ⟨fun h => ?_, nodup_cpyL⟩
    obtain ⟨j, hj, e⟩ := mem_cpyL_fst h
    have := cpy_inj e; omega

theorem cpyL_snd : ∀ {i : Nat} {ps : List (String × String)}, (cpyL i ps).map (·.2) = ps.map (·.1)
  | _, [] => rfl
  | i, (a, x) :: ps => by simp only [cpyL, List.map_cons, cpyL_snd]

theorem check_copies (hS : S.WF) (hC : ∀ c ∈ C, D.mem c = true) :
    ∀ {i : Nat} {ps : List (String × String)} {e : CRA} {as : List String},
      e.check S D = some as → (∀ p ∈ ps, enc p.2 ∈ as) → (∀ j, i ≤ j → cpy j ∉ as) →
      (copies S C i ps e).check S D = some (as ++ (cpyL i ps).map (·.1))
  | _, [], e, as, he, _, _ => by simp [copies, cpyL, he]
  | i, (a, x) :: ps, e, as, he, hx, hc => by
    simp only [copies, cpyL, List.map_cons]
    have hp := check_prod he (check_adE (C := C) hS (isAttribute_cpy i) hC) (by
      intro b hb; simp only [List.mem_singleton] at hb; subst hb; exact hc i (Nat.le_refl _))
    have hs := check_selA hp (List.mem_append_right _ (List.mem_singleton_self _))
      (List.mem_append_left _ (hx (a, x) List.mem_cons_self))
    have := check_copies hS hC (i := i + 1) hs (fun p hp => List.mem_append_left _ (hx p (List.mem_cons_of_mem _ hp)))
      (fun j hj h => by
        rcases List.mem_append.mp h with h | h
        · exact hc j (by omega) h
        · simp only [List.mem_singleton] at h; have := cpy_inj h; omega)
    simpa using this

/-- `q.toRA` is well typed, with the output heading's attributes. -/
theorem check_toRA (hS : S.WF) {q : Query} (hq : q.WT S D) :
    (q.toRA S).check S D = some (q.out.map (·.1)) := by
  obtain ⟨hwt, hcD, hon, hoa, hfv⟩ := hq
  have hC : ∀ c ∈ q.body.consts, D.mem c = true := hcD
  obtain ⟨W, hW, hn, hs⟩ := checksTo_ra hS hC q.body hwt fun c h => h
  have hy := nodup_diffL (xs := V q.body) (nodup_eraseDups q.vars)
  obtain ⟨hpad, _⟩ := checksTo_pad hS hC hW hn hy fun y hy hyW =>
    (mem_diffL.mp hy).2 (mem_V.mpr ((hs y).mp hyW))
  have hcop := check_copies hS hC (i := 0) (ps := q.out) hpad (fun p hp => by
      refine List.mem_map_of_mem ?_
      by_cases h : p.2 ∈ W
      · exact List.mem_append_left _ h
      · refine List.mem_append_right _ (mem_diffL.mpr ⟨List.mem_eraseDups.mpr ?_, fun h' => h ?_⟩)
        · exact List.mem_map_of_mem hp
        · exact (hs _).mpr (mem_V.mp h'))
    (fun j _ h => by obtain ⟨y, _, e⟩ := List.mem_map.mp h; exact enc_ne_cpy y j e)
  have hproj := check_proj hcop nodup_cpyL fun b hb => List.mem_append_right _ hb
  have := check_ren hproj (r := cpyL 0 q.out) ⟨nodup_cpyL, List.all_eq_true.mpr fun b hb =>
      List.contains_iff_mem.mpr hb, ?_, by rw [renamed_self nodup_cpyL, cpyL_snd]; exact hon⟩
  · rw [renamed_self nodup_cpyL, cpyL_snd] at this
    exact this
  · rw [cpyL_snd]
    exact List.all_eq_true.mpr fun b hb => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb; exact hoa p hp

end Check

/-! ## What the evaluator gives, operator by operator

`EvRep env D e as P`: Rasso's evaluator runs `e` without refusing, and gives a well-formed
relation with attributes `as` (each with domain `D`) holding exactly the tuples that fit
and satisfy `P`. -/

def EvRep (env : Env) (D : Domain) (e : CRA) (as : List String) (P : Tuple → Prop) : Prop :=
  ∃ r, Expr.eval env [] (e.toExpr D) = .ok (.finrel r) ∧ Rep (headerOf D as) P r

section EvRep
variable {env : Env} {D : Domain}

theorem EvRep.congr {e : CRA} {as : List String} {P Q : Tuple → Prop} (h : EvRep env D e as P)
    (hpq : ∀ t, t.Fits (headerOf D as) → (P t ↔ Q t)) : EvRep env D e as Q := by
  obtain ⟨r, hr, rr⟩ := h
  refine ⟨r, hr, rr.wf, rr.head, fun t => ?_⟩
  rw [rr.mem]
  exact ⟨fun ⟨f, h⟩ => ⟨f, (hpq t f).mp h⟩, fun ⟨f, h⟩ => ⟨f, (hpq t f).mpr h⟩⟩

theorem EvRep.congrH {e : CRA} {as bs : List String} {P : Tuple → Prop} (h : EvRep env D e as P)
    (hs : ∀ a, a ∈ as ↔ a ∈ bs) : EvRep env D e bs P := by
  obtain ⟨r, hr, rr⟩ := h
  exact ⟨r, hr, rep_congrH rr (headerOf_congr hs)⟩

theorem ev_rel {S : Schema} (henv : Conforms S D env) {n : String} {as : List String}
    (hp : (n, as) ∈ S) : ∃ r, env.lookup n = some (.finrel r) ∧
      EvRep env D (.rel n) as (· ∈ r.tuples) := by
  obtain ⟨r, hr, hw, hh⟩ := henv _ hp
  refine ⟨r, hr, r, by simp only [CRA.toExpr]; exact eval_name hr, hw, hh, fun t => ?_⟩
  exact ⟨fun ht => ⟨fits_of_mem hw hh ht, ht⟩, fun h => h.2⟩

theorem ev_lit {bs : List String} {rows : List (List Value)} (hn : bs.Nodup)
    (hrows : ∀ row ∈ rows, row.length = bs.length ∧ ∀ v ∈ row, D.mem v = true) :
    EvRep env D (.lit bs rows) bs (· ∈ litTuples bs rows) := by
  refine ⟨_, by simp only [CRA.toExpr]; exact eval_lit hrows,
    Finrel.wf_ofTuples (by have := attrs_headerOf D bs; simp only [headerOf] at this; rw [this]; exact hn) ?_,
    fun a => rfl, fun t => ?_⟩
  · intro t ht
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp ht
    exact fits_litTuple hn (hrows row hrow).1 (hrows row hrow).2
  · rw [Finrel.mem_ofTuples]
    refine ⟨fun ht => ⟨?_, ht⟩, fun h => h.2⟩
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp ht
    exact fits_litTuple hn (hrows row hrow).1 (hrows row hrow).2

theorem ev_join {e f : CRA} {as bs : List String} {P Q : Tuple → Prop}
    (he : EvRep env D e as P) (hf : EvRep env D f bs Q) :
    EvRep env D (.join e f) (as ++ bs.filter fun b => !as.contains b)
      (fun t => P (t.restrict as) ∧ Q (t.restrict bs)) ∧
    ((∀ b ∈ bs, b ∉ as) → EvRep env D (.prod e f) (as ++ bs.filter fun b => !as.contains b)
      (fun t => P (t.restrict as) ∧ Q (t.restrict bs))) := by
  obtain ⟨r1, hr1, i1⟩ := he
  obtain ⟨r2, hr2, i2⟩ := hf
  obtain ⟨q, hq, rq⟩ := rep_join i1 i2 (fun a d e h1 h2 => by
    rw [lookup_headerOf] at h1 h2
    split at h1 <;> split at h2 <;> simp_all)
  have hH : ∀ a, (joinH (headerOf D as) (headerOf D bs)).lookup a =
      (headerOf D (as ++ bs.filter fun b => !as.contains b)).lookup a := by
    intro a
    rw [lookup_joinH, lookup_headerOf, lookup_headerOf, lookup_headerOf]
    by_cases h1 : a ∈ as
    · simp [h1]
    · by_cases h2 : a ∈ bs <;> simp [h1, h2, List.contains_iff_mem]
  rw [attrs_headerOf, attrs_headerOf] at rq
  have rq' := rep_congrH rq hH
  exact ⟨⟨q, by simp only [CRA.toExpr]; exact eval_join2 hr1 hr2 hq, rq'⟩,
    fun hdj => ⟨q, by
      simp only [CRA.toExpr]
      refine eval_prod2 hr1 hr2 hq fun a h1 h2 => ?_
      rw [attrs_congr i1.head a, attrs_headerOf] at h1
      rw [attrs_congr i2.head a, attrs_headerOf] at h2
      exact hdj a h2 h1, rq'⟩⟩

theorem ev_prod {e f : CRA} {as bs : List String} {P Q : Tuple → Prop}
    (he : EvRep env D e as P) (hf : EvRep env D f bs Q) (hd : ∀ b ∈ bs, b ∉ as) :
    EvRep env D (.prod e f) (as ++ bs) (fun t => P (t.restrict as) ∧ Q (t.restrict bs)) := by
  have : (bs.filter fun b => !as.contains b) = bs :=
    List.filter_eq_self.mpr fun b hb => by simp [List.contains_iff_mem, hd b hb]
  have := (ev_join he hf).2 hd
  rwa [‹(bs.filter fun b => !as.contains b) = bs›] at this

theorem ev_union {e f : CRA} {as bs : List String} {P Q : Tuple → Prop}
    (he : EvRep env D e as P) (hf : EvRep env D f bs Q) (hs : ∀ a, a ∈ as ↔ a ∈ bs) :
    EvRep env D (.union e f) as (fun t => P t ∨ Q t) ∧
    EvRep env D (.diff e f) as (fun t => P t ∧ ¬ Q t) := by
  obtain ⟨r1, hr1, i1⟩ := he
  obtain ⟨r2, hr2, i2⟩ := hf.congrH fun a => (hs a).symm
  obtain ⟨q, hq, rq⟩ := rep_union i1 i2
  obtain ⟨q', hq', rq'⟩ := rep_diff i1 i2
  exact ⟨⟨q, by simp only [CRA.toExpr]; exact eval_union2 hr1 hr2 hq, rq⟩,
    ⟨q', by simp only [CRA.toExpr]; exact eval_except2 hr1 hr2 hq', rq'⟩⟩

theorem ev_selA (hD : DomOK D = true) {e : CRA} {as : List String} {P : Tuple → Prop}
    (he : EvRep env D e as P) {a b : String} (ha : a ∈ as) (hb : b ∈ as) :
    EvRep env D (.sel (.eqA a b) e) as (fun t => P t ∧ t.get? a = t.get? b) := by
  obtain ⟨r, hr, rr⟩ := he
  have hta : ∀ c ∈ (Test.eqA a b).attrs, c ∈ as := fun c hc => by
    simp only [Test.attrs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> assumption
  have hev : ∀ u ∈ r.tuples, Term.holds u (Test.eqA a b).toTerm = .ok ((Test.eqA a b).evalOn u) :=
    fun u hu => Test.holds_toTerm hD (rr.mem_fits hu) hta (by simp [Test.consts])
  obtain ⟨q, hq⟩ := Finrel.select_ok.mpr fun u hu => ⟨_, hev u hu⟩
  have rq := rep_select rr hq
  have hsc : ∀ c ∈ (Test.eqA a b).toTerm.attrs, c ∈ r.heading.attrs := fun c h =>
    (attrs_congr rr.head c).mpr (by rw [attrs_headerOf]; exact hta c (Test.attrs_toTerm _ c h))
  refine ⟨q, by simp only [CRA.toExpr]; exact eval_select hr hq hsc, rq.wf, rq.head, fun t => ?_⟩
  rw [rq.mem]
  constructor
  · rintro ⟨f, hp, h⟩
    rw [hev t ((rr.mem t).mpr ⟨f, hp⟩)] at h
    exact ⟨f, hp, by simpa [Test.evalOn] using Except.ok.inj h⟩
  · rintro ⟨f, hp, h⟩
    refine ⟨f, hp, ?_⟩
    rw [hev t ((rr.mem t).mpr ⟨f, hp⟩)]
    simp [Test.evalOn, h]

/-- σ with any test whose attributes are there and whose constants are in `D`. -/
theorem ev_selT (hD : DomOK D = true) {e : CRA} {as : List String} {P : Tuple → Prop}
    (he : EvRep env D e as P) {t : Test} (hta : ∀ c ∈ t.attrs, c ∈ as)
    (htc : ∀ c ∈ t.consts, D.mem c = true) :
    EvRep env D (.sel t e) as (fun u => P u ∧ t.evalOn u = true) := by
  obtain ⟨r, hr, rr⟩ := he
  have hev : ∀ u ∈ r.tuples, Term.holds u t.toTerm = .ok (t.evalOn u) :=
    fun u hu => Test.holds_toTerm hD (rr.mem_fits hu) hta htc
  obtain ⟨q, hq⟩ := Finrel.select_ok.mpr fun u hu => ⟨_, hev u hu⟩
  have rq := rep_select rr hq
  have hsc : ∀ c ∈ t.toTerm.attrs, c ∈ r.heading.attrs := fun c h =>
    (attrs_congr rr.head c).mpr (by rw [attrs_headerOf]; exact hta c (Test.attrs_toTerm _ c h))
  refine ⟨q, by simp only [CRA.toExpr]; exact eval_select hr hq hsc, rq.wf, rq.head, fun u => ?_⟩
  rw [rq.mem]
  constructor
  · rintro ⟨f, hp, h⟩
    rw [hev u ((rr.mem u).mpr ⟨f, hp⟩)] at h
    exact ⟨f, hp, Except.ok.inj h⟩
  · rintro ⟨f, hp, h⟩
    refine ⟨f, hp, ?_⟩
    rw [hev u ((rr.mem u).mpr ⟨f, hp⟩), h]

theorem ev_proj {e : CRA} {as bs : List String} {P : Tuple → Prop}
    (he : EvRep env D e as P) (hsub : ∀ b ∈ bs, b ∈ as) (hn : bs.Nodup) :
    EvRep env D (.proj bs e) bs
      (fun t => ∃ u, u.Fits (headerOf D as) ∧ P u ∧ u.restrict bs = t) := by
  obtain ⟨r, hr, rr⟩ := he
  obtain ⟨q, hq, rq⟩ := rep_project rr (fun a ha => by rw [attrs_headerOf]; exact hsub a ha) hn
  refine ⟨q, by simp only [CRA.toExpr]; exact eval_project hr hq, rep_congrH rq fun a => ?_⟩
  rw [lookup_restrictH, lookup_headerOf, lookup_headerOf]
  by_cases ha : a ∈ bs
  · rw [if_pos ha, if_pos (hsub a ha), if_pos ha]
  · rw [if_neg ha, if_neg ha]

theorem ev_ren {e : CRA} {as : List String} {P : Tuple → Prop} {ren : List (String × String)}
    (he : EvRep env D e as P) (hsrc : ∀ p ∈ ren, p.1 ∈ as)
    (hn' : (CRA.renamed ren as).Nodup) :
    EvRep env D (.ren ren e) (CRA.renamed ren as)
      (fun t => ∃ u, u.Fits (headerOf D as) ∧ P u ∧ Finrel.renameTuple ren u = t) := by
  obtain ⟨r, hr, rr⟩ := he
  have hren : CRA.renamed ren as = as.map (Finrel.renameAttr ren) := rfl
  have hinj : ∀ a ∈ as, ∀ b ∈ as, Finrel.renameAttr ren a = Finrel.renameAttr ren b → a = b := by
    rw [hren] at hn'; exact inj_of_nodup_map hn'
  have hattr := mem_attrs_of_headIs rr.head
  obtain ⟨q, hq⟩ := Finrel.rename_ok.mpr ⟨fun p hp => (hattr p.1).mpr (hsrc p hp), by
    simp only [Finrel.renameHeading, Heading.attrs, List.map_map]
    exact nodup_map_of_inj (nodup_of_map_fst rr.wf.nodup) fun x hx y hy e => by
      have hx' := (hattr x.1).mp (List.mem_map_of_mem hx)
      have hy' := (hattr y.1).mp (List.mem_map_of_mem hy)
      exact inj_of_nodup_map rr.wf.nodup x hx y hy (hinj _ hx' _ hy' e)⟩
  have hall := allD_of_headIs rr.wf.nodup rr.head
  have hhead : HeadIs D (CRA.renamed ren as) q.heading := by
    intro b
    rw [Finrel.rename_heading hq, lookup_allD (fun p hp => by
      simp only [Finrel.renameHeading, List.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp; exact hall x hx), lookup_headerOf]
    have : b ∈ (Finrel.renameHeading ren r.heading).map (·.1) ↔ b ∈ CRA.renamed ren as := by
      simp only [Finrel.renameHeading, List.map_map, hren, List.mem_map, Function.comp_def]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x.1, (hattr x.1).mp (List.mem_map_of_mem hx), rfl⟩
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨x, hx, e⟩ := List.mem_map.mp ((hattr a).mpr ha)
        exact ⟨x, hx, by rw [e]⟩
    by_cases hb : b ∈ CRA.renamed ren as
    · rw [if_pos (this.mpr hb), if_pos hb]
    · rw [if_neg (fun h => hb (this.mp h)), if_neg hb]
  have hw := Finrel.rename_wf hq rr.wf
  refine ⟨q, by simp only [CRA.toExpr]; exact eval_rename hr hq, hw, hhead, fun t => ?_⟩
  rw [Finrel.mem_rename hq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fits_of_mem hw hhead ((Finrel.mem_rename hq _).mpr ⟨u, hu, rfl⟩), u, ?_⟩
    exact ⟨((rr.mem u).mp hu).1, ((rr.mem u).mp hu).2, rfl⟩
  · rintro ⟨-, u, fu, hp, rfl⟩
    exact ⟨u, (rr.mem u).mpr ⟨fu, hp⟩, rfl⟩

end EvRep

/-! ## The active domain, computed -/

section ActiveDomain
variable {S : Schema} {D : Domain} {env : Env} {C : List Value}

theorem fits_single {a : String} {t : Tuple} (f : t.Fits (headerOf D [a])) :
    t = [(a, readAsg t a)] := by
  have := eq_tupOf (by simp) f (match_readAsg f)
  simpa [tupOf, Tuple.ofPairs] using this

theorem fits_single_of {a : String} {v : Value} (hv : D.mem v = true) :
    Tuple.Fits (headerOf D [a]) [(a, v)] := by
  have := fits_tupOf (D := D) (as := [a]) (μ := id) (ρ := fun _ => v) (by simp) (by simp [hv])
  simpa [tupOf, Tuple.ofPairs] using this

theorem readAsg_single (a : String) (v : Value) : readAsg [(a, v)] a = v := by
  simp [readAsg, Tuple.get?]

/-- A one-attribute relation described by its values. -/
theorem EvRep.single {e : CRA} {a : String} {P : Tuple → Prop} {R : Value → Prop}
    (h : EvRep env D e [a] P) (hpr : ∀ v, D.mem v = true → (P [(a, v)] ↔ R v)) :
    EvRep env D e [a] (fun t => R (readAsg t a)) := by
  refine h.congr fun t f => ?_
  obtain ⟨v, hv, hD, -⟩ := get?_fits f (List.mem_singleton_self a)
  have e1 : readAsg t a = v := by simp [readAsg, hv]
  rw [fits_single f, e1]
  have := hpr v hD
  rw [readAsg_single]; exact this

theorem ev_litVals {a : String} {vs : List Value} (hv : ∀ v ∈ vs, D.mem v = true) :
    EvRep env D (.lit [a] (vs.map ([·]))) [a] (fun t => readAsg t a ∈ vs) := by
  refine (ev_lit (by simp) (fun row hrow => ?_)).single fun v _ => ?_
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrow
    simp [hv c hc]
  · simp only [litTuples, List.map_map, List.mem_map, Function.comp_def, List.zip_cons_cons,
      List.zip_nil_right]
    constructor
    · rintro ⟨c, hc, e⟩
      have : c = v := by simpa [Tuple.ofPairs] using e
      exact this ▸ hc
    · intro h; exact ⟨v, h, by simp [Tuple.ofPairs]⟩

theorem ev_colE (henv : Conforms S D env) {a n b : String} {as : List String} (hp : (n, as) ∈ S)
    (hb : b ∈ as) :
    EvRep env D (colE a n b) [a] (fun t => ∃ u ∈ tuplesOf env n, u.get? b = some (readAsg t a)) := by
  obtain ⟨r, hr, e1⟩ := ev_rel henv hp
  have e2 := ev_proj e1 (bs := [b]) (by simp [hb]) (by simp)
  have e3 := ev_ren e2 (ren := [(b, a)]) (by simp) (by simp [CRA.renamed])
  have hren : CRA.renamed [(b, a)] [b] = [a] := by simp [CRA.renamed]
  rw [hren] at e3
  unfold colE
  refine e3.single (R := fun v => ∃ u ∈ tuplesOf env n, u.get? b = some v) fun v hv => ?_
  rw [tuplesOf_eq hr]
  constructor
  · rintro ⟨t', ft', ⟨u, fu, hu, hres⟩, hrn⟩
    rw [fits_single ft'] at hrn hres
    have hw : readAsg t' b = v := by
      simpa [Finrel.renameTuple, Finrel.renameAttr, Tuple.ofPairs] using hrn
    refine ⟨u, hu, ?_⟩
    have := congrArg (Tuple.get? · b) hres
    simp only [get?_restrict, List.mem_singleton, if_true] at this
    rw [this, hw]; simp [Tuple.get?]
  · rintro ⟨u, hu, hv'⟩
    obtain ⟨r', hr', hw, hh⟩ := henv _ hp
    rw [hr] at hr'; cases hr'
    have fu := fits_of_mem hw hh hu
    refine ⟨[(b, v)], fits_single_of hv, ⟨u, fu, hu, ?_⟩, by
      simp [Finrel.renameTuple, Finrel.renameAttr, Tuple.ofPairs]⟩
    exact restrict_eq_of_agree fu.sorted (fits_single_of hv) fun c hc => by
      simp only [List.mem_singleton] at hc; subst hc; rw [hv']; simp [Tuple.get?]

theorem ev_foldl (henv : Conforms S D env) {a : String} :
    ∀ {L : List (String × String)}, (∀ nb ∈ L, ∃ as, (nb.1, as) ∈ S ∧ nb.2 ∈ as) →
    ∀ {acc : CRA} {R : Value → Prop}, EvRep env D acc [a] (fun t => R (readAsg t a)) →
      EvRep env D ((L.map fun nb => colE a nb.1 nb.2).foldl .union acc) [a]
        (fun t => R (readAsg t a) ∨
          ∃ nb ∈ L, ∃ u ∈ tuplesOf env nb.1, u.get? nb.2 = some (readAsg t a))
  | [], _, acc, R, h => h.congr fun t _ => by simp
  | nb :: L, hL, acc, R, h => by
    obtain ⟨as, hp, hb⟩ := hL nb List.mem_cons_self
    have hu := (ev_union h (ev_colE (a := a) henv hp hb) fun _ => Iff.rfl).1
    have := ev_foldl henv (L := L) (fun nb' h' => hL nb' (List.mem_cons_of_mem _ h'))
      (R := fun v => R v ∨ ∃ u ∈ tuplesOf env nb.1, u.get? nb.2 = some v) hu
    simp only [List.map_cons, List.foldl_cons]
    refine this.congr fun t _ => ?_
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

/-- The active domain column `adE S C a` holds exactly the stored values and the
constants. -/
theorem ev_adE (henv : Conforms S D env) (hC : ∀ c ∈ C, D.mem c = true) {a : String} :
    EvRep env D (adE S C a) [a] (fun t => readAsg t a ∈ adom S env ++ C) := by
  have h0 := (ev_union (ev_litVals (env := env) (D := D) (a := a) (vs := []) (by simp))
    (ev_litVals (env := env) (a := a) hC) fun _ => Iff.rfl).1
  have hL : ∀ nb ∈ S.flatMap (fun p => p.2.map fun b => (p.1, b)),
      ∃ as, (nb.1, as) ∈ S ∧ nb.2 ∈ as := by
    intro nb h
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hp, b, hb, rfl⟩ := h
    exact ⟨p.2, hp, hb⟩
  have h1 := ev_foldl henv hL (R := fun v => v ∈ ([] : List Value).map (fun x => x) ∨ v ∈ C) (by
    simpa using h0)
  have hcols : (S.flatMap fun p => p.2.map fun b => colE a p.1 b) =
      (S.flatMap fun p => p.2.map fun b => (p.1, b)).map fun nb => colE a nb.1 nb.2 := by
    simp [List.map_flatMap, List.map_map, Function.comp_def]
  unfold adE
  rw [hcols]
  refine h1.congr fun t _ => ?_
  simp only [List.map_id', List.not_mem_nil, false_or, List.mem_append]
  constructor
  · rintro (h | ⟨nb, hnb, u, hu, hv⟩)
    · exact Or.inr h
    · exact Or.inl (mem_adom (hL nb hnb).choose_spec.1 hu (p := (nb.2, readAsg t a)) (lookup_mem hv))
  · rintro (h | h)
    · simp only [adom, List.mem_flatMap, List.mem_map] at h
      obtain ⟨p, hp, u, hu, q, hq, e⟩ := h
      obtain ⟨r, hr, hw, hh⟩ := henv p hp
      have fu := fits_of_mem hw hh (by rw [← tuplesOf_eq hr]; exact hu)
      have hq1 : q.1 ∈ p.2 := by
        rw [← attrs_headerOf D p.2, ← fu.attrs]; exact List.mem_map_of_mem hq
      refine Or.inr ⟨(p.1, q.1), ?_, u, hu, ?_⟩
      · simp only [List.mem_flatMap, List.mem_map]; exact ⟨p, hp, q.1, hq1, rfl⟩
      · rw [get?_of_mem fu hq, e]
    · exact Or.inl h

end ActiveDomain

/-! ## Tuples over encoded variables -/

section Assignments
variable {D : Domain}

/-- The assignment a tuple over encoded variables gives. -/
def asg (t : Tuple) : String → Value := fun x => readAsg t (enc x)

/-- The tuple giving each variable of `W` the value `ρ` gives it. -/
def encTup (W : List String) (ρ : String → Value) : Tuple :=
  Tuple.ofPairs (W.map fun y => (enc y, ρ y))

theorem readAsg_restrict {as : List String} {a : String} (ha : a ∈ as) (t : Tuple) :
    readAsg (t.restrict as) a = readAsg t a := by
  simp [readAsg, get?_restrict, ha]

theorem asg_restrict {as : List String} {x : String} (hx : enc x ∈ as) (t : Tuple) :
    asg (t.restrict as) x = asg t x := readAsg_restrict hx t

theorem keys_encTup (W : List String) (ρ : String → Value) :
    (W.map fun y => (enc y, ρ y)).map (·.1) = W.map enc := by simp [List.map_map, Function.comp_def]

theorem lookup_map_enc {ρ : String → Value} {x : String} :
    ∀ {W : List String}, x ∈ W → (W.map fun y => (enc y, ρ y)).lookup (enc x) = some (ρ x)
  | [], h => by cases h
  | y :: W, hx => by
    simp only [List.map_cons, List.lookup_cons]
    by_cases e : x = y
    · subst e; simp
    · have : (enc x == enc y) = false := by simp only [beq_eq_false_iff_ne]; exact fun h => e (enc_inj h)
      rw [this]
      exact lookup_map_enc (by simpa [e] using hx)

theorem get?_encTup {W : List String} (hn : W.Nodup) (ρ : String → Value) {x : String}
    (hx : x ∈ W) : (encTup W ρ).get? (enc x) = some (ρ x) := by
  rw [encTup, Tuple.get?_ofPairs (by rw [keys_encTup]; exact nodup_map_enc hn)]
  exact lookup_map_enc hx

theorem asg_encTup {W : List String} (hn : W.Nodup) (ρ : String → Value) {x : String}
    (hx : x ∈ W) : asg (encTup W ρ) x = ρ x := by
  simp [asg, readAsg, get?_encTup hn ρ hx]

theorem fits_encTup {W : List String} (hn : W.Nodup) {ρ : String → Value}
    (hd : ∀ y ∈ W, D.mem (ρ y) = true) : (encTup W ρ).Fits (headerOf D (W.map enc)) where
  sorted := ofPairs_sorted (by rw [keys_encTup]; exact nodup_map_enc hn)
  attrs a := by rw [encTup, attrs_ofPairs, keys_encTup, attrs_headerOf]
  dom p hp d hd' := by
    rw [encTup, mem_ofPairs] at hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
    rw [lookup_headerOf, if_pos (List.mem_map_of_mem hy)] at hd'
    cases hd'; exact hd y hy

/-- In a tuple over encoded variables, each variable's attribute holds its value. -/
theorem get?_asg {W : List String} {t : Tuple} (f : t.Fits (headerOf D (W.map enc))) {x : String}
    (hx : x ∈ W) : t.get? (enc x) = some (asg t x) := by
  obtain ⟨v, hv, -⟩ := get?_fits f (List.mem_map_of_mem hx)
  simp [asg, readAsg, hv]

theorem asg_mem_D {W : List String} {t : Tuple} (f : t.Fits (headerOf D (W.map enc))) {x : String}
    (hx : x ∈ W) : D.mem (asg t x) = true := by
  obtain ⟨v, hv, hD, -⟩ := get?_fits f (List.mem_map_of_mem hx)
  simp [asg, readAsg, hv, hD]

/-- Two tuples over the same encoded variables with the same values are equal. -/
theorem eq_of_asg {W : List String} {t u : Tuple} (ft : t.Fits (headerOf D (W.map enc)))
    (fu : u.Fits (headerOf D (W.map enc))) (h : ∀ x ∈ W, asg t x = asg u x) : t = u := by
  apply Tuple.ext_get? ft.sorted fu.sorted
  intro a
  by_cases ha : a ∈ W.map enc
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    rw [get?_asg ft hx, get?_asg fu hx, h x hx]
  · rw [ft.get?_none (by rw [attrs_headerOf]; exact ha), fu.get?_none (by rw [attrs_headerOf]; exact ha)]

theorem eq_encTup {W : List String} (hn : W.Nodup) {t : Tuple}
    (f : t.Fits (headerOf D (W.map enc))) : t = encTup W (asg t) :=
  eq_of_asg f (fits_encTup hn fun _ hy => asg_mem_D f hy) fun _ hx => (asg_encTup hn _ hx).symm

theorem fits_restrict_enc {W Z : List String} {t : Tuple} (f : t.Fits (headerOf D (W.map enc)))
    (hsub : ∀ z ∈ Z, z ∈ W) : (t.restrict (Z.map enc)).Fits (headerOf D (Z.map enc)) := by
  have := f.restrict (H := headerOf D (Z.map enc)) fun a d h => by
    rw [lookup_headerOf] at h ⊢
    split at h
    · rename_i ha; cases h
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
      rw [if_pos (List.mem_map_of_mem (hsub z hz))]
    · cases h
  rwa [attrs_headerOf] at this

theorem fits_restrict_any {as bs : List String} {u : Tuple} (f : u.Fits (headerOf D as))
    (hsub : ∀ b ∈ bs, b ∈ as) : (u.restrict bs).Fits (headerOf D bs) := by
  have := f.restrict (H := headerOf D bs) fun a d h => by
    rw [lookup_headerOf] at h ⊢
    split at h
    · rename_i ha; cases h; rw [if_pos (hsub a ha)]
    · cases h
  rwa [attrs_headerOf] at this

end Assignments

/-! ## Relations over encoded variables -/

/-- The values the translation's quantifiers range over: the active domain of the database
and the constants `C`. -/
def AD (S : Schema) (env : Env) (C : List Value) : List Value := adom S env ++ C

/-- `e` evaluates to the tuples over the variables `W` whose values are in `AD` and whose
assignment satisfies `G`. -/
def AsgRep (S : Schema) (D : Domain) (env : Env) (C : List Value) (e : CRA) (W : List String)
    (G : (String → Value) → Prop) : Prop :=
  EvRep env D e (W.map enc) (fun t => (∀ y ∈ W, asg t y ∈ AD S env C) ∧ G (asg t))

/-- `G` depends only on the variables `W`. -/
def Loc (W : List String) (G : (String → Value) → Prop) : Prop :=
  ∀ ρ ρ', (∀ y ∈ W, ρ y = ρ' y) → (G ρ ↔ G ρ')

section AsgRep
variable {S : Schema} {D : Domain} {env : Env} {C : List Value}

theorem AD_mem_D (henv : Conforms S D env) (hC : ∀ c ∈ C, D.mem c = true) {v : Value}
    (hv : v ∈ AD S env C) : D.mem v = true := by
  rcases List.mem_append.mp hv with h | h
  · simp only [adom, List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hp, u, hu, q, hq, rfl⟩ := h
    obtain ⟨r, hr, hw, hh⟩ := henv p hp
    have fu := fits_of_mem hw hh (by rw [← tuplesOf_eq hr]; exact hu)
    exact fu.dom q hq D (by
      rw [lookup_headerOf, if_pos]
      rw [← attrs_headerOf D p.2, ← fu.attrs]; exact List.mem_map_of_mem hq)
  · exact hC v h

theorem mem_map_enc_iff {W W' : List String} (hs : ∀ x, x ∈ W ↔ x ∈ W') (a : String) :
    a ∈ W.map enc ↔ a ∈ W'.map enc := by
  simp only [List.mem_map]
  exact ⟨fun ⟨x, hx, e⟩ => ⟨x, (hs x).mp hx, e⟩, fun ⟨x, hx, e⟩ => ⟨x, (hs x).mpr hx, e⟩⟩

theorem AsgRep.congrW {e : CRA} {W W' : List String} {G : (String → Value) → Prop}
    (h : AsgRep S D env C e W G) (hs : ∀ x, x ∈ W ↔ x ∈ W') : AsgRep S D env C e W' G := by
  refine (EvRep.congrH h (mem_map_enc_iff hs)).congr fun t _ => ?_
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun y hy => h1 y ((hs y).mpr hy), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun y hy => h1 y ((hs y).mp hy), h2⟩

theorem AsgRep.congrG {e : CRA} {W : List String} {G G' : (String → Value) → Prop}
    (h : AsgRep S D env C e W G) (hg : ∀ ρ, (∀ y ∈ W, ρ y ∈ AD S env C) → (G ρ ↔ G' ρ)) :
    AsgRep S D env C e W G' :=
  h.congr fun _ _ => ⟨fun ⟨h1, h2⟩ => ⟨h1, (hg _ h1).mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (hg _ h1).mpr h2⟩⟩

theorem fits_nil {t : Tuple} (f : t.Fits (headerOf D [])) : t = [] := by
  match t, f with
  | [], _ => rfl
  | p :: _, f =>
    have := (f.attrs p.1).mp (List.mem_cons_self)
    simp [attrs_headerOf] at this

theorem a_adV (henv : Conforms S D env) (hC : ∀ c ∈ C, D.mem c = true) :
    ∀ {xs : List String}, xs.Nodup → AsgRep S D env C (adV S C xs) xs (fun _ => True)
  | [], _ => by
    refine (ev_lit (bs := []) (rows := [[]]) (by simp) (by simp)).congr fun t f => ?_
    rw [fits_nil f]
    simp [litTuples, Tuple.ofPairs]
  | x :: xs, hn => by
    have h1 := ev_adE (a := enc x) henv hC
    have h2 := a_adV henv hC (List.nodup_cons.mp hn).2
    have hp := ev_prod h1 h2 (by
      intro b hb hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact (List.nodup_cons.mp hn).1 (mem_map_enc.mp hb))
    refine (hp.congrH fun a => by simp).congr fun t f => ?_
    simp only [List.mem_cons, forall_eq_or_imp, and_true]
    rw [readAsg_restrict (List.mem_singleton_self _)]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun y hy => by rw [← asg_restrict (List.mem_map_of_mem hy)]; exact h2 y hy⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun y hy => by rw [asg_restrict (List.mem_map_of_mem hy)]; exact h2 y hy⟩

theorem restrict_pred {W : List String} {G : (String → Value) → Prop} (hl : Loc W G)
    (t : Tuple) :
    ((∀ y ∈ W, asg (t.restrict (W.map enc)) y ∈ AD S env C) ∧ G (asg (t.restrict (W.map enc)))) ↔
      ((∀ y ∈ W, asg t y ∈ AD S env C) ∧ G (asg t)) := by
  have e : ∀ y ∈ W, asg (t.restrict (W.map enc)) y = asg t y := fun y hy =>
    asg_restrict (List.mem_map_of_mem hy) t
  rw [hl _ _ e]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun y hy => e y hy ▸ h1 y hy, h2⟩,
    fun ⟨h1, h2⟩ => ⟨fun y hy => (e y hy).symm ▸ h1 y hy, h2⟩⟩

theorem a_join {e f : CRA} {W W' : List String} {G G' : (String → Value) → Prop}
    (he : AsgRep S D env C e W G) (hf : AsgRep S D env C f W' G') (hl : Loc W G) (hl' : Loc W' G') :
    AsgRep S D env C (.join e f) (W ++ W'.filter fun b => !W.contains b) (fun ρ => G ρ ∧ G' ρ) := by
  have := (ev_join he hf).1
  rw [enc_filter] at this
  rw [AsgRep, List.map_append]
  refine this.congr fun t _ => ?_
  rw [restrict_pred hl, restrict_pred hl']
  simp only [List.mem_append, List.mem_filter]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun y hy => hy.elim (h1 y) fun h => h3 y h.1, h2, h4⟩
  · rintro ⟨h1, h2, h4⟩
    exact ⟨⟨fun y hy => h1 y (Or.inl hy), h2⟩, fun y hy => by
      by_cases hw : y ∈ W
      · exact h1 y (Or.inl hw)
      · exact h1 y (Or.inr ⟨hy, by simp [List.contains_iff_mem, hw]⟩), h4⟩

theorem a_prod {e f : CRA} {W W' : List String} {G G' : (String → Value) → Prop}
    (he : AsgRep S D env C e W G) (hf : AsgRep S D env C f W' G') (hl : Loc W G) (hl' : Loc W' G')
    (hd : ∀ y ∈ W', y ∉ W) :
    AsgRep S D env C (.prod e f) (W ++ W') (fun ρ => G ρ ∧ G' ρ) := by
  have := ev_prod he hf (fun b hb hbW => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb; exact hd y hy (mem_map_enc.mp hbW))
  rw [AsgRep, List.map_append]
  refine this.congr fun t _ => ?_
  rw [restrict_pred hl, restrict_pred hl']
  simp only [List.mem_append]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun y hy => hy.elim (h1 y) (h3 y), h2, h4⟩
  · rintro ⟨h1, h2, h4⟩
    exact ⟨⟨fun y hy => h1 y (Or.inl hy), h2⟩, fun y hy => h1 y (Or.inr hy), h4⟩

theorem a_pad (henv : Conforms S D env) (hC : ∀ c ∈ C, D.mem c = true) {e : CRA}
    {W ys : List String} {G : (String → Value) → Prop} (he : AsgRep S D env C e W G)
    (hl : Loc W G) (hy : ys.Nodup) (hd : ∀ y ∈ ys, y ∉ W) :
    AsgRep S D env C (pad S C e ys) (W ++ ys) G :=
  (a_prod he (a_adV henv hC hy) hl (fun _ _ _ => Iff.rfl) hd).congrG fun _ _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

theorem a_union {e f : CRA} {W W' : List String} {G G' : (String → Value) → Prop}
    (he : AsgRep S D env C e W G) (hf : AsgRep S D env C f W' G') (hs : ∀ x, x ∈ W ↔ x ∈ W') :
    AsgRep S D env C (.union e f) W (fun ρ => G ρ ∨ G' ρ) ∧
    AsgRep S D env C (.diff e f) W (fun ρ => G ρ ∧ ¬ G' ρ) := by
  have hf' := hf.congrW fun x => (hs x).symm
  obtain ⟨h1, h2⟩ := ev_union he hf' fun a => Iff.rfl
  refine ⟨h1.congr fun t _ => ?_, h2.congr fun t _ => ?_⟩
  · constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, Or.inl h2⟩
      · exact ⟨h1, Or.inr h2⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
  · constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, fun h => h3 ⟨h1, h⟩⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, fun ⟨_, h⟩ => h3 h⟩

theorem a_selEq (hD : DomOK D = true) {e : CRA} {W : List String} {G : (String → Value) → Prop}
    (he : AsgRep S D env C e W G) {x y : String} (hx : x ∈ W) (hy : y ∈ W) :
    AsgRep S D env C (.sel (.eqA (enc x) (enc y)) e) W (fun ρ => G ρ ∧ ρ x = ρ y) := by
  refine (ev_selA hD he (List.mem_map_of_mem hx) (List.mem_map_of_mem hy)).congr fun t f => ?_
  rw [get?_asg f hx, get?_asg f hy]
  simp only [Option.some.injEq]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

theorem a_selCmpA (hD : DomOK D = true) {e : CRA} {W : List String} {G : (String → Value) → Prop}
    (he : AsgRep S D env C e W G) (o : Cmp) {x y : String} (hx : x ∈ W) (hy : y ∈ W) :
    AsgRep S D env C (.sel (.cmpA o (enc x) (enc y)) e) W
      (fun ρ => G ρ ∧ o.holds (ρ x) (ρ y) = true) := by
  refine (ev_selT hD he (t := .cmpA o (enc x) (enc y)) (fun c hc => by
      simp only [Test.attrs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact List.mem_map_of_mem hx
      · exact List.mem_map_of_mem hy) (by simp [Test.consts])).congr fun t f => ?_
  simp only [Test.evalOn, get?_asg f hx, get?_asg f hy]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

theorem a_selCmpC (hD : DomOK D = true) {e : CRA} {W : List String} {G : (String → Value) → Prop}
    (he : AsgRep S D env C e W G) (o : Cmp) {x : String} {c : Value} (hx : x ∈ W)
    (hc : D.mem c = true) :
    AsgRep S D env C (.sel (.cmpC o (enc x) c) e) W (fun ρ => G ρ ∧ o.holds (ρ x) c = true) := by
  refine (ev_selT hD he (t := .cmpC o (enc x) c) (fun a ha => by
      simp only [Test.attrs, List.mem_singleton] at ha
      subst ha; exact List.mem_map_of_mem hx) (by simp [Test.consts, hc])).congr fun t f => ?_
  simp only [Test.evalOn, get?_asg f hx]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-- π that drops the variable `x`: "there is a value of `x`". -/
theorem a_projEx (henv : Conforms S D env) (hC : ∀ c ∈ C, D.mem c = true) {e : CRA}
    {W Z : List String} {G : (String → Value) → Prop} {x : String}
    (he : AsgRep S D env C e W G) (hl : Loc W G) (hn : W.Nodup) (hz : Z.Nodup)
    (hZW : ∀ z ∈ Z, z ∈ W) (hx : x ∈ W) (hxZ : x ∉ Z) (hWZ : ∀ y ∈ W, y = x ∨ y ∈ Z) :
    AsgRep S D env C (.proj (Z.map enc) e) Z (fun ρ => ∃ a ∈ AD S env C, G (upd ρ x a)) := by
  refine (ev_proj he (fun b hb => by
      obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hb; exact List.mem_map_of_mem (hZW z hz'))
    (nodup_map_enc hz)).congr fun t ft => ?_
  have hagree : ∀ u : Tuple, u.restrict (Z.map enc) = t → ∀ z ∈ Z, asg t z = asg u z := by
    rintro u rfl z hz'; exact asg_restrict (List.mem_map_of_mem hz') u
  constructor
  · rintro ⟨u, fu, ⟨h1, h2⟩, hr⟩
    have ag := hagree u hr
    refine ⟨fun z hz' => ag z hz' ▸ h1 z (hZW z hz'), asg u x, h1 x hx, ?_⟩
    refine (hl _ _ fun y hy => ?_).mp h2
    rcases hWZ y hy with rfl | hyZ
    · simp
    · rw [upd_other (fun (e : y = x) => hxZ (e ▸ hyZ)), ag y hyZ]
  · rintro ⟨h1, a, ha, h2⟩
    have hval : ∀ y ∈ W, upd (asg t) x a y ∈ AD S env C := fun y hy => by
      rcases hWZ y hy with rfl | hyZ
      · simp [ha]
      · rw [upd_other (fun (e : y = x) => hxZ (e ▸ hyZ))]; exact h1 y hyZ
    have fu := fits_encTup (D := D) hn fun y hy => AD_mem_D henv hC (hval y hy)
    refine ⟨_, fu, ⟨fun y hy => ?_, ?_⟩, ?_⟩
    · rw [asg_encTup hn _ hy]; exact hval y hy
    · exact (hl _ _ fun y hy => asg_encTup hn _ hy).mpr h2
    · apply eq_of_asg (fits_restrict_enc fu (fun z hz' => hZW z hz')) ft
      intro z hz'
      rw [asg_restrict (List.mem_map_of_mem hz'), asg_encTup hn _ (hZW z hz'),
        upd_other (fun (e : z = x) => hxZ (e ▸ hz'))]

end AsgRep

/-! ## Formula by formula -/

section Formulas
variable {S : Schema} {D : Domain} {env : Env} {C : List Value}

theorem loc_sat {W : List String} (φ : Formula) (h : ∀ x ∈ φ.fv, x ∈ W) :
    Loc W (Sat (· ∈ AD S env C) S env φ) := fun _ _ e =>
  Sat_congr φ fun x hx => e x (h x hx)

theorem a_adE1 (henv : Conforms S D env) (hC : ∀ c ∈ C, D.mem c = true) (x : String) :
    AsgRep S D env C (adE S C (enc x)) [x] (fun _ => True) :=
  (ev_adE henv hC).congr fun t _ => by simp [asg, AD]

theorem mem_zip_swap : ∀ {xs as : List String} {x a : String}, (x, a) ∈ xs.zip as → (a, x) ∈ as.zip xs
  | [], _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | y :: xs, b :: as, x, a, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h ⊢
    rcases h with ⟨rfl, rfl⟩ | h
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (mem_zip_swap h)

theorem ev_sels (hD : DomOK D = true) {e : CRA} {as : List String} {P : Tuple → Prop}
    (he : EvRep env D e as P) :
    ∀ {ps : List (String × String)}, (∀ p ∈ ps, p.1 ∈ as ∧ p.2 ∈ as) →
      EvRep env D ((ps.map fun p => Test.eqA p.1 p.2).foldr .sel e) as
        (fun t => P t ∧ ∀ p ∈ ps, t.get? p.1 = t.get? p.2)
  | [], _ => he.congr fun _ _ => by simp
  | p :: ps, h => by
    simp only [List.map_cons, List.foldr_cons]
    have ih := ev_sels hD he (ps := ps) fun q hq => h q (List.mem_cons_of_mem _ hq)
    refine (ev_selA hD ih (h p List.mem_cons_self).1 (h p List.mem_cons_self).2).congr fun t _ => ?_
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h3, h2⟩, fun ⟨h1, h3, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

theorem fits_renameTuple {as : List String} {ren : List (String × String)} {u : Tuple}
    (fu : u.Fits (headerOf D as))
    (hinj : ∀ a ∈ as, ∀ b ∈ as, Finrel.renameAttr ren a = Finrel.renameAttr ren b → a = b) :
    (Finrel.renameTuple ren u).Fits (headerOf D (as.map (Finrel.renameAttr ren))) := by
  have hkeys : ∀ p ∈ u, p.1 ∈ as := fun p hp => by
    rw [← attrs_headerOf D as, ← fu.attrs]; exact List.mem_map_of_mem hp
  have hn : ((u.map fun p => (Finrel.renameAttr ren p.1, p.2)).map (·.1)).Nodup := by
    rw [List.map_map]
    exact nodup_map_of_inj (nodup_of_map_fst (Tuple.nodup_keys fu.sorted))
      (fun x hx y hy e => by
        have := hinj x.1 (hkeys x hx) y.1 (hkeys y hy) e
        exact inj_of_nodup_map (Tuple.nodup_keys fu.sorted) x hx y hy this)
  refine ⟨ofPairs_sorted hn, fun a => ?_, fun p hp d hd => ?_⟩
  · rw [Finrel.renameTuple, attrs_ofPairs, attrs_headerOf, List.map_map]
    simp only [List.mem_map, Function.comp_def]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨q.1, hkeys q hq, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      have : b ∈ u.map (·.1) := by rw [← Tuple.attrs, fu.attrs, attrs_headerOf]; exact hb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp this
      exact ⟨q, hq, rfl⟩
  · rw [Finrel.renameTuple, mem_ofPairs] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have : d = D := by
      rw [lookup_headerOf] at hd
      by_cases hc : (Finrel.renameAttr ren q.1, q.2).1 ∈ as.map (Finrel.renameAttr ren)
      · rw [if_pos hc] at hd; cases hd; rfl
      · rw [if_neg hc] at hd; cases hd
    subst this
    exact fu.dom q hq d (by rw [lookup_headerOf, if_pos (hkeys q hq)])

theorem a_atom (henv : Conforms S D env) (hS : S.WF) (hD : DomOK D = true) {n : String}
    {xs : List String} (hwt : (Formula.rel n xs).WT S = true) :
    AsgRep S D env C (atomE S n xs) xs.eraseDups (Sat (· ∈ AD S env C) S env (.rel n xs)) := by
  obtain ⟨as, has, hat, hn, hl⟩ := atom_attrs hS hwt
  have hp : (n, as) ∈ S := lookup_mem has
  obtain ⟨r, hr, e1⟩ := ev_rel henv hp
  obtain ⟨r', hr', hw, hh⟩ := henv _ hp
  rw [hr] at hr'; cases hr'
  have hmem : ∀ x ∈ xs.eraseDups, x ∈ xs := fun x h => List.mem_eraseDups.mp h
  have hvn : xs.eraseDups.Nodup := nodup_eraseDups xs
  have hfaz : ∀ x ∈ xs, ((firstAttr as xs) x, x) ∈ as.zip xs := fun x hx => mem_zip_swap (firstAttr_mem hl hx)
  have hfam : ∀ x ∈ xs, (firstAttr as xs) x ∈ as := fun x hx => (List.of_mem_zip (hfaz x hx)).1
  have hinj : ∀ x ∈ xs.eraseDups, ∀ y ∈ xs.eraseDups, (firstAttr as xs) y = (firstAttr as xs) x → y = x := fun x hx y hy e =>
    firstAttr_inj hl hn (hmem y hy) (hmem x hx) e
  have hfan : (xs.eraseDups.map (firstAttr as xs)).Nodup := nodup_map_of_inj hvn fun x hx y hy e => hinj y hy x hx e
  -- σ
  have e2 := ev_sels hD e1 (ps := (as.zip xs).map fun p => (p.1, (firstAttr as xs) p.2)) (by
    intro p hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
    exact ⟨(List.of_mem_zip hq).1, hfam q.2 (List.of_mem_zip hq).2⟩)
  -- π
  have e3 := ev_proj e2 (bs := xs.eraseDups.map (firstAttr as xs)) (fun b hb => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb; exact hfam x (hmem x hx)) hfan
  -- ρ
  have hra : ∀ x ∈ xs.eraseDups, Finrel.renameAttr (xs.eraseDups.map fun x => (firstAttr as xs x, enc x)) ((firstAttr as xs) x) = enc x := fun x hx => by
    simp only [Finrel.renameAttr]; rw [lookup_map_inj hx (hinj x hx)]; rfl
  have hren : CRA.renamed (xs.eraseDups.map fun x => (firstAttr as xs x, enc x)) (xs.eraseDups.map (firstAttr as xs)) = xs.eraseDups.map enc := by
    simp only [CRA.renamed, List.map_map]
    apply List.map_congr_left
    intro x hx; exact hra x hx
  have e4 := ev_ren e3 (ren := (xs.eraseDups.map fun x => (firstAttr as xs x, enc x))) (fun q hq => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq; exact List.mem_map_of_mem hx)
    (by rw [hren]; exact nodup_map_enc hvn)
  rw [hren] at e4
  have hinjR : ∀ a ∈ xs.eraseDups.map (firstAttr as xs), ∀ b ∈ xs.eraseDups.map (firstAttr as xs),
      Finrel.renameAttr (xs.eraseDups.map fun x => (firstAttr as xs x, enc x)) a = Finrel.renameAttr (xs.eraseDups.map fun x => (firstAttr as xs x, enc x)) b → a = b := by
    intro a ha b hb e
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    rw [hra x hx, hra y hy] at e
    rw [enc_inj e]
  have hmapR : (xs.eraseDups.map (firstAttr as xs)).map (Finrel.renameAttr (xs.eraseDups.map fun x => (firstAttr as xs x, enc x))) = xs.eraseDups.map enc := hren
  -- the value at `enc y` of the renamed restriction of `u` is `u`'s value at `(firstAttr as xs) y`
  have K : ∀ u : Tuple, u.Fits (headerOf D as) → ∀ y ∈ xs.eraseDups,
      asg (Finrel.renameTuple (xs.eraseDups.map fun x => (firstAttr as xs x, enc x)) (u.restrict (xs.eraseDups.map (firstAttr as xs)))) y = readAsg u ((firstAttr as xs) y) := by
    intro u fu y hy
    have ft' := fits_restrict_any fu (bs := xs.eraseDups.map (firstAttr as xs)) (fun b hb => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb; exact hfam x (hmem x hx))
    simp only [asg, readAsg]
    rw [← hra y hy, get?_renameTuple ft' hinjR (List.mem_map_of_mem hy), get?_restrict,
      if_pos (List.mem_map_of_mem hy)]
  simp only [atomE, hat]
  rw [show ((as.zip xs).map fun p => Test.eqA p.1 ((firstAttr as xs) p.2)) =
      (((as.zip xs).map fun p => (p.1, (firstAttr as xs) p.2)).map fun p => Test.eqA p.1 p.2) by
    simp [List.map_map, Function.comp_def]]
  refine e4.congr fun t ft => ?_
  simp only [Sat, AtomHolds, hat, tuplesOf_eq hr, List.mem_map]
  constructor
  · rintro ⟨t', ft', ⟨u, fu, ⟨hu, htest⟩, rfl⟩, rfl⟩
    have hv : ∀ x ∈ xs, u.get? ((firstAttr as xs) x) = some (asg (Finrel.renameTuple (xs.eraseDups.map fun x => (firstAttr as xs x, enc x)) (u.restrict (xs.eraseDups.map (firstAttr as xs)))) x) := by
      intro x hx
      rw [K u fu x (List.mem_eraseDups.mpr hx)]
      obtain ⟨v, hv, -⟩ := get?_fits fu (hfam x hx)
      simp [readAsg, hv]
    refine ⟨fun y hy => ?_, u, hu, fun q hq => ?_⟩
    · rw [K u fu y hy]
      obtain ⟨v, hv, -, hpv⟩ := get?_fits fu (hfam y (hmem y hy))
      simp only [readAsg, hv, Option.getD_some]
      exact List.mem_append_left _ (mem_adom hp (by rw [tuplesOf_eq hr]; exact hu) hpv)
    · rw [htest (q.1, (firstAttr as xs) q.2) ⟨q, hq, rfl⟩]
      exact hv q.2 (List.of_mem_zip hq).2
  · rintro ⟨-, u, hu, hm⟩
    have fu := fits_of_mem hw hh hu
    have ft' := fits_restrict_any fu (bs := xs.eraseDups.map (firstAttr as xs)) (fun b hb => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb; exact hfam x (hmem x hx))
    refine ⟨u.restrict (xs.eraseDups.map (firstAttr as xs)), ft', ⟨u, fu, ⟨hu, ?_⟩, rfl⟩, ?_⟩
    · rintro p ⟨q, hq, rfl⟩
      rw [hm q hq, hm ((firstAttr as xs) q.2, q.2) (hfaz q.2 (List.of_mem_zip hq).2)]
    · have fr := fits_renameTuple ft' hinjR
      rw [hmapR] at fr
      apply eq_of_asg fr ft
      intro y hy
      rw [K u fu y hy]
      simp [readAsg, hm ((firstAttr as xs) y, y) (hfaz y (hmem y hy))]

theorem V_sub {φ : Formula} {W : List String} (h : ∀ x, x ∈ W ↔ x ∈ φ.fv) :
    ∀ x, x ∈ W ↔ x ∈ V φ := fun x => (h x).trans mem_V.symm

/-- **The induction.** `ra φ` holds the assignments from the active domain that satisfy
`φ`, over its free variables. -/
theorem ev_ra (henv : Conforms S D env) (hS : S.WF) (hD : DomOK D = true)
    (hC : ∀ c ∈ C, D.mem c = true) :
    (φ : Formula) → φ.WT S = true → (∀ c ∈ φ.consts, c ∈ C) →
      AsgRep S D env C (ra S C φ) (V φ) (Sat (· ∈ AD S env C) S env φ)
  | .rel n xs, hwt, _ => by
    simp only [ra]
    exact (a_atom henv hS hD hwt).congrW fun x => by simp [V, Formula.fv]
  | .eqv x y, _, _ => by
    by_cases e : x = y
    · subst e
      simp only [ra, if_pos rfl]
      refine ((a_adE1 henv hC x).congrW fun z => by simp [V, Formula.fv]).congrG fun ρ _ => ?_
      simp [Sat]
    · simp only [ra, if_neg e]
      have hp := a_prod (a_adE1 henv hC x) (a_adE1 henv hC y) (fun _ _ _ => Iff.rfl)
        (fun _ _ _ => Iff.rfl) (by simpa using Ne.symm e)
      have hs := a_selEq hD hp (x := x) (y := y) (by simp) (by simp)
      refine (hs.congrW fun z => by simp [V, Formula.fv]).congrG fun ρ _ => ?_
      simp [Sat]
  | .eqc x c, _, hc => by
    simp only [ra]
    have hcA : c ∈ AD S env C := List.mem_append_right _ (hc c (by simp [Formula.consts]))
    have h := ev_litVals (env := env) (a := enc x) (vs := [c]) (by
      intro v hv; simp only [List.mem_singleton] at hv; subst hv
      exact AD_mem_D henv hC hcA)
    refine (h.congrH (as := [enc x]) (bs := (V (.eqc x c)).map enc) fun a => by
      simp [V, Formula.fv, eq_comm]).congr fun t _ => ?_
    simp only [V, Formula.fv, List.eraseDups_cons, List.eraseDups_nil, List.filter_nil,
      List.mem_singleton, forall_eq, Sat, asg]
    constructor
    · intro h; rw [h]; exact ⟨hcA, rfl⟩
    · rintro ⟨-, h⟩; exact h
  | .cmpv o x y, _, _ => by
    by_cases e : x = y
    · subst e
      simp only [ra, if_pos rfl]
      have hs := a_selCmpA hD (a_adE1 henv hC x) o (x := x) (y := x) (by simp) (by simp)
      refine (hs.congrW fun z => by simp [V, Formula.fv]).congrG fun ρ _ => ?_
      simp [Sat]
    · simp only [ra, if_neg e]
      have hp := a_prod (a_adE1 henv hC x) (a_adE1 henv hC y) (fun _ _ _ => Iff.rfl)
        (fun _ _ _ => Iff.rfl) (by simpa using Ne.symm e)
      have hs := a_selCmpA hD hp o (x := x) (y := y) (by simp) (by simp)
      refine (hs.congrW fun z => by simp [V, Formula.fv]).congrG fun ρ _ => ?_
      simp [Sat]
  | .cmpc o x c, _, hc => by
    simp only [ra]
    have hcD : D.mem c = true := hC c (hc c (by simp [Formula.consts]))
    have hs := a_selCmpC hD (a_adE1 henv hC x) o (x := x) (by simp) hcD
    refine (hs.congrW fun z => by simp [V, Formula.fv]).congrG fun ρ _ => ?_
    simp [Sat]
  | .not φ, hwt, hc => by
    have ih := ev_ra henv hS hD hC φ hwt hc
    simp only [ra]
    exact ((a_union (a_adV henv hC (nodup_V φ)) ih fun _ => Iff.rfl).2).congrG fun ρ _ => by
      simp [Sat]
  | .and φ ψ, hwt, hc => by
    simp only [Formula.WT, Bool.and_eq_true] at hwt
    have ih1 := ev_ra henv hS hD hC φ hwt.1 fun c h => hc c (by simp [Formula.consts, h])
    have ih2 := ev_ra henv hS hD hC ψ hwt.2 fun c h => hc c (by simp [Formula.consts, h])
    simp only [ra]
    refine (a_join ih1 ih2 (loc_sat φ fun x h => mem_V.mpr h)
      (loc_sat ψ fun x h => mem_V.mpr h)).congrW fun x => ?_
    simp only [List.mem_append, List.mem_filter, mem_V, Formula.fv, List.contains_iff_mem]
    by_cases h : x ∈ φ.fv <;> simp [h, mem_V]
  | .or φ ψ, hwt, hc => by
    simp only [Formula.WT, Bool.and_eq_true] at hwt
    have ih1 := ev_ra henv hS hD hC φ hwt.1 fun c h => hc c (by simp [Formula.consts, h])
    have ih2 := ev_ra henv hS hD hC ψ hwt.2 fun c h => hc c (by simp [Formula.consts, h])
    have p1 := a_pad henv hC ih1 (loc_sat φ fun x h => mem_V.mpr h)
      (nodup_diffL (nodup_V ψ)) (ys := diffL (V ψ) (V φ)) fun y hy => (mem_diffL.mp hy).2
    have p2 := a_pad henv hC ih2 (loc_sat ψ fun x h => mem_V.mpr h)
      (nodup_diffL (nodup_V φ)) (ys := diffL (V φ) (V ψ)) fun y hy => (mem_diffL.mp hy).2
    have hs : ∀ x, x ∈ V φ ++ diffL (V ψ) (V φ) ↔ x ∈ V ψ ++ diffL (V φ) (V ψ) := fun x => by
      simp only [List.mem_append, mem_diffL]
      by_cases h1 : x ∈ V φ <;> by_cases h2 : x ∈ V ψ <;> simp [h1, h2]
    simp only [ra]
    refine (a_union p1 p2 hs).1.congrW fun x => ?_
    simp only [List.mem_append, mem_diffL, mem_V, Formula.fv]
    by_cases h : x ∈ φ.fv <;> simp [h]
  | .ex x φ, hwt, hc => by
    have ih := ev_ra henv hS hD hC φ hwt hc
    have hex : (extra x φ).Nodup := by unfold extra; split <;> simp
    have p := a_pad henv hC ih (loc_sat φ fun x h => mem_V.mpr h) hex (ys := extra x φ)
      fun y hy hyV => (mem_extra.mp hy).2 ((mem_extra.mp hy).1 ▸ hyV)
    have hW : (V φ ++ extra x φ).Nodup := nodup_append_of (nodup_V φ) hex
      fun y hy hyV => (mem_extra.mp hy).2 ((mem_extra.mp hy).1 ▸ hyV)
    have hx : x ∈ V φ ++ extra x φ := by
      by_cases h : x ∈ V φ
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (mem_extra.mpr ⟨rfl, h⟩)
    have hmemZ : ∀ y, y ∈ V (.ex x φ) ↔ y ∈ φ.fv ∧ y ≠ x := fun y => by
      simp [mem_V, Formula.fv, List.mem_filter]
    have pr := a_projEx henv hC p (loc_sat φ fun y h => List.mem_append_left _ (mem_V.mpr h)) hW
      (nodup_V _) (Z := V (.ex x φ)) (x := x)
      (fun z hz => List.mem_append_left _ (mem_V.mpr ((hmemZ z).mp hz).1)) hx
      (fun h => ((hmemZ x).mp h).2 rfl)
      (fun y hy => by
        rcases List.mem_append.mp hy with h | h
        · by_cases e : y = x
          · exact Or.inl e
          · exact Or.inr ((hmemZ y).mpr ⟨mem_V.mp h, e⟩)
        · exact Or.inl (mem_extra.mp h).1)
    simp only [ra]
    exact pr.congrG fun ρ _ => by simp [Sat]
  | .all x φ, hwt, hc => by
    have ih := ev_ra henv hS hD hC φ hwt hc
    have hex : (extra x φ).Nodup := by unfold extra; split <;> simp
    have hd : ∀ y ∈ extra x φ, y ∉ V φ := fun y hy hyV => (mem_extra.mp hy).2 ((mem_extra.mp hy).1 ▸ hyV)
    have p := a_pad henv hC ih (loc_sat φ fun x h => mem_V.mpr h) hex hd
    have hW : (V φ ++ extra x φ).Nodup := nodup_append_of (nodup_V φ) hex hd
    have inner := (a_union (a_adV henv hC hW) p fun _ => Iff.rfl).2
    have hx : x ∈ V φ ++ extra x φ := by
      by_cases h : x ∈ V φ
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (mem_extra.mpr ⟨rfl, h⟩)
    have hmemZ : ∀ y, y ∈ V (.all x φ) ↔ y ∈ φ.fv ∧ y ≠ x := fun y => by
      simp [mem_V, Formula.fv, List.mem_filter]
    have hloc : Loc (V φ ++ extra x φ) (fun ρ => True ∧ ¬ Sat (· ∈ AD S env C) S env φ ρ) :=
      fun ρ ρ' e => by
        simp only [true_and]
        rw [loc_sat (S := S) (env := env) (C := C) φ
          (fun y h => List.mem_append_left _ (mem_V.mpr h)) ρ ρ' e]
    have pr := a_projEx henv hC inner hloc hW (nodup_V _) (Z := V (.all x φ)) (x := x)
      (fun z hz => List.mem_append_left _ (mem_V.mpr ((hmemZ z).mp hz).1)) hx
      (fun h => ((hmemZ x).mp h).2 rfl)
      (fun y hy => by
        rcases List.mem_append.mp hy with h | h
        · by_cases e : y = x
          · exact Or.inl e
          · exact Or.inr ((hmemZ y).mpr ⟨mem_V.mp h, e⟩)
        · exact Or.inl (mem_extra.mp h).1)
    simp only [ra]
    refine (a_union (a_adV henv hC (nodup_V _)) pr fun _ => Iff.rfl).2.congrG fun ρ _ => ?_
    simp only [Sat, true_and]
    constructor
    · intro h a ha
      exact Classical.byContradiction fun hn => h ⟨a, ha, hn⟩
    · intro h ⟨a, ha, hn⟩; exact hn (h a ha)

end Formulas

/-! ## The output heading -/

section Output
variable {S : Schema} {D : Domain} {env : Env} {C : List Value}

theorem restrict_restrict {as bs : List String} (h : ∀ a ∈ as, a ∈ bs) (t : Tuple) :
    (t.restrict bs).restrict as = t.restrict as := by
  simp only [Tuple.restrict, List.filter_filter]
  apply List.filter_congr
  intro p _
  by_cases ha : p.1 ∈ as
  · simp [List.contains_iff_mem, ha, h _ ha]
  · simp [List.contains_iff_mem, ha]

theorem restrict_self {as : List String} {t : Tuple} (f : t.Fits (headerOf D as)) :
    t.restrict as = t := by
  apply List.filter_eq_self.mpr
  intro p hp
  have : p.1 ∈ as := by rw [← attrs_headerOf D as, ← f.attrs]; exact List.mem_map_of_mem hp
  simp [List.contains_iff_mem, this]

theorem keys_cpyX : ∀ {i : Nat} {ps : List (String × String)},
    (cpyX i ps).map (·.1) = (cpyL i ps).map (·.1)
  | _, [] => rfl
  | i, (a, x) :: ps => by simp only [cpyX, cpyL, List.map_cons, keys_cpyX]

theorem ev_copies (hD : DomOK D = true) (henv : Conforms S D env) (hC : ∀ c ∈ C, D.mem c = true) :
    ∀ {i : Nat} {ps : List (String × String)} {e : CRA} {as : List String} {P : Tuple → Prop},
      EvRep env D e as P → (∀ p ∈ ps, enc p.2 ∈ as) → (∀ j, i ≤ j → cpy j ∉ as) →
      EvRep env D (copies S C i ps e) (as ++ (cpyL i ps).map (·.1))
        (fun t => P (t.restrict as) ∧ (∀ p ∈ cpyX i ps, t.get? p.1 = t.get? (enc p.2)) ∧
          ∀ p ∈ cpyX i ps, readAsg t p.1 ∈ AD S env C)
  | _, [], e, as, P, he, _, _ => by
    simp only [copies, cpyL, cpyX, List.map_nil, List.append_nil]
    refine he.congr fun t f => ?_
    simp only [List.not_mem_nil, false_imp_iff, implies_true, and_true]
    rw [restrict_self f]
  | i, (a, x) :: ps, e, as, P, he, hx, hc => by
    simp only [copies, cpyL, cpyX, List.map_cons]
    have hp := ev_prod he (ev_adE (a := cpy i) henv hC) (by
      intro b hb; simp only [List.mem_singleton] at hb; subst hb; exact hc i (Nat.le_refl _))
    have hs := ev_selA hD hp (List.mem_append_right _ (List.mem_singleton_self _))
      (List.mem_append_left _ (hx (a, x) List.mem_cons_self))
    have ih := ev_copies hD henv hC (i := i + 1) (ps := ps) hs
      (fun p hp => List.mem_append_left _ (hx p (List.mem_cons_of_mem _ hp)))
      (fun j hj h => by
        rcases List.mem_append.mp h with h | h
        · exact hc j (by omega) h
        · simp only [List.mem_singleton] at h; have := cpy_inj h; omega)
    rw [List.append_assoc] at ih
    refine ih.congr fun t _ => ?_
    have hsub : ∀ b ∈ as, b ∈ as ++ [cpy i] := fun b h => List.mem_append_left _ h
    have hci : cpy i ∈ as ++ [cpy i] := List.mem_append_right _ (List.mem_singleton_self _)
    have hxi : enc x ∈ as ++ [cpy i] := List.mem_append_left _ (hx (a, x) List.mem_cons_self)
    rw [restrict_restrict hsub, readAsg_restrict (List.mem_singleton_self _),
      readAsg_restrict hci, get?_restrict, if_pos hci, get?_restrict, if_pos hxi]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩; exact ⟨h1, ⟨h3, h4⟩, h2, h5⟩
    · rintro ⟨h1, ⟨h3, h4⟩, h2, h5⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩

theorem cpy_pair : ∀ {i : Nat} {ps : List (String × String)} {p : String × String}, p ∈ ps →
    ∃ c, (c, p.1) ∈ cpyL i ps ∧ (c, p.2) ∈ cpyX i ps
  | _, [], _, h => by cases h
  | i, (a, x) :: ps, p, h => by
    simp only [cpyL, cpyX, List.mem_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨cpy i, Or.inl rfl, Or.inl rfl⟩
    · obtain ⟨c, h1, h2⟩ := cpy_pair (i := i + 1) h
      exact ⟨c, Or.inr h1, Or.inr h2⟩

theorem inj_of_nodup_snd : ∀ {l : List (String × String)}, (l.map (·.2)).Nodup →
    ∀ {c c' a : String}, (c, a) ∈ l → (c', a) ∈ l → c = c'
  | [], _, _, _, _, h, _ => by cases h
  | (d, b) :: l, hn, c, c', a, h1, h2 => by
    have hn' := List.nodup_cons.mp hn
    simp only [List.mem_cons, Prod.mk.injEq] at h1 h2
    rcases h1 with ⟨rfl, rfl⟩ | h1 <;> rcases h2 with ⟨rfl, e⟩ | h2
    · rfl
    · exact absurd (List.mem_map_of_mem (f := (·.2)) h2) hn'.1
    · exact absurd (e ▸ List.mem_map_of_mem (f := (·.2)) h1) hn'.1
    · exact inj_of_nodup_snd hn'.2 h1 h2

theorem fits_ofPairs {ps : List (String × Value)} (hn : (ps.map (·.1)).Nodup)
    (hd : ∀ p ∈ ps, D.mem p.2 = true) : (Tuple.ofPairs ps).Fits (headerOf D (ps.map (·.1))) where
  sorted := ofPairs_sorted hn
  attrs a := by rw [attrs_ofPairs, attrs_headerOf]
  dom p hp d hd' := by
    rw [mem_ofPairs] at hp
    rw [lookup_headerOf, if_pos (List.mem_map_of_mem hp)] at hd'
    cases hd'; exact hd p hp

theorem eq_of_get? {as : List String} {t t' : Tuple} (ft : t.Fits (headerOf D as))
    (ft' : t'.Fits (headerOf D as)) (h : ∀ a ∈ as, t.get? a = t'.get? a) : t = t' := by
  apply Tuple.ext_get? ft.sorted ft'.sorted
  intro a
  by_cases ha : a ∈ as
  · exact h a ha
  · rw [ft.get?_none (by rw [attrs_headerOf]; exact ha), ft'.get?_none (by rw [attrs_headerOf]; exact ha)]

/-- After the last ρ, output attribute `a` holds the value of its copy. -/
theorem get?_output {out : List (String × String)} (hon : (out.map (·.1)).Nodup) {as : List String}
    {u : Tuple} (fu : u.Fits (headerOf D as)) (hsub : ∀ c ∈ (cpyL 0 out).map (·.1), c ∈ as)
    {c a : String} (hc : (c, a) ∈ cpyL 0 out) :
    (Finrel.renameTuple (cpyL 0 out) (u.restrict ((cpyL 0 out).map (·.1)))).get? a = u.get? c := by
  have ft' := fits_restrict_any fu hsub
  have hsnd : ((cpyL 0 out).map (·.2)).Nodup := by rw [cpyL_snd]; exact hon
  have hra : ∀ p ∈ cpyL 0 out, Finrel.renameAttr (cpyL 0 out) p.1 = p.2 := fun p hp => by
    simp [Finrel.renameAttr, lookup_of_mem' nodup_cpyL hp]
  have hinj : ∀ x ∈ (cpyL 0 out).map (·.1), ∀ y ∈ (cpyL 0 out).map (·.1),
      Finrel.renameAttr (cpyL 0 out) x = Finrel.renameAttr (cpyL 0 out) y → x = y := by
    intro x hx y hy e
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hy
    rw [hra p hp, hra p' hp'] at e
    exact inj_of_nodup_snd hsnd (c := p.1) (a := p.2) hp (e ▸ hp')
  have hcm : c ∈ (cpyL 0 out).map (·.1) := List.mem_map_of_mem (f := (·.1)) hc
  have e : Finrel.renameAttr (cpyL 0 out) c = a := hra (c, a) hc
  rw [← e, get?_renameTuple ft' hinj hcm, get?_restrict, if_pos hcm]

theorem get?_enc_asg {as : List String} {u : Tuple} (f : u.Fits (headerOf D as)) {x : String}
    (hx : enc x ∈ as) : u.get? (enc x) = some (asg u x) := by
  obtain ⟨v, hv, -⟩ := get?_fits f hx
  simp [asg, readAsg, hv]

theorem mem_cpyX_snd : ∀ {i : Nat} {ps : List (String × String)} {p : String × String},
    p ∈ cpyX i ps → p.2 ∈ ps.map (·.2)
  | _, [], _, h => by cases h
  | i, (a, x) :: ps, p, h => by
    simp only [cpyX, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_cpyX_snd (i := i + 1) h)

theorem get?_ofPairs_mem {ps : List (String × Value)} (hn : (ps.map (·.1)).Nodup)
    {a : String} {v : Value} (h : (a, v) ∈ ps) : (Tuple.ofPairs ps).get? a = some v := by
  rw [Tuple.get?_ofPairs hn]; exact lookup_of_mem' hn h

/-- The output tuple of an assignment, attribute by attribute. -/
theorem get?_tupleOf {q : Query} (hon : (q.out.map (·.1)).Nodup) (ρ : String → Value)
    {p : String × String} (hp : p ∈ q.out) : (q.tupleOf ρ).get? p.1 = some (ρ p.2) := by
  refine get?_ofPairs_mem (by simpa [List.map_map, Function.comp_def] using hon) ?_
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

theorem fits_tupleOf {q : Query} (hon : (q.out.map (·.1)).Nodup) {ρ : String → Value}
    (hd : ∀ p ∈ q.out, D.mem (ρ p.2) = true) :
    (q.tupleOf ρ).Fits (headerOf D (q.out.map (·.1))) := by
  have h := fits_ofPairs (D := D) (ps := q.out.map fun p => (p.1, ρ p.2))
    (by simpa [List.map_map, Function.comp_def] using hon)
    (fun p hp => by obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp; exact hd p' hp')
  simpa [Query.tupleOf, List.map_map, Function.comp_def] using h

end Output

/-! ## Theorem B -/

/-- **Theorem B** (calculus to algebra). Every well-typed calculus query has an algebra
query, itself well typed, that Rasso's evaluator runs on every database of the schema
without refusing, giving a well-formed relation with the query's output heading whose
tuples are exactly the query's active-domain answers. The algebra query is the same for
every database: it computes the active domain from the stored relations and the query's
constants. -/
theorem calculus_to_algebra {S : Schema} {D : Domain} (hS : S.WF) (hD : DomOK D = true)
    {q : Query} (hq : q.WT S D) :
    (q.toRA S).check S D = some (q.out.map (·.1)) ∧
    ∀ env, Conforms S D env →
      ∃ r, Expr.eval env [] ((q.toRA S).toExpr D) = .ok (.finrel r) ∧ r.WF ∧
        (∀ a, r.heading.lookup a = (headerOf D (q.out.map (·.1))).lookup a) ∧
        ∀ t, t ∈ r.tuples ↔ q.answers (· ∈ q.adom S env) S env t := by
  refine ⟨check_toRA hS hq, fun env henv => ?_⟩
  obtain ⟨hwt, hcD, hon, -, hfv⟩ := hq
  have hC : ∀ c ∈ q.body.consts, D.mem c = true := hcD
  -- the variables after padding: the body's, then the other output variables
  have hy : (diffL q.vars.eraseDups (V q.body)).Nodup := nodup_diffL (nodup_eraseDups q.vars)
  have hyd : ∀ y ∈ diffL q.vars.eraseDups (V q.body), y ∉ V q.body := fun y h => (mem_diffL.mp h).2
  have hWn : (V q.body ++ diffL q.vars.eraseDups (V q.body)).Nodup :=
    nodup_append_of (nodup_V _) hy hyd
  have hvW : ∀ x ∈ q.vars, x ∈ V q.body ++ diffL q.vars.eraseDups (V q.body) := fun x hx => by
    by_cases h : x ∈ V q.body
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (mem_diffL.mpr ⟨List.mem_eraseDups.mpr hx, h⟩)
  have hWv : ∀ x ∈ V q.body ++ diffL q.vars.eraseDups (V q.body), x ∈ q.vars := fun x hx => by
    rcases List.mem_append.mp hx with h | h
    · exact hfv x (mem_V.mp h)
    · exact List.mem_eraseDups.mp (mem_diffL.mp h).1
  have hfW : ∀ x ∈ q.body.fv, x ∈ V q.body ++ diffL q.vars.eraseDups (V q.body) :=
    fun x hx => List.mem_append_left _ (mem_V.mpr hx)
  have h1 := a_pad henv hC (ev_ra henv hS hD hC q.body hwt fun c h => h)
    (loc_sat q.body fun x hx => mem_V.mpr hx) hy hyd
  have hencW : ∀ p ∈ q.out, enc p.2 ∈ (V q.body ++ diffL q.vars.eraseDups (V q.body)).map enc :=
    fun p hp => List.mem_map_of_mem (hvW p.2 (List.mem_map_of_mem hp))
  have h2 := ev_copies hD henv hC (i := 0) (ps := q.out) h1 hencW
    (fun j _ h => by obtain ⟨y, _, e⟩ := List.mem_map.mp h; exact enc_ne_cpy y j e)
  have h3 := ev_proj h2 (fun b hb => List.mem_append_right _ hb) nodup_cpyL
  have h4 := ev_ren h3 (ren := cpyL 0 q.out) (fun p hp => List.mem_map_of_mem hp)
    (by rw [renamed_self nodup_cpyL, cpyL_snd]; exact hon)
  rw [renamed_self nodup_cpyL, cpyL_snd] at h4
  obtain ⟨r, hev, rr⟩ := h4
  refine ⟨r, hev, rr.wf, rr.head, fun t => (rr.mem t).trans ?_⟩
  -- the names used below
  have hcs : ∀ c ∈ (cpyL 0 q.out).map (·.1),
      c ∈ (V q.body ++ diffL q.vars.eraseDups (V q.body)).map enc ++ (cpyL 0 q.out).map (·.1) :=
    fun c hc => List.mem_append_right _ hc
  have hAD : ∀ {v}, v ∈ AD S env q.body.consts → D.mem v = true := fun hv => AD_mem_D henv hC hv
  constructor
  · rintro ⟨ft, u', -, ⟨u, fu, ⟨⟨hval, hsat⟩, hcp, -⟩, rfl⟩, rfl⟩
    have hasg : ∀ y ∈ V q.body ++ diffL q.vars.eraseDups (V q.body),
        asg (u.restrict ((V q.body ++ diffL q.vars.eraseDups (V q.body)).map enc)) y = asg u y :=
      fun y hy => asg_restrict (List.mem_map_of_mem hy) u
    refine ⟨asg u, fun x hx => ?_, ?_, ?_⟩
    · rw [← hasg x (hvW x hx)]; exact hval x (hvW x hx)
    · refine eq_of_get? ft (fits_tupleOf hon fun p hp => ?_) fun a ha => ?_
      · have hx := hvW p.2 (List.mem_map_of_mem hp)
        exact hAD (hasg p.2 hx ▸ hval p.2 hx)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
        obtain ⟨c, hc1, hc2⟩ := cpy_pair (i := 0) hp
        rw [get?_output hon fu hcs hc1, hcp _ hc2, get?_tupleOf hon _ hp,
          get?_enc_asg fu (List.mem_append_left _ (hencW p hp))]
    · exact (Sat_congr q.body fun x hx => hasg x (hfW x hx)).mp hsat
  · rintro ⟨ρ, hρ, rfl, hsat⟩
    let ps := (V q.body ++ diffL q.vars.eraseDups (V q.body)).map (fun y => (enc y, ρ y)) ++
      (cpyX 0 q.out).map (fun p => (p.1, ρ p.2))
    have hkeys : ps.map (·.1) =
        (V q.body ++ diffL q.vars.eraseDups (V q.body)).map enc ++ (cpyL 0 q.out).map (·.1) := by
      simp only [ps, List.map_append, List.map_map, Function.comp_def]
      rw [← keys_cpyX]
    have hpn : (ps.map (·.1)).Nodup := by
      rw [hkeys]
      exact nodup_append_of (nodup_map_enc hWn) nodup_cpyL fun c hc h => by
        obtain ⟨j, -, rfl⟩ := mem_cpyL_fst hc
        obtain ⟨y, _, e⟩ := List.mem_map.mp h; exact enc_ne_cpy y j e
    have hpd : ∀ p ∈ ps, D.mem p.2 = true := fun p hp => by
      rcases List.mem_append.mp hp with h | h
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h; exact hAD (hρ y (hWv y hy))
      · obtain ⟨p', hp', rfl⟩ := List.mem_map.mp h
        exact hAD (hρ p'.2 (mem_cpyX_snd hp'))
    have fu := fits_ofPairs hpn hpd
    rw [hkeys] at fu
    have hget : ∀ y ∈ V q.body ++ diffL q.vars.eraseDups (V q.body),
        (Tuple.ofPairs ps).get? (enc y) = some (ρ y) := fun y hy =>
      get?_ofPairs_mem hpn (List.mem_append_left _ (List.mem_map.mpr ⟨y, hy, rfl⟩))
    have hgetc : ∀ p ∈ cpyX 0 q.out, (Tuple.ofPairs ps).get? p.1 = some (ρ p.2) := fun p hp =>
      get?_ofPairs_mem hpn (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
    have hasg : ∀ y ∈ V q.body ++ diffL q.vars.eraseDups (V q.body),
        asg ((Tuple.ofPairs ps).restrict
          ((V q.body ++ diffL q.vars.eraseDups (V q.body)).map enc)) y = ρ y := fun y hy => by
      rw [asg_restrict (List.mem_map_of_mem hy)]
      simp [asg, readAsg, hget y hy]
    have ft := fits_tupleOf (q := q) hon (ρ := ρ) fun p hp => hAD (hρ p.2 (List.mem_map_of_mem hp))
    refine ⟨ft, _, fits_restrict_any fu fun c hc => hcs c hc,
      ⟨Tuple.ofPairs ps, fu, ⟨⟨fun y hy => ?_, ?_⟩, fun p hp => ?_, fun p hp => ?_⟩, rfl⟩, ?_⟩
    · rw [hasg y hy]; exact hρ y (hWv y hy)
    · exact (Sat_congr q.body fun x hx => hasg x (hfW x hx)).mpr hsat
    · rw [hgetc p hp, hget p.2 (hvW p.2 (mem_cpyX_snd hp))]
    · simp [readAsg, hgetc p hp]; exact hρ p.2 (mem_cpyX_snd hp)
    · have hinj : ∀ x ∈ (cpyL 0 q.out).map (·.1), ∀ y ∈ (cpyL 0 q.out).map (·.1),
          Finrel.renameAttr (cpyL 0 q.out) x = Finrel.renameAttr (cpyL 0 q.out) y → x = y := by
        intro x hx y hy e
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hy
        have hra : ∀ p ∈ cpyL 0 q.out, Finrel.renameAttr (cpyL 0 q.out) p.1 = p.2 := fun p hp => by
          simp [Finrel.renameAttr, lookup_of_mem' nodup_cpyL hp]
        have hsnd : ((cpyL 0 q.out).map (·.2)).Nodup := by rw [cpyL_snd]; exact hon
        rw [hra p hp, hra p' hp'] at e
        exact inj_of_nodup_snd hsnd (c := p.1) (a := p.2) hp (e ▸ hp')
      have fr := fits_renameTuple (fits_restrict_any fu fun c hc => hcs c hc) hinj
      have hren : (cpyL 0 q.out |>.map (·.1)).map (Finrel.renameAttr (cpyL 0 q.out)) =
          q.out.map (·.1) := by
        have h := renamed_self (l := cpyL 0 q.out) nodup_cpyL; rw [cpyL_snd] at h; exact h
      rw [hren] at fr
      refine eq_of_get? fr ft fun a ha => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      obtain ⟨c, hc1, hc2⟩ := cpy_pair (i := 0) hp
      rw [get?_output hon fu hcs hc1, hgetc _ hc2, get?_tupleOf hon _ hp]

end Coddstheorem
