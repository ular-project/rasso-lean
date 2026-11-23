/-!
# Function spaces, not powersets (plain types)

Why Rasso builds solution sets on the function space `Decision ^ Data` (the relations
`R ⊆ Data × Decision` that are total and functional) rather than on the whole powerset
`𝒫(Data × Decision)`. Blueprint chapter "Why function spaces". The same counts on
Rasso's own solution sets are checked in `Rasso/FunctionSpaceExamples.lean`; that
candidates of ω_sol are graphs of total functions is `Rasso.mem_omegaSolCandidates`.

This file works with plain Lean types (`α` for data, `β` for decisions), so that each
claim is stated once, without heading bookkeeping. It uses core Lean only, and no
`sorry`.

## Conventions

* **Relations as Bool-valued functions.** A (decidable) subset of `α` is a function
  `α → Bool`, so a relation `R ⊆ α × β` is `α → β → Bool`. Every finite and every
  unrestricted relation in Rasso has decidable membership, so nothing is lost. The
  Prop-valued powerset `α → Prop` is only used to show where choice enters (`ofPropRel`).
* **"+1 attribute"**: the powerset and multisets are recoverable from
  the function space by adding one attribute. Read as: move the decision attributes into
  the data and add one new decision attribute, of kind `bool` for subsets and a count for
  multiplicities. So `𝒫(A × D) ≅ Bool ^ (A × D)` and `Multiset(A × D) ≅ Nat ^ (A × D)`
  (finite support). A second "+1" is `Option`: partial functions `A ⇀ D` are
  `(D + 1) ^ A`.
* **A small `Iso`.** Core has no `Equiv`, so `Iso` is a four-field structure with the two
  inverse laws.
-/

namespace Rasso.FunctionSpace

/-! ## 0. Isomorphisms of types -/

/-- A bijection, given by maps both ways that are mutually inverse. -/
structure Iso (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-! ## 1. The graph of a function is a total, functional relation -/

variable {α β : Type}

/-- A relation as a two-place Boolean function: the decidable powerset of `α × β`. -/
abbrev BRel (α β : Type) := α → β → Bool

/-- Every `a` is related to at least one `b`. -/
def Total (R : BRel α β) : Prop := ∀ a, ∃ b, R a b = true

/-- Every `a` is related to at most one `b`. -/
def Functional (R : BRel α β) : Prop := ∀ a b b', R a b = true → R a b' = true → b = b'

/-- The graph of `f`, as a relation. -/
def graph [DecidableEq β] (f : α → β) : BRel α β := fun a b => decide (f a = b)

@[simp] theorem graph_apply [DecidableEq β] (f : α → β) (a : α) (b : β) :
    graph f a b = true ↔ f a = b := by simp [graph]

theorem graph_total [DecidableEq β] (f : α → β) : Total (graph f) :=
  fun a => ⟨f a, by simp⟩

theorem graph_functional [DecidableEq β] (f : α → β) : Functional (graph f) :=
  fun a b b' h h' => by
    rw [graph_apply] at h h'
    exact h ▸ h'

/-- Different functions have different graphs: the function space embeds in the
powerset. -/
theorem graph_injective [DecidableEq β] {f g : α → β} (e : graph f = graph g) : f = g :=
  funext fun a => by
    have : graph g a (f a) = true := e ▸ (graph_apply f a (f a)).2 rfl
    exact ((graph_apply g a (f a)).1 this).symm

/-- **The order on graphs is discrete.** One total function's graph is inside another's
only when they are equal. So the function space, ordered by `⊆`, is an antichain: it
has no ⊥, no ⊤, and no meets or joins of distinct elements. -/
theorem graph_le_graph [DecidableEq β] {f g : α → β}
    (le : ∀ a b, graph f a b = true → graph g a b = true) : f = g :=
  funext fun a => ((graph_apply g a (f a)).1 (le a (f a) ((graph_apply f a (f a)).2 rfl))).symm

/-- **The union of two graphs is not a graph** (when the functions differ somewhere):
the function space is not closed under `∪`. -/
theorem union_graph_not_functional [DecidableEq β] {f g : α → β} {a : α} (ne : f a ≠ g a) :
    ¬ Functional (fun x y => graph f x y || graph g x y) := fun F =>
  ne (F a (f a) (g a) (by simp) (by simp))

/-! ## 2. From a total functional relation back to a function, without choice

When the decisions can be listed (a list `bs` that contains every `b`) and the relation
is decidable (it is `Bool`-valued here), the function is computed by search. This is the
situation of a `Finrel` candidate: decisions are looked up, never chosen. -/

/-- The function read off a total relation by searching a covering list. -/
def ofRel (bs : List β) (cover : ∀ b, b ∈ bs) (R : BRel α β) (tot : Total R) : α → β :=
  fun a => (bs.find? (R a)).get (by
    obtain ⟨b, hb⟩ := tot a
    exact List.find?_isSome.2 ⟨b, cover b, hb⟩)

theorem ofRel_spec (bs : List β) (cover : ∀ b, b ∈ bs) (R : BRel α β) (tot : Total R) (a : α) :
    R a (ofRel bs cover R tot a) = true := by
  unfold ofRel
  exact List.find?_some (Option.get_mem _)

/-- A total functional relation is the graph of the function read off it. -/
theorem graph_ofRel [DecidableEq β] (bs : List β) (cover : ∀ b, b ∈ bs) (R : BRel α β)
    (tot : Total R) (fn : Functional R) : graph (ofRel bs cover R tot) = R :=
  funext fun a => funext fun b => by
    have h := ofRel_spec bs cover R tot a
    cases hR : R a b with
    | true => exact (graph_apply _ a b).2 (fn a _ _ h hR)
    | false =>
      cases hg : graph (ofRel bs cover R tot) a b with
      | false => rfl
      | true => rw [graph_apply] at hg; rw [hg] at h; rw [h] at hR; cases hR

theorem ofRel_graph [DecidableEq β] (bs : List β) (cover : ∀ b, b ∈ bs) (f : α → β) :
    ofRel bs cover (graph f) (graph_total f) = f :=
  graph_injective (graph_ofRel bs cover _ _ (graph_functional f))

/-- With Prop-valued relations and no enumeration, getting a function from totality
needs the axiom of choice: this definition is `noncomputable`. The universe avoids it,
because candidates are stored as finite graphs and decisions are looked up
(a candidate of ω_sol is a finite graph: `Rasso.mem_omegaSolCandidates`). -/
noncomputable def ofPropRel (R : α → β → Prop) (tot : ∀ a, ∃ b, R a b) : α → β :=
  fun a => Classical.choose (tot a)

/-! ## 3. Counting: the function space is exponentially smaller

With `|α| = m` and `|β| = n` there are `n ^ m` functions and `2 ^ (m * n)` relations.
On solution sets the count of functions is `Rasso.length_omegaSolCandidates`; here is
the comparison. -/

theorem fspace_le_pset (m n : Nat) : n ^ m ≤ 2 ^ (n * m) := by
  rw [Nat.pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) m

/-- For `n ≥ 2` decisions and at least one data item, strictly fewer. -/
example : 3 ^ 4 < 2 ^ (3 * 4) := by decide

/-! ## 4. The "+1 attribute": powerset, multisets and partial functions are function
spaces -/

/-- **The powerset is a function space.** A relation `R ⊆ α × β` is a function from the
*pairs* to `Bool`: move `β` into the data and add one Boolean decision. (Curry and
uncurry; both inverse laws hold by `rfl`.) -/
def psetIso : Iso (BRel α β) (α × β → Bool) where
  toFun R p := R p.1 p.2
  invFun F a b := F (a, b)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Subset selection is the case `β = Unit`: `𝒫(α) ≅ Bool ^ α`. -/
def selectIso : Iso (α → Bool) (BRel α Unit) where
  toFun s a _ := s a
  invFun R a := R a ()
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Partial functions are total functions into `Option`.** Data items with no
decision get `none`. -/
def partialGraph [DecidableEq β] (f : α → Option β) : BRel α β := fun a b => decide (f a = some b)

theorem partialGraph_functional [DecidableEq β] (f : α → Option β) : Functional (partialGraph f) :=
  fun a b b' h h' => by
    simp only [partialGraph, decide_eq_true_eq] at h h'
    exact Option.some.inj (h.symm.trans h')

/-- A functional relation over a listable codomain is a partial function. -/
def ofFunctionalRel (bs : List β) (R : BRel α β) : α → Option β := fun a => bs.find? (R a)

theorem partialGraph_ofFunctionalRel [DecidableEq β] (bs : List β) (cover : ∀ b, b ∈ bs)
    (R : BRel α β) (fn : Functional R) : partialGraph (ofFunctionalRel bs R) = R :=
  funext fun a => funext fun b => by
    show decide (bs.find? (R a) = some b) = R a b
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    constructor
    · exact fun hf => List.find?_some hf
    · intro hR
      cases hf : bs.find? (R a) with
      | none => exact absurd hR (List.find?_eq_none.1 hf b (cover b))
      | some c => rw [fn a c b (List.find?_some hf) hR]

/-! ### Multisets are `Nat`-valued functions

A finite multiset over a listed, duplicate-free domain `xs` is a list up to
permutation. It corresponds to its multiplicity function `α → Nat`: the decision is a
count instead of a flag. -/

section Multiset
variable [BEq α] [LawfulBEq α]

/-- The multiplicity function of a list. -/
def mult (l : List α) : α → Nat := fun a => l.count a

/-- The list (multiset) with multiplicities `f`, over the domain `xs`. -/
def ofMult (xs : List α) (f : α → Nat) : List α := xs.flatMap fun a => List.replicate (f a) a

theorem count_ofMult {xs : List α} (nd : xs.Nodup) (f : α → Nat) (a : α) :
    (ofMult xs f).count a = if a ∈ xs then f a else 0 := by
  induction xs with
  | nil => simp [ofMult]
  | cons x xs ih =>
    have hx : x ∉ xs := (List.nodup_cons.1 nd).1
    have ih := ih (List.nodup_cons.1 nd).2
    simp only [ofMult, List.flatMap_cons, List.count_append, List.count_replicate] at ih ⊢
    rw [ih]
    by_cases e : x = a
    · subst e; simp [hx]
    · have : ¬ (x == a) = true := by simpa using e
      simp only [this, List.mem_cons]
      by_cases m : a ∈ xs
      · simp [m]
      · simp [m, Ne.symm e]

/-- Multiplicities survive the round trip (on the domain). -/
theorem mult_ofMult {xs : List α} (nd : xs.Nodup) (f : α → Nat) {a : α} (ha : a ∈ xs) :
    mult (ofMult xs f) a = f a := by
  simp [mult, count_ofMult nd, ha]

/-- A list over the domain is a permutation of the one rebuilt from its multiplicities:
the multiset is recovered exactly. -/
theorem ofMult_mult_perm {xs : List α} (nd : xs.Nodup) {l : List α} (sub : ∀ a ∈ l, a ∈ xs) :
    (ofMult xs (mult l)).Perm l := by
  refine List.perm_iff_count.2 fun a => ?_
  rw [count_ofMult nd]
  by_cases ha : a ∈ xs
  · simp [ha, mult]
  · simp only [ha]
    exact (List.count_eq_zero.2 fun m => ha (sub a m)).symm

end Multiset

/-! ## 5. Exponential laws: which hold for functions and fail for relations -/

/-- **Product of decisions**, `(X × Y) ^ A ≅ X ^ A × Y ^ A`: a function into a product is
a pair of functions. (Sol version: `Sol.join_omega_same_data`.) -/
def prodIso {γ : Type} : Iso (α → β × γ) ((α → β) × (α → γ)) where
  toFun f := (fun a => (f a).1, fun a => (f a).2)
  invFun p a := (p.1 a, p.2 a)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The same law fails for relations.** The natural map
`𝒫(A × (X × Y)) → 𝒫(A × X) × 𝒫(A × Y)` (project the relation onto each factor) is not
injective: it forgets which `x` went with which `y`. Here `A = Unit`, `X = Y = Bool`,
`R₁ = {(f,f), (t,t)}` and `R₂ = {(f,t), (t,f)}` have the same projections. -/
def projX (R : BRel Unit (Bool × Bool)) : BRel Unit Bool :=
  fun a x => R a (x, false) || R a (x, true)
def projY (R : BRel Unit (Bool × Bool)) : BRel Unit Bool :=
  fun a y => R a (false, y) || R a (true, y)

def R₁ : BRel Unit (Bool × Bool) := fun _ p => p.1 == p.2
def R₂ : BRel Unit (Bool × Bool) := fun _ p => p.1 != p.2

theorem prod_law_fails_for_relations :
    R₁ ≠ R₂ ∧ projX R₁ = projX R₂ ∧ projY R₁ = projY R₂ := by
  refine ⟨fun e => ?_, ?_, ?_⟩
  · have := congrFun (congrFun e ()) (false, false); simp [R₁, R₂] at this
  · funext a x; cases x <;> rfl
  · funext a y; cases y <;> rfl

/-- …and by counting: with `|A| = 1`, `|X| = |Y| = 3`, `2 ^ 9 ≠ 2 ^ 3 · 2 ^ 3`. (For
functions the counts agree: `9 ^ 1 = 3 ^ 1 · 3 ^ 1`.) -/
example : 2 ^ (1 * (3 * 3)) ≠ 2 ^ (1 * 3) * 2 ^ (1 * 3) ∧ (3 * 3) ^ 1 = 3 ^ 1 * 3 ^ 1 := by decide

/-- **Sum of data**, `D ^ (A ⊎ B) ≅ D ^ A × D ^ B`, holds for functions… -/
def sumIso {γ : Type} : Iso (α ⊕ γ → β) ((α → β) × (γ → β)) where
  toFun f := (fun a => f (.inl a), fun c => f (.inr c))
  invFun p := fun | .inl a => p.1 a | .inr c => p.2 c
  left_inv _ := funext fun | .inl _ => rfl | .inr _ => rfl
  right_inv _ := rfl

/-- …and for relations too: `𝒫((A ⊎ B) × D) ≅ 𝒫(A × D) × 𝒫(B × D)`. This law does not
separate the two views. (Sol version: `IsCand.restrict`, `IsCand.union_data`.) -/
def sumIsoRel {γ : Type} : Iso (BRel (α ⊕ γ) β) (BRel α β × BRel γ β) := sumIso

/-- **Currying**, `(D ^ B) ^ A ≅ D ^ (A × B)`. For functions it is an isomorphism. For
relations the analogue `𝒫(A × (B × D)) ≅ 𝒫((A × B) × D)` is just reassociation, and the
"exponential" `𝒫(B × D)` as a decision is a set, not a tuple. -/
def curryIso {γ : Type} : Iso (α → γ → β) (α × γ → β) where
  toFun f p := f p.1 p.2
  invFun g a c := g (a, c)
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## 6. Where the powerset is the more general view

* `𝒫(A × D)` contains every function space `D ^ A` (`graph_injective`), and every
  partial function (`partialGraph_functional`), and is a Boolean algebra under `⊆`
  (pointwise `&&`, `||`, `!`). The function space has none of that order structure
  (`graph_le_graph`, `union_graph_not_functional`).
* The two are reconciled by the "+1 attribute" isomorphisms of section 4: every
  powerset is a function space into `Bool` (`psetIso`), so building on function spaces
  loses nothing, provided the old decision attributes may move into the data. That last
  proviso is the cost: in the universe, data is a `Finrel`, so this needs the decision
  relation to be finite as well (blueprint chapter "Why function spaces").
-/

end Rasso.FunctionSpace
