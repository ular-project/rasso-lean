/-!
# Rasso: values and domains

Rasso is the second Lean formulation of rasso, built to agree with the Racket
implementation type for type and operator for operator, and to run as a small reference
evaluator on programs given as a JSON CST.

Design principles, not themselves expressible in Lean:

* **Domains are sets of values**, as databases have historically treated them. There is
  one universe of values (`Value`), and a domain (`Domain`) is data with a decidable
  membership test. Domains overlap: `3` is the same value in `int`, `range 0 5` and
  `enum [1, 3]`.
* Value kinds: int (`Int`), rat (`Rat`), bool (`Bool`), symbol (its own kind, distinct
  from string), string (`String`), and float. The evaluator computes on int, rat and bool;
  strings and floats are carried (the JSON surface has them) and compared, and float
  arithmetic is deferred.
* **One `1`**. Since domains
  are sets of values, the ints are a subset of the rats: `1` is one value. A whole number
  is always held as `.int`; `.rat` carries a proof that its number is not whole, so the
  derived equality is equality of numbers. `Value.ofRat` builds a number from a `Rat`.
* Values are ordered **by kind first, then within the kind** (Racket orders across kinds
  by printed form, an implementation artefact). Int, rat and float are one kind for the
  order: numbers, ordered as numbers. Within symbol: by character codes, as Racket's
  `string<?` on the printed form.
* **Two orders**. The program's order
  `Value.cmp` (`<`, `min`, `max`, ℰ's keys) is a total preorder with Racket's ties: `0`,
  `0.0` and `-0.0` are equal under it. The canonical order (`instance : Ord Value`), which
  lists enums and a relation's tuples, is `Value.cmp` with its ties broken by the key.
* No null.

Conventions:

* A symbol is held as a `String` (its spelling). The kind tag keeps it distinct from a
  future string kind.
* Ties are broken by an injective key into `List Int`, whose `compare` core Lean
  already proves lawful. The key is an implementation device; only the order it
  induces on tied values is meant. Both orders are lexicographic combinations of lawful
  compares, so core Lean's generic instances make them lawful.
* A float is held as the decimal that names it (`Decimal`: a sign, digits and a power
  of ten, with no trailing zeros), not as a Lean `Float`. Racket's printer writes the
  shortest digits that read back as the same double, so on every text it writes the
  two agree; a float written with more digits than a double holds is kept as written,
  where Racket would round it. A program sees floats ordered as numbers (`Value.cmp`),
  which is the order of the doubles they name; float arithmetic is deferred. `-0.0` is its own
  value, as in Racket.
-/

namespace Rasso

/-- A decimal number: `(-1)^neg * mant * 10^exp`. Normal when `mant` has no trailing
zero, and `exp = 0` when `mant = 0`. -/
structure Decimal where
  neg : Bool
  mant : Nat
  exp : Int
  deriving DecidableEq, Repr, Inhabited

/-- One universe of values. -/
inductive Value where
  | bool (b : Bool)
  | int (n : Int)
  | symbol (s : String)
  | string (s : String)
  | float (d : Decimal)
  /-- A rational number that is not whole (a whole number is an `int`). -/
  | rat (q : Rat) (h : q.den ≠ 1)
  deriving DecidableEq, Repr, Inhabited


/-! ## Rationals: the order, and numbers as values -/

/-- Core Lean has no `Ord Rat`; this is its order (`<` and `=`). -/
instance : Ord Rat := ⟨fun a b => compareOfLessAndEq a b⟩

instance : Std.TransOrd Rat :=
  Std.TransOrd.compareOfLessAndEq_of_antisymm_of_trans_of_total_of_not_le
    Rat.le_antisymm Rat.le_trans (fun _ _ => Rat.le_total) Rat.not_le

instance : Std.LawfulEqOrd Rat :=
  ⟨fun h => (compareOfLessAndEq_eq_eq (fun _ => Rat.le_refl) Rat.not_le).mp h⟩

/-- A number as a value: an `int` when it is whole, a `rat` otherwise. -/
def Value.ofRat (q : Rat) : Value := if h : q.den = 1 then .int q.num else .rat q h

/-- The exact number a value is (an int or a rat), if it is one. -/
def Value.exact? : Value → Option Rat
  | .int n => some n
  | .rat q _ => some q
  | _ => none

theorem Rat.eq_num_of_den_eq_one {q : Rat} (h : q.den = 1) : q = (q.num : Rat) := by
  exact Rat.ext (by simp) (by simp [h])

theorem Value.exact?_ofRat (q : Rat) : (Value.ofRat q).exact? = some q := by
  unfold Value.ofRat
  split
  · simp only [Value.exact?, Option.some.injEq]
    exact (Rat.eq_num_of_den_eq_one ‹_›).symm
  · rfl

theorem Value.ofRat_inj {q r : Rat} (h : Value.ofRat q = Value.ofRat r) : q = r := by
  have := congrArg Value.exact? h
  simpa [Value.exact?_ofRat] using this

/-- A float. -/
def Value.isFloat : Value → Bool
  | .float _ => true
  | _ => false

/-- An exact number: an int or a rat. -/
def Value.isExact (v : Value) : Bool := v.exact?.isSome

/-- A symbol. `=` refuses a symbol beside a string (`applyOp`), as an exact number beside a
float. -/
def Value.isSymbol : Value → Bool
  | .symbol _ => true
  | _ => false

/-- A string. -/
def Value.isString : Value → Bool
  | .string _ => true
  | _ => false

/-- A decimal as the rational number it names. -/
def Decimal.toRat (d : Decimal) : Rat :=
  let m : Rat := if d.neg then -(d.mant : Rat) else (d.mant : Rat)
  if 0 ≤ d.exp then m * ((10 ^ d.exp.toNat : Nat) : Rat)
  else m / ((10 ^ (-d.exp).toNat : Nat) : Rat)

/-- The number a value is (an int, a rat or a float), if it is one. -/
def Value.num? : Value → Option Rat
  | .float d => some d.toRat
  | v => v.exact?

/-- A string as its character codes. -/
def strKey (s : String) : List Int := s.toList.map fun c => (c.toNat : Int)

theorem map_inj_of_inj {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l₁ l₂ : List α}, l₁.map f = l₂.map f → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf _ _ h.1, map_inj_of_inj hf h.2]

theorem strKey_inj {s t : String} (h : strKey s = strKey t) : s = t := by
  apply String.ext
  apply map_inj_of_inj _ h
  intro c d e
  exact Char.toNat_inj.mp (by omega)

/-- The key that orders values: the kind first, then the value within its kind. -/
def Value.key : Value → List Int
  | .bool b => [0, if b then 1 else 0]
  | .int n => [1, n]
  | .symbol s => 2 :: strKey s
  | .string s => 3 :: strKey s
  | .float d => [4, if d.neg then 1 else 0, d.mant, d.exp]
  | .rat q _ => [1, q.num, q.den]

theorem Value.key_inj : ∀ {v w : Value}, v.key = w.key → v = w
  | .bool b, .bool c, h => by cases b <;> cases c <;> simp_all [Value.key]
  | .int n, .int m, h => by simp_all [Value.key]
  | .symbol s, .symbol t, h => by
    simp only [Value.key, List.cons.injEq, true_and] at h
    rw [strKey_inj h]
  | .string s, .string t, h => by
    simp only [Value.key, List.cons.injEq, true_and] at h
    rw [strKey_inj h]
  | .float ⟨n₁, m₁, e₁⟩, .float ⟨n₂, m₂, e₂⟩, h => by
    simp only [Value.key, List.cons.injEq, true_and, and_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    have : n₁ = n₂ := by cases n₁ <;> cases n₂ <;> simp_all
    subst this
    have : m₁ = m₂ := by omega
    subst this; subst h3; rfl
  | .rat q hq, .rat r hr, h => by
    simp only [Value.key, List.cons.injEq, true_and, and_true] at h
    obtain ⟨h1, h2⟩ := h
    have : q = r := Rat.ext h1 (by omega)
    subst this; rfl
  | .int _, .rat _ _, h | .rat _ _, .int _, h => by simp [Value.key] at h
  | .bool _, .rat _ _, h | .symbol _, .rat _ _, h | .string _, .rat _ _, h | .float _, .rat _ _, h
  | .rat _ _, .bool _, h | .rat _ _, .symbol _, h | .rat _ _, .string _, h | .rat _ _, .float _, h => by
    simp [Value.key] at h
  | .bool _, .int _, h | .bool _, .symbol _, h | .bool _, .string _, h | .bool _, .float _, h
  | .int _, .bool _, h | .int _, .symbol _, h | .int _, .string _, h | .int _, .float _, h
  | .symbol _, .bool _, h | .symbol _, .int _, h | .symbol _, .string _, h | .symbol _, .float _, h
  | .string _, .bool _, h | .string _, .int _, h | .string _, .symbol _, h | .string _, .float _, h
  | .float _, .bool _, h | .float _, .int _, h | .float _, .symbol _, h | .float _, .string _, h => by
    simp [Value.key] at h

def Value.kindRank : Value → Nat
  | .bool _ => 0 | .int _ => 1 | .float _ => 1 | .rat _ _ => 1 | .symbol _ => 2 | .string _ => 3

/-- The key of a value that is not a number (`[]` for a number, which `num?` orders). -/
def Value.nonNumKey (v : Value) : List Int := if v.num?.isSome then [] else v.key

/-- The order on values that a program sees (comparisons, ℰ's keys, `min` and `max`):
kind first, then within the kind; ints, rats and floats together, as numbers. A total preorder: equal numbers of different kinds (`0`, `0.0`, `-0.0`) are tied, as in
Racket. -/
def Value.cmp : Value → Value → Ordering :=
  compareLex (compareOn Value.kindRank) (compareLex (compareOn Value.num?) (compareOn Value.nonNumKey))

instance : Std.TransCmp Value.cmp := by unfold Value.cmp; infer_instance

/-- The canonical order: `Value.cmp`, ties broken by the key. It lists enums and a
relation's tuples. -/
instance : Ord Value := ⟨compareLex Value.cmp (compareOn Value.key)⟩

instance : Std.TransOrd Value :=
  inferInstanceAs (Std.TransCmp (compareLex Value.cmp (compareOn Value.key)))

instance : Std.LawfulEqOrd Value where
  eq_of_compare {v w} h := by
    change compareLex Value.cmp (compareOn Value.key) v w = .eq at h
    rw [compareLex_eq_eq] at h
    exact Value.key_inj (Std.LawfulEqCmp.eq_of_compare (cmp := compare) h.2)

/-- `v` sorts no later than `w` in the canonical order (used to list a body's tuples). -/
def Value.le (v w : Value) : Bool := (compare v w).isLE

/-- Two decimals compared as numbers. -/
def Decimal.cmp (a b : Decimal) : Ordering :=
  let num (d : Decimal) : Int := (if d.neg then -1 else 1) * (d.mant : Int)
  let k := min a.exp b.exp
  compare (num a * 10 ^ (a.exp - k).toNat) (num b * 10 ^ (b.exp - k).toNat)

/-- Numbers (ints, rats, floats) compared as numbers, or none. -/
def Value.numCmp (v w : Value) : Option Ordering :=
  match v.num?, w.num? with
  | some a, some b => some (compare a b)
  | _, _ => none

/-- A decimal as Racket writes a float (`number->string`, Racket 8.10 CS): the
digits in positions when the decimal exponent `s` (of `d.ddd × 10^s`) is in
`-4 ≤ s ≤ max 13 (n + 2)`, `n` the number of digits, and otherwise `d.ddde+s`; a whole
number keeps `.0`. Found by probing Racket, not from its source. -/
def Decimal.toRacket (d : Decimal) : String :=
  let sign := if d.neg then "-" else ""
  if d.mant = 0 then sign ++ "0.0" else
  let ds := toString d.mant
  let n := ds.length
  let s : Int := d.exp + n - 1
  let zeros (k : Nat) := String.ofList (List.replicate k '0')
  if -4 ≤ s ∧ s ≤ max 13 (n + 2) then
    if s ≥ n - 1 then sign ++ ds ++ zeros (s - (n - 1)).toNat ++ ".0"
    else if s ≥ 0 then
      sign ++ String.ofList (ds.toList.take (s + 1).toNat) ++ "." ++
        String.ofList (ds.toList.drop (s + 1).toNat)
    else sign ++ "0." ++ zeros (-s - 1).toNat ++ ds
  else
    let rest := String.ofList (ds.toList.drop 1)
    sign ++ String.ofList (ds.toList.take 1) ++ (if n > 1 then "." ++ rest else "") ++ "e" ++
      (if s ≥ 0 then "+" else "-") ++ toString s.natAbs

/-- The value as Racket would print it in a result. -/
def Value.toString : Value → String
  | .bool b => if b then "#t" else "#f"
  | .int n => s!"{n}"
  | .symbol s => s
  | .string s => s
  | .float d => d.toRacket
  | .rat q _ => s!"{q.num}/{q.den}"

instance : ToString Value := ⟨Value.toString⟩

/-! ## Domains -/

/-- The kinds of value. `Domain.kind k` is the domain of every value of kind `k`. -/
inductive Kind where
  | bool | int | symbol | string | float
  /-- The rationals: every int and every rat. -/
  | rat
  deriving DecidableEq, Repr, Inhabited

/-- A domain: a set of values, given as data (Racket's `domain?`). -/
inductive Domain where
  | kind (k : Kind)
  /-- The integers lo..hi, inclusive. -/
  | range (lo hi : Int)
  /-- A finite set of values. -/
  | set (vs : List Value)
  deriving DecidableEq, Repr, Inhabited


def Kind.has : Kind → Value → Bool
  | .bool, .bool _ => true
  | .int, .int _ => true
  | .symbol, .symbol _ => true
  | .string, .string _ => true
  | .float, .float _ => true
  | .rat, .int _ => true
  | .rat, .rat _ _ => true
  | _, _ => false

/-- Membership (Racket's `dom-member?`). -/
def Domain.mem : Domain → Value → Bool
  | .kind k, v => k.has v
  | .range lo hi, .int n => decide (lo ≤ n) && decide (n ≤ hi)
  | .range _ _, _ => false
  | .set vs, v => vs.contains v

/-- The values of a domain, in value order, when it is finite (Racket's `dom-values`). -/
def Domain.values? : Domain → Option (List Value)
  | .kind .bool => some [.bool false, .bool true]
  | .kind _ => none
  | .range lo hi => some ((List.range (hi - lo + 1).toNat).map fun (i : Nat) => .int (lo + Int.ofNat i))
  | .set vs => some (vs.mergeSort Value.le)

/-- The set domain of a list of values: duplicates dropped, in value order (Racket's `dom-set`). -/
def Domain.ofValues (vs : List Value) : Domain := .set (vs.eraseDups.mergeSort Value.le)

/-- Intersection, the domain a join gives a shared attribute (Racket's `dom-intersect`). -/
def Domain.inter (a b : Domain) : Except String Domain :=
  if a = b then .ok a else
  match a, b with
  | .range l₁ h₁, .range l₂ h₂ =>
    let lo := max l₁ l₂; let hi := min h₁ h₂
    .ok (if lo ≤ hi then .range lo hi else .set [])
  | .kind .int, .range _ _ => .ok b
  | .range _ _, .kind .int => .ok a
  | .kind .rat, .range _ _ => .ok b
  | .range _ _, .kind .rat => .ok a
  | .kind .rat, .kind .int => .ok b
  | .kind .int, .kind .rat => .ok a
  | _, _ =>
    match a.values?, b.values? with
    | some va, _ => .ok (Domain.ofValues (va.filter b.mem))
    | _, some vb => .ok (Domain.ofValues (vb.filter a.mem))
    | none, none => .error s!"cannot intersect the domains {repr a} and {repr b}"

end Rasso
