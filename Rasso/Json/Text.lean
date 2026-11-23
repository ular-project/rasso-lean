import Rasso.Value

/-!
# Rasso: JSON text

The JSON surface's text layer, a port of the Racket implementation's: the strict reader
(`read-json-text`), and the layout (Wadler's "A prettier printer", at width 80) with the
writer of rassoAST.

The reader is as strict as Racket's: one JSON value, then only whitespace; no `null`; an
object's key once; a number with a fraction or an exponent is a float, and refused if it
isn't finite (`1e400`); one without is an integer, with no leading zero; `-0.0` kept; a
lone surrogate refused. A refusal names the line and column, as Racket's does.

The writer escapes a string as Racket's `jsexpr->string` does (`"`, `\`, the control
characters and DEL; `\b \t \n \f \r` by their short forms, the rest as `\u00XX`), writes
an integer in decimal and a float as Racket's `number->string` does
(`Decimal.toRacket`), and lays out each object or array on one line if it fits, else
one member a line, nested two spaces.

Conventions:

* A float that is too small for a double reads as zero (as Racket rounds it); one with
  more significant digits than a double holds is kept as written (Racket rounds it).
  Neither is written by Racket's printer.
-/

namespace Rasso.Json

/-- A JSON tree: an object's keys in order. -/
inductive J where
  | obj (ps : List (String × J))
  | arr (xs : List J)
  | str (s : String)
  | int (n : Int)
  | float (d : Decimal)
  | bool (b : Bool)
  deriving Inhabited, Repr

/-! ## Reading -/

structure Reader where
  s : Array Char
  i : Nat

abbrev R := StateT Reader (Except String)

def where_ : R String := do
  let r ← get
  let before := (r.s.toList.take r.i)
  let lines := before.splitOn '\n'
  return s!"line {lines.length}, column {(lines.getLast?.map List.length).getD 0 + 1}"

def fail {α : Type} (msg : String) : R α := do
  throw s!"json-parse: {← where_}: {msg}"

def peek : R (Option Char) := do
  let r ← get
  return r.s[r.i]?

def adv (k : Nat := 1) : R Unit := modify fun r => { r with i := r.i + k }

partial def skipWs : R Unit := do
  match ← peek with
  | some ' ' | some '\t' | some '\n' | some '\r' => adv; skipWs
  | _ => pure ()

def expect (c : Char) : R Unit := do
  match ← peek with
  | some d => if d == c then adv else fail s!"expected {c}, found {d}"
  | none => fail s!"expected {c}, found the end"

def word (w : String) (v : J) : R J := do
  let r ← get
  if (r.s.toList.drop r.i).take w.length == w.toList then adv w.length; return v
  else fail "not JSON"

def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hex4 : R Nat := do
  let r ← get
  let cs := (r.s.toList.drop r.i).take 4
  if cs.length < 4 then fail "a \\u escape takes four hex digits"
  match cs.mapM hexDigit? with
  | some ds => adv 4; return ds.foldl (fun a d => a * 16 + d) 0
  | none => fail "a \\u escape takes four hex digits"

def hexText (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

partial def strBody (acc : String) : R String := do
  match ← peek with
  | none => fail "a string isn't closed"
  | some '"' => adv; return acc
  | some c =>
    if c.toNat < 32 then fail "a control character in a string must be escaped"
    else if c == '\\' then
      adv
      let e ← peek
      adv
      match e with
      | some '"' => strBody (acc.push '"')
      | some '\\' => strBody (acc.push '\\')
      | some '/' => strBody (acc.push '/')
      | some 'b' => strBody (acc.push (Char.ofNat 8))
      | some 'f' => strBody (acc.push (Char.ofNat 12))
      | some 'n' => strBody (acc.push '\n')
      | some 'r' => strBody (acc.push '\r')
      | some 't' => strBody (acc.push '\t')
      | some 'u' =>
        let h ← hex4
        if 0xD800 ≤ h && h ≤ 0xDBFF then
          let r ← get
          unless r.s[r.i]? == some '\\' && r.s[r.i + 1]? == some 'u' do
            fail s!"a lone surrogate, \\u{hexText h}, is not a character"
          adv 2
          let lo ← hex4
          unless 0xDC00 ≤ lo && lo ≤ 0xDFFF do
            fail s!"a lone surrogate, \\u{hexText h}, is not a character"
          strBody (acc.push (Char.ofNat (0x10000 + (h - 0xD800) * 0x400 + (lo - 0xDC00))))
        else if 0xDC00 ≤ h && h ≤ 0xDFFF then
          fail s!"a lone surrogate, \\u{hexText h}, is not a character"
        else strBody (acc.push (Char.ofNat h))
      | some x => fail s!"\\{x} is not an escape"
      | none => fail "\\the end is not an escape"
    else adv; strBody (acc.push c)

def str : R String := do expect '"'; strBody ""

/-- The digits of a decimal, as a number. -/
def digitsVal (ds : List Char) : Nat := ds.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0

/-- Normal form: no trailing zero in the digits; zero has exponent 0. -/
partial def _root_.Rasso.Decimal.normalize (d : Decimal) : Decimal :=
  if d.mant = 0 then { d with exp := 0 }
  else if d.mant % 10 = 0 then Rasso.Decimal.normalize { d with mant := d.mant / 10, exp := d.exp + 1 }
  else d

/-- Whether a decimal (not zero) is beyond the largest double, so reads as infinite:
at or past the halfway point 1.797693134862315807937…e308. -/
def _root_.Rasso.Decimal.overflows (d : Decimal) : Bool :=
  let ds := toString d.mant
  let s : Int := d.exp + ds.length - 1
  if s > 308 then true else if s < 308 then false
  else
    let lim := "17976931348623158079372897"
    let pad := ds ++ String.ofList (List.replicate (lim.length - min ds.length lim.length) '0')
    !(pad < lim)

/-- Whether a decimal is below half the smallest double, so reads as zero. -/
def _root_.Rasso.Decimal.underflows (d : Decimal) : Bool :=
  let ds := toString d.mant
  let s : Int := d.exp + ds.length - 1
  if s < -324 then true else if s > -324 then false
  else
    let lim := "24703282292062327208828"
    let pad := ds ++ String.ofList (List.replicate (lim.length - min ds.length lim.length) '0')
    pad ≤ lim

def num : R J := do
  let r ← get
  let rest := r.s.toList.drop r.i
  let digitsFrom (l : List Char) := l.takeWhile Char.isDigit
  let (neg, afterSign) := match rest with
    | '-' :: t => (true, t)
    | t => (false, t)
  let intPart : List Char := match afterSign with
    | '0' :: _ => ['0']
    | c :: t => if c.isDigit && c != '0' then c :: digitsFrom t else []
    | [] => []
  if intPart.isEmpty then fail "not JSON"
  let afterInt := afterSign.drop intPart.length
  let fracPart : Option (List Char) := match afterInt with
    | '.' :: t => let ds := digitsFrom t; if ds.isEmpty then none else some ds
    | _ => none
  let afterFrac := afterInt.drop (fracPart.map (·.length + 1) |>.getD 0)
  let expPart : Option (Bool × List Char) := match afterFrac with
    | e :: t =>
      if e == 'e' || e == 'E' then
        let (eneg, sgnLen, t') := match t with
          | '-' :: u => (true, 1, u)
          | '+' :: u => (false, 1, u)
          | u => (false, 0, u)
        let ds := digitsFrom t'
        if ds.isEmpty then none else some (eneg, List.replicate (1 + sgnLen) 'x' ++ ds)
      else none
    | [] => none
  let text := String.ofList (rest.take ((if neg then 1 else 0) + intPart.length +
    (fracPart.map (·.length + 1) |>.getD 0) + (expPart.map (·.2.length) |>.getD 0)))
  adv text.length
  if let some c ← peek then
    if c.isDigit then fail s!"a number has no leading zero: {text}…"
  match fracPart, expPart with
  | none, none =>
    let n : Int := digitsVal intPart
    return .int (if neg then -n else n)
  | _, _ =>
    let fr := fracPart.getD []
    let ev : Int := match expPart with
      | some (eneg, chars) =>
        let ds := chars.dropWhile (fun c => c == 'x')
        let v : Int := digitsVal ds
        if eneg then -v else v
      | none => 0
    let d := Decimal.normalize ⟨neg, digitsVal (intPart ++ fr), ev - fr.length⟩
    if d.mant ≠ 0 && d.overflows then fail s!"{text} is not a finite float"
    if d.mant ≠ 0 && d.underflows then return .float ⟨neg, 0, 0⟩
    return .float d

mutual
partial def val : R J := do
  skipWs
  match ← peek with
  | none => fail "expected a value, found the end"
  | some '{' =>
    adv; skipWs
    if (← peek) == some '}' then adv; return .obj []
    objLoop []
  | some '[' =>
    adv; skipWs
    if (← peek) == some ']' then adv; return .arr []
    arrLoop []
  | some '"' => return .str (← str)
  | some 't' => word "true" (.bool true)
  | some 'f' => word "false" (.bool false)
  | some 'n' => fail "null is not in this surface: every node names its kind"
  | some _ => num

partial def objLoop (pairs : List (String × J)) : R J := do
  skipWs
  unless (← peek) == some '"' do fail "expected a key, a string"
  let k ← str
  if pairs.any (·.1 == k) then fail s!"the key {reprStr k} is repeated"
  skipWs; expect ':'
  let v ← val
  skipWs
  match ← peek with
  | some ',' => adv; objLoop ((k, v) :: pairs)
  | some '}' => adv; return .obj ((k, v) :: pairs).reverse
  | _ => fail "expected , or }"

partial def arrLoop (items : List J) : R J := do
  let v ← val
  skipWs
  match ← peek with
  | some ',' => adv; arrLoop (v :: items)
  | some ']' => adv; return .arr (v :: items).reverse
  | _ => fail "expected , or ]"
end

/-- Read one JSON value, then only whitespace. -/
def read (text : String) : Except String J := do
  let (v, _) ← (do
    let v ← val
    skipWs
    let r ← get
    if r.i < r.s.size then fail "after the value, only whitespace"
    return v : R J).run ⟨text.toList.toArray, 0⟩
  return v

/-! ## Layout (Racket's) -/

inductive Doc where
  | text (s : String)
  | cat (ds : List Doc)
  | line
  | softline
  | nest (i : Nat) (d : Doc)
  | group (d : Doc)
  deriving Inhabited

def width : Nat := 80

/-- Whether the rest of the line fits in `w` columns: the group being tried lies flat,
and what follows it breaks at its first chance. -/
partial def fits (w : Int) (items : List (Nat × Bool × Doc)) : Bool :=
  if w < 0 then false else
  match items with
  | [] => true
  | (i, flat, d) :: more =>
    match d with
    | .text s => fits (w - s.length) more
    | .cat ds => fits w (ds.map (fun x => (i, flat, x)) ++ more)
    | .nest _ x => fits w ((i, flat, x) :: more)
    | .group x => fits w ((i, flat, x) :: more)
    | .line => !flat || fits (w - 1) more
    | .softline => !flat || fits w more

def render (d : Doc) (w : Nat) : String := Id.run do
  let mut out := ""
  let mut col : Nat := 0
  let mut items : List (Nat × Bool × Doc) := [(0, false, d)]
  -- a loop with fuel enough for any document: each step consumes or expands one item
  for _ in [0:100000000] do
    match items with
    | [] => break
    | (i, flat, d) :: more =>
      match d with
      | .text s => out := out ++ s; col := col + s.length; items := more
      | .cat ds => items := ds.map (fun x => (i, flat, x)) ++ more
      | .nest n x => items := (i + n, flat, x) :: more
      | .group x =>
        let f := flat || fits ((w : Int) - col) ((i, true, x) :: more)
        items := (i, f, x) :: more
      | .line =>
        if flat then out := out ++ " "; col := col + 1
        else out := out ++ "\n" ++ String.ofList (List.replicate i ' '); col := i
        items := more
      | .softline =>
        if flat then pure ()
        else out := out ++ "\n" ++ String.ofList (List.replicate i ' '); col := i
        items := more
  return out

def commas : List Doc → List Doc
  | [] => []
  | [d] => [d]
  | d :: ds => d :: .text "," :: .line :: commas ds

def bracketed (o c : String) (items : List Doc) : Doc :=
  if items.isEmpty then .text (o ++ c)
  else .group (.cat [.text o, .nest 2 (.cat (.softline :: commas items)), .softline, .text c])

/-! ## Writing -/

def hex2 (n : Nat) : String :=
  let ds := Nat.toDigits 16 n
  String.ofList (List.replicate (4 - ds.length) '0' ++ ds)

/-- A string as Racket's `jsexpr->string` writes it. -/
def jsonString (s : String) : String :=
  let esc (c : Char) : String :=
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c.toNat == 8 then "\\b" else if c == '\t' then "\\t" else if c == '\n' then "\\n"
    else if c.toNat == 12 then "\\f" else if c == '\r' then "\\r"
    else if c.toNat < 32 || c.toNat == 127 then "\\u" ++ hex2 c.toNat
    else c.toString
  "\"" ++ String.join (s.toList.map esc) ++ "\""

partial def J.doc : J → Doc
  | .obj ps => bracketed "{" "}" (ps.map fun (k, v) => .cat [.text (jsonString k), .text ": ", v.doc])
  | .arr xs => bracketed "[" "]" (xs.map J.doc)
  | .str s => .text (jsonString s)
  | .bool b => .text (if b then "true" else "false")
  | .int n => .text (toString n)
  | .float d => .text d.toRacket

/-- The text of a tree, laid out at width 80, with a final new line. -/
def J.text (t : J) : String := render t.doc width ++ "\n"

/-! ## rassoAST's layout (Racket's)

rassoAST has one layout: Racket's `(write-json jsexpr #:indent 2)`, then a new line.
Every object's keys come out sorted (`symbol<?`, which for these ASCII keys is the order
of `String`'s `<`), every non-empty object or array is spread one member a line, each
level indented two more spaces, and an empty one is written `{}` or `[]`. Strings and
numbers are written as `J.text` writes them.

Convention: two keys of one object are never equal; the
reader refuses a repeated key, so a tree read from text never has one. -/

/-- A tree's text in rassoAST's layout, at an indent of `i` spaces. -/
partial def J.astAt (i : Nat) : J → String
  | .obj [] => "{}"
  | .arr [] => "[]"
  | .obj ps =>
    let pad := String.ofList (List.replicate (i + 2) ' ')
    let sorted := ps.mergeSort (fun a b => decide (a.1 ≤ b.1))
    "{\n" ++ ",\n".intercalate (sorted.map fun (k, v) => pad ++ jsonString k ++ ": " ++ v.astAt (i + 2))
      ++ "\n" ++ String.ofList (List.replicate i ' ') ++ "}"
  | .arr xs =>
    let pad := String.ofList (List.replicate (i + 2) ' ')
    "[\n" ++ ",\n".intercalate (xs.map fun v => pad ++ v.astAt (i + 2))
      ++ "\n" ++ String.ofList (List.replicate i ' ') ++ "]"
  | t => render t.doc width

/-- A tree's text as Racket's `json-print-ast` writes it: `write-json` at an indent of 2,
and a final new line. -/
def J.textAst (t : J) : String := t.astAt 0 ++ "\n"

#guard (J.obj [("b", .int 1), ("a", .arr [])]).textAst == "{\n  \"a\": [],\n  \"b\": 1\n}\n"
#guard (J.obj []).textAst == "{}\n"
#guard (J.arr [.obj [("x", .str "é\u007f")], .obj []]).textAst ==
  "[\n  {\n    \"x\": \"é\\u007f\"\n  },\n  {}\n]\n"
#guard (J.obj [("Z", .int 1), ("_", .bool true), ("a", .int 2)]).textAst ==
  "{\n  \"Z\": 1,\n  \"_\": true,\n  \"a\": 2\n}\n"

/-- JSON on one line, with no spaces, as Racket's `jsexpr->string` writes it. -/
partial def J.compact : J → String
  | .obj ps => "{" ++ ",".intercalate (ps.map fun (k, v) => jsonString k ++ ":" ++ v.compact) ++ "}"
  | .arr xs => "[" ++ ",".intercalate (xs.map J.compact) ++ "]"
  | .str s => jsonString s
  | .int n => toString n
  | .float d => d.toRacket
  | .bool b => if b then "true" else "false"

end Rasso.Json
