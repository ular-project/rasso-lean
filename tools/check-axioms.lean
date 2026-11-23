/-
The axiom audit: no declaration of the released libraries rests on an axiom other than
Lean's three standard ones.

    lake build
    lake env lean --run tools/check-axioms.lean

It loads `Rasso`, `Rasso.Main` (the root of the `rasso-lean` executable), `ConstraintDB`
and `Coddstheorem` at run time, and takes every constant whose module is under one of the
three libraries. For each, it finds the
axioms the constant rests on, following the edges `Lean.collectAxioms` follows: the
constants in its type and value, and an inductive's constructors.

The axioms are computed once for the whole graph: from each axiom of the environment, one
search backwards along the edges. Calling `collectAxioms` once per declaration would take
many minutes. As a cross-check, about 200 constants, spread evenly by name, and every
failing one are also run through `collectAxioms`, and the two must agree.

Allowed: `propext`, `Classical.choice` and `Quot.sound`. Anything else fails: `sorryAx`
(a `sorry`), an `axiom` declared in the library, and the auxiliary axiom that
`native_decide` declares. Exit 0 when the audit passes, 1 when it fails.
-/
import Lean
open Lean

def runCore (env : Environment) (x : CoreM α) : IO α := do
  let ctx : Core.Context := { fileName := "<check-axioms>", fileMap := default, options := {},
                              maxHeartbeats := 0 }
  let (a, _) ← (x.run ctx { env }).toIO (fun _ => IO.userError "check-axioms: a CoreM error")
  return a

/-- The constants that `collectAxioms` visits from `ci`. -/
def edges (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => t ++ v.value.getUsedConstants
  | .thmInfo v => t ++ v.value.getUsedConstants
  | .opaqueInfo v => t ++ v.value.getUsedConstants
  | .inductInfo v => t ++ v.ctors.toArray
  | .axiomInfo _ => #[]
  | _ => t

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def sameSet (a b : Array Name) : Bool := a.all b.contains && b.all a.contains

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let t0 ← IO.monoMsNow
  let env ← importModules #[{ module := `Rasso }, { module := `Rasso.Main },
    { module := `ConstraintDB }, { module := `Coddstheorem }] {} (trustLevel := 1024)
  let roots : List Name := [`Rasso, `ConstraintDB, `Coddstheorem]
  let inRasso (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => roots.contains (env.header.moduleNames[i.toNat]!).getRoot
    | none => false
  let mut ours : Array Name := #[]
  let mut axioms : Array Name := #[]
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    if inRasso n then ours := ours.push n
    if ci matches .axiomInfo _ then axioms := axioms.push n
    for c in edges ci do
      rev := rev.alter c (fun o => some ((o.getD #[]).push n))
  -- From each axiom, every constant that rests on it.
  let mut rests : Std.HashMap Name (Array Name) := {}
  for a in axioms do
    let mut seen : NameSet := NameSet.empty.insert a
    let mut stack := #[a]
    while !stack.isEmpty do
      let x := stack.back!
      stack := stack.pop
      for y in rev.getD x #[] do
        unless seen.contains y do
          seen := seen.insert y
          stack := stack.push y
    for n in ours do
      if seen.contains n then rests := rests.alter n (fun o => some ((o.getD #[]).push a))
  -- The failures.
  let mut bad : Array Name := #[]
  for n in ours do
    let not_allowed := (rests.getD n #[]).filter (!allowed.contains ·)
    unless not_allowed.isEmpty do
      bad := bad.push n
      IO.eprintln s!"FAIL {n} rests on {not_allowed.toList}"
  -- The cross-check against collectAxioms.
  let sorted := ours.qsort (fun a b => Name.lt a b)
  let step := max 1 (sorted.size / 200)
  let sample := (List.range ((sorted.size + step - 1) / step)).toArray.map (sorted[· * step]!) ++ bad
  let mut differ := 0
  for n in sample do
    let theirs ← runCore env (collectAxioms n)
    unless sameSet theirs (rests.getD n #[]) do
      differ := differ + 1
      IO.eprintln s!"FAIL the cross-check: {n}: collectAxioms says {theirs.toList}, the audit {(rests.getD n #[]).toList}"
  let t1 ← IO.monoMsNow
  let counts := allowed.map fun a => s!"{a} {(ours.filter fun n => (rests.getD n #[]).contains a).size}"
  IO.println s!"{ours.size} declarations, {bad.size} failing; resting on {", ".intercalate counts}; {sample.size} cross-checked with collectAxioms, {differ} differing; {(t1 - t0) / 1000} s"
  return if bad.isEmpty && differ == 0 then 0 else 1
