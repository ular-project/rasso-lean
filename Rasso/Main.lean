import Rasso.Json.Surface
import Rasso.Json.Result
import Rasso.Json.Answer

/-!
# `rasso-lean`: run a rasso program given as a rassoAST document

    lake exe rasso-lean PROGRAM.json

reads the program, a rassoAST document `{"rasso": "1", "program": [item, …]}`, with the
JSON surface (`Rasso.Json.parseProgram`: Racket's `json-read-ast` and
`document->program`; pragmas are read and ignored), runs it, and prints a JSON object with every definition's value,
in program order. A refusal is printed on standard error, with exit code 1.

    lake exe rasso-lean --answers PROGRAM.json

prints instead each statement's answer in the Racket implementation's answer format
(`Rasso.Json.answersOf`), up to the first statement with none, for checking against
that implementation's conformance services.

    lake exe rasso-lean --read DOCUMENT.json

reads the text as a rassoAST document, its annotations kept (`readDocument`), and prints
`{"printed": text}`, the document printed again (`Document.print`), or
`{"refused": message}`, the message naming the place. Exit code 0 either way.
-/

open Rasso Rasso.Json

def main (args : List String) : IO UInt32 := do
  let (mode, path) ← match args with
    | [p] => pure ("", p)
    | ["--answers", p] => pure ("answers", p)
    | ["--read", p] => pure ("read", p)
    | _ => do IO.eprintln "usage: rasso-lean [--answers | --read] PROGRAM.json"; return 2
  let text ← IO.FS.readFile path
  if mode == "read" then
    match readDocument text with
    | .error e => IO.println (node "refused" (.str e)).compact
    | .ok d => IO.println (node "printed" (.str d.print)).compact
    return 0
  let answering := mode == "answers"
  if answering then
    match parseProgram text with
    | .error e => IO.println (J.arr [J.arr [.str "(document)", node "refused" (.str e)]]).compact; return 0
    | .ok prog => IO.println (answersOf prog).compact; return 0
  match parseProgram text with
  | .error e => IO.eprintln s!"rasso-lean: {e}"; return 1
  | .ok prog =>
    match runProgram prog with
    | .error e => IO.eprintln s!"rasso-lean: {e}"; return 1
    | .ok env => IO.print (envJ env).text; return 0
