import VLMOF.Interchange.Json
import VLMOF.Checker.Basic
import VLMOF.Source.Parser
import VLMOF.Source.Elaboration

open Lean VLMOF

private def diagnosticJson : Diagnostic → Json
  | .schema field => Json.mkObj [("phase", "schema"), ("field", field)]
  | .snapshot field => Json.mkObj [("phase", "snapshot"), ("field", field)]

private def failure (status message : String) : Json :=
  Json.mkObj [("status", status), ("message", message)]

/-- The runtime calls the same `checkSnapshot` function covered by checkSnapshot_iff.
JSON decoding and IO are separate, tested trust boundaries. -/
def checkDocument (d : Interchange.Document) : UInt32 × Json :=
  let accepted := checkSnapshot d.schema d.snapshot
  let diagnostics := if accepted then [] else
    schemaDiagnostics d.schema ++ snapshotDiagnostics d.schema d.snapshot
  (if accepted then 0 else 1,
    Json.mkObj [("status", if accepted then "accepted" else "invalid"),
      ("diagnostics", Json.arr (diagnostics.toArray.map diagnosticJson))])

def checkCore (schema : Schema) (snapshot : Snapshot) : UInt32 × Json :=
  let accepted := checkSnapshot schema snapshot
  let diagnostics := if accepted then [] else
    schemaDiagnostics schema ++ snapshotDiagnostics schema snapshot
  (if accepted then 0 else 1,
    Json.mkObj [("status", if accepted then "accepted" else "invalid"),
      ("diagnostics", Json.arr (diagnostics.toArray.map diagnosticJson))])

def checkJson (input : String) : UInt32 × Json :=
  match Json.parse input with
  | .error message => (2, failure "malformed" message)
  | .ok json =>
    match json.getObjVal? "version" >>= Json.getStr? with
    | .error message => (2, failure "malformed" message)
    | .ok version =>
      if version != Interchange.version then
        (3, failure "unsupported" s!"Unsupported interchange version: {version}")
      else match Interchange.decodeDocument json with
        | .error message => (2, failure "malformed" message)
        | .ok document => checkDocument document

/-- The DSL parser and binder are explicit trust boundaries.  Acceptance below means
only that the elaborated Core schema and snapshot pass the same executable predicate
as `check-json`; source-to-core conformance correspondence remains a separate theorem. -/
def checkDsl (input : String) : UInt32 × Json :=
  match Source.parse input with
  | .error message => (2, failure "parse-malformed" message)
  | .ok document =>
    match Source.elaborate document with
    | .error message => (2, failure "binding-failure" message)
    | .ok (schema, snapshot) =>
      checkCore schema snapshot

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  match args with
  | ["check-json", path] =>
    try
      let input ← IO.FS.readFile path
      let (code, report) := checkJson input
      out.putStrLn report.compress
      return code
    catch e =>
      out.putStrLn (failure "io-error" e.toString).compress
      return 4
  | ["check-dsl", path] =>
    try
      let input ← IO.FS.readFile path
      let (code, report) := checkDsl input
      out.putStrLn report.compress
      return code
    catch e =>
      out.putStrLn (failure "io-error" e.toString).compress
      return 4
  | _ =>
    out.putStrLn (failure "usage" "Usage: vlmof check-json FILE | vlmof check-dsl FILE").compress
    return 2
