import VLMOF.Interchange.Json
import VLMOF.Checker.Basic

/-!
# Repeated validation of an already decoded finite model

This experiment entry point keeps file loading and JSON decoding outside the
validation window. Each iteration reads the document through an IO reference
and calls a non-inlined worker, preventing a loop-invariant pure result from
being hoisted by inlining. Boolean results are retained so work
cannot be discarded. The schema-only and combined windows are separate runs;
subtracting them is not an instance-only measurement.
-/

open Lean VLMOF

/-- Execute schema obligations without collecting diagnostics. No result is cached. -/
@[noinline] def measureSchema (d : Interchange.Document) : Bool :=
  checkSchema d.schema

/-- Execute all snapshot obligations, including schema well-formedness. Diagnostic
collection belongs to the separate untimed correctness experiment. -/
@[noinline] def measureCombined (d : Interchange.Document) : Bool :=
  checkSnapshot d.schema d.snapshot

private def samples (ref : IO.Ref Interchange.Document)
    (worker : Interchange.Document → Bool) (warmups repetitions : Nat) :
    IO Json := do
  let mut rows := #[]
  for i in [:warmups + repetitions] do
    let document ← ref.get
    let start ← IO.monoNanosNow
    let accepted := worker document
    -- Force the result into an IO cell before ending the timed work.
    let result ← IO.mkRef accepted
    let stop ← IO.monoNanosNow
    let accepted ← result.get
    rows := rows.push <| Json.mkObj [
      ("index", toJson i), ("warmup", toJson (decide (i < warmups))),
      ("nanoseconds", toJson (stop - start)),
      ("accepted", toJson accepted)]
  return Json.arr rows

/-- Benchmark CLI; semantic invalidity is a recorded outcome, while malformed
input or bad experiment parameters cause a nonzero process exit. -/
def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  match args with
  | [path, warmupText, repeatText] =>
    try
      let some warmups := warmupText.toNat? | throw <| IO.userError "invalid warmup count"
      let some repetitions := repeatText.toNat? | throw <| IO.userError "invalid repetition count"
      if repetitions = 0 then throw <| IO.userError "repetitions must be positive"
      let start ← IO.monoNanosNow
      let input ← IO.FS.readFile path
      let loaded ← IO.monoNanosNow
      let document ← match Json.parse input >>= Interchange.decodeDocument with
        | .ok document => pure document
        | .error message => throw <| IO.userError message
      let ref ← IO.mkRef document
      let decoded ← IO.monoNanosNow
      let schema ← samples ref measureSchema warmups repetitions
      let combined ← samples ref measureCombined warmups repetitions
      out.putStrLn <| (Json.mkObj [
        ("format", toJson "vlmof-validation-timing-1"),
        ("loadNanoseconds", toJson (loaded - start)),
        ("decodeNanoseconds", toJson (decoded - loaded)),
        ("objects", toJson document.snapshot.objects.length),
        ("observations", toJson document.snapshot.observations.length),
        ("schema", schema), ("schemaAndSnapshot", combined)]).compress
      return 0
    catch error =>
      out.putStrLn <| (Json.mkObj [("error", toJson error.toString)]).compress
      return 2
  | _ =>
    out.putStrLn "Usage: validationBench CORE.json WARMUPS REPETITIONS"
    return 2

