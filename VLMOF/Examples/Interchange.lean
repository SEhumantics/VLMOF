import VLMOF.Interchange.Json

/-!
# JSON codec examples

The concrete round trip checks that the codec carries the fixture's declaration
identities and occurrence lists. It does not prove a round-trip theorem for every
document, or establish conformance of an arbitrary successfully decoded input.
-/

namespace VLMOF.Interchange.Example

open Lean

/-- The decoder preserves the raw Core records exactly; validation remains the
separate checker responsibility. -/
def tiny : Document :=
  { schema := VLMOF.Example.schema
    snapshot := VLMOF.Example.snapshot
    provenance := Json.mkObj [("source", Json.str "authored")] }

/-- Compare the schema and snapshot with their decoded encoding. The model-only
decoder does not inspect or compare producer metadata.
This executable test is used below on a fixed fixture; it is not a universal
serialization guarantee. -/
def roundTrips (d : Document) : Bool :=
  match decode (encode d) with
  | .ok (s, i) => s == d.schema && i == d.snapshot
  | .error _ => false

example : roundTrips tiny = true := by
  native_decide

example : decode (Json.mkObj [("version", "not-e1")]) = .error "E1: unsupported interchange version `not-e1`" := by
  rfl

end VLMOF.Interchange.Example
