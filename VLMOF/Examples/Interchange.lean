import VLMOF.Interchange.Json

namespace VLMOF.Interchange.Example

open Lean

/-- The decoder preserves the raw Core records exactly; validation remains the
separate checker responsibility. -/
def tiny : Document :=
  { schema := VLMOF.Example.schema
    snapshot := VLMOF.Example.snapshot
    provenance := Json.mkObj [("source", Json.str "authored")] }

def roundTrips (d : Document) : Bool :=
  match decode (encode d) with
  | .ok (s, i) => s == d.schema && i == d.snapshot
  | .error _ => false

example : roundTrips tiny = true := by
  native_decide

example : decode (Json.mkObj [("version", "not-e1")]) = .error "E1: unsupported interchange version `not-e1`" := by
  rfl

end VLMOF.Interchange.Example
