import VLMOF
import VLMOF.Interchange.Json

open VLMOF Lean

/-- A reusable client: once a model conforms, toggling its Route.active slot
needs no additional structural side conditions. The concrete full Train runtime
experiment below selects its actual object/property IDs and checks its effect. -/
theorem toggle_accepted {s : Schema} {m : Snapshot}
    (h : checkSnapshot s m = true) (o : ObjectId) (p : PropertyId) :
    checkSnapshot s (toggleBooleanSlot m o p) = true :=
  (checkSnapshot_iff _ _).mpr (toggleBooleanSlot_conforms ((checkSnapshot_iff _ _).mp h) o p)

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

/-- Executed boundary test: compare an independently decoded retained Core input
with actual DSL parsing/elaboration, then exercise one safe and one unsafe edit.
Exact equality is tested here, not asserted as a general converter theorem. -/
def main (args : List String) : IO Unit := do
  let [corePath, dslPath] := args | throw (IO.userError "usage: CORE_JSON FULL_DSL")
  let raw ← IO.FS.readFile corePath
  let json ← IO.ofExcept (Json.parse raw)
  let d ← IO.ofExcept (Interchange.decodeDocument json)
  let ast ← IO.ofExcept (Source.parse (← IO.FS.readFile dslPath))
  let (s, m) ← IO.ofExcept (Source.elaborate ast |>.mapError reprStr)
  require (s == d.schema) "schema differs from retained Core"
  require (m == d.snapshot) "snapshot differs from retained Core"
  require (checkSnapshot s m) "full Train rejected"
  -- Full-profile declaration and object identity checks guard against silently
  -- applying the demonstration to another slot after a generator change.
  require (s.classes.length == 10 && s.properties.length == 21 &&
    s.enumerations.length == 2 && s.associations.length == 3) "coverage mismatch"
  require (s.properties.any fun q => q.id == ⟨5⟩ && q.name == some "active" &&
    q.owner == .class ⟨3⟩ && q.type == .boolean) "Route.active identity mismatch"
  require (m.objects.any fun x => x.id == ⟨1⟩ && x.classifier == ⟨3⟩) "Route object mismatch"
  require (m.occurrences ⟨1⟩ ⟨5⟩ == [.boolean true]) "expected present active=true"
  let changed := toggleBooleanSlot m ⟨1⟩ ⟨5⟩
  require (changed.occurrences ⟨1⟩ ⟨5⟩ == [.boolean false]) "toggle had no expected effect"
  require (checkSnapshot s changed) "toggled full Train rejected"
  require (toggleBooleanSlot changed ⟨1⟩ ⟨5⟩ == m) "double toggle changed snapshot"
  let invalid := { m with observations := m.observations.map fun a =>
    if a.object == ⟨1⟩ && a.property == ⟨7⟩ then {a with occurrences := a.occurrences.take 1} else a }
  require (!checkSnapshot s invalid) "one required sensor was accepted"
  require (snapshotDiagnostics s invalid == [.snapshot "multiplicity bounds"])
    "unexpected missing-sensor diagnostics"
  -- Raw edge cases: optional absence, malformed Boolean repetitions, and
  -- non-Boolean values retain their cardinalities and reference occurrences.
  require ((toggleBooleanRow ⟨0⟩ ⟨0⟩ ⟨⟨0⟩, ⟨0⟩, []⟩).occurrences == []) "absence changed"
  require ((toggleBooleanRow ⟨0⟩ ⟨0⟩ ⟨⟨0⟩, ⟨0⟩,
    [.boolean true, .boolean true, .reference ⟨9⟩]⟩).occurrences ==
    [.boolean false, .boolean false, .reference ⟨9⟩]) "occurrences collapsed"
  IO.println s!"PASS exact schema/snapshot; 10 classes, 21 features, 2 enums, 3 associations; {m.objects.length} objects, {m.observations.length} rows; active true -> false accepted; double toggle restored; one required sensor rejected for multiplicity bounds; raw edge cases passed"
