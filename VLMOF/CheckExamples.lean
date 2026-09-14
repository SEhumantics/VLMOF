import VLMOF.CheckDiagnosticsCorrect

/-! Source-derived separating cases. These cases hold all unrelated K0 rows fixed:
MOF multiplicity absence, identity uniqueness, type domains, and reciprocal counts. -/
namespace VLMOF.CheckExample
open VLMOF.Example

private def replaceValues (s : Snapshot) (o : ObjectId) (p : PropertyId)
    (values : List Value) : Snapshot :=
  { s with observations := s.observations.map fun a =>
      if a.object = o ∧ a.property = p then { a with occurrences := values } else a }

-- A diamond shares its inherited declaration once; equal display names do not
-- merge the two other properties. Repeated nonunique values and links are valid.
example : checkSchema schema = true := by native_decide
example : checkSnapshot schema snapshot = true := by native_decide

-- Optional means an empty observation is legal. False and zero are still values.
def optionalEmpty := replaceValues snapshot p active []
example : checkSnapshot schema optionalEmpty = true := by native_decide

def missingOptional : Snapshot :=
  { snapshot with observations := snapshot.observations.filter (fun a => a.property != active) }
example : Diagnostic.snapshot "observations exact" ∈ snapshotDiagnostics schema missingOptional := by native_decide

-- A duplicate key must not be hidden by a first-match lookup, even when its row is empty.
def duplicateKey : Snapshot :=
  { snapshot with observations := snapshot.observations ++ [{ object := p, property := active, occurrences := [] }] }
example : Diagnostic.snapshot "unique observation keys" ∈ snapshotDiagnostics schema duplicateKey := by native_decide

-- Integer zero cannot stand in for Boolean false.
def wrongBoolean := replaceValues snapshot p active [.integer 0]
example : Diagnostic.snapshot "values typed" ∈ snapshotDiagnostics schema wrongBoolean := by native_decide

-- The XSD String domain includes empty text but excludes U+0000.
def emptyText := replaceValues snapshot diamondObject rootCode [.string ""]
def nulText := replaceValues snapshot diamondObject rootCode [.string (String.singleton (Char.ofNat 0))]
example : checkSnapshot schema emptyText = true := by native_decide
example : Diagnostic.snapshot "values typed" ∈ snapshotDiagnostics schema nulText := by native_decide

-- One reciprocal occurrence cannot justify two forward occurrences.
def missingReciprocalOccurrence := replaceValues snapshot fido owner [.reference p]
example : Diagnostic.snapshot "opposite counts" ∈ snapshotDiagnostics schema missingReciprocalOccurrence := by native_decide

end VLMOF.CheckExample
