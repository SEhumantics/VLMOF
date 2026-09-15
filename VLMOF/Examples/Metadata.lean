import VLMOF.Metadata.Pilot

/-!
# Interpreting and rejecting metadata

The same checker validates descriptor objects and the interpreted Person instance.
The negative cases distinguish malformed metadata references from metadata that is
well typed but describes an invalid multiplicity. General interpreter results live
in `VLMOF.Metadata.Pilot`; these are concrete witnesses, not a universal claim of
EMOF self-description.
-/
namespace VLMOF.MetadataPilot

/-- Two metadata objects describe `Person.active : Boolean [0..1]`. The owner
reference points to the class descriptor through an ordinary observation. -/
def descriptions : Snapshot :=
  { objects := [{ id := ⟨0⟩, classifier := classKind }, { id := ⟨1⟩, classifier := attributeKind }],
    observations := [
      { object := ⟨0⟩, property := className, occurrences := [.string "Person"] },
      { object := ⟨1⟩, property := attributeName, occurrences := [.string "active"] },
      { object := ⟨1⟩, property := attributeOwner, occurrences := [.reference ⟨0⟩] },
      { object := ⟨1⟩, property := attributeType, occurrences := [.enumeration typeKind ⟨0⟩] },
      { object := ⟨1⟩, property := lowerBound, occurrences := [.integer 0] },
      { object := ⟨1⟩, property := upperBound, occurrences := [.integer 1] },
      { object := ⟨1⟩, property := ordered, occurrences := [.boolean false] },
      { object := ⟨1⟩, property := unique, occurrences := [.boolean true] }] }

/-- Expected application schema after reading the descriptor objects. -/
def personSchema : Schema :=
  { packages := [], classes := [{ id := ⟨0⟩, name := some "Person", package := none, isAbstract := false, directSupers := [] }],
    properties := [{ id := ⟨1⟩, name := some "active", owner := .class ⟨0⟩, type := .boolean, multiplicity := { lower := 0, upper := .finite 1, isOrdered := false, isUnique := true }, aggregation := .none, isId := false }],
    associations := [], enumerations := [], literals := [] }

/-- One Person with an explicitly present false value, rather than an empty slot. -/
def people : Snapshot :=
  { objects := [{ id := ⟨42⟩, classifier := ⟨0⟩ }],
    observations := [{ object := ⟨42⟩, property := ⟨1⟩, occurrences := [.boolean false] }] }

private def setValues (p : PropertyId) (values : List Value) : Snapshot :=
  { descriptions with observations := descriptions.observations.map fun a =>
      if a.property = p then { a with occurrences := values } else a }

/-- An attribute descriptor points to an object missing from the metadata store. -/
def danglingOwner := setValues attributeOwner [.reference ⟨999⟩]
/-- Integer-typed metadata describes the inconsistent interval 2..1. -/
def reversedBounds := setValues lowerBound [.integer 2]
/-- The application object supplies an Integer for the interpreted Boolean slot. -/
def wrongPeople : Snapshot :=
  { people with observations := [{ object := ⟨42⟩, property := ⟨1⟩, occurrences := [.integer 0] }] }

/-- The descriptor fixture satisfies ordinary metadata conformance. The proof
reduces the same finite checker used for application snapshots and applies its
correctness theorem. -/
theorem descriptions_conform : SnapshotConforms vocabulary descriptions := by
  apply (checkSnapshot_iff _ _).mp
  decide

/-- Executing the metadata reader constructs the expected Person schema exactly. -/
theorem interpretation_reads_descriptions : interpret descriptions = .ok personSchema := by rfl

/-- The schema described by this fixture is valid, in addition to its metadata
being well typed. The reversed-bounds example below separates these facts. -/
theorem interpreted_schema_wellFormed : SchemaWellFormed personSchema := by
  apply (checkSchema_iff _).mp
  decide

/-- A concrete application instance conforms to the interpreted schema. This is
a witness for the pilot, not a claim about every well-typed descriptor snapshot. -/
theorem people_conform : SnapshotConforms personSchema people := by
  apply (checkSnapshot_iff _ _).mp
  decide

-- Typed metadata rejects a dangling owner through the common conformance predicate.
example : checkSnapshot vocabulary danglingOwner = false := by decide
example : interpret danglingOwner = .error "invalid metadata snapshot" := by rfl
-- Bounds are well-typed Integer metadata, yet their interpreted interval is invalid.
example : checkSnapshot vocabulary reversedBounds = true := by decide
example : interpretChecked reversedBounds = .error "invalid interpreted schema" := by rfl
example : checkSnapshot personSchema wrongPeople = false := by decide


end VLMOF.MetadataPilot
