import VLMOF.Model.Properties
import VLMOF.Checker.Correctness.Acceptance

/-!
# Semantic examples

These cases exercise the raw K0 example and the interaction theorem.  The duplicated
snapshots separate the theorem's two material premises: reciprocity and upper one.
-/

namespace VLMOF.SemanticExample

set_option maxHeartbeats 2000000

open VLMOF

private def mult (upper : Upper) (unique : Bool := false) : Multiplicity :=
  { lower := 0, upper, isOrdered := false, isUnique := unique }

def A : ClassId := ⟨200⟩
def B : ClassId := ⟨201⟩
def forward : PropertyId := ⟨200⟩
def reverse : PropertyId := ⟨201⟩
def assoc : AssociationId := ⟨200⟩
def x : ObjectId := ⟨200⟩
def y : ObjectId := ⟨201⟩

/-- The forward end is expressly non-unique; the reverse end has upper one. -/
def interactionSchema : Schema :=
  { packages := [{ id := ⟨200⟩, name := some "P", parent := none }]
    classes :=
      [{ id := A, name := some "A", package := some ⟨200⟩, isAbstract := false,
         directSupers := [] },
       { id := B, name := some "B", package := some ⟨200⟩, isAbstract := false,
         directSupers := [] }]
    properties :=
      [{ id := forward, name := some "forward", owner := .class A, type := .reference B,
         multiplicity := mult .unlimited false, aggregation := .none, isId := false },
       { id := reverse, name := some "reverse", owner := .class B, type := .reference A,
         multiplicity := mult (.finite 1) false, aggregation := .none, isId := false }]
    associations :=
      [{ id := assoc, name := some "AB", package := some ⟨200⟩,
         ends := (forward, reverse) }]
    enumerations := []
    literals := [] }

def oneLink : Snapshot :=
  { objects := [{ id := x, classifier := A }, { id := y, classifier := B }]
    observations :=
      [{ object := x, property := forward, occurrences := [.reference y] },
       { object := y, property := reverse, occurrences := [.reference x] }] }

/-- Dropping reciprocity admits repetition while every local multiplicity still holds. -/
def withoutReciprocity : Snapshot :=
  { objects := oneLink.objects
    observations :=
      [{ object := x, property := forward, occurrences := [.reference y, .reference y] },
       { object := y, property := reverse, occurrences := [.reference x] }] }

/-- Raising the reverse upper bound admits reciprocal repeated occurrences. -/
def withoutUpperOne : Snapshot :=
  { objects := oneLink.objects
    observations :=
      [{ object := x, property := forward, occurrences := [.reference y, .reference y] },
       { object := y, property := reverse, occurrences := [.reference x, .reference x] }] }

def bothComposite : Schema :=
  { interactionSchema with properties := interactionSchema.properties.map fun p =>
      { p with aggregation := .composite } }

def orphan : PropertyId := ⟨202⟩
def orphanAssociationEnd : Schema :=
  { interactionSchema with properties := interactionSchema.properties ++
      [{ id := orphan, name := some "orphan", owner := .association assoc,
         type := .reference A, multiplicity := mult .unlimited,
         aggregation := .none, isId := false }] }

example : validString "" := by simp [validString]
example : ¬ validString (String.singleton '\u0000') := by simp [validString, xmlChar]

example : interactionSchema.isSubtype A A := by native_decide
example : interactionSchema.applicableProperty A forward := by native_decide
example : interactionSchema.applicableProperty B reverse := by native_decide
example : oneLink.occurrences x forward = [.reference y] := by native_decide
example : withoutReciprocity.occurrences x forward = [.reference y, .reference y] := by native_decide
example : withoutReciprocity.occurrences y reverse = [.reference x] := by native_decide
example : withoutUpperOne.occurrences y reverse = [.reference x, .reference x] := by native_decide
example : withinMultiplicity (mult .unlimited) 2 := by simp [mult, withinMultiplicity]
example : withinMultiplicity (mult (.finite 1)) 1 := by simp [mult, withinMultiplicity]
example :
    (withoutUpperOne.occurrences x forward).count (.reference y) =
    (withoutUpperOne.occurrences y reverse).count (.reference x) := by native_decide
example :
    (withoutReciprocity.occurrences x forward).count (.reference y) ≠
    (withoutReciprocity.occurrences y reverse).count (.reference x) := by native_decide

example : ¬ SchemaWellFormed bothComposite := by
  intro h
  have hb := h.associationEnds bothComposite.associations[0] (by simp [bothComposite, interactionSchema])
  rcases hb with ⟨p, q, hends, hp, hq, hrest⟩
  simp [bothComposite, interactionSchema] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    simp [forward, reverse] at hends hrest

example : ¬ SchemaWellFormed orphanAssociationEnd := by
  intro h
  have ho := h.propertyOwnersResolved orphanAssociationEnd.properties[2]
    (by simp [orphanAssociationEnd, interactionSchema])
  simp [orphanAssociationEnd, interactionSchema, orphan, assoc, forward, reverse] at ho

/-- The checker correspondence certifies the unchanged K0 declaration fixture. -/
theorem k0_schema_wellFormed : SchemaWellFormed VLMOF.Example.schema := by
  apply (checkSchema_iff _).mp
  decide

/-- Repeated values and reciprocal repeated links in the K0 snapshot conform. -/
theorem k0_snapshot_conforms : SnapshotConforms VLMOF.Example.schema VLMOF.Example.snapshot := by
  apply (checkSnapshot_iff _ _).mp
  decide

theorem interactionSchema_wellFormed : SchemaWellFormed interactionSchema := by
  apply (checkSchema_iff _).mp
  decide

theorem oneLink_conforms : SnapshotConforms interactionSchema oneLink := by
  apply (checkSnapshot_iff _ _).mp
  decide
example : ¬ SnapshotConforms interactionSchema withoutReciprocity := by
  intro h
  have hc := h.oppositeCounts interactionSchema.associations[0] (by simp [interactionSchema])
    forward reverse (by simp [interactionSchema])
    oneLink.objects[0] (by simp [oneLink, withoutReciprocity])
    oneLink.objects[1] (by simp [oneLink, withoutReciprocity])
  simp [withoutReciprocity, oneLink, Snapshot.occurrences, x, y, forward, reverse] at hc

end VLMOF.SemanticExample

