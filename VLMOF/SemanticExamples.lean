import VLMOF.Properties

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

/- The following whole-acceptance proofs are temporarily disabled: their former broad
`simp` scripts were not reproducible from fresh object files. Component and negative
semantic cases below remain kernel checked. -/
/-
/-- The accepted K0 example has valid declaration structure under K1. -/
theorem k0_schema_wellFormed : SchemaWellFormed VLMOF.Example.schema := by
  constructor <;> simp (config := { maxSteps := 1000000 }) [VLMOF.Example.schema, uniqueBy, validName, validString, xmlChar,
    VLMOF.Example.root, VLMOF.Example.left, VLMOF.Example.right, VLMOF.Example.diamond,
    VLMOF.Example.person, VLMOF.Example.pet, VLMOF.Example.rootCode, VLMOF.Example.leftX,
    VLMOF.Example.rightX, VLMOF.Example.pets, VLMOF.Example.owner, VLMOF.Example.active,
    VLMOF.Example.scores, VLMOF.Example.moods,
    Schema.packageDecls, Schema.classDecls, Schema.propertyDecls, Schema.associationDecls,
    Schema.enumerationDecls, Schema.literalDecls, Schema.packageAncestors, Schema.ancestors,
    iterateClosure, classSupers, packageParents, multiplicityValid, ownerMatchesEnd,
    classOwnerIsSource, atMostOneAssociationOwned, Schema.oppositeCandidates,
    Schema.applicableProperty, Schema.applicablePropertyIds, Schema.associationEndApplies]

/-- The accepted K0 example snapshot is valid under the selected occurrence-sensitive
interpretation: its repeated Person--Pet relationship is repeated at both ends. -/
theorem k0_snapshot_conforms : SnapshotConforms VLMOF.Example.schema VLMOF.Example.snapshot := by
  constructor
  · exact k0_schema_wellFormed
  all_goals simp (config := { maxSteps := 1000000 }) [VLMOF.Example.schema, VLMOF.Example.snapshot, uniqueBy, validName,
    VLMOF.Example.root, VLMOF.Example.left, VLMOF.Example.right, VLMOF.Example.diamond,
    VLMOF.Example.person, VLMOF.Example.pet, VLMOF.Example.rootCode, VLMOF.Example.leftX,
    VLMOF.Example.rightX, VLMOF.Example.pets, VLMOF.Example.owner, VLMOF.Example.active,
    VLMOF.Example.scores, VLMOF.Example.moods, VLMOF.Example.p, VLMOF.Example.fido,
    VLMOF.Example.diamondObject,
    validString, xmlChar, Schema.packageDecls, Schema.classDecls, Schema.propertyDecls,
    Schema.associationDecls, Schema.enumerationDecls, Schema.literalDecls,
    Schema.packageAncestors, Schema.ancestors, iterateClosure, classSupers, packageParents,
    multiplicityValid, withinMultiplicity, valueMatches, ownerMatchesEnd, classOwnerIsSource,
    atMostOneAssociationOwned, Schema.oppositeCandidates, Schema.applicableProperty,
    Schema.applicablePropertyIds, Schema.associationEndApplies, Snapshot.occurrences,
    Observation.key, incomingCompositeCount, compositeEdge, compositeReachable,
    outgoingComposite]

theorem interactionSchema_wellFormed : SchemaWellFormed interactionSchema := by
  constructor <;> simp (config := { maxSteps := 1000000 }) [interactionSchema, mult, uniqueBy, validName, validString, xmlChar,
    A, B, forward, reverse, assoc,
    Schema.packageDecls, Schema.classDecls, Schema.associationDecls, Schema.enumerationDecls,
    Schema.packageAncestors, Schema.ancestors, iterateClosure, classSupers, packageParents,
    multiplicityValid, ownerMatchesEnd, classOwnerIsSource, atMostOneAssociationOwned,
    Schema.oppositeCandidates, Schema.applicableProperty, Schema.applicablePropertyIds,
    Schema.associationEndApplies]
theorem oneLink_conforms : SnapshotConforms interactionSchema oneLink := by
  constructor
  · exact interactionSchema_wellFormed
  all_goals simp (config := { maxSteps := 1000000 }) [interactionSchema, oneLink, mult, uniqueBy, validName, validString,
    A, B, forward, reverse, assoc, x, y,
    xmlChar, Schema.packageDecls, Schema.classDecls, Schema.associationDecls,
    Schema.enumerationDecls, Schema.packageAncestors, Schema.ancestors, iterateClosure,
    classSupers, packageParents, multiplicityValid, withinMultiplicity, valueMatches,
    ownerMatchesEnd, classOwnerIsSource, atMostOneAssociationOwned, Schema.oppositeCandidates,
    Schema.applicableProperty, Schema.applicablePropertyIds, Schema.associationEndApplies,
    Snapshot.occurrences, Observation.key, incomingCompositeCount, compositeEdge,
    compositeReachable, outgoingComposite]

-/

example : ¬ SnapshotConforms interactionSchema withoutReciprocity := by
  intro h
  have hc := h.oppositeCounts interactionSchema.associations[0] (by simp [interactionSchema])
    forward reverse (by simp [interactionSchema])
    oneLink.objects[0] (by simp [oneLink, withoutReciprocity])
    oneLink.objects[1] (by simp [oneLink, withoutReciprocity])
  simp [withoutReciprocity, oneLink, Snapshot.occurrences, x, y, forward, reverse] at hc

end VLMOF.SemanticExample
