import VLMOF.Model.Properties
import VLMOF.Checker.Correctness.Acceptance
import VLMOF.Examples.Model

/-!
# Semantic examples

These cases exercise the diamond/association fixture and the interaction theorem. The duplicated
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

/-- The shared diamond/association fixture satisfies the schema constraints.
The proof reduces the finite checker and uses checker correctness; it does not
assume that constructing the raw fixture made it valid. -/
theorem k0_schema_wellFormed : SchemaWellFormed VLMOF.Example.schema := by
  apply (checkSchema_iff _).mp
  decide

/-- The fixture's snapshot conforms with inherited properties and an
association-owned end represented through the ordinary occurrence store. -/
theorem k0_snapshot_conforms : SnapshotConforms VLMOF.Example.schema VLMOF.Example.snapshot := by
  apply (checkSnapshot_iff _ _).mp
  decide

/-- The two-end schema used to study reciprocity and the upper-one bound is
itself valid; the interaction example is not vacuous because of an invalid schema. -/
theorem interactionSchema_wellFormed : SchemaWellFormed interactionSchema := by
  apply (checkSchema_iff _).mp
  decide

/-- A single reciprocal link witnesses satisfiability of the interaction
theorem's premises. The duplicated variants above separate those premises. -/
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

/-- A zero-upper reference declaration is structurally valid even though its
owning class does not meet Factory.create's positive-upper bound prerequisite.
The reverse end remains optional, so the all-empty snapshot is a real witness. -/
def zeroBoundSchema : Schema :=
  { interactionSchema with properties := interactionSchema.properties.map fun p =>
      if p.id = forward then
        { p with multiplicity := { p.multiplicity with upper := .finite 0 } }
      else p }

/-- Complete observations distinguish empty property values from missing rows. -/
def emptyLinks : Snapshot :=
  { oneLink with observations := oneLink.observations.map fun o =>
      { o with occurrences := [] } }

/-- This witnesses structural conformance rather than just interval arithmetic. -/
theorem zeroBound_empty_conforms : SnapshotConforms zeroBoundSchema emptyLinks := by
  apply (checkSnapshot_iff _ _).mp
  decide

/-- A single reference exceeds the zero bound; accepting the schema does not
remove the snapshot obligation to obey its declared multiplicities. -/
theorem zeroBound_nonempty_rejected : ¬ SnapshotConforms zeroBoundSchema oneLink := by
  intro h
  have checked := (checkSnapshot_iff zeroBoundSchema oneLink).mpr h
  have rejected : checkSnapshot zeroBoundSchema oneLink = false := by decide
  rw [rejected] at checked
  contradiction

/-- The zero-upper class is not creation-bound-ready, despite a conforming
static snapshot. Static state validity does not imply reflective reachability. -/
theorem zeroBound_not_creation_ready : ¬ zeroBoundSchema.classCreationBounds A := by
  intro h
  have hp : zeroBoundSchema.properties[0] ∈ zeroBoundSchema.properties := by
    simp [zeroBoundSchema, interactionSchema]
  have bound := h.2 zeroBoundSchema.properties[0] hp A (by decide) (by decide)
  have impossible : ¬ zeroBoundSchema.properties[0].multiplicity.creationBounds := by
    simp [zeroBoundSchema, interactionSchema, forward, reverse,
      Multiplicity.creationBounds, Upper.allows]
  exact impossible bound

/-- One unpaired composite feature is nonunique and has unlimited upper bound.
No opposite container property is manufactured for this declaration. -/
def unpairedContainmentSchema : Schema :=
  { interactionSchema with
    properties := [{ interactionSchema.properties[0] with aggregation := .composite }]
    associations := [] }

/-- One parent mentions one child twice in the same nonunique composite slot. -/
def repeatedContainedChild : Snapshot :=
  { objects := oneLink.objects
    observations := [{ object := x, property := forward, occurrences := [.reference y, .reference y] }] }

/-- Occurrence multiplicity two is compatible with one container object. This
separates the source-supported rule from the former incoming-occurrence bound. -/
theorem repeated_unpaired_child_conforms :
    SnapshotConforms unpairedContainmentSchema repeatedContainedChild := by
  apply (checkSnapshot_iff _ _).mp
  decide

/-- The old aggregate count would have rejected the preceding conforming state. -/
theorem repeated_child_has_two_incoming_occurrences :
    incomingCompositeCount unpairedContainmentSchema repeatedContainedChild y = 2 := by
  decide

/-- A different parent creates an ownership conflict even without opposites. -/
def twoContainers : Snapshot :=
  { repeatedContainedChild with
    objects := oneLink.objects ++ [{ id := ⟨202⟩, classifier := A }]
    observations := repeatedContainedChild.observations ++
      [{ object := ⟨202⟩, property := forward, occurrences := [.reference y] }] }

/-- Distinct container identities violate conformance. -/
theorem two_containers_rejected : ¬ SnapshotConforms unpairedContainmentSchema twoContainers := by
  intro h
  have hc := (checkSnapshot_iff _ _).mpr h
  have hn : checkSnapshot unpairedContainmentSchema twoContainers = false := by decide
  rw [hn] at hc
  contradiction

/-- Two unpaired forward features may name the same container object. The
mandatory source does not supply an implicit opposite for either feature. -/
def twoUnpairedFeatures : Schema :=
  { unpairedContainmentSchema with properties := unpairedContainmentSchema.properties ++
      [{ unpairedContainmentSchema.properties[0] with id := ⟨202⟩, name := some "other" }] }

/-- Both unpaired forward slots use one parent identity and one child identity. -/
def sameParentTwoFeatures : Snapshot :=
  { repeatedContainedChild with observations := repeatedContainedChild.observations ++
      [{ object := x, property := ⟨202⟩, occurrences := [.reference y] }] }

/-- One-parent ownership differs from the stronger unique-forward-slot policy
used by some runtimes. This witness makes that boundary explicit. -/
theorem same_parent_two_unpaired_features_conform :
    SnapshotConforms twoUnpairedFeatures sameParentTwoFeatures := by
  apply (checkSnapshot_iff _ _).mp
  decide

/-- Two separate paired composite roles have two separate reverse properties. -/
def twoPairedRoles : Schema :=
  { interactionSchema with
    properties :=
      [{ interactionSchema.properties[0] with aggregation := .composite },
       interactionSchema.properties[1],
       { interactionSchema.properties[0] with id := ⟨202⟩, name := some "otherForward", aggregation := .composite },
       { interactionSchema.properties[1] with id := ⟨203⟩, name := some "otherReverse" }]
    associations := interactionSchema.associations ++
      [{ id := ⟨201⟩, name := some "OtherAB", package := some ⟨200⟩,
         ends := (⟨202⟩, ⟨203⟩) }] }

/-- Both inverse pairs are reciprocal and within their bounds, but their reverse
container roles are simultaneously nonempty. -/
def sameParentTwoRoles : Snapshot :=
  { oneLink with observations := oneLink.observations ++
      [{ object := x, property := ⟨202⟩, occurrences := [.reference y] },
       { object := y, property := ⟨203⟩, occurrences := [.reference x] }] }

/-- The counterexample's schema itself is well formed: the defect is in the
instance having two active container roles, not invalid association metadata. -/
theorem two_paired_roles_schema_valid : SchemaWellFormed twoPairedRoles := by
  apply (checkSchema_iff _).mp
  decide

/-- One container object alone does not establish containment validity. -/
theorem same_parent_two_roles_one_object : SingleContainer twoPairedRoles sameParentTwoRoles y := by
  decide

/-- Two nonempty reverse container roles violate the second source obligation. -/
theorem same_parent_two_roles_rejected : ¬ SnapshotConforms twoPairedRoles sameParentTwoRoles := by
  intro h
  have hc := (checkSnapshot_iff _ _).mpr h
  have hn : checkSnapshot twoPairedRoles sameParentTwoRoles = false := by decide
  rw [hn] at hc
  contradiction

/-- The two-role counterexample fails only the ownership category: typing,
multiplicity, opposite counts and all other snapshot checks pass. -/
theorem two_roles_fail_only_ownership :
    snapshotDiagnostics twoPairedRoles sameParentTwoRoles =
      [.snapshot "one container and active container property"] := by
  decide

end VLMOF.SemanticExample
