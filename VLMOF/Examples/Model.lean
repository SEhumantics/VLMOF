import VLMOF.Model.Reachability.Basic

/-!
# Executable examples for the raw model and reachability layers

These fixtures deliberately live outside `VLMOF.Model.Basic` so importing the raw
representation does not also import a large research example. They exercise identity
based inheritance, association incidence, occurrence preservation, malformed input,
and a raw metadata sketch. Production modules must not depend on these values.
-/

namespace VLMOF
namespace Example


/-- Construct the recurring optional-unlimited multiplicity while varying collection
order and uniqueness for the fixture's occurrence examples. -/
private def many (ordered unique : Bool) : Multiplicity :=
  { lower := 0, upper := .unlimited, isOrdered := ordered, isUnique := unique }

/-- Abstract root shared by both inheritance branches. -/
def root : ClassId := ⟨0⟩
/-- Left direct subclass of `root` in the diamond. -/
def left : ClassId := ⟨1⟩
/-- Right direct subclass of `root` in the diamond. -/
def right : ClassId := ⟨2⟩
/-- Concrete subclass inheriting through both `left` and `right`. -/
def diamond : ClassId := ⟨3⟩
/-- Source class for the navigable `pets` association end. -/
def person : ClassId := ⟨4⟩
/-- Target class for the navigable `pets` association end. -/
def pet : ClassId := ⟨5⟩

/-- Identity property inherited once through the diamond despite two paths. -/
def rootCode : PropertyId := ⟨0⟩
/-- Integer property declared on the left branch; its spelling collides intentionally. -/
def leftX : PropertyId := ⟨1⟩
/-- Distinct integer property on the right branch with the same optional name. -/
def rightX : PropertyId := ⟨2⟩
/-- Ordered, non-unique navigable end from `person` to `pet`. -/
def pets : PropertyId := ⟨3⟩
/-- Association-owned opposite end used to record nonnavigable incidence. -/
def owner : PropertyId := ⟨4⟩
/-- Optional Boolean slot distinguishing absence from `false`. -/
def active : PropertyId := ⟨5⟩
/-- Non-unique integer slot preserving repeated zero occurrences. -/
def scores : PropertyId := ⟨6⟩
/-- Enumeration slot preserving repeated literal occurrences. -/
def moods : PropertyId := ⟨7⟩

/-- A diamond shares `rootCode` by identity.  `leftX` and `rightX` deliberately have
the same spelling but remain distinct declarations.  `owner` is association-owned and
therefore nonnavigable, while its observations still record incidence. -/
def schema : Schema :=
  { packages := [{ id := ⟨0⟩, name := some "example", parent := none }]
    classes :=
      [{ id := root, name := some "Root", package := some ⟨0⟩, isAbstract := true,
         directSupers := [] },
       { id := left, name := some "Left", package := some ⟨0⟩, isAbstract := false,
         directSupers := [root] },
       { id := right, name := some "Right", package := some ⟨0⟩, isAbstract := false,
         directSupers := [root] },
       { id := diamond, name := some "Diamond", package := some ⟨0⟩, isAbstract := false,
         directSupers := [left, right] },
       { id := person, name := some "Person", package := some ⟨0⟩, isAbstract := false,
         directSupers := [] },
       { id := pet, name := some "Pet", package := some ⟨0⟩, isAbstract := false,
         directSupers := [] }]
    properties :=
      [{ id := rootCode, name := some "code", owner := .class root, type := .string,
         multiplicity := many false true, aggregation := .none, isId := true },
       { id := leftX, name := some "x", owner := .class left, type := .integer,
         multiplicity := many false true, aggregation := .none, isId := false },
       { id := rightX, name := some "x", owner := .class right, type := .integer,
         multiplicity := many false true, aggregation := .none, isId := false },
       { id := pets, name := some "pets", owner := .class person, type := .reference pet,
         multiplicity := many true false, aggregation := .none, isId := false },
       { id := owner, name := some "owner", owner := .association ⟨0⟩, type := .reference person,
         multiplicity := many false false, aggregation := .none, isId := false },
       { id := active, name := some "active", owner := .class person, type := .boolean,
         multiplicity := { lower := 0, upper := .finite 1, isOrdered := false,
                           isUnique := true },
         aggregation := .none, isId := false },
       { id := scores, name := some "scores", owner := .class person, type := .integer,
         multiplicity := many false false, aggregation := .none, isId := false },
       { id := moods, name := some "moods", owner := .class person,
         type := .enumeration ⟨0⟩, multiplicity := many false false,
         aggregation := .none, isId := false }]
    associations := [{ id := ⟨0⟩, name := some "PersonPet", package := some ⟨0⟩,
                       ends := (pets, owner) }]
    enumerations := [{ id := ⟨0⟩, name := some "Mood", package := some ⟨0⟩ }]
    literals := [{ id := ⟨0⟩, name := some "happy", enumeration := ⟨0⟩ }] }

/-- The fixture's `person` instance. -/
def p : ObjectId := ⟨0⟩
/-- The fixture's `pet` instance and repeated association target. -/
def fido : ObjectId := ⟨1⟩
/-- Concrete diamond instance used to observe inherited properties by identity. -/
def diamondObject : ObjectId := ⟨2⟩

/-- Repeated links are retained at both ends.  Empty observations express optional
absence and are distinct from `[.boolean false]`, `[.integer 0]`, or `[.string ""]`. -/
def snapshot : Snapshot :=
  { objects :=
      [{ id := p, classifier := person }, { id := fido, classifier := pet },
       { id := diamondObject, classifier := diamond }]
    observations :=
      [{ object := p, property := pets,
         occurrences := [.reference fido, .reference fido] },
       { object := fido, property := owner,
         occurrences := [.reference p, .reference p] },
       { object := diamondObject, property := rootCode, occurrences := [] },
       { object := diamondObject, property := leftX, occurrences := [.integer 1] },
       { object := diamondObject, property := rightX, occurrences := [.integer 2] },
       { object := p, property := active, occurrences := [.boolean false] },
       { object := p, property := scores, occurrences := [.integer 0, .integer 0] },
       { object := p, property := moods,
         occurrences := [.enumeration ⟨0⟩ ⟨0⟩, .enumeration ⟨0⟩ ⟨0⟩] }] }

/-- Raw malformed schemas compile: this one has a cycle, a dangling superclass, a
zero upper bound below its lower bound, and association-end ownership disagreement. -/
def malformed : Schema :=
  { packages := []
    classes :=
      [{ id := ⟨90⟩, name := none, package := some ⟨99⟩, isAbstract := false,
         directSupers := [⟨90⟩, ⟨99⟩] }]
    properties :=
      [{ id := ⟨90⟩, name := some "bad", owner := .class ⟨98⟩, type := .reference ⟨97⟩,
         multiplicity := { lower := 2, upper := .finite 0, isOrdered := false,
                           isUnique := false },
         aggregation := .composite, isId := false }]
    associations := [{ id := ⟨90⟩, name := none, package := none, ends := (⟨90⟩, ⟨91⟩) }]
    enumerations := []
    literals := [{ id := ⟨90⟩, name := none, enumeration := ⟨99⟩ }] }

/-- Raw snapshots likewise retain dangling objects/properties, duplicate observation
keys, and ill-typed values for later diagnostics. -/
def malformedSnapshot : Snapshot :=
  { objects := [{ id := ⟨90⟩, classifier := ⟨99⟩ }]
    observations :=
      [{ object := ⟨90⟩, property := ⟨99⟩, occurrences := [.string "wrong type"] },
       { object := ⟨90⟩, property := ⟨99⟩, occurrences := [.reference ⟨98⟩] }] }

/-! ## Raw metadata sketch

This pair only shows that the ordinary model constructors can encode a bounded
metadata-shaped object. `VLMOF.Metadata.Pilot` gives the separate fixed-point pilot
and its proved well-formedness and conformance properties.
-/

/-- A raw schema with an ordinary `Class` object type and required `name` property.
It introduces no privileged metadata value or observation path and makes no
self-description claim. -/
def metadataSchema : Schema :=
  { packages := [{ id := ⟨100⟩, name := some "metadata", parent := none }]
    classes := [{ id := ⟨100⟩, name := some "Class", package := some ⟨100⟩,
                  isAbstract := false, directSupers := [] }]
    properties :=
      [{ id := ⟨100⟩, name := some "name", owner := .class ⟨100⟩, type := .string,
         multiplicity := { lower := 1, upper := .finite 1, isOrdered := false,
                           isUnique := true },
         aggregation := .none, isId := false }]
    associations := []
    enumerations := []
    literals := [] }

/-- One ordinary object representing a class description by storing the string
`"Person"` in the raw metadata sketch's `name` property. -/
def metadataSnapshot : Snapshot :=
  { objects := [{ id := ⟨100⟩, classifier := ⟨100⟩ }]
    observations :=
      [{ object := ⟨100⟩, property := ⟨100⟩, occurrences := [.string "Person"] }] }

example : schema.oppositeCandidates pets = [owner] := rfl
example : Occurrences.equivalent false [.integer 1, .integer 2] [.integer 2, .integer 1] := by
  simp only [Occurrences.equivalent, Bool.false_eq_true, ↓reduceIte]
  exact .swap (Value.integer 2) (Value.integer 1) []
example : ¬ Occurrences.equivalent true [.integer 1, .integer 2] [.integer 2, .integer 1] := by
  simp [Occurrences.equivalent]
example : ([] : List Value) ≠ [.boolean false] := by simp
example : ¬ Occurrences.equivalent false [.string "x", .string "x"] [.string "x"] := by
  simp [Occurrences.equivalent]

end Example

namespace ClosureExample

/-- The K0 diamond reaches its root once despite two inheritance paths, demonstrating
that ancestor closure deduplicates declaration identities rather than paths. -/
example : VLMOF.Example.schema.ancestors VLMOF.Example.diamond =
    [VLMOF.Example.diamond, VLMOF.Example.left, VLMOF.Example.right,
      VLMOF.Example.root] := by native_decide

end ClosureExample
end VLMOF
