/-!
# Finite raw representation for the selected structural MOF fragment

This module deliberately represents raw finite schemas and snapshots.  It does not
assert schema well-formedness or object conformance.  Later predicates can therefore
diagnose dangling references, inheritance cycles, inconsistent ownership, invalid
bounds, and other malformed records instead of losing them during construction.

Declaration identity is separate from the optional spelling carried as metadata.
Source-language name resolution belongs in an elaboration layer which produces these
identities.  In particular, inherited properties are referenced by `PropertyId`, so
the two paths through a diamond still reach one declaration, while two declarations
with the same name remain different.
-/

namespace VLMOF

structure PackageId where val : Nat deriving DecidableEq, Repr
structure ClassId where val : Nat deriving DecidableEq, Repr
structure PropertyId where val : Nat deriving DecidableEq, Repr
structure AssociationId where val : Nat deriving DecidableEq, Repr
structure EnumerationId where val : Nat deriving DecidableEq, Repr
structure LiteralId where val : Nat deriving DecidableEq, Repr
structure ObjectId where val : Nat deriving DecidableEq, Repr

/-- A normalized upper multiplicity.  Positivity is checked later, so zero remains
representable for diagnostics. -/
inductive Upper where
  | finite (value : Nat)
  | unlimited
  deriving DecidableEq, Repr

structure Multiplicity where
  lower : Nat
  upper : Upper
  isOrdered : Bool
  isUnique : Bool
  deriving DecidableEq, Repr

inductive ValueType where
  | boolean
  | integer
  | string
  | enumeration (id : EnumerationId)
  | reference (id : ClassId)
  deriving DecidableEq, Repr

inductive PropertyOwner where
  | class (id : ClassId)
  | association (id : AssociationId)
  deriving DecidableEq, Repr

inductive Aggregation where
  | none
  | composite
  deriving DecidableEq, Repr

structure PackageDecl where
  id : PackageId
  name : Option String
  parent : Option PackageId
  deriving DecidableEq, Repr

structure ClassDecl where
  id : ClassId
  name : Option String
  package : Option PackageId
  isAbstract : Bool
  directSupers : List ClassId
  deriving DecidableEq, Repr

structure PropertyDecl where
  id : PropertyId
  name : Option String
  owner : PropertyOwner
  type : ValueType
  multiplicity : Multiplicity
  aggregation : Aggregation
  isId : Bool
  deriving DecidableEq, Repr

/-- Binary arity is structural.  Membership is kept on the association rather than
duplicated as arbitrary `opposite` pointers.  At most one end may be association-owned,
but malformed ownership and dangling end identifiers remain representable. -/
structure AssociationDecl where
  id : AssociationId
  name : Option String
  package : Option PackageId
  ends : PropertyId × PropertyId
  deriving DecidableEq, Repr

structure EnumerationDecl where
  id : EnumerationId
  name : Option String
  package : Option PackageId
  deriving DecidableEq, Repr

structure LiteralDecl where
  id : LiteralId
  name : Option String
  enumeration : EnumerationId
  deriving DecidableEq, Repr

/-- Finite stores are lists so duplicate identifiers and dangling references survive
long enough for a later validator to report them. -/
structure Schema where
  packages : List PackageDecl
  classes : List ClassDecl
  properties : List PropertyDecl
  associations : List AssociationDecl
  enumerations : List EnumerationDecl
  literals : List LiteralDecl
  deriving DecidableEq, Repr

inductive Value where
  | boolean (value : Bool)
  | integer (value : Int)
  | string (value : String)
  | enumeration (enumeration : EnumerationId) (literal : LiteralId)
  | reference (object : ObjectId)
  deriving DecidableEq, Repr

structure ObjectDecl where
  id : ObjectId
  classifier : ClassId
  deriving DecidableEq, Repr

/-- One common observation path covers ordinary properties and every association end.
For an association-owned nonnavigable end this is incidence data, not a reflective slot.
Its applicable source class is derived later from the other end's reference type. -/
structure Observation where
  object : ObjectId
  property : PropertyId
  occurrences : List Value
  deriving DecidableEq, Repr

structure Snapshot where
  objects : List ObjectDecl
  observations : List Observation
  deriving DecidableEq, Repr

/-- The candidates for an end's opposite, derived only from binary end membership.
Several candidates expose malformed duplicate membership rather than choosing a pointer. -/
def Schema.oppositeCandidates (schema : Schema) (endId : PropertyId) : List PropertyId :=
  schema.associations.flatMap fun association =>
    if association.ends.1 = endId then [association.ends.2]
    else if association.ends.2 = endId then [association.ends.1]
    else []

/-- Observable equality for an occurrence collection.  Ordering changes observation;
uniqueness is a later validity condition and never erases duplicate occurrences here. -/
def Occurrences.equivalent (isOrdered : Bool) (left right : List Value) : Prop :=
  if isOrdered then left = right else left.Perm right

namespace Example

private def many (ordered unique : Bool) : Multiplicity :=
  { lower := 0, upper := .unlimited, isOrdered := ordered, isUnique := unique }

def root : ClassId := ⟨0⟩
def left : ClassId := ⟨1⟩
def right : ClassId := ⟨2⟩
def diamond : ClassId := ⟨3⟩
def person : ClassId := ⟨4⟩
def pet : ClassId := ⟨5⟩

def rootCode : PropertyId := ⟨0⟩
def leftX : PropertyId := ⟨1⟩
def rightX : PropertyId := ⟨2⟩
def pets : PropertyId := ⟨3⟩
def owner : PropertyId := ⟨4⟩
def active : PropertyId := ⟨5⟩
def scores : PropertyId := ⟨6⟩
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
       { id := owner, name := none, owner := .association ⟨0⟩, type := .reference person,
         multiplicity := many false false, aggregation := .none, isId := false },
       { id := active, name := some "active", owner := .class person, type := .boolean,
         multiplicity := many false true, aggregation := .none, isId := false },
       { id := scores, name := some "scores", owner := .class person, type := .integer,
         multiplicity := many false false, aggregation := .none, isId := false },
       { id := moods, name := some "moods", owner := .class person,
         type := .enumeration ⟨0⟩, multiplicity := many false false,
         aggregation := .none, isId := false }]
    associations := [{ id := ⟨0⟩, name := some "PersonPet", package := some ⟨0⟩,
                       ends := (pets, owner) }]
    enumerations := [{ id := ⟨0⟩, name := some "Mood", package := some ⟨0⟩ }]
    literals := [{ id := ⟨0⟩, name := some "happy", enumeration := ⟨0⟩ }] }

def p : ObjectId := ⟨0⟩
def fido : ObjectId := ⟨1⟩

/-- Repeated links are retained at both ends.  Empty observations express optional
absence and are distinct from `[.boolean false]`, `[.integer 0]`, or `[.string ""]`. -/
def snapshot : Snapshot :=
  { objects := [{ id := p, classifier := person }, { id := fido, classifier := pet }]
    observations :=
      [{ object := p, property := pets,
         occurrences := [.reference fido, .reference fido] },
       { object := fido, property := owner,
         occurrences := [.reference p, .reference p] },
       { object := p, property := rootCode, occurrences := [] },
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

example : schema.oppositeCandidates pets = [owner] := rfl
example : Occurrences.equivalent false [.integer 1, .integer 2] [.integer 2, .integer 1] := by
  simp only [Occurrences.equivalent, Bool.false_eq_true, ↓reduceIte]
  exact .swap (Value.integer 2) (Value.integer 1) []
example : ¬ Occurrences.equivalent true [.integer 1, .integer 2] [.integer 2, .integer 1] := by
  simp [Occurrences.equivalent]
example : Occurrences.equivalent false [.string "x", .string "x"] [.string "x", .string "x"] := by
  simp [Occurrences.equivalent]

end Example
end VLMOF
