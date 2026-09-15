import VLMOF.Checker.Correctness.Acceptance

/-!
# Bounded metadata pilot

Class and scalar-attribute descriptions are ordinary objects checked by the same
SnapshotConforms predicate as application data. The interpretation below reads
these objects to construct a schema; this is not full EMOF self-description.

The vocabulary is deliberately small: class descriptors have a name; attribute
descriptors have a name, owner, scalar type, bounds, ordering and uniqueness.
`interpret` first checks metadata conformance and reads these ordinary observations.
`interpretChecked` also validates the resulting schema, because typing the two
bound fields as Integers does not express the relation lower ≤ upper.

The general theorems below expose these two distinct guarantees. The Person
fixture and corrupted-metadata examples live in `VLMOF.Examples.Metadata`.
-/
namespace VLMOF.MetadataPilot

/-- Classifier of objects that describe application classes. -/
def classKind : ClassId := ⟨100⟩
/-- Classifier of objects that describe scalar attributes of application classes. -/
def attributeKind : ClassId := ⟨101⟩
/-- Enumeration identifying the three scalar types supported by this interpreter. -/
def typeKind : EnumerationId := ⟨100⟩
/-- String-valued name slot of a class descriptor. -/
def className : PropertyId := ⟨200⟩
/-- String-valued name slot of an attribute descriptor. -/
def attributeName : PropertyId := ⟨201⟩
/-- Reference from an attribute descriptor to its owning class descriptor. -/
def attributeOwner : PropertyId := ⟨202⟩
/-- Scalar-type enumeration slot of an attribute descriptor. -/
def attributeType : PropertyId := ⟨203⟩
/-- Integer observation interpreted as the attribute's nonnegative lower bound. -/
def lowerBound : PropertyId := ⟨204⟩
/-- Integer observation interpreted as a finite upper bound; unlimited is omitted. -/
def upperBound : PropertyId := ⟨205⟩
/-- Boolean observation specifying whether attribute occurrence order matters. -/
def ordered : PropertyId := ⟨206⟩
/-- Boolean observation requiring duplicate-free attribute values when true. -/
def unique : PropertyId := ⟨207⟩

private def field (id : PropertyId) (name : String) (owner : ClassId) (type : ValueType) : PropertyDecl :=
  { id, name := some name, owner := .class owner, type,
    multiplicity := { lower := 1, upper := .finite 1, isOrdered := false, isUnique := true },
    aggregation := .none, isId := false }

/-- An ordinary schema for class and scalar-attribute descriptors. Each slot is
required and single-valued. Cross-field semantic constraints, such as consistency
of lower and upper bounds, belong to the interpreted schema's validity check. -/
def vocabulary : Schema :=
  { packages := [],
    classes := [{ id := classKind, name := some "ClassDescription", package := none,
                  isAbstract := false, directSupers := [] },
                { id := attributeKind, name := some "AttributeDescription", package := none,
                  isAbstract := false, directSupers := [] }],
    properties := [field className "name" classKind .string,
      field attributeName "name" attributeKind .string,
      field attributeOwner "owner" attributeKind (.reference classKind),
      field attributeType "type" attributeKind (.enumeration typeKind),
      field lowerBound "lower" attributeKind .integer,
      field upperBound "upper" attributeKind .integer,
      field ordered "ordered" attributeKind .boolean,
      field unique "unique" attributeKind .boolean],
    associations := [],
    enumerations := [{ id := typeKind, name := some "ScalarType", package := none }],
    literals := [{ id := ⟨0⟩, name := some "Boolean", enumeration := typeKind },
                 { id := ⟨1⟩, name := some "Integer", enumeration := typeKind },
                 { id := ⟨2⟩, name := some "String", enumeration := typeKind }] }

/-- Read exactly one String occurrence through the same object/property lookup
used by application snapshots. Empty or ill-typed observations fail explicitly. -/
def text (m : Snapshot) (o : ObjectId) (p : PropertyId) : Except String String :=
  match m.occurrences o p with
  | [.string value] => .ok value
  | _ => .error "expected one String observation"

private def natural (m : Snapshot) (o : ObjectId) (p : PropertyId) : Except String Nat :=
  match m.occurrences o p with
  | [.integer value] => if value < 0 then .error "negative metadata bound" else .ok value.toNat
  | _ => .error "expected one Integer observation"

private def boolean (m : Snapshot) (o : ObjectId) (p : PropertyId) : Except String Bool :=
  match m.occurrences o p with
  | [.boolean value] => .ok value
  | _ => .error "expected one Boolean observation"

private def owner (m : Snapshot) (o : ObjectId) : Except String ClassId :=
  match m.occurrences o attributeOwner with
  | [.reference target] => .ok ⟨target.val⟩
  | _ => .error "expected one owner reference"

private def scalarType (m : Snapshot) (o : ObjectId) : Except String ValueType :=
  match m.occurrences o attributeType with
  | [.enumeration e l] =>
    if e ≠ typeKind then .error "wrong scalar enumeration"
    else match l.val with
      | 0 => .ok .boolean | 1 => .ok .integer | 2 => .ok .string
      | _ => .error "unsupported scalar literal"
  | _ => .error "expected one scalar type observation"

/-- The pilot maps descriptor object identity to declaration identity. It supports
concrete root classes and scalar attributes with finite bounds; inheritance,
packages, references, associations and unlimited bounds are outside this pilot. -/
def interpret (m : Snapshot) : Except String Schema := do
  if !checkSnapshot vocabulary m then throw "invalid metadata snapshot"
  let classes ← (m.objects.filter fun o => o.classifier == classKind).mapM fun o => do
    pure ({
      id := ⟨o.id.val⟩
      name := some (← text m o.id className)
      package := none
      isAbstract := false
      directSupers := [] } : ClassDecl)
  let properties ← (m.objects.filter fun o => o.classifier == attributeKind).mapM fun o => do
    pure ({
      id := ⟨o.id.val⟩
      name := some (← text m o.id attributeName)
      owner := .class (← owner m o.id)
      type := ← scalarType m o.id
      multiplicity := {
        lower := ← natural m o.id lowerBound
        upper := .finite (← natural m o.id upperBound)
        isOrdered := ← boolean m o.id ordered
        isUnique := ← boolean m o.id unique }
      aggregation := .none
      isId := false } : PropertyDecl)
  pure { packages := [], classes, properties, associations := [], enumerations := [], literals := [] }

/-- The vocabulary alone does not enforce interpreted bounds or nonempty names.
Those external semantic obligations are checked by the ordinary schema checker. -/
def interpretChecked (m : Snapshot) : Except String Schema := do
  let s ← interpret m
  if checkSchema s then pure s else throw "invalid interpreted schema"

/-- Reading metadata text requires exactly one String occurrence; nothing is
inferred from the descriptor's identity or from an absent/default observation. -/
theorem text_ok_iff (m : Snapshot) (o : ObjectId) (p : PropertyId) (value : String) :
    text m o p = .ok value ↔ m.occurrences o p = [.string value] := by
  unfold text
  split <;> simp_all

/-- Every interpreted input passes ordinary metadata conformance. -/
theorem interpret_input_conforms {m : Snapshot} {s : Schema}
    (h : interpret m = .ok s) : SnapshotConforms vocabulary m := by
  apply (checkSnapshot_iff _ _).mp
  cases hc : checkSnapshot vocabulary m with
  | true => rfl
  | false => simp [interpret, hc, Bind.bind, Except.bind] at h

/-- The external semantic check is the same schema checker used elsewhere. -/
theorem interpretChecked_wellFormed {m : Snapshot} {s : Schema}
    (h : interpretChecked m = .ok s) : SchemaWellFormed s := by
  cases hi : interpret m with
  | error message => simp [interpretChecked, hi, Bind.bind, Except.bind] at h
  | ok decoded =>
    cases hc : checkSchema decoded with
    | false => simp [interpretChecked, hi, hc, Bind.bind, Except.bind] at h
    | true =>
      have he : decoded = s := by simpa [interpretChecked, hi, hc, Bind.bind, Except.bind, pure, Except.pure] using h
      subst decoded
      exact (checkSchema_iff _).mp hc
end VLMOF.MetadataPilot

