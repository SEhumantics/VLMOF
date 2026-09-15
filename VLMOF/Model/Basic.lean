import VLMOF.Model.Multiplicity

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

Each Schema denotes an implicit outer package scope. A missing explicit package
reference on a class, enumeration or association denotes ownership by that scope,
not an ownerless EMOF declaration. Explicit packages with no parent also sit in
that scope. See `docs/model.md` for the interpretation and its omitted root API.

Reading order: `VLMOF.Model.Multiplicity` defines cardinality intervals; this module
defines raw records; `VLMOF.Model.Semantics` adds well-formedness and conformance;
the `VLMOF.Model.Reachability` modules justify the bounded closure computations.
-/

namespace VLMOF

/-! ## Declaration and object identities -/

/-- Package identity used by declaration ownership and parent links. It remains
stable when optional presentation names change. -/
structure PackageId where val : Nat deriving DecidableEq, Repr
/-- Class identity shared by superclass links, reference types, and object
classifiers, so semantic equality does not depend on names. -/
structure ClassId where val : Nat deriving DecidableEq, Repr
/-- Property identity shared by schema declarations, association membership, and
snapshot observations; association ends use the same common property store. -/
structure PropertyId where val : Nat deriving DecidableEq, Repr
/-- Association identity used both by the association store and by ownership of a
nonnavigable end. -/
structure AssociationId where val : Nat deriving DecidableEq, Repr
/-- Enumeration identity referenced by property types and by each literal's owner. -/
structure EnumerationId where val : Nat deriving DecidableEq, Repr
/-- Literal identity carried in enumeration occurrence values and resolved together
with its enumeration identity. -/
structure LiteralId where val : Nat deriving DecidableEq, Repr
/-- Object identity shared by references and observation sources, independently of
an object's asserted classifier. -/
structure ObjectId where val : Nat deriving DecidableEq, Repr

/-! ## Raw schema declarations -/

/-- The property types supported by the selected structural profile. Enumeration and
reference types retain declaration identities for later resolution checks. -/
inductive ValueType where
  | boolean
  | integer
  | string
  | enumeration (id : EnumerationId)
  | reference (id : ClassId)
  deriving DecidableEq, Repr

/-- The declaration that owns a property. Association ownership represents a
nonnavigable end while keeping it in the common property store. -/
inductive PropertyOwner where
  | class (id : ClassId)
  | association (id : AssociationId)
  deriving DecidableEq, Repr

/-- The supported aggregation modes. `composite` contributes containment edges;
shared aggregation is outside the selected profile. -/
inductive Aggregation where
  | none
  | composite
  deriving DecidableEq, Repr

/-- A raw package declaration. `none` denotes the schema's implicit outer package
scope; explicit parent references are resolved during schema validation. -/
structure PackageDecl where
  id : PackageId
  name : Option String
  parent : Option PackageId
  deriving DecidableEq, Repr

/-- A raw class declaration with direct superclass identities. Cycles and dangling
superclasses remain representable so validation can diagnose them. -/
structure ClassDecl where
  id : ClassId
  name : Option String
  package : Option PackageId
  isAbstract : Bool
  directSupers : List ClassId
  deriving DecidableEq, Repr

/-- A raw structural feature or association end, including its normalized type,
multiplicity, containment mode, and identity-property marker. -/
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

/-- A raw enumeration declaration; its literals are stored separately by identity. -/
structure EnumerationDecl where
  id : EnumerationId
  name : Option String
  package : Option PackageId
  deriving DecidableEq, Repr

/-- A raw enumeration literal linked to its owning enumeration by identity. -/
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

/-! ## Raw snapshot data -/

/-- A runtime occurrence value in the selected primitive, enumeration, and reference
domains. References use object identity and enumeration values retain both IDs. -/
inductive Value where
  | boolean (value : Bool)
  | integer (value : Int)
  | string (value : String)
  | enumeration (enumeration : EnumerationId) (literal : LiteralId)
  | reference (object : ObjectId)
  deriving DecidableEq, Repr

/-- An object identity and its asserted classifier in a raw snapshot. -/
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

/-- A raw finite object graph. Lists preserve duplicate identities and observation
keys until the conformance predicate or checker reports them. -/
structure Snapshot where
  objects : List ObjectDecl
  observations : List Observation
  deriving DecidableEq, Repr

/-! ## Representation-level observations -/

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

end VLMOF
