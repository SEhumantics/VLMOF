import VLMOF.Model.Basic

/-!
# Declarative semantics for the finite structural profile

`SchemaWellFormed` validates declarations independently of any snapshot.
`SnapshotConforms` then states when one raw snapshot belongs to the set denoted by a
well-formed schema.  All closure computations are bounded by the finite declaration
store.  Raw lookup collects every matching row; duplicate keys are rejected explicitly
rather than being silently overwritten by a map.

The profile and source locators are recorded in `sources/PROFILE.md`: MOF 2.5.1
9.3.3, 9.4.1, 10.5--10.6, 12.4 and 12.5, and UML 2.5 9.9.4.
-/

namespace VLMOF

/-! ## Lexical domains and finite-key discipline -/

/-- XML 1.0 character admissibility used by the profile's string and name checks.
The numeric ranges follow XML 1.0 Second Edition, production [2] `Char`, as
identified by the adopted datatype source; see `sources/PROFILE.md`. -/
def xmlChar (c : Char) : Prop :=
  let n := c.toNat
  n = 0x9 ∨ n = 0xA ∨ n = 0xD ∨
    (0x20 ≤ n ∧ n ≤ 0xD7FF) ∨ (0xE000 ≤ n ∧ n ≤ 0xFFFD) ∨
    (0x10000 ≤ n ∧ n ≤ 0x10FFFF)

/-- A runtime string is valid when every character belongs to the XML character
domain required by XMI-facing EMOF data. -/
def validString (s : String) : Prop := ∀ c ∈ s.toList, xmlChar c
/-- Declaration names must be present, nonempty, and composed of valid XML
characters. Lexical identifier grammar is handled by the source layer. -/
def validName : Option String → Prop
  | some s => s ≠ "" ∧ validString s
  | none => False

/-- Key uniqueness for a raw list. This leaves duplicate records representable in
`Schema` and `Snapshot`, then rejects them in the relevant validity predicate. -/
def uniqueBy {κ α : Type} [DecidableEq κ] (key : α → κ) (xs : List α) : Prop :=
  (xs.map key).Nodup

/-- Key uniqueness is decidable whenever key equality is decidable. -/
instance {κ α : Type} [DecidableEq κ] (key : α → κ) (xs : List α) :
    Decidable (uniqueBy key xs) := by
  unfold uniqueBy
  infer_instance

/-! ## Duplicate-preserving lookup -/

/-- Resolve a package identity for parent and ownership checks. A list result keeps
zero, one, and duplicate declarations distinguishable to the validator. -/
def Schema.packageDecls (s : Schema) (id : PackageId) : List PackageDecl :=
  s.packages.filter (fun d => d.id = id)
/-- Resolve a class identity used by classifiers, superclass links, and reference
types while retaining duplicate declarations for diagnostics. -/
def Schema.classDecls (s : Schema) (id : ClassId) : List ClassDecl :=
  s.classes.filter (fun d => d.id = id)
/-- Resolve the common identity of a structural feature or association end; the list
result avoids silently choosing among malformed duplicates. -/
def Schema.propertyDecls (s : Schema) (id : PropertyId) : List PropertyDecl :=
  s.properties.filter (fun d => d.id = id)
/-- Resolve association ownership and membership without collapsing duplicate raw
association declarations. -/
def Schema.associationDecls (s : Schema) (id : AssociationId) : List AssociationDecl :=
  s.associations.filter (fun d => d.id = id)
/-- Resolve an enumeration referenced by a property type or literal owner while
preserving malformed duplicate declarations. -/
def Schema.enumerationDecls (s : Schema) (id : EnumerationId) : List EnumerationDecl :=
  s.enumerations.filter (fun d => d.id = id)
/-- Resolve a literal identity carried by an enumeration occurrence; its owning
enumeration is checked separately by `valueMatches`. -/
def Schema.literalDecls (s : Schema) (id : LiteralId) : List LiteralDecl :=
  s.literals.filter (fun d => d.id = id)

/-- Resolve reference targets and observation sources without trusting raw object
identity uniqueness before snapshot conformance is established. -/
def Snapshot.objectDecls (m : Snapshot) (id : ObjectId) : List ObjectDecl :=
  m.objects.filter (fun d => d.id = id)

/-- Concatenating all matching rows makes duplicate observation keys visible.  Under
`SnapshotConforms.uniqueObservationKeys` there is exactly one contributing row. -/
def Snapshot.occurrences (m : Snapshot) (o : ObjectId) (p : PropertyId) : List Value :=
  (m.observations.filter (fun a => a.object = o ∧ a.property = p)).flatMap
    Observation.occurrences

/-! ## Bounded declaration reachability -/

/-- One superclass expansion from every stored class whose identity is in `ids`.
The result retains repeated edges for the closure layer to deduplicate. -/
def classSupers (s : Schema) (ids : List ClassId) : List ClassId :=
  (s.classes.filter (fun c => ids.contains c.id)).flatMap ClassDecl.directSupers

/-- One parent-package expansion from the declarations selected by `ids`. Root
packages contribute no successor. -/
def packageParents (s : Schema) (ids : List PackageId) : List PackageId :=
  (s.packages.filter (fun p => ids.contains p.id)).filterMap PackageDecl.parent

/-- Bounded monotone closure from an initial `seen` list. Each round appends newly
exposed identities once; callers choose a store-size fuel bound. -/
def iterateClosure {α : Type} [DecidableEq α]
    (step : List α → List α) : Nat → List α → List α
  | 0, seen => seen
  | n + 1, seen =>
      iterateClosure step n (seen ++ (step seen).eraseDups.filter (fun x => !seen.contains x))

/-- Identity-deduplicated reflexive ancestor closure, bounded by the class store. -/
def Schema.ancestors (s : Schema) (c : ClassId) : List ClassId :=
  (iterateClosure (classSupers s) s.classes.length [c]).eraseDups

/-- Reflexive package-ancestor closure, bounded by the number of package records. -/
def Schema.packageAncestors (s : Schema) (p : PackageId) : List PackageId :=
  (iterateClosure (packageParents s) s.packages.length [p]).eraseDups

/-- Computational subtyping: `super` occurs in the reflexive ancestor closure of
`sub`. Reachability modules relate this bounded computation to stored paths. -/
def Schema.isSubtype (s : Schema) (sub super : ClassId) : Prop :=
  super ∈ s.ancestors sub

/-- Subtyping is decidable because the computed ancestor list is finite. -/
instance (s : Schema) (sub super : ClassId) : Decidable (s.isSubtype sub super) := by
  unfold Schema.isSubtype
  infer_instance

/-- Identities of properties directly owned by class `c`, without inheritance. -/
def Schema.directProperties (s : Schema) (c : ClassId) : List PropertyId :=
  (s.properties.filter (fun p => p.owner = .class c)).map PropertyDecl.id

/-! ## Property applicability and local semantic checks -/

/-- Whether an association-owned end applies to class `c`. Applicability is inferred
from the opposite end's reference source because the end itself is nonnavigable. -/
def Schema.associationEndApplies (s : Schema) (c : ClassId)
    (aid : AssociationId) (pid : PropertyId) : Bool :=
  s.associations.any fun a =>
    a.id = aid &&
      if a.ends.1 = pid then
        s.properties.any fun q => q.id = a.ends.2 && match q.type with
          | .reference source => (s.ancestors c).contains source | _ => false
      else if a.ends.2 = pid then
        s.properties.any fun p => p.id = a.ends.1 && match p.type with
          | .reference source => (s.ancestors c).contains source | _ => false
      else false

/-- Applicable declarations, computed by identity.  A class-owned declaration is
inherited once through a diamond.  An association-owned end applies to instances of
the class selected by the other end's reference type. -/
def Schema.applicablePropertyIds (s : Schema) (c : ClassId) : List PropertyId :=
  (s.properties.filter fun p => match p.owner with
    | .class owner => (s.ancestors c).contains owner
    | .association aid => s.associationEndApplies c aid p.id).map PropertyDecl.id |>.eraseDups

/-- Proposition-level membership in the identity-deduplicated applicable-property
list for class `c`. -/
def Schema.applicableProperty (s : Schema) (c : ClassId) (pid : PropertyId) : Prop :=
  pid ∈ s.applicablePropertyIds c

/-- Property applicability is decidable by list membership. -/
instance (s : Schema) (c : ClassId) (pid : PropertyId) :
    Decidable (s.applicableProperty c pid) := by
  unfold Schema.applicableProperty
  infer_instance

/-- Semantic typing of one occurrence. Reference values must resolve to objects whose
classifier is a subtype; enumeration values must resolve to a literal of that enum. -/
def valueMatches (s : Schema) (m : Snapshot) : ValueType → Value → Prop
  | .boolean, .boolean _ => True
  | .integer, .integer _ => True
  | .string, .string x => validString x
  | .enumeration e, .enumeration e' l =>
      e = e' ∧ ∃ ld ∈ s.literals, ld.id = l ∧ ld.enumeration = e
  | .reference c, .reference o =>
      ∃ od ∈ m.objects, od.id = o ∧ s.isSubtype od.classifier c
  | _, _ => False

/-- An association end may be class-owned, or association-owned by this association.
The latter condition prevents a nonnavigable end from naming another association. -/
def ownerMatchesEnd (a : AssociationDecl) (p : PropertyDecl) : Prop :=
  match p.owner with | .class _ => True | .association aid => aid = a.id

/-- A class-owned association end's owner must equal the reference source inferred
from its opposite end. Association-owned ends have no navigable class owner. -/
def classOwnerIsSource (p opposite : PropertyDecl) : Prop :=
  match p.owner, opposite.type with
  | .class source, .reference targetSource => source = targetSource
  | .association _, .reference _ => True
  | _, _ => False

/-- The selected binary-association representation permits at most one nonnavigable,
association-owned end. -/
def atMostOneAssociationOwned (p q : PropertyDecl) : Prop :=
  match p.owner, q.owner with
  | .association _, .association _ => False
  | _, _ => True

/-! ## Schema well-formedness -/

/-- The schema-only obligations.  Every navigation used by snapshot semantics is
resolved here, including names, ownership, types, binary ends and inheritance. -/
structure SchemaWellFormed (s : Schema) : Prop where
  uniquePackageIds : uniqueBy PackageDecl.id s.packages
  uniqueClassIds : uniqueBy ClassDecl.id s.classes
  uniquePropertyIds : uniqueBy PropertyDecl.id s.properties
  uniqueAssociationIds : uniqueBy AssociationDecl.id s.associations
  uniqueEnumerationIds : uniqueBy EnumerationDecl.id s.enumerations
  uniqueLiteralIds : uniqueBy LiteralDecl.id s.literals
  names :
    (∀ x ∈ s.packages, validName x.name) ∧
    (∀ x ∈ s.classes, validName x.name) ∧
    (∀ x ∈ s.properties, validName x.name) ∧
    (∀ x ∈ s.associations, validName x.name) ∧
    (∀ x ∈ s.enumerations, validName x.name) ∧
    (∀ x ∈ s.literals, validName x.name)
  packageParentsResolved : ∀ d ∈ s.packages, ∀ p, d.parent = some p → s.packageDecls p ≠ []
  packageAcyclic : ∀ d ∈ s.packages, ∀ p, d.parent = some p → d.id ∉ s.packageAncestors p
  classPackagesResolved : ∀ d ∈ s.classes, ∀ p, d.package = some p → s.packageDecls p ≠ []
  enumPackagesResolved : ∀ d ∈ s.enumerations, ∀ p, d.package = some p → s.packageDecls p ≠ []
  associationPackagesResolved : ∀ d ∈ s.associations, ∀ p, d.package = some p → s.packageDecls p ≠ []
  supersResolved : ∀ d ∈ s.classes, ∀ p ∈ d.directSupers, s.classDecls p ≠ []
  inheritanceAcyclic : ∀ d ∈ s.classes, ∀ p ∈ d.directSupers, d.id ∉ s.ancestors p
  multiplicities : ∀ p ∈ s.properties, multiplicityValid p.multiplicity
  propertyOwnersResolved : ∀ p ∈ s.properties,
    match p.owner with
    | .class c => s.classDecls c ≠ []
    | .association aid => ∃ a ∈ s.associations, a.id = aid ∧ (a.ends.1 = p.id ∨ a.ends.2 = p.id)
  propertyTypesResolved : ∀ p ∈ s.properties,
    match p.type with
    | .reference c => s.classDecls c ≠ []
    | .enumeration e => s.enumerationDecls e ≠ []
    | _ => True
  compositeReferences : ∀ p ∈ s.properties, p.aggregation = .composite → ∃ c, p.type = .reference c
  literalsResolved : ∀ l ∈ s.literals, s.enumerationDecls l.enumeration ≠ []
  associationEnds : ∀ a ∈ s.associations, ∃ p q,
    a.ends = (p.id, q.id) ∧ p ∈ s.properties ∧ q ∈ s.properties ∧ p.id ≠ q.id ∧
    (∃ pc, p.type = .reference pc) ∧ (∃ qc, q.type = .reference qc) ∧
    ownerMatchesEnd a p ∧ ownerMatchesEnd a q ∧ classOwnerIsSource p q ∧
    classOwnerIsSource q p ∧ atMostOneAssociationOwned p q ∧
    ¬(p.aggregation = .composite ∧ q.aggregation = .composite)
  endMembershipUnique : ∀ p ∈ s.properties, (s.oppositeCandidates p.id).length ≤ 1
  containerUpperOne : ∀ a ∈ s.associations, ∀ p q,
    a.ends = (p.id, q.id) → p ∈ s.properties → q ∈ s.properties →
    (p.aggregation = .composite → q.multiplicity.upper = .finite 1) ∧
    (q.aggregation = .composite → p.multiplicity.upper = .finite 1)
  inheritedIdCount : ∀ c ∈ s.classes,
    (s.properties.filter (fun p => p.isId && match p.owner with
      | .class owner => (s.ancestors c.id).contains owner
      | .association _ => false)).length ≤ 1

/-- The bound prerequisites for creating an instance of `c`, including properties
inherited from its superclasses (MOF 2.5.1, 9.3.3). Requiring the class to exist
avoids treating an unresolved classifier as creation-ready. This predicate covers
bounds only: it neither executes creation nor supplies all its other premises.
Association-owned incidence ends are not class-owned reflective properties. -/
def Schema.classCreationBounds (s : Schema) (c : ClassId) : Prop :=
  s.classDecls c ≠ [] ∧ ∀ p ∈ s.properties, ∀ owner,
    p.owner = .class owner → s.isSubtype c owner → p.multiplicity.creationBounds

/-! ## Snapshot graph and conformance -/

/-- The logical slot key used to reject duplicate observation rows. -/
def Observation.key (o : Observation) : ObjectId × PropertyId := (o.object, o.property)

/-- A stored occurrence from `src` to `dst` through a composite property. This raw
edge predicate does not itself require resolved objects or typed observations. -/
def compositeEdge (s : Schema) (m : Snapshot) (src dst : ObjectId) : Prop :=
  ∃ obs ∈ m.observations, obs.object = src ∧
    ∃ p ∈ s.properties, p.id = obs.property ∧ p.aggregation = .composite ∧
      .reference dst ∈ obs.occurrences

/-- One executable containment expansion from objects in `ids`, retaining reference
occurrences reached through composite properties. -/
def outgoingComposite (s : Schema) (m : Snapshot) (ids : List ObjectId) : List ObjectId :=
  (m.observations.filter (fun o => ids.contains o.object)).flatMap fun o =>
    if s.properties.any (fun p => p.id = o.property ∧ p.aggregation = .composite)
    then o.occurrences.filterMap (fun v => match v with | .reference x => some x | _ => none)
    else []

/-- Bounded reflexive-transitive containment reachability over the snapshot's object
store. The containment reachability module proves its stored-path interpretation. -/
def compositeReachable (s : Schema) (m : Snapshot) (src dst : ObjectId) : Prop :=
  dst ∈ iterateClosure (outgoingComposite s m) m.objects.length [src]

/-- Number of raw composite reference occurrences that target one object. Occurrence
counting, rather than distinct-source counting, supports the single-container rule. -/
def incomingCompositeCount (s : Schema) (m : Snapshot) (target : ObjectId) : Nat :=
  (m.observations.flatMap fun o =>
    if s.properties.any (fun p => p.id = o.property ∧ p.aggregation = .composite)
    then o.occurrences.filter (· = .reference target) else []).length

/-- Static snapshot conformance.  Multiplicity counts raw occurrences, uniqueness uses
`Value` equality (object identity for references), and opposite matching compares the
count of each ordered object pair in both directions. -/
structure SnapshotConforms (s : Schema) (m : Snapshot) : Prop where
  schema : SchemaWellFormed s
  uniqueObjectIds : uniqueBy ObjectDecl.id m.objects
  uniqueObservationKeys : uniqueBy Observation.key m.observations
  classifiersResolved : ∀ o ∈ m.objects, s.classDecls o.classifier ≠ []
  concreteClassifiers : ∀ o ∈ m.objects, ∀ c ∈ s.classes,
    c.id = o.classifier → c.isAbstract = false
  observationsExact : ∀ o ∈ m.objects, ∀ p ∈ s.properties,
    (∃ a ∈ m.observations, a.object = o.id ∧ a.property = p.id) ↔
      s.applicableProperty o.classifier p.id
  observationKeysResolved : ∀ a ∈ m.observations,
    (∃ o ∈ m.objects, o.id = a.object) ∧
    (∃ p ∈ s.properties, p.id = a.property)
  observationApplicable : ∀ a ∈ m.observations, ∀ o ∈ m.objects,
    o.id = a.object → s.applicableProperty o.classifier a.property
  valuesTyped : ∀ a ∈ m.observations, ∀ p ∈ s.properties,
    p.id = a.property → ∀ v ∈ a.occurrences, valueMatches s m p.type v
  bounds : ∀ o ∈ m.objects, ∀ p ∈ s.properties,
    s.applicableProperty o.classifier p.id →
      withinMultiplicity p.multiplicity (m.occurrences o.id p.id).length
  uniqueness : ∀ o ∈ m.objects, ∀ p ∈ s.properties,
    s.applicableProperty o.classifier p.id → p.multiplicity.isUnique = true →
      (m.occurrences o.id p.id).Nodup
  oppositeCounts : ∀ a ∈ s.associations, ∀ p q,
    a.ends = (p, q) → ∀ x ∈ m.objects, ∀ y ∈ m.objects,
      (m.occurrences x.id p).count (.reference y.id) =
      (m.occurrences y.id q).count (.reference x.id)
  oneIncomingComposite : ∀ o ∈ m.objects, incomingCompositeCount s m o.id ≤ 1
  containmentAcyclic : ∀ o ∈ m.objects, ∀ child,
    compositeEdge s m o.id child → ¬ compositeReachable s m child o.id

/-- Compatibility spelling for `SchemaWellFormed`. -/
abbrev WellFormedSchema := SchemaWellFormed
/-- Compatibility spelling for `SnapshotConforms`. -/
abbrev Conforms := SnapshotConforms

end VLMOF
