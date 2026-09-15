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

def xmlChar (c : Char) : Prop :=
  let n := c.toNat
  n = 0x9 ∨ n = 0xA ∨ n = 0xD ∨
    (0x20 ≤ n ∧ n ≤ 0xD7FF) ∨ (0xE000 ≤ n ∧ n ≤ 0xFFFD) ∨
    (0x10000 ≤ n ∧ n ≤ 0x10FFFF)

def validString (s : String) : Prop := ∀ c ∈ s.toList, xmlChar c
def validName : Option String → Prop
  | some s => s ≠ "" ∧ validString s
  | none => False

def uniqueBy {κ α : Type} [DecidableEq κ] (key : α → κ) (xs : List α) : Prop :=
  (xs.map key).Nodup

instance {κ α : Type} [DecidableEq κ] (key : α → κ) (xs : List α) :
    Decidable (uniqueBy key xs) := by
  unfold uniqueBy
  infer_instance

def Schema.packageDecls (s : Schema) (id : PackageId) : List PackageDecl :=
  s.packages.filter (fun d => d.id = id)
def Schema.classDecls (s : Schema) (id : ClassId) : List ClassDecl :=
  s.classes.filter (fun d => d.id = id)
def Schema.propertyDecls (s : Schema) (id : PropertyId) : List PropertyDecl :=
  s.properties.filter (fun d => d.id = id)
def Schema.associationDecls (s : Schema) (id : AssociationId) : List AssociationDecl :=
  s.associations.filter (fun d => d.id = id)
def Schema.enumerationDecls (s : Schema) (id : EnumerationId) : List EnumerationDecl :=
  s.enumerations.filter (fun d => d.id = id)
def Schema.literalDecls (s : Schema) (id : LiteralId) : List LiteralDecl :=
  s.literals.filter (fun d => d.id = id)

def Snapshot.objectDecls (m : Snapshot) (id : ObjectId) : List ObjectDecl :=
  m.objects.filter (fun d => d.id = id)

/-- Concatenating all matching rows makes duplicate observation keys visible.  Under
`SnapshotConforms.uniqueObservationKeys` there is exactly one contributing row. -/
def Snapshot.occurrences (m : Snapshot) (o : ObjectId) (p : PropertyId) : List Value :=
  (m.observations.filter (fun a => a.object = o ∧ a.property = p)).flatMap
    Observation.occurrences

def classSupers (s : Schema) (ids : List ClassId) : List ClassId :=
  (s.classes.filter (fun c => ids.contains c.id)).flatMap ClassDecl.directSupers

def packageParents (s : Schema) (ids : List PackageId) : List PackageId :=
  (s.packages.filter (fun p => ids.contains p.id)).filterMap PackageDecl.parent

def iterateClosure {α : Type} [DecidableEq α]
    (step : List α → List α) : Nat → List α → List α
  | 0, seen => seen
  | n + 1, seen =>
      iterateClosure step n (seen ++ (step seen).eraseDups.filter (fun x => !seen.contains x))

/-- Identity-deduplicated reflexive ancestor closure, bounded by the class store. -/
def Schema.ancestors (s : Schema) (c : ClassId) : List ClassId :=
  (iterateClosure (classSupers s) s.classes.length [c]).eraseDups

def Schema.packageAncestors (s : Schema) (p : PackageId) : List PackageId :=
  (iterateClosure (packageParents s) s.packages.length [p]).eraseDups

def Schema.isSubtype (s : Schema) (sub super : ClassId) : Prop :=
  super ∈ s.ancestors sub

instance (s : Schema) (sub super : ClassId) : Decidable (s.isSubtype sub super) := by
  unfold Schema.isSubtype
  infer_instance

def Schema.directProperties (s : Schema) (c : ClassId) : List PropertyId :=
  (s.properties.filter (fun p => p.owner = .class c)).map PropertyDecl.id

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

def Schema.applicableProperty (s : Schema) (c : ClassId) (pid : PropertyId) : Prop :=
  pid ∈ s.applicablePropertyIds c

instance (s : Schema) (c : ClassId) (pid : PropertyId) :
    Decidable (s.applicableProperty c pid) := by
  unfold Schema.applicableProperty
  infer_instance

def multiplicityValid (m : Multiplicity) : Prop :=
  match m.upper with
  | .finite u => 0 < u ∧ m.lower ≤ u
  | .unlimited => True

def withinMultiplicity (m : Multiplicity) (n : Nat) : Prop :=
  m.lower ≤ n ∧ match m.upper with | .finite u => n ≤ u | .unlimited => True

def valueMatches (s : Schema) (m : Snapshot) : ValueType → Value → Prop
  | .boolean, .boolean _ => True
  | .integer, .integer _ => True
  | .string, .string x => validString x
  | .enumeration e, .enumeration e' l =>
      e = e' ∧ ∃ ld ∈ s.literals, ld.id = l ∧ ld.enumeration = e
  | .reference c, .reference o =>
      ∃ od ∈ m.objects, od.id = o ∧ s.isSubtype od.classifier c
  | _, _ => False

def ownerMatchesEnd (a : AssociationDecl) (p : PropertyDecl) : Prop :=
  match p.owner with | .class _ => True | .association aid => aid = a.id

def classOwnerIsSource (p opposite : PropertyDecl) : Prop :=
  match p.owner, opposite.type with
  | .class source, .reference targetSource => source = targetSource
  | .association _, .reference _ => True
  | _, _ => False

def atMostOneAssociationOwned (p q : PropertyDecl) : Prop :=
  match p.owner, q.owner with
  | .association _, .association _ => False
  | _, _ => True

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

def Observation.key (o : Observation) : ObjectId × PropertyId := (o.object, o.property)

def compositeEdge (s : Schema) (m : Snapshot) (src dst : ObjectId) : Prop :=
  ∃ obs ∈ m.observations, obs.object = src ∧
    ∃ p ∈ s.properties, p.id = obs.property ∧ p.aggregation = .composite ∧
      .reference dst ∈ obs.occurrences

def outgoingComposite (s : Schema) (m : Snapshot) (ids : List ObjectId) : List ObjectId :=
  (m.observations.filter (fun o => ids.contains o.object)).flatMap fun o =>
    if s.properties.any (fun p => p.id = o.property ∧ p.aggregation = .composite)
    then o.occurrences.filterMap (fun v => match v with | .reference x => some x | _ => none)
    else []

def compositeReachable (s : Schema) (m : Snapshot) (src dst : ObjectId) : Prop :=
  dst ∈ iterateClosure (outgoingComposite s m) m.objects.length [src]

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

abbrev WellFormedSchema := SchemaWellFormed
abbrev Conforms := SnapshotConforms

end VLMOF
