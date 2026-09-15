import VLMOF.Source.Syntax
import VLMOF.Model.Semantics

/-!
# Declarative source semantics

This module gives the symbolic source document its own meaning.  Qualified aliases
are the identities used here: no source predicate invokes elaboration, and no target
schema or snapshot conformance predicate appears in a definition below.  The finite
lists remain raw syntax, so the predicates deliberately reject duplicate aliases,
dangling names, and repeated observation keys instead of normalising them away.

The two reachability relations are inductive finite-path relations over aliases.
Their declarative meaning does not depend on the numeric closure bound used by the
elaborated representation; the bridge to that bounded computation belongs at the
binding boundary.

The development proceeds from lexical and resolution predicates, through
inheritance and property applicability, to values and containment.  The two final
structures then collect those local predicates into model and whole-document
contracts.  This order is also the intended reading order for the preservation
proofs under `Source.Correctness`.
-/

namespace VLMOF.Source

/-- Lexical admissibility of a qualified alias: it has at least one component and
every component is nonempty and valid under the Core string discipline. -/
def NameValid (n : Name) : Prop :=
  n ≠ [] ∧ ∀ component ∈ n, component ≠ "" ∧ VLMOF.validString component

/-- The source domain uses the binder's exact lexical rule: a declaration is one
component below its owner.  This is `checkQualification` stated as a proposition. -/
def qualifiedBy (parent child : Name) : Prop := child.dropLast = parent

/-- A declaration is root-qualified when removing its local component leaves the
implicit outer source scope. -/
def rootQualified (child : Name) : Prop := child.dropLast = []

/-- Source display metadata uses the same nonempty valid-string condition as
named Core declarations, while remaining independent of alias identity. -/
def validDisplayName (s : String) : Prop := s ≠ "" ∧ VLMOF.validString s

/-- All model declaration aliases in their allocation order.  Global alias
uniqueness is checked across declaration kinds, not merely within each list. -/
def aliases (m : Model) : List Name :=
  m.packages.map Package.alias ++ m.classes.map Class.alias ++
    m.properties.map Property.alias ++ m.associations.map Association.alias ++
    m.enumerations.map Enumeration.alias ++ m.literals.map Literal.alias

/-- No two declarations in the source model share a qualified binding alias. -/
def uniqueAliases (m : Model) : Prop := (aliases m).Nodup

/-- All packages carrying a given alias.  Multiple results expose ambiguity. -/
def packageEntries (m : Model) (n : Name) := lookupAll Package.alias m.packages n
/-- All classes carrying a given alias. -/
def classEntries (m : Model) (n : Name) := lookupAll Class.alias m.classes n
/-- All properties carrying a given alias. -/
def propertyEntries (m : Model) (n : Name) := lookupAll Property.alias m.properties n
/-- All associations carrying a given alias. -/
def associationEntries (m : Model) (n : Name) := lookupAll Association.alias m.associations n
/-- All enumerations carrying a given alias. -/
def enumerationEntries (m : Model) (n : Name) := lookupAll Enumeration.alias m.enumerations n
/-- All literals carrying a given alias. -/
def literalEntries (m : Model) (n : Name) := lookupAll Literal.alias m.literals n

/-- A package alias has at least one declaration candidate. -/
def resolvesPackage (m : Model) (n : Name) : Prop := packageEntries m n ≠ []
/-- A class alias has at least one declaration candidate.  Model well-formedness
later supplies global uniqueness, turning existence into unique resolution. -/
def resolvesClass (m : Model) (n : Name) : Prop := classEntries m n ≠ []
/-- A property alias has at least one declaration candidate. -/
def resolvesProperty (m : Model) (n : Name) : Prop := propertyEntries m n ≠ []
/-- An association alias has at least one declaration candidate. -/
def resolvesAssociation (m : Model) (n : Name) : Prop := associationEntries m n ≠ []
/-- An enumeration alias has at least one declaration candidate. -/
def resolvesEnumeration (m : Model) (n : Name) : Prop := enumerationEntries m n ≠ []
/-- A literal alias has at least one declaration candidate. -/
def resolvesLiteral (m : Model) (n : Name) : Prop := literalEntries m n ≠ []

/-! ## Inheritance and feature applicability -/

/-- Reflexive transitive superclass paths over symbolic class aliases. -/
inductive ClassAncestor (m : Model) : Name → Name → Prop where
  | refl (c) : ClassAncestor m c c
  | step {sub mid sup} : ClassAncestor m sub mid →
      (∃ d ∈ m.classes, d.alias = mid ∧ sup ∈ d.directSupers) →
      ClassAncestor m sub sup

/-- Reflexive transitive parent-package paths over symbolic package aliases. -/
inductive PackageAncestor (m : Model) : Name → Name → Prop where
  | refl (p) : PackageAncestor m p p
  | step {child mid parent} : PackageAncestor m child mid →
      (∃ d ∈ m.packages, d.alias = mid ∧ d.parent = some parent) →
      PackageAncestor m child parent

/-- Source subtyping is symbolic superclass reachability, including reflexivity. -/
def sourceSubtype (m : Model) (sub super : Name) : Prop := ClassAncestor m sub super

/-- A property applies to a class either through class ownership and inheritance,
or as an association end whose opposite reference end accepts the class.  This is
the declarative counterpart of `Schema.applicablePropertyIds`. -/
def propertyApplies (m : Model) (classAlias propertyAlias : Name) : Prop :=
  ∃ p ∈ m.properties, p.alias = propertyAlias ∧
    match p.owner with
    | .class owner => ClassAncestor m classAlias owner
    | .association association =>
      ∃ a ∈ m.associations, a.alias = association ∧ propertyAlias ∈ a.ends ∧
        ∃ other ∈ a.ends, other ≠ propertyAlias ∧
          ∃ q ∈ m.properties, q.alias = other ∧
            match q.type with
            | .reference source => ClassAncestor m classAlias source
            | _ => False

/-! ## Occurrences, values, and containment -/

/-- Concatenate every row for one symbolic object/property key.  The definition
does not assume key uniqueness, so duplicate rows remain semantically visible. -/
def sourceOccurrences (i : Instance) (object property : Name) : List Value :=
  (i.observations.filter fun o => o.object = object ∧ o.property = property).flatMap
    Observation.occurrences

/-- Declarative source value typing.  Reference values permit instances of
subclasses; enumeration values must name a literal owned by the stated enum. -/
def sourceValueMatches (m : Model) (i : Instance) : ValueType → Value → Prop
  | .boolean, .boolean _ => True
  | .integer, .integer _ => True
  | .string, .string s => VLMOF.validString s
  | .enumeration e, .enumeration e' l => e = e' ∧ ∃ d ∈ m.literals, d.alias = l ∧ d.enumeration = e
  | .reference c, .reference o => ∃ d ∈ i.objects, d.alias = o ∧ ClassAncestor m d.classifier c
  | _, _ => False

/-- The key used to require one observation row per applicable object/property
pair while leaving repeated values inside a row untouched. -/
def SourceObservation.key (o : Observation) : Name × Name := (o.object, o.property)

/-- A directed containment edge contributed by a composite property occurrence.
`src` is the observing container and `dst` is the referenced contained object. -/
def sourceCompositeEdge (m : Model) (i : Instance) (src dst : Name) : Prop :=
  ∃ o ∈ i.observations, o.object = src ∧ .reference dst ∈ o.occurrences ∧
    ∃ p ∈ m.properties, p.alias = o.property ∧ p.aggregation = .composite

/-- A declarative containment path.  It is deliberately not a list iteration. -/
inductive SourceCompositeReachable (m : Model) (i : Instance) : Name → Name → Prop where
  | refl (o) : SourceCompositeReachable m i o o
  | step {src mid dst} : SourceCompositeReachable m i src mid →
      sourceCompositeEdge m i mid dst → SourceCompositeReachable m i src dst

/-- Count composite references to `target`, including duplicate occurrences and
rows.  The single-container rule bounds this number by one. -/
def incomingCompositeCount (m : Model) (i : Instance) (target : Name) : Nat :=
  (i.observations.flatMap fun o =>
    if m.properties.any (fun p => p.alias = o.property && p.aggregation = .composite)
    then o.occurrences.filter (· = .reference target) else []).length

/-! ## Local association invariants -/

/-- Class-owned properties may serve as navigable ends; association-owned ends
must name the association in which they occur. -/
def ownerMatches (a : Association) (p : Property) : Prop :=
  match p.owner with | .class _ => True | .association x => x = a.alias

/-- When an end is class-owned, its owner must be the class referenced by the
opposite end.  Association-owned ends impose no class-owner equation. -/
def classOwnerMatchesSource (p q : Property) : Prop :=
  match p.owner, q.type with
  | .class owner, .reference source => owner = source
  | .association _, .reference _ => True
  | _, _ => False

/-- A binary association cannot have both end properties owned by associations;
at least one end is class-owned and therefore provides a navigable anchor. -/
def atMostOneAssociationOwner (p q : Property) : Prop :=
  match p.owner, q.owner with | .association _, .association _ => False | _, _ => True

/-- The declaration-side source contract, before numeric identity allocation.
Its fields separate lexical uniqueness, ownership and resolution, finite graph
constraints, and EMOF association/ID rules so preservation proofs can transport
each obligation independently. -/
structure ModelWellFormed (m : Model) : Prop where
  uniqueQualifiedAliases : uniqueAliases m
  aliasesValid : ∀ n ∈ aliases m, NameValid n
  displayNames :
    (∀ x ∈ m.packages, validDisplayName x.name) ∧
    (∀ x ∈ m.classes, validDisplayName x.name) ∧
    (∀ x ∈ m.properties, validDisplayName x.name) ∧
    (∀ x ∈ m.associations, validDisplayName x.name) ∧
    (∀ x ∈ m.enumerations, validDisplayName x.name) ∧
    (∀ x ∈ m.literals, validDisplayName x.name)
  packageParents : ∀ p ∈ m.packages, match p.parent with
    | none => rootQualified p.alias
    | some parent => resolvesPackage m parent ∧ qualifiedBy parent p.alias
  packageAcyclic : ∀ p ∈ m.packages, ∀ parent, p.parent = some parent → ¬ PackageAncestor m parent p.alias
  classPackages : ∀ c ∈ m.classes, match c.package with
    | none => rootQualified c.alias
    | some package => resolvesPackage m package ∧ qualifiedBy package c.alias
  enumPackages : ∀ e ∈ m.enumerations, match e.package with
    | none => rootQualified e.alias
    | some package => resolvesPackage m package ∧ qualifiedBy package e.alias
  associationPackages : ∀ a ∈ m.associations, match a.package with
    | none => rootQualified a.alias
    | some package => resolvesPackage m package ∧ qualifiedBy package a.alias
  supersResolved : ∀ c ∈ m.classes, ∀ super ∈ c.directSupers, resolvesClass m super
  inheritanceAcyclic : ∀ c ∈ m.classes, ∀ super ∈ c.directSupers, ¬ ClassAncestor m super c.alias
  multiplicities : ∀ p ∈ m.properties, VLMOF.multiplicityValid p.multiplicity
  propertyOwners : ∀ p ∈ m.properties, match p.owner with
    | .class c => resolvesClass m c ∧ qualifiedBy c p.alias
    | .association a => resolvesAssociation m a ∧ qualifiedBy a p.alias
  propertyTypes : ∀ p ∈ m.properties, match p.type with
    | .reference c => resolvesClass m c | .enumeration e => resolvesEnumeration m e | _ => True
  compositesAreReferences : ∀ p ∈ m.properties, p.aggregation = .composite → ∃ c, p.type = .reference c
  literalsResolved : ∀ l ∈ m.literals, resolvesEnumeration m l.enumeration ∧ qualifiedBy l.enumeration l.alias
  associationEnds : ∀ a ∈ m.associations, ∃ p q,
    a.ends = [p.alias, q.alias] ∧ p ∈ m.properties ∧ q ∈ m.properties ∧ p.alias ≠ q.alias ∧
    (∃ source, p.type = .reference source) ∧ (∃ source, q.type = .reference source) ∧
    ownerMatches a p ∧ ownerMatches a q ∧ classOwnerMatchesSource p q ∧
    classOwnerMatchesSource q p ∧ atMostOneAssociationOwner p q ∧
    ¬ (p.aggregation = .composite ∧ q.aggregation = .composite)
  associationOwnedEnds : ∀ p ∈ m.properties, match p.owner with
    | .class _ => True
    | .association a => ∃ d ∈ m.associations, d.alias = a ∧ p.alias ∈ d.ends
  endMembershipUnique : ∀ p ∈ m.properties,
    (m.associations.flatMap fun a => if p.alias ∈ a.ends then [a.alias] else []).length ≤ 1
  containerUpperOne : ∀ a ∈ m.associations, ∀ p q,
    a.ends = [p.alias, q.alias] → p ∈ m.properties → q ∈ m.properties →
      (p.aggregation = .composite → q.multiplicity.upper = .finite 1) ∧
      (q.aggregation = .composite → p.multiplicity.upper = .finite 1)
  /-- At most one inherited ID declaration, counted by declaration alias rather than
  display spelling.  The pairwise form is the declarative finite-set statement. -/
  inheritedIdCount : ∀ c ∈ m.classes, ∀ p ∈ m.properties, ∀ q ∈ m.properties,
    p.isId = true → q.isId = true →
    (∃ owner, p.owner = .class owner ∧ ClassAncestor m c.alias owner) →
    (∃ owner, q.owner = .class owner ∧ ClassAncestor m c.alias owner) →
    p.alias = q.alias

/-- Whole-document source satisfaction.  It extends model well-formedness with
object allocation, complete and unique observation rows, value typing,
multiplicity and uniqueness, opposite-end counts, and containment constraints.
Observation rows are exact source facts; order and duplicate occurrences are
retained rather than canonicalised. -/
structure SourceSatisfies (d : Document) : Prop where
  model : ModelWellFormed d.model
  uniqueObjectAliases : (d.snapshot.objects.map Object.alias).Nodup
  objectAliasesValid : ∀ o ∈ d.snapshot.objects, NameValid o.alias
  classifiersResolved : ∀ o ∈ d.snapshot.objects, resolvesClass d.model o.classifier
  concreteClassifiers : ∀ o ∈ d.snapshot.objects, ∀ c ∈ d.model.classes,
    c.alias = o.classifier → c.isAbstract = false
  uniqueObservationKeys : (d.snapshot.observations.map SourceObservation.key).Nodup
  observationsExact : ∀ o ∈ d.snapshot.objects, ∀ p ∈ d.model.properties,
    (∃ a ∈ d.snapshot.observations, a.object = o.alias ∧ a.property = p.alias) ↔
      propertyApplies d.model o.classifier p.alias
  observationKeysResolved : ∀ a ∈ d.snapshot.observations,
    (∃ o ∈ d.snapshot.objects, o.alias = a.object) ∧ (∃ p ∈ d.model.properties, p.alias = a.property)
  observationApplicable : ∀ a ∈ d.snapshot.observations, ∀ o ∈ d.snapshot.objects,
    o.alias = a.object → propertyApplies d.model o.classifier a.property
  valuesTyped : ∀ a ∈ d.snapshot.observations, ∀ p ∈ d.model.properties,
    p.alias = a.property → ∀ v ∈ a.occurrences, sourceValueMatches d.model d.snapshot p.type v
  bounds : ∀ o ∈ d.snapshot.objects, ∀ p ∈ d.model.properties,
    propertyApplies d.model o.classifier p.alias →
      VLMOF.withinMultiplicity p.multiplicity (sourceOccurrences d.snapshot o.alias p.alias).length
  uniqueness : ∀ o ∈ d.snapshot.objects, ∀ p ∈ d.model.properties,
    propertyApplies d.model o.classifier p.alias → p.multiplicity.isUnique = true →
      (sourceOccurrences d.snapshot o.alias p.alias).Nodup
  oppositeCounts : ∀ a ∈ d.model.associations, ∀ p q,
    a.ends = [p, q] → ∀ x ∈ d.snapshot.objects, ∀ y ∈ d.snapshot.objects,
      (sourceOccurrences d.snapshot x.alias p).count (.reference y.alias) =
      (sourceOccurrences d.snapshot y.alias q).count (.reference x.alias)
  oneIncomingComposite : ∀ o ∈ d.snapshot.objects, incomingCompositeCount d.model d.snapshot o.alias ≤ 1
  containmentAcyclic : ∀ o ∈ d.snapshot.objects, ∀ child,
    sourceCompositeEdge d.model d.snapshot o.alias child →
      ¬ SourceCompositeReachable d.model d.snapshot child o.alias

end VLMOF.Source
