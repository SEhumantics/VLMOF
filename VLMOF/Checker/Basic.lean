import VLMOF.Model.Semantics
import VLMOF.Finite.FastClosure

/-!
# Executable schema and snapshot checks

The functions in this module mirror fields of `SchemaWellFormed` and
`SnapshotConforms` with finite Boolean computations. Field labels are stable diagnostic
categories, while the correctness modules prove the Boolean checks equivalent to the
declarative predicates. The modeled constraints come from the selected EMOF profile
listed in `sources/PROFILE.md`; this checker does not extend that profile.
-/

namespace VLMOF

/-! ## Decidable semantic predicates -/

/-- Decidability bridge for XML character validity used by `decide` in the checker. -/
instance (c : Char) : Decidable (xmlChar c) := by unfold xmlChar; infer_instance
/-- Decidability bridge for finite string validity. -/
instance (x : String) : Decidable (validString x) := by unfold validString; infer_instance
/-- Decidability bridge for optional declaration-name validity. -/
instance (x : Option String) : Decidable (validName x) := by unfold validName; split <;> infer_instance
/-- Decidability bridge for the selected-profile multiplicity restriction. -/
instance (x : Multiplicity) : Decidable (multiplicityValid x) := by unfold multiplicityValid; split <;> infer_instance
/-- Decidability bridge for interval membership of an occurrence count. -/
instance (x : Multiplicity) (n : Nat) : Decidable (withinMultiplicity x n) := by
  unfold withinMultiplicity Upper.allows
  split <;> infer_instance
/-- Decidability bridge for association-end ownership agreement. -/
instance (a : AssociationDecl) (p : PropertyDecl) : Decidable (ownerMatchesEnd a p) := by unfold ownerMatchesEnd; split <;> infer_instance
/-- Decidability bridge for a navigable end's source-class agreement. -/
instance (p q : PropertyDecl) : Decidable (classOwnerIsSource p q) := by unfold classOwnerIsSource; split <;> infer_instance
/-- Decidability bridge for the one-nonnavigable-end profile restriction. -/
instance (p q : PropertyDecl) : Decidable (atMostOneAssociationOwned p q) := by unfold atMostOneAssociationOwned; split <;> infer_instance

/-- A failed named checker field, classified by whether it belongs to schema
well-formedness or snapshot conformance. -/
inductive Diagnostic where
  | schema (field : String)
  | snapshot (field : String)
  deriving DecidableEq, Repr

/-! ## Schema checks -/

/-- Boolean recognition of class-reference property types for association and
composite constraints. -/
def refType : ValueType → Bool | .reference _ => true | _ => false

/-- Check one candidate pair against all structural obligations for the two ends of
association `a`, including distinctness, reference typing, ownership, and aggregation. -/
def associationPairOK (a : AssociationDecl) (p q : PropertyDecl) : Bool :=
  decide (a.ends = (p.id, q.id)) && decide (p.id ≠ q.id) && refType p.type && refType q.type &&
  decide (ownerMatchesEnd a p) && decide (ownerMatchesEnd a q) &&
  decide (classOwnerIsSource p q) && decide (classOwnerIsSource q p) &&
  decide (atMostOneAssociationOwned p q) &&
  decide (¬ (p.aggregation = .composite ∧ q.aggregation = .composite))

/-- Named Boolean checks corresponding one-for-one to the fields of
`SchemaWellFormed`. Keeping the list centralizes both acceptance and diagnostics. -/
def schemaFieldChecks (s : Schema) : List (String × Bool) :=
  [("unique package identifiers", decide (uniqueBy PackageDecl.id s.packages)),
   ("unique class identifiers", decide (uniqueBy ClassDecl.id s.classes)),
   ("unique property identifiers", decide (uniqueBy PropertyDecl.id s.properties)),
   ("unique association identifiers", decide (uniqueBy AssociationDecl.id s.associations)),
   ("unique enumeration identifiers", decide (uniqueBy EnumerationDecl.id s.enumerations)),
   ("unique literal identifiers", decide (uniqueBy LiteralDecl.id s.literals)),
   ("declaration names", s.packages.all (fun x => decide (validName x.name)) &&
      s.classes.all (fun x => decide (validName x.name)) && s.properties.all (fun x => decide (validName x.name)) &&
      s.associations.all (fun x => decide (validName x.name)) && s.enumerations.all (fun x => decide (validName x.name)) &&
      s.literals.all (fun x => decide (validName x.name))),
   ("package parents resolved", s.packages.all fun d => match d.parent with | none => true | some p => decide (s.packageDecls p ≠ [])),
   ("package hierarchy acyclic", s.packages.all fun d => match d.parent with | none => true | some p => decide (d.id ∉ s.packageAncestors p)),
   ("class packages resolved", s.classes.all fun d => match d.package with | none => true | some p => decide (s.packageDecls p ≠ [])),
   ("enumeration packages resolved", s.enumerations.all fun d => match d.package with | none => true | some p => decide (s.packageDecls p ≠ [])),
   ("association packages resolved", s.associations.all fun d => match d.package with | none => true | some p => decide (s.packageDecls p ≠ [])),
   ("superclasses resolved", s.classes.all fun d => d.directSupers.all fun p => decide (s.classDecls p ≠ [])),
   ("inheritance acyclic", s.classes.all fun d => d.directSupers.all fun p => decide (d.id ∉ s.ancestors p)),
   ("multiplicities valid", s.properties.all fun p => decide (multiplicityValid p.multiplicity)),
   ("property owners resolved", s.properties.all fun p => match p.owner with
      | .class c => decide (s.classDecls c ≠ [])
      | .association aid => s.associations.any fun a => decide (a.id = aid) && (decide (a.ends.1 = p.id) || decide (a.ends.2 = p.id))),
   ("property types resolved", s.properties.all fun p => match p.type with
      | .reference c => decide (s.classDecls c ≠ []) | .enumeration e => decide (s.enumerationDecls e ≠ []) | _ => true),
   ("composites reference classes", s.properties.all fun p => decide (p.aggregation ≠ .composite) || refType p.type),
   ("literals resolved", s.literals.all fun l => decide (s.enumerationDecls l.enumeration ≠ [])),
   ("association ends valid", s.associations.all fun a => s.properties.any fun p => s.properties.any fun q => associationPairOK a p q),
   ("unique end membership", s.properties.all fun p => decide ((s.oppositeCandidates p.id).length ≤ 1)),
   ("container upper bound", s.associations.all fun a => s.properties.all fun p => s.properties.all fun q =>
      decide (a.ends ≠ (p.id, q.id)) ||
        ((decide (p.aggregation ≠ .composite) || decide (q.multiplicity.upper = .finite 1)) &&
         (decide (q.aggregation ≠ .composite) || decide (p.multiplicity.upper = .finite 1)))),
   ("at most one inherited ID", s.classes.all fun c => decide
      ((s.properties.filter (fun p => p.isId && match p.owner with
        | .class owner => (s.ancestors c.id).contains owner | .association _ => false)).length ≤ 1))]

/-- Accept a schema exactly when every named schema field check succeeds. -/
def checkSchema (s : Schema) : Bool := (schemaFieldChecks s).all (fun x => x.2)
/-- Report one schema diagnostic for each failed named field check, in check order. -/
def schemaDiagnostics (s : Schema) : List Diagnostic :=
  (schemaFieldChecks s).filterMap fun x => if x.2 then none else some (.schema x.1)

/-! ## Snapshot-local executable relations -/

/-- All object identities mentioned by reference occurrences, retaining repetition.
This exposes the raw reference workload for finite checker reasoning. -/
def referenceTargets (m : Snapshot) : List ObjectId :=
  m.observations.flatMap fun a => a.occurrences.filterMap fun
    | .reference o => some o | _ => none

/-- Executable recognition of a raw `compositeEdge` between two object identities. -/
def compositeEdgeB (s : Schema) (m : Snapshot) (src dst : ObjectId) : Bool :=
  m.observations.any fun a => decide (a.object = src) && s.properties.any fun p =>
    decide (p.id = a.property) && decide (p.aggregation = .composite) &&
      a.occurrences.contains (.reference dst)

/-- Executable bounded containment reachability, using early stopping without changing
the semantic `iterateClosure` result. -/
def compositeReachableB (s : Schema) (m : Snapshot) (src dst : ObjectId) : Bool :=
  (iterateClosureFast (outgoingComposite s m) m.objects.length [src]).contains dst

/-- Boolean counterpart of `valueMatches`, including literal resolution and subtype
checking for the two identity-bearing value forms. -/
def valueMatchesB (s : Schema) (m : Snapshot) : ValueType → Value → Bool
  | .boolean, .boolean _ => true
  | .integer, .integer _ => true
  | .string, .string x => decide (validString x)
  | .enumeration e, .enumeration e' l => decide (e = e') &&
      s.literals.any (fun d => decide (d.id = l) && decide (d.enumeration = e))
  | .reference c, .reference o => m.objects.any (fun d =>
      decide (d.id = o) && decide (s.isSubtype d.classifier c))
  | _, _ => false

/-- Cache each object's two occurrence lists once per association, before the
pairwise comparison. Duplicate rows and repeated values remain in the cached lists. -/
def oppositeCountsForB (m : Snapshot) (p q : PropertyId) : Bool :=
  let forward := m.objects.map fun x => (x.id, m.occurrences x.id p)
  let backward := m.objects.map fun y => (y.id, m.occurrences y.id q)
  forward.all fun x => backward.all fun y =>
    decide (x.2.count (.reference y.1) = y.2.count (.reference x.1))

/-- Check that no direct composite child of `source` can reach `source`, the local
Boolean form used for global containment acyclicity. -/
def containmentForB (s : Schema) (m : Snapshot) (source : ObjectId) : Bool :=
  (outgoingComposite s m [source]).all fun child => !compositeReachableB s m child source

/-! ## Snapshot checks -/

/-- Named Boolean checks corresponding one-for-one to the fields of
`SnapshotConforms`, including schema validity as the first field. -/
def snapshotFieldChecks (s : Schema) (m : Snapshot) : List (String × Bool) :=
  [("schema well formed", checkSchema s),
   ("unique object identifiers", decide (uniqueBy ObjectDecl.id m.objects)),
   ("unique observation keys", decide (uniqueBy Observation.key m.observations)),
   ("classifiers resolved", m.objects.all fun o => decide (s.classDecls o.classifier ≠ [])),
   ("classifiers concrete", m.objects.all fun o => s.classes.all fun c =>
      decide (c.id ≠ o.classifier) || decide (c.isAbstract = false)),
   ("observations exact", m.objects.all fun o => s.properties.all fun p =>
      decide ((m.observations.any fun a => decide (a.object = o.id) && decide (a.property = p.id)) =
        decide (s.applicableProperty o.classifier p.id))),
   ("observation keys resolved", m.observations.all fun a =>
      (m.objects.any fun o => decide (o.id = a.object)) && (s.properties.any fun p => decide (p.id = a.property))),
   ("observations applicable", m.observations.all fun a => m.objects.all fun o =>
      decide (o.id ≠ a.object) || decide (s.applicableProperty o.classifier a.property)),
   ("values typed", m.observations.all fun a => s.properties.all fun p =>
      decide (p.id ≠ a.property) || a.occurrences.all (valueMatchesB s m p.type)),
   ("multiplicity bounds", m.objects.all fun o => s.properties.all fun p =>
      decide (¬ s.applicableProperty o.classifier p.id) ||
        decide (withinMultiplicity p.multiplicity (m.occurrences o.id p.id).length)),
   ("unique occurrences", m.objects.all fun o => s.properties.all fun p =>
      decide (¬ s.applicableProperty o.classifier p.id) || decide (p.multiplicity.isUnique ≠ true) ||
        decide ((m.occurrences o.id p.id).Nodup)),
   ("opposite counts", s.associations.all fun a => oppositeCountsForB m a.ends.1 a.ends.2),
   ("one incoming composite", m.objects.all fun o => decide (incomingCompositeCount s m o.id ≤ 1)),
   ("containment acyclic", m.objects.all fun o => containmentForB s m o.id)]

/-- Accept a snapshot exactly when every named conformance field check succeeds. -/
def checkSnapshot (s : Schema) (m : Snapshot) : Bool :=
  (snapshotFieldChecks s m).all (fun x => x.2)

/-- Report one snapshot diagnostic for each failed named conformance check, in check
order. -/
def snapshotDiagnostics (s : Schema) (m : Snapshot) : List Diagnostic :=
  (snapshotFieldChecks s m).filterMap fun x => if x.2 then none else some (.snapshot x.1)

end VLMOF
