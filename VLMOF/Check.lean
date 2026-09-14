import VLMOF.Semantics

namespace VLMOF

instance (c : Char) : Decidable (xmlChar c) := by unfold xmlChar; infer_instance
instance (x : String) : Decidable (validString x) := by unfold validString; infer_instance
instance (x : Option String) : Decidable (validName x) := by unfold validName; split <;> infer_instance
instance (x : Multiplicity) : Decidable (multiplicityValid x) := by unfold multiplicityValid; split <;> infer_instance
instance (x : Multiplicity) (n : Nat) : Decidable (withinMultiplicity x n) := by unfold withinMultiplicity; split <;> infer_instance
instance (a : AssociationDecl) (p : PropertyDecl) : Decidable (ownerMatchesEnd a p) := by unfold ownerMatchesEnd; split <;> infer_instance
instance (p q : PropertyDecl) : Decidable (classOwnerIsSource p q) := by unfold classOwnerIsSource; split <;> infer_instance
instance (p q : PropertyDecl) : Decidable (atMostOneAssociationOwned p q) := by unfold atMostOneAssociationOwned; split <;> infer_instance

inductive Diagnostic where
  | schema (field : String)
  | snapshot (field : String)
  deriving DecidableEq, Repr

def refType : ValueType → Bool | .reference _ => true | _ => false

def associationPairOK (a : AssociationDecl) (p q : PropertyDecl) : Bool :=
  decide (a.ends = (p.id, q.id)) && decide (p.id ≠ q.id) && refType p.type && refType q.type &&
  decide (ownerMatchesEnd a p) && decide (ownerMatchesEnd a q) &&
  decide (classOwnerIsSource p q) && decide (classOwnerIsSource q p) &&
  decide (atMostOneAssociationOwned p q) &&
  decide (¬ (p.aggregation = .composite ∧ q.aggregation = .composite))

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

def checkSchema (s : Schema) : Bool := (schemaFieldChecks s).all (fun x => x.2)
def schemaDiagnostics (s : Schema) : List Diagnostic :=
  (schemaFieldChecks s).filterMap fun x => if x.2 then none else some (.schema x.1)

def referenceTargets (m : Snapshot) : List ObjectId :=
  m.observations.flatMap fun a => a.occurrences.filterMap fun
    | .reference o => some o | _ => none

def compositeEdgeB (s : Schema) (m : Snapshot) (src dst : ObjectId) : Bool :=
  m.observations.any fun a => decide (a.object = src) && s.properties.any fun p =>
    decide (p.id = a.property) && decide (p.aggregation = .composite) &&
      a.occurrences.contains (.reference dst)

def compositeReachableB (s : Schema) (m : Snapshot) (src dst : ObjectId) : Bool :=
  (iterateClosure (outgoingComposite s m) m.objects.length [src]).contains dst

def valueMatchesB (s : Schema) (m : Snapshot) : ValueType → Value → Bool
  | .boolean, .boolean _ => true
  | .integer, .integer _ => true
  | .string, .string x => decide (validString x)
  | .enumeration e, .enumeration e' l => decide (e = e') &&
      s.literals.any (fun d => decide (d.id = l) && decide (d.enumeration = e))
  | .reference c, .reference o => m.objects.any (fun d =>
      decide (d.id = o) && decide (s.isSubtype d.classifier c))
  | _, _ => false

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
   ("opposite counts", s.associations.all fun a => m.objects.all fun x => m.objects.all fun y =>
      decide ((m.occurrences x.id a.ends.1).count (.reference y.id) =
        (m.occurrences y.id a.ends.2).count (.reference x.id))),
   ("one incoming composite", m.objects.all fun o => decide (incomingCompositeCount s m o.id ≤ 1)),
   ("containment acyclic", m.objects.all fun o => (referenceTargets m).all fun child =>
      !compositeEdgeB s m o.id child || !compositeReachableB s m child o.id)]

def checkSnapshot (s : Schema) (m : Snapshot) : Bool :=
  (snapshotFieldChecks s m).all (fun x => x.2)

def snapshotDiagnostics (s : Schema) (m : Snapshot) : List Diagnostic :=
  (snapshotFieldChecks s m).filterMap fun x => if x.2 then none else some (.snapshot x.1)

end VLMOF
