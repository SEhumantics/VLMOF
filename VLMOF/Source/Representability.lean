import VLMOF.Source.Adequacy

/-!
# Canonical source images and representation up to typed identities

The symbolic binder does not preserve user supplied numeric identities: it allocates
each declaration and object at its position in the corresponding source list.  This
module makes that image explicit without defining it by running `elaborate`.

`canonicalSchema` and `canonicalSnapshot` are total structural translations.  Their
only lookup primitive is the first entry of `matchingIndices`; successful binding
guarantees that this list is a singleton.  Thus the exact-image theorems below say
which Core records the existing binder constructs, rather than merely asserting that
some elaboration result exists.

Core artifacts commonly carry different numeric identities.  `TypedIdRenaming` keeps
the six declaration identity spaces and the object identity space distinct.  The
`RepresentableModuloIds` predicate says precisely that a Core pair is a typed renaming
of the canonical image of a satisfying source document.
-/
namespace VLMOF.Source

/-- The numeric position selected by a uniquely resolving alias.  The default is
irrelevant on successful binding paths, where `matchingIndices` is a singleton. -/
def resolvedIndex (names : List Name) (name : Name) : Nat :=
  (matchingIndices names name).head?.getD 0

theorem resolvedIndex_eq_of_resolveIndex {kind : String} {names : List Name}
    {name : Name} {index : Nat} (h : resolveIndex kind names name = .ok index) :
    resolvedIndex names name = index := by
  rw [resolvedIndex, (resolveIndex_ok_iff kind names name index).mp h]
  rfl

def canonicalPackageId (model : Model) (name : Name) : PackageId :=
  ⟨resolvedIndex (model.packages.map Package.alias) name⟩

def canonicalClassId (model : Model) (name : Name) : ClassId :=
  ⟨resolvedIndex (model.classes.map Class.alias) name⟩

def canonicalPropertyId (model : Model) (name : Name) : PropertyId :=
  ⟨resolvedIndex (model.properties.map Property.alias) name⟩

def canonicalAssociationId (model : Model) (name : Name) : AssociationId :=
  ⟨resolvedIndex (model.associations.map Association.alias) name⟩

def canonicalEnumerationId (model : Model) (name : Name) : EnumerationId :=
  ⟨resolvedIndex (model.enumerations.map Enumeration.alias) name⟩

def canonicalLiteralId (model : Model) (name : Name) : LiteralId :=
  ⟨resolvedIndex (model.literals.map Literal.alias) name⟩

def canonicalObjectId (snapshot : Instance) (name : Name) : ObjectId :=
  ⟨resolvedIndex (snapshot.objects.map Object.alias) name⟩

def canonicalType (model : Model) : Source.ValueType → VLMOF.ValueType
  | .boolean => .boolean
  | .integer => .integer
  | .string => .string
  | .enumeration name => .enumeration (canonicalEnumerationId model name)
  | .reference name => .reference (canonicalClassId model name)

def canonicalOwner (model : Model) : Owner → PropertyOwner
  | .class name => .class (canonicalClassId model name)
  | .association name => .association (canonicalAssociationId model name)

def canonicalValue (model : Model) (snapshot : Instance) : Source.Value → VLMOF.Value
  | .boolean value => .boolean value
  | .integer value => .integer value
  | .string value => .string value
  | .enumeration enumeration literal =>
      .enumeration (canonicalEnumerationId model enumeration)
        (canonicalLiteralId model literal)
  | .reference object => .reference (canonicalObjectId snapshot object)

private def canonicalEnds (model : Model) (ends : List Name) : PropertyId × PropertyId :=
  match ends with
  | [first, second] =>
      (canonicalPropertyId model first, canonicalPropertyId model second)
  | _ => (⟨0⟩, ⟨0⟩)

private def canonicalPackageEntry (model : Model) (x : Package × Nat) : PackageDecl :=
  { id := ⟨x.2⟩, name := some x.1.name,
    parent := x.1.parent.map (canonicalPackageId model) }

private def canonicalClassEntry (model : Model) (x : Class × Nat) : ClassDecl :=
  { id := ⟨x.2⟩, name := some x.1.name,
    package := x.1.package.map (canonicalPackageId model),
    isAbstract := x.1.isAbstract,
    directSupers := x.1.directSupers.map (canonicalClassId model) }

private def canonicalPropertyEntry (model : Model) (x : Property × Nat) : PropertyDecl :=
  { id := ⟨x.2⟩, name := some x.1.name,
    owner := canonicalOwner model x.1.owner,
    type := canonicalType model x.1.type,
    multiplicity := x.1.multiplicity,
    aggregation := x.1.aggregation,
    isId := x.1.isId }

private def canonicalAssociationEntry (model : Model)
    (x : Association × Nat) : AssociationDecl :=
  { id := ⟨x.2⟩, name := some x.1.name,
    package := x.1.package.map (canonicalPackageId model),
    ends := canonicalEnds model x.1.ends }

private def canonicalEnumerationEntry (model : Model)
    (x : Enumeration × Nat) : EnumerationDecl :=
  { id := ⟨x.2⟩, name := some x.1.name,
    package := x.1.package.map (canonicalPackageId model) }

private def canonicalLiteralEntry (model : Model) (x : Literal × Nat) : LiteralDecl :=
  { id := ⟨x.2⟩, name := some x.1.name,
    enumeration := canonicalEnumerationId model x.1.enumeration }

private def canonicalObjectEntry (model : Model) (x : Object × Nat) : ObjectDecl :=
  { id := ⟨x.2⟩, classifier := canonicalClassId model x.1.classifier }

private def canonicalObservationEntry (model : Model) (snapshot : Instance)
    (source : Source.Observation) : VLMOF.Observation :=
  { object := canonicalObjectId snapshot source.object
    property := canonicalPropertyId model source.property
    occurrences := source.occurrences.map (canonicalValue model snapshot) }

/-- The Core schema structurally selected by the binder's allocation policy. -/
def canonicalSchema (model : Model) : Schema :=
  { packages := model.packages.zipIdx.map (canonicalPackageEntry model)
    classes := model.classes.zipIdx.map (canonicalClassEntry model)
    properties := model.properties.zipIdx.map (canonicalPropertyEntry model)
    associations := model.associations.zipIdx.map (canonicalAssociationEntry model)
    enumerations := model.enumerations.zipIdx.map (canonicalEnumerationEntry model)
    literals := model.literals.zipIdx.map (canonicalLiteralEntry model) }

/-- The Core snapshot structurally selected by the binder's allocation policy. -/
def canonicalSnapshot (model : Model) (snapshot : Instance) : Snapshot :=
  { objects := snapshot.objects.zipIdx.map (canonicalObjectEntry model)
    observations := snapshot.observations.map (canonicalObservationEntry model snapshot) }

private theorem packageId_eq_canonical {model : Model} {name : Name} {id : PackageId}
    (h : packageId model name = .ok id) : id = canonicalPackageId model name := by
  unfold packageId at h
  cases hr : resolveIndex "package" (model.packages.map Package.alias) name with
  | error error => simp [hr, Functor.map, Except.map] at h
  | ok index =>
      simp [hr, Functor.map, Except.map] at h
      subst id
      simp [canonicalPackageId, resolvedIndex_eq_of_resolveIndex hr]

private theorem classId_eq_canonical {model : Model} {name : Name} {id : ClassId}
    (h : classId model name = .ok id) : id = canonicalClassId model name := by
  unfold classId at h
  cases hr : resolveIndex "class" (model.classes.map Class.alias) name with
  | error error => simp [hr, Functor.map, Except.map] at h
  | ok index =>
      simp [hr, Functor.map, Except.map] at h
      subst id
      simp [canonicalClassId, resolvedIndex_eq_of_resolveIndex hr]

private theorem propertyId_eq_canonical {model : Model} {name : Name} {id : PropertyId}
    (h : propertyId model name = .ok id) : id = canonicalPropertyId model name := by
  unfold propertyId at h
  cases hr : resolveIndex "property" (model.properties.map Property.alias) name with
  | error error => simp [hr, Functor.map, Except.map] at h
  | ok index =>
      simp [hr, Functor.map, Except.map] at h
      subst id
      simp [canonicalPropertyId, resolvedIndex_eq_of_resolveIndex hr]

private theorem associationId_eq_canonical {model : Model} {name : Name}
    {id : AssociationId} (h : associationId model name = .ok id) :
    id = canonicalAssociationId model name := by
  unfold associationId at h
  cases hr : resolveIndex "association" (model.associations.map Association.alias) name with
  | error error => simp [hr, Functor.map, Except.map] at h
  | ok index =>
      simp [hr, Functor.map, Except.map] at h
      subst id
      simp [canonicalAssociationId, resolvedIndex_eq_of_resolveIndex hr]

private theorem enumerationId_eq_canonical {model : Model} {name : Name}
    {id : EnumerationId} (h : enumerationId model name = .ok id) :
    id = canonicalEnumerationId model name := by
  unfold enumerationId at h
  cases hr : resolveIndex "enumeration" (model.enumerations.map Enumeration.alias) name with
  | error error => simp [hr, Functor.map, Except.map] at h
  | ok index =>
      simp [hr, Functor.map, Except.map] at h
      subst id
      simp [canonicalEnumerationId, resolvedIndex_eq_of_resolveIndex hr]

private theorem literalId_eq_canonical {model : Model} {name : Name} {id : LiteralId}
    (h : literalId model name = .ok id) : id = canonicalLiteralId model name := by
  unfold literalId at h
  cases hr : resolveIndex "literal" (model.literals.map Literal.alias) name with
  | error error => simp [hr, Functor.map, Except.map] at h
  | ok index =>
      simp [hr, Functor.map, Except.map] at h
      subst id
      simp [canonicalLiteralId, resolvedIndex_eq_of_resolveIndex hr]

private theorem objectId_eq_canonical {snapshot : Instance} {name : Name} {id : ObjectId}
    (h : objectId snapshot name = .ok id) : id = canonicalObjectId snapshot name := by
  unfold objectId at h
  cases hr : resolveIndex "object" (snapshot.objects.map Object.alias) name with
  | error error => simp [hr, Functor.map, Except.map] at h
  | ok index =>
      simp [hr, Functor.map, Except.map] at h
      subst id
      simp [canonicalObjectId, resolvedIndex_eq_of_resolveIndex hr]

private theorem optionalPackage_eq_canonical {model : Model} {source : Option Name}
    {target : Option PackageId} (h : optionalPackage model source = .ok target) :
    target = source.map (canonicalPackageId model) := by
  cases source with
  | none =>
      have h' : (none : Option PackageId) = target := by
        change Except.ok none = Except.ok target at h
        exact Except.ok.inj h
      exact h'.symm
  | some name =>
      simp only [optionalPackage] at h
      cases hp : packageId model name with
      | error error => simp [hp, Functor.map, Except.map] at h
      | ok id =>
          simp [hp, Functor.map, Except.map] at h
          subst target
          simp [packageId_eq_canonical hp]

private theorem bindType_eq_canonical {model : Model} {source : Source.ValueType}
    {target : VLMOF.ValueType} (h : bindType model source = .ok target) :
    target = canonicalType model source := by
  cases source
  · change target = VLMOF.ValueType.boolean
    change Except.ok VLMOF.ValueType.boolean = Except.ok target at h
    exact (Except.ok.inj h).symm
  · change target = VLMOF.ValueType.integer
    change Except.ok VLMOF.ValueType.integer = Except.ok target at h
    exact (Except.ok.inj h).symm
  · change target = VLMOF.ValueType.string
    change Except.ok VLMOF.ValueType.string = Except.ok target at h
    exact (Except.ok.inj h).symm
  · rename_i name
    cases he : enumerationId model name with
    | error error => simp [bindType, he, Functor.map, Except.map] at h
    | ok eid =>
        have hb : (Except.ok (VLMOF.ValueType.enumeration eid) : BindingResult VLMOF.ValueType) =
            .ok target := by
          simpa [bindType, he, Functor.map, Except.map] using h
        have ht : VLMOF.ValueType.enumeration eid = target := by
          exact Except.ok.inj hb
        rw [← ht, canonicalType, ← enumerationId_eq_canonical he]
  · rename_i name
    cases hc : classId model name with
    | error error => simp [bindType, hc, Functor.map, Except.map] at h
    | ok cid =>
        have hb : (Except.ok (VLMOF.ValueType.reference cid) : BindingResult VLMOF.ValueType) =
            .ok target := by
          simpa [bindType, hc, Functor.map, Except.map] using h
        have ht : VLMOF.ValueType.reference cid = target := by
          exact Except.ok.inj hb
        rw [← ht, canonicalType, ← classId_eq_canonical hc]

private theorem bindOwner_eq_canonical {model : Model} {source : Owner}
    {target : PropertyOwner} (h : bindOwner model source = .ok target) :
    target = canonicalOwner model source := by
  cases source with
  | «class» name =>
      cases hc : classId model name <;>
        simp [bindOwner, canonicalOwner, hc, Functor.map, Except.map] at h
      subst target
      change PropertyOwner.class _ = PropertyOwner.class _
      rw [classId_eq_canonical hc]
  | association name =>
      cases ha : associationId model name <;>
        simp [bindOwner, canonicalOwner, ha, Functor.map, Except.map] at h
      subst target
      change PropertyOwner.association _ = PropertyOwner.association _
      rw [associationId_eq_canonical ha]

private theorem bindValue_eq_canonical {model : Model} {snapshot : Instance}
    {source : Source.Value} {target : VLMOF.Value}
    (h : bindValue model snapshot source = .ok target) :
    target = canonicalValue model snapshot source := by
  cases source
  · rename_i value
    change target = VLMOF.Value.boolean value
    change Except.ok (VLMOF.Value.boolean value) = Except.ok target at h
    exact (Except.ok.inj h).symm
  · rename_i value
    change target = VLMOF.Value.integer value
    change Except.ok (VLMOF.Value.integer value) = Except.ok target at h
    exact (Except.ok.inj h).symm
  · rename_i value
    change target = VLMOF.Value.string value
    change Except.ok (VLMOF.Value.string value) = Except.ok target at h
    exact (Except.ok.inj h).symm
  · rename_i enumeration literal
    cases he : enumerationId model enumeration with
    | error error => simp [bindValue, he, Bind.bind, Except.bind] at h
    | ok eid =>
        cases hl : literalId model literal with
        | error error => simp [bindValue, he, hl, Bind.bind, Except.bind] at h
        | ok lid =>
            simp [bindValue, he, hl, Bind.bind, Except.bind, pure, Except.pure] at h
            subst target
            simp [canonicalValue, enumerationId_eq_canonical he,
              literalId_eq_canonical hl]
  · rename_i object
    cases ho : objectId snapshot object with
    | error error => simp [bindValue, ho, Functor.map, Except.map] at h
    | ok oid =>
        have hb : (Except.ok (VLMOF.Value.reference oid) : BindingResult VLMOF.Value) =
            .ok target := by
          simpa [bindValue, ho, Functor.map, Except.map] using h
        have ht : VLMOF.Value.reference oid = target := by
          exact Except.ok.inj hb
        rw [← ht, canonicalValue, ← objectId_eq_canonical ho]

private theorem packageEntry_eq_canonical {model : Model} {x : Package × Nat}
    {target : PackageDecl} (h : bindPackageEntry model x = .ok target) :
    target = canonicalPackageEntry model x := by
  unfold bindPackageEntry at h
  cases hq : checkQualification x.1.alias x.1.parent <;>
    cases hp : optionalPackage model x.1.parent <;>
    simp [hq, hp, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  simp [canonicalPackageEntry, optionalPackage_eq_canonical hp]

private theorem classEntry_eq_canonical {model : Model} {x : Class × Nat}
    {target : ClassDecl} (h : bindClassEntry model x = .ok target) :
    target = canonicalClassEntry model x := by
  unfold bindClassEntry at h
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    cases hs : x.1.directSupers.mapM (classId model) <;>
    simp [hq, hp, hs, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  have hsmap := mapM_ok_map_eq hs (keySource := canonicalClassId model)
    (keyTarget := id) (fun source target hb => classId_eq_canonical hb)
  simp only [List.map_id] at hsmap
  simp [canonicalClassEntry, optionalPackage_eq_canonical hp, hsmap]

private theorem propertyEntry_eq_canonical {model : Model} {x : Property × Nat}
    {target : PropertyDecl} (h : bindPropertyEntry model x = .ok target) :
    target = canonicalPropertyEntry model x := by
  unfold bindPropertyEntry at h
  cases hq : checkQualification x.1.alias (some (ownerName x.1.owner)) <;>
    cases ho : bindOwner model x.1.owner <;>
    cases ht : bindType model x.1.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  simp [canonicalPropertyEntry, bindOwner_eq_canonical ho, bindType_eq_canonical ht]

private theorem associationEntry_eq_canonical {model : Model} {x : Association × Nat}
    {target : AssociationDecl} (h : bindAssociationEntry model x = .ok target) :
    target = canonicalAssociationEntry model x := by
  unfold bindAssociationEntry at h
  cases hq : checkQualification x.1.alias x.1.package with
  | error error => simp [hq, Bind.bind, Except.bind] at h
  | ok unit =>
      cases hp : optionalPackage model x.1.package with
      | error error => simp [hq, hp, Bind.bind, Except.bind] at h
      | ok package =>
          cases he : x.1.ends with
          | nil => simp [hq, hp, he, Bind.bind, Except.bind] at h
          | cons first rest =>
              cases rest with
              | nil => simp [hq, hp, he, Bind.bind, Except.bind] at h
              | cons second tail =>
                  cases tail with
                  | cons third tail => simp [hq, hp, he, Bind.bind, Except.bind] at h
                  | nil =>
                      cases hf : propertyId model first with
                      | error error => simp [hq, hp, he, hf, Bind.bind, Except.bind] at h
                      | ok firstId =>
                          cases hs : propertyId model second with
                          | error error =>
                              simp [hq, hp, he, hf, hs, Bind.bind, Except.bind] at h
                          | ok secondId =>
                              simp [hq, hp, he, hf, hs, Bind.bind, Except.bind,
                                pure, Except.pure] at h
                              subst target
                              simp [canonicalAssociationEntry, canonicalEnds, he,
                                optionalPackage_eq_canonical hp,
                                propertyId_eq_canonical hf, propertyId_eq_canonical hs]

private theorem enumerationEntry_eq_canonical {model : Model} {x : Enumeration × Nat}
    {target : EnumerationDecl} (h : bindEnumerationEntry model x = .ok target) :
    target = canonicalEnumerationEntry model x := by
  unfold bindEnumerationEntry at h
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    simp [hq, hp, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  simp [canonicalEnumerationEntry, optionalPackage_eq_canonical hp]

private theorem literalEntry_eq_canonical {model : Model} {x : Literal × Nat}
    {target : LiteralDecl} (h : bindLiteralEntry model x = .ok target) :
    target = canonicalLiteralEntry model x := by
  unfold bindLiteralEntry at h
  cases hq : checkQualification x.1.alias (some x.1.enumeration) <;>
    cases he : enumerationId model x.1.enumeration <;>
    simp [hq, he, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  simp [canonicalLiteralEntry, enumerationId_eq_canonical he]

/-- A successful model binding has one exact, structurally defined Core result. -/
theorem bindModel_eq_canonical {model : Model} {target : Schema}
    (h : bindModel model = .ok target) : target = canonicalSchema model := by
  let a := modelAllocation_of_bindModel h
  cases target
  simp only [canonicalSchema]
  congr 1
  · simpa using mapM_ok_map_eq a.packages (keySource := canonicalPackageEntry model)
      (keyTarget := id) (fun _ _ hb => packageEntry_eq_canonical hb)
  · simpa using mapM_ok_map_eq a.classes (keySource := canonicalClassEntry model)
      (keyTarget := id) (fun _ _ hb => classEntry_eq_canonical hb)
  · simpa using mapM_ok_map_eq a.properties (keySource := canonicalPropertyEntry model)
      (keyTarget := id) (fun _ _ hb => propertyEntry_eq_canonical hb)
  · simpa using mapM_ok_map_eq a.associations (keySource := canonicalAssociationEntry model)
      (keyTarget := id) (fun _ _ hb => associationEntry_eq_canonical hb)
  · simpa using mapM_ok_map_eq a.enumerations (keySource := canonicalEnumerationEntry model)
      (keyTarget := id) (fun _ _ hb => enumerationEntry_eq_canonical hb)
  · simpa using mapM_ok_map_eq a.literals (keySource := canonicalLiteralEntry model)
      (keyTarget := id) (fun _ _ hb => literalEntry_eq_canonical hb)

private theorem objectEntry_eq_canonical {model : Model}
    {x : Object × Nat} {target : ObjectDecl}
    (h : bindObjectAllocation model x = .ok target) :
    target = canonicalObjectEntry model x := by
  unfold bindObjectAllocation at h
  cases hc : classId model x.1.classifier <;>
    simp [hc, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  simp [canonicalObjectEntry, classId_eq_canonical hc]

private theorem observationEntry_eq_canonical {model : Model} {snapshot : Instance}
    {source : Source.Observation} {target : VLMOF.Observation}
    (h : bindObservationAllocation model snapshot source = .ok target) :
    target = canonicalObservationEntry model snapshot source := by
  unfold bindObservationAllocation at h
  cases ho : objectId snapshot source.object <;>
    cases hp : propertyId model source.property <;>
    cases hv : source.occurrences.mapM (bindValue model snapshot) <;>
    simp [ho, hp, hv, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  have hvmap := mapM_ok_map_eq hv (keySource := canonicalValue model snapshot)
    (keyTarget := id) (fun source target hb => bindValue_eq_canonical hb)
  simp only [List.map_id] at hvmap
  simp [canonicalObservationEntry, objectId_eq_canonical ho,
    propertyId_eq_canonical hp, hvmap]

/-- A successful instance binding likewise has one exact structural result. -/
theorem bindInstance_eq_canonical {model : Model} {snapshot : Instance}
    {target : Snapshot} (h : bindInstance model snapshot = .ok target) :
    target = canonicalSnapshot model snapshot := by
  obtain ⟨ho, ha⟩ := bindInstance_ok_mapM h
  cases target
  simp only [canonicalSnapshot]
  congr 1
  · simpa using mapM_ok_map_eq ho (keySource := canonicalObjectEntry model)
      (keyTarget := id) (fun _ _ hb => objectEntry_eq_canonical hb)
  · simpa using mapM_ok_map_eq ha (keySource := canonicalObservationEntry model snapshot)
      (keyTarget := id) (fun _ _ hb => observationEntry_eq_canonical hb)

/-- Declarative source satisfaction is a sufficient condition for elaboration to
the explicitly computed canonical Core pair. -/
theorem elaborate_eq_canonical {document : Document} (h : SourceSatisfies document) :
    elaborate document = .ok
      (canonicalSchema document.model,
        canonicalSnapshot document.model document.snapshot) := by
  obtain ⟨schema, snapshot, he⟩ := elaborate_complete h
  obtain ⟨hm, hi⟩ := elaborate_bindings he
  rw [← bindModel_eq_canonical hm, ← bindInstance_eq_canonical hi]
  exact he

/-- Canonical allocation means that each stored numeric identity is its list index. -/
structure CanonicalSchemaIds (schema : Schema) : Prop where
  packages : schema.packages.map (fun d => d.id.val) = List.range schema.packages.length
  classes : schema.classes.map (fun d => d.id.val) = List.range schema.classes.length
  properties : schema.properties.map (fun d => d.id.val) = List.range schema.properties.length
  associations : schema.associations.map (fun d => d.id.val) =
    List.range schema.associations.length
  enumerations : schema.enumerations.map (fun d => d.id.val) =
    List.range schema.enumerations.length
  literals : schema.literals.map (fun d => d.id.val) = List.range schema.literals.length

def CanonicalSnapshotIds (snapshot : Snapshot) : Prop :=
  snapshot.objects.map (fun d => d.id.val) = List.range snapshot.objects.length

private theorem mappedZipIdx_indices {α β : Type} (xs : List α)
    (f : α × Nat → β) (value : β → Nat)
    (h : ∀ x, value (f x) = x.2) :
    (xs.zipIdx.map f).map value = List.range (xs.zipIdx.map f).length := by
  rw [List.map_map]
  have hfun : value ∘ f = Prod.snd := by
    funext x
    exact h x
  rw [hfun, List.zipIdx_map_snd, List.length_map, List.length_zipIdx,
    List.range_eq_range']

theorem canonicalSchema_ids (model : Model) : CanonicalSchemaIds (canonicalSchema model) := by
  refine {
    packages := ?_, classes := ?_, properties := ?_, associations := ?_,
    enumerations := ?_, literals := ?_ }
  · exact mappedZipIdx_indices model.packages (canonicalPackageEntry model)
      (fun d => d.id.val) (fun _ => rfl)
  · exact mappedZipIdx_indices model.classes (canonicalClassEntry model)
      (fun d => d.id.val) (fun _ => rfl)
  · exact mappedZipIdx_indices model.properties (canonicalPropertyEntry model)
      (fun d => d.id.val) (fun _ => rfl)
  · exact mappedZipIdx_indices model.associations (canonicalAssociationEntry model)
      (fun d => d.id.val) (fun _ => rfl)
  · exact mappedZipIdx_indices model.enumerations (canonicalEnumerationEntry model)
      (fun d => d.id.val) (fun _ => rfl)
  · exact mappedZipIdx_indices model.literals (canonicalLiteralEntry model)
      (fun d => d.id.val) (fun _ => rfl)

theorem canonicalSnapshot_ids (model : Model) (snapshot : Instance) :
    CanonicalSnapshotIds (canonicalSnapshot model snapshot) := by
  exact mappedZipIdx_indices snapshot.objects (canonicalObjectEntry model)
    (fun d => d.id.val) (fun _ => rfl)

theorem bindModel_canonical_ids {model : Model} {target : Schema}
    (h : bindModel model = .ok target) : CanonicalSchemaIds target := by
  rw [bindModel_eq_canonical h]
  exact canonicalSchema_ids model

theorem bindInstance_canonical_ids {model : Model} {snapshot : Instance}
    {target : Snapshot} (h : bindInstance model snapshot = .ok target) :
    CanonicalSnapshotIds target := by
  rw [bindInstance_eq_canonical h]
  exact canonicalSnapshot_ids model snapshot

theorem noncanonicalSchema_not_directly_representable {schema : Schema}
    (h : ¬ CanonicalSchemaIds schema) : ¬ ∃ model, bindModel model = .ok schema := by
  rintro ⟨model, hb⟩
  exact h (bindModel_canonical_ids hb)

theorem noncanonicalSnapshot_not_directly_representable {schema : Model}
    {source : Instance} {snapshot : Snapshot} (h : ¬ CanonicalSnapshotIds snapshot) :
    ¬ bindInstance schema source = .ok snapshot := by
  intro hb
  exact h (bindInstance_canonical_ids hb)

/-- Every declaration produced by the source binder has a metadata spelling. -/
structure FullyNamedSchema (schema : Schema) : Prop where
  packages : ∀ d ∈ schema.packages, d.name ≠ none
  classes : ∀ d ∈ schema.classes, d.name ≠ none
  properties : ∀ d ∈ schema.properties, d.name ≠ none
  associations : ∀ d ∈ schema.associations, d.name ≠ none
  enumerations : ∀ d ∈ schema.enumerations, d.name ≠ none
  literals : ∀ d ∈ schema.literals, d.name ≠ none

theorem canonicalSchema_fullyNamed (model : Model) : FullyNamedSchema (canonicalSchema model) := by
  constructor
  · intro d hd
    rcases List.mem_map.mp hd with ⟨x, _, rfl⟩
    simp [canonicalPackageEntry]
  · intro d hd
    rcases List.mem_map.mp hd with ⟨x, _, rfl⟩
    simp [canonicalClassEntry]
  · intro d hd
    rcases List.mem_map.mp hd with ⟨x, _, rfl⟩
    simp [canonicalPropertyEntry]
  · intro d hd
    rcases List.mem_map.mp hd with ⟨x, _, rfl⟩
    simp [canonicalAssociationEntry]
  · intro d hd
    rcases List.mem_map.mp hd with ⟨x, _, rfl⟩
    simp [canonicalEnumerationEntry]
  · intro d hd
    rcases List.mem_map.mp hd with ⟨x, _, rfl⟩
    simp [canonicalLiteralEntry]

theorem bindModel_fullyNamed {model : Model} {target : Schema}
    (h : bindModel model = .ok target) : FullyNamedSchema target := by
  rw [bindModel_eq_canonical h]
  exact canonicalSchema_fullyNamed model

/-- In particular an unnamed Core class has no direct source image. -/
theorem unnamedClass_not_directly_representable {schema : Schema} {declaration : ClassDecl}
    (hm : declaration ∈ schema.classes) (hn : declaration.name = none) :
    ¬ ∃ model, bindModel model = .ok schema := by
  rintro ⟨model, hb⟩
  exact (bindModel_fullyNamed hb).classes declaration hm hn

/-- A renaming cannot accidentally mix identity kinds.  Each field is an equivalence,
so the renamed Core graph preserves and reflects identity. -/
structure TypedIdRenaming where
  package : PackageId → PackageId
  classId : ClassId → ClassId
  property : PropertyId → PropertyId
  association : AssociationId → AssociationId
  enumeration : EnumerationId → EnumerationId
  literal : LiteralId → LiteralId
  object : ObjectId → ObjectId
  package_injective : Function.Injective package
  package_surjective : Function.Surjective package
  class_injective : Function.Injective classId
  class_surjective : Function.Surjective classId
  property_injective : Function.Injective property
  property_surjective : Function.Surjective property
  association_injective : Function.Injective association
  association_surjective : Function.Surjective association
  enumeration_injective : Function.Injective enumeration
  enumeration_surjective : Function.Surjective enumeration
  literal_injective : Function.Injective literal
  literal_surjective : Function.Surjective literal
  object_injective : Function.Injective object
  object_surjective : Function.Surjective object

/-- Qualified source identities supplied independently of optional Core metadata. -/
structure CoreAliasAssignment where
  package : PackageId → Name
  classId : ClassId → Name
  property : PropertyId → Name
  association : AssociationId → Name
  enumeration : EnumerationId → Name
  literal : LiteralId → Name
  object : ObjectId → Name

private def sourceDisplayName (name : Option String) : String := name.getD ""

private def reifyType (names : CoreAliasAssignment) : VLMOF.ValueType → Source.ValueType
  | .boolean => .boolean
  | .integer => .integer
  | .string => .string
  | .enumeration id => .enumeration (names.enumeration id)
  | .reference id => .reference (names.classId id)

private def reifyOwner (names : CoreAliasAssignment) : PropertyOwner → Owner
  | .class id => .class (names.classId id)
  | .association id => .association (names.association id)

private def reifyValue (names : CoreAliasAssignment) : VLMOF.Value → Source.Value
  | .boolean value => .boolean value
  | .integer value => .integer value
  | .string value => .string value
  | .enumeration enumeration literal =>
      .enumeration (names.enumeration enumeration) (names.literal literal)
  | .reference object => .reference (names.object object)

/-- A total Core-to-source reifier.  Alias policy and semantic admissibility are
stated separately in `ReificationConditions`; unnamed metadata becomes the empty
display spelling and therefore cannot satisfy those conditions. -/
def reifyModel (names : CoreAliasAssignment) (schema : Schema) : Model :=
  { packages := schema.packages.map fun d =>
      { alias := names.package d.id, name := sourceDisplayName d.name,
        parent := d.parent.map names.package }
    classes := schema.classes.map fun d =>
      { alias := names.classId d.id, name := sourceDisplayName d.name,
        package := d.package.map names.package, isAbstract := d.isAbstract,
        directSupers := d.directSupers.map names.classId }
    properties := schema.properties.map fun d =>
      { alias := names.property d.id, name := sourceDisplayName d.name,
        owner := reifyOwner names d.owner, type := reifyType names d.type,
        multiplicity := d.multiplicity, aggregation := d.aggregation, isId := d.isId }
    associations := schema.associations.map fun d =>
      { alias := names.association d.id, name := sourceDisplayName d.name,
        package := d.package.map names.package,
        ends := [names.property d.ends.1, names.property d.ends.2] }
    enumerations := schema.enumerations.map fun d =>
      { alias := names.enumeration d.id, name := sourceDisplayName d.name,
        package := d.package.map names.package }
    literals := schema.literals.map fun d =>
      { alias := names.literal d.id, name := sourceDisplayName d.name,
        enumeration := names.enumeration d.enumeration } }

def reifyInstance (names : CoreAliasAssignment) (snapshot : Snapshot) : Instance :=
  { objects := snapshot.objects.map fun d =>
      { alias := names.object d.id, classifier := names.classId d.classifier }
    observations := snapshot.observations.map fun a =>
      { object := names.object a.object, property := names.property a.property,
        occurrences := a.occurrences.map (reifyValue names) } }

def reifyDocument (names : CoreAliasAssignment) (schema : Schema)
    (snapshot : Snapshot) : Document :=
  { model := reifyModel names schema, snapshot := reifyInstance names snapshot }

/-- Schema-only sufficient conditions.  They mention the declarative source model
contract and a structural round trip, but no successful binding result. -/
structure ModelReificationConditions (names : CoreAliasAssignment)
    (schema : Schema) : Prop where
  sourceModelWF : ModelWellFormed (reifyModel names schema)
  schemaRoundTrip : canonicalSchema (reifyModel names schema) = schema

/-- A well-formed reified source model whose structural canonical form is `schema`
passes the actual binder with exactly that result. -/
theorem model_reification_binds {names : CoreAliasAssignment} {schema : Schema}
    (h : ModelReificationConditions names schema) :
    bindModel (reifyModel names schema) = .ok schema := by
  obtain ⟨target, hb⟩ := bindModel_complete h.sourceModelWF
  have ht : target = schema := (bindModel_eq_canonical hb).trans h.schemaRoundTrip
  subst target
  exact hb

theorem model_reification_target_wellFormed {names : CoreAliasAssignment}
    {schema : Schema} (h : ModelReificationConditions names schema) :
    SchemaWellFormed schema := by
  exact schemaWellFormed_of_modelWellFormed_of_bindModel h.sourceModelWF
    (model_reification_binds h)

/-- Concrete sufficient conditions for a Core pair to be an exact source image.
`sourceMeaning` is the independently defined declarative source predicate.  The two
round-trip equations mention only the total structural translations above; no binder,
checker, or existential elaboration result is hidden in this record. -/
structure ReificationConditions (names : CoreAliasAssignment)
    (schema : Schema) (snapshot : Snapshot) : Prop where
  sourceMeaning : SourceSatisfies (reifyDocument names schema snapshot)
  schemaRoundTrip : canonicalSchema (reifyModel names schema) = schema
  snapshotRoundTrip : canonicalSnapshot (reifyModel names schema)
    (reifyInstance names snapshot) = snapshot

/-- The stated Core-side reification conditions construct a source document whose
actual executable elaboration is exactly the requested Core pair. -/
theorem reification_elaborates {names : CoreAliasAssignment}
    {schema : Schema} {snapshot : Snapshot}
    (h : ReificationConditions names schema snapshot) :
    elaborate (reifyDocument names schema snapshot) = .ok (schema, snapshot) := by
  have he := elaborate_eq_canonical h.sourceMeaning
  simpa [reifyDocument, h.schemaRoundTrip, h.snapshotRoundTrip] using he

theorem reification_target_conforms {names : CoreAliasAssignment}
    {schema : Schema} {snapshot : Snapshot}
    (h : ReificationConditions names schema snapshot) : SnapshotConforms schema snapshot := by
  exact snapshotConforms_of_sourceSatisfies_of_elaborate h.sourceMeaning
    (reification_elaborates h)

def renameValue (r : TypedIdRenaming) : VLMOF.Value → VLMOF.Value
  | .boolean value => .boolean value
  | .integer value => .integer value
  | .string value => .string value
  | .enumeration enumeration literal => .enumeration (r.enumeration enumeration) (r.literal literal)
  | .reference object => .reference (r.object object)

def renameType (r : TypedIdRenaming) : VLMOF.ValueType → VLMOF.ValueType
  | .boolean => .boolean
  | .integer => .integer
  | .string => .string
  | .enumeration enumeration => .enumeration (r.enumeration enumeration)
  | .reference cls => .reference (r.classId cls)

def renameOwner (r : TypedIdRenaming) : PropertyOwner → PropertyOwner
  | .class cls => .class (r.classId cls)
  | .association association => .association (r.association association)

def renameSchema (r : TypedIdRenaming) (schema : Schema) : Schema :=
  { packages := schema.packages.map fun d =>
      { id := r.package d.id, name := d.name, parent := d.parent.map r.package }
    classes := schema.classes.map fun d =>
      { id := r.classId d.id, name := d.name, package := d.package.map r.package,
        isAbstract := d.isAbstract,
        directSupers := d.directSupers.map r.classId }
    properties := schema.properties.map fun d =>
      { id := r.property d.id, name := d.name, owner := renameOwner r d.owner,
        type := renameType r d.type, multiplicity := d.multiplicity,
        aggregation := d.aggregation, isId := d.isId }
    associations := schema.associations.map fun d =>
      { id := r.association d.id, name := d.name, package := d.package.map r.package,
        ends := (r.property d.ends.1, r.property d.ends.2) }
    enumerations := schema.enumerations.map fun d =>
      { id := r.enumeration d.id, name := d.name,
        package := d.package.map r.package }
    literals := schema.literals.map fun d =>
      { id := r.literal d.id, name := d.name,
        enumeration := r.enumeration d.enumeration } }

def renameSnapshot (r : TypedIdRenaming) (snapshot : Snapshot) : Snapshot :=
  { objects := snapshot.objects.map fun d =>
      { id := r.object d.id, classifier := r.classId d.classifier }
    observations := snapshot.observations.map fun a =>
      { object := r.object a.object, property := r.property a.property,
        occurrences := a.occurrences.map (renameValue r) } }

/-- Explicit representability domain for Core pairs.  The witness is declarative source
satisfaction plus a typed identity equivalence from its structural canonical image. -/
def RepresentableModuloIds (schema : Schema) (snapshot : Snapshot) : Prop :=
  ∃ document : Document, ∃ ids : TypedIdRenaming,
    SourceSatisfies document ∧
    renameSchema ids (canonicalSchema document.model) = schema ∧
    renameSnapshot ids (canonicalSnapshot document.model document.snapshot) = snapshot

theorem satisfying_source_representable_modulo_ids (document : Document)
    (h : SourceSatisfies document) (ids : TypedIdRenaming) :
    RepresentableModuloIds
      (renameSchema ids (canonicalSchema document.model))
      (renameSnapshot ids (canonicalSnapshot document.model document.snapshot)) := by
  exact ⟨document, ids, h, rfl, rfl⟩

end VLMOF.Source
