import VLMOF.Source.Binding.Applicability
import VLMOF.Source.Correctness.Containment
import VLMOF.Checker.Correctness.Acceptance

/-!
# Full snapshot conformance across elaboration

The remaining row-level fields are transported through the actual object,
property, and observation allocations.  In particular, multiplicity and
uniqueness use the aggregate occurrence correspondence, which retains every
matching source row in order.

Private allocation helpers first identify the source object/property behind each
target row.  Four row-level preservation theorems then establish applicability,
exact coverage, bounds, and uniqueness.  The final assembly theorem combines
those results with typing and graph preservation, followed by elaboration and
checker-facing corollaries.
-/
namespace VLMOF.Source

/-! The local inversion lemmas recover source aliases and rows from allocated
target IDs.  Alias uniqueness is used only to identify the actual row selected by
binding; semantic snapshot facts still come from `SourceSatisfies`. -/

private theorem objectId_ok_iff (snapshot : Instance) (name : Name) (id : ObjectId) :
    objectId snapshot name = .ok id ↔
      resolveIndex "object" (snapshot.objects.map Object.alias) name = .ok id.val := by
  cases id with
  | mk index =>
      cases h : resolveIndex "object" (snapshot.objects.map Object.alias) name <;>
        simp [objectId, h, Except.map]

private theorem propertyId_ok_iff (model : Model) (name : Name) (id : PropertyId) :
    propertyId model name = .ok id ↔
      resolveIndex "property" (model.properties.map Property.alias) name = .ok id.val := by
  cases id with
  | mk index =>
      cases h : resolveIndex "property" (model.properties.map Property.alias) name <;>
        simp [propertyId, h, Except.map]

private theorem objectId_source_injective {snapshot : Instance} {first second : Name}
    {id : ObjectId} (hfirst : objectId snapshot first = .ok id)
    (hsecond : objectId snapshot second = .ok id) : first = second := by
  exact resolveIndex_injective ((objectId_ok_iff snapshot first id).mp hfirst)
    ((objectId_ok_iff snapshot second id).mp hsecond)

private theorem propertyId_source_injective {model : Model} {first second : Name}
    {id : PropertyId} (hfirst : propertyId model first = .ok id)
    (hsecond : propertyId model second = .ok id) : first = second := by
  exact resolveIndex_injective ((propertyId_ok_iff model first id).mp hfirst)
    ((propertyId_ok_iff model second id).mp hsecond)

private theorem bindObjectAllocation_classifier {model : Model} {source : Object}
    {index : Nat} {target : ObjectDecl}
    (h : bindObjectAllocation model (source, index) = .ok target) :
    classId model source.classifier = .ok target.classifier := by
  unfold bindObjectAllocation at h
  cases hc : classId model source.classifier <;>
    simp [hc, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  exact rfl

private theorem bindObjectAllocation_id {model : Model} {source : Object}
    {index : Nat} {target : ObjectDecl}
    (h : bindObjectAllocation model (source, index) = .ok target) :
    target.id = ⟨index⟩ := by
  unfold bindObjectAllocation at h
  cases hc : classId model source.classifier <;>
    simp [hc, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  rfl

private theorem targetObject_source {model : Model} {snapshot : Instance}
    {target : Snapshot} (hsource : SourceSatisfies { model, snapshot })
    (hinstance : bindInstance model snapshot = .ok target)
    {object : ObjectDecl} (hobject : object ∈ target.objects) :
    ∃ sourceObject ∈ snapshot.objects,
      objectId snapshot sourceObject.alias = .ok object.id ∧
      classId model sourceObject.classifier = .ok object.classifier := by
  obtain ⟨entry, hentry, hbind⟩ :=
    mapM_ok_target_mem (bindInstance_ok_mapM hinstance).1 hobject
  obtain ⟨sourceObject, index⟩ := entry
  have hsourceObject := List.fst_mem_of_mem_zipIdx hentry
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp hentry
  have halias : (snapshot.objects.map Object.alias)[index]? = some sourceObject.alias := by
    simp [List.getElem?_map, hget]
  have hresolve : resolveIndex "object" (snapshot.objects.map Object.alias)
      sourceObject.alias = .ok index := by
    rw [resolveIndex_iff_uniqueAliasAt]
    exact uniqueAliasAt_of_nodup hsource.uniqueObjectAliases halias
  have hid := bindObjectAllocation_id hbind
  refine ⟨sourceObject, hsourceObject, ?_, bindObjectAllocation_classifier hbind⟩
  apply (objectId_ok_iff snapshot sourceObject.alias object.id).mpr
  simpa [hid] using hresolve

private theorem propertyAliases_nodup {model : Model} (h : ModelWellFormed model) :
    (model.properties.map Property.alias).Nodup := by
  have hn := h.uniqueQualifiedAliases
  unfold uniqueAliases at hn
  simp only [aliases, List.nodup_append] at hn
  exact hn.1.1.1.2.1

private theorem bindPropertyEntry_id {model : Model} {source : Property}
    {index : Nat} {target : PropertyDecl}
    (h : bindPropertyEntry model (source, index) = .ok target) :
    target.id = ⟨index⟩ := by
  unfold bindPropertyEntry at h
  cases hq : checkQualification source.alias (some (ownerName source.owner)) <;>
    cases ho : bindOwner model source.owner <;>
    cases ht : bindType model source.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  rfl

private theorem bindPropertyEntry_data {model : Model} {source : Property}
    {index : Nat} {target : PropertyDecl}
    (h : bindPropertyEntry model (source, index) = .ok target) :
    target.multiplicity = source.multiplicity ∧ target.isId = source.isId := by
  unfold bindPropertyEntry at h
  cases hq : checkQualification source.alias (some (ownerName source.owner)) <;>
    cases ho : bindOwner model source.owner <;>
    cases ht : bindType model source.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  exact ⟨rfl, rfl⟩

private theorem targetProperty_source {model : Model} {schema : Schema}
    (hwell : ModelWellFormed model)
    (hmodel : bindModel model = .ok schema)
    {property : PropertyDecl} (hproperty : property ∈ schema.properties) :
    ∃ sourceProperty ∈ model.properties,
      propertyId model sourceProperty.alias = .ok property.id ∧
      property.multiplicity = sourceProperty.multiplicity ∧
      property.isId = sourceProperty.isId := by
  have allocation := modelAllocation_of_bindModel hmodel
  obtain ⟨entry, hentry, hbind⟩ :=
    (mapM_ok_mem_iff allocation.properties).mp hproperty
  obtain ⟨sourceProperty, index⟩ := entry
  have hsourceProperty := List.fst_mem_of_mem_zipIdx hentry
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp hentry
  have halias : (model.properties.map Property.alias)[index]? = some sourceProperty.alias := by
    simp [List.getElem?_map, hget]
  have hresolve : resolveIndex "property" (model.properties.map Property.alias)
      sourceProperty.alias = .ok index := by
    rw [resolveIndex_iff_uniqueAliasAt]
    exact uniqueAliasAt_of_nodup (propertyAliases_nodup hwell) halias
  have hid := bindPropertyEntry_id hbind
  refine ⟨sourceProperty, hsourceProperty, ?_, (bindPropertyEntry_data hbind).1,
    (bindPropertyEntry_data hbind).2⟩
  apply (propertyId_ok_iff model sourceProperty.alias property.id).mpr
  simpa [hid] using hresolve

private theorem boundObservation_exists_iff {model : Model} {snapshot : Instance}
    {target : Snapshot}
    (hinstance : bindInstance model snapshot = .ok target)
    {objectName propertyName : Name} {objectTarget : ObjectId} {propertyTarget : PropertyId}
    (hobject : objectId snapshot objectName = .ok objectTarget)
    (hproperty : propertyId model propertyName = .ok propertyTarget) :
    (∃ sourceObservation ∈ snapshot.observations,
      sourceObservation.object = objectName ∧ sourceObservation.property = propertyName) ↔
    ∃ observation ∈ target.observations,
      observation.object = objectTarget ∧ observation.property = propertyTarget := by
  constructor
  · rintro ⟨sourceObservation, hsourceObservation, ho, hp⟩
    obtain ⟨observation, hobservation, hbind⟩ :=
      mapM_ok_source (bindInstance_ok_mapM hinstance).2 hsourceObservation
    have hfacts :=
      (bindObservationAllocation_ok_iff model snapshot sourceObservation observation).mp hbind
    refine ⟨observation, hobservation, ?_, ?_⟩
    · exact Except.ok.inj (hfacts.1.symm.trans (ho ▸ hobject))
    · exact Except.ok.inj (hfacts.2.1.symm.trans (hp ▸ hproperty))
  · rintro ⟨observation, hobservation, ho, hp⟩
    obtain ⟨sourceObservation, hsourceObservation, hsourceObject,
      hsourceProperty, _⟩ := boundObservation_source hinstance hobservation
    refine ⟨sourceObservation, hsourceObservation, ?_, ?_⟩
    · exact objectId_source_injective hsourceObject (by simpa [ho] using hobject)
    · exact propertyId_source_injective hsourceProperty (by simpa [hp] using hproperty)

/-- Exact source observation coverage becomes exact Core coverage for every
allocated object and property.  Applicability is translated in both directions. -/
theorem bindInstance_observationsExact {model : Model} {snapshot : Instance}
    {schema : Schema} {target : Snapshot}
    (hsource : SourceSatisfies { model, snapshot })
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model snapshot = .ok target) :
    ∀ object ∈ target.objects, ∀ property ∈ schema.properties,
      (∃ observation ∈ target.observations,
        observation.object = object.id ∧ observation.property = property.id) ↔
        schema.applicableProperty object.classifier property.id := by
  intro object hobject property hproperty
  obtain ⟨sourceObject, hsourceObject, hobjectId, hclassifier⟩ :=
    targetObject_source hsource hinstance hobject
  obtain ⟨sourceProperty, hsourceProperty, hpropertyId, _, _⟩ :=
    targetProperty_source hsource.model hmodel hproperty
  rw [← boundObservation_exists_iff hinstance hobjectId hpropertyId]
  rw [hsource.observationsExact sourceObject hsourceObject sourceProperty hsourceProperty]
  exact propertyApplies_iff_applicableProperty hsource.model hmodel hclassifier hpropertyId

/-- Every allocated observation is applicable to its object's target classifier,
by reflecting the row to its source key and preserving source applicability. -/
theorem bindInstance_observationApplicable {model : Model} {snapshot : Instance}
    {schema : Schema} {target : Snapshot}
    (hsource : SourceSatisfies { model, snapshot })
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model snapshot = .ok target) :
    ∀ observation ∈ target.observations, ∀ object ∈ target.objects,
      object.id = observation.object →
        schema.applicableProperty object.classifier observation.property := by
  intro observation hobservation object hobject hkey
  obtain ⟨sourceObservation, hsourceObservation, hsourceObjectId,
    hsourcePropertyId, _⟩ := boundObservation_source hinstance hobservation
  obtain ⟨sourceObject, hsourceObject, hobjectId, hclassifier⟩ :=
    targetObject_source hsource hinstance hobject
  have hobjectAlias : sourceObject.alias = sourceObservation.object :=
    objectId_source_injective hobjectId (by simpa [hkey] using hsourceObjectId)
  have happlies := hsource.observationApplicable sourceObservation hsourceObservation
    sourceObject hsourceObject hobjectAlias
  exact (propertyApplies_iff_applicableProperty hsource.model hmodel
    hclassifier hsourcePropertyId).mp happlies

/-- Source multiplicity bounds are preserved because property multiplicities are
copied and aggregate occurrence-list lengths are equal after binding. -/
theorem bindInstance_bounds {model : Model} {snapshot : Instance}
    {schema : Schema} {target : Snapshot}
    (hsource : SourceSatisfies { model, snapshot })
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model snapshot = .ok target) :
    ∀ object ∈ target.objects, ∀ property ∈ schema.properties,
      schema.applicableProperty object.classifier property.id →
        withinMultiplicity property.multiplicity
          (target.occurrences object.id property.id).length := by
  intro object hobject property hproperty happlies
  obtain ⟨sourceObject, hsourceObject, hobjectId, hclassifier⟩ :=
    targetObject_source hsource hinstance hobject
  obtain ⟨sourceProperty, hsourceProperty, hpropertyId, hmultiplicity, _⟩ :=
    targetProperty_source hsource.model hmodel hproperty
  have hsourceApplies := (propertyApplies_iff_applicableProperty hsource.model hmodel
    hclassifier hpropertyId).mpr happlies
  have hbound := hsource.bounds sourceObject hsourceObject sourceProperty
    hsourceProperty hsourceApplies
  rw [hmultiplicity]
  rw [← bindInstance_occurrences_length_eq hinstance hobjectId hpropertyId]
  exact hbound

/-- A source unique property has duplicate-free target occurrences; property flags
are copied and occurrence `Nodup` is preserved and reflected. -/
theorem bindInstance_uniqueness {model : Model} {snapshot : Instance}
    {schema : Schema} {target : Snapshot}
    (hsource : SourceSatisfies { model, snapshot })
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model snapshot = .ok target) :
    ∀ object ∈ target.objects, ∀ property ∈ schema.properties,
      schema.applicableProperty object.classifier property.id →
      property.multiplicity.isUnique = true →
        (target.occurrences object.id property.id).Nodup := by
  intro object hobject property hproperty happlies hunique
  obtain ⟨sourceObject, hsourceObject, hobjectId, hclassifier⟩ :=
    targetObject_source hsource hinstance hobject
  obtain ⟨sourceProperty, hsourceProperty, hpropertyId, hmultiplicity, _⟩ :=
    targetProperty_source hsource.model hmodel hproperty
  have hsourceApplies := (propertyApplies_iff_applicableProperty hsource.model hmodel
    hclassifier hpropertyId).mpr happlies
  have hsourceUnique : sourceProperty.multiplicity.isUnique = true := by
    simpa [hmultiplicity] using hunique
  apply (bindInstance_occurrences_nodup_iff hinstance hobjectId hpropertyId).mp
  exact hsource.uniqueness sourceObject hsourceObject sourceProperty hsourceProperty
    hsourceApplies hsourceUnique

/-- Assemble all schema, allocation, typing, observation, multiplicity, reciprocity,
and containment fields into `SnapshotConforms` from source satisfaction and the
two successful binding equations. -/
theorem snapshotConforms_of_sourceSatisfies_of_bindings
    {model : Model} {snapshot : Instance} {schema : Schema} {target : Snapshot}
    (hsource : SourceSatisfies { model, snapshot })
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model snapshot = .ok target) :
    SnapshotConforms schema target := by
  exact {
    schema := schemaWellFormed_of_modelWellFormed_of_bindModel hsource.model hmodel
    uniqueObjectIds := boundObject_ids_nodup hinstance
    uniqueObservationKeys := bindInstance_uniqueObservationKeys hsource hinstance
    classifiersResolved := bindInstance_classifiersResolved hmodel hinstance
    concreteClassifiers := bindInstance_concreteClassifiers hsource hmodel hinstance
    observationsExact := bindInstance_observationsExact hsource hmodel hinstance
    observationKeysResolved := bindInstance_observationKeysResolved hsource hmodel hinstance
    observationApplicable := bindInstance_observationApplicable hsource hmodel hinstance
    valuesTyped := bindInstance_valuesTyped hsource hmodel hinstance
    bounds := bindInstance_bounds hsource hmodel hinstance
    uniqueness := bindInstance_uniqueness hsource hmodel hinstance
    oppositeCounts := oppositeCounts_of_sourceSatisfies hsource hmodel hinstance
    oneIncomingComposite := oneIncomingComposite_of_sourceSatisfies hsource hmodel hinstance
    containmentAcyclic := containmentAcyclic_of_sourceSatisfies hsource hmodel hinstance
  }

private theorem elaborate_ok_bindings {document : Document} {schema : Schema}
    {snapshot : Snapshot} (h : elaborate document = .ok (schema, snapshot)) :
    bindModel document.model = .ok schema ∧
      bindInstance document.model document.snapshot = .ok snapshot := by
  unfold elaborate at h
  cases hm : bindModel document.model with
  | error error => simp [hm, Bind.bind, Except.bind] at h
  | ok boundSchema =>
    cases hi : bindInstance document.model document.snapshot with
    | error error => simp [hm, hi, Bind.bind, Except.bind] at h
    | ok boundSnapshot =>
      have heq : (boundSchema, boundSnapshot) = (schema, snapshot) := by
        simpa [hm, hi, Bind.bind, Except.bind, pure, Except.pure] using h
      have hschema := congrArg Prod.fst heq
      have hsnapshot := congrArg Prod.snd heq
      change boundSchema = schema at hschema
      change boundSnapshot = snapshot at hsnapshot
      rw [← hschema, ← hsnapshot]
      exact ⟨rfl, rfl⟩

/-- Preservation for a concrete elaboration result, obtained by inverting
`elaborate` and applying the binding-level assembly theorem. -/
theorem snapshotConforms_of_sourceSatisfies_of_elaborate
    {document : Document} {schema : Schema} {snapshot : Snapshot}
    (hsource : SourceSatisfies document)
    (h : elaborate document = .ok (schema, snapshot)) :
    SnapshotConforms schema snapshot := by
  obtain ⟨hmodel, hinstance⟩ := elaborate_ok_bindings h
  exact snapshotConforms_of_sourceSatisfies_of_bindings hsource hmodel hinstance

/-- A satisfying source document both elaborates and is accepted by the executable
snapshot checker.  Binding completeness supplies the pair; preservation and
checker correctness supply acceptance. -/
theorem elaborate_complete_and_snapshot_accepted {document : Document}
    (hsource : SourceSatisfies document) :
    ∃ schema snapshot, elaborate document = .ok (schema, snapshot) ∧
      SnapshotConforms schema snapshot ∧ checkSnapshot schema snapshot = true := by
  obtain ⟨schema, snapshot, helaborate⟩ := elaborate_complete hsource
  have hconforms := snapshotConforms_of_sourceSatisfies_of_elaborate hsource helaborate
  exact ⟨schema, snapshot, helaborate, hconforms,
    (checkSnapshot_iff schema snapshot).mpr hconforms⟩

end VLMOF.Source
