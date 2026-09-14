import VLMOF.SnapshotConformanceCorrect

/-!
# Reflection of snapshot conformance through binding

Successful binding is injective on symbolic aliases and values.  Consequently
target conformance can be reflected to the original source snapshot once the
source declaration model is known to be well formed.  Object alias XML validity
is kept explicit because the binder checks only nonempty alias components.
-/
namespace VLMOF.Source

private theorem propertyAliases_uniqueBy {model : Model} (h : ModelWellFormed model) :
    uniqueBy Property.alias model.properties := by
  have hn := h.uniqueQualifiedAliases
  unfold uniqueAliases at hn
  simp only [aliases, List.nodup_append] at hn
  exact hn.1.1.1.2.1

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

private theorem classId_ok_iff (model : Model) (name : Name) (id : ClassId) :
    classId model name = .ok id ↔
      resolveIndex "class" (model.classes.map Class.alias) name = .ok id.val := by
  cases id with
  | mk index =>
      cases h : resolveIndex "class" (model.classes.map Class.alias) name <;>
        simp [classId, h, Except.map]

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

private theorem objectAliases_nodup_of_bindInstance {model : Model} {snapshot : Instance}
    {target : Snapshot} (hbind : bindInstance model snapshot = .ok target) :
    (snapshot.objects.map Object.alias).Nodup := by
  have hcheck := (bindInstance_ok_iff model snapshot target).mp hbind |>.1
  exact ((aliasEnvironment_iff _).mp ((checkAliases_iff _ _).mp hcheck)).1

private theorem sourceObject_target {model : Model} {snapshot : Instance}
    {target : Snapshot} (hbind : bindInstance model snapshot = .ok target)
    {sourceObject : Object} (hsource : sourceObject ∈ snapshot.objects) :
    ∃ targetObject ∈ target.objects,
      objectId snapshot sourceObject.alias = .ok targetObject.id ∧
      classId model sourceObject.classifier = .ok targetObject.classifier := by
  have hn := objectAliases_nodup_of_bindInstance hbind
  obtain ⟨index, hget⟩ := List.mem_iff_getElem?.mp hsource
  have halias : (snapshot.objects.map Object.alias)[index]? = some sourceObject.alias := by
    simp [List.getElem?_map, hget]
  have hunique := uniqueAliasAt_of_nodup hn halias
  obtain ⟨classifier, targetObject, hclassifier, htarget, hid, htc⟩ :=
    boundObject_classifierForId hbind hunique hsource rfl
  subst htc
  exact ⟨targetObject, htarget, by
    apply (objectId_ok_iff snapshot sourceObject.alias targetObject.id).mpr
    simpa [hid] using (resolveIndex_iff_uniqueAliasAt _ _ _ _).mpr hunique,
    hclassifier⟩

private theorem propertyEntry_resolves_id {model : Model} (hwell : ModelWellFormed model)
    {x : Property × Nat} {target : PropertyDecl}
    (hx : x ∈ model.properties.zipIdx)
    (hbind : bindPropertyEntry model x = .ok target) :
    propertyId model x.1.alias = .ok target.id := by
  have hget := List.mk_mem_zipIdx_iff_getElem?.mp hx
  have halias : (model.properties.map Property.alias)[x.2]? = some x.1.alias := by
    simp [List.getElem?_map, hget]
  have hresolve : resolveIndex "property" (model.properties.map Property.alias)
      x.1.alias = .ok x.2 := (resolveIndex_iff_uniqueAliasAt _ _ _ _).mpr
    (uniqueAliasAt_of_nodup (show (model.properties.map Property.alias).Nodup from
      propertyAliases_uniqueBy hwell) halias)
  unfold bindPropertyEntry at hbind
  cases hq : checkQualification x.1.alias (some (ownerName x.1.owner)) <;>
    cases ho : bindOwner model x.1.owner <;>
    cases ht : bindType model x.1.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at hbind
  subst target
  simp [propertyId, hresolve, Except.map]

private theorem bindPropertyEntry_data {model : Model} {source : Property}
    {index : Nat} {target : PropertyDecl}
    (h : bindPropertyEntry model (source, index) = .ok target) :
    bindType model source.type = .ok target.type ∧
      target.multiplicity = source.multiplicity ∧ target.isId = source.isId := by
  unfold bindPropertyEntry at h
  cases hq : checkQualification source.alias (some (ownerName source.owner)) <;>
    cases ho : bindOwner model source.owner <;>
    cases ht : bindType model source.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  exact ⟨rfl, rfl, rfl⟩

private theorem sourceProperty_target {model : Model} {schema : Schema}
    (hwell : ModelWellFormed model) (hbind : bindModel model = .ok schema)
    {sourceProperty : Property} (hsource : sourceProperty ∈ model.properties) :
    ∃ targetProperty ∈ schema.properties,
      propertyId model sourceProperty.alias = .ok targetProperty.id ∧
      bindType model sourceProperty.type = .ok targetProperty.type ∧
      targetProperty.multiplicity = sourceProperty.multiplicity ∧
      targetProperty.isId = sourceProperty.isId := by
  have allocation := modelAllocation_of_bindModel hbind
  obtain ⟨index, targetProperty, hzip, htarget, hentry⟩ :=
    allocation.propertyForSource hsource
  exact ⟨targetProperty, htarget, propertyEntry_resolves_id hwell hzip hentry,
    bindPropertyEntry_data hentry⟩

private theorem resolvesClass_of_classId {model : Model} {name : Name} {id : ClassId}
    (h : classId model name = .ok id) : resolvesClass model name := by
  have hget := resolveIndex_getElem ((classId_ok_iff model name id).mp h)
  rw [List.getElem?_map] at hget
  cases he : model.classes[id.val]? with
  | none => simp [he] at hget
  | some declaration =>
    simp [he] at hget
    intro hempty
    have hmem : declaration ∈ classEntries model name :=
      (mem_lookupAll Class.alias model.classes name declaration).mpr
        ⟨List.mem_iff_getElem?.mpr ⟨id.val, he⟩, hget⟩
    rw [show classEntries model name = [] from hempty] at hmem
    simp at hmem

private theorem bindClassEntry_isAbstract {model : Model} {source : Class}
    {index : Nat} {target : ClassDecl}
    (h : bindClassEntry model (source, index) = .ok target) :
    target.isAbstract = source.isAbstract := by
  unfold bindClassEntry at h
  cases hq : checkQualification source.alias source.package <;>
    cases hp : optionalPackage model source.package <;>
    cases hs : source.directSupers.mapM (classId model) <;>
    simp [hq, hp, hs, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  rfl

private theorem observation_key_preserved {model : Model} {snapshot : Instance}
    {first second : Source.Observation} {firstTarget secondTarget : VLMOF.Observation}
    (hfirst : bindObservationAllocation model snapshot first = .ok firstTarget)
    (hsecond : bindObservationAllocation model snapshot second = .ok secondTarget)
    (hkey : SourceObservation.key first = SourceObservation.key second) :
    VLMOF.Observation.key firstTarget = VLMOF.Observation.key secondTarget := by
  have hf := (bindObservationAllocation_ok_iff model snapshot first firstTarget).mp hfirst
  have hs := (bindObservationAllocation_ok_iff model snapshot second secondTarget).mp hsecond
  have hobject : first.object = second.object := congrArg Prod.fst hkey
  have hproperty : first.property = second.property := congrArg Prod.snd hkey
  apply Prod.ext
  · exact Except.ok.inj (hf.1.symm.trans (hobject ▸ hs.1))
  · exact Except.ok.inj (hf.2.1.symm.trans (hproperty ▸ hs.2.1))

private theorem sourceObservationKeys_nodup {model : Model} {snapshot : Instance}
    {target : Snapshot} (hbind : bindInstance model snapshot = .ok target)
    (hn : (target.observations.map VLMOF.Observation.key).Nodup) :
    (snapshot.observations.map SourceObservation.key).Nodup := by
  have aux : ∀ {sources : List Source.Observation} {targets : List VLMOF.Observation},
      sources.mapM (bindObservationAllocation model snapshot) = .ok targets →
      (targets.map VLMOF.Observation.key).Nodup →
      (sources.map SourceObservation.key).Nodup := by
    intro sources
    induction sources with
    | nil => intro targets _ _; simp
    | cons first rest ih =>
      intro targets hmap htargets
      obtain ⟨firstTarget, tailTargets, heq, hfirst, hrest⟩ := mapM_ok_cons hmap
      subst targets
      simp only [List.map_cons, List.nodup_cons] at htargets ⊢
      refine ⟨?_, ih hrest htargets.2⟩
      intro hmem
      obtain ⟨second, hsecond, hkey⟩ := List.mem_map.mp hmem
      obtain ⟨secondTarget, hsecondTarget, hsecondBind⟩ := mapM_ok_source hrest hsecond
      apply htargets.1
      exact List.mem_map.mpr ⟨secondTarget, hsecondTarget,
        (observation_key_preserved (first := first) (second := second)
          hfirst hsecondBind hkey.symm).symm⟩
  exact aux (bindInstance_ok_mapM hbind).2 hn

private theorem sourceObservation_target {model : Model} {snapshot : Instance}
    {target : Snapshot} (hbind : bindInstance model snapshot = .ok target)
    {sourceObservation : Source.Observation}
    (hsource : sourceObservation ∈ snapshot.observations) :
    ∃ targetObservation ∈ target.observations,
      objectId snapshot sourceObservation.object = .ok targetObservation.object ∧
      propertyId model sourceObservation.property = .ok targetObservation.property ∧
      OccurrencesBind model snapshot sourceObservation.occurrences targetObservation.occurrences := by
  obtain ⟨targetObservation, htarget, hentry⟩ :=
    mapM_ok_source (bindInstance_ok_mapM hbind).2 hsource
  exact ⟨targetObservation, htarget,
    (bindObservationAllocation_ok_iff model snapshot sourceObservation targetObservation).mp hentry⟩

private theorem sourceObservation_exists_iff {model : Model} {snapshot : Instance}
    {target : Snapshot} (hbind : bindInstance model snapshot = .ok target)
    {objectName propertyName : Name} {objectTarget : ObjectId} {propertyTarget : PropertyId}
    (hobject : objectId snapshot objectName = .ok objectTarget)
    (hproperty : propertyId model propertyName = .ok propertyTarget) :
    (∃ sourceObservation ∈ snapshot.observations,
      sourceObservation.object = objectName ∧ sourceObservation.property = propertyName) ↔
    ∃ observation ∈ target.observations,
      observation.object = objectTarget ∧ observation.property = propertyTarget := by
  constructor
  · rintro ⟨sourceObservation, hsourceObservation, ho, hp⟩
    obtain ⟨observation, hobservation, hso, hsp, _⟩ :=
      sourceObservation_target hbind hsourceObservation
    exact ⟨observation, hobservation, Except.ok.inj (hso.symm.trans (ho ▸ hobject)),
      Except.ok.inj (hsp.symm.trans (hp ▸ hproperty))⟩
  · rintro ⟨observation, hobservation, ho, hp⟩
    obtain ⟨sourceObservation, hsourceObservation, hso, hsp, _⟩ :=
      boundObservation_source hbind hobservation
    exact ⟨sourceObservation, hsourceObservation,
      objectId_source_injective hso (by simpa [ho] using hobject),
      propertyId_source_injective hsp (by simpa [hp] using hproperty)⟩

private theorem classAliases_uniqueBy {model : Model} (h : ModelWellFormed model) :
    uniqueBy Class.alias model.classes := by
  have hn := h.uniqueQualifiedAliases
  unfold uniqueAliases at hn
  simp only [aliases, List.nodup_append] at hn
  exact hn.1.1.1.1.2.1

theorem source_classifiersResolved_of_snapshotConforms
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hinstance : bindInstance model source = .ok target) :
    ∀ object ∈ source.objects, resolvesClass model object.classifier := by
  intro object hobject
  obtain ⟨targetObject, _, _, hclassifier⟩ := sourceObject_target hinstance hobject
  exact resolvesClass_of_classId hclassifier

theorem source_concreteClassifiers_of_snapshotConforms
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    (hconforms : SnapshotConforms schema target) :
    ∀ object ∈ source.objects, ∀ declaration ∈ model.classes,
      declaration.alias = object.classifier → declaration.isAbstract = false := by
  intro object hobject declaration hdeclaration halias
  obtain ⟨targetObject, htargetObject, _, hclassifier⟩ :=
    sourceObject_target hinstance hobject
  obtain ⟨allocatedSource, targetClass, hallocatedSource, hallocatedAlias,
    htargetClass, htargetClassId, hclassBind⟩ :=
      (modelAllocation_of_bindModel hmodel).classForId hclassifier
  have hsame : allocatedSource = declaration := by
    apply uniqueBy_eq_of_mem Class.alias (classAliases_uniqueBy hwell)
      hallocatedSource hdeclaration
    exact hallocatedAlias.trans halias.symm
  subst allocatedSource
  rw [← bindClassEntry_isAbstract hclassBind]
  exact hconforms.concreteClassifiers targetObject htargetObject targetClass htargetClass
    htargetClassId

theorem source_observationsExact_of_snapshotConforms
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    (hconforms : SnapshotConforms schema target) :
    ∀ object ∈ source.objects, ∀ property ∈ model.properties,
      (∃ observation ∈ source.observations,
        observation.object = object.alias ∧ observation.property = property.alias) ↔
        propertyApplies model object.classifier property.alias := by
  intro object hobject property hproperty
  obtain ⟨targetObject, htargetObject, hobjectId, hclassifier⟩ :=
    sourceObject_target hinstance hobject
  obtain ⟨targetProperty, htargetProperty, hpropertyId, _, _, _⟩ :=
    sourceProperty_target hwell hmodel hproperty
  rw [sourceObservation_exists_iff hinstance hobjectId hpropertyId]
  rw [hconforms.observationsExact targetObject htargetObject targetProperty htargetProperty]
  exact (propertyApplies_iff_applicableProperty hwell hmodel hclassifier hpropertyId).symm

private theorem sourceObject_of_objectId {snapshot : Instance} {name : Name} {id : ObjectId}
    (h : objectId snapshot name = .ok id) :
    ∃ object ∈ snapshot.objects, object.alias = name := by
  have hget := resolveIndex_getElem ((objectId_ok_iff snapshot name id).mp h)
  rw [List.getElem?_map] at hget
  cases he : snapshot.objects[id.val]? with
  | none => simp [he] at hget
  | some object =>
    simp [he] at hget
    exact ⟨object, List.mem_iff_getElem?.mpr ⟨id.val, he⟩, hget⟩

private theorem sourceProperty_of_propertyId {model : Model} {name : Name} {id : PropertyId}
    (h : propertyId model name = .ok id) :
    ∃ property ∈ model.properties, property.alias = name := by
  have hget := resolveIndex_getElem ((propertyId_ok_iff model name id).mp h)
  rw [List.getElem?_map] at hget
  cases he : model.properties[id.val]? with
  | none => simp [he] at hget
  | some property =>
    simp [he] at hget
    exact ⟨property, List.mem_iff_getElem?.mpr ⟨id.val, he⟩, hget⟩

theorem source_observationKeysResolved_of_binding
    {model : Model} {source : Instance} {target : Snapshot}
    (hinstance : bindInstance model source = .ok target) :
    ∀ observation ∈ source.observations,
      (∃ object ∈ source.objects, object.alias = observation.object) ∧
      (∃ property ∈ model.properties, property.alias = observation.property) := by
  intro observation hobservation
  obtain ⟨_, _, hobject, hproperty, _⟩ :=
    sourceObservation_target hinstance hobservation
  exact ⟨sourceObject_of_objectId hobject, sourceProperty_of_propertyId hproperty⟩

theorem source_observationApplicable_of_snapshotConforms
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    (hconforms : SnapshotConforms schema target) :
    ∀ observation ∈ source.observations, ∀ object ∈ source.objects,
      object.alias = observation.object →
        propertyApplies model object.classifier observation.property := by
  intro observation hobservation object hobject hkey
  obtain ⟨targetObservation, htargetObservation, hobservationObject,
    hobservationProperty, _⟩ := sourceObservation_target hinstance hobservation
  obtain ⟨targetObject, htargetObject, hobjectId, hclassifier⟩ :=
    sourceObject_target hinstance hobject
  have htargetKey : targetObject.id = targetObservation.object := by
    apply Except.ok.inj
    exact hobjectId.symm.trans (hkey ▸ hobservationObject)
  have happlicable := hconforms.observationApplicable targetObservation
    htargetObservation targetObject htargetObject htargetKey
  exact (propertyApplies_iff_applicableProperty hwell hmodel
    hclassifier hobservationProperty).mpr happlicable

theorem source_bounds_of_snapshotConforms
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    (hconforms : SnapshotConforms schema target) :
    ∀ object ∈ source.objects, ∀ property ∈ model.properties,
      propertyApplies model object.classifier property.alias →
        withinMultiplicity property.multiplicity
          (sourceOccurrences source object.alias property.alias).length := by
  intro object hobject property hproperty happlies
  obtain ⟨targetObject, htargetObject, hobjectId, hclassifier⟩ :=
    sourceObject_target hinstance hobject
  obtain ⟨targetProperty, htargetProperty, hpropertyId, _, hmultiplicity, _⟩ :=
    sourceProperty_target hwell hmodel hproperty
  have htargetApplies := (propertyApplies_iff_applicableProperty hwell hmodel
    hclassifier hpropertyId).mp happlies
  have hbound := hconforms.bounds targetObject htargetObject targetProperty
    htargetProperty htargetApplies
  rw [hmultiplicity] at hbound
  rw [← bindInstance_occurrences_length_eq hinstance hobjectId hpropertyId] at hbound
  exact hbound

theorem source_uniqueness_of_snapshotConforms
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    (hconforms : SnapshotConforms schema target) :
    ∀ object ∈ source.objects, ∀ property ∈ model.properties,
      propertyApplies model object.classifier property.alias →
      property.multiplicity.isUnique = true →
        (sourceOccurrences source object.alias property.alias).Nodup := by
  intro object hobject property hproperty happlies hunique
  obtain ⟨targetObject, htargetObject, hobjectId, hclassifier⟩ :=
    sourceObject_target hinstance hobject
  obtain ⟨targetProperty, htargetProperty, hpropertyId, _, hmultiplicity, _⟩ :=
    sourceProperty_target hwell hmodel hproperty
  have htargetApplies := (propertyApplies_iff_applicableProperty hwell hmodel
    hclassifier hpropertyId).mp happlies
  have htargetUnique : targetProperty.multiplicity.isUnique = true := by
    simpa [hmultiplicity] using hunique
  apply (bindInstance_occurrences_nodup_iff hinstance hobjectId hpropertyId).mpr
  exact hconforms.uniqueness targetObject htargetObject targetProperty htargetProperty
    htargetApplies htargetUnique

private theorem enumerationId_of_uniqueAliasAt {model : Model} {name : Name}
    {id : EnumerationId}
    (h : UniqueAliasAt (model.enumerations.map Enumeration.alias) name id.val) :
    enumerationId model name = .ok id := by
  have hr : resolveIndex "enumeration" (model.enumerations.map Enumeration.alias)
      name = .ok id.val := (resolveIndex_iff_uniqueAliasAt _ _ _ _).mpr h
  cases id
  simp [enumerationId, hr, Except.map]

private theorem literalId_of_uniqueAliasAt {model : Model} {name : Name}
    {id : LiteralId}
    (h : UniqueAliasAt (model.literals.map Literal.alias) name id.val) :
    literalId model name = .ok id := by
  have hr : resolveIndex "literal" (model.literals.map Literal.alias)
      name = .ok id.val := (resolveIndex_iff_uniqueAliasAt _ _ _ _).mpr h
  cases id
  simp [literalId, hr, Except.map]

private theorem classAliasAt_of_classId {model : Model} {name : Name} {id : ClassId}
    (h : classId model name = .ok id) : ClassAliasAt model id name :=
  resolveIndex_getElem ((classId_ok_iff model name id).mp h)

private theorem bindLiteralEntry_enumeration {model : Model} {source : Literal}
    {index : Nat} {target : LiteralDecl}
    (h : bindLiteralEntry model (source, index) = .ok target) :
    enumerationId model source.enumeration = .ok target.enumeration := by
  unfold bindLiteralEntry at h
  cases hq : checkQualification source.alias (some source.enumeration) <;>
    cases he : enumerationId model source.enumeration <;>
    simp [hq, he, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  exact rfl

private theorem sourceObject_of_uniqueAliasAt {snapshot : Instance} {name : Name}
    {id : ObjectId}
    (h : UniqueAliasAt (snapshot.objects.map Object.alias) name id.val) :
    ∃ object ∈ snapshot.objects, object.alias = name := by
  have hget := h.1
  rw [List.getElem?_map] at hget
  cases he : snapshot.objects[id.val]? with
  | none => simp [he] at hget
  | some object =>
    simp [he] at hget
    exact ⟨object, List.mem_iff_getElem?.mpr ⟨id.val, he⟩, hget⟩

private theorem enumerationId_ok_iff (model : Model) (name : Name) (id : EnumerationId) :
    enumerationId model name = .ok id ↔
      resolveIndex "enumeration" (model.enumerations.map Enumeration.alias) name = .ok id.val := by
  cases id with
  | mk index =>
    cases h : resolveIndex "enumeration" (model.enumerations.map Enumeration.alias) name <;>
      simp [enumerationId, h, Except.map]

/-- Target value typing reflects to source value typing under the same successful
type and value bindings.  Reference subtyping is reflected through the allocated
class graph; enumeration literals are recovered through unique target IDs. -/
theorem valueMatches_to_sourceValueMatches
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    (hconforms : SnapshotConforms schema target)
    {sourceType : Source.ValueType} {targetType : VLMOF.ValueType}
    {sourceValue : Source.Value} {targetValue : VLMOF.Value}
    (htype : bindType model sourceType = .ok targetType)
    (hvalue : ValueBinds model source sourceValue targetValue)
    (htarget : valueMatches schema target targetType targetValue) :
    sourceValueMatches model source sourceType sourceValue := by
  cases sourceType with
  | boolean =>
    cases sourceValue <;> cases targetType <;> cases targetValue <;>
      simp_all [bindType, ValueBinds, valueMatches, sourceValueMatches,
        pure, Except.pure]
  | integer =>
    cases sourceValue <;> cases targetType <;> cases targetValue <;>
      simp_all [bindType, ValueBinds, valueMatches, sourceValueMatches,
        pure, Except.pure]
  | string =>
    cases sourceValue <;> cases targetType <;> cases targetValue <;>
      simp_all [bindType, ValueBinds, valueMatches, sourceValueMatches,
        pure, Except.pure]
  | enumeration expected =>
    cases he : enumerationId model expected with
    | error error => simp [bindType, he, Functor.map, Except.map] at htype
    | ok expectedId =>
      have htt : targetType = .enumeration expectedId := by
        apply Except.ok.inj
        exact htype.symm.trans (by simp [bindType, he, Functor.map, Except.map])
      subst targetType
      cases sourceValue with
      | boolean value => cases targetValue <;> simp [ValueBinds, valueMatches] at hvalue htarget
      | integer value => cases targetValue <;> simp [ValueBinds, valueMatches] at hvalue htarget
      | string value => cases targetValue <;> simp [ValueBinds, valueMatches] at hvalue htarget
      | reference value => cases targetValue <;> simp [ValueBinds, valueMatches] at hvalue htarget
      | enumeration actual literal =>
        cases targetValue with
        | boolean _ => simp [ValueBinds] at hvalue
        | integer _ => simp [ValueBinds] at hvalue
        | string _ => simp [ValueBinds] at hvalue
        | reference _ => simp [ValueBinds] at hvalue
        | enumeration actualId literalId' =>
          rcases htarget with ⟨henumIds, targetLiteral, htargetLiteral,
            htargetLiteralId, htargetEnumeration⟩
          have hactual := enumerationId_of_uniqueAliasAt hvalue.1
          have hname : expected = actual := by
            exact resolveIndex_injective
              ((enumerationId_ok_iff model expected expectedId).mp he)
              ((enumerationId_ok_iff model actual expectedId).mp
                (by simpa [henumIds] using hactual))
          have hliteral := literalId_of_uniqueAliasAt hvalue.2
          obtain ⟨sourceLiteral, allocatedLiteral, hsourceLiteral, hsourceAlias,
            hallocatedLiteral, hallocatedLiteralId, hliteralBind⟩ :=
              (modelAllocation_of_bindModel hmodel).literalForId hliteral
          have hsameLiteral : targetLiteral = allocatedLiteral := by
            apply uniqueBy_eq_of_mem LiteralDecl.id
              (modelAllocation_of_bindModel hmodel).uniqueIds.2.2.2.2.2
              htargetLiteral hallocatedLiteral
            exact htargetLiteralId.trans hallocatedLiteralId.symm
          subst targetLiteral
          have hsourceEnumeration := bindLiteralEntry_enumeration hliteralBind
          have hsourceEnumName : sourceLiteral.enumeration = expected := by
            apply resolveIndex_injective
            · apply (enumerationId_ok_iff model sourceLiteral.enumeration expectedId).mp
              simpa [htargetEnumeration] using hsourceEnumeration
            · exact (enumerationId_ok_iff model expected expectedId).mp he
          exact ⟨hname, sourceLiteral, hsourceLiteral, hsourceAlias,
            hsourceEnumName⟩
  | reference expected =>
    cases hc : classId model expected with
    | error error => simp [bindType, hc, Functor.map, Except.map] at htype
    | ok expectedId =>
      have htt : targetType = .reference expectedId := by
        apply Except.ok.inj
        exact htype.symm.trans (by simp [bindType, hc, Functor.map, Except.map])
      subst targetType
      cases sourceValue with
      | boolean value => cases targetValue <;> simp [ValueBinds, valueMatches] at hvalue htarget
      | integer value => cases targetValue <;> simp [ValueBinds, valueMatches] at hvalue htarget
      | string value => cases targetValue <;> simp [ValueBinds, valueMatches] at hvalue htarget
      | enumeration enum lit => cases targetValue <;> simp [ValueBinds, valueMatches] at hvalue htarget
      | reference objectName =>
        cases targetValue with
        | boolean _ => simp [ValueBinds] at hvalue
        | integer _ => simp [ValueBinds] at hvalue
        | string _ => simp [ValueBinds] at hvalue
        | enumeration _ _ => simp [ValueBinds] at hvalue
        | reference objectId' =>
          rcases htarget with ⟨targetObject, htargetObject, htargetId, hsubtype⟩
          obtain ⟨sourceObject, hsourceObject, hsourceAlias⟩ :=
            sourceObject_of_uniqueAliasAt hvalue
          obtain ⟨allocatedObject, hallocatedObject, hobjectId, hclassifier⟩ :=
            sourceObject_target hinstance hsourceObject
          have hsameObject : targetObject = allocatedObject := by
            apply uniqueBy_eq_of_mem ObjectDecl.id hconforms.uniqueObjectIds
              htargetObject hallocatedObject
            have hboundObjectId : objectId source objectName = .ok objectId' := by
              apply (objectId_ok_iff source objectName objectId').mpr
              exact (resolveIndex_iff_uniqueAliasAt _ _ _ _).mpr hvalue
            exact htargetId.trans (Except.ok.inj
              (hboundObjectId.symm.trans (hsourceAlias ▸ hobjectId)))
          subst targetObject
          exact ⟨sourceObject, hsourceObject, hsourceAlias,
            isSubtype_to_classAncestor hwell (modelAllocation_of_bindModel hmodel)
              hsubtype (classAliasAt_of_classId hclassifier)
              (classAliasAt_of_classId hc)⟩

theorem source_valuesTyped_of_snapshotConforms
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    (hconforms : SnapshotConforms schema target) :
    ∀ observation ∈ source.observations, ∀ property ∈ model.properties,
      property.alias = observation.property → ∀ value ∈ observation.occurrences,
        sourceValueMatches model source property.type value := by
  intro observation hobservation property hproperty halias value hvalue
  obtain ⟨targetObservation, htargetObservation, _, hobservationProperty,
    hoccurrences⟩ := sourceObservation_target hinstance hobservation
  obtain ⟨targetProperty, htargetProperty, hpropertyId, htype, _, _⟩ :=
    sourceProperty_target hwell hmodel hproperty
  have htargetPropertyId : targetProperty.id = targetObservation.property := by
    apply Except.ok.inj
    exact hpropertyId.symm.trans (halias ▸ hobservationProperty)
  obtain ⟨targetValue, htargetValue, hvalueBind⟩ :=
    hoccurrences.source_covered value hvalue
  exact valueMatches_to_sourceValueMatches hwell hmodel hinstance hconforms htype
    hvalueBind (hconforms.valuesTyped targetObservation htargetObservation targetProperty
      htargetProperty htargetPropertyId targetValue htargetValue)

private theorem bindAssociationEntry_ends {model : Model} {source : Association}
    {index : Nat} {target : AssociationDecl}
    (h : bindAssociationEntry model (source, index) = .ok target) :
    ∃ first second firstId secondId,
      source.ends = [first, second] ∧ propertyId model first = .ok firstId ∧
      propertyId model second = .ok secondId ∧ target.ends = (firstId, secondId) := by
  unfold bindAssociationEntry at h
  cases hq : checkQualification source.alias source.package <;>
    cases hp : optionalPackage model source.package <;>
    cases hend : source.ends with
    | nil => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at h
    | cons first rest =>
      cases rest with
      | nil => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at h
      | cons second tail =>
        cases tail with
        | cons third tail =>
          simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at h
        | nil =>
          cases hf : propertyId model first with
          | error error => simp [hq, hp, hend, hf, Bind.bind, Except.bind] at h
          | ok firstId =>
            cases hs : propertyId model second with
            | error error => simp [hq, hp, hend, hf, hs, Bind.bind, Except.bind] at h
            | ok secondId =>
              simp [hq, hp, hend, hf, hs, Bind.bind, Except.bind,
                pure, Except.pure] at h
              all_goals try subst target
              all_goals exact ⟨first, second, firstId, secondId, rfl, hf, hs, rfl⟩

private theorem referenceValueBinds_of_objectId {model : Model} {source : Instance}
    {name : Name} {id : ObjectId} (h : objectId source name = .ok id) :
    ValueBinds model source (.reference name) (.reference id) := by
  exact (resolveIndex_iff_uniqueAliasAt _ _ _ _).mp
    ((objectId_ok_iff source name id).mp h)

theorem source_oppositeCounts_of_snapshotConforms
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    (hconforms : SnapshotConforms schema target) :
    ∀ association ∈ model.associations, ∀ first second,
      association.ends = [first, second] →
      ∀ firstObject ∈ source.objects, ∀ secondObject ∈ source.objects,
      (sourceOccurrences source firstObject.alias first).count (.reference secondObject.alias) =
      (sourceOccurrences source secondObject.alias second).count (.reference firstObject.alias) := by
  intro association hassociation first second hends firstObject hfirstObject
    secondObject hsecondObject
  have allocation := modelAllocation_of_bindModel hmodel
  obtain ⟨index, hget⟩ := List.mem_iff_getElem?.mp hassociation
  have hzip : (association, index) ∈ model.associations.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hget
  obtain ⟨targetAssociation, htargetAssociation, hassociationBind⟩ :=
    mapM_ok_source allocation.associations hzip
  obtain ⟨boundFirst, boundSecond, firstId, secondId, hboundEnds,
    hfirstId, hsecondId, htargetEnds⟩ := bindAssociationEntry_ends hassociationBind
  have hfirstName : boundFirst = first := by
    have h : first = boundFirst := by
      simpa [hends] using congrArg List.head? hboundEnds
    exact h.symm
  have hsecondName : boundSecond = second := by
    have h : second = boundSecond := by
      simpa [hends] using congrArg (fun xs => (xs.drop 1).head?) hboundEnds
    exact h.symm
  subst boundFirst
  subst boundSecond
  obtain ⟨targetFirst, htargetFirst, hfirstObjectId, _⟩ :=
    sourceObject_target hinstance hfirstObject
  obtain ⟨targetSecond, htargetSecond, hsecondObjectId, _⟩ :=
    sourceObject_target hinstance hsecondObject
  have hleft := bindInstance_occurrences_count_eq hinstance hfirstObjectId hfirstId
    (referenceValueBinds_of_objectId hsecondObjectId)
  have hright := bindInstance_occurrences_count_eq hinstance hsecondObjectId hsecondId
    (referenceValueBinds_of_objectId hfirstObjectId)
  calc
    (sourceOccurrences source firstObject.alias first).count (.reference secondObject.alias) =
        (target.occurrences targetFirst.id firstId).count (.reference targetSecond.id) := hleft
    _ = (target.occurrences targetSecond.id secondId).count (.reference targetFirst.id) :=
      hconforms.oppositeCounts targetAssociation htargetAssociation firstId secondId
        htargetEnds targetFirst htargetFirst targetSecond htargetSecond
    _ = (sourceOccurrences source secondObject.alias second).count
        (.reference firstObject.alias) := hright.symm

private theorem bindPropertyEntry_aggregation {model : Model} {source : Property}
    {index : Nat} {target : PropertyDecl}
    (h : bindPropertyEntry model (source, index) = .ok target) :
    target.aggregation = source.aggregation := by
  unfold bindPropertyEntry at h
  cases hq : checkQualification source.alias (some (ownerName source.owner)) <;>
    cases ho : bindOwner model source.owner <;>
    cases ht : bindType model source.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  rfl

private theorem compositeTest_eq {model : Model} {schema : Schema}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    {sourceObservation : Source.Observation} {targetObservation : VLMOF.Observation}
    (hproperty : propertyId model sourceObservation.property = .ok targetObservation.property) :
    (model.properties.any fun p =>
      p.alias = sourceObservation.property && p.aggregation = .composite) =
    (schema.properties.any fun p =>
      p.id = targetObservation.property ∧ p.aggregation = .composite) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨property, hp, halias, haggregation⟩
    obtain ⟨index, targetProperty, hzip, htargetProperty, hbind⟩ :=
      (modelAllocation_of_bindModel hmodel).propertyForSource hp
    have hpid := propertyEntry_resolves_id hwell hzip hbind
    exact ⟨targetProperty, htargetProperty,
      Except.ok.inj (hpid.symm.trans (halias ▸ hproperty)),
      (bindPropertyEntry_aggregation hbind).trans haggregation⟩
  · rintro ⟨targetProperty, htargetProperty, hid, haggregation⟩
    obtain ⟨entry, hentry, hbind⟩ :=
      (mapM_ok_mem_iff (modelAllocation_of_bindModel hmodel).properties).mp htargetProperty
    have hsource := List.fst_mem_of_mem_zipIdx hentry
    have hpid := propertyEntry_resolves_id hwell hentry hbind
    have halias : entry.1.alias = sourceObservation.property :=
      propertyId_source_injective hpid (by simpa [hid] using hproperty)
    exact ⟨entry.1, hsource, halias,
      (bindPropertyEntry_aggregation hbind).symm.trans haggregation⟩

private theorem referenceFilter_length_eq {model : Model} {source : Instance}
    {sourceValues : List Source.Value} {targetValues : List VLMOF.Value}
    (hocc : OccurrencesBind model source sourceValues targetValues)
    {name : Name} {id : ObjectId} (hid : objectId source name = .ok id) :
    (sourceValues.filter (fun v => v = .reference name)).length =
      (targetValues.filter (fun v => v = .reference id)).length := by
  have hv := referenceValueBinds_of_objectId (model := model) hid
  induction sourceValues generalizing targetValues with
  | nil => cases targetValues <;> simp_all [OccurrencesBind]
  | cons first rest ih =>
    cases targetValues with
    | nil => simp [OccurrencesBind] at hocc
    | cons translated translatedRest =>
      simp only [OccurrencesBind] at hocc
      have htail := ih hocc.2
      cases first <;> cases translated <;> simp_all [ValueBinds]
      case reference.reference sourceObject targetObject =>
        by_cases hn : sourceObject = name
        · have ht : targetObject = id := by
            have hval : targetObject.val = id.val :=
              (hocc.1.2 id.val (by simpa [hn] using hv.1)).symm
            cases targetObject
            cases id
            simp_all
          simp [hn, ht, htail]
        · have ht : targetObject ≠ id := fun heq =>
            hn (Option.some.inj (hocc.1.1.symm.trans (heq ▸ hv.1)))
          simp [hn, ht, htail]

private theorem incomingCompositeCount_mapM {model : Model} {source : Instance}
    {schema : Schema} (hwell : ModelWellFormed model)
    (hmodel : bindModel model = .ok schema)
    {sources : List Source.Observation} {targets : List VLMOF.Observation}
    (hmap : sources.mapM (bindObservationAllocation model source) = .ok targets)
    {targetName : Name} {targetId : ObjectId}
    (hid : objectId source targetName = .ok targetId) :
    (sources.flatMap fun observation =>
      if model.properties.any (fun p =>
        p.alias = observation.property && p.aggregation = .composite)
      then observation.occurrences.filter (fun v => v = .reference targetName) else []).length =
    (targets.flatMap fun observation =>
      if schema.properties.any (fun p =>
        p.id = observation.property ∧ p.aggregation = .composite)
      then observation.occurrences.filter (fun v => v = .reference targetId) else []).length := by
  induction sources generalizing targets with
  | nil =>
    change Except.ok [] = Except.ok targets at hmap
    cases targets with
    | nil => simp
    | cons first rest => simp at hmap
  | cons first rest ih =>
    obtain ⟨translated, translatedRest, rfl, hfirst, hrest⟩ := mapM_ok_cons hmap
    have hfacts :=
      (bindObservationAllocation_ok_iff model source first translated).mp hfirst
    have htest := compositeTest_eq hwell hmodel hfacts.2.1
    have hcount := referenceFilter_length_eq hfacts.2.2 hid
    simp only [List.flatMap_cons, List.length_append]
    have htail := ih hrest
    rw [htest]
    by_cases hc : schema.properties.any (fun p =>
        p.id = translated.property ∧ p.aggregation = .composite) = true
    · simp only [hc, if_true]
      omega
    · have hf : schema.properties.any (fun p =>
          p.id = translated.property ∧ p.aggregation = .composite) = false := by
        cases hv : schema.properties.any (fun p =>
          p.id = translated.property ∧ p.aggregation = .composite)
        · rfl
        · exact False.elim (hc hv)
      simp only [hf, Bool.false_eq_true, if_false]
      omega

private theorem incomingCompositeCount_reflect_eq {model : Model} {source : Instance}
    {schema : Schema} {target : Snapshot} (hwell : ModelWellFormed model)
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    {name : Name} {id : ObjectId} (hid : objectId source name = .ok id) :
    incomingCompositeCount model source name = VLMOF.incomingCompositeCount schema target id := by
  unfold Source.incomingCompositeCount VLMOF.incomingCompositeCount
  exact incomingCompositeCount_mapM hwell hmodel (bindInstance_ok_mapM hinstance).2 hid

theorem source_oneIncomingComposite_of_snapshotConforms
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    (hconforms : SnapshotConforms schema target) :
    ∀ object ∈ source.objects, incomingCompositeCount model source object.alias ≤ 1 := by
  intro object hobject
  obtain ⟨targetObject, htargetObject, hobjectId, _⟩ :=
    sourceObject_target hinstance hobject
  rw [incomingCompositeCount_reflect_eq hwell hmodel hinstance hobjectId]
  exact hconforms.oneIncomingComposite targetObject htargetObject

private theorem sourceCompositeEdge_ids
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    {sourceName targetName : Name}
    (hedge : sourceCompositeEdge model source sourceName targetName) :
    ∃ sourceId targetId,
      objectId source sourceName = .ok sourceId ∧
      objectId source targetName = .ok targetId ∧
      compositeEdge schema target sourceId targetId := by
  have hedgeOriginal := hedge
  obtain ⟨observation, hobservation, hsourceName, hreference, _, _, _, _⟩ := hedge
  obtain ⟨targetObservation, _, hobjectId, _, hoccurrences⟩ :=
    sourceObservation_target hinstance hobservation
  obtain ⟨targetValue, _, hvalue⟩ :=
    hoccurrences.source_covered (.reference targetName) hreference
  cases targetValue with
  | boolean value => simp [ValueBinds] at hvalue
  | integer value => simp [ValueBinds] at hvalue
  | string value => simp [ValueBinds] at hvalue
  | enumeration enumeration literal => simp [ValueBinds] at hvalue
  | reference targetId =>
    have htargetId : objectId source targetName = .ok targetId := by
      apply (objectId_ok_iff source targetName targetId).mpr
      exact (resolveIndex_iff_uniqueAliasAt _ _ _ _).mpr hvalue
    have hsourceId : objectId source sourceName = .ok targetObservation.object := by
      simpa [hsourceName] using hobjectId
    exact ⟨targetObservation.object, targetId, hsourceId, htargetId,
      (sourceCompositeEdge_iff_compositeEdge hwell hmodel hinstance
        hsourceId htargetId).mp hedgeOriginal⟩

private theorem sourceCompositeReachable_to_storedPath
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    {sourceName targetName : Name}
    (hreach : SourceCompositeReachable model source sourceName targetName)
    {sourceId targetId : ObjectId}
    (hsourceId : objectId source sourceName = .ok sourceId)
    (htargetId : objectId source targetName = .ok targetId) :
    StoredPath (compositeEdge schema target) sourceId targetId := by
  induction hreach generalizing sourceId targetId with
  | refl =>
    have hid : sourceId = targetId := Except.ok.inj (hsourceId.symm.trans htargetId)
    subst targetId
    exact .refl sourceId
  | @step middle finish hprefix hedge ih =>
    obtain ⟨middleId, finishId, hmiddleId, hfinishId, htargetEdge⟩ :=
      sourceCompositeEdge_ids hwell hmodel hinstance hedge
    have hprefixTarget := ih hsourceId hmiddleId
    have hfinish : finishId = targetId :=
      Except.ok.inj (hfinishId.symm.trans htargetId)
    subst finishId
    exact .step hprefixTarget htargetEdge

theorem source_containmentAcyclic_of_snapshotConforms
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    (hconforms : SnapshotConforms schema target) :
    ∀ object ∈ source.objects, ∀ child,
      sourceCompositeEdge model source object.alias child →
      ¬ SourceCompositeReachable model source child object.alias := by
  intro object hobject child hedge hcycle
  obtain ⟨targetObject, htargetObject, hobjectId, _⟩ :=
    sourceObject_target hinstance hobject
  obtain ⟨sourceId, childId, hsourceId, hchildId, htargetEdge⟩ :=
    sourceCompositeEdge_ids hwell hmodel hinstance hedge
  have hsourceEq : sourceId = targetObject.id :=
    Except.ok.inj (hsourceId.symm.trans hobjectId)
  subst sourceId
  have hpath := sourceCompositeReachable_to_storedPath hwell hmodel hinstance
    hcycle hchildId hobjectId
  have hreachable : compositeReachable schema target childId targetObject.id :=
    (hconforms.compositeReachable_iff_path
      (hconforms.compositeTargetsResolved htargetEdge)).mpr hpath
  exact hconforms.containmentAcyclic targetObject htargetObject childId
    htargetEdge hreachable

/-- Full source snapshot satisfaction reflects from target conformance.  The
source model is explicit because schema adequacy is a separate reverse theorem;
object XML-name validity is explicit because binding checks only empty parts. -/
theorem sourceSatisfies_of_snapshotConforms_of_bindings
    {model : Model} {source : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model)
    (hobjectNames : ∀ object ∈ source.objects, NameValid object.alias)
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model source = .ok target)
    (hconforms : SnapshotConforms schema target) :
    SourceSatisfies { model, snapshot := source } := by
  exact {
    model := hwell
    uniqueObjectAliases := objectAliases_nodup_of_bindInstance hinstance
    objectAliasesValid := hobjectNames
    classifiersResolved := source_classifiersResolved_of_snapshotConforms
      (schema := schema) hinstance
    concreteClassifiers := source_concreteClassifiers_of_snapshotConforms
      hwell hmodel hinstance hconforms
    uniqueObservationKeys := sourceObservationKeys_nodup hinstance
      hconforms.uniqueObservationKeys
    observationsExact := source_observationsExact_of_snapshotConforms
      hwell hmodel hinstance hconforms
    observationKeysResolved := source_observationKeysResolved_of_binding hinstance
    observationApplicable := source_observationApplicable_of_snapshotConforms
      hwell hmodel hinstance hconforms
    valuesTyped := source_valuesTyped_of_snapshotConforms
      hwell hmodel hinstance hconforms
    bounds := source_bounds_of_snapshotConforms hwell hmodel hinstance hconforms
    uniqueness := source_uniqueness_of_snapshotConforms hwell hmodel hinstance hconforms
    oppositeCounts := source_oppositeCounts_of_snapshotConforms hmodel hinstance hconforms
    oneIncomingComposite := source_oneIncomingComposite_of_snapshotConforms
      hwell hmodel hinstance hconforms
    containmentAcyclic := source_containmentAcyclic_of_snapshotConforms
      hwell hmodel hinstance hconforms
  }

private theorem elaborate_ok_bindings {document : Document} {schema : Schema}
    {target : Snapshot} (h : elaborate document = .ok (schema, target)) :
    bindModel document.model = .ok schema ∧
      bindInstance document.model document.snapshot = .ok target := by
  unfold elaborate at h
  cases hm : bindModel document.model with
  | error error => simp [hm, Bind.bind, Except.bind] at h
  | ok boundSchema =>
    cases hi : bindInstance document.model document.snapshot with
    | error error => simp [hm, hi, Bind.bind, Except.bind] at h
    | ok boundTarget =>
      have heq : (boundSchema, boundTarget) = (schema, target) := by
        simpa [hm, hi, Bind.bind, Except.bind, pure, Except.pure] using h
      have hs := congrArg Prod.fst heq
      have ht := congrArg Prod.snd heq
      change boundSchema = schema at hs
      change boundTarget = target at ht
      rw [← hs, ← ht]
      exact ⟨rfl, rfl⟩

theorem sourceSatisfies_of_snapshotConforms_of_elaborate
    {document : Document} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed document.model)
    (hobjectNames : ∀ object ∈ document.snapshot.objects, NameValid object.alias)
    (helaborate : elaborate document = .ok (schema, target))
    (hconforms : SnapshotConforms schema target) :
    SourceSatisfies document := by
  obtain ⟨hmodel, hinstance⟩ := elaborate_ok_bindings helaborate
  exact sourceSatisfies_of_snapshotConforms_of_bindings hwell hobjectNames
    hmodel hinstance hconforms

end VLMOF.Source
