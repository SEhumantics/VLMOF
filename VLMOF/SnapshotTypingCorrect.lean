import VLMOF.SubtypeBindingCorrect

/-!
# Snapshot resolution and value typing fields

These proofs establish four target snapshot-conformance fields directly from a
satisfying source document and successful model/instance binding.  Declaration
and object witnesses come from the actual allocation computations; no target
schema well-formedness or target conformance field is assumed.
-/
namespace VLMOF.Source

private theorem classAliases_uniqueBy {model : Model} (h : ModelWellFormed model) :
    uniqueBy Class.alias model.classes := by
  have hn := h.uniqueQualifiedAliases
  unfold uniqueAliases at hn
  simp only [aliases, List.nodup_append] at hn
  exact hn.1.1.1.1.2.1

private theorem propertyAliases_uniqueBy {model : Model} (h : ModelWellFormed model) :
    uniqueBy Property.alias model.properties := by
  have hn := h.uniqueQualifiedAliases
  unfold uniqueAliases at hn
  simp only [aliases, List.nodup_append] at hn
  exact hn.1.1.1.2.1

private theorem bindObjectAllocation_classifier {model : Model} {source : Object}
    {index : Nat} {target : ObjectDecl}
    (h : bindObjectAllocation model (source, index) = .ok target) :
    classId model source.classifier = .ok target.classifier := by
  unfold bindObjectAllocation at h
  cases hc : classId model source.classifier <;>
    simp [hc, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  exact rfl

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

private theorem bindPropertyEntry_type {model : Model} {source : Property}
    {index : Nat} {target : PropertyDecl}
    (h : bindPropertyEntry model (source, index) = .ok target) :
    bindType model source.type = .ok target.type := by
  unfold bindPropertyEntry at h
  cases hq : checkQualification source.alias (some (ownerName source.owner)) <;>
    cases ho : bindOwner model source.owner <;>
    cases ht : bindType model source.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  exact rfl

private theorem objectId_uniqueAliasAt {snapshot : Instance} {name : Name} {id : ObjectId}
    (h : objectId snapshot name = .ok id) :
    UniqueAliasAt (snapshot.objects.map Object.alias) name id.val := by
  cases id with
  | mk index =>
      unfold objectId at h
      cases hr : resolveIndex "object" (snapshot.objects.map Object.alias) name <;>
        simp [hr, Except.map] at h
      subst index
      exact (resolveIndex_iff_uniqueAliasAt _ _ _ _).mp hr

/-- Every allocated object classifier resolves to an allocated schema class. -/
theorem bindInstance_classifiersResolved {model : Model} {snapshot : Instance}
    {schema : Schema} {target : Snapshot}
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model snapshot = .ok target) :
    ∀ object ∈ target.objects, schema.classDecls object.classifier ≠ [] := by
  intro object hobject
  have allocation := modelAllocation_of_bindModel hmodel
  obtain ⟨entry, _, hb⟩ := mapM_ok_target_mem (bindInstance_ok_mapM hinstance).1 hobject
  exact allocation.classResolved (bindObjectAllocation_classifier hb)

/-- Abstractness is copied from the uniquely resolved source classifier, so every
target object produced from a satisfying source has a concrete classifier. -/
theorem bindInstance_concreteClassifiers {model : Model} {snapshot : Instance}
    {schema : Schema} {target : Snapshot}
    (hsource : SourceSatisfies { model, snapshot })
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model snapshot = .ok target) :
    ∀ object ∈ target.objects, ∀ declaration ∈ schema.classes,
      declaration.id = object.classifier → declaration.isAbstract = false := by
  intro object hobject declaration hdeclaration hid
  have allocation := modelAllocation_of_bindModel hmodel
  obtain ⟨entry, hentry, hb⟩ :=
    mapM_ok_target_mem (bindInstance_ok_mapM hinstance).1 hobject
  obtain ⟨sourceObject, index⟩ := entry
  have hsourceObject := List.fst_mem_of_mem_zipIdx hentry
  have hclassifier := bindObjectAllocation_classifier hb
  obtain ⟨sourceClass, allocatedClass, hs, halias, ht, htid, hclassBind⟩ :=
    allocation.classForId hclassifier
  have hsame : declaration = allocatedClass := by
    apply uniqueBy_eq_of_mem ClassDecl.id allocation.uniqueIds.2.1
      hdeclaration ht
    exact hid.trans htid.symm
  subst declaration
  rw [bindClassEntry_isAbstract hclassBind]
  exact hsource.concreteClassifiers sourceObject hsourceObject sourceClass hs halias

/-- Every bound observation key is backed by allocated object and property rows. -/
theorem bindInstance_observationKeysResolved {model : Model} {snapshot : Instance}
    {schema : Schema} {target : Snapshot}
    (hsource : SourceSatisfies { model, snapshot })
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model snapshot = .ok target) :
    ∀ observation ∈ target.observations,
      (∃ object ∈ target.objects, object.id = observation.object) ∧
      (∃ property ∈ schema.properties, property.id = observation.property) := by
  intro observation hobservation
  have allocation := modelAllocation_of_bindModel hmodel
  obtain ⟨sourceObservation, hsourceObservation, ho, hp, _⟩ :=
    boundObservation_source hinstance hobservation
  obtain ⟨sourceObject, hsourceObject, halias⟩ :=
    (hsource.observationKeysResolved sourceObservation hsourceObservation).1
  obtain ⟨classifier, targetObject, _, ht, htid, _⟩ :=
    boundObject_classifierForId hinstance (objectId_uniqueAliasAt ho)
      hsourceObject halias
  obtain ⟨sourceProperty, targetProperty, _, _, htp, htpid, _⟩ :=
    allocation.propertyForId hp
  exact ⟨⟨targetObject, ht, htid⟩, ⟨targetProperty, htp, htpid⟩⟩

/-- Values in every allocated observation have the type of the uniquely allocated
target property row. -/
theorem bindInstance_valuesTyped {model : Model} {snapshot : Instance}
    {schema : Schema} {target : Snapshot}
    (hsource : SourceSatisfies { model, snapshot })
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model snapshot = .ok target) :
    ∀ observation ∈ target.observations, ∀ property ∈ schema.properties,
      property.id = observation.property →
      ∀ value ∈ observation.occurrences,
        valueMatches schema target property.type value := by
  intro observation hobservation property hproperty hpropertyId value hvalue
  have allocation := modelAllocation_of_bindModel hmodel
  obtain ⟨sourceObservation, hsourceObservation, _, hp, hoccurrences⟩ :=
    boundObservation_source hinstance hobservation
  obtain ⟨sourceProperty, hsourceProperty, hsourceAlias⟩ :=
    (hsource.observationKeysResolved sourceObservation hsourceObservation).2
  obtain ⟨allocatedSource, allocatedProperty, has, haa, hat, haid, habind⟩ :=
    allocation.propertyForId hp
  have hsameSource : allocatedSource = sourceProperty := by
    apply uniqueBy_eq_of_mem Property.alias (propertyAliases_uniqueBy hsource.model)
      has hsourceProperty
    exact haa.trans hsourceAlias.symm
  subst allocatedSource
  have hsameTarget : property = allocatedProperty := by
    apply uniqueBy_eq_of_mem PropertyDecl.id allocation.uniqueIds.2.2.1
      hproperty hat
    exact hpropertyId.trans haid.symm
  subst property
  obtain ⟨sourceValue, hsourceValue, hvalueBind⟩ :=
    hoccurrences.target_covered value hvalue
  have hsourceTyped := hsource.valuesTyped sourceObservation hsourceObservation
    sourceProperty hsourceProperty hsourceAlias sourceValue hsourceValue
  exact sourceValueMatches_to_valueMatches_of_modelWellFormed hsource.model
    hmodel hinstance (bindPropertyEntry_type habind) hvalueBind hsourceTyped

end VLMOF.Source
