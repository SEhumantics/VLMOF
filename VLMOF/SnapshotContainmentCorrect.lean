import VLMOF.SchemaElaborationCorrect
import VLMOF.SnapshotObservationCorrect
import VLMOF.ContainmentClosureCorrect

namespace VLMOF.Source

variable {model : Model} {source : Instance} {schema : Schema} {snapshot : Snapshot}

def ObjectAliasAt (source : Instance) (id : ObjectId) (name : Name) : Prop :=
  (source.objects.map Object.alias)[id.val]? = some name

private theorem objectId_resolve_get {name : Name} {id : ObjectId}
    (h : objectId source name = .ok id) : ObjectAliasAt source id name := by
  unfold objectId at h
  cases hr : resolveIndex "object" (source.objects.map Object.alias) name <;>
    simp [hr, Except.map] at h
  subst id
  exact ((resolveIndex_iff_uniqueAliasAt _ _ _ _).mp hr).1

private theorem propertyId_resolve_get {name : Name} {id : PropertyId}
    (h : propertyId model name = .ok id) :
    (model.properties.map Property.alias)[id.val]? = some name := by
  unfold propertyId at h
  cases hr : resolveIndex "property" (model.properties.map Property.alias) name <;>
    simp [hr, Except.map] at h
  subst id
  exact ((resolveIndex_iff_uniqueAliasAt _ _ _ _).mp hr).1

private theorem propertyId_source_injective {first second : Name} {id : PropertyId}
    (hf : propertyId model first = .ok id) (hs : propertyId model second = .ok id) : first = second := by
  exact Option.some.inj ((propertyId_resolve_get hf).symm.trans (propertyId_resolve_get hs))

private theorem objectId_source_injective {first second : Name} {id : ObjectId}
    (hf : objectId source first = .ok id) (hs : objectId source second = .ok id) : first = second := by
  exact Option.some.inj ((objectId_resolve_get hf).symm.trans (objectId_resolve_get hs))

private theorem targetObjectSource (hb : bindInstance model source = .ok snapshot)
    {object : ObjectDecl} (ho : object ∈ snapshot.objects) :
    ∃ original ∈ source.objects, ObjectAliasAt source object.id original.alias := by
  rcases mapM_ok_target_mem (bindInstance_ok_mapM hb).1 ho with ⟨x, hx, hbind⟩
  have hs := List.fst_mem_of_mem_zipIdx hx
  unfold bindObjectAllocation at hbind
  cases hc : classId model x.1.classifier <;>
    simp [hc, Bind.bind, Except.bind, pure, Except.pure] at hbind
  subst object
  refine ⟨x.1, hs, ?_⟩
  have hg := List.mk_mem_zipIdx_iff_getElem?.mp hx
  simp [ObjectAliasAt, List.getElem?_map, hg]

private theorem objectAliasAt_unique {id : ObjectId} {first second : Name}
    (hf : ObjectAliasAt source id first) (hs : ObjectAliasAt source id second) : first = second :=
  Option.some.inj (hf.symm.trans hs)

private theorem propertyBinding_resolves_id (h : ModelWellFormed model)
    {x : Property × Nat} {p : PropertyDecl} (hx : x ∈ model.properties.zipIdx)
    (hb : bindPropertyEntry model x = .ok p) : propertyId model x.1.alias = .ok p.id := by
  have hn : (model.properties.map Property.alias).Nodup := by
    have hall := h.uniqueQualifiedAliases
    simp only [uniqueAliases, aliases, List.nodup_append] at hall
    exact hall.1.1.1.2.1
  have hi : (model.properties.map Property.alias)[x.2]? = some x.1.alias := by
    have hg := List.mk_mem_zipIdx_iff_getElem?.mp hx
    simp [List.getElem?_map, hg]
  have hr : resolveIndex "property" (model.properties.map Property.alias) x.1.alias = .ok x.2 := by
    rw [resolveIndex_iff_uniqueAliasAt]
    exact uniqueAliasAt_of_nodup hn hi
  unfold bindPropertyEntry at hb
  cases hq : checkQualification x.1.alias (some (ownerName x.1.owner)) <;>
    cases ho : bindOwner model x.1.owner <;>
    cases ht : bindType model x.1.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst p
  simp [propertyId, hr, Except.map]

private theorem propertyBinding_aggregation {x : Property × Nat} {p : PropertyDecl}
    (hb : bindPropertyEntry model x = .ok p) : p.aggregation = x.1.aggregation := by
  unfold bindPropertyEntry at hb
  cases hq : checkQualification x.1.alias (some (ownerName x.1.owner)) <;>
    cases ho : bindOwner model x.1.owner <;>
    cases ht : bindType model x.1.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst p
  rfl

theorem sourceCompositeEdge_iff_compositeEdge
    (hwf : ModelWellFormed model) (hm : bindModel model = .ok schema)
    (hi : bindInstance model source = .ok snapshot)
    {src dst : Name} {srcId dstId : ObjectId}
    (hsrc : objectId source src = .ok srcId) (hdst : objectId source dst = .ok dstId) :
    sourceCompositeEdge model source src dst ↔ compositeEdge schema snapshot srcId dstId := by
  have allocation := modelAllocation_of_bindModel hm
  constructor
  · rintro ⟨observation, hobservation, hosrc, href, property, hp, hproperty, hcomposite⟩
    rcases mapM_ok_source (bindInstance_ok_mapM hi).2 hobservation with
      ⟨translatedObservation, hto, htob⟩
    have htobFacts := (bindObservationAllocation_ok_iff model source observation translatedObservation).mp htob
    rcases allocation.propertyForSource hp with ⟨index, translatedProperty, hpz, htp, htpb⟩
    have hpropertyId := propertyBinding_resolves_id hwf hpz htpb
    have hobsProperty : translatedObservation.property = translatedProperty.id := by
      apply Except.ok.inj
      exact htobFacts.2.1.symm.trans (hproperty ▸ hpropertyId)
    rcases htobFacts.2.2.source_covered (.reference dst) href with ⟨value, hv, hvalue⟩
    cases value with
    | reference targetId =>
        have htarget : targetId = dstId := by
          have hbval : objectId source dst = .ok targetId := by
            unfold objectId
            rw [(resolveIndex_iff_uniqueAliasAt _ _ _ _).mpr hvalue]
            simp [Except.map]
          exact Except.ok.inj (hbval.symm.trans hdst)
        subst targetId
        refine ⟨translatedObservation, hto, ?_, translatedProperty, htp,
          hobsProperty.symm, ?_, hv⟩
        · exact Except.ok.inj (htobFacts.1.symm.trans (hosrc ▸ hsrc))
        · exact (propertyBinding_aggregation htpb).trans hcomposite
    | boolean => simp [ValueBinds] at hvalue
    | integer => simp [ValueBinds] at hvalue
    | string => simp [ValueBinds] at hvalue
    | enumeration => simp [ValueBinds] at hvalue
  · rintro ⟨translatedObservation, hto, hosrc, translatedProperty, htp,
      hproperty, hcomposite, href⟩
    rcases boundObservation_source hi hto with
      ⟨observation, ho, hobjectId, hpropertyId, hoccurrences⟩
    rcases (mapM_ok_mem_iff allocation.properties).mp htp with ⟨x, hx, htpb⟩
    have hp := List.fst_mem_of_mem_zipIdx hx
    have htranslatedPropertyId := propertyBinding_resolves_id hwf hx htpb
    have hpropertyAlias : x.1.alias = observation.property := by
      apply propertyId_source_injective htranslatedPropertyId
      simpa [hproperty] using hpropertyId
    rcases hoccurrences.target_covered (.reference dstId) href with ⟨value, hv, hvalue⟩
    cases value with
    | reference targetName =>
        have htargetName : targetName = dst := by
          exact objectId_source_injective (by
            unfold objectId
            rw [(resolveIndex_iff_uniqueAliasAt _ _ _ _).mpr hvalue]
            simp [Except.map]) hdst
        subst targetName
        refine ⟨observation, ho, ?_, hv, x.1, hp, hpropertyAlias, ?_⟩
        · exact objectId_source_injective hobjectId (by simpa [hosrc] using hsrc)
        · exact (propertyBinding_aggregation htpb).symm.trans hcomposite
    | boolean => simp [ValueBinds] at hvalue
    | integer => simp [ValueBinds] at hvalue
    | string => simp [ValueBinds] at hvalue
    | enumeration => simp [ValueBinds] at hvalue

private theorem objectId_of_aliasAt (h : SourceSatisfies { model, snapshot := source })
    {id : ObjectId} {name : Name} (ha : ObjectAliasAt source id name) :
    objectId source name = .ok id := by
  have hu : UniqueAliasAt (source.objects.map Object.alias) name id.val :=
    uniqueAliasAt_of_nodup h.uniqueObjectAliases ha
  unfold objectId
  rw [(resolveIndex_iff_uniqueAliasAt _ _ _ _).mpr hu]
  simp [Except.map]

private theorem compositeEdge_reflect
    (h : SourceSatisfies { model, snapshot := source })
    (hm : bindModel model = .ok schema) (hi : bindInstance model source = .ok snapshot)
    {start finish : ObjectId} (edge : compositeEdge schema snapshot start finish) :
    ∃ sourceStart sourceFinish, ObjectAliasAt source start sourceStart ∧
      ObjectAliasAt source finish sourceFinish ∧
      sourceCompositeEdge model source sourceStart sourceFinish := by
  rcases edge with ⟨observation, ho, hobject, property, hp, hproperty, haggregation, hv⟩
  rcases boundObservation_source hi ho with
    ⟨sourceObservation, hso, hsourceObject, hsourceProperty, hoccurrences⟩
  rcases hoccurrences.target_covered (.reference finish) hv with
    ⟨sourceValue, hsv, hvalue⟩
  cases sourceValue with
  | reference sourceFinish =>
      have hfinishId : objectId source sourceFinish = .ok finish := by
        unfold objectId
        rw [(resolveIndex_iff_uniqueAliasAt _ _ _ _).mpr hvalue]
        simp [Except.map]
      have hsourceObject' : objectId source sourceObservation.object = .ok start := by
        simpa [hobject] using hsourceObject
      refine ⟨sourceObservation.object, sourceFinish, objectId_resolve_get hsourceObject',
        objectId_resolve_get hfinishId, ?_⟩
      apply (sourceCompositeEdge_iff_compositeEdge h.model hm hi hsourceObject' hfinishId).mpr
      exact ⟨observation, ho, hobject, property, hp, hproperty, haggregation, hv⟩
  | boolean => simp [ValueBinds] at hvalue
  | integer => simp [ValueBinds] at hvalue
  | string => simp [ValueBinds] at hvalue
  | enumeration => simp [ValueBinds] at hvalue

theorem containmentPath_to_sourceReachable
    (h : SourceSatisfies { model, snapshot := source })
    (hm : bindModel model = .ok schema) (hi : bindInstance model source = .ok snapshot)
    {start finish : ObjectId}
    (path : StoredPath (compositeEdge schema snapshot) start finish)
    {sourceStart sourceFinish : Name}
    (hs : ObjectAliasAt source start sourceStart)
    (hf : ObjectAliasAt source finish sourceFinish) :
    SourceCompositeReachable model source sourceStart sourceFinish := by
  induction path generalizing sourceStart sourceFinish with
  | refl =>
      rw [objectAliasAt_unique hs hf]
      exact .refl _
  | @step here next path edge ih =>
      rcases compositeEdge_reflect h hm hi edge with
        ⟨hereName, nextName, hhere, hnext, hedge⟩
      have hprefix := ih hs hhere
      have result := SourceCompositeReachable.step hprefix hedge
      rw [objectAliasAt_unique hnext hf] at result
      exact result

theorem compositeReachable_to_sourceReachable
    (h : SourceSatisfies { model, snapshot := source })
    (hm : bindModel model = .ok schema) (hi : bindInstance model source = .ok snapshot)
    {start finish : ObjectId}
    (path : compositeReachable schema snapshot start finish)
    {sourceStart sourceFinish : Name}
    (hs : ObjectAliasAt source start sourceStart)
    (hf : ObjectAliasAt source finish sourceFinish) :
    SourceCompositeReachable model source sourceStart sourceFinish := by
  exact containmentPath_to_sourceReachable h hm hi
    (containmentClosure_sound schema snapshot path) hs hf

theorem containmentAcyclic_of_sourceSatisfies
    (h : SourceSatisfies { model, snapshot := source })
    (hm : bindModel model = .ok schema) (hi : bindInstance model source = .ok snapshot) :
    ∀ object ∈ snapshot.objects, ∀ child,
      compositeEdge schema snapshot object.id child →
      ¬ compositeReachable schema snapshot child object.id := by
  intro object ho child hedge hcycle
  rcases targetObjectSource hi ho with ⟨sourceObject, hsourceObject, hobjectAlias⟩
  rcases compositeEdge_reflect h hm hi hedge with
    ⟨sourceParent, sourceChild, hparentAlias, hchildAlias, hsourceEdge⟩
  have hparentName : sourceParent = sourceObject.alias :=
    objectAliasAt_unique hparentAlias hobjectAlias
  subst sourceParent
  have hsourceCycle := compositeReachable_to_sourceReachable h hm hi hcycle
    hchildAlias hobjectAlias
  exact h.containmentAcyclic sourceObject hsourceObject sourceChild hsourceEdge hsourceCycle

end VLMOF.Source
