import VLMOF.Source.Correctness.SchemaPreservation
import VLMOF.Source.Correctness.Observations
import VLMOF.Model.Reachability.Containment

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

private theorem compositeTest_eq
    (hwf : ModelWellFormed model) (hm : bindModel model = .ok schema)
    {sourceObservation : Source.Observation} {targetObservation : VLMOF.Observation}
    (hp : propertyId model sourceObservation.property = .ok targetObservation.property) :
    (model.properties.any (fun p =>
      p.alias = sourceObservation.property && p.aggregation = .composite)) =
    (schema.properties.any (fun p =>
      p.id = targetObservation.property ∧ p.aggregation = .composite)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨property, hproperty, htest⟩
    rcases (modelAllocation_of_bindModel hm).propertyForSource hproperty with
      ⟨index, translated, hz, ht, hb⟩
    have hid := propertyBinding_resolves_id hwf hz hb
    refine ⟨translated, ht, ?_, ?_⟩
    · exact Except.ok.inj (hid.symm.trans (htest.1 ▸ hp))
    · exact (propertyBinding_aggregation hb).trans htest.2
  · rintro ⟨translated, ht, hid, haggregation⟩
    rcases (mapM_ok_mem_iff (modelAllocation_of_bindModel hm).properties).mp ht with
      ⟨x, hx, hb⟩
    have hsource := List.fst_mem_of_mem_zipIdx hx
    have hresolved := propertyBinding_resolves_id hwf hx hb
    have halias : x.1.alias = sourceObservation.property := by
      apply propertyId_source_injective hresolved
      simpa [hid] using hp
    refine ⟨x.1, hsource, ?_⟩
    exact ⟨halias, (propertyBinding_aggregation hb).symm.trans haggregation⟩

private theorem referenceFilter_length_eq
    {sourceValues : List Source.Value} {targetValues : List VLMOF.Value}
    (hocc : OccurrencesBind model source sourceValues targetValues)
    {name : Name} {id : ObjectId} (hid : objectId source name = .ok id) :
    (sourceValues.filter (· = .reference name)).length =
      (targetValues.filter (· = .reference id)).length := by
  have hv : ValueBinds model source (.reference name) (.reference id) := by
    unfold ValueBinds
    unfold objectId at hid
    cases hres : resolveIndex "object" (source.objects.map Object.alias) name <;>
      simp [hres, Except.map] at hid
    subst id
    exact (resolveIndex_iff_uniqueAliasAt _ _ _ _).mp hres
  induction sourceValues generalizing targetValues with
  | nil => cases targetValues <;> simp_all [OccurrencesBind]
  | cons first rest ih =>
      cases targetValues with
      | nil => simp [OccurrencesBind] at hocc
      | cons translated translatedRest =>
          simp only [OccurrencesBind] at hocc
          have htail := ih hocc.2
          cases first <;> cases translated <;>
            simp_all [ValueBinds]
          case reference.reference sourceObject targetObject =>
            have hsourceId : objectId source sourceObject = .ok targetObject := by
              unfold objectId
              rw [(resolveIndex_iff_uniqueAliasAt _ _ _ _).mpr hocc.1]
              simp [Except.map]
            by_cases hn : sourceObject = name
            · have ht : targetObject = id := by
                apply Except.ok.inj
                exact hsourceId.symm.trans (hn ▸ hid)
              simp [hn, ht, htail]
            · have ht : targetObject ≠ id := by
                intro heq
                apply hn
                exact objectId_source_injective hsourceId (by simpa [heq] using hid)
              simp [hn, ht, htail]

private theorem incomingCompositeCount_mapM
    (hwf : ModelWellFormed model) (hm : bindModel model = .ok schema)
    {sources : List Source.Observation} {targets : List VLMOF.Observation}
    (hmap : sources.mapM (bindObservationAllocation model source) = .ok targets)
    {targetName : Name} {targetId : ObjectId}
    (hid : objectId source targetName = .ok targetId) :
    (sources.flatMap fun observation =>
      if model.properties.any (fun p =>
        p.alias = observation.property && p.aggregation = .composite)
      then observation.occurrences.filter (· = .reference targetName) else []).length =
    (targets.flatMap fun observation =>
      if schema.properties.any (fun p =>
        p.id = observation.property ∧ p.aggregation = .composite)
      then observation.occurrences.filter (· = .reference targetId) else []).length := by
  induction sources generalizing targets with
  | nil =>
      change Except.ok [] = Except.ok targets at hmap
      have : targets = [] := Except.ok.inj hmap.symm
      subst targets
      simp
  | cons first rest ih =>
      obtain ⟨translated, translatedRest, rfl, hfirst, hrest⟩ := mapM_ok_cons hmap
      have hfacts := (bindObservationAllocation_ok_iff model source first translated).mp hfirst
      have htest := compositeTest_eq hwf hm hfacts.2.1
      have hcount := referenceFilter_length_eq hfacts.2.2 hid
      simp only [List.flatMap_cons, List.length_append]
      have htail := ih hrest
      rw [htest]
      by_cases hc : schema.properties.any (fun p =>
        p.id = translated.property ∧ p.aggregation = .composite) = true
      · simp only [hc, if_true]
        omega
      · have hfalse : schema.properties.any (fun p =>
            p.id = translated.property ∧ p.aggregation = .composite) = false := by
          cases hv : schema.properties.any (fun p =>
            p.id = translated.property ∧ p.aggregation = .composite)
          · rfl
          · exact False.elim (hc hv)
        simp only [hfalse, Bool.false_eq_true, if_false]
        omega

theorem incomingCompositeCount_eq
    (h : SourceSatisfies { model, snapshot := source })
    (hm : bindModel model = .ok schema) (hi : bindInstance model source = .ok snapshot)
    {targetName : Name} {targetId : ObjectId}
    (hid : objectId source targetName = .ok targetId) :
    incomingCompositeCount model source targetName =
      VLMOF.incomingCompositeCount schema snapshot targetId := by
  unfold Source.incomingCompositeCount VLMOF.incomingCompositeCount
  exact incomingCompositeCount_mapM h.model hm (bindInstance_ok_mapM hi).2 hid

theorem oneIncomingComposite_of_sourceSatisfies
    (h : SourceSatisfies { model, snapshot := source })
    (hm : bindModel model = .ok schema) (hi : bindInstance model source = .ok snapshot) :
    ∀ object ∈ snapshot.objects,
      VLMOF.incomingCompositeCount schema snapshot object.id ≤ 1 := by
  intro object ho
  rcases targetObjectSource hi ho with ⟨sourceObject, hsourceObject, halias⟩
  have hid := objectId_of_aliasAt h halias
  rw [← incomingCompositeCount_eq h hm hi hid]
  exact h.oneIncomingComposite sourceObject hsourceObject

private theorem associationBinding_ends {x : Association × Nat} {a : AssociationDecl}
    (hb : bindAssociationEntry model x = .ok a) :
    ∃ first second firstId secondId,
      x.1.ends = [first, second] ∧ propertyId model first = .ok firstId ∧
      propertyId model second = .ok secondId ∧ a.ends = (firstId, secondId) := by
  unfold bindAssociationEntry at hb
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    cases hend : x.1.ends with
    | nil => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at hb
    | cons first rest =>
      cases rest with
      | nil => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at hb
      | cons second tail =>
        cases tail with
        | cons third tail => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at hb
        | nil =>
          cases hf : propertyId model first with
          | error error => simp [hq, hp, hend, hf, Bind.bind, Except.bind] at hb
          | ok firstId =>
            cases hs : propertyId model second with
            | error error => simp [hq, hp, hend, hf, hs, Bind.bind, Except.bind] at hb
            | ok secondId =>
              simp [hq, hp, hend, hf, hs, Bind.bind, Except.bind, pure, Except.pure] at hb
              all_goals try subst a
              all_goals exact ⟨first, second, firstId, secondId, rfl, hf, hs, rfl⟩

private theorem referenceValueBinds {name : Name} {id : ObjectId}
    (hid : objectId source name = .ok id) :
    ValueBinds model source (.reference name) (.reference id) := by
  unfold ValueBinds objectId at *
  cases hr : resolveIndex "object" (source.objects.map Object.alias) name <;>
    simp [hr, Except.map] at hid
  subst id
  exact (resolveIndex_iff_uniqueAliasAt _ _ _ _).mp hr

theorem oppositeCounts_of_sourceSatisfies
    (h : SourceSatisfies { model, snapshot := source })
    (hm : bindModel model = .ok schema) (hi : bindInstance model source = .ok snapshot) :
    ∀ association ∈ schema.associations, ∀ firstId secondId,
      association.ends = (firstId, secondId) →
      ∀ firstObject ∈ snapshot.objects, ∀ secondObject ∈ snapshot.objects,
      (snapshot.occurrences firstObject.id firstId).count (.reference secondObject.id) =
      (snapshot.occurrences secondObject.id secondId).count (.reference firstObject.id) := by
  intro association ha firstId secondId hends firstObject hfirstObject secondObject hsecondObject
  let allocation := modelAllocation_of_bindModel hm
  rcases (mapM_ok_mem_iff allocation.associations).mp ha with ⟨x, hx, hb⟩
  have hsourceAssociation := List.fst_mem_of_mem_zipIdx hx
  rcases associationBinding_ends hb with
    ⟨first, second, boundFirstId, boundSecondId, hsourceEnds,
      hfirstProperty, hsecondProperty, hboundEnds⟩
  have hfirstId : firstId = boundFirstId := by
    exact congrArg Prod.fst (hends.symm.trans hboundEnds)
  have hsecondId : secondId = boundSecondId := by
    exact congrArg Prod.snd (hends.symm.trans hboundEnds)
  subst firstId
  subst secondId
  rcases targetObjectSource hi hfirstObject with
    ⟨sourceFirst, hsourceFirst, hfirstAlias⟩
  rcases targetObjectSource hi hsecondObject with
    ⟨sourceSecond, hsourceSecond, hsecondAlias⟩
  have hfirstObjectId := objectId_of_aliasAt h hfirstAlias
  have hsecondObjectId := objectId_of_aliasAt h hsecondAlias
  have hleft := bindInstance_occurrences_count_eq hi hfirstObjectId hfirstProperty
    (referenceValueBinds hsecondObjectId)
  have hright := bindInstance_occurrences_count_eq hi hsecondObjectId hsecondProperty
    (referenceValueBinds hfirstObjectId)
  calc
    (snapshot.occurrences firstObject.id boundFirstId).count (.reference secondObject.id) =
        (sourceOccurrences source sourceFirst.alias first).count (.reference sourceSecond.alias) :=
      hleft.symm
    _ = (sourceOccurrences source sourceSecond.alias second).count (.reference sourceFirst.alias) :=
      h.oppositeCounts x.1 hsourceAssociation first second hsourceEnds
        sourceFirst hsourceFirst sourceSecond hsourceSecond
    _ = (snapshot.occurrences secondObject.id boundSecondId).count (.reference firstObject.id) :=
      hright

end VLMOF.Source
