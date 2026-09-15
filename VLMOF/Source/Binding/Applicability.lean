import VLMOF.Source.Correctness.Typing

/-!
# Property applicability across binding

The source predicate and target computation both distinguish class-owned
properties from association-owned ends.  This module exposes the proposition
computed by the target booleans, then transports both branches through the actual
schema allocation in both directions.

The two opening lemmas isolate the Core computation from source allocation.  The
private proof block then recovers uniquely allocated properties, classes,
associations, owners, and opposite ends.  The final theorem uses those witnesses
to prove the source and Core applicability predicates equivalent for successfully
resolved identities.
-/
namespace VLMOF.Source

/-- Propositional form of the owner test in `Schema.applicablePropertyIds`. -/
def TargetPropertyApplies (schema : Schema) (classId : ClassId)
    (property : PropertyDecl) : Prop :=
  match property.owner with
  | .class owner => schema.isSubtype classId owner
  | .association associationId =>
      ∃ association ∈ schema.associations, association.id = associationId ∧
        if association.ends.1 = property.id then
            ∃ opposite ∈ schema.properties, opposite.id = association.ends.2 ∧
              (match opposite.type with
                | .reference source => (schema.ancestors classId).contains source
                | _ => false) = true
        else if association.ends.2 = property.id then
            ∃ opposite ∈ schema.properties, opposite.id = association.ends.1 ∧
              (match opposite.type with
                | .reference source => (schema.ancestors classId).contains source
                | _ => false) = true
        else False

private theorem referenceTest_eq_true_iff (schema : Schema) (classId : ClassId)
    (property : PropertyDecl) :
    (match property.type with
      | .reference source => (schema.ancestors classId).contains source
      | _ => false) = true ↔
      ∃ source, property.type = .reference source ∧ schema.isSubtype classId source := by
  cases property.type <;>
    simp [Schema.isSubtype, List.contains_eq_mem, decide_eq_true_eq]

/-- `TargetPropertyApplies` is exactly the Boolean owner branch used by the Core
applicability computation, expressed as a proposition. -/
theorem targetPropertyApplies_iff_computed (schema : Schema) (classId : ClassId)
    (property : PropertyDecl) :
    TargetPropertyApplies schema classId property ↔
      (match property.owner with
      | .class owner => (schema.ancestors classId).contains owner
      | .association associationId =>
          schema.associationEndApplies classId associationId property.id) = true := by
  cases howner : property.owner with
  | «class» owner =>
      simp [TargetPropertyApplies, Schema.isSubtype, List.contains_eq_mem, howner]
  | association associationId =>
      simp [TargetPropertyApplies, Schema.associationEndApplies,
        List.contains_eq_mem, Bool.and_eq_true,
        decide_eq_true_eq, howner]
      rfl

/-- Membership in the computed applicable-property list is exactly existence of
a stored property with that ID satisfying its owner-specific applicability test. -/
theorem applicableProperty_iff_exists (schema : Schema) (classId : ClassId)
    (propertyId : PropertyId) :
    schema.applicableProperty classId propertyId ↔
      ∃ property ∈ schema.properties,
        property.id = propertyId ∧ TargetPropertyApplies schema classId property := by
  unfold Schema.applicableProperty Schema.applicablePropertyIds
  rw [List.mem_eraseDups]
  constructor
  · intro h
    obtain ⟨property, hproperty, hid⟩ := List.mem_map.mp h
    rw [List.mem_filter] at hproperty
    refine ⟨property, hproperty.1, hid, ?_⟩
    exact (targetPropertyApplies_iff_computed schema classId property).mpr hproperty.2
  · rintro ⟨property, hproperty, hid, happlies⟩
    apply List.mem_map.mpr
    refine ⟨property, ?_, hid⟩
    rw [List.mem_filter]
    exact ⟨hproperty,
      (targetPropertyApplies_iff_computed schema classId property).mp happlies⟩

/-! The following allocation-inversion lemmas are the source side of the bridge.
They use global alias uniqueness to identify the source row selected by a numeric
ID, then expose the translated owner, type, and association-end fields required
by the two applicability branches. -/

private theorem propertyAliases_uniqueBy {model : Model} (h : ModelWellFormed model) :
    uniqueBy Property.alias model.properties := by
  have hn := h.uniqueQualifiedAliases
  unfold uniqueAliases at hn
  simp only [aliases, List.nodup_append] at hn
  exact hn.1.1.1.2.1

private theorem associationAliases_uniqueBy {model : Model} (h : ModelWellFormed model) :
    uniqueBy Association.alias model.associations := by
  have hn := h.uniqueQualifiedAliases
  unfold uniqueAliases at hn
  simp only [aliases, List.nodup_append] at hn
  exact hn.1.1.2.1

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

private theorem propertyId_source_injective {model : Model} {first second : Name}
    {id : PropertyId} (hfirst : propertyId model first = .ok id)
    (hsecond : propertyId model second = .ok id) : first = second := by
  exact resolveIndex_injective ((propertyId_ok_iff model first id).mp hfirst)
    ((propertyId_ok_iff model second id).mp hsecond)

private theorem classAliasAt_of_classId {model : Model} {name : Name} {id : ClassId}
    (h : classId model name = .ok id) : ClassAliasAt model id name := by
  exact resolveIndex_getElem ((classId_ok_iff model name id).mp h)

private theorem bindPropertyEntry_owner {model : Model} {source : Property}
    {index : Nat} {target : PropertyDecl}
    (h : bindPropertyEntry model (source, index) = .ok target) :
    bindOwner model source.owner = .ok target.owner := by
  unfold bindPropertyEntry at h
  cases hq : checkQualification source.alias (some (ownerName source.owner)) <;>
    cases ho : bindOwner model source.owner <;>
    cases ht : bindType model source.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at h
  subst target
  exact rfl

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

private theorem bindReferenceType_iff {model : Model} {sourceType : Source.ValueType}
    {targetClass : ClassId} :
    bindType model sourceType = .ok (.reference targetClass) ↔
      ∃ sourceClass, sourceType = .reference sourceClass ∧
        classId model sourceClass = .ok targetClass := by
  cases sourceType with
  | boolean => simp [bindType, pure, Except.pure]
  | integer => simp [bindType, pure, Except.pure]
  | string => simp [bindType, pure, Except.pure]
  | enumeration name =>
      cases h : enumerationId model name <;>
        simp [bindType, h, Functor.map, Except.map]
  | reference name =>
      cases h : classId model name <;>
        simp [bindType, h, Functor.map, Except.map]

private theorem targetReferenceApplies_iff {model : Model} {schema : Schema}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    {sourceProperty : Property} {targetProperty : PropertyDecl} {index : Nat}
    (hbind : bindPropertyEntry model (sourceProperty, index) = .ok targetProperty)
    {className sourceClass : Name} {classTarget : ClassId}
    (hclass : classId model className = .ok classTarget)
    (htype : sourceProperty.type = .reference sourceClass) :
    (match targetProperty.type with
      | .reference source => (schema.ancestors classTarget).contains source
      | _ => false) = true ↔
      ClassAncestor model className sourceClass := by
  have htypeBind := bindPropertyEntry_type hbind
  rw [htype] at htypeBind
  cases hs : classId model sourceClass with
  | error error => simp [bindType, hs, Functor.map, Except.map] at htypeBind
  | ok sourceTarget =>
      have heq : targetProperty.type = .reference sourceTarget := by
        simpa [bindType, hs, Functor.map, Except.map] using htypeBind.symm
      rw [heq]
      simp only [List.contains_eq_mem, decide_eq_true_eq]
      constructor
      · intro hsubtype
        exact isSubtype_to_classAncestor hwell (modelAllocation_of_bindModel hmodel)
          hsubtype (classAliasAt_of_classId hclass) (classAliasAt_of_classId hs)
      · intro hancestor
        exact subtypeBindingPreserved_of_bindModel hwell hmodel
          hclass hs hancestor

/-- Applicability is preserved and reflected for the identities returned by the
successful source resolvers.  Association-owned properties use the exact binary
end order consumed by `bindAssociationEntry`. -/
theorem propertyApplies_iff_applicableProperty {model : Model} {schema : Schema}
    (hwell : ModelWellFormed model) (hmodel : bindModel model = .ok schema)
    {className propertyName : Name} {classTarget : ClassId} {propertyTarget : PropertyId}
    (hclass : classId model className = .ok classTarget)
    (hproperty : propertyId model propertyName = .ok propertyTarget) :
    propertyApplies model className propertyName ↔
      schema.applicableProperty classTarget propertyTarget := by
  have allocation := modelAllocation_of_bindModel hmodel
  obtain ⟨sourceProperty, targetProperty, hsourceProperty, hsourceAlias,
    htargetProperty, htargetId, hpropertyBind⟩ := allocation.propertyForId hproperty
  rw [applicableProperty_iff_exists]
  constructor
  · rintro ⟨property, hp, halias, happlies⟩
    have hsameSource : property = sourceProperty := by
      apply uniqueBy_eq_of_mem Property.alias (propertyAliases_uniqueBy hwell)
        hp hsourceProperty
      exact halias.trans hsourceAlias.symm
    subst property
    refine ⟨targetProperty, htargetProperty, htargetId, ?_⟩
    have hownerBind := bindPropertyEntry_owner hpropertyBind
    cases howner : sourceProperty.owner with
    | «class» ownerName =>
      cases ho : classId model ownerName with
      | error error =>
          simp [howner, bindOwner, ho, Functor.map, Except.map] at hownerBind
      | ok ownerTarget =>
          have htargetOwner : targetProperty.owner = .class ownerTarget := by
            simpa [howner, bindOwner, ho, Functor.map, Except.map] using hownerBind.symm
          simp only [TargetPropertyApplies, htargetOwner]
          exact subtypeBindingPreserved_of_bindModel hwell hmodel hclass ho
            (by simpa [howner] using happlies)
    | association associationName =>
      cases haid : associationId model associationName with
      | error error =>
          simp [howner, bindOwner, haid, Functor.map, Except.map] at hownerBind
      | ok associationTarget =>
        have htargetOwner : targetProperty.owner = .association associationTarget := by
          simpa [howner, bindOwner, haid, Functor.map, Except.map] using hownerBind.symm
        simp only [TargetPropertyApplies, htargetOwner]
        obtain ⟨sourceAssociation, hsourceAssociation, hsourceAssociationAlias,
          hpropertyEnd, otherName, hotherEnd, hotherNe, oppositeProperty,
          hoppositeProperty, hoppositeAlias, hoppositeApplies⟩ :=
            (by simpa [howner] using happlies)
        obtain ⟨allocatedAssociation, targetAssociation, hallocatedAssociation,
          hallocatedAssociationAlias, htargetAssociation, htargetAssociationId,
          hassociationBind⟩ := allocation.associationForId haid
        have hassociationSame : allocatedAssociation = sourceAssociation := by
          apply uniqueBy_eq_of_mem Association.alias (associationAliases_uniqueBy hwell)
            hallocatedAssociation hsourceAssociation
          exact hallocatedAssociationAlias.trans hsourceAssociationAlias.symm
        subst allocatedAssociation
        obtain ⟨firstName, secondName, firstTarget, secondTarget, hsourceEnds,
          hfirst, hsecond, htargetEnds⟩ := bindAssociationEntry_ends hassociationBind
        rw [hsourceEnds] at hpropertyEnd hotherEnd
        simp at hpropertyEnd hotherEnd
        rcases hpropertyEnd with hpropertyFirst | hpropertySecond
        · rcases hotherEnd with hotherFirst | hotherSecond
          · exact False.elim (hotherNe (hotherFirst.trans hpropertyFirst.symm))
          · have hfirstId : firstTarget = propertyTarget :=
              Except.ok.inj (hfirst.symm.trans (hpropertyFirst ▸ hproperty))
            obtain ⟨allocatedOpposite, targetOpposite, hallocatedOpposite,
              hallocatedOppositeAlias, htargetOpposite, htargetOppositeId,
              hoppositeBind⟩ := allocation.propertyForId hsecond
            have hoppositeSame : allocatedOpposite = oppositeProperty := by
              apply uniqueBy_eq_of_mem Property.alias (propertyAliases_uniqueBy hwell)
                hallocatedOpposite hoppositeProperty
              exact hallocatedOppositeAlias.trans
                (hotherSecond.symm.trans hoppositeAlias.symm)
            subst allocatedOpposite
            cases htype : oppositeProperty.type with
            | boolean => simp [htype] at hoppositeApplies
            | integer => simp [htype] at hoppositeApplies
            | string => simp [htype] at hoppositeApplies
            | enumeration enumeration => simp [htype] at hoppositeApplies
            | reference sourceClass =>
              refine ⟨targetAssociation, htargetAssociation, htargetAssociationId, ?_⟩
              rw [htargetEnds]
              simp only [Prod.fst, Prod.snd]
              rw [if_pos (hfirstId.trans htargetId.symm)]
              exact ⟨targetOpposite, htargetOpposite, htargetOppositeId,
                (targetReferenceApplies_iff hwell hmodel hoppositeBind hclass htype).2
                  (by simpa [htype] using hoppositeApplies)⟩
        · rcases hotherEnd with hotherFirst | hotherSecond
          · have hsecondId : secondTarget = propertyTarget :=
              Except.ok.inj (hsecond.symm.trans (hpropertySecond ▸ hproperty))
            have hfirstNe : firstTarget ≠ targetProperty.id := by
              intro heq
              apply hotherNe
              have hpTarget : propertyId model propertyName = .ok targetProperty.id := by
                simpa [htargetId] using hproperty
              have hfirstProperty : firstName = propertyName :=
                propertyId_source_injective hfirst (heq ▸ hpTarget)
              exact hotherFirst.trans hfirstProperty
            obtain ⟨allocatedOpposite, targetOpposite, hallocatedOpposite,
              hallocatedOppositeAlias, htargetOpposite, htargetOppositeId,
              hoppositeBind⟩ := allocation.propertyForId hfirst
            have hoppositeSame : allocatedOpposite = oppositeProperty := by
              apply uniqueBy_eq_of_mem Property.alias (propertyAliases_uniqueBy hwell)
                hallocatedOpposite hoppositeProperty
              exact hallocatedOppositeAlias.trans
                (hotherFirst.symm.trans hoppositeAlias.symm)
            subst allocatedOpposite
            cases htype : oppositeProperty.type with
            | boolean => simp [htype] at hoppositeApplies
            | integer => simp [htype] at hoppositeApplies
            | string => simp [htype] at hoppositeApplies
            | enumeration enumeration => simp [htype] at hoppositeApplies
            | reference sourceClass =>
              refine ⟨targetAssociation, htargetAssociation, htargetAssociationId, ?_⟩
              rw [htargetEnds]
              simp only [Prod.fst, Prod.snd]
              rw [if_neg hfirstNe, if_pos (hsecondId.trans htargetId.symm)]
              exact ⟨targetOpposite, htargetOpposite, htargetOppositeId,
                (targetReferenceApplies_iff hwell hmodel hoppositeBind hclass htype).2
                  (by simpa [htype] using hoppositeApplies)⟩
          · exact False.elim (hotherNe (hotherSecond.trans hpropertySecond.symm))
  · rintro ⟨property, hpropertyMem, hpropertyId, happlies⟩
    have hsameTarget : property = targetProperty := by
      apply uniqueBy_eq_of_mem PropertyDecl.id allocation.uniqueIds.2.2.1
        hpropertyMem htargetProperty
      exact hpropertyId.trans htargetId.symm
    subst property
    refine ⟨sourceProperty, hsourceProperty, hsourceAlias, ?_⟩
    have hownerBind := bindPropertyEntry_owner hpropertyBind
    cases howner : sourceProperty.owner with
    | «class» ownerName =>
      cases ho : classId model ownerName with
      | error error =>
          simp [howner, bindOwner, ho, Functor.map, Except.map] at hownerBind
      | ok ownerTarget =>
          have htargetOwner : targetProperty.owner = .class ownerTarget := by
            simpa [howner, bindOwner, ho, Functor.map, Except.map] using hownerBind.symm
          simp only [TargetPropertyApplies, htargetOwner] at happlies
          simpa [howner] using isSubtype_to_classAncestor hwell allocation happlies
            (classAliasAt_of_classId hclass) (classAliasAt_of_classId ho)
    | association associationName =>
      cases haid : associationId model associationName with
      | error error =>
          simp [howner, bindOwner, haid, Functor.map, Except.map] at hownerBind
      | ok associationTarget =>
        have htargetOwner : targetProperty.owner = .association associationTarget := by
          simpa [howner, bindOwner, haid, Functor.map, Except.map] using hownerBind.symm
        simp only [TargetPropertyApplies, htargetOwner] at happlies
        obtain ⟨targetAssociation, htargetAssociation, htargetAssociationId, hendApplies⟩ := happlies
        obtain ⟨sourceAssociation, allocatedAssociation, hsourceAssociation,
          hsourceAssociationAlias, hallocatedAssociation, hallocatedAssociationId,
          hassociationBind⟩ := allocation.associationForId haid
        have hassociationSame : targetAssociation = allocatedAssociation := by
          apply uniqueBy_eq_of_mem AssociationDecl.id allocation.uniqueIds.2.2.2.1
            htargetAssociation hallocatedAssociation
          exact htargetAssociationId.trans hallocatedAssociationId.symm
        subst targetAssociation
        obtain ⟨firstName, secondName, firstTarget, secondTarget, hsourceEnds,
          hfirst, hsecond, htargetEnds⟩ := bindAssociationEntry_ends hassociationBind
        have htargetEndsNe : firstTarget ≠ secondTarget := by
          obtain ⟨firstProperty, secondProperty, hassociationEnds, _, _, hne, _⟩ :=
            allocation.associationEnds hwell allocatedAssociation hallocatedAssociation
          have hpairs : (firstTarget, secondTarget) =
              (firstProperty.id, secondProperty.id) := htargetEnds.symm.trans hassociationEnds
          have hfirstEq := congrArg Prod.fst hpairs
          have hsecondEq := congrArg Prod.snd hpairs
          intro heq
          exact hne (hfirstEq.symm.trans (heq.trans hsecondEq))
        rw [htargetEnds] at hendApplies
        simp only [Prod.fst, Prod.snd] at hendApplies
        split at hendApplies
        next hfirstTarget =>
          obtain ⟨targetOpposite, htargetOpposite, htargetOppositeId,
            htargetReference⟩ := hendApplies
          obtain ⟨sourceOpposite, allocatedOpposite, hsourceOpposite,
            hsourceOppositeAlias, hallocatedOpposite, hallocatedOppositeId,
            hoppositeBind⟩ := allocation.propertyForId hsecond
          have hoppositeSame : targetOpposite = allocatedOpposite := by
            apply uniqueBy_eq_of_mem PropertyDecl.id allocation.uniqueIds.2.2.1
              htargetOpposite hallocatedOpposite
            exact htargetOppositeId.trans hallocatedOppositeId.symm
          subst targetOpposite
          obtain ⟨targetSource, htargetType, htargetSubtype⟩ :=
            (referenceTest_eq_true_iff schema classTarget allocatedOpposite).1
              htargetReference
          have hoppositeTypeBind := bindPropertyEntry_type hoppositeBind
          rw [htargetType] at hoppositeTypeBind
          obtain ⟨sourceClass, hsourceType, _⟩ :=
            (bindReferenceType_iff).1 hoppositeTypeBind
          have hancestor :=
            (targetReferenceApplies_iff hwell hmodel hoppositeBind hclass hsourceType).1
              htargetReference
          have hfirstName : firstName = propertyName :=
            propertyId_source_injective hfirst (by
              rw [hfirstTarget, htargetId]
              exact hproperty)
          have hne : secondName ≠ propertyName := by
            intro heq
            have hsecondEq : secondTarget = propertyTarget := by
              exact Except.ok.inj (hsecond.symm.trans (heq ▸ hproperty))
            exact htargetEndsNe (hfirstTarget.trans (htargetId.trans hsecondEq.symm))
          simpa [howner] using ⟨sourceAssociation, hsourceAssociation,
            hsourceAssociationAlias, by simp [hsourceEnds, hfirstName], secondName,
            by simp [hsourceEnds], hne, sourceOpposite, hsourceOpposite,
            hsourceOppositeAlias, by simpa [hsourceType] using hancestor⟩
        next hfirstTarget =>
          split at hendApplies
          next hsecondTarget =>
            obtain ⟨targetOpposite, htargetOpposite, htargetOppositeId,
              htargetReference⟩ := hendApplies
            obtain ⟨sourceOpposite, allocatedOpposite, hsourceOpposite,
              hsourceOppositeAlias, hallocatedOpposite, hallocatedOppositeId,
              hoppositeBind⟩ := allocation.propertyForId hfirst
            have hoppositeSame : targetOpposite = allocatedOpposite := by
              apply uniqueBy_eq_of_mem PropertyDecl.id allocation.uniqueIds.2.2.1
                htargetOpposite hallocatedOpposite
              exact htargetOppositeId.trans hallocatedOppositeId.symm
            subst targetOpposite
            obtain ⟨targetSource, htargetType, htargetSubtype⟩ :=
              (referenceTest_eq_true_iff schema classTarget allocatedOpposite).1
                htargetReference
            have hoppositeTypeBind := bindPropertyEntry_type hoppositeBind
            rw [htargetType] at hoppositeTypeBind
            obtain ⟨sourceClass, hsourceType, _⟩ :=
              (bindReferenceType_iff).1 hoppositeTypeBind
            have hancestor :=
              (targetReferenceApplies_iff hwell hmodel hoppositeBind hclass hsourceType).1
                htargetReference
            have hsecondName : secondName = propertyName :=
              propertyId_source_injective hsecond (by
                rw [hsecondTarget, htargetId]
                exact hproperty)
            have hne : firstName ≠ propertyName := by
              intro heq
              have hfirstEq : firstTarget = propertyTarget :=
                Except.ok.inj (hfirst.symm.trans (heq ▸ hproperty))
              exact htargetEndsNe (hfirstEq.trans
                (htargetId.symm.trans hsecondTarget.symm))
            simpa [howner] using ⟨sourceAssociation, hsourceAssociation,
              hsourceAssociationAlias, by simp [hsourceEnds, hsecondName], firstName,
              by simp [hsourceEnds], hne, sourceOpposite, hsourceOpposite,
              hsourceOppositeAlias, by simpa [hsourceType] using hancestor⟩
          next => contradiction

end VLMOF.Source
