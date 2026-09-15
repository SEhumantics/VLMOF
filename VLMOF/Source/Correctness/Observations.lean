import VLMOF.Source.Correctness.Allocation
import VLMOF.Source.Semantics

/-!
# Snapshot observation correspondence

The source and core occurrence lookups both concatenate every matching row.  A
successful instance binding preserves this aggregation in list order, while
source observation-key uniqueness prevents two allocated rows from sharing a
numeric key.

The first private group establishes injectivity of resolved object/property
aliases.  Key uniqueness is then transported through the observation allocation.
The second private group proves an accumulator invariant for filtered `flatMap`;
it yields the aggregate occurrence correspondence used by all final corollaries.
-/
namespace VLMOF.Source

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

/-- Two object aliases successfully resolving to the same allocated identity are
the same source alias. -/
private theorem objectId_source_injective {snapshot : Instance} {first second : Name} {id : ObjectId}
    (hf : objectId snapshot first = .ok id) (hs : objectId snapshot second = .ok id) :
    first = second := by
  exact resolveIndex_injective ((objectId_ok_iff snapshot first id).mp hf)
    ((objectId_ok_iff snapshot second id).mp hs)

/-- Two property aliases successfully resolving to the same allocated identity
are the same source alias. -/
private theorem propertyId_source_injective {model : Model} {first second : Name} {id : PropertyId}
    (hf : propertyId model first = .ok id) (hs : propertyId model second = .ok id) :
    first = second := by
  exact resolveIndex_injective ((propertyId_ok_iff model first id).mp hf)
    ((propertyId_ok_iff model second id).mp hs)

/-- Pointwise occurrence binding is closed under appending corresponding source
and target segments. -/
theorem OccurrencesBind.append {model : Model} {snapshot : Instance}
    {source₁ source₂ : List Source.Value} {target₁ target₂ : List VLMOF.Value}
    (h₁ : OccurrencesBind model snapshot source₁ target₁)
    (h₂ : OccurrencesBind model snapshot source₂ target₂) :
    OccurrencesBind model snapshot (source₁ ++ source₂) (target₁ ++ target₂) := by
  induction source₁ generalizing target₁ with
  | nil => cases target₁ <;> simp_all [OccurrencesBind]
  | cons source sources ih =>
      cases target₁ with
      | nil => simp [OccurrencesBind] at h₁
      | cons target targets =>
          simp only [OccurrencesBind] at h₁ ⊢
          exact ⟨h₁.1, ih h₁.2⟩

private theorem observationAllocation_key_reflects {model : Model} {snapshot : Instance}
    {firstSource secondSource : Source.Observation}
    {firstTarget secondTarget : VLMOF.Observation}
    (hf : bindObservationAllocation model snapshot firstSource = .ok firstTarget)
    (hs : bindObservationAllocation model snapshot secondSource = .ok secondTarget)
    (hk : VLMOF.Observation.key firstTarget = VLMOF.Observation.key secondTarget) :
    SourceObservation.key firstSource = SourceObservation.key secondSource := by
  have hf' := (bindObservationAllocation_ok_iff model snapshot firstSource firstTarget).mp hf
  have hs' := (bindObservationAllocation_ok_iff model snapshot secondSource secondTarget).mp hs
  have ho : firstTarget.object = secondTarget.object := congrArg Prod.fst hk
  have hp : firstTarget.property = secondTarget.property := congrArg Prod.snd hk
  apply Prod.ext
  · change firstSource.object = secondSource.object
    exact objectId_source_injective hf'.1 (by simpa [ho] using hs'.1)
  · change firstSource.property = secondSource.property
    exact propertyId_source_injective hf'.2.1 (by simpa [hp] using hs'.2.1)

private theorem mapM_observation_keys_nodup {model : Model} {snapshot : Instance}
    {sources : List Source.Observation} {targets : List VLMOF.Observation}
    (hsource : (sources.map SourceObservation.key).Nodup)
    (hmap : sources.mapM (bindObservationAllocation model snapshot) = .ok targets) :
    (targets.map VLMOF.Observation.key).Nodup := by
  induction sources generalizing targets with
  | nil =>
      change Except.ok [] = Except.ok targets at hmap
      have : targets = [] := Except.ok.inj hmap.symm
      subst targets
      simp
  | cons source sources ih =>
      obtain ⟨target, targets, rfl, hhead, htail⟩ := mapM_ok_cons hmap
      simp only [List.map_cons, List.nodup_cons] at hsource ⊢
      refine ⟨?_, ih hsource.2 htail⟩
      intro hm
      obtain ⟨other, hother, hk⟩ := List.mem_map.mp hm
      obtain ⟨otherSource, hsourceMem, hotherBind⟩ :=
        mapM_ok_target_mem htail hother
      have hkey := observationAllocation_key_reflects hhead hotherBind hk.symm
      exact hsource.1 (List.mem_map.mpr ⟨otherSource, hsourceMem, hkey.symm⟩)

/-- Source observation-key uniqueness is preserved by the actual successful
instance binder.  No target schema or other source-conformance premise is needed. -/
theorem bindInstance_uniqueObservationKeys_of_nodup {model : Model} {snapshot : Instance}
    {target : Snapshot}
    (hsource : (snapshot.observations.map SourceObservation.key).Nodup)
    (hbind : bindInstance model snapshot = .ok target) :
    uniqueBy VLMOF.Observation.key target.observations := by
  unfold uniqueBy
  exact mapM_observation_keys_nodup hsource
    (bindInstance_ok_mapM hbind).2

/-- Source satisfaction supplies source-key uniqueness, so successful binding
produces duplicate-free numeric observation keys. -/
theorem bindInstance_uniqueObservationKeys {model : Model} {snapshot : Instance}
    {target : Snapshot} (hsource : SourceSatisfies { model, snapshot })
    (hbind : bindInstance model snapshot = .ok target) :
    uniqueBy VLMOF.Observation.key target.observations :=
  bindInstance_uniqueObservationKeys_of_nodup hsource.uniqueObservationKeys hbind

private theorem observationAllocation_key_matches {model : Model} {snapshot : Instance}
    {source : Source.Observation} {target : VLMOF.Observation}
    {object property : Name} {objectId' : ObjectId} {propertyId' : PropertyId}
    (hbind : bindObservationAllocation model snapshot source = .ok target)
    (ho : objectId snapshot object = .ok objectId')
    (hp : propertyId model property = .ok propertyId') :
    (source.object = object ∧ source.property = property) ↔
      (target.object = objectId' ∧ target.property = propertyId') := by
  have hb := (bindObservationAllocation_ok_iff model snapshot source target).mp hbind
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨Except.ok.inj (hb.1.symm.trans ho), Except.ok.inj (hb.2.1.symm.trans hp)⟩
  · rintro ⟨hto, htp⟩
    constructor
    · exact objectId_source_injective hb.1 (by simpa [hto] using ho)
    · exact propertyId_source_injective hb.2.1 (by simpa [htp] using hp)

private theorem observationMapM_occurrencesBind {model : Model} {snapshot : Instance}
    {sources : List Source.Observation} {targets : List VLMOF.Observation}
    {object property : Name} {objectId' : ObjectId} {propertyId' : PropertyId}
    (hmap : sources.mapM (bindObservationAllocation model snapshot) = .ok targets)
    (ho : objectId snapshot object = .ok objectId')
    (hp : propertyId model property = .ok propertyId') :
    OccurrencesBind model snapshot
      ((sources.filter fun row => row.object = object ∧ row.property = property).flatMap
        Source.Observation.occurrences)
      ((targets.filter fun row => row.object = objectId' ∧ row.property = propertyId').flatMap
        VLMOF.Observation.occurrences) := by
  induction sources generalizing targets with
  | nil =>
      change Except.ok [] = Except.ok targets at hmap
      have : targets = [] := Except.ok.inj hmap.symm
      subst targets
      simp [OccurrencesBind]
  | cons source sources ih =>
      obtain ⟨target, targets, rfl, hhead, htail⟩ := mapM_ok_cons hmap
      have hocc := (bindObservationAllocation_ok_iff model snapshot source target).mp hhead
      have hkey := observationAllocation_key_matches hhead ho hp
      by_cases hm : source.object = object ∧ source.property = property
      · have hmt := hkey.mp hm
        simpa [hm, hmt] using hocc.2.2.append (ih htail)
      · have hmtn : ¬(target.object = objectId' ∧ target.property = propertyId') := by
          exact fun hmt => hm (hkey.mpr hmt)
        simpa [hm, hmtn] using ih htail

/-- Aggregate source and Core occurrence lookups for a successfully resolved key
are pointwise related.  The proof keeps every matching row and appends its bound
occurrences in list order. -/
theorem bindInstance_occurrencesBind {model : Model} {snapshot : Instance}
    {target : Snapshot} (hbind : bindInstance model snapshot = .ok target)
    {object property : Name} {objectId' : ObjectId} {propertyId' : PropertyId}
    (ho : objectId snapshot object = .ok objectId')
    (hp : propertyId model property = .ok propertyId') :
    OccurrencesBind model snapshot (sourceOccurrences snapshot object property)
      (target.occurrences objectId' propertyId') := by
  exact observationMapM_occurrencesBind (bindInstance_ok_mapM hbind).2 ho hp

/-- Aggregate occurrence count is unchanged by successful instance binding. -/
theorem bindInstance_occurrences_length_eq {model : Model} {snapshot : Instance}
    {target : Snapshot} (hbind : bindInstance model snapshot = .ok target)
    {object property : Name} {objectId' : ObjectId} {propertyId' : PropertyId}
    (ho : objectId snapshot object = .ok objectId')
    (hp : propertyId model property = .ok propertyId') :
    (sourceOccurrences snapshot object property).length =
      (target.occurrences objectId' propertyId').length :=
  (bindInstance_occurrencesBind hbind ho hp).length_eq

/-- Aggregate occurrences are duplicate-free in the source exactly when their
bound Core occurrences are duplicate-free. -/
theorem bindInstance_occurrences_nodup_iff {model : Model} {snapshot : Instance}
    {target : Snapshot} (hbind : bindInstance model snapshot = .ok target)
    {object property : Name} {objectId' : ObjectId} {propertyId' : PropertyId}
    (ho : objectId snapshot object = .ok objectId')
    (hp : propertyId model property = .ok propertyId') :
    (sourceOccurrences snapshot object property).Nodup ↔
      (target.occurrences objectId' propertyId').Nodup :=
  (bindInstance_occurrencesBind hbind ho hp).nodup_iff

/-- A related source/Core value occurs under a symbolic key exactly when the Core
value occurs under the resolved numeric key. -/
theorem bindInstance_occurrences_mem_iff {model : Model} {snapshot : Instance}
    {target : Snapshot} (hbind : bindInstance model snapshot = .ok target)
    {object property : Name} {objectId' : ObjectId} {propertyId' : PropertyId}
    (ho : objectId snapshot object = .ok objectId')
    (hp : propertyId model property = .ok propertyId')
    {sourceValue : Source.Value} {targetValue : VLMOF.Value}
    (hv : ValueBinds model snapshot sourceValue targetValue) :
    sourceValue ∈ sourceOccurrences snapshot object property ↔
      targetValue ∈ target.occurrences objectId' propertyId' :=
  (bindInstance_occurrencesBind hbind ho hp).mem_iff hv

/-- Multiplicity of a related value under an observation key is preserved exactly,
which is later used for opposite-end reciprocity. -/
theorem bindInstance_occurrences_count_eq {model : Model} {snapshot : Instance}
    {target : Snapshot} (hbind : bindInstance model snapshot = .ok target)
    {object property : Name} {objectId' : ObjectId} {propertyId' : PropertyId}
    (ho : objectId snapshot object = .ok objectId')
    (hp : propertyId model property = .ok propertyId')
    {sourceValue : Source.Value} {targetValue : VLMOF.Value}
    (hv : ValueBinds model snapshot sourceValue targetValue) :
    (sourceOccurrences snapshot object property).count sourceValue =
      (target.occurrences objectId' propertyId').count targetValue :=
  (bindInstance_occurrencesBind hbind ho hp).count_eq hv

/-- Ordered equality and unordered permutation of aggregate occurrence lists are
both preserved and reflected by instance binding. -/
theorem bindInstance_occurrences_equivalent_iff {model : Model} {snapshot : Instance}
    {target : Snapshot} (hbind : bindInstance model snapshot = .ok target)
    {leftObject leftProperty rightObject rightProperty : Name}
    {leftObjectId rightObjectId : ObjectId} {leftPropertyId rightPropertyId : PropertyId}
    (hlo : objectId snapshot leftObject = .ok leftObjectId)
    (hlp : propertyId model leftProperty = .ok leftPropertyId)
    (hro : objectId snapshot rightObject = .ok rightObjectId)
    (hrp : propertyId model rightProperty = .ok rightPropertyId) (ordered : Bool) :
    Equivalent ordered
        (sourceOccurrences snapshot leftObject leftProperty)
        (sourceOccurrences snapshot rightObject rightProperty) ↔
      VLMOF.Occurrences.equivalent ordered
        (target.occurrences leftObjectId leftPropertyId)
        (target.occurrences rightObjectId rightPropertyId) :=
  (bindInstance_occurrencesBind hbind hlo hlp).equivalent_iff
    (bindInstance_occurrencesBind hbind hro hrp) ordered

end VLMOF.Source
