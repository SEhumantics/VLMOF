import VLMOF.ValueTypingCorrect
import VLMOF.FiniteClosure
import VLMOF.Properties

/-!
# Source-to-target subtype completeness

Successful class allocation turns every symbolic direct-super edge into a stored
target edge.  The target superclass expansion stays inside the finite allocated
class carrier because all stored direct supers are resolved.  Generic finite
closure therefore contains every translated symbolic ancestor path, without a
`SchemaWellFormed` premise.
-/
namespace VLMOF.Source

/-- The stored edge exposed by `classSupers`. -/
def ClassDirectSuperEdge (schema : Schema) (sub super : ClassId) : Prop :=
  ∃ declaration ∈ schema.classes,
    declaration.id = sub ∧ super ∈ declaration.directSupers

theorem classSupers_iff_directSuperEdge (schema : Schema) (seen : List ClassId)
    (super : ClassId) :
    super ∈ classSupers schema seen ↔
      ∃ sub ∈ seen, ClassDirectSuperEdge schema sub super := by
  unfold classSupers ClassDirectSuperEdge
  constructor
  · intro h
    obtain ⟨declaration, hd, hs⟩ := List.mem_flatMap.mp h
    rw [List.mem_filter] at hd
    exact ⟨declaration.id, by simpa using hd.2,
      declaration, hd.1, rfl, hs⟩
  · rintro ⟨sub, hsub, declaration, hd, hid, hs⟩
    apply List.mem_flatMap.mpr
    refine ⟨declaration, ?_, hs⟩
    rw [List.mem_filter]
    exact ⟨hd, by simpa [hid] using hsub⟩

/-- Resolution of every stored direct super closes `classSupers` over the class
identifier carrier. -/
theorem classSupers_closed_of_supersResolved {schema : Schema}
    (hresolved : ∀ declaration ∈ schema.classes, ∀ super ∈ declaration.directSupers,
      schema.classDecls super ≠ []) :
    ∀ seen super, super ∈ classSupers schema seen → super ∈ classUniverse schema := by
  intro seen super hsuper
  obtain ⟨sub, _, declaration, hd, _, hs⟩ :=
    (classSupers_iff_directSuperEdge schema seen super).mp hsuper
  exact mem_classUniverse_of_classDecls_ne_nil (hresolved declaration hd super hs)

/-- A stored superclass path is included in the bounded semantic closure whenever
the start is allocated and all stored direct supers resolve. -/
theorem storedClassPath_isSubtype_of_supersResolved {schema : Schema}
    (hresolved : ∀ declaration ∈ schema.classes, ∀ super ∈ declaration.directSupers,
      schema.classDecls super ≠ [])
    {start finish : ClassId} (hstart : start ∈ classUniverse schema)
    (path : StoredPath (ClassDirectSuperEdge schema) start finish) :
    schema.isSubtype start finish := by
  unfold Schema.isSubtype Schema.ancestors
  rw [List.mem_eraseDups]
  have hpath := (finiteClosure_iff_path
    (classSupers schema) (ClassDirectSuperEdge schema) (classUniverse schema)
    (classSupers_iff_directSuperEdge schema)
    (classSupers_closed_of_supersResolved hresolved) hstart).mpr path
  simpa [classUniverse] using hpath

private theorem classAliases_nodup {model : Model} (h : ModelWellFormed model) :
    (model.classes.map Class.alias).Nodup := by
  have hn := h.uniqueQualifiedAliases
  unfold uniqueAliases at hn
  simp only [aliases, List.nodup_append] at hn
  exact hn.1.1.1.1.2.1

private theorem classId_exists_of_mem {model : Model} (h : ModelWellFormed model)
    {declaration : Class} (hd : declaration ∈ model.classes) :
    ∃ id, classId model declaration.alias = .ok id := by
  obtain ⟨index, hi⟩ := exists_resolveIndex_of_mem_of_nodup
    (kind := "class") (classAliases_nodup h)
    (List.mem_map.mpr ⟨declaration, hd, rfl⟩)
  exact ⟨⟨index⟩, by simp [classId, hi, Except.map]⟩

private theorem bindClassEntry_directSuper {model : Model} {source : Class}
    {index : Nat} {target : ClassDecl}
    (hbind : bindClassEntry model (source, index) = .ok target)
    {superName : Name} (hsource : superName ∈ source.directSupers)
    {superId : ClassId} (hresolve : classId model superName = .ok superId) :
    superId ∈ target.directSupers := by
  unfold bindClassEntry at hbind
  cases hq : checkQualification source.alias source.package <;>
    cases hp : optionalPackage model source.package <;>
    cases hs : source.directSupers.mapM (classId model) <;>
    simp [hq, hp, hs, Bind.bind, Except.bind, pure, Except.pure] at hbind
  subst target
  obtain ⟨translated, ht, hb⟩ := mapM_ok_source hs hsource
  have : translated = superId := Except.ok.inj (hb.symm.trans hresolve)
  simpa [this] using ht

/-- Symbolic ancestor paths translate to stored superclass paths under the actual
class allocation. -/
theorem classAncestor_to_storedClassPath {model : Model} {schema : Schema}
    (hwell : ModelWellFormed model) (allocation : ModelAllocation model schema)
    {subName superName : Name} (path : ClassAncestor model subName superName)
    {subId superId : ClassId}
    (hsub : classId model subName = .ok subId)
    (hsuper : classId model superName = .ok superId) :
    StoredPath (ClassDirectSuperEdge schema) subId superId := by
  induction path generalizing subId superId
  · have hid : subId = superId := Except.ok.inj (hsub.symm.trans hsuper)
    subst superId
    exact .refl subId
  · rename_i hedge ih
    obtain ⟨sourceClass, hsourceClass, halias, hsourceSuper⟩ := hedge
    obtain ⟨middleId, hmiddle⟩ := classId_exists_of_mem hwell hsourceClass
    rw [halias] at hmiddle
    have prefixTarget := ih hsub hmiddle
    obtain ⟨allocatedSource, targetClass, hs, hsa, ht, htid, hentry⟩ :=
      allocation.classForId hmiddle
    have hsame : allocatedSource = sourceClass := by
      apply uniqueBy_eq_of_mem Class.alias
        (show uniqueBy Class.alias model.classes from classAliases_nodup hwell)
        hs hsourceClass
      exact hsa.trans halias.symm
    subst allocatedSource
    have htargetSuper := bindClassEntry_directSuper hentry hsourceSuper hsuper
    exact .step prefixTarget ⟨targetClass, ht, htid, htargetSuper⟩

/-- Successful model binding preserves every symbolic subtype relation.  The
proof uses model well-formedness and allocation carrier resolution, not target
schema well-formedness. -/
theorem subtypeBindingPreserved_of_bindModel {model : Model} {schema : Schema}
    (hwell : ModelWellFormed model) (hbind : bindModel model = .ok schema) :
    SubtypeBindingPreserved model schema := by
  intro subName superName subId superId hsub hsuper path
  have allocation := modelAllocation_of_bindModel hbind
  have hstart := mem_classUniverse_of_classDecls_ne_nil (allocation.classResolved hsub)
  exact storedClassPath_isSubtype_of_supersResolved allocation.supersResolved hstart
    (classAncestor_to_storedClassPath hwell allocation path hsub hsuper)

/-- Value typing preservation with the inheritance premise discharged from source
model well-formedness and the actual successful model binding. -/
theorem sourceValueMatches_to_valueMatches_of_modelWellFormed
    {model : Model} {snapshot : Instance} {schema : Schema} {target : Snapshot}
    (hwell : ModelWellFormed model)
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model snapshot = .ok target)
    {sourceType : Source.ValueType} {targetType : VLMOF.ValueType}
    {sourceValue : Source.Value} {targetValue : VLMOF.Value}
    (htype : bindType model sourceType = .ok targetType)
    (hvalue : ValueBinds model snapshot sourceValue targetValue)
    (hsource : sourceValueMatches model snapshot sourceType sourceValue) :
    valueMatches schema target targetType targetValue := by
  have hpremise : ValueTypingSubtypePremise model schema sourceType := by
    cases sourceType with
    | boolean => trivial
    | integer => trivial
    | string => trivial
    | enumeration _ => trivial
    | reference _ => exact subtypeBindingPreserved_of_bindModel hwell hmodel
  exact sourceValueMatches_to_valueMatches hmodel hinstance hpremise htype hvalue hsource

end VLMOF.Source
