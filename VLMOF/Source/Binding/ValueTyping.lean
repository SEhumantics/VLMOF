import VLMOF.Source.Correctness.SchemaPreservation
import VLMOF.Source.Correctness.Observations

/-!
# Value typing across binding

Primitive and enumeration typing follows entirely from successful declaration,
snapshot, type, and value binding.  Reference typing additionally needs the one
inheritance fact not yet supplied by schema allocation: a symbolic ancestor path
between successfully resolved class aliases becomes target `isSubtype`.

Private helpers recover the exact source rows selected by unique aliases.  The
enumeration lemma then follows the allocated literal row; the main theorem handles
primitive cases directly and uses `SubtypeBindingPreserved` only for references.
-/
namespace VLMOF.Source

/-- The precise inheritance-only premise needed to transport reference values
from source typing to target typing.  It does not assume value typing or target
schema well-formedness. -/
def SubtypeBindingPreserved (model : Model) (schema : Schema) : Prop :=
  ∀ {subName superName : Name} {subId superId : ClassId},
    classId model subName = .ok subId →
    classId model superName = .ok superId →
    ClassAncestor model subName superName →
    schema.isSubtype subId superId

/-- Only reference-typed values consume the subtype transport premise. -/
def ValueTypingSubtypePremise (model : Model) (schema : Schema) :
    Source.ValueType → Prop
  | .reference _ => SubtypeBindingPreserved model schema
  | _ => True

private theorem uniqueAliasAt_entry_getElem {α : Type} {key : α → Name}
    {entries : List α} {name : Name} {index : Nat}
    (hunique : UniqueAliasAt (entries.map key) name index)
    {entry : α} (hmem : entry ∈ entries) (hkey : key entry = name) :
    entries[index]? = some entry := by
  obtain ⟨other, hother⟩ := List.mem_iff_getElem?.mp hmem
  have hmap : (entries.map key)[other]? = some name := by
    simp [List.getElem?_map, hother, hkey]
  have hi := hunique.2 other hmap
  subst other
  exact hother

private theorem enumerationId_of_uniqueAliasAt {model : Model} {name : Name}
    {id : EnumerationId}
    (h : UniqueAliasAt (model.enumerations.map Enumeration.alias) name id.val) :
    enumerationId model name = .ok id := by
  have hr := (resolveIndex_iff_uniqueAliasAt "enumeration"
    (model.enumerations.map Enumeration.alias) name id.val).mpr h
  cases id
  simp [enumerationId, hr, Except.map]

private theorem literalId_of_uniqueAliasAt {model : Model} {name : Name}
    {id : LiteralId}
    (h : UniqueAliasAt (model.literals.map Literal.alias) name id.val) :
    literalId model name = .ok id := by
  have hr := (resolveIndex_iff_uniqueAliasAt "literal"
    (model.literals.map Literal.alias) name id.val).mpr h
  cases id
  simp [literalId, hr, Except.map]

private theorem bindType_enumeration_iff (model : Model) (name : Name) (id : EnumerationId) :
    bindType model (.enumeration name) = .ok (.enumeration id) ↔
      enumerationId model name = .ok id := by
  cases h : enumerationId model name <;>
    simp [bindType, h, Functor.map, Except.map]

private theorem bindType_reference_iff (model : Model) (name : Name) (id : ClassId) :
    bindType model (.reference name) = .ok (.reference id) ↔
      classId model name = .ok id := by
  cases h : classId model name <;>
    simp [bindType, h, Functor.map, Except.map]

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

/-- The target object allocated for a uniquely bound source alias has exactly
the resolved source classifier. -/
theorem boundObject_classifierForId {model : Model} {snapshot : Instance}
    {target : Snapshot} (hbind : bindInstance model snapshot = .ok target)
    {name : Name} {id : ObjectId}
    (hunique : UniqueAliasAt (snapshot.objects.map Object.alias) name id.val)
    {source : Object} (hsource : source ∈ snapshot.objects) (halias : source.alias = name) :
    ∃ classifier translated,
      classId model source.classifier = .ok classifier ∧
      translated ∈ target.objects ∧ translated.id = id ∧
      translated.classifier = classifier := by
  have hget := uniqueAliasAt_entry_getElem hunique hsource halias
  obtain ⟨classifier, hc, ht⟩ := boundObject_at_index hbind hget
  let translated : ObjectDecl := { id := ⟨id.val⟩, classifier }
  have hm : translated ∈ target.objects :=
    List.mem_iff_getElem?.mpr ⟨id.val, ht⟩
  refine ⟨classifier, translated, hc, hm, ?_, rfl⟩
  cases id
  rfl

/-- Enumeration typing is preserved using the literal row allocated by the
successful model binder. -/
theorem enumerationValueMatches_of_binding {model : Model} {snapshot : Instance}
    {schema : Schema} {target : Snapshot} (hmodel : bindModel model = .ok schema)
    {expected actual literal : Name} {expectedId actualId : EnumerationId}
    {literalId' : LiteralId}
    (htype : bindType model (.enumeration expected) = .ok (.enumeration expectedId))
    (hvalue : ValueBinds model snapshot (.enumeration actual literal)
      (.enumeration actualId literalId'))
    (hsource : sourceValueMatches model snapshot (.enumeration expected)
      (.enumeration actual literal)) :
    valueMatches schema target
      (.enumeration expectedId) (.enumeration actualId literalId') := by
  rcases hsource with ⟨rfl, declaration, hd, halias, henum⟩
  have heid := (bindType_enumeration_iff model expected expectedId).mp htype
  have hae := enumerationId_of_uniqueAliasAt hvalue.1
  have hid : expectedId = actualId := Except.ok.inj (heid.symm.trans hae)
  have hlid := literalId_of_uniqueAliasAt hvalue.2
  have allocation := modelAllocation_of_bindModel hmodel
  rcases allocation.literalForId hlid with
    ⟨sourceLiteral, targetLiteral, hs, hsa, ht, hti, hentry⟩
  have hsourceLiteral : sourceLiteral = declaration := by
    apply Option.some.inj
    exact (uniqueAliasAt_entry_getElem hvalue.2 hs hsa).symm.trans
      (uniqueAliasAt_entry_getElem hvalue.2 hd halias)
  subst sourceLiteral
  have htargetEnum := bindLiteralEntry_enumeration hentry
  rw [henum] at htargetEnum
  have hte : targetLiteral.enumeration = expectedId :=
    Except.ok.inj (htargetEnum.symm.trans heid)
  exact ⟨hid, targetLiteral, ht, hti, hte⟩

/-- Source value typing is preserved by the actual binders.  The only external
semantic premise is `SubtypeBindingPreserved`, used solely in the reference case. -/
theorem sourceValueMatches_to_valueMatches {model : Model} {snapshot : Instance}
    {schema : Schema} {target : Snapshot}
    (hmodel : bindModel model = .ok schema)
    (hinstance : bindInstance model snapshot = .ok target)
    {sourceType : Source.ValueType} {targetType : VLMOF.ValueType}
    {sourceValue : Source.Value} {targetValue : VLMOF.Value}
    (hsubtype : ValueTypingSubtypePremise model schema sourceType)
    (htype : bindType model sourceType = .ok targetType)
    (hvalue : ValueBinds model snapshot sourceValue targetValue)
    (hsource : sourceValueMatches model snapshot sourceType sourceValue) :
    valueMatches schema target targetType targetValue := by
  cases sourceType with
  | boolean =>
      cases sourceValue <;> simp [sourceValueMatches] at hsource
      rename_i value
      cases targetType <;> cases targetValue <;>
        simp_all [bindType, ValueBinds, valueMatches, pure, Except.pure]
  | integer =>
      cases sourceValue <;> simp [sourceValueMatches] at hsource
      rename_i value
      cases targetType <;> cases targetValue <;>
        simp_all [bindType, ValueBinds, valueMatches, pure, Except.pure]
  | string =>
      cases sourceValue <;> simp [sourceValueMatches] at hsource
      rename_i value
      cases targetType <;> cases targetValue <;>
        simp_all [bindType, ValueBinds, valueMatches, pure, Except.pure]
  | enumeration expected =>
      cases sourceValue <;> simp [sourceValueMatches] at hsource
      rename_i actual literal
      cases he : enumerationId model expected with
      | error error => simp [bindType, he, Functor.map, Except.map] at htype
      | ok expectedId =>
          have htt : targetType = .enumeration expectedId := by
            have hb : bindType model (.enumeration expected) =
                .ok (.enumeration expectedId) := by
              simp [bindType, he, Functor.map, Except.map]
            exact Except.ok.inj (htype.symm.trans hb)
          subst targetType
          cases targetValue with
          | boolean _ => simp [ValueBinds] at hvalue
          | integer _ => simp [ValueBinds] at hvalue
          | string _ => simp [ValueBinds] at hvalue
          | reference _ => simp [ValueBinds] at hvalue
          | enumeration actualId literalId' =>
              exact enumerationValueMatches_of_binding hmodel htype hvalue hsource
  | reference expected =>
      cases sourceValue <;> simp [sourceValueMatches] at hsource
      rename_i object
      cases hc : classId model expected with
      | error error => simp [bindType, hc, Functor.map, Except.map] at htype
      | ok expectedId =>
          have htt : targetType = .reference expectedId := by
            have hb : bindType model (.reference expected) =
                .ok (.reference expectedId) := by
              simp [bindType, hc, Functor.map, Except.map]
            exact Except.ok.inj (htype.symm.trans hb)
          subst targetType
          cases targetValue with
          | boolean _ => simp [ValueBinds] at hvalue
          | integer _ => simp [ValueBinds] at hvalue
          | string _ => simp [ValueBinds] at hvalue
          | enumeration _ _ => simp [ValueBinds] at hvalue
          | reference objectId' =>
              rcases hsource with ⟨sourceObject, hobject, halias, hancestor⟩
              rcases boundObject_classifierForId hinstance hvalue hobject halias with
                ⟨classifier, translated, hclassifierId, ht, hid, hclassifier⟩
              change SubtypeBindingPreserved model schema at hsubtype
              exact ⟨translated, ht, hid,
                hclassifier ▸ hsubtype hclassifierId hc hancestor⟩

end VLMOF.Source
