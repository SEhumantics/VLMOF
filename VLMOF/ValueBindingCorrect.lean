import VLMOF.BindingCorrect

namespace VLMOF.Source

/-- Meaning of a symbolic value under the declaration environments, independent
of executable binding. Primitive values are unchanged; references require unique
source aliases at the corresponding identity indices. -/
def ValueBinds (model : Model) (snapshot : Instance) : Source.Value → VLMOF.Value → Prop
  | .boolean a, .boolean b => a = b
  | .integer a, .integer b => a = b
  | .string a, .string b => a = b
  | .enumeration enum lit, .enumeration eid lid =>
      UniqueAliasAt (model.enumerations.map Enumeration.alias) enum eid.val ∧
      UniqueAliasAt (model.literals.map Literal.alias) lit lid.val
  | .reference object, .reference oid =>
      UniqueAliasAt (snapshot.objects.map Object.alias) object oid.val
  | _, _ => False

theorem bindValue_iff (model : Model) (snapshot : Instance)
    (source : Source.Value) (target : VLMOF.Value) :
    bindValue model snapshot source = .ok target ↔ ValueBinds model snapshot source target := by
  cases source with
  | boolean value => cases target <;> simp [bindValue, ValueBinds, pure, Except.pure]
  | integer value => cases target <;> simp [bindValue, ValueBinds, pure, Except.pure]
  | string value => cases target <;> simp [bindValue, ValueBinds, pure, Except.pure]
  | reference object =>
    have hrel : ∀ i, UniqueAliasAt (snapshot.objects.map Object.alias) object i ↔
        resolveIndex "object" (snapshot.objects.map Object.alias) object = .ok i :=
      fun i => (resolveIndex_iff_uniqueAliasAt _ _ _ i).symm
    cases h : resolveIndex "object" (snapshot.objects.map Object.alias) object <;>
      cases target <;>
      simp [bindValue, objectId, ValueBinds, hrel, h, Functor.map, Except.map]
    rename_i oid
    cases oid
    simp
  | enumeration enum lit =>
    have he : ∀ i, UniqueAliasAt (model.enumerations.map Enumeration.alias) enum i ↔
        resolveIndex "enumeration" (model.enumerations.map Enumeration.alias) enum = .ok i :=
      fun i => (resolveIndex_iff_uniqueAliasAt _ _ _ i).symm
    have hl : ∀ i, UniqueAliasAt (model.literals.map Literal.alias) lit i ↔
        resolveIndex "literal" (model.literals.map Literal.alias) lit = .ok i :=
      fun i => (resolveIndex_iff_uniqueAliasAt _ _ _ i).symm
    cases h₁ : resolveIndex "enumeration" (model.enumerations.map Enumeration.alias) enum <;>
      cases h₂ : resolveIndex "literal" (model.literals.map Literal.alias) lit <;>
      cases target <;>
      simp [bindValue, enumerationId, literalId, ValueBinds, he, hl, h₁, h₂,
        Except.map, Bind.bind, Except.bind, pure, Except.pure]
    rename_i eid lid
    cases eid
    cases lid
    simp

end VLMOF.Source


