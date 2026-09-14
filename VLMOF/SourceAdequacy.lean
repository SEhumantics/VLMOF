import VLMOF.SchemaReflectionCorrect
import VLMOF.SnapshotReflectionCorrect

/-!
# Source satisfaction and executable acceptance

This connects independently defined symbolic satisfaction to actual elaboration.
Lexical admissibility is explicit: the raw binder only checks nonempty alias
components, whereas source names also require XML-valid characters. No parser
correctness, source satisfaction, or target well-formedness is hidden in this
boundary condition. Source display names are reflected from target conformance.
-/
namespace VLMOF.Source

structure LexicallyAdmissible (document : Document) : Prop where
  modelAliases : ∀ n ∈ aliases document.model, NameValid n
  objectAliases : ∀ object ∈ document.snapshot.objects, NameValid object.alias

theorem elaborate_bindings {document : Document} {schema : Schema}
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
      cases heq
      exact ⟨rfl, rfl⟩

/-- Successful elaboration reflects every source conformance field under the
explicit lexical boundary, with no source model validity assumption. -/
theorem sourceSatisfies_of_conforms
    {document : Document} {schema : Schema} {snapshot : Snapshot}
    (hlex : LexicallyAdmissible document)
    (helab : elaborate document = .ok (schema, snapshot))
    (hconforms : SnapshotConforms schema snapshot) : SourceSatisfies document := by
  obtain ⟨hm, hi⟩ := elaborate_bindings helab
  have hw := modelWellFormed_of_bindModel hlex.modelAliases hm hconforms.schema
  exact sourceSatisfies_of_snapshotConforms_of_bindings hw hlex.objectAliases hm hi hconforms

/-- Noncircular source/Core adequacy for the actual elaboration result. -/
theorem sourceSatisfies_iff_conforms
    {document : Document} {schema : Schema} {snapshot : Snapshot}
    (hlex : LexicallyAdmissible document)
    (helab : elaborate document = .ok (schema, snapshot)) :
    SourceSatisfies document ↔ SnapshotConforms schema snapshot :=
  ⟨fun hs => snapshotConforms_of_sourceSatisfies_of_elaborate hs helab,
    sourceSatisfies_of_conforms hlex helab⟩

/-- The same equivalence composed with the unconditional executable checker theorem. -/
theorem sourceSatisfies_iff_accepted
    {document : Document} {schema : Schema} {snapshot : Snapshot}
    (hlex : LexicallyAdmissible document)
    (helab : elaborate document = .ok (schema, snapshot)) :
    SourceSatisfies document ↔ checkSnapshot schema snapshot = true :=
  (sourceSatisfies_iff_conforms hlex helab).trans (checkSnapshot_iff schema snapshot).symm

/-- This form includes elaboration success rather than assuming it. -/
theorem sourceSatisfies_iff_exists_accepted {document : Document}
    (hlex : LexicallyAdmissible document) :
    SourceSatisfies document ↔ ∃ schema snapshot,
      elaborate document = .ok (schema, snapshot) ∧ checkSnapshot schema snapshot = true := by
  constructor
  · intro hs
    obtain ⟨schema, snapshot, he, _, ha⟩ := elaborate_complete_and_snapshot_accepted hs
    exact ⟨schema, snapshot, he, ha⟩
  · rintro ⟨schema, snapshot, he, ha⟩
    exact (sourceSatisfies_iff_accepted hlex he).mpr ha

end VLMOF.Source
