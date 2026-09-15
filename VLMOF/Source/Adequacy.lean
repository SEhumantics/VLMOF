import VLMOF.Source.Correctness.SchemaReflection
import VLMOF.Source.Correctness.SnapshotReflection

/-!
# Source satisfaction and executable acceptance

This connects independently defined symbolic satisfaction to actual elaboration.
Lexical admissibility is explicit: the raw binder only checks nonempty alias
components, whereas source names also require XML-valid characters. No parser
correctness, source satisfaction, or target well-formedness is hidden in this
boundary condition. Source display names are reflected from target conformance.

The results are conditional in two distinct ways.  Equivalences for a fixed Core
pair assume that elaboration produced that pair, and reflection additionally
assumes lexical admissibility because the executable binder checks fewer
characters than `NameValid`.  The final existential theorem discharges elaboration
success from source satisfaction but retains that explicit lexical boundary in
the reverse direction.
-/
namespace VLMOF.Source

/-- The exact lexical premise missing from successful binding: all declaration
and object aliases satisfy the source `NameValid` predicate, including the shared
Core valid-string rule for every component. -/
structure LexicallyAdmissible (document : Document) : Prop where
  modelAliases : ∀ n ∈ aliases document.model, NameValid n
  objectAliases : ∀ object ∈ document.snapshot.objects, NameValid object.alias

/-- Invert a successful whole-document elaboration into the model and instance
binding equations consumed by preservation and reflection theorems. -/
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

/-- For the actual elaboration result, source satisfaction and Core snapshot
conformance coincide under the explicit lexical premise.  The forward implication
uses preservation; the reverse implication combines schema and snapshot reflection. -/
theorem sourceSatisfies_iff_conforms
    {document : Document} {schema : Schema} {snapshot : Snapshot}
    (hlex : LexicallyAdmissible document)
    (helab : elaborate document = .ok (schema, snapshot)) :
    SourceSatisfies document ↔ SnapshotConforms schema snapshot :=
  ⟨fun hs => snapshotConforms_of_sourceSatisfies_of_elaborate hs helab,
    sourceSatisfies_of_conforms hlex helab⟩

/-- Replace target conformance in adequacy by the executable snapshot checker,
using the checker's unconditional correctness theorem. -/
theorem sourceSatisfies_iff_accepted
    {document : Document} {schema : Schema} {snapshot : Snapshot}
    (hlex : LexicallyAdmissible document)
    (helab : elaborate document = .ok (schema, snapshot)) :
    SourceSatisfies document ↔ checkSnapshot schema snapshot = true :=
  (sourceSatisfies_iff_conforms hlex helab).trans (checkSnapshot_iff schema snapshot).symm

/-- Characterize source satisfaction by existence of an elaborated pair accepted
by the executable checker.  Completeness constructs the forward witness; the
reverse implication remains conditional on lexical admissibility. -/
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
