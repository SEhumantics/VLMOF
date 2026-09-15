import VLMOF.Checker.Basic

/-! Diagnostics report failed named checks. They do not promise a minimal set of
causes or repair suggestions, nor do they classify unsupported parser/adapter input. -/
namespace VLMOF

/-- A filtered diagnostic list is empty exactly when all underlying named checks pass.
This private helper is shared by schema and snapshot diagnostics. -/
private theorem diagnostics_empty_iff (checks : List (String × Bool))
    (tag : String → Diagnostic) :
    (checks.filterMap fun x => if x.2 then none else some (tag x.1)) = [] ↔
      checks.all (fun x => x.2) = true := by
  simp [List.filterMap_eq_nil_iff, List.all_eq_true]

/-- Schema diagnostics are empty exactly when executable schema acceptance succeeds. -/
theorem schemaDiagnostics_empty_iff (s : Schema) :
    schemaDiagnostics s = [] ↔ checkSchema s = true := by
  exact diagnostics_empty_iff (schemaFieldChecks s) Diagnostic.schema

/-- Snapshot diagnostics are empty exactly when executable snapshot acceptance
succeeds. -/
theorem snapshotDiagnostics_empty_iff (s : Schema) (m : Snapshot) :
    snapshotDiagnostics s m = [] ↔ checkSnapshot s m = true := by
  exact diagnostics_empty_iff (snapshotFieldChecks s m) Diagnostic.snapshot

/-- A tagged diagnostic is present exactly when its named field occurs with result
`false`; injectivity of the tag recovers the field label. -/
private theorem diagnostic_mem_iff (checks : List (String × Bool))
    (tag : String → Diagnostic) (hinj : ∀ a b, tag a = tag b → a = b) (field : String) :
    tag field ∈ (checks.filterMap fun x => if x.2 then none else some (tag x.1)) ↔
      (field, false) ∈ checks := by
  constructor
  · intro h
    obtain ⟨⟨label, result⟩, hm, he⟩ := List.mem_filterMap.mp h
    cases result with
    | true => simp at he
    | false =>
      have hl : label = field := hinj label field (by simpa using he)
      simpa [hl] using hm
  · intro hm
    exact List.mem_filterMap.mpr ⟨(field, false), hm, rfl⟩

/-- Membership of a schema diagnostic identifies the corresponding failed named
schema check. -/
theorem schemaDiagnostic_mem_iff (s : Schema) (field : String) :
    Diagnostic.schema field ∈ schemaDiagnostics s ↔ (field, false) ∈ schemaFieldChecks s := by
  exact diagnostic_mem_iff _ Diagnostic.schema (fun _ _ h => Diagnostic.schema.inj h) field

/-- Membership of a snapshot diagnostic identifies the corresponding failed named
snapshot check. -/
theorem snapshotDiagnostic_mem_iff (s : Schema) (m : Snapshot) (field : String) :
    Diagnostic.snapshot field ∈ snapshotDiagnostics s m ↔ (field, false) ∈ snapshotFieldChecks s m := by
  exact diagnostic_mem_iff _ Diagnostic.snapshot (fun _ _ h => Diagnostic.snapshot.inj h) field

end VLMOF
