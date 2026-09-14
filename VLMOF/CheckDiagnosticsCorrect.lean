import VLMOF.Check

/-! Diagnostics report failed named checks. They do not promise a minimal set of
causes or repair suggestions, nor do they classify unsupported parser/adapter input. -/
namespace VLMOF

private theorem diagnostics_empty_iff (checks : List (String × Bool))
    (tag : String → Diagnostic) :
    (checks.filterMap fun x => if x.2 then none else some (tag x.1)) = [] ↔
      checks.all (fun x => x.2) = true := by
  simp [List.filterMap_eq_nil_iff, List.all_eq_true]

theorem schemaDiagnostics_empty_iff (s : Schema) :
    schemaDiagnostics s = [] ↔ checkSchema s = true := by
  exact diagnostics_empty_iff (schemaFieldChecks s) Diagnostic.schema

theorem snapshotDiagnostics_empty_iff (s : Schema) (m : Snapshot) :
    snapshotDiagnostics s m = [] ↔ checkSnapshot s m = true := by
  exact diagnostics_empty_iff (snapshotFieldChecks s m) Diagnostic.snapshot

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

theorem schemaDiagnostic_mem_iff (s : Schema) (field : String) :
    Diagnostic.schema field ∈ schemaDiagnostics s ↔ (field, false) ∈ schemaFieldChecks s := by
  exact diagnostic_mem_iff _ Diagnostic.schema (fun _ _ h => Diagnostic.schema.inj h) field

theorem snapshotDiagnostic_mem_iff (s : Schema) (m : Snapshot) (field : String) :
    Diagnostic.snapshot field ∈ snapshotDiagnostics s m ↔ (field, false) ∈ snapshotFieldChecks s m := by
  exact diagnostic_mem_iff _ Diagnostic.snapshot (fun _ _ h => Diagnostic.snapshot.inj h) field

end VLMOF
