import VLMOF.Checker.Correctness.Schema
import VLMOF.Checker.Correctness.Snapshot
import VLMOF.Checker.Correctness.Diagnostics

/-!
# Public checker correctness interface

Clients normally import this module. It composes schema, snapshot, and diagnostic
reflection into the three acceptance equivalences below.
-/

namespace VLMOF

/-- Executable snapshot acceptance is exactly declarative conformance, for every
represented schema and snapshot, without a prevalidated-input assumption. -/
theorem checkSnapshot_iff (s : Schema) (m : Snapshot) :
    checkSnapshot s m = true ↔ SnapshotConforms s m :=
  checkSnapshot_iff_of_schema s m (checkSchema_iff s)

/-- Having no schema diagnostics is equivalent to declarative schema well-formedness,
by transitivity through `checkSchema`. -/
theorem schemaDiagnostics_empty_iff_wellFormed (s : Schema) :
    schemaDiagnostics s = [] ↔ SchemaWellFormed s :=
  (schemaDiagnostics_empty_iff s).trans (checkSchema_iff s)

/-- Having no snapshot diagnostics is equivalent to declarative conformance, by
transitivity through executable snapshot acceptance. -/
theorem snapshotDiagnostics_empty_iff_conforms (s : Schema) (m : Snapshot) :
    snapshotDiagnostics s m = [] ↔ SnapshotConforms s m :=
  (snapshotDiagnostics_empty_iff s m).trans (checkSnapshot_iff s m)

end VLMOF
