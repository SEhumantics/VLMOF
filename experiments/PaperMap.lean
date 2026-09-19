import VLMOF

/-!
# Paper-to-Lean map, checked by Lean

The manuscript is written without Lean names. This file names the declaration
behind each numbered definition and theorem, so that renaming or weakening one
of them breaks the map. The `example`s restate Theorems 1 and 2 and Equation (2)
in the paper's shape and prove them by the library results. The `#print axioms`
lines show the axioms behind them. Run from the repository root after `lake build`:

    lake env lean experiments/PaperMap.lean

The prose version of this map is `docs/paper-map.md`.
-/

open VLMOF

-- Definition 1 (Schema) and Definition 2 (Snapshot): raw records, identities by value.
#check @Schema
#check @Snapshot
#check @Observation
#check @Value
-- Definition 3 (Lookup L_M(o,p)): concatenation of every matching row, in order.
#check @Snapshot.occurrences
-- Applicability app(c), computed through the reflexive ancestor closure.
#check @Schema.ancestors
#check @Schema.applicableProperty
-- Definition 4 (W1–W6) and Definition 5 (C1–C6); C(S,M) includes W(S).
#check @SchemaWellFormed
#check @SnapshotConforms
#check @SnapshotConforms.schema
-- C6: one parent, one active container end, no containment cycle.
#check @SingleContainer
#check @SingleContainerProperty
#check @compositeReachable
-- The executable checker.
#check @checkSchema
#check @checkSnapshot
-- Definitions 6–8: source documents, lexical admissibility, elaboration, meaning.
#check @Source.Document
#check @Source.LexicallyAdmissible
#check @Source.elaborate
#check @Source.SourceSatisfies

/-- Theorem 1 (checker correctness), Equation (1), for every raw schema and snapshot. -/
example (s : Schema) (m : Snapshot) : checkSnapshot s m = true ↔ SnapshotConforms s m :=
  checkSnapshot_iff s m

/-- Theorem 2 (i): a document satisfying its meaning elaborates successfully. -/
example (d : Source.Document) (h : Source.SourceSatisfies d) :
    ∃ s m, Source.elaborate d = .ok (s, m) :=
  Source.elaborate_complete h

/-- Theorem 2 (ii): for a lexically admissible document, meaning and Core
conformance of the actual elaboration result coincide. -/
example (d : Source.Document) (s : Schema) (m : Snapshot)
    (hlex : Source.LexicallyAdmissible d) (he : Source.elaborate d = .ok (s, m)) :
    Source.SourceSatisfies d ↔ SnapshotConforms s m :=
  Source.sourceSatisfies_iff_conforms hlex he

/-- Equation (2): meaning coincides with acceptance of the elaborated pair. -/
example (d : Source.Document) (s : Schema) (m : Snapshot)
    (hlex : Source.LexicallyAdmissible d) (he : Source.elaborate d = .ok (s, m)) :
    Source.SourceSatisfies d ↔ checkSnapshot s m = true :=
  Source.sourceSatisfies_iff_accepted hlex he

#print axioms checkSnapshot_iff
#print axioms Source.elaborate_complete
#print axioms Source.sourceSatisfies_iff_conforms
#print axioms Source.sourceSatisfies_iff_accepted
#print axioms Source.sourceSatisfies_iff_exists_accepted
