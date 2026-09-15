import VLMOF

namespace Evaluation
open VLMOF

/-- A client can treat observations as a partial function after establishing
conformance: two rows for one object/property cannot disagree on occurrence order. -/
theorem observations_agree {s : Schema} {m : Snapshot}
    (valid : SnapshotConforms s m) {left right : Observation}
    (hl : left ∈ m.observations) (hr : right ∈ m.observations)
    (object : left.object = right.object) (property : left.property = right.property) :
    left.occurrences = right.occurrences := by
  have key : left.key = right.key := by simp [Observation.key, object, property]
  exact congrArg Observation.occurrences (observation_key_injective valid hl hr key)

/-- An author considering the edit "add the same `y` to `x.forward` twice" can
rule out *every* candidate snapshot of this metamodel.  The forward property is
expressly non-unique.  Rejection follows instead from the association's
reciprocity and the reverse property's upper-one bound, so this applies to an
arbitrary future snapshot rather than inspecting one stored occurrence list. -/
theorem repeated_forward_reference_rejected (m : Snapshot)
    (hx : SemanticExample.oneLink.objects[0] ∈ m.objects)
    (hy : SemanticExample.oneLink.objects[1] ∈ m.objects)
    (hrepeated : 2 ≤ (m.occurrences SemanticExample.x SemanticExample.forward).count
      (.reference SemanticExample.y)) :
    ¬ SnapshotConforms SemanticExample.interactionSchema m := by
  intro hconforms
  have hbound := opposite_upper_one_forces_reference_count_le_one
    (h := hconforms)
    (a := SemanticExample.interactionSchema.associations[0])
    (ha := by simp [SemanticExample.interactionSchema])
    (p := SemanticExample.forward) (q := SemanticExample.reverse)
    (hends := by rfl)
    (qd := SemanticExample.interactionSchema.properties[1])
    (hqd := by simp [SemanticExample.interactionSchema])
    (hqId := by rfl) (hqUpper := by rfl)
    (x := SemanticExample.oneLink.objects[0])
    (y := SemanticExample.oneLink.objects[1])
    (hx := hx)
    (hy := hy)
    (hqApplicable := by decide)
  have hbound' :
      (m.occurrences SemanticExample.x SemanticExample.forward).count
          (.reference SemanticExample.y) ≤ 1 := by
    simpa [SemanticExample.oneLink] using hbound
  omega

/-- The stored edit witness duplicates the non-unique forward reference while
leaving one reverse occurrence.  The universal theorem diagnoses why no
conforming completion of this precise snapshot is possible. -/
theorem duplicated_forward_edit_rejected :
    ¬ SnapshotConforms SemanticExample.interactionSchema SemanticExample.withoutReciprocity := by
  apply repeated_forward_reference_rejected
  · simp [SemanticExample.withoutReciprocity, SemanticExample.oneLink]
  · simp [SemanticExample.withoutReciprocity, SemanticExample.oneLink]
  · decide

#print axioms observations_agree
#print axioms repeated_forward_reference_rejected
#print axioms duplicated_forward_edit_rejected
end Evaluation
