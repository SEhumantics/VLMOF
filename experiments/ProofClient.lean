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

#print axioms observations_agree
end Evaluation
