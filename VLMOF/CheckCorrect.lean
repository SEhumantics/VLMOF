import VLMOF.Check

namespace VLMOF

theorem valueMatchesB_eq_true (s : Schema) (m : Snapshot) (t : ValueType) (v : Value) :
    valueMatchesB s m t v = true ↔ valueMatches s m t v := by
  cases t <;> cases v <;>
    simp [valueMatchesB, valueMatches, List.any_eq_true]

theorem compositeEdgeB_eq_true (s : Schema) (m : Snapshot) (src dst : ObjectId) :
    compositeEdgeB s m src dst = true ↔ compositeEdge s m src dst := by
  simp [compositeEdgeB, compositeEdge, List.any_eq_true]
  constructor
  · rintro ⟨a, ha, hao, p, hp, ⟨⟨hpid, hagg⟩, hv⟩⟩
    exact ⟨a, ha, hao, p, hp, hpid, hagg, hv⟩
  · rintro ⟨a, ha, hao, p, hp, hpid, hagg, hv⟩
    exact ⟨a, ha, hao, p, hp, ⟨⟨hpid, hagg⟩, hv⟩⟩

theorem compositeReachableB_eq_true (s : Schema) (m : Snapshot) (src dst : ObjectId) :
    compositeReachableB s m src dst = true ↔ compositeReachable s m src dst := by
  simp [compositeReachableB, compositeReachable, iterateClosureFast_eq]

end VLMOF
