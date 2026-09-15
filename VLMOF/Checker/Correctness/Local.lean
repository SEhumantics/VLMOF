import VLMOF.Checker.Basic
import VLMOF.Model.Reachability.Containment

namespace VLMOF

theorem oppositeCountsForB_eq (m : Snapshot) (p q : PropertyId) :
    oppositeCountsForB m p q = (m.objects.all fun x => m.objects.all fun y =>
      decide ((m.occurrences x.id p).count (.reference y.id) =
        (m.occurrences y.id q).count (.reference x.id))) := by
  simp [oppositeCountsForB, List.all_map, Function.comp_def]

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

theorem containmentForB_eq_true (s : Schema) (m : Snapshot) (source : ObjectId) :
    containmentForB s m source = true ↔
      ∀ child, compositeEdge s m source child → ¬ compositeReachable s m child source := by
  constructor
  · intro h child edge reachable
    have member : child ∈ outgoingComposite s m [source] :=
      (outgoingComposite_spec s m [source] child).mpr ⟨source, by simp, edge⟩
    have tested := (List.all_eq_true.mp h) child member
    have positive := (compositeReachableB_eq_true s m child source).mpr reachable
    simp [positive] at tested
  · intro h
    apply List.all_eq_true.mpr
    intro child member
    obtain ⟨src, hsrc, edge⟩ := (outgoingComposite_spec s m [source] child).mp member
    simp only [List.mem_singleton] at hsrc
    subst src
    have hn : compositeReachableB s m child source ≠ true := by
      intro hr
      exact h child edge ((compositeReachableB_eq_true s m child source).mp hr)
    cases hr : compositeReachableB s m child source <;> simp_all

end VLMOF
