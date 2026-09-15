import VLMOF.Checker.Basic
import VLMOF.Model.Reachability.Containment

/-!
# Local checker reflection lemmas

Each theorem relates one executable Boolean helper to the declarative predicate it
implements. Keeping these local bridges separate makes the later whole-checker proofs
read as assembly of already justified fields.
-/

namespace VLMOF

/-- Comparing with one representative establishes agreement for every pair.
The reverse direction uses the first element as one of those pairs. -/
theorem keysAgree_iff {α κ : Type} [BEq κ] [LawfulBEq κ]
    (key : α → κ) (xs : List α) :
    keysAgree key xs = true ↔ ∀ a ∈ xs, ∀ b ∈ xs, key a = key b := by
  cases xs with
  | nil => simp [keysAgree]
  | cons first rest =>
    simp only [keysAgree, List.all_eq_true, beq_iff_eq]
    constructor
    · intro h a ha b hb
      have hfirst : ∀ z ∈ first :: rest, key first = key z := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · rfl
        · exact h z hz
      exact (hfirst a ha).symm.trans (hfirst b hb)
    · intro h b hb
      exact h first (by simp) b (by simp [hb])

/-- The optimized parent test is equivalent to the pairwise semantic statement
on all raw observations, with no conformance assumption. -/
theorem singleContainerB_iff (s : Schema) (m : Snapshot) (target : ObjectId) :
    singleContainerB s m target = true ↔ SingleContainer s m target := by
  rw [singleContainerB, keysAgree_iff]
  constructor
  · intro h a ha b hb hca hcb
    exact h a (List.mem_filter.mpr ⟨ha, hca⟩) b (List.mem_filter.mpr ⟨hb, hcb⟩)
  · intro h a ha b hb
    obtain ⟨ha, hca⟩ := List.mem_filter.mp ha
    obtain ⟨hb, hcb⟩ := List.mem_filter.mp hb
    exact h a ha b hb hca hcb

/-- The active-role filter preserves precisely the source clause's nonempty
container ends; raw duplicates and malformed rows remain visible to other checks. -/
theorem singleContainerPropertyB_iff (s : Schema) (m : Snapshot) (target : ObjectId) :
    singleContainerPropertyB s m target = true ↔ SingleContainerProperty s m target := by
  rw [singleContainerPropertyB, keysAgree_iff]
  have member (o : Observation) :
      o ∈ m.observations.filter (fun o => o.object == target &&
        containerProperty s o.property && !o.occurrences.isEmpty) ↔
      o ∈ m.observations ∧ o.object = target ∧
        containerProperty s o.property = true ∧ o.occurrences ≠ [] := by
    simp [List.mem_filter, Bool.and_eq_true, List.isEmpty_eq_false_iff, and_assoc]
  constructor
  · intro h a ha b hb hao hbo hca hcb hna hnb
    exact h a ((member a).mpr ⟨ha, hao, hca, hna⟩)
      b ((member b).mpr ⟨hb, hbo, hcb, hnb⟩)
  · intro h a ha b hb
    obtain ⟨ha, hao, hca, hna⟩ := (member a).mp ha
    obtain ⟨hb, hbo, hcb, hnb⟩ := (member b).mp hb
    exact h a ha b hb hao hbo hca hcb hna hnb

/-- Expands the cached opposite-count implementation into the direct all-pairs
comparison used by `SnapshotConforms.oppositeCounts`. -/
theorem oppositeCountsForB_eq (m : Snapshot) (p q : PropertyId) :
    oppositeCountsForB m p q = (m.objects.all fun x => m.objects.all fun y =>
      decide ((m.occurrences x.id p).count (.reference y.id) =
        (m.occurrences y.id q).count (.reference x.id))) := by
  simp [oppositeCountsForB, List.all_map, Function.comp_def]

/-- Boolean value typing is equivalent to declarative `valueMatches`; proof is by
cases on both the expected type and supplied value. -/
theorem valueMatchesB_eq_true (s : Schema) (m : Snapshot) (t : ValueType) (v : Value) :
    valueMatchesB s m t v = true ↔ valueMatches s m t v := by
  cases t <;> cases v <;>
    simp [valueMatchesB, valueMatches, List.any_eq_true]

/-- Boolean composite-edge recognition is equivalent to the existential observation
and property witnesses in `compositeEdge`. -/
theorem compositeEdgeB_eq_true (s : Schema) (m : Snapshot) (src dst : ObjectId) :
    compositeEdgeB s m src dst = true ↔ compositeEdge s m src dst := by
  simp [compositeEdgeB, compositeEdge, List.any_eq_true]
  constructor
  · rintro ⟨a, ha, hao, p, hp, ⟨⟨hpid, hagg⟩, hv⟩⟩
    exact ⟨a, ha, hao, p, hp, hpid, hagg, hv⟩
  · rintro ⟨a, ha, hao, p, hp, hpid, hagg, hv⟩
    exact ⟨a, ha, hao, p, hp, ⟨⟨hpid, hagg⟩, hv⟩⟩

/-- Early-stopping Boolean containment reachability agrees with the declarative
bounded closure, using `iterateClosureFast_eq`. -/
theorem compositeReachableB_eq_true (s : Schema) (m : Snapshot) (src dst : ObjectId) :
    compositeReachableB s m src dst = true ↔ compositeReachable s m src dst := by
  simp [compositeReachableB, compositeReachable, iterateClosureFast_eq]

/-- The local containment check succeeds exactly when no direct composite child can
reach its source. The proof uses the expansion specification in both directions. -/
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
