import VLMOF.Checker.Correctness.Local

namespace VLMOF

private theorem guard_iff (p q : Prop) : (¬p ∨ q) ↔ (p → q) := by
  classical
  constructor
  · intro h hp; exact h.resolve_left (not_not_intro hp)
  · intro h; by_cases hp : p
    · exact Or.inr (h hp)
    · exact Or.inl hp

private theorem notB_eq_true (b : Bool) : (!b = true) ↔ ¬ (b = true) := by
  cases b <;> decide

private theorem bool_eq_decide (b : Bool) (p : Prop) [Decidable p] :
    b = decide p ↔ (b = true ↔ p) := by
  cases b <;> by_cases p <;> simp_all

theorem compositeEdge_target_mem {s : Schema} {m : Snapshot} {src dst : ObjectId}
    (h : compositeEdge s m src dst) : dst ∈ referenceTargets m := by
  obtain ⟨a, ha, _, p, _, _, _, hv⟩ := h
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  exact List.mem_filterMap.mpr ⟨.reference dst, hv, rfl⟩

private theorem finite_containment_iff (s : Schema) (m : Snapshot) :
    (∀ o ∈ m.objects, ∀ child ∈ referenceTargets m,
      compositeEdge s m o.id child → ¬ compositeReachable s m child o.id) ↔
    (∀ o ∈ m.objects, ∀ child,
      compositeEdge s m o.id child → ¬ compositeReachable s m child o.id) := by
  constructor
  · intro h o ho child he
    exact h o ho child (compositeEdge_target_mem he) he
  · intro h o ho child _ he
    exact h o ho child he

/-- Snapshot reflection, parameterized only by the separately proved schema checker
interface. No snapshot-validity assumption is required. -/
theorem checkSnapshot_iff_of_schema (s : Schema) (m : Snapshot)
    (hschema : checkSchema s = true ↔ SchemaWellFormed s) :
    checkSnapshot s m = true ↔ SnapshotConforms s m := by
  classical
  simp only [checkSnapshot, snapshotFieldChecks, oppositeCountsForB_eq, List.all_cons, List.all_nil,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true, bool_eq_decide, List.any_eq_true,
    valueMatchesB_eq_true, containmentForB_eq_true, hschema, and_true, guard_iff]

  constructor
  · rintro ⟨hs, hu, hk, hr, hc, he, hkr, ha, ht, hb, hn, ho, hi, hcy⟩
    refine ⟨hs, hu, hk, hr, hc, he, hkr, ha, ht, hb, ?_, ?_, hi, ?_⟩
    · intro o hom p hpm hap huniq
      exact (hn o hom p hpm).resolve_left (fun h => h hap huniq)
    · intro a ham p q heq x hx y hy
      have h := ho a ham x hx y hy
      simpa [heq] using h
    · exact hcy
  · intro h
    refine ⟨h.schema, h.uniqueObjectIds, h.uniqueObservationKeys, h.classifiersResolved,
      h.concreteClassifiers, h.observationsExact, h.observationKeysResolved,
      h.observationApplicable, h.valuesTyped, h.bounds, ?_, ?_,
      h.oneIncomingComposite, ?_⟩
    · intro o ho p hp
      by_cases hn : (m.occurrences o.id p.id).Nodup
      · exact Or.inr hn
      · exact Or.inl (fun ha hu => hn (h.uniqueness o ho p hp ha hu))
    · intro a ha x hx y hy
      exact h.oppositeCounts a ha a.ends.1 a.ends.2 rfl x hx y hy
    · exact h.containmentAcyclic

end VLMOF


