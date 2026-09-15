import VLMOF.Model.Semantics

/-!
# Consequences of the declarative semantics

The main result combines occurrence-sensitive opposite reciprocity with an upper-one
opposite.  It does not assume uniqueness of the forward property.
-/

namespace VLMOF

/-- Two members of a key-unique list are equal when their keys are equal. The proof
peels the list and uses head-key exclusion to rule out the two mixed cases. -/
theorem uniqueBy_eq_of_mem {κ α : Type} [DecidableEq κ] (key : α → κ)
    {xs : List α} (h : uniqueBy key xs) {a b : α}
    (ha : a ∈ xs) (hb : b ∈ xs) (hk : key a = key b) : a = b := by
  induction xs generalizing a b with
  | nil => simp at ha
  | cons x xs ih =>
      simp only [uniqueBy, List.map_cons, List.nodup_cons] at h
      rcases h with ⟨hnot, htail⟩
      rcases List.mem_cons.mp ha with hax | ha
      · subst a
        rcases List.mem_cons.mp hb with hbx | hb
        · exact hbx.symm
        · exfalso
          apply hnot
          rw [hk]
          exact List.mem_map.mpr ⟨b, hb, rfl⟩
      · rcases List.mem_cons.mp hb with hbx | hb
        · subst b
          exfalso
          apply hnot
          rw [← hk]
          exact List.mem_map.mpr ⟨a, ha, rfl⟩
        · exact ih htail ha hb hk

/-- Conformance makes the common observation store a partial function of its key;
raw duplicate rows are therefore never trusted as a first-match lookup. -/
theorem observation_key_injective {s : Schema} {m : Snapshot}
    (h : SnapshotConforms s m) {a b : Observation}
    (ha : a ∈ m.observations) (hb : b ∈ m.observations)
    (hk : a.key = b.key) : a = b :=
  uniqueBy_eq_of_mem Observation.key h.uniqueObservationKeys ha hb hk

/-- The occurrences of one value cannot exceed the total occurrence-list length.
This small bound connects opposite counts to a property's multiplicity bound. -/
theorem occurrence_count_le_length (v : Value) (xs : List Value) : xs.count v ≤ xs.length := by
  exact List.count_le_length

/-- An opposite upper bound of one forces forward reference uniqueness for each target,
even if the forward end is declared non-unique. -/
theorem opposite_upper_one_forces_reference_count_le_one
    {s : Schema} {m : Snapshot} (h : SnapshotConforms s m)
    {a : AssociationDecl} (ha : a ∈ s.associations) {p q : PropertyId}
    (hends : a.ends = (p, q)) {qd : PropertyDecl} (hqd : qd ∈ s.properties)
    (hqId : qd.id = q) (hqUpper : qd.multiplicity.upper = .finite 1)
    {x y : ObjectDecl} (hx : x ∈ m.objects) (hy : y ∈ m.objects)
    (hqApplicable : s.applicableProperty y.classifier qd.id) :
    (m.occurrences x.id p).count (.reference y.id) ≤ 1 := by
  rw [h.oppositeCounts a ha p q hends x hx y hy]
  calc
    (m.occurrences y.id q).count (.reference x.id) ≤ (m.occurrences y.id q).length :=
      occurrence_count_le_length _ _
    _ ≤ 1 := by
      have hb := h.bounds y hy qd hqd hqApplicable
      rw [hqId] at hb
      simpa [withinMultiplicity, Upper.allows, hqUpper] using hb.2

end VLMOF
