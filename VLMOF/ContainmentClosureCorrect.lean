import VLMOF.FiniteClosure

namespace VLMOF

def objectUniverse (m : Snapshot) : List ObjectId := m.objects.map ObjectDecl.id

theorem outgoingComposite_spec (s : Schema) (m : Snapshot) (seen : List ObjectId)
    (target : ObjectId) :
    target ∈ outgoingComposite s m seen ↔ ∃ source ∈ seen, compositeEdge s m source target := by
  unfold outgoingComposite compositeEdge
  simp only [List.mem_flatMap, List.mem_filter]
  constructor
  · rintro ⟨o, ⟨ho, hs⟩, h⟩
    split at h <;> try simp at h
    rcases h with ⟨v, hv, htarget⟩
    cases v with
    | reference target =>
      simp at htarget
      simp only [List.any_eq_true, decide_eq_true_eq] at *
      rcases ‹∃ a ∈ s.properties, a.id = o.property ∧ a.aggregation = .composite› with ⟨p, hp, hid, hagg⟩
      exact ⟨o.object, by simpa using hs, o, ho, rfl, p, hp, hid, hagg, by simpa [htarget] using hv⟩
    | boolean => simp at htarget
    | integer => simp at htarget
    | string => simp at htarget
    | enumeration => simp at htarget
  · rintro ⟨source, hs, o, ho, hos, p, hp, hid, hagg, hv⟩
    refine ⟨o, ⟨ho, by simpa [hos] using hs⟩, ?_⟩
    simp only [List.any_eq_true]
    have hany : ∃ q ∈ s.properties, q.id = o.property ∧ q.aggregation = .composite :=
      ⟨p, hp, hid, hagg⟩
    simp [hany]
    exact ⟨.reference target, hv, rfl⟩

theorem outgoingComposite_closed (s : Schema) (m : Snapshot)
    (targetsResolved : ∀ src dst, compositeEdge s m src dst → dst ∈ objectUniverse m)
    (seen : List ObjectId) (target : ObjectId) (h : target ∈ outgoingComposite s m seen) :
    target ∈ objectUniverse m := by
  rcases (outgoingComposite_spec s m seen target).mp h with ⟨src, _, hedge⟩
  exact targetsResolved src target hedge

theorem containmentClosure_sound (s : Schema) (m : Snapshot) {start target : ObjectId} :
    target ∈ iterateClosure (outgoingComposite s m) m.objects.length [start] →
      StoredPath (compositeEdge s m) start target :=
  iterateClosure_has_path (outgoingComposite s m) (compositeEdge s m) (outgoingComposite_spec s m) _

theorem containmentClosure_iff (s : Schema) (m : Snapshot)
    (targetsResolved : ∀ src dst, compositeEdge s m src dst → dst ∈ objectUniverse m)
    {start target : ObjectId} (hstart : start ∈ objectUniverse m) :
    target ∈ iterateClosure (outgoingComposite s m) m.objects.length [start] ↔
      StoredPath (compositeEdge s m) start target := by
  simpa [objectUniverse] using
    (finiteClosure_iff_path (outgoingComposite s m) (compositeEdge s m) (objectUniverse m)
      (outgoingComposite_spec s m) (outgoingComposite_closed s m targetsResolved)
      hstart (target := target))

/-- Typed composite occurrences discharge the carrier premise for conforming snapshots. -/
theorem SnapshotConforms.compositeTargetsResolved {s : Schema} {m : Snapshot}
    (h : SnapshotConforms s m) {src dst : ObjectId}
    (edge : compositeEdge s m src dst) : dst ∈ objectUniverse m := by
  obtain ⟨a, ha, _, p, hp, hid, hagg, hv⟩ := edge
  obtain ⟨c, hc⟩ := h.schema.compositeReferences p hp hagg
  have typed := h.valuesTyped a ha p hp hid (.reference dst) hv
  rw [hc] at typed
  obtain ⟨o, ho, heq, _⟩ := typed
  exact List.mem_map.mpr ⟨o, ho, heq⟩

theorem SnapshotConforms.compositeReachable_iff_path {s : Schema} {m : Snapshot}
    (h : SnapshotConforms s m) {start target : ObjectId}
    (hstart : start ∈ objectUniverse m) :
    compositeReachable s m start target ↔ StoredPath (compositeEdge s m) start target :=
  containmentClosure_iff s m (fun _ _ edge => h.compositeTargetsResolved edge) hstart

end VLMOF
