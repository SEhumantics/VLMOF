import VLMOF.FiniteClosure

namespace VLMOF

def PackageParentEdge (s : Schema) (child parent : PackageId) : Prop :=
  ∃ d ∈ s.packages, d.id = child ∧ d.parent = some parent

def packageUniverse (s : Schema) : List PackageId := s.packages.map PackageDecl.id

theorem packageParents_spec (s : Schema) (seen : List PackageId) (parent : PackageId) :
    parent ∈ packageParents s seen ↔ ∃ child ∈ seen, PackageParentEdge s child parent := by
  unfold packageParents PackageParentEdge
  simp [List.mem_filterMap]
  constructor
  · rintro ⟨d, ⟨hd, hs⟩, hp⟩
    exact ⟨d.id, hs, d, hd, rfl, hp⟩
  · rintro ⟨child, hs, d, hd, hid, hp⟩
    exact ⟨d, ⟨hd, hid ▸ hs⟩, hp⟩

theorem packageParents_closed (s : Schema) (wf : SchemaWellFormed s)
    (seen : List PackageId) (parent : PackageId)
    (h : parent ∈ packageParents s seen) : parent ∈ packageUniverse s := by
  rcases (packageParents_spec s seen parent).mp h with ⟨child, _, d, hd, _, hp⟩
  have hr := wf.packageParentsResolved d hd parent hp
  unfold Schema.packageDecls at hr
  unfold packageUniverse
  simp only [List.mem_map]
  apply Classical.byContradiction
  intro hn
  apply hr
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro q hq
  rw [List.mem_filter] at hq
  exact hn ⟨q, hq.1, by simpa using hq.2⟩

theorem packageClosure_sound (s : Schema) {start target : PackageId} :
    target ∈ iterateClosure (packageParents s) s.packages.length [start] →
      StoredPath (PackageParentEdge s) start target :=
  iterateClosure_has_path (packageParents s) (PackageParentEdge s) (packageParents_spec s) _

theorem packageClosure_iff (s : Schema) (wf : SchemaWellFormed s)
    {start target : PackageId} (hstart : start ∈ packageUniverse s) :
    target ∈ iterateClosure (packageParents s) s.packages.length [start] ↔
      StoredPath (PackageParentEdge s) start target := by
  simpa [packageUniverse] using
    (finiteClosure_iff_path (packageParents s) (PackageParentEdge s) (packageUniverse s)
      (packageParents_spec s) (packageParents_closed s wf) hstart (target := target))

end VLMOF
