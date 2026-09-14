import VLMOF.ClosureCorrect

/-!
# Saturation invariants for the finite superclass closure

The executable ancestor list is a monotone frontier computation.  These lemmas keep
the finite universe and resolution facts explicit so that the eventual saturation
argument does not need to delete cycles from a source path.
-/

namespace VLMOF

def classUniverse (s : Schema) : List ClassId := s.classes.map ClassDecl.id

theorem mem_classUniverse_of_classDecls_ne_nil {s : Schema} {id : ClassId}
    (h : s.classDecls id ≠ []) : id ∈ classUniverse s := by
  unfold Schema.classDecls at h
  unfold classUniverse
  simp only [List.mem_map]
  classical
  apply Classical.byContradiction
  intro hno
  apply h
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro d hd
  rw [List.mem_filter] at hd
  apply hno
  exact ⟨d, hd.1, by simpa using hd.2⟩

theorem classSupers_mem_classUniverse (s : Schema) (wf : SchemaWellFormed s)
    {seen : List ClassId} {super : ClassId}
    (h : super ∈ classSupers s seen) : super ∈ classUniverse s := by
  unfold classSupers at h
  rcases List.mem_flatMap.mp h with ⟨d, hd, hs⟩
  rw [List.mem_filter] at hd
  exact mem_classUniverse_of_classDecls_ne_nil (wf.supersResolved d hd.1 super hs)

theorem iterateClosure_mem_classUniverse (s : Schema) (wf : SchemaWellFormed s)
    {start target : ClassId} (hstart : start ∈ classUniverse s) :
    ∀ n, target ∈ iterateClosure (classSupers s) n [start] → target ∈ classUniverse s := by
  intro n
  induction n generalizing target with
  | zero =>
    simp only [iterateClosure, List.mem_singleton]
    intro h
    subst target
    exact hstart
  | succ n ih =>
    rw [iterateClosure_add (classSupers s) n 1 [start]]
    intro h
    unfold iterateClosure at h
    rcases List.mem_append.mp h with hold | fresh
    · exact ih hold
    · have hstep : target ∈ classSupers s (iterateClosure (classSupers s) n [start]) := by
        exact List.mem_eraseDups.mp (List.mem_filter.mp fresh).1
      exact classSupers_mem_classUniverse s wf hstep

/-- Every direct edge from a discovered frontier remains inside the finite class
universe under schema resolution. -/
theorem classSupers_closed_in_universe (s : Schema) (wf : SchemaWellFormed s)
    (seen : List ClassId) :
    ∀ super ∈ classSupers s seen, super ∈ classUniverse s := by
  intro super hs
  exact classSupers_mem_classUniverse s wf hs

end VLMOF
