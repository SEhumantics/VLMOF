import VLMOF.ClosureCorrect

/-!
# Saturation invariants for the finite superclass closure

The executable ancestor list is a monotone frontier computation.  These lemmas keep
the finite universe and resolution facts explicit so that the eventual saturation
argument does not need to delete cycles from a source path.
-/

namespace VLMOF

def classUniverse (s : Schema) : List ClassId := s.classes.map ClassDecl.id

def closureAdvance {α : Type} [DecidableEq α] (step : List α → List α)
    (seen : List α) : List α :=
  seen ++ (step seen).eraseDups.filter (fun x => !seen.contains x)

/-- `eraseDups` is implemented by retaining a head and recursing on the strictly
smaller tail filtered away from that head.  The library supplies membership
preservation; this local termination proof supplies the Nodup fact needed by the
finite-frontier cardinality argument. -/
theorem eraseDups_nodup {α : Type} [DecidableEq α] (xs : List α) : xs.eraseDups.Nodup := by
  match xs with
  | [] => simp
  | a :: as =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro ha
      have hmem : a ∈ as.filter (fun b => !b == a) := by
        simpa using (List.mem_eraseDups.mp ha)
      rw [List.mem_filter] at hmem
      simp at hmem
    · exact eraseDups_nodup (as.filter (fun b => !b == a))
termination_by xs.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem closureAdvance_nodup {α : Type} [DecidableEq α] (step : List α → List α)
    {seen : List α} (hseen : seen.Nodup) : (closureAdvance step seen).Nodup := by
  unfold closureAdvance
  rw [List.nodup_append]
  refine ⟨hseen, (eraseDups_nodup _).filter _, ?_⟩
  intro a ha b hb hab
  rw [List.mem_filter] at hb
  have hnot : b ∉ seen := by simpa using hb.2
  exact hnot (hab ▸ ha)

theorem iterateClosure_nodup {α : Type} [DecidableEq α]
    (step : List α → List α) {seen : List α} (hseen : seen.Nodup) :
    ∀ n, (iterateClosure step n seen).Nodup := by
  intro n
  induction n generalizing seen with
  | zero => exact hseen
  | succ n ih =>
    unfold iterateClosure
    exact ih (closureAdvance_nodup step hseen)

theorem closureAdvance_strict_of_unseen_step {α : Type} [DecidableEq α]
    (step : List α → List α) {seen : List α} {x : α}
    (hstep : x ∈ step seen) (hunseen : x ∉ seen) :
    seen.length < (closureAdvance step seen).length := by
  unfold closureAdvance
  rw [List.length_append]
  apply Nat.lt_add_of_pos_right
  apply List.length_pos_of_mem
  rw [List.mem_filter]
  refine ⟨?_, by simpa using hunseen⟩
  exact List.mem_eraseDups.mpr hstep

theorem closureAdvance_eq_of_step_subset {α : Type} [DecidableEq α]
    (step : List α → List α) (seen : List α)
    (hclosed : ∀ x, x ∈ step seen → x ∈ seen) : closureAdvance step seen = seen := by
  unfold closureAdvance
  have hempty : (step seen).eraseDups.filter (fun x => !seen.contains x) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    rw [List.mem_filter] at hx
    simp at hx
    exact hx.2 (hclosed x hx.1)
  rw [hempty]
  simp

theorem iterateClosure_succ_eq_advance {α : Type} [DecidableEq α]
    (step : List α → List α) (n : Nat) (seen : List α) :
    iterateClosure step (n + 1) seen =
      iterateClosure step n (closureAdvance step seen) := by
  rfl

theorem iterateClosure_of_closureAdvance_eq {α : Type} [DecidableEq α]
    (step : List α → List α) (seen : List α)
    (hstable : closureAdvance step seen = seen) :
    ∀ n, iterateClosure step n seen = seen := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterateClosure_succ_eq_advance]
    rw [hstable]
    exact ih

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
