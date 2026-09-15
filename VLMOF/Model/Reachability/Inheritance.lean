import VLMOF.Model.Reachability.Basic

/-!
# Saturation invariants for the finite superclass closure

The executable ancestor list is a monotone frontier computation.  These lemmas keep
the finite universe and resolution facts explicit so that the eventual saturation
argument does not need to delete cycles from a source path.
-/

namespace VLMOF

/-- Finite carrier of class identities stored by a schema. Under well-formedness it
has no duplicates and contains every resolved superclass. -/
def classUniverse (s : Schema) : List ClassId := s.classes.map ClassDecl.id

/-- One closure round: retain the discovered prefix and append each newly exposed
identity once. This named form supports the saturation and size arguments below. -/
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

/-- One closure advance preserves duplicate-freedom: new values are deduplicated
internally and filtered away from the previously seen prefix. -/
theorem closureAdvance_nodup {α : Type} [DecidableEq α] (step : List α → List α)
    {seen : List α} (hseen : seen.Nodup) : (closureAdvance step seen).Nodup := by
  unfold closureAdvance
  rw [List.nodup_append]
  refine ⟨hseen, (eraseDups_nodup _).filter _, ?_⟩
  intro a ha b hb hab
  rw [List.mem_filter] at hb
  have hnot : b ∉ seen := by simpa using hb.2
  exact hnot (hab ▸ ha)

/-- Every bounded approximation remains duplicate-free when the initial frontier is. -/
theorem iterateClosure_nodup {α : Type} [DecidableEq α]
    (step : List α → List α) {seen : List α} (hseen : seen.Nodup) :
    ∀ n, (iterateClosure step n seen).Nodup := by
  intro n
  induction n generalizing seen with
  | zero => exact hseen
  | succ n ih =>
    unfold iterateClosure
    exact ih (closureAdvance_nodup step hseen)

/-- Exposing an unseen successor strictly increases the next frontier's length. This
is the growth fact used to force saturation in a finite carrier. -/
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

/-- If every exposed successor is already seen, a closure round is a fixed point. -/
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

/-- Unfold one successor iteration through the named `closureAdvance` operation. -/
theorem iterateClosure_succ_eq_advance {α : Type} [DecidableEq α]
    (step : List α → List α) (n : Nat) (seen : List α) :
    iterateClosure step (n + 1) seen =
      iterateClosure step n (closureAdvance step seen) := by
  rfl

/-- Once `closureAdvance` reaches a fixed point, every remaining fuel amount returns
the same frontier; the proof is induction over the unused fuel. -/
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

/-- A successful raw class lookup places the requested identity in the finite class
carrier, even before uniqueness is assumed. -/
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

/-- Every superclass exposed by one expansion is in the class carrier. The material
assumption is `supersResolved` from schema well-formedness. -/
theorem classSupers_mem_classUniverse (s : Schema) (wf : SchemaWellFormed s)
    {seen : List ClassId} {super : ClassId}
    (h : super ∈ classSupers s seen) : super ∈ classUniverse s := by
  unfold classSupers at h
  rcases List.mem_flatMap.mp h with ⟨d, hd, hs⟩
  rw [List.mem_filter] at hd
  exact mem_classUniverse_of_classDecls_ne_nil (wf.supersResolved d hd.1 super hs)

/-- Starting inside the class carrier, every bounded superclass approximation stays
inside it. The proof inducts over expansions and applies superclass resolution. -/
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

/-- Schema identifier uniqueness makes the finite class carrier duplicate-free. -/
theorem classUniverse_nodup (s : Schema) (wf : SchemaWellFormed s) :
    (classUniverse s).Nodup := by
  simpa [classUniverse, uniqueBy] using wf.uniqueClassIds

/-- Every superclass approximation has length at most the class store. The proof
combines duplicate-freedom with containment in `classUniverse`. -/
theorem iterateClosure_length_le_class_count (s : Schema) (wf : SchemaWellFormed s)
    {start : ClassId} (hstart : start ∈ classUniverse s) (n : Nat) :
    (iterateClosure (classSupers s) n [start]).length ≤ s.classes.length := by
  have hbound : (iterateClosure (classSupers s) n [start]).length ≤
      (classUniverse s).length := by
    apply List.Nodup.length_le_of_subset
    · exact iterateClosure_nodup (classSupers s) (seen := [start]) (.cons (by simp) .nil) n
    · intro target htarget
      exact iterateClosure_mem_classUniverse s wf hstart n htarget
  simpa [classUniverse] using hbound

/-- If each of the first `n` frontiers exposes an unseen successor, their lengths
grow from the singleton start to at least `n + 1`. -/
theorem iterateClosure_length_ge_of_unseen_each {α : Type} [DecidableEq α]
    (step : List α → List α) (start : α) (n : Nat)
    (hunseen : ∀ k, k < n → ∃ x, x ∈ step (iterateClosure step k [start]) ∧
      x ∉ iterateClosure step k [start]) :
    n + 1 ≤ (iterateClosure step n [start]).length := by
  induction n with
  | zero => simp [iterateClosure]
  | succ n ih =>
    have hprev : ∀ k, k < n → ∃ x, x ∈ step (iterateClosure step k [start]) ∧
        x ∉ iterateClosure step k [start] := by
      intro k hk
      exact hunseen k (Nat.lt_trans hk (Nat.lt_succ_self n))
    have hlen := ih hprev
    rcases hunseen n (Nat.lt_succ_self n) with ⟨x, hxstep, hxnew⟩
    rw [iterateClosure_add step n 1 [start]]
    have hgrow := closureAdvance_strict_of_unseen_step step hxstep hxnew
    change n.succ + 1 ≤ (iterateClosure step 1 (iterateClosure step n [start])).length
    unfold iterateClosure
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hlen hgrow)

/-- Once a frontier is closed, every later approximation is that same frontier. -/
theorem iterateClosure_eq_earlier_closed {α : Type} [DecidableEq α]
    (step : List α → List α) (seen : List α) {k n : Nat} (hkn : k ≤ n)
    (hclosed : ∀ x, x ∈ step (iterateClosure step k seen) →
      x ∈ iterateClosure step k seen) :
    iterateClosure step n seen = iterateClosure step k seen := by
  have heq : k + (n - k) = n := Nat.add_sub_of_le hkn
  rw [← heq, iterateClosure_add]
  exact iterateClosure_of_closureAdvance_eq step _
    (closureAdvance_eq_of_step_subset step _ hclosed) _

/-- Finite resolved class declarations force saturation within the class count. -/
theorem classClosure_closed (s : Schema) (wf : SchemaWellFormed s)
    {start : ClassId} (hstart : start ∈ classUniverse s) :
    ∀ x, x ∈ classSupers s (iterateClosure (classSupers s) s.classes.length [start]) →
      x ∈ iterateClosure (classSupers s) s.classes.length [start] := by
  classical
  apply Classical.byContradiction
  intro hnotclosed
  have hunseen : ∀ k, k < s.classes.length →
      ∃ x, x ∈ classSupers s (iterateClosure (classSupers s) k [start]) ∧
        x ∉ iterateClosure (classSupers s) k [start] := by
    intro k hk
    apply Classical.byContradiction
    intro hnone
    have hclosed : ∀ x, x ∈ classSupers s (iterateClosure (classSupers s) k [start]) →
        x ∈ iterateClosure (classSupers s) k [start] := by
      intro x hx
      apply Classical.byContradiction
      intro hn
      exact hnone ⟨x, hx, hn⟩
    have heq := iterateClosure_eq_earlier_closed (classSupers s) [start] (Nat.le_of_lt hk) hclosed
    exact hnotclosed (by simpa only [heq] using hclosed)
  have hlarge := iterateClosure_length_ge_of_unseen_each (classSupers s) start s.classes.length hunseen
  have hsmall := iterateClosure_length_le_class_count s wf hstart s.classes.length
  omega
/-- Every finite stored superclass path is present at the saturated class-count
frontier. Each path step uses closure of that frontier under resolved direct edges. -/
theorem SuperPath.mem_saturated {s : Schema} (wf : SchemaWellFormed s)
    {start target : ClassId} {n : Nat} (path : SuperPath s start target n)
    (hstart : start ∈ classUniverse s) :
    target ∈ iterateClosure (classSupers s) s.classes.length [start] := by
  induction path with
  | refl => exact mem_iterateClosure_of_mem (classSupers s) (by simp) _
  | step path edge ih =>
    apply classClosure_closed s wf hstart
    obtain ⟨d, hd, heq, hs⟩ := edge
    apply List.mem_flatMap.mpr
    refine ⟨d, ?_, hs⟩
    rw [List.mem_filter]
    exact ⟨hd, by simpa [heq] using ih⟩

/-- The class-count cutoff computes full reflexive-transitive reachability for
resolved starting classes in a well-formed schema. No path-length premise remains. -/
theorem Schema.isSubtype_iff_superReachable (s : Schema) (wf : SchemaWellFormed s)
    {start target : ClassId} (hstart : start ∈ classUniverse s) :
    s.isSubtype start target ↔ SuperReachable s start target := by
  constructor
  · exact s.isSubtype_implies_superReachable
  · rintro ⟨n, path⟩
    unfold Schema.isSubtype Schema.ancestors
    exact List.mem_eraseDups.mpr (path.mem_saturated wf hstart)
end VLMOF


