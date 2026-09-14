import VLMOF.Semantics

/-!
# Evidence for the bounded closure computation

This module is separate from the semantic interface.  It proves that bounded closure
never loses an already discovered identity and that every edge exposed by the current
frontier is present after one further iteration.  The schema corollaries establish
reflexivity and inclusion of every resolved direct superclass.
-/

namespace VLMOF

/-- Iteration only extends `seen`; it never removes an identity. -/
theorem mem_iterateClosure_of_mem {α : Type} [DecidableEq α]
    (step : List α → List α) {x : α} {seen : List α}
    (hx : x ∈ seen) : ∀ n, x ∈ iterateClosure step n seen := by
  intro n
  induction n generalizing seen with
  | zero => exact hx
  | succ n ih =>
      unfold iterateClosure
      apply ih
      exact List.mem_append_left _ hx

/-- One expansion discovers every member returned by `step seen`; later iterations
retain it.  `eraseDups` affects multiplicity only, and filtering removes only identities
that were already in `seen`. -/
theorem mem_iterateClosure_succ_of_mem_step {α : Type} [DecidableEq α]
    (step : List α → List α) {x : α} {seen : List α}
    (hx : x ∈ step seen) : ∀ n, x ∈ iterateClosure step (n + 1) seen := by
  intro n
  unfold iterateClosure
  apply mem_iterateClosure_of_mem
  by_cases old : x ∈ seen
  · exact List.mem_append_left _ old
  · apply List.mem_append_right
    simp [List.mem_eraseDups.mpr hx, old]

/-- Iterating `m` and then `n` times is the same as iterating `m+n` times. -/
theorem iterateClosure_add {α : Type} [DecidableEq α]
    (step : List α → List α) (m n : Nat) (seen : List α) :
    iterateClosure step (m + n) seen =
      iterateClosure step n (iterateClosure step m seen) := by
  induction m generalizing seen with
  | zero => simp [iterateClosure]
  | succ m ih =>
      simp only [Nat.succ_add, iterateClosure]
      exact ih _

/-- `classSupers` is monotone in its frontier: adding discovered classes cannot remove
an exposed direct-super edge. -/
theorem classSupers_mono (s : Schema) {small large : List ClassId}
    (hsub : ∀ x, x ∈ small → x ∈ large) :
    ∀ x, x ∈ classSupers s small → x ∈ classSupers s large := by
  intro x hx
  unfold classSupers at hx ⊢
  rcases List.mem_flatMap.mp hx with ⟨c, hc, hx⟩
  rw [List.mem_filter] at hc
  apply List.mem_flatMap.mpr
  exact ⟨c, by
    rw [List.mem_filter]
    exact ⟨hc.1, by simpa using hsub c.id (by simpa using hc.2)⟩, hx⟩

/-- A length-indexed reflexive-transitive superclass path.  The final rule extends a
known path by one stored direct-super edge. -/
inductive SuperPath (s : Schema) : ClassId → ClassId → Nat → Prop where
  | refl (c : ClassId) : SuperPath s c c 0
  | step {start here next : ClassId} {n : Nat} :
      SuperPath s start here n →
      (∃ d ∈ s.classes, d.id = here ∧ next ∈ d.directSupers) →
      SuperPath s start next (n + 1)

/-- Exact computational completeness at a given path length: `n` stored superclass
edges are discovered in `n` expansions. -/
theorem SuperPath.mem_iterateClosure {s : Schema} {start target : ClassId} {n : Nat}
    (path : SuperPath s start target n) :
    target ∈ iterateClosure (classSupers s) n [start] := by
  cases path with
  | refl => simp [iterateClosure]
  | step path hedge =>
      have ih := SuperPath.mem_iterateClosure path
      rcases hedge with ⟨d, hd, hid, hnext⟩
      rw [iterateClosure_add (classSupers s) _ 1 [start]]
      apply mem_iterateClosure_succ_of_mem_step (classSupers s)
      unfold classSupers
      apply List.mem_flatMap.mpr
      exact ⟨d, by
        rw [List.mem_filter]
        refine ⟨hd, ?_⟩
        rw [List.contains_eq_mem]
        exact decide_eq_true (hid ▸ ih), hnext⟩

/-- Every superclass path within the store-size bound is included in the semantic
ancestor closure. -/
theorem SuperPath.isSubtype_of_length_le {s : Schema} {start target : ClassId} {n : Nat}
    (path : SuperPath s start target n) (bound : n ≤ s.classes.length) :
    s.isSubtype start target := by
  unfold Schema.isSubtype Schema.ancestors
  rw [List.mem_eraseDups]
  obtain ⟨extra, hlen⟩ := Nat.exists_eq_add_of_le bound
  rw [hlen, iterateClosure_add]
  exact mem_iterateClosure_of_mem (classSupers s) path.mem_iterateClosure extra

/-- The finite path relation consumed by the semantic cutoff. -/
def BoundedSuperReachable (s : Schema) (start target : ClassId) : Prop :=
  ∃ n, n ≤ s.classes.length ∧ SuperPath s start target n

theorem BoundedSuperReachable.isSubtype {s : Schema} {start target : ClassId}
    (h : BoundedSuperReachable s start target) : s.isSubtype start target := by
  rcases h with ⟨n, hn, path⟩
  exact path.isSubtype_of_length_le hn

/-- Every identity produced after `n` expansions has a stored superclass path of length
at most `n`.  Together with `SuperPath.mem_iterateClosure`, this characterizes each
finite approximation exactly. -/
theorem mem_iterateClosure_has_SuperPath {s : Schema} {start target : ClassId} {n : Nat}
    (h : target ∈ iterateClosure (classSupers s) n [start]) :
    ∃ k, k ≤ n ∧ SuperPath s start target k := by
  induction n generalizing target with
  | zero =>
      simp [iterateClosure] at h
      subst target
      exact ⟨0, Nat.le_refl 0, .refl start⟩
  | succ n ih =>
      rw [iterateClosure_add (classSupers s) n 1 [start]] at h
      unfold iterateClosure at h
      rcases List.mem_append.mp h with hold | hnew
      · rcases ih hold with ⟨k, hk, path⟩
        exact ⟨k, Nat.le_trans hk (Nat.le_succ n), path⟩
      · have hstep : target ∈ classSupers s (iterateClosure (classSupers s) n [start]) := by
          exact List.mem_eraseDups.mp (List.mem_filter.mp hnew).1
        unfold classSupers at hstep
        rcases List.mem_flatMap.mp hstep with ⟨d, hd, htarget⟩
        rw [List.mem_filter] at hd
        change d ∈ s.classes ∧
          (iterateClosure (classSupers s) n [start]).contains d.id = true at hd
        have hdmem : d.id ∈ iterateClosure (classSupers s) n [start] := by
          simpa using hd.2
        rcases ih hdmem with ⟨k, hk, path⟩
        exact ⟨k + 1, Nat.add_le_add_right hk 1,
          .step path ⟨d, hd.1, rfl, htarget⟩⟩

/-- Exact bridge from the semantic computation to bounded reflexive-transitive
superclass reachability. -/
theorem Schema.isSubtype_iff_boundedSuperReachable (s : Schema)
    (start target : ClassId) :
    s.isSubtype start target ↔ BoundedSuperReachable s start target := by
  constructor
  · intro h
    unfold Schema.isSubtype Schema.ancestors at h
    rw [List.mem_eraseDups] at h
    exact mem_iterateClosure_has_SuperPath h
  · exact BoundedSuperReachable.isSubtype

/-- Ordinary unbounded reflexive-transitive superclass reachability. -/
def SuperReachable (s : Schema) (start target : ClassId) : Prop :=
  ∃ n, SuperPath s start target n

theorem Schema.isSubtype_implies_superReachable (s : Schema)
    {start target : ClassId} (h : s.isSubtype start target) :
    SuperReachable s start target := by
  rcases (s.isSubtype_iff_boundedSuperReachable start target).mp h with ⟨n, _, path⟩
  exact ⟨n, path⟩

/-- The reflexive part of the subtype relation is not an assumption: the starting
classifier is retained by the computed closure. -/
theorem Schema.isSubtype_refl (s : Schema) (c : ClassId) : s.isSubtype c c := by
  unfold Schema.isSubtype Schema.ancestors
  rw [List.mem_eraseDups]
  exact mem_iterateClosure_of_mem (classSupers s) (by simp) s.classes.length

/-- Every declared direct superclass is discovered by the bounded closure.  Membership
of the subclass declaration makes the store length positive, so at least one expansion
is available.  Resolution of the superclass is a separate schema-well-formedness field;
this inclusion result itself only needs the stored edge. -/
theorem Schema.directSuper_isSubtype (s : Schema) {c : ClassDecl}
    (hc : c ∈ s.classes) {super : ClassId} (hs : super ∈ c.directSupers) :
    s.isSubtype c.id super := by
  have hne : s.classes.length ≠ 0 := by
    intro hz
    have hempty : s.classes = [] := List.eq_nil_of_length_eq_zero hz
    simp [hempty] at hc
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hne
  unfold Schema.isSubtype Schema.ancestors
  rw [List.mem_eraseDups]
  rw [hn]
  have hstep : super ∈ classSupers s [c.id] := by
    unfold classSupers
    simp only [List.mem_flatMap, List.mem_filter]
    exact ⟨c, ⟨hc, by simp⟩, hs⟩
  simpa [Nat.succ_eq_add_one] using
    (mem_iterateClosure_succ_of_mem_step (classSupers s) hstep n)

namespace ClosureExample

private def cls (id : Nat) (supers : List Nat) : ClassDecl :=
  { id := ⟨id⟩, name := some s!"C{id}", package := none,
    isAbstract := false, directSupers := supers.map ClassId.mk }

/-- Four declarations and a three-edge chain exercise the last useful expansion before
the store-length cutoff. -/
def chain : Schema :=
  { packages := []
    classes := [cls 0 [], cls 1 [0], cls 2 [1], cls 3 [2]]
    properties := []
    associations := []
    enumerations := []
    literals := [] }

example : chain.isSubtype ⟨3⟩ ⟨0⟩ := by native_decide
example : chain.ancestors ⟨3⟩ = [⟨3⟩, ⟨2⟩, ⟨1⟩, ⟨0⟩] := by native_decide

/-- The K0 diamond reaches its root once despite two inheritance paths. -/
example : VLMOF.Example.schema.ancestors VLMOF.Example.diamond =
    [VLMOF.Example.diamond, VLMOF.Example.left, VLMOF.Example.right,
      VLMOF.Example.root] := by native_decide

end ClosureExample
end VLMOF

