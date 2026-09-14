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
