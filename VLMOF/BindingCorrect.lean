import VLMOF.Elaboration
import Init.Data.List.Nat.Range

/-!
# Binding identity guarantees

A successful numeric resolution refers to exactly the source alias stored at
that index. Consequently assigning one numeric ID to two successfully resolved
aliases cannot collapse distinct declarations. These are binding guarantees;
they are not yet the source-conformance correspondence theorem.
-/
namespace VLMOF.Source

theorem mem_matchingIndices (names : List Name) (name : Name) (index : Nat) :
    index ∈ matchingIndices names name ↔ names[index]? = some name := by
  simp only [matchingIndices, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨entry, i⟩, ⟨hmem, heq⟩, hi⟩
    simp only at heq hi
    subst entry
    subst i
    exact List.mk_mem_zipIdx_iff_getElem?.mp hmem
  · intro h
    exact ⟨(name, index), ⟨List.mk_mem_zipIdx_iff_getElem?.mpr h, rfl⟩, rfl⟩

theorem resolveIndex_ok_iff (kind : String) (names : List Name) (name : Name) (index : Nat) :
    resolveIndex kind names name = .ok index ↔ matchingIndices names name = [index] := by
  unfold resolveIndex
  cases h : matchingIndices names name with
  | nil => simp
  | cons first rest =>
    cases rest with
    | nil => simp
    | cons second rest => simp

/-- The ID returned by successful resolution addresses the original alias. -/
theorem resolveIndex_getElem {kind : String} {names : List Name} {name : Name} {index : Nat}
    (h : resolveIndex kind names name = .ok index) : names[index]? = some name := by
  apply (mem_matchingIndices names name index).mp
  rw [(resolveIndex_ok_iff kind names name index).mp h]
  simp

/-- Distinct successfully resolved source aliases cannot share a generated ID. -/
theorem resolveIndex_injective {kind : String} {names : List Name}
    {first second : Name} {index : Nat}
    (hfirst : resolveIndex kind names first = .ok index)
    (hsecond : resolveIndex kind names second = .ok index) : first = second := by
  exact Option.some.inj ((resolveIndex_getElem hfirst).symm.trans (resolveIndex_getElem hsecond))

end VLMOF.Source
