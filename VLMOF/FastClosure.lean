import VLMOF.ClosureSaturation

namespace VLMOF

/-- Stop expanding a frontier once it is unchanged. The finite cutoff is retained
for arbitrary steps that do not saturate. -/
def iterateClosureFast {α : Type} [DecidableEq α]
    (step : List α → List α) : Nat → List α → List α
  | 0, seen => seen
  | n + 1, seen =>
    let next := closureAdvance step seen
    if next = seen then seen else iterateClosureFast step n next

/-- Early stopping is an unconditional optimization of the original computation,
not a change to the semantic reachability relation. -/
theorem iterateClosureFast_eq {α : Type} [DecidableEq α]
    (step : List α → List α) (n : Nat) (seen : List α) :
    iterateClosureFast step n seen = iterateClosure step n seen := by
  induction n generalizing seen with
  | zero => rfl
  | succ n ih =>
    unfold iterateClosureFast
    dsimp only
    split
    · rename_i stable
      exact (iterateClosure_of_closureAdvance_eq step seen stable (n + 1)).symm
    · rw [ih]
      rfl

end VLMOF
