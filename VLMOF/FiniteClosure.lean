import VLMOF.ClosureSaturation

namespace VLMOF

/-- Closure remains in a finite carrier whenever every expansion does. -/
theorem iterateClosure_mem_universe {α : Type} [DecidableEq α]
    (step : List α → List α) (carrier : List α)
    (closed : ∀ seen x, x ∈ step seen → x ∈ carrier)
    {start target : α} (hstart : start ∈ carrier) :
    ∀ n, target ∈ iterateClosure step n [start] → target ∈ carrier := by
  intro n
  induction n generalizing target with
  | zero =>
    intro h
    simp only [iterateClosure, List.mem_singleton] at h
    exact h ▸ hstart
  | succ n ih =>
    rw [iterateClosure_add step n 1 [start]]
    intro h
    unfold iterateClosure at h
    rcases List.mem_append.mp h with old | fresh
    · exact ih old
    · exact closed _ _ (List.mem_eraseDups.mp (List.mem_filter.mp fresh).1)

theorem finiteClosure_closed {α : Type} [DecidableEq α]
    (step : List α → List α) (carrier : List α)
    (closed : ∀ seen x, x ∈ step seen → x ∈ carrier)
    {start : α} (hstart : start ∈ carrier) :
    ∀ x, x ∈ step (iterateClosure step carrier.length [start]) →
      x ∈ iterateClosure step carrier.length [start] := by
  classical
  apply Classical.byContradiction
  intro hnotclosed
  have hunseen : ∀ k, k < carrier.length →
      ∃ x, x ∈ step (iterateClosure step k [start]) ∧
        x ∉ iterateClosure step k [start] := by
    intro k hk
    apply Classical.byContradiction
    intro hnone
    have hclosed : ∀ x, x ∈ step (iterateClosure step k [start]) →
        x ∈ iterateClosure step k [start] := by
      intro x hx
      apply Classical.byContradiction
      intro hn
      exact hnone ⟨x, hx, hn⟩
    have heq := iterateClosure_eq_earlier_closed step [start] (Nat.le_of_lt hk) hclosed
    exact hnotclosed (by simpa only [heq] using hclosed)
  have hlarge := iterateClosure_length_ge_of_unseen_each step start carrier.length hunseen
  have hsmall : (iterateClosure step carrier.length [start]).length ≤ carrier.length := by
    apply List.Nodup.length_le_of_subset
    · exact iterateClosure_nodup step (seen := [start]) (by simp) _
    · intro target ht
      exact iterateClosure_mem_universe step carrier closed hstart _ ht
  omega

/-- Reflexive-transitive paths independent of the executable closure. -/
inductive StoredPath {α : Type} (edge : α → α → Prop) : α → α → Prop where
  | refl (start : α) : StoredPath edge start start
  | step {start here next : α} :
      StoredPath edge start here → edge here next → StoredPath edge start next

/-- Soundness does not require well-formedness or a finite carrier. -/
theorem iterateClosure_has_path {α : Type} [DecidableEq α]
    (step : List α → List α) (edge : α → α → Prop)
    (spec : ∀ seen x, x ∈ step seen ↔ ∃ y ∈ seen, edge y x)
    {start target : α} (n : Nat)
    (h : target ∈ iterateClosure step n [start]) : StoredPath edge start target := by
  induction n generalizing target with
  | zero =>
    simp only [iterateClosure, List.mem_singleton] at h
    subst target
    exact .refl start
  | succ n ih =>
    rw [iterateClosure_add step n 1 [start]] at h
    unfold iterateClosure at h
    rcases List.mem_append.mp h with old | fresh
    · exact ih old
    · obtain ⟨y, hy, hedge⟩ := (spec _ _).mp
        (List.mem_eraseDups.mp (List.mem_filter.mp fresh).1)
      exact .step (ih hy) hedge

/-- Saturation removes every path-length premise from completeness. -/
theorem finiteClosure_iff_path {α : Type} [DecidableEq α]
    (step : List α → List α) (edge : α → α → Prop) (carrier : List α)
    (spec : ∀ seen x, x ∈ step seen ↔ ∃ y ∈ seen, edge y x)
    (closed : ∀ seen x, x ∈ step seen → x ∈ carrier)
    {start target : α} (hstart : start ∈ carrier) :
    target ∈ iterateClosure step carrier.length [start] ↔ StoredPath edge start target := by
  constructor
  · exact iterateClosure_has_path step edge spec _
  · intro path
    induction path with
    | refl => exact mem_iterateClosure_of_mem step (by simp) _
    | step path hedge ih =>
      exact finiteClosure_closed step carrier closed hstart _ ((spec _ _).mpr ⟨_, ih, hedge⟩)

end VLMOF

