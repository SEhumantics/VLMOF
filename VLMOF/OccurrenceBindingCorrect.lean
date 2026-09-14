import VLMOF.ValueBindingCorrect

/-! Binding respects ordered equality and unordered multiset observations. -/
namespace VLMOF.Source

theorem OccurrencesBind.source_covered {model : Model} {snapshot : Instance}
    {sources : List Source.Value} {targets : List VLMOF.Value}
    (h : OccurrencesBind model snapshot sources targets) :
    ∀ source ∈ sources, ∃ target ∈ targets, ValueBinds model snapshot source target := by
  induction sources generalizing targets with
  | nil => simp
  | cons first rest ih =>
    cases targets with
    | nil => simp [OccurrencesBind] at h
    | cons second tail =>
      intro source hm
      rcases List.mem_cons.mp hm with he | ht
      · subst source
        exact ⟨second, by simp, h.1⟩
      · obtain ⟨target, hm, hv⟩ := ih h.2 source ht
        exact ⟨target, List.mem_cons_of_mem second hm, hv⟩

theorem OccurrencesBind.target_covered {model : Model} {snapshot : Instance}
    {sources : List Source.Value} {targets : List VLMOF.Value}
    (h : OccurrencesBind model snapshot sources targets) :
    ∀ target ∈ targets, ∃ source ∈ sources, ValueBinds model snapshot source target := by
  induction sources generalizing targets with
  | nil => cases targets <;> simp_all [OccurrencesBind]
  | cons first rest ih =>
    cases targets with
    | nil => simp [OccurrencesBind] at h
    | cons second tail =>
      intro target hm
      rcases List.mem_cons.mp hm with he | ht
      · subst target
        exact ⟨first, by simp, h.1⟩
      · obtain ⟨source, hm, hv⟩ := ih h.2 target ht
        exact ⟨source, List.mem_cons_of_mem first hm, hv⟩

theorem OccurrencesBind.eq_iff {model : Model} {snapshot : Instance}
    {left right : List Source.Value} {left' right' : List VLMOF.Value}
    (hl : OccurrencesBind model snapshot left left')
    (hr : OccurrencesBind model snapshot right right') : left = right ↔ left' = right' := by
  constructor
  · intro he
    subst right
    exact Except.ok.inj (((bindOccurrences_iff _ _ _ _).mpr hl).symm.trans
      ((bindOccurrences_iff _ _ _ _).mpr hr))
  · intro he
    subst right'
    induction left generalizing left' right with
    | nil =>
      cases left' <;> cases right <;> simp_all [OccurrencesBind]
    | cons first rest ih =>
      cases left' with
      | nil => simp [OccurrencesBind] at hl
      | cons target tail =>
        cases right with
        | nil => simp [OccurrencesBind] at hr
        | cons second remaining =>
          have he := hl.1.source_unique hr.1
          have ht := ih hl.2 hr.2
          simp [he, ht]

theorem OccurrencesBind.perm_iff {model : Model} {snapshot : Instance}
    {left right : List Source.Value} {left' right' : List VLMOF.Value}
    (hl : OccurrencesBind model snapshot left left')
    (hr : OccurrencesBind model snapshot right right') : left.Perm right ↔ left'.Perm right' := by
  classical
  constructor
  · intro hp
    apply List.perm_iff_count.mpr
    intro target
    by_cases hv : ∃ source, ValueBinds model snapshot source target
    · obtain ⟨source, hv⟩ := hv
      rw [← hl.count_eq hv, ← hr.count_eq hv]
      exact hp.count source
    · have hn (sources targets) (h : OccurrencesBind model snapshot sources targets) : target ∉ targets := by
        intro hm
        obtain ⟨source, _, hst⟩ := h.target_covered target hm
        exact hv ⟨source, hst⟩
      rw [List.count_eq_zero_of_not_mem (hn _ _ hl), List.count_eq_zero_of_not_mem (hn _ _ hr)]
  · intro hp
    apply List.perm_iff_count.mpr
    intro source
    by_cases hv : ∃ target, ValueBinds model snapshot source target
    · obtain ⟨target, hv⟩ := hv
      rw [hl.count_eq hv, hr.count_eq hv]
      exact hp.count target
    · have hn (sources targets) (h : OccurrencesBind model snapshot sources targets) : source ∉ sources := by
        intro hm
        obtain ⟨target, _, hst⟩ := h.source_covered source hm
        exact hv ⟨target, hst⟩
      rw [List.count_eq_zero_of_not_mem (hn _ _ hl), List.count_eq_zero_of_not_mem (hn _ _ hr)]

/-- Source and core have the same observable collection equality after binding. -/
theorem OccurrencesBind.equivalent_iff {model : Model} {snapshot : Instance}
    {left right : List Source.Value} {left' right' : List VLMOF.Value}
    (hl : OccurrencesBind model snapshot left left')
    (hr : OccurrencesBind model snapshot right right') (ordered : Bool) :
    Equivalent ordered left right ↔ Occurrences.equivalent ordered left' right' := by
  cases ordered <;> simp only [Equivalent, Occurrences.equivalent, Bool.false_eq_true,
    if_false, if_true]
  · exact hl.perm_iff hr
  · exact hl.eq_iff hr

end VLMOF.Source
