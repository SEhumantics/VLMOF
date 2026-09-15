import VLMOF.Source.Binding.Resolution

namespace VLMOF.Source

/-- Meaning of a symbolic value under the declaration environments, independent
of executable binding. Primitive values are unchanged; references require unique
source aliases at the corresponding identity indices. -/
def ValueBinds (model : Model) (snapshot : Instance) : Source.Value → VLMOF.Value → Prop
  | .boolean a, .boolean b => a = b
  | .integer a, .integer b => a = b
  | .string a, .string b => a = b
  | .enumeration enum lit, .enumeration eid lid =>
      UniqueAliasAt (model.enumerations.map Enumeration.alias) enum eid.val ∧
      UniqueAliasAt (model.literals.map Literal.alias) lit lid.val
  | .reference object, .reference oid =>
      UniqueAliasAt (snapshot.objects.map Object.alias) object oid.val
  | _, _ => False

theorem bindValue_iff (model : Model) (snapshot : Instance)
    (source : Source.Value) (target : VLMOF.Value) :
    bindValue model snapshot source = .ok target ↔ ValueBinds model snapshot source target := by
  cases source with
  | boolean value => cases target <;> simp [bindValue, ValueBinds, pure, Except.pure]
  | integer value => cases target <;> simp [bindValue, ValueBinds, pure, Except.pure]
  | string value => cases target <;> simp [bindValue, ValueBinds, pure, Except.pure]
  | reference object =>
    have hrel : ∀ i, UniqueAliasAt (snapshot.objects.map Object.alias) object i ↔
        resolveIndex "object" (snapshot.objects.map Object.alias) object = .ok i :=
      fun i => (resolveIndex_iff_uniqueAliasAt _ _ _ i).symm
    cases h : resolveIndex "object" (snapshot.objects.map Object.alias) object <;>
      cases target <;>
      simp [bindValue, objectId, ValueBinds, hrel, h, Functor.map, Except.map]
    rename_i oid
    cases oid
    simp
  | enumeration enum lit =>
    have he : ∀ i, UniqueAliasAt (model.enumerations.map Enumeration.alias) enum i ↔
        resolveIndex "enumeration" (model.enumerations.map Enumeration.alias) enum = .ok i :=
      fun i => (resolveIndex_iff_uniqueAliasAt _ _ _ i).symm
    have hl : ∀ i, UniqueAliasAt (model.literals.map Literal.alias) lit i ↔
        resolveIndex "literal" (model.literals.map Literal.alias) lit = .ok i :=
      fun i => (resolveIndex_iff_uniqueAliasAt _ _ _ i).symm
    cases h₁ : resolveIndex "enumeration" (model.enumerations.map Enumeration.alias) enum <;>
      cases h₂ : resolveIndex "literal" (model.literals.map Literal.alias) lit <;>
      cases target <;>
      simp [bindValue, enumerationId, literalId, ValueBinds, he, hl, h₁, h₂,
        Except.map, Bind.bind, Except.bind, pure, Except.pure]
    rename_i eid lid
    cases eid
    cases lid
    simp

/-- Every occurrence has a corresponding value in the same position; no set
conversion, default insertion, or duplicate removal is part of binding. -/
def OccurrencesBind (model : Model) (snapshot : Instance) :
    List Source.Value → List VLMOF.Value → Prop
  | [], [] => True
  | source :: sources, target :: targets =>
      ValueBinds model snapshot source target ∧ OccurrencesBind model snapshot sources targets
  | _, _ => False

theorem bindOccurrences_iff (model : Model) (snapshot : Instance)
    (sources : List Source.Value) (targets : List VLMOF.Value) :
    sources.mapM (bindValue model snapshot) = .ok targets ↔
      OccurrencesBind model snapshot sources targets := by
  induction sources generalizing targets with
  | nil => cases targets <;> simp [OccurrencesBind, pure, Except.pure]
  | cons source sources ih =>
    have hv : ∀ target, ValueBinds model snapshot source target ↔
        bindValue model snapshot source = .ok target := fun target => (bindValue_iff _ _ _ target).symm
    have ht : ∀ targets, OccurrencesBind model snapshot sources targets ↔
        sources.mapM (bindValue model snapshot) = .ok targets := fun targets => (ih targets).symm
    cases hs : bindValue model snapshot source <;>
      cases hss : sources.mapM (bindValue model snapshot) <;>
      cases targets <;>
      simp [List.mapM_cons, OccurrencesBind, hv, ht, hs, hss,
        Bind.bind, Except.bind, pure, Except.pure]

theorem OccurrencesBind.length_eq {model : Model} {snapshot : Instance}
    {sources : List Source.Value} {targets : List VLMOF.Value}
    (h : OccurrencesBind model snapshot sources targets) : sources.length = targets.length := by
  induction sources generalizing targets with
  | nil => cases targets <;> simp_all [OccurrencesBind]
  | cons source sources ih =>
    cases targets with
    | nil => simp [OccurrencesBind] at h
    | cons target targets =>
      simp only [OccurrencesBind] at h
      simpa using congrArg Nat.succ (ih h.2)
/-- Binding does not identify distinct symbolic values. This includes declaration
and object aliases, whose identity is separate from their display names. -/
theorem ValueBinds.source_unique {model : Model} {snapshot : Instance}
    {first second : Source.Value} {target : VLMOF.Value}
    (hf : ValueBinds model snapshot first target)
    (hs : ValueBinds model snapshot second target) : first = second := by
  cases first <;> cases second <;> cases target <;>
    simp_all [ValueBinds]
  · exact ⟨Option.some.inj (hf.1.1.symm.trans hs.1.1),
      Option.some.inj (hf.2.1.symm.trans hs.2.1)⟩
  · exact Option.some.inj (hf.1.symm.trans hs.1)

/-- A source value cannot bind to two distinct core values. -/
theorem ValueBinds.target_unique {model : Model} {snapshot : Instance}
    {source : Source.Value} {first second : VLMOF.Value}
    (hf : ValueBinds model snapshot source first)
    (hs : ValueBinds model snapshot source second) : first = second := by
  exact Except.ok.inj (((bindValue_iff _ _ _ _).mpr hf).symm.trans
    ((bindValue_iff _ _ _ _).mpr hs))
/-- Membership is preserved and reflected for any successfully bound value. -/
theorem OccurrencesBind.mem_iff {model : Model} {snapshot : Instance}
    {sources : List Source.Value} {targets : List VLMOF.Value}
    {source : Source.Value} {target : VLMOF.Value}
    (h : OccurrencesBind model snapshot sources targets)
    (hv : ValueBinds model snapshot source target) : source ∈ sources ↔ target ∈ targets := by
  induction sources generalizing targets with
  | nil => cases targets <;> simp_all [OccurrencesBind]
  | cons first rest ih =>
    cases targets with
    | nil => simp [OccurrencesBind] at h
    | cons second tail =>
      have hp := h.1
      have ht := ih h.2
      have he : source = first ↔ target = second := by
        constructor
        · intro eq
          subst first
          exact hv.target_unique hp
        · intro eq
          subst second
          exact hv.source_unique hp
      simpa only [List.mem_cons, he] using or_congr Iff.rfl ht

/-- `isUnique` observes exactly the same duplicates before and after binding. -/
theorem OccurrencesBind.nodup_iff {model : Model} {snapshot : Instance}
    {sources : List Source.Value} {targets : List VLMOF.Value}
    (h : OccurrencesBind model snapshot sources targets) : sources.Nodup ↔ targets.Nodup := by
  induction sources generalizing targets with
  | nil => cases targets <;> simp_all [OccurrencesBind]
  | cons first rest ih =>
    cases targets with
    | nil => simp [OccurrencesBind] at h
    | cons second tail =>
      rw [List.nodup_cons, List.nodup_cons, h.2.mem_iff h.1, ih h.2]
/-- Opposite reciprocity can compare occurrence counts on either side of binding. -/
theorem OccurrencesBind.count_eq {model : Model} {snapshot : Instance}
    {sources : List Source.Value} {targets : List VLMOF.Value}
    {source : Source.Value} {target : VLMOF.Value}
    (h : OccurrencesBind model snapshot sources targets)
    (hv : ValueBinds model snapshot source target) : sources.count source = targets.count target := by
  induction sources generalizing targets with
  | nil => cases targets <;> simp_all [OccurrencesBind]
  | cons first rest ih =>
    cases targets with
    | nil => simp [OccurrencesBind] at h
    | cons second tail =>
      have ht := ih h.2
      by_cases eq : source = first
      · subst first
        have eqt := hv.target_unique h.1
        subst second
        simpa using ht
      · have neqt : second ≠ target := by
          intro eqt
          subst second
          exact eq (hv.source_unique h.1)
        simpa [List.count_cons_of_ne (Ne.symm eq), List.count_cons_of_ne neqt] using ht
end VLMOF.Source









