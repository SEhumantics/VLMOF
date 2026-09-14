import VLMOF.ElaborationComplete
import VLMOF.ClosureSaturation

/-!
# Preservation of model well-formedness by schema elaboration

The executable binder allocates each declaration at its source-list index.  The
lemmas below first expose that allocation from a successful `bindModel` run and
then transport every source well-formedness obligation to the resulting schema.
-/
namespace VLMOF.Source

variable {α β γ ε : Type} {model : Model} {target : Schema}

def bindPackageEntry (model : Model) (x : Package × Nat) : BindingResult PackageDecl := do
  checkQualification x.1.alias x.1.parent
  let parent ← optionalPackage model x.1.parent
  pure { id := ⟨x.2⟩, name := some x.1.name, parent }

def bindClassEntry (model : Model) (x : Class × Nat) : BindingResult ClassDecl := do
  checkQualification x.1.alias x.1.package
  let package ← optionalPackage model x.1.package
  let directSupers ← x.1.directSupers.mapM (classId model)
  pure (ClassDecl.mk ⟨x.2⟩ (some x.1.name) package x.1.isAbstract directSupers)

def bindPropertyEntry (model : Model) (x : Property × Nat) : BindingResult PropertyDecl := do
  checkQualification x.1.alias (some (ownerName x.1.owner))
  let owner ← bindOwner model x.1.owner
  let type ← bindType model x.1.type
  pure (PropertyDecl.mk ⟨x.2⟩ (some x.1.name) owner type x.1.multiplicity
    x.1.aggregation x.1.isId)

def bindAssociationEntry (model : Model) (x : Association × Nat) : BindingResult AssociationDecl := do
  checkQualification x.1.alias x.1.package
  let package ← optionalPackage model x.1.package
  let ends ← match x.1.ends with
    | [first, second] => do pure (← propertyId model first, ← propertyId model second)
    | _ => throw ("association requires exactly two ends: " ++ showName x.1.alias)
  pure (AssociationDecl.mk ⟨x.2⟩ (some x.1.name) package ends)

def bindEnumerationEntry (model : Model) (x : Enumeration × Nat) : BindingResult EnumerationDecl := do
  checkQualification x.1.alias x.1.package
  let package ← optionalPackage model x.1.package
  pure (EnumerationDecl.mk ⟨x.2⟩ (some x.1.name) package)

def bindLiteralEntry (model : Model) (x : Literal × Nat) : BindingResult LiteralDecl := do
  checkQualification x.1.alias (some x.1.enumeration)
  let enumeration ← enumerationId model x.1.enumeration
  pure { id := ⟨x.2⟩, name := some x.1.name, enumeration }

structure ModelAllocation (model : Model) (target : Schema) : Prop where
  packages : model.packages.zipIdx.mapM (bindPackageEntry model) = .ok target.packages
  classes : model.classes.zipIdx.mapM (bindClassEntry model) = .ok target.classes
  properties : model.properties.zipIdx.mapM (bindPropertyEntry model) = .ok target.properties
  associations : model.associations.zipIdx.mapM (bindAssociationEntry model) = .ok target.associations
  enumerations : model.enumerations.zipIdx.mapM (bindEnumerationEntry model) = .ok target.enumerations
  literals : model.literals.zipIdx.mapM (bindLiteralEntry model) = .ok target.literals

private theorem except_bind_ok {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : x.bind f = .ok y) : ∃ value, x = .ok value ∧ f value = .ok y := by
  cases hx : x with
  | error error => simp [hx, Bind.bind, Except.bind] at h
  | ok value => exact ⟨value, rfl, by simpa [hx, Bind.bind, Except.bind] using h⟩

/-- Inverting `bindModel` yields the actual successful per-kind allocations. -/
theorem modelAllocation_of_bindModel (h : bindModel model = .ok target) :
    ModelAllocation model target := by
  change (checkAliases "declaration" (aliases model)).bind (fun _ =>
    (model.packages.zipIdx.mapM (bindPackageEntry model)).bind (fun packages =>
    (model.classes.zipIdx.mapM (bindClassEntry model)).bind (fun classes =>
    (model.properties.zipIdx.mapM (bindPropertyEntry model)).bind (fun properties =>
    (model.associations.zipIdx.mapM (bindAssociationEntry model)).bind (fun associations =>
    (model.enumerations.zipIdx.mapM (bindEnumerationEntry model)).bind (fun enumerations =>
    (model.literals.zipIdx.mapM (bindLiteralEntry model)).bind (fun literals =>
      .ok (Schema.mk packages classes properties associations enumerations literals)))))))) =
        .ok target at h
  rcases except_bind_ok h with ⟨_, _, h⟩
  rcases except_bind_ok h with ⟨packages, hp, h⟩
  rcases except_bind_ok h with ⟨classes, hc, h⟩
  rcases except_bind_ok h with ⟨properties, hpr, h⟩
  rcases except_bind_ok h with ⟨associations, ha, h⟩
  rcases except_bind_ok h with ⟨enumerations, he, h⟩
  rcases except_bind_ok h with ⟨literals, hl, h⟩
  have ht : target = Schema.mk packages classes properties associations enumerations literals := by
    exact Except.ok.inj h.symm
  subst target
  exact ⟨hp, hc, hpr, ha, he, hl⟩

theorem mapM_ok_mem_iff {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {y : β} :
    y ∈ ys ↔ ∃ x ∈ xs, f x = .ok y := by
  induction xs generalizing ys with
  | nil =>
      simp [List.mapM_nil, pure, Except.pure] at h
      subst ys
      simp
  | cons x xs ih =>
      cases hx : f x <;> cases ht : xs.mapM f <;>
        simp [List.mapM_cons, hx, ht, Bind.bind, Except.bind, pure, Except.pure] at h
      subst ys
      simp only [List.mem_cons, ih ht]
      constructor
      · rintro (rfl | hy)
        · exact ⟨x, by simp, hx⟩
        · rcases hy with ⟨z, hz, hf⟩
          exact ⟨z, by simp [hz], hf⟩
      · rintro ⟨z, hz, hf⟩
        rcases hz with rfl | hz
        · exact Or.inl (Except.ok.inj (hx.symm.trans hf)).symm
        · exact Or.inr ⟨z, hz, hf⟩

theorem mapM_ok_length {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
      simp [List.mapM_nil, pure, Except.pure] at h
      subst ys
      rfl
  | cons x xs ih =>
      cases hx : f x <;> cases ht : xs.mapM f <;>
        simp [List.mapM_cons, hx, ht, Bind.bind, Except.bind, pure, Except.pure] at h
      subst ys
      simp [ih ht]

theorem mapM_ok_source {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {x : α} (hx : x ∈ xs) :
    ∃ y ∈ ys, f x = .ok y := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons first rest ih =>
      cases hf : f first <;> cases ht : rest.mapM f <;>
        simp [List.mapM_cons, hf, ht, Bind.bind, Except.bind, pure, Except.pure] at h
      subst ys
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, by simp, hf⟩
      · rcases ih ht hx with ⟨y, hy, hfy⟩
        exact ⟨y, by simp [hy], hfy⟩

theorem mapM_ok_map_eq {f : α → Except ε β} {xs : List α} {ys : List β}
    {keySource : α → γ} {keyTarget : β → γ}
    (h : xs.mapM f = .ok ys)
    (hkey : ∀ x y, f x = .ok y → keyTarget y = keySource x) :
    ys.map keyTarget = xs.map keySource := by
  induction xs generalizing ys with
  | nil =>
      simp [List.mapM_nil, pure, Except.pure] at h
      subst ys
      rfl
  | cons x xs ih =>
      cases hx : f x <;> cases ht : xs.mapM f <;>
        simp [List.mapM_cons, hx, ht, Bind.bind, Except.bind, pure, Except.pure] at h
      subst ys
      simp [hkey _ _ hx, ih ht]

private theorem packageEntry_id {x : Package × Nat} {d : PackageDecl}
    (h : bindPackageEntry model x = .ok d) : d.id.val = x.2 := by
  unfold bindPackageEntry at h
  cases hq : checkQualification x.1.alias x.1.parent <;>
    cases hp : optionalPackage model x.1.parent <;>
    simp [hq, hp, Bind.bind, Except.bind, pure, Except.pure] at h
  subst d
  rfl

private theorem classEntry_id {x : Class × Nat} {d : ClassDecl}
    (h : bindClassEntry model x = .ok d) : d.id.val = x.2 := by
  unfold bindClassEntry at h
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    cases hs : x.1.directSupers.mapM (classId model) <;>
    simp [hq, hp, hs, Bind.bind, Except.bind, pure, Except.pure] at h
  subst d
  rfl

private theorem propertyEntry_id {x : Property × Nat} {d : PropertyDecl}
    (h : bindPropertyEntry model x = .ok d) : d.id.val = x.2 := by
  unfold bindPropertyEntry at h
  cases hq : checkQualification x.1.alias (some (ownerName x.1.owner)) <;>
    cases ho : bindOwner model x.1.owner <;>
    cases ht : bindType model x.1.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at h
  subst d
  rfl

private theorem associationEntry_id {x : Association × Nat} {d : AssociationDecl}
    (h : bindAssociationEntry model x = .ok d) : d.id.val = x.2 := by
  unfold bindAssociationEntry at h
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    cases hend : x.1.ends with
    | nil => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at h
    | cons first rest =>
      cases rest with
      | nil => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at h
      | cons second tail =>
        cases tail with
        | cons third tail => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at h
        | nil =>
          cases hf : propertyId model first <;> cases hs : propertyId model second <;>
            simp [hq, hp, hend, hf, hs, Bind.bind, Except.bind, pure, Except.pure] at h
          all_goals subst d; rfl

private theorem enumerationEntry_id {x : Enumeration × Nat} {d : EnumerationDecl}
    (h : bindEnumerationEntry model x = .ok d) : d.id.val = x.2 := by
  unfold bindEnumerationEntry at h
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    simp [hq, hp, Bind.bind, Except.bind, pure, Except.pure] at h
  subst d
  rfl

private theorem literalEntry_id {x : Literal × Nat} {d : LiteralDecl}
    (h : bindLiteralEntry model x = .ok d) : d.id.val = x.2 := by
  unfold bindLiteralEntry at h
  cases hq : checkQualification x.1.alias (some x.1.enumeration) <;>
    cases he : enumerationId model x.1.enumeration <;>
    simp [hq, he, Bind.bind, Except.bind, pure, Except.pure] at h
  subst d
  rfl

private theorem zipIdx_snd_nodup (xs : List α) : (xs.zipIdx.map Prod.snd).Nodup := by
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' _

private theorem nodup_of_map_nodup (f : α → β) {xs : List α}
    (h : (xs.map f).Nodup) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.nodup_cons] at h
      rw [List.nodup_cons]
      exact ⟨fun hx => h.1 (List.mem_map_of_mem hx), ih h.2⟩

/-- Numeric declaration identities are unique because each kind is allocated at
its position in the corresponding source list. -/
theorem ModelAllocation.uniqueIds (a : ModelAllocation model target) :
    uniqueBy PackageDecl.id target.packages ∧ uniqueBy ClassDecl.id target.classes ∧
    uniqueBy PropertyDecl.id target.properties ∧
    uniqueBy AssociationDecl.id target.associations ∧
    uniqueBy EnumerationDecl.id target.enumerations ∧
    uniqueBy LiteralDecl.id target.literals := by
  have hp := mapM_ok_map_eq a.packages (fun x y h => packageEntry_id h)
  have hc := mapM_ok_map_eq a.classes (fun x y h => classEntry_id h)
  have hpr := mapM_ok_map_eq a.properties (fun x y h => propertyEntry_id h)
  have ha := mapM_ok_map_eq a.associations (fun x y h => associationEntry_id h)
  have he := mapM_ok_map_eq a.enumerations (fun x y h => enumerationEntry_id h)
  have hl := mapM_ok_map_eq a.literals (fun x y h => literalEntry_id h)
  simp only [uniqueBy]
  constructor
  · apply nodup_of_map_nodup PackageId.val
    rw [List.map_map]
    rw [show (PackageId.val ∘ PackageDecl.id) = (fun y => y.id.val) by rfl]
    rw [hp]
    exact zipIdx_snd_nodup _
  · constructor
    · apply nodup_of_map_nodup ClassId.val
      rw [List.map_map]
      rw [show (ClassId.val ∘ ClassDecl.id) = (fun y => y.id.val) by rfl]
      rw [hc]
      exact zipIdx_snd_nodup _
    · constructor
      · apply nodup_of_map_nodup PropertyId.val
        rw [List.map_map]
        rw [show (PropertyId.val ∘ PropertyDecl.id) = (fun y => y.id.val) by rfl]
        rw [hpr]
        exact zipIdx_snd_nodup _
      · constructor
        · apply nodup_of_map_nodup AssociationId.val
          rw [List.map_map]
          rw [show (AssociationId.val ∘ AssociationDecl.id) = (fun y => y.id.val) by rfl]
          rw [ha]
          exact zipIdx_snd_nodup _
        · constructor
          · apply nodup_of_map_nodup EnumerationId.val
            rw [List.map_map]
            rw [show (EnumerationId.val ∘ EnumerationDecl.id) = (fun y => y.id.val) by rfl]
            rw [he]
            exact zipIdx_snd_nodup _
          · apply nodup_of_map_nodup LiteralId.val
            rw [List.map_map]
            rw [show (LiteralId.val ∘ LiteralDecl.id) = (fun y => y.id.val) by rfl]
            rw [hl]
            exact zipIdx_snd_nodup _

theorem ModelAllocation.lengths (a : ModelAllocation model target) :
    target.packages.length = model.packages.length ∧
    target.classes.length = model.classes.length ∧
    target.properties.length = model.properties.length ∧
    target.associations.length = model.associations.length ∧
    target.enumerations.length = model.enumerations.length ∧
    target.literals.length = model.literals.length := by
  have hp := mapM_ok_length (f := bindPackageEntry model) (xs := model.packages.zipIdx) a.packages
  have hc := mapM_ok_length (f := bindClassEntry model) (xs := model.classes.zipIdx) a.classes
  have hpr := mapM_ok_length (f := bindPropertyEntry model) (xs := model.properties.zipIdx) a.properties
  have ha := mapM_ok_length (f := bindAssociationEntry model) (xs := model.associations.zipIdx) a.associations
  have he := mapM_ok_length (f := bindEnumerationEntry model) (xs := model.enumerations.zipIdx) a.enumerations
  have hl := mapM_ok_length (f := bindLiteralEntry model) (xs := model.literals.zipIdx) a.literals
  rw [List.length_zipIdx] at hp hc hpr ha he hl
  exact ⟨hp, hc, hpr, ha, he, hl⟩

private theorem packageEntry_name {x : Package × Nat} {d : PackageDecl}
    (h : bindPackageEntry model x = .ok d) : d.name = some x.1.name := by
  unfold bindPackageEntry at h
  cases hq : checkQualification x.1.alias x.1.parent <;>
    cases hp : optionalPackage model x.1.parent <;>
    simp [hq, hp, Bind.bind, Except.bind, pure, Except.pure] at h
  subst d
  rfl

private theorem classEntry_name {x : Class × Nat} {d : ClassDecl}
    (h : bindClassEntry model x = .ok d) : d.name = some x.1.name := by
  unfold bindClassEntry at h
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    cases hs : x.1.directSupers.mapM (classId model) <;>
    simp [hq, hp, hs, Bind.bind, Except.bind, pure, Except.pure] at h
  subst d
  rfl

private theorem propertyEntry_data {x : Property × Nat} {d : PropertyDecl}
    (h : bindPropertyEntry model x = .ok d) :
    d.name = some x.1.name ∧ d.multiplicity = x.1.multiplicity ∧
      d.aggregation = x.1.aggregation ∧ d.isId = x.1.isId := by
  unfold bindPropertyEntry at h
  cases hq : checkQualification x.1.alias (some (ownerName x.1.owner)) <;>
    cases ho : bindOwner model x.1.owner <;>
    cases ht : bindType model x.1.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at h
  subst d
  simp

private theorem enumerationEntry_name {x : Enumeration × Nat} {d : EnumerationDecl}
    (h : bindEnumerationEntry model x = .ok d) : d.name = some x.1.name := by
  unfold bindEnumerationEntry at h
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    simp [hq, hp, Bind.bind, Except.bind, pure, Except.pure] at h
  subst d
  rfl

private theorem literalEntry_name {x : Literal × Nat} {d : LiteralDecl}
    (h : bindLiteralEntry model x = .ok d) : d.name = some x.1.name := by
  unfold bindLiteralEntry at h
  cases hq : checkQualification x.1.alias (some x.1.enumeration) <;>
    cases he : enumerationId model x.1.enumeration <;>
    simp [hq, he, Bind.bind, Except.bind, pure, Except.pure] at h
  subst d
  rfl

/-- Display-name validity and the non-binding property flags are copied exactly
from the source declarations selected by the successful allocation. -/
theorem ModelAllocation.packageNames (a : ModelAllocation model target)
    (h : ModelWellFormed model) : ∀ d ∈ target.packages, validName d.name := by
  intro d hd
  rcases (mapM_ok_mem_iff a.packages).mp hd with ⟨x, hx, hb⟩
  have hs := List.fst_mem_of_mem_zipIdx hx
  rw [packageEntry_name hb]
  simpa [validName, validDisplayName] using h.displayNames.1 x.1 hs

theorem ModelAllocation.classNames (a : ModelAllocation model target)
    (h : ModelWellFormed model) : ∀ d ∈ target.classes, validName d.name := by
  intro d hd
  rcases (mapM_ok_mem_iff a.classes).mp hd with ⟨x, hx, hb⟩
  have hs := List.fst_mem_of_mem_zipIdx hx
  rw [classEntry_name hb]
  simpa [validName, validDisplayName] using h.displayNames.2.1 x.1 hs

theorem ModelAllocation.propertyFacts (a : ModelAllocation model target)
    (h : ModelWellFormed model) :
    (∀ d ∈ target.properties, validName d.name) ∧
    (∀ d ∈ target.properties, multiplicityValid d.multiplicity) := by
  constructor
  · intro d hd
    rcases (mapM_ok_mem_iff a.properties).mp hd with ⟨x, hx, hb⟩
    have hs := List.fst_mem_of_mem_zipIdx hx
    rw [(propertyEntry_data hb).1]
    simpa [validName, validDisplayName] using h.displayNames.2.2.1 x.1 hs
  ·
    intro d hd
    rcases (mapM_ok_mem_iff a.properties).mp hd with ⟨x, hx, hb⟩
    have hs := List.fst_mem_of_mem_zipIdx hx
    rw [(propertyEntry_data hb).2.1]
    exact h.multiplicities x.1 hs

end VLMOF.Source
