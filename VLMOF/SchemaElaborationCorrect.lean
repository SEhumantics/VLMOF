import VLMOF.ElaborationComplete
import VLMOF.ClosureSaturation
import VLMOF.PackageClosureCorrect

/-!
# Preservation of model well-formedness by schema elaboration

The executable binder allocates each declaration at its source-list index.  The
lemmas below first expose that allocation from a successful `bindModel` run and
then transport every source well-formedness obligation to the resulting schema.
-/
namespace VLMOF.Source

variable {α β γ ε : Type} {model : Model} {target : Schema}
variable {name : Name}

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

private theorem uniqueBy_eq_of_mem_local {κ δ : Type} [DecidableEq κ] (key : δ → κ)
    {xs : List δ} (h : uniqueBy key xs) {left right : δ}
    (hl : left ∈ xs) (hr : right ∈ xs) (hk : key left = key right) : left = right := by
  induction xs generalizing left right with
  | nil => simp at hl
  | cons x xs ih =>
      simp only [uniqueBy, List.map_cons, List.nodup_cons] at h
      rcases h with ⟨hnot, htail⟩
      rcases List.mem_cons.mp hl with hleft | hl
      · subst left
        rcases List.mem_cons.mp hr with hright | hr
        · exact hright.symm
        · exfalso
          apply hnot
          rw [hk]
          exact List.mem_map.mpr ⟨right, hr, rfl⟩
      · rcases List.mem_cons.mp hr with hright | hr
        · subst right
          exfalso
          apply hnot
          rw [← hk]
          exact List.mem_map.mpr ⟨left, hl, rfl⟩
        · exact ih htail hl hr hk

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

private theorem associationEntry_name {x : Association × Nat} {d : AssociationDecl}
    (h : bindAssociationEntry model x = .ok d) : d.name = some x.1.name := by
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
          all_goals subst d
          all_goals rfl

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

theorem ModelAllocation.otherNames (a : ModelAllocation model target)
    (h : ModelWellFormed model) :
    (∀ d ∈ target.associations, validName d.name) ∧
    (∀ d ∈ target.enumerations, validName d.name) ∧
    (∀ d ∈ target.literals, validName d.name) := by
  constructor
  · intro d hd
    rcases (mapM_ok_mem_iff a.associations).mp hd with ⟨x, hx, hb⟩
    rw [associationEntry_name hb]
    exact h.displayNames.2.2.2.1 x.1 (List.fst_mem_of_mem_zipIdx hx)
  · constructor
    · intro d hd
      rcases (mapM_ok_mem_iff a.enumerations).mp hd with ⟨x, hx, hb⟩
      rw [enumerationEntry_name hb]
      exact h.displayNames.2.2.2.2.1 x.1 (List.fst_mem_of_mem_zipIdx hx)
    · intro d hd
      rcases (mapM_ok_mem_iff a.literals).mp hd with ⟨x, hx, hb⟩
      rw [literalEntry_name hb]
      exact h.displayNames.2.2.2.2.2 x.1 (List.fst_mem_of_mem_zipIdx hx)

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

/-- A successful resolver result addresses a source declaration at that exact
index, and a successful list allocation contains its translated target row. -/
theorem resolved_has_allocated {entries : List α} {targets : List β}
    (key : α → Name) (bindEntry : α × Nat → BindingResult β)
    (allocation : entries.zipIdx.mapM bindEntry = .ok targets)
    {kind : String} {name : Name} {index : Nat}
    (resolved : resolveIndex kind (entries.map key) name = .ok index) :
    ∃ source target,
      source ∈ entries ∧ key source = name ∧ target ∈ targets ∧
      bindEntry (source, index) = .ok target := by
  have hget := resolveIndex_getElem resolved
  rw [List.getElem?_map] at hget
  cases hs : entries[index]? with
  | none => simp [hs] at hget
  | some source =>
      simp [hs] at hget
      have hzip : (source, index) ∈ entries.zipIdx :=
        List.mk_mem_zipIdx_iff_getElem?.mpr hs
      rcases mapM_ok_source allocation hzip with ⟨translated, ht, hb⟩
      exact ⟨source, translated, List.fst_mem_of_mem_zipIdx hzip, hget, ht, hb⟩

private theorem packageId_resolve {name : Name} {id : PackageId}
    (h : packageId model name = .ok id) :
    resolveIndex "package" (model.packages.map Package.alias) name = .ok id.val := by
  unfold packageId at h
  cases hr : resolveIndex "package" (model.packages.map Package.alias) name <;>
    simp [hr, Except.map] at h
  subst id
  rfl

private theorem classId_resolve {name : Name} {id : ClassId}
    (h : classId model name = .ok id) :
    resolveIndex "class" (model.classes.map Class.alias) name = .ok id.val := by
  unfold classId at h
  cases hr : resolveIndex "class" (model.classes.map Class.alias) name <;>
    simp [hr, Except.map] at h
  subst id
  rfl

private theorem propertyId_resolve {name : Name} {id : PropertyId}
    (h : propertyId model name = .ok id) :
    resolveIndex "property" (model.properties.map Property.alias) name = .ok id.val := by
  unfold propertyId at h
  cases hr : resolveIndex "property" (model.properties.map Property.alias) name <;>
    simp [hr, Except.map] at h
  subst id
  rfl

private theorem associationId_resolve {name : Name} {id : AssociationId}
    (h : associationId model name = .ok id) :
    resolveIndex "association" (model.associations.map Association.alias) name = .ok id.val := by
  unfold associationId at h
  cases hr : resolveIndex "association" (model.associations.map Association.alias) name <;>
    simp [hr, Except.map] at h
  subst id
  rfl

private theorem enumerationId_resolve {name : Name} {id : EnumerationId}
    (h : enumerationId model name = .ok id) :
    resolveIndex "enumeration" (model.enumerations.map Enumeration.alias) name = .ok id.val := by
  unfold enumerationId at h
  cases hr : resolveIndex "enumeration" (model.enumerations.map Enumeration.alias) name <;>
    simp [hr, Except.map] at h
  subst id
  rfl

private theorem literalId_resolve {name : Name} {id : LiteralId}
    (h : literalId model name = .ok id) :
    resolveIndex "literal" (model.literals.map Literal.alias) name = .ok id.val := by
  unfold literalId at h
  cases hr : resolveIndex "literal" (model.literals.map Literal.alias) name <;>
    simp [hr, Except.map] at h
  subst id
  rfl

theorem ModelAllocation.packageForId (a : ModelAllocation model target)
    {id : PackageId}
    (h : packageId model name = .ok id) :
    ∃ source translated, source ∈ model.packages ∧ source.alias = name ∧
      translated ∈ target.packages ∧ translated.id = id ∧
      bindPackageEntry model (source, id.val) = .ok translated := by
  rcases resolved_has_allocated Package.alias (bindPackageEntry model) a.packages
      (packageId_resolve h) with ⟨source, translated, hs, hn, ht, hb⟩
  have hid : translated.id = id := by
    have hv := packageEntry_id hb
    calc translated.id = ⟨translated.id.val⟩ := by cases translated.id; rfl
      _ = ⟨id.val⟩ := congrArg PackageId.mk hv
      _ = id := by cases id; rfl
  exact ⟨source, translated, hs, hn, ht, hid, hb⟩

theorem ModelAllocation.classForId (a : ModelAllocation model target)
    {id : ClassId}
    (h : classId model name = .ok id) :
    ∃ source translated, source ∈ model.classes ∧ source.alias = name ∧
      translated ∈ target.classes ∧ translated.id = id ∧
      bindClassEntry model (source, id.val) = .ok translated := by
  rcases resolved_has_allocated Class.alias (bindClassEntry model) a.classes
      (classId_resolve h) with ⟨source, translated, hs, hn, ht, hb⟩
  have hid : translated.id = id := by
    have hv := classEntry_id hb
    calc translated.id = ⟨translated.id.val⟩ := by cases translated.id; rfl
      _ = ⟨id.val⟩ := congrArg ClassId.mk hv
      _ = id := by cases id; rfl
  exact ⟨source, translated, hs, hn, ht, hid, hb⟩

theorem ModelAllocation.propertyForId (a : ModelAllocation model target)
    {id : PropertyId}
    (h : propertyId model name = .ok id) :
    ∃ source translated, source ∈ model.properties ∧ source.alias = name ∧
      translated ∈ target.properties ∧ translated.id = id ∧
      bindPropertyEntry model (source, id.val) = .ok translated := by
  rcases resolved_has_allocated Property.alias (bindPropertyEntry model) a.properties
      (propertyId_resolve h) with ⟨source, translated, hs, hn, ht, hb⟩
  have hid : translated.id = id := by
    have hv := propertyEntry_id hb
    calc translated.id = ⟨translated.id.val⟩ := by cases translated.id; rfl
      _ = ⟨id.val⟩ := congrArg PropertyId.mk hv
      _ = id := by cases id; rfl
  exact ⟨source, translated, hs, hn, ht, hid, hb⟩

theorem ModelAllocation.associationForId (a : ModelAllocation model target)
    {id : AssociationId}
    (h : associationId model name = .ok id) :
    ∃ source translated, source ∈ model.associations ∧ source.alias = name ∧
      translated ∈ target.associations ∧ translated.id = id ∧
      bindAssociationEntry model (source, id.val) = .ok translated := by
  rcases resolved_has_allocated Association.alias (bindAssociationEntry model) a.associations
      (associationId_resolve h) with ⟨source, translated, hs, hn, ht, hb⟩
  have hid : translated.id = id := by
    have hv := associationEntry_id hb
    calc translated.id = ⟨translated.id.val⟩ := by cases translated.id; rfl
      _ = ⟨id.val⟩ := congrArg AssociationId.mk hv
      _ = id := by cases id; rfl
  exact ⟨source, translated, hs, hn, ht, hid, hb⟩

theorem ModelAllocation.enumerationForId (a : ModelAllocation model target)
    {id : EnumerationId}
    (h : enumerationId model name = .ok id) :
    ∃ source translated, source ∈ model.enumerations ∧ source.alias = name ∧
      translated ∈ target.enumerations ∧ translated.id = id ∧
      bindEnumerationEntry model (source, id.val) = .ok translated := by
  rcases resolved_has_allocated Enumeration.alias (bindEnumerationEntry model) a.enumerations
      (enumerationId_resolve h) with ⟨source, translated, hs, hn, ht, hb⟩
  have hid : translated.id = id := by
    have hv := enumerationEntry_id hb
    calc translated.id = ⟨translated.id.val⟩ := by cases translated.id; rfl
      _ = ⟨id.val⟩ := congrArg EnumerationId.mk hv
      _ = id := by cases id; rfl
  exact ⟨source, translated, hs, hn, ht, hid, hb⟩

theorem ModelAllocation.literalForId (a : ModelAllocation model target)
    {id : LiteralId}
    (h : literalId model name = .ok id) :
    ∃ source translated, source ∈ model.literals ∧ source.alias = name ∧
      translated ∈ target.literals ∧ translated.id = id ∧
      bindLiteralEntry model (source, id.val) = .ok translated := by
  rcases resolved_has_allocated Literal.alias (bindLiteralEntry model) a.literals
      (literalId_resolve h) with ⟨source, translated, hs, hn, ht, hb⟩
  have hid : translated.id = id := by
    have hv := literalEntry_id hb
    calc translated.id = ⟨translated.id.val⟩ := by cases translated.id; rfl
      _ = ⟨id.val⟩ := congrArg LiteralId.mk hv
      _ = id := by cases id; rfl
  exact ⟨source, translated, hs, hn, ht, hid, hb⟩

theorem ModelAllocation.packageResolved (a : ModelAllocation model target)
    {id : PackageId}
    (h : packageId model name = .ok id) : target.packageDecls id ≠ [] := by
  rcases a.packageForId h with ⟨_, d, _, _, hd, hid, _⟩
  intro hempty
  have : d ∈ target.packageDecls id := by simp [Schema.packageDecls, hd, hid]
  simpa [hempty] using this

theorem ModelAllocation.classResolved (a : ModelAllocation model target)
    {id : ClassId}
    (h : classId model name = .ok id) : target.classDecls id ≠ [] := by
  rcases a.classForId h with ⟨_, d, _, _, hd, hid, _⟩
  intro hempty
  have : d ∈ target.classDecls id := by simp [Schema.classDecls, hd, hid]
  simpa [hempty] using this

theorem ModelAllocation.propertyResolved (a : ModelAllocation model target)
    {id : PropertyId}
    (h : propertyId model name = .ok id) :
    ∃ d ∈ target.properties, d.id = id := by
  rcases a.propertyForId h with ⟨_, d, _, _, hd, hid, _⟩
  exact ⟨d, hd, hid⟩

theorem ModelAllocation.associationResolved (a : ModelAllocation model target)
    {id : AssociationId}
    (h : associationId model name = .ok id) :
    ∃ d ∈ target.associations, d.id = id := by
  rcases a.associationForId h with ⟨_, d, _, _, hd, hid, _⟩
  exact ⟨d, hd, hid⟩

theorem ModelAllocation.enumerationResolved (a : ModelAllocation model target)
    {id : EnumerationId}
    (h : enumerationId model name = .ok id) : target.enumerationDecls id ≠ [] := by
  rcases a.enumerationForId h with ⟨_, d, _, _, hd, hid, _⟩
  intro hempty
  have : d ∈ target.enumerationDecls id := by simp [Schema.enumerationDecls, hd, hid]
  simpa [hempty] using this

theorem ModelAllocation.literalResolved (a : ModelAllocation model target)
    {id : LiteralId}
    (h : literalId model name = .ok id) : target.literalDecls id ≠ [] := by
  rcases a.literalForId h with ⟨_, d, _, _, hd, hid, _⟩
  intro hempty
  have : d ∈ target.literalDecls id := by simp [Schema.literalDecls, hd, hid]
  simpa [hempty] using this

private theorem optionalPackage_target_resolved (a : ModelAllocation model target)
    {source : Option Name} {translated : Option PackageId}
    (hb : optionalPackage model source = .ok translated) {id : PackageId}
    (hid : translated = some id) : target.packageDecls id ≠ [] := by
  cases source with
  | none =>
      have heq : translated = none := by
        simpa [optionalPackage, pure, Except.pure] using (Except.ok.inj hb).symm
      rw [heq] at hid
      simp at hid
  | some name =>
      unfold optionalPackage at hb
      cases hp : packageId model name with
      | error error => simp [hp, Functor.map, Except.map] at hb
      | ok package =>
          simp [hp, Functor.map, Except.map] at hb
          have hi : id = package := Option.some.inj (hid.symm.trans hb.symm)
          subst id
          exact a.packageResolved hp

theorem ModelAllocation.packageParentsResolved (a : ModelAllocation model target) :
    ∀ d ∈ target.packages, ∀ id, d.parent = some id → target.packageDecls id ≠ [] := by
  intro d hd id hid
  rcases (mapM_ok_mem_iff a.packages).mp hd with ⟨x, _, hb⟩
  unfold bindPackageEntry at hb
  cases hq : checkQualification x.1.alias x.1.parent <;>
    cases hp : optionalPackage model x.1.parent <;>
    simp [hq, hp, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  exact optionalPackage_target_resolved a hp hid

theorem ModelAllocation.classPackagesResolved (a : ModelAllocation model target) :
    ∀ d ∈ target.classes, ∀ id, d.package = some id → target.packageDecls id ≠ [] := by
  intro d hd id hid
  rcases (mapM_ok_mem_iff a.classes).mp hd with ⟨x, _, hb⟩
  unfold bindClassEntry at hb
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    cases hs : x.1.directSupers.mapM (classId model) <;>
    simp [hq, hp, hs, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  exact optionalPackage_target_resolved a hp hid

theorem ModelAllocation.enumPackagesResolved (a : ModelAllocation model target) :
    ∀ d ∈ target.enumerations, ∀ id, d.package = some id → target.packageDecls id ≠ [] := by
  intro d hd id hid
  rcases (mapM_ok_mem_iff a.enumerations).mp hd with ⟨x, _, hb⟩
  unfold bindEnumerationEntry at hb
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    simp [hq, hp, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  exact optionalPackage_target_resolved a hp hid

theorem ModelAllocation.associationPackagesResolved (a : ModelAllocation model target) :
    ∀ d ∈ target.associations, ∀ id, d.package = some id → target.packageDecls id ≠ [] := by
  intro d hd id hid
  rcases (mapM_ok_mem_iff a.associations).mp hd with ⟨x, _, hb⟩
  unfold bindAssociationEntry at hb
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    cases hend : x.1.ends with
    | nil => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at hb
    | cons first rest =>
      cases rest with
      | nil => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at hb
      | cons second tail =>
        cases tail with
        | cons third tail => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at hb
        | nil =>
          cases hf : propertyId model first <;> cases hs : propertyId model second <;>
            simp [hq, hp, hend, hf, hs, Bind.bind, Except.bind, pure, Except.pure] at hb
          all_goals subst d
          all_goals exact optionalPackage_target_resolved a hp hid

theorem ModelAllocation.supersResolved (a : ModelAllocation model target) :
    ∀ d ∈ target.classes, ∀ id ∈ d.directSupers, target.classDecls id ≠ [] := by
  intro d hd id hid
  rcases (mapM_ok_mem_iff a.classes).mp hd with ⟨x, _, hb⟩
  unfold bindClassEntry at hb
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    cases hs : x.1.directSupers.mapM (classId model) <;>
    simp [hq, hp, hs, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  rcases (mapM_ok_mem_iff hs).mp hid with ⟨name, _, hn⟩
  exact a.classResolved hn

private theorem bindType_reference_resolved (a : ModelAllocation model target)
    {source : Source.ValueType} {id : ClassId}
    (hb : bindType model source = .ok (.reference id)) : target.classDecls id ≠ [] := by
  cases source with
  | boolean => simp [bindType, pure, Except.pure] at hb
  | integer => simp [bindType, pure, Except.pure] at hb
  | string => simp [bindType, pure, Except.pure] at hb
  | enumeration name => cases he : enumerationId model name <;> simp [bindType, he, Functor.map, Except.map] at hb
  | reference name =>
      cases hc : classId model name with
      | error error => simp [bindType, hc, Functor.map, Except.map] at hb
      | ok cid =>
          simp [bindType, hc, Functor.map, Except.map] at hb
          have hid : id = cid := hb.symm
          subst id
          exact a.classResolved hc

private theorem bindType_enumeration_resolved (a : ModelAllocation model target)
    {source : Source.ValueType} {id : EnumerationId}
    (hb : bindType model source = .ok (.enumeration id)) : target.enumerationDecls id ≠ [] := by
  cases source with
  | boolean => simp [bindType, pure, Except.pure] at hb
  | integer => simp [bindType, pure, Except.pure] at hb
  | string => simp [bindType, pure, Except.pure] at hb
  | enumeration name =>
      cases he : enumerationId model name with
      | error error => simp [bindType, he, Functor.map, Except.map] at hb
      | ok eid =>
          simp [bindType, he, Functor.map, Except.map] at hb
          have hid : id = eid := hb.symm
          subst id
          exact a.enumerationResolved he
  | reference name => cases hc : classId model name <;> simp [bindType, hc, Functor.map, Except.map] at hb

private theorem propertyEntry_type_binding {x : Property × Nat} {d : PropertyDecl}
    (hb : bindPropertyEntry model x = .ok d) : bindType model x.1.type = .ok d.type := by
  unfold bindPropertyEntry at hb
  cases hq : checkQualification x.1.alias (some (ownerName x.1.owner)) <;>
    cases ho : bindOwner model x.1.owner <;>
    cases ht : bindType model x.1.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  simpa using ht

private theorem propertyEntry_owner_binding {x : Property × Nat} {d : PropertyDecl}
    (hb : bindPropertyEntry model x = .ok d) : bindOwner model x.1.owner = .ok d.owner := by
  unfold bindPropertyEntry at hb
  cases hq : checkQualification x.1.alias (some (ownerName x.1.owner)) <;>
    cases ho : bindOwner model x.1.owner <;>
    cases ht : bindType model x.1.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  simpa using ho

private theorem associationEntry_ends {x : Association × Nat} {d : AssociationDecl}
    (hb : bindAssociationEntry model x = .ok d) :
    ∃ first second firstId secondId,
      x.1.ends = [first, second] ∧ propertyId model first = .ok firstId ∧
      propertyId model second = .ok secondId ∧ d.ends = (firstId, secondId) := by
  unfold bindAssociationEntry at hb
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    cases hend : x.1.ends with
    | nil => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at hb
    | cons first rest =>
      cases rest with
      | nil => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at hb
      | cons second tail =>
        cases tail with
        | cons third tail => simp [hq, hp, hend, Bind.bind, Except.bind, pure, Except.pure] at hb
        | nil =>
          cases hf : propertyId model first with
          | error error => simp [hq, hp, hend, hf, Bind.bind, Except.bind] at hb
          | ok firstId =>
            cases hs : propertyId model second with
            | error error => simp [hq, hp, hend, hf, hs, Bind.bind, Except.bind] at hb
            | ok secondId =>
              simp [hq, hp, hend, hf, hs, Bind.bind, Except.bind, pure, Except.pure] at hb
              all_goals try subst d
              all_goals exact ⟨first, second, firstId, secondId, rfl, hf, hs, rfl⟩

private theorem propertyEntry_resolves_id (h : ModelWellFormed model)
    {x : Property × Nat} {d : PropertyDecl} (hx : x ∈ model.properties.zipIdx)
    (hb : bindPropertyEntry model x = .ok d) : propertyId model x.1.alias = .ok d.id := by
  have hn : (model.properties.map Property.alias).Nodup := by
    have hall := h.uniqueQualifiedAliases
    simp only [uniqueAliases, aliases, List.nodup_append] at hall
    exact hall.1.1.1.2.1
  have hi : (model.properties.map Property.alias)[x.2]? = some x.1.alias := by
    have hg := List.mk_mem_zipIdx_iff_getElem?.mp hx
    simp [List.getElem?_map, hg]
  have hr : resolveIndex "property" (model.properties.map Property.alias) x.1.alias = .ok x.2 := by
    rw [resolveIndex_iff_uniqueAliasAt]
    exact uniqueAliasAt_of_nodup hn hi
  unfold propertyId
  rw [hr]
  simp [Except.map]
  cases hid : d.id with
  | mk value =>
      have hv := propertyEntry_id hb
      simp [hid] at hv
      subst value
      rfl

private theorem associationEntry_resolves_id (h : ModelWellFormed model)
    {x : Association × Nat} {d : AssociationDecl} (hx : x ∈ model.associations.zipIdx)
    (hb : bindAssociationEntry model x = .ok d) : associationId model x.1.alias = .ok d.id := by
  have hn : (model.associations.map Association.alias).Nodup := by
    have hall := h.uniqueQualifiedAliases
    simp only [uniqueAliases, aliases, List.nodup_append] at hall
    exact hall.1.1.2.1
  have hi : (model.associations.map Association.alias)[x.2]? = some x.1.alias := by
    have hg := List.mk_mem_zipIdx_iff_getElem?.mp hx
    simp [List.getElem?_map, hg]
  have hr : resolveIndex "association" (model.associations.map Association.alias) x.1.alias = .ok x.2 := by
    rw [resolveIndex_iff_uniqueAliasAt]
    exact uniqueAliasAt_of_nodup hn hi
  unfold associationId
  rw [hr]
  simp [Except.map]
  cases hid : d.id with
  | mk value =>
      have hv := associationEntry_id hb
      simp [hid] at hv
      subst value
      rfl

theorem ModelAllocation.propertyForSource (a : ModelAllocation model target)
    {source : Property} (hs : source ∈ model.properties) :
    ∃ index translated, (source, index) ∈ model.properties.zipIdx ∧
      translated ∈ target.properties ∧
      bindPropertyEntry model (source, index) = .ok translated := by
  obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp hs
  have hz : (source, index) ∈ model.properties.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hi
  rcases mapM_ok_source a.properties hz with ⟨translated, ht, hb⟩
  exact ⟨index, translated, hz, ht, hb⟩

private theorem ownerMatches_translated {sa : Association} {ta : AssociationDecl}
    {sp : Property} {tp : PropertyDecl}
    (ha : associationId model sa.alias = .ok ta.id)
    (hp : bindOwner model sp.owner = .ok tp.owner)
    (hs : ownerMatches sa sp) : ownerMatchesEnd ta tp := by
  cases ho : sp.owner with
  | «class» name =>
      cases hr : classId model name <;>
        simp [ho, bindOwner, hr, Functor.map, Except.map] at hp
      unfold ownerMatchesEnd
      rw [← hp]
      trivial
  | association name =>
      cases hr : associationId model name <;>
        simp [ho, bindOwner, hr, Functor.map, Except.map] at hp
      unfold ownerMatchesEnd
      rw [← hp]
      unfold ownerMatches at hs
      rw [ho] at hs
      subst name
      exact Except.ok.inj (hr.symm.trans ha)

private theorem classOwnerSource_translated {sp sq : Property} {tp tq : PropertyDecl}
    (hop : bindOwner model sp.owner = .ok tp.owner)
    (htq : bindType model sq.type = .ok tq.type)
    (hs : classOwnerMatchesSource sp sq) : classOwnerIsSource tp tq := by
  cases ho : sp.owner <;> cases hv : sq.type <;>
    simp [classOwnerMatchesSource, ho, hv] at hs
  case «class».reference owner source =>
    cases hc : classId model owner <;>
      simp [ho, bindOwner, hc, Functor.map, Except.map] at hop
    cases hsId : classId model source <;>
      simp [hv, bindType, hsId, Functor.map, Except.map] at htq
    unfold classOwnerIsSource
    rw [← hop, ← htq]
    exact Except.ok.inj (hc.symm.trans (hs ▸ hsId))
  case association.reference owner source =>
    cases ha : associationId model owner <;>
      simp [ho, bindOwner, ha, Functor.map, Except.map] at hop
    cases hsId : classId model source <;>
      simp [hv, bindType, hsId, Functor.map, Except.map] at htq
    unfold classOwnerIsSource
    rw [← hop, ← htq]
    trivial

private theorem atMostOneOwner_translated {sp sq : Property} {tp tq : PropertyDecl}
    (hp : bindOwner model sp.owner = .ok tp.owner)
    (hq : bindOwner model sq.owner = .ok tq.owner)
    (hs : atMostOneAssociationOwner sp sq) : atMostOneAssociationOwned tp tq := by
  cases hop : sp.owner <;> cases hoq : sq.owner <;>
    simp [atMostOneAssociationOwner, hop, hoq] at hs
  all_goals simp [hop, bindOwner, hoq, Functor.map, Except.map] at hp hq
  all_goals split at hp <;> simp_all [atMostOneAssociationOwned]
  all_goals split at hq <;> simp_all [atMostOneAssociationOwned]
  all_goals rw [← hp, ← hq]
  all_goals trivial

theorem ModelAllocation.propertyTypesResolved (a : ModelAllocation model target) :
    ∀ d ∈ target.properties, match d.type with
      | .reference id => target.classDecls id ≠ []
      | .enumeration id => target.enumerationDecls id ≠ []
      | _ => True := by
  intro d hd
  rcases (mapM_ok_mem_iff a.properties).mp hd with ⟨x, _, hb⟩
  have ht := propertyEntry_type_binding hb
  cases htype : d.type with
  | boolean => trivial
  | integer => trivial
  | string => trivial
  | enumeration id => exact bindType_enumeration_resolved a (htype ▸ ht)
  | reference id => exact bindType_reference_resolved a (htype ▸ ht)

theorem ModelAllocation.literalsResolved (a : ModelAllocation model target) :
    ∀ d ∈ target.literals, target.enumerationDecls d.enumeration ≠ [] := by
  intro d hd
  rcases (mapM_ok_mem_iff a.literals).mp hd with ⟨x, _, hb⟩
  unfold bindLiteralEntry at hb
  cases hq : checkQualification x.1.alias (some x.1.enumeration) <;>
    cases he : enumerationId model x.1.enumeration <;>
    simp [hq, he, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  exact a.enumerationResolved he

theorem ModelAllocation.compositeReferences (a : ModelAllocation model target)
    (h : ModelWellFormed model) :
    ∀ d ∈ target.properties, d.aggregation = .composite →
      ∃ id, d.type = .reference id := by
  intro d hd hc
  rcases (mapM_ok_mem_iff a.properties).mp hd with ⟨x, hx, hb⟩
  have hs := List.fst_mem_of_mem_zipIdx hx
  have hagg : x.1.aggregation = .composite := by
    rw [← (propertyEntry_data hb).2.2.1]
    exact hc
  rcases h.compositesAreReferences x.1 hs hagg with ⟨name, hsource⟩
  have ht := propertyEntry_type_binding hb
  rw [hsource] at ht
  unfold bindType at ht
  cases hid : classId model name with
  | error error => simp [hid, Functor.map, Except.map] at ht
  | ok id =>
      have : d.type = .reference id := by
        simpa [hid, Functor.map, Except.map] using ht.symm
      exact ⟨id, this⟩

def ClassAliasAt (model : Model) (id : ClassId) (name : Name) : Prop :=
  (model.classes.map Class.alias)[id.val]? = some name

def PackageAliasAt (model : Model) (id : PackageId) (name : Name) : Prop :=
  (model.packages.map Package.alias)[id.val]? = some name

private theorem classAliasAt_unique (h : ModelWellFormed model)
    {id : ClassId} {first second : Name}
    (ha : ClassAliasAt model id first) (hb : ClassAliasAt model id second) : first = second := by
  exact Option.some.inj (ha.symm.trans hb)

private theorem packageAliasAt_unique (h : ModelWellFormed model)
    {id : PackageId} {first second : Name}
    (ha : PackageAliasAt model id first) (hb : PackageAliasAt model id second) : first = second := by
  exact Option.some.inj (ha.symm.trans hb)

/-- Every allocated target class retains its source alias, and every target direct
super retains the symbolic superclass alias from the same source row. -/
theorem ModelAllocation.classEdgeSource (a : ModelAllocation model target)
    {d : ClassDecl} (hd : d ∈ target.classes) :
    ∃ source ∈ model.classes,
      ClassAliasAt model d.id source.alias ∧
      ∀ super ∈ d.directSupers, ∃ name ∈ source.directSupers,
        ClassAliasAt model super name := by
  rcases (mapM_ok_mem_iff a.classes).mp hd with ⟨x, hx, hb⟩
  have hsource := List.fst_mem_of_mem_zipIdx hx
  unfold bindClassEntry at hb
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    cases hs : x.1.directSupers.mapM (classId model) <;>
    simp [hq, hp, hs, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  refine ⟨x.1, hsource, ?_, ?_⟩
  · have hg := List.mk_mem_zipIdx_iff_getElem?.mp hx
    simp [ClassAliasAt, List.getElem?_map, hg]
  · intro super hsuper
    rcases (mapM_ok_mem_iff hs).mp hsuper with ⟨name, hn, hr⟩
    exact ⟨name, hn, resolveIndex_getElem (classId_resolve hr)⟩

theorem superPath_to_classAncestor (h : ModelWellFormed model)
    (a : ModelAllocation model target) {start finish : ClassId} {n : Nat}
    (path : SuperPath target start finish n)
    {sourceStart sourceFinish : Name}
    (hs : ClassAliasAt model start sourceStart)
    (hf : ClassAliasAt model finish sourceFinish) :
    ClassAncestor model sourceStart sourceFinish := by
  induction path generalizing sourceStart sourceFinish with
  | refl =>
      rw [classAliasAt_unique h hs hf]
      exact .refl _
  | @step here next n path hedge ih =>
      rcases hedge with ⟨d, hd, hid, hn⟩
      rcases a.classEdgeSource hd with ⟨source, hsource, hhere, hedges⟩
      rw [hid] at hhere
      rcases hedges next hn with ⟨nextName, hnext, hnextAlias⟩
      have hpre := ih hs hhere
      have suffix : ClassAncestor model sourceStart nextName :=
        .step hpre ⟨source, hsource, rfl, hnext⟩
      rw [classAliasAt_unique h hnextAlias hf] at suffix
      exact suffix

theorem isSubtype_to_classAncestor (h : ModelWellFormed model)
    (a : ModelAllocation model target) {start finish : ClassId}
    {sourceStart sourceFinish : Name}
    (path : target.isSubtype start finish)
    (hs : ClassAliasAt model start sourceStart)
    (hf : ClassAliasAt model finish sourceFinish) :
    ClassAncestor model sourceStart sourceFinish := by
  rcases target.isSubtype_implies_superReachable path with ⟨n, hp⟩
  exact superPath_to_classAncestor h a hp hs hf

/-- A stored target package-parent edge reflects the exact symbolic parent edge
from the source row that allocated the child. -/
theorem ModelAllocation.packageEdgeSource (a : ModelAllocation model target)
    {d : PackageDecl} (hd : d ∈ target.packages) :
    ∃ source ∈ model.packages,
      PackageAliasAt model d.id source.alias ∧
      ∀ parent, d.parent = some parent → ∃ name,
        source.parent = some name ∧ PackageAliasAt model parent name := by
  rcases (mapM_ok_mem_iff a.packages).mp hd with ⟨x, hx, hb⟩
  have hsource := List.fst_mem_of_mem_zipIdx hx
  unfold bindPackageEntry at hb
  cases hq : checkQualification x.1.alias x.1.parent <;>
    cases hp : optionalPackage model x.1.parent <;>
    simp [hq, hp, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  refine ⟨x.1, hsource, ?_, ?_⟩
  · have hg := List.mk_mem_zipIdx_iff_getElem?.mp hx
    simp [PackageAliasAt, List.getElem?_map, hg]
  · intro parent hparent
    cases hs : x.1.parent with
    | none =>
        simp [hs, optionalPackage, pure, Except.pure] at hp
        rw [← hp] at hparent
        simp at hparent
    | some name =>
        cases hr : packageId model name with
        | error error => simp [hs, optionalPackage, hr, Functor.map, Except.map] at hp
        | ok id =>
            simp [hs, optionalPackage, hr, Functor.map, Except.map] at hp
            rw [← hp] at hparent
            have hid : id = parent := Option.some.inj hparent
            subst parent
            exact ⟨name, rfl, resolveIndex_getElem (packageId_resolve hr)⟩

theorem packagePath_to_packageAncestor (h : ModelWellFormed model)
    (a : ModelAllocation model target) {start finish : PackageId}
    (path : StoredPath (PackageParentEdge target) start finish)
    {sourceStart sourceFinish : Name}
    (hs : PackageAliasAt model start sourceStart)
    (hf : PackageAliasAt model finish sourceFinish) :
    PackageAncestor model sourceStart sourceFinish := by
  induction path generalizing sourceStart sourceFinish with
  | refl =>
      rw [packageAliasAt_unique h hs hf]
      exact .refl _
  | @step here next path hedge ih =>
      rcases hedge with ⟨d, hd, hid, hp⟩
      rcases a.packageEdgeSource hd with ⟨source, hsource, hhere, hedgeSource⟩
      rw [hid] at hhere
      rcases hedgeSource next hp with ⟨parentName, hparent, hparentAlias⟩
      have hpre := ih hs hhere
      have hsuffix : PackageAncestor model sourceStart parentName :=
        .step hpre ⟨source, hsource, rfl, hparent⟩
      rw [packageAliasAt_unique h hparentAlias hf] at hsuffix
      exact hsuffix

theorem packageAncestors_to_packageAncestor (h : ModelWellFormed model)
    (a : ModelAllocation model target) {start finish : PackageId}
    {sourceStart sourceFinish : Name}
    (path : finish ∈ target.packageAncestors start)
    (hs : PackageAliasAt model start sourceStart)
    (hf : PackageAliasAt model finish sourceFinish) :
    PackageAncestor model sourceStart sourceFinish := by
  unfold Schema.packageAncestors at path
  rw [List.mem_eraseDups] at path
  exact packagePath_to_packageAncestor h a (packageClosure_sound target path) hs hf

theorem ModelAllocation.inheritanceAcyclic (a : ModelAllocation model target)
    (h : ModelWellFormed model) :
    ∀ d ∈ target.classes, ∀ super ∈ d.directSupers,
      d.id ∉ target.ancestors super := by
  intro d hd super hsuper hcycle
  rcases a.classEdgeSource hd with ⟨source, hsource, hclass, hedges⟩
  rcases hedges super hsuper with ⟨superName, hsuperName, hsuperAlias⟩
  have sourceCycle : ClassAncestor model superName source.alias :=
    isSubtype_to_classAncestor h a hcycle hsuperAlias hclass
  exact h.inheritanceAcyclic source hsource superName hsuperName sourceCycle

theorem ModelAllocation.packageAcyclic (a : ModelAllocation model target)
    (h : ModelWellFormed model) :
    ∀ d ∈ target.packages, ∀ parent, d.parent = some parent →
      d.id ∉ target.packageAncestors parent := by
  intro d hd parent hparent hcycle
  rcases a.packageEdgeSource hd with ⟨source, hsource, hpackage, hedge⟩
  rcases hedge parent hparent with ⟨parentName, hparentName, hparentAlias⟩
  have sourceCycle : PackageAncestor model parentName source.alias :=
    packageAncestors_to_packageAncestor h a hcycle hparentAlias hpackage
  exact h.packageAcyclic source hsource parentName hparentName sourceCycle

theorem ModelAllocation.propertyOwnersResolved (a : ModelAllocation model target)
    (h : ModelWellFormed model) :
    ∀ p ∈ target.properties, match p.owner with
      | .class c => target.classDecls c ≠ []
      | .association aid => ∃ d ∈ target.associations, d.id = aid ∧
          (d.ends.1 = p.id ∨ d.ends.2 = p.id) := by
  intro p hp
  rcases (mapM_ok_mem_iff a.properties).mp hp with ⟨x, hx, hb⟩
  have hsource := List.fst_mem_of_mem_zipIdx hx
  have howner := propertyEntry_owner_binding hb
  have hpid := propertyEntry_resolves_id h hx hb
  cases hsowner : x.1.owner with
  | «class» className =>
      cases hc : classId model className with
      | error error => simp [hsowner, bindOwner, hc, Functor.map, Except.map] at howner
      | ok classTarget =>
          simp [hsowner, bindOwner, hc, Functor.map, Except.map] at howner
          rw [← howner]
          exact a.classResolved hc
  | association associationName =>
      cases haid : associationId model associationName with
      | error error => simp [hsowner, bindOwner, haid, Functor.map, Except.map] at howner
      | ok associationTarget =>
          simp [hsowner, bindOwner, haid, Functor.map, Except.map] at howner
          rw [← howner]
          have hao := h.associationOwnedEnds x.1 hsource
          rw [hsowner] at hao
          rcases hao with ⟨sourceAssociation, hsa, halias, hendMem⟩
          obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp hsa
          have hz : (sourceAssociation, index) ∈ model.associations.zipIdx :=
            List.mk_mem_zipIdx_iff_getElem?.mpr hi
          rcases mapM_ok_source a.associations hz with ⟨translated, ht, hbind⟩
          rcases associationEntry_ends hbind with
            ⟨first, second, firstId, secondId, hends, hfirst, hsecond, htends⟩
          have haid' := associationEntry_resolves_id h hz hbind
          have htranslatedId : translated.id = associationTarget := by
            apply Except.ok.inj
            exact haid'.symm.trans (halias ▸ haid)
          refine ⟨translated, ht, htranslatedId, ?_⟩
          rw [hends] at hendMem
          simp at hendMem
          rcases hendMem with heq | heq
          · rw [htends]
            left
            have : firstId = p.id := Except.ok.inj (hfirst.symm.trans (heq ▸ hpid))
            exact this
          · rw [htends]
            right
            have : secondId = p.id := Except.ok.inj (hsecond.symm.trans (heq ▸ hpid))
            exact this

theorem ModelAllocation.associationEnds (a : ModelAllocation model target)
    (h : ModelWellFormed model) :
    ∀ association ∈ target.associations, ∃ p q,
      association.ends = (p.id, q.id) ∧ p ∈ target.properties ∧ q ∈ target.properties ∧
      p.id ≠ q.id ∧ (∃ pc, p.type = .reference pc) ∧
      (∃ qc, q.type = .reference qc) ∧ ownerMatchesEnd association p ∧
      ownerMatchesEnd association q ∧ classOwnerIsSource p q ∧
      classOwnerIsSource q p ∧ atMostOneAssociationOwned p q ∧
      ¬(p.aggregation = .composite ∧ q.aggregation = .composite) := by
  intro association ha
  rcases (mapM_ok_mem_iff a.associations).mp ha with ⟨x, hx, hb⟩
  have hsource := List.fst_mem_of_mem_zipIdx hx
  rcases h.associationEnds x.1 hsource with
    ⟨sp, sq, hsourceEnds, hsp, hsq, hneq, hpt, hqt, hop, hoq,
      hsourcepq, hsourceqp, hone, hcomposite⟩
  rcases a.propertyForSource hsp with ⟨pi, p, hpz, hp, hpb⟩
  rcases a.propertyForSource hsq with ⟨qi, q, hqz, hq, hqb⟩
  have hpid := propertyEntry_resolves_id h hpz hpb
  have hqid := propertyEntry_resolves_id h hqz hqb
  have hpo := propertyEntry_owner_binding hpb
  have hqo := propertyEntry_owner_binding hqb
  have hpty := propertyEntry_type_binding hpb
  have hqty := propertyEntry_type_binding hqb
  have haid := associationEntry_resolves_id h hx hb
  rcases associationEntry_ends hb with
    ⟨first, second, firstId, secondId, hends, hfirst, hsecond, htends⟩
  have hpAlias : first = sp.alias := by
    simpa [hsourceEnds] using (congrArg List.head? hends).symm
  have hqAlias : second = sq.alias := by
    have := congrArg (fun xs => xs.drop 1 |>.head?) hends
    simpa [hsourceEnds] using this.symm
  have hfirstId : firstId = p.id := Except.ok.inj (hfirst.symm.trans (hpAlias ▸ hpid))
  have hsecondId : secondId = q.id := Except.ok.inj (hsecond.symm.trans (hqAlias ▸ hqid))
  refine ⟨p, q, ?_, hp, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hfirstId, hsecondId] using htends
  · intro heq
    have hi := resolveIndex_getElem (propertyId_resolve hpid)
    have hj := resolveIndex_getElem (propertyId_resolve hqid)
    rw [heq] at hi
    exact hneq (Option.some.inj (hi.symm.trans hj))
  · rcases hpt with ⟨source, hs⟩
    rw [hs] at hpty
    cases hc : classId model source <;> simp [bindType, hc, Functor.map, Except.map] at hpty
    exact ⟨_, hpty.symm⟩
  · rcases hqt with ⟨source, hs⟩
    rw [hs] at hqty
    cases hc : classId model source <;> simp [bindType, hc, Functor.map, Except.map] at hqty
    exact ⟨_, hqty.symm⟩
  · exact ownerMatches_translated haid hpo hop
  · exact ownerMatches_translated haid hqo hoq
  · exact classOwnerSource_translated hpo hqty hsourcepq
  · exact classOwnerSource_translated hqo hpty hsourceqp
  · exact atMostOneOwner_translated hpo hqo hone
  · intro hc
    apply hcomposite
    exact ⟨(propertyEntry_data hpb).2.2.1.symm.trans hc.1,
      (propertyEntry_data hqb).2.2.1.symm.trans hc.2⟩

theorem ModelAllocation.containerUpperOne (a : ModelAllocation model target)
    (h : ModelWellFormed model) :
    ∀ association ∈ target.associations, ∀ p q,
      association.ends = (p.id, q.id) → p ∈ target.properties → q ∈ target.properties →
      (p.aggregation = .composite → q.multiplicity.upper = .finite 1) ∧
      (q.aggregation = .composite → p.multiplicity.upper = .finite 1) := by
  intro association ha p q hendsTarget hp hq
  rcases (mapM_ok_mem_iff a.associations).mp ha with ⟨x, hx, hb⟩
  have hsource := List.fst_mem_of_mem_zipIdx hx
  rcases h.associationEnds x.1 hsource with ⟨sp, sq, hendsSource, hsp, hsq, _⟩
  rcases a.propertyForSource hsp with ⟨pi, tp, hpz, htp, hpb⟩
  rcases a.propertyForSource hsq with ⟨qi, tq, hqz, htq, hqb⟩
  have hpid := propertyEntry_resolves_id h hpz hpb
  have hqid := propertyEntry_resolves_id h hqz hqb
  rcases associationEntry_ends hb with
    ⟨first, second, firstId, secondId, hends, hfirst, hsecond, htends⟩
  have hpAlias : first = sp.alias := by
    simpa [hendsSource] using (congrArg List.head? hends).symm
  have hqAlias : second = sq.alias := by
    have hh := congrArg (fun xs => xs.drop 1 |>.head?) hends
    simpa [hendsSource] using hh.symm
  have hfirstId : firstId = tp.id := Except.ok.inj (hfirst.symm.trans (hpAlias ▸ hpid))
  have hsecondId : secondId = tq.id := Except.ok.inj (hsecond.symm.trans (hqAlias ▸ hqid))
  have hpair : association.ends = (tp.id, tq.id) := by
    simpa [hfirstId, hsecondId] using htends
  have hpeq : p = tp := by
    apply uniqueBy_eq_of_mem_local PropertyDecl.id a.uniqueIds.2.2.1 hp htp
    exact congrArg Prod.fst (hendsTarget.symm.trans hpair)
  have hqeq : q = tq := by
    apply uniqueBy_eq_of_mem_local PropertyDecl.id a.uniqueIds.2.2.1 hq htq
    exact congrArg Prod.snd (hendsTarget.symm.trans hpair)
  subst p
  subst q
  have hsourceUpper := h.containerUpperOne x.1 hsource sp sq hendsSource hsp hsq
  constructor
  · intro hc
    have hcSource : sp.aggregation = .composite :=
      (propertyEntry_data hpb).2.2.1.symm.trans hc
    rw [(propertyEntry_data hqb).2.1]
    exact hsourceUpper.1 hcSource
  · intro hc
    have hcSource : sq.aggregation = .composite :=
      (propertyEntry_data hqb).2.2.1.symm.trans hc
    rw [(propertyEntry_data hpb).2.1]
    exact hsourceUpper.2 hcSource

private theorem propertyIds_eq_iff {first second : Name} {firstId secondId : PropertyId}
    (hf : propertyId model first = .ok firstId)
    (hs : propertyId model second = .ok secondId) : firstId = secondId ↔ first = second := by
  constructor
  · intro hid
    have hi := resolveIndex_getElem (propertyId_resolve hf)
    have hj := resolveIndex_getElem (propertyId_resolve hs)
    rw [hid] at hi
    exact Option.some.inj (hi.symm.trans hj)
  · intro hn
    subst second
    exact Except.ok.inj (hf.symm.trans hs)

private def targetEndHit (id : PropertyId) (association : AssociationDecl) : Nat :=
  if association.ends.1 = id then 1 else if association.ends.2 = id then 1 else 0

private def sourceEndHit (alias : Name) (association : Association) : Nat :=
  if alias ∈ association.ends then 1 else 0

private theorem associationEndHit_translated
    {source : Association} {translated : AssociationDecl} {property : Property}
    {propertyTarget : PropertyDecl} {index : Nat}
    (hb : bindAssociationEntry model (source, index) = .ok translated)
    (hp : propertyId model property.alias = .ok propertyTarget.id) :
    targetEndHit propertyTarget.id translated = sourceEndHit property.alias source := by
  rcases associationEntry_ends hb with
    ⟨first, second, firstId, secondId, hends, hfirst, hsecond, htends⟩
  have hf : (firstId = propertyTarget.id) ↔ (first = property.alias) := propertyIds_eq_iff hfirst hp
  have hsnd : (secondId = propertyTarget.id) ↔ (second = property.alias) := propertyIds_eq_iff hsecond hp
  unfold targetEndHit sourceEndHit
  rw [htends]
  simp only [Prod.fst, Prod.snd]
  rw [hends]
  simp only [List.mem_cons, List.mem_singleton]
  by_cases hfirstEq : first = property.alias
  · simp [hfirstEq, hf]
  · by_cases hsecondEq : second = property.alias
    · simp [hfirstEq, hsecondEq, hf, hsnd]
    · simp [hfirstEq, hsecondEq, hf, hsnd, Ne.symm hfirstEq, Ne.symm hsecondEq]

theorem ModelAllocation.endMembershipUnique (a : ModelAllocation model target)
    (h : ModelWellFormed model) :
    ∀ p ∈ target.properties, (target.oppositeCandidates p.id).length ≤ 1 := by
  intro p hp
  rcases (mapM_ok_mem_iff a.properties).mp hp with ⟨x, hx, hb⟩
  have hsource := List.fst_mem_of_mem_zipIdx hx
  have hpid := propertyEntry_resolves_id h hx hb
  have hmap : target.associations.map (targetEndHit p.id) =
      model.associations.zipIdx.map (fun z => sourceEndHit x.1.alias z.1) := by
    exact mapM_ok_map_eq a.associations (fun z translated hbind =>
      associationEndHit_translated hbind hpid)
  have hmap' : target.associations.map (targetEndHit p.id) =
      model.associations.map (sourceEndHit x.1.alias) := by
    rw [hmap]
    have aux : ∀ (xs : List Association) (i : Nat),
        (xs.zipIdx i).map (fun z => sourceEndHit x.1.alias z.1) =
          xs.map (sourceEndHit x.1.alias) := by
      intro xs i
      induction xs generalizing i with
      | nil => simp
      | cons first rest ih => simp [List.zipIdx, ih]
    exact aux model.associations 0
  have hlenTarget : (target.oppositeCandidates p.id).length =
      (target.associations.map (targetEndHit p.id)).sum := by
    unfold Schema.oppositeCandidates
    have aux : ∀ xs : List AssociationDecl,
        (xs.flatMap fun association =>
          if association.ends.1 = p.id then [association.ends.2]
          else if association.ends.2 = p.id then [association.ends.1] else []).length =
        (xs.map (targetEndHit p.id)).sum := by
      intro xs
      induction xs with
      | nil => simp
      | cons association rest ih =>
          by_cases hf : association.ends.1 = p.id <;>
            by_cases hs : association.ends.2 = p.id <;>
            simp [targetEndHit, hf, hs, ih] <;> omega
    exact aux target.associations
  have hlenSource :
      (model.associations.flatMap fun association =>
        if x.1.alias ∈ association.ends then [association.alias] else []).length =
      (model.associations.map (sourceEndHit x.1.alias)).sum := by
    have aux : ∀ xs : List Association,
        (xs.flatMap fun association =>
          if x.1.alias ∈ association.ends then [association.alias] else []).length =
        (xs.map (sourceEndHit x.1.alias)).sum := by
      intro xs
      induction xs with
      | nil => simp
      | cons association rest ih =>
          by_cases hm : x.1.alias ∈ association.ends <;>
            simp [sourceEndHit, hm, ih] <;> omega
    exact aux model.associations
  rw [hlenTarget, hmap', ← hlenSource]
  exact h.endMembershipUnique x.1 hsource

private theorem ModelAllocation.inheritedPropertySource (a : ModelAllocation model target)
    (h : ModelWellFormed model) {c : ClassDecl} (hc : c ∈ target.classes)
    {p : PropertyDecl} (hp : p ∈ target.properties)
    (hselected : p.isId && match p.owner with
      | .class owner => (target.ancestors c.id).contains owner
      | .association _ => false) :
    ∃ sourceClass ∈ model.classes, ∃ sourceProperty ∈ model.properties,
      ClassAliasAt model c.id sourceClass.alias ∧ sourceProperty.isId = true ∧
      (∃ owner, sourceProperty.owner = .class owner ∧
        ClassAncestor model sourceClass.alias owner) ∧
      propertyId model sourceProperty.alias = .ok p.id := by
  rcases a.classEdgeSource hc with ⟨sourceClass, hsourceClass, hcAlias, _⟩
  rcases (mapM_ok_mem_iff a.properties).mp hp with ⟨x, hx, hb⟩
  have hsourceProperty := List.fst_mem_of_mem_zipIdx hx
  have hid : p.isId = true := (Bool.and_eq_true_iff.mp hselected).1
  have hownerSelected := (Bool.and_eq_true_iff.mp hselected).2
  have hownerBinding := propertyEntry_owner_binding hb
  cases hsourceOwner : x.1.owner with
  | association name =>
      cases ha : associationId model name <;>
        simp [hsourceOwner, bindOwner, ha, Functor.map, Except.map] at hownerBinding
      rw [← hownerBinding] at hownerSelected
      simp at hownerSelected
  | «class» ownerName =>
      cases ho : classId model ownerName with
      | error error =>
          simp [hsourceOwner, bindOwner, ho, Functor.map, Except.map] at hownerBinding
      | ok ownerId =>
          simp [hsourceOwner, bindOwner, ho, Functor.map, Except.map] at hownerBinding
          rw [← hownerBinding] at hownerSelected
          have hancestorMem : ownerId ∈ target.ancestors c.id :=
            List.contains_iff_mem.mp hownerSelected
          have hownerAlias : ClassAliasAt model ownerId ownerName :=
            resolveIndex_getElem (classId_resolve ho)
          have hancestor : ClassAncestor model sourceClass.alias ownerName :=
            isSubtype_to_classAncestor h a hancestorMem hcAlias hownerAlias
          refine ⟨sourceClass, hsourceClass, x.1, hsourceProperty, hcAlias, ?_,
            ⟨ownerName, hsourceOwner, hancestor⟩, propertyEntry_resolves_id h hx hb⟩
          exact (propertyEntry_data hb).2.2.2.symm.trans hid

theorem ModelAllocation.inheritedIdCount (a : ModelAllocation model target)
    (h : ModelWellFormed model) : ∀ c ∈ target.classes,
    (target.properties.filter (fun p => p.isId && match p.owner with
      | .class owner => (target.ancestors c.id).contains owner
      | .association _ => false)).length ≤ 1 := by
  intro c hc
  let selected := target.properties.filter (fun p => p.isId && match p.owner with
    | .class owner => (target.ancestors c.id).contains owner
    | .association _ => false)
  have hn : selected.Nodup := by
    exact List.filter_sublist.nodup (nodup_of_map_nodup PropertyDecl.id a.uniqueIds.2.2.1)
  change selected.length ≤ 1
  cases hs : selected with
  | nil => simp
  | cons first rest =>
      cases hr : rest with
      | nil => simp
      | cons second tail =>
          have hfirst : first ∈ selected := by simp [hs]
          have hsecond : second ∈ selected := by simp [hs, hr]
          have hfilt := List.mem_filter.mp hfirst
          have hsilt := List.mem_filter.mp hsecond
          rcases a.inheritedPropertySource h hc hfilt.1 hfilt.2 with
            ⟨sourceClass, hsc, sourceFirst, hsf, hcAlias, hfirstId, hfirstOwner, hfirstResolve⟩
          rcases a.inheritedPropertySource h hc hsilt.1 hsilt.2 with
            ⟨sourceClass', hsc', sourceSecond, hss, hcAlias', hsecondId, hsecondOwner,
              hsecondResolve⟩
          have hclasses : sourceClass = sourceClass' := by
            apply uniqueBy_eq_of_mem_local Class.alias
            · have hall := h.uniqueQualifiedAliases
              simp only [uniqueAliases, aliases, List.nodup_append] at hall
              exact hall.1.1.1.1.2.1
            · exact hsc
            · exact hsc'
            · exact classAliasAt_unique h hcAlias hcAlias'
          subst sourceClass'
          have halias : sourceFirst.alias = sourceSecond.alias :=
            h.inheritedIdCount sourceClass hsc sourceFirst hsf sourceSecond hss
              hfirstId hsecondId hfirstOwner hsecondOwner
          have htargetIds : first.id = second.id := by
            apply Except.ok.inj
            exact hfirstResolve.symm.trans (halias ▸ hsecondResolve)
          have heq : first = second :=
            uniqueBy_eq_of_mem_local PropertyDecl.id a.uniqueIds.2.2.1 hfilt.1 hsilt.1 htargetIds
          have hne : first ≠ second := by
            rw [hs, List.nodup_cons, hr, List.nodup_cons] at hn
            exact fun heq' => hn.1 (by simp [heq'])
          exact False.elim (hne heq)

/-- Successful executable allocation preserves every declaration-side semantic
constraint of a well-formed source model. -/
theorem schemaWellFormed_of_modelWellFormed_of_bindModel
    (h : ModelWellFormed model) (hb : bindModel model = .ok target) :
    SchemaWellFormed target := by
  have a := modelAllocation_of_bindModel hb
  have hu := a.uniqueIds
  have hproperties := a.propertyFacts h
  have hotherNames := a.otherNames h
  exact {
    uniquePackageIds := hu.1
    uniqueClassIds := hu.2.1
    uniquePropertyIds := hu.2.2.1
    uniqueAssociationIds := hu.2.2.2.1
    uniqueEnumerationIds := hu.2.2.2.2.1
    uniqueLiteralIds := hu.2.2.2.2.2
    names := ⟨a.packageNames h, a.classNames h, hproperties.1,
      hotherNames.1, hotherNames.2.1, hotherNames.2.2⟩
    packageParentsResolved := a.packageParentsResolved
    packageAcyclic := a.packageAcyclic h
    classPackagesResolved := a.classPackagesResolved
    enumPackagesResolved := a.enumPackagesResolved
    associationPackagesResolved := a.associationPackagesResolved
    supersResolved := a.supersResolved
    inheritanceAcyclic := a.inheritanceAcyclic h
    multiplicities := hproperties.2
    propertyOwnersResolved := a.propertyOwnersResolved h
    propertyTypesResolved := a.propertyTypesResolved
    compositeReferences := a.compositeReferences h
    literalsResolved := a.literalsResolved
    associationEnds := a.associationEnds h
    endMembershipUnique := a.endMembershipUnique h
    containerUpperOne := a.containerUpperOne h
    inheritedIdCount := a.inheritedIdCount h
  }

end VLMOF.Source
