import VLMOF.SchemaElaborationCorrect

/-!
# Reflection of schema well-formedness to source models

The reverse direction explicitly assumes XML lexical admissibility of raw source
aliases.  Successful binding itself supplies the weaker executable alias check,
global uniqueness, qualification, and all resolver successes.
-/
namespace VLMOF.Source

variable {α : Type}
variable {model : Model} {target : Schema}

private theorem except_bind_ok_reflect {ε α β : Type} {x : Except ε α}
    {f : α → Except ε β} {y : β} (h : x.bind f = .ok y) :
    ∃ value, x = .ok value ∧ f value = .ok y := by
  cases hx : x with
  | error error => simp [hx, Bind.bind, Except.bind] at h
  | ok value => exact ⟨value, rfl, by simpa [hx, Bind.bind, Except.bind] using h⟩

private theorem bindModel_checkAliases (hb : bindModel model = .ok target) :
    checkAliases "declaration" (aliases model) = .ok () := by
  change (checkAliases "declaration" (aliases model)).bind (fun _ =>
    (model.packages.zipIdx.mapM (bindPackageEntry model)).bind (fun packages =>
    (model.classes.zipIdx.mapM (bindClassEntry model)).bind (fun classes =>
    (model.properties.zipIdx.mapM (bindPropertyEntry model)).bind (fun properties =>
    (model.associations.zipIdx.mapM (bindAssociationEntry model)).bind (fun associations =>
    (model.enumerations.zipIdx.mapM (bindEnumerationEntry model)).bind (fun enumerations =>
    (model.literals.zipIdx.mapM (bindLiteralEntry model)).bind (fun literals =>
      .ok (Schema.mk packages classes properties associations enumerations literals)))))))) =
      .ok target at hb
  rcases except_bind_ok_reflect hb with ⟨value, hc, _⟩
  cases value
  simpa using hc

/-- Successful binding enforces global alias uniqueness independently of any
source semantic assumption. -/
theorem aliasNodup_of_bindModel (hb : bindModel model = .ok target) :
    (aliases model).Nodup := by
  have hc := bindModel_checkAliases hb
  rw [checkAliases_iff, aliasEnvironment_iff] at hc
  exact hc.1

private theorem packageBinding_components {x : Package × Nat} {d : PackageDecl}
    (hb : bindPackageEntry model x = .ok d) :
    checkQualification x.1.alias x.1.parent = .ok () ∧
      optionalPackage model x.1.parent = .ok d.parent ∧ d.name = some x.1.name := by
  unfold bindPackageEntry at hb
  cases hq : checkQualification x.1.alias x.1.parent <;>
    cases hp : optionalPackage model x.1.parent <;>
    simp [hq, hp, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  exact ⟨by simpa using hq, by simpa using hp, rfl⟩

private theorem classBinding_components {x : Class × Nat} {d : ClassDecl}
    (hb : bindClassEntry model x = .ok d) :
    checkQualification x.1.alias x.1.package = .ok () ∧
      optionalPackage model x.1.package = .ok d.package ∧
      x.1.directSupers.mapM (classId model) = .ok d.directSupers ∧
      d.name = some x.1.name := by
  unfold bindClassEntry at hb
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    cases hs : x.1.directSupers.mapM (classId model) <;>
    simp [hq, hp, hs, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  exact ⟨by simpa using hq, by simpa using hp, by simpa using hs, rfl⟩

private theorem propertyBinding_components {x : Property × Nat} {d : PropertyDecl}
    (hb : bindPropertyEntry model x = .ok d) :
    checkQualification x.1.alias (some (ownerName x.1.owner)) = .ok () ∧
      bindOwner model x.1.owner = .ok d.owner ∧ bindType model x.1.type = .ok d.type ∧
      d.name = some x.1.name := by
  unfold bindPropertyEntry at hb
  cases hq : checkQualification x.1.alias (some (ownerName x.1.owner)) <;>
    cases ho : bindOwner model x.1.owner <;>
    cases ht : bindType model x.1.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  exact ⟨by simpa using hq, by simpa using ho, by simpa using ht, rfl⟩

private theorem propertyBinding_data {x : Property × Nat} {d : PropertyDecl}
    (hb : bindPropertyEntry model x = .ok d) :
    d.multiplicity = x.1.multiplicity ∧ d.aggregation = x.1.aggregation ∧
      d.isId = x.1.isId := by
  unfold bindPropertyEntry at hb
  cases hq : checkQualification x.1.alias (some (ownerName x.1.owner)) <;>
    cases ho : bindOwner model x.1.owner <;>
    cases ht : bindType model x.1.type <;>
    simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  exact ⟨rfl, rfl, rfl⟩

private theorem enumerationBinding_components {x : Enumeration × Nat} {d : EnumerationDecl}
    (hb : bindEnumerationEntry model x = .ok d) :
    checkQualification x.1.alias x.1.package = .ok () ∧
      optionalPackage model x.1.package = .ok d.package ∧ d.name = some x.1.name := by
  unfold bindEnumerationEntry at hb
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    simp [hq, hp, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  exact ⟨by simpa using hq, by simpa using hp, rfl⟩

private theorem literalBinding_components {x : Literal × Nat} {d : LiteralDecl}
    (hb : bindLiteralEntry model x = .ok d) :
    checkQualification x.1.alias (some x.1.enumeration) = .ok () ∧
      enumerationId model x.1.enumeration = .ok d.enumeration ∧ d.name = some x.1.name := by
  unfold bindLiteralEntry at hb
  cases hq : checkQualification x.1.alias (some x.1.enumeration) <;>
    cases he : enumerationId model x.1.enumeration <;>
    simp [hq, he, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  exact ⟨by simpa using hq, by simpa using he, rfl⟩

private theorem associationBinding_name {x : Association × Nat} {d : AssociationDecl}
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

private theorem associationBinding_data {x : Association × Nat} {d : AssociationDecl}
    (h : bindAssociationEntry model x = .ok d) :
    ∃ first second firstId secondId,
      x.1.ends = [first, second] ∧ propertyId model first = .ok firstId ∧
      propertyId model second = .ok secondId ∧ d.ends = (firstId, secondId) ∧
      d.id = ⟨x.2⟩ := by
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
          all_goals exact ⟨first, second, _, _, rfl, hf, hs, rfl, rfl⟩

private theorem uniqueBy_eq_local {κ δ : Type} [DecidableEq κ] (key : δ → κ)
    {xs : List δ} (h : uniqueBy key xs) {left right : δ}
    (hl : left ∈ xs) (hr : right ∈ xs) (heq : key left = key right) : left = right := by
  unfold uniqueBy at h
  induction xs with
  | nil => simp at hl
  | cons x xs ih =>
      simp only [List.map_cons, List.nodup_cons] at h
      rcases h with ⟨hnot, hnodup⟩
      simp only [List.mem_cons] at hl hr
      rcases hl with rfl | hl
      · rcases hr with rfl | hr
        · rfl
        · exact False.elim (hnot (heq ▸ List.mem_map.mpr ⟨right, hr, rfl⟩))
      · rcases hr with rfl | hr
        · exact False.elim (hnot (heq.symm ▸ List.mem_map.mpr ⟨left, hl, rfl⟩))
        · exact ih hnodup hl hr

private theorem resolves_of_resolveIndex {entries : List α} {key : α → Name}
    {kind : String} {name : Name} {index : Nat}
    (hr : resolveIndex kind (entries.map key) name = .ok index) :
    lookupAll key entries name ≠ [] := by
  have hg := resolveIndex_getElem hr
  rw [List.getElem?_map] at hg
  cases he : entries[index]? with
  | none => simp [he] at hg
  | some entry =>
      simp [he] at hg
      subst name
      intro hempty
      have hm : entry ∈ lookupAll key entries (key entry) :=
        (mem_lookupAll key entries (key entry) entry).mpr
          ⟨List.mem_iff_getElem?.mpr ⟨index, he⟩, rfl⟩
      simpa [hempty] using hm

private theorem packageResolved_of_id {name : Name} {id : PackageId}
    (h : packageId model name = .ok id) : resolvesPackage model name := by
  unfold packageId at h
  cases hr : resolveIndex "package" (model.packages.map Package.alias) name <;>
    simp [hr, Except.map] at h
  exact resolves_of_resolveIndex hr

private theorem classResolved_of_id {name : Name} {id : ClassId}
    (h : classId model name = .ok id) : resolvesClass model name := by
  unfold classId at h
  cases hr : resolveIndex "class" (model.classes.map Class.alias) name <;>
    simp [hr, Except.map] at h
  exact resolves_of_resolveIndex hr

private theorem enumerationResolved_of_id {name : Name} {id : EnumerationId}
    (h : enumerationId model name = .ok id) : resolvesEnumeration model name := by
  unfold enumerationId at h
  cases hr : resolveIndex "enumeration" (model.enumerations.map Enumeration.alias) name <;>
    simp [hr, Except.map] at h
  exact resolves_of_resolveIndex hr

private theorem source_zip_mem {xs : List α} {x : α} (hx : x ∈ xs) :
    ∃ index, (x, index) ∈ xs.zipIdx := by
  obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp hx
  exact ⟨index, List.mk_mem_zipIdx_iff_getElem?.mpr hi⟩

private theorem optionalPackage_resolved {owner : Option Name} {translated : Option PackageId}
    (h : optionalPackage model owner = .ok translated) :
    match owner with | none => True | some name => resolvesPackage model name := by
  cases owner with
  | none => trivial
  | some name =>
      unfold optionalPackage at h
      cases hp : packageId model name <;> simp [hp, Functor.map, Except.map] at h
      exact packageResolved_of_id hp

private theorem qualifiedOptional {alias : Name} {owner : Option Name}
    (hq : checkQualification alias owner = .ok ()) :
    match owner with
    | none => rootQualified alias
    | some name => qualifiedBy name alias := by
  rw [checkQualification_iff] at hq
  cases owner <;> simpa [rootQualified, qualifiedBy] using hq

theorem ModelAllocation.reflectedPackageFields (a : ModelAllocation model target) :
    (∀ p ∈ model.packages, match p.parent with
      | none => rootQualified p.alias
      | some parent => resolvesPackage model parent ∧ qualifiedBy parent p.alias) ∧
    (∀ c ∈ model.classes, match c.package with
      | none => rootQualified c.alias
      | some package => resolvesPackage model package ∧ qualifiedBy package c.alias) ∧
    (∀ e ∈ model.enumerations, match e.package with
      | none => rootQualified e.alias
      | some package => resolvesPackage model package ∧ qualifiedBy package e.alias) := by
  constructor
  · intro p hp
    rcases source_zip_mem hp with ⟨index, hz⟩
    rcases mapM_ok_source a.packages hz with ⟨d, _, hb⟩
    have hc := packageBinding_components hb
    simp only [Prod.fst] at hc
    cases hparent : p.parent with
    | none =>
        simp only [hparent] at hc
        exact qualifiedOptional hc.1
    | some parent =>
        simp only [hparent] at hc
        exact ⟨optionalPackage_resolved hc.2.1, qualifiedOptional hc.1⟩
  · constructor
    · intro c hc
      rcases source_zip_mem hc with ⟨index, hz⟩
      rcases mapM_ok_source a.classes hz with ⟨d, _, hb⟩
      have hf := classBinding_components hb
      simp only [Prod.fst] at hf
      cases hpackage : c.package with
      | none =>
          simp only [hpackage] at hf
          exact qualifiedOptional hf.1
      | some package =>
          simp only [hpackage] at hf
          exact ⟨optionalPackage_resolved hf.2.1, qualifiedOptional hf.1⟩
    · intro e he
      rcases source_zip_mem he with ⟨index, hz⟩
      rcases mapM_ok_source a.enumerations hz with ⟨d, _, hb⟩
      have hf := enumerationBinding_components hb
      simp only [Prod.fst] at hf
      cases hpackage : e.package with
      | none =>
          simp only [hpackage] at hf
          exact qualifiedOptional hf.1
      | some package =>
          simp only [hpackage] at hf
          exact ⟨optionalPackage_resolved hf.2.1, qualifiedOptional hf.1⟩

theorem ModelAllocation.reflectedAssociationPackages (a : ModelAllocation model target) :
    ∀ association ∈ model.associations, match association.package with
      | none => rootQualified association.alias
      | some package => resolvesPackage model package ∧ qualifiedBy package association.alias := by
  intro association ha
  rcases source_zip_mem ha with ⟨index, hz⟩
  rcases mapM_ok_source a.associations hz with ⟨d, _, hb⟩
  unfold bindAssociationEntry at hb
  rcases except_bind_ok_reflect hb with ⟨unit, hq, hrest⟩
  cases unit
  rcases except_bind_ok_reflect hrest with ⟨parent, hp, _⟩
  cases hpackage : association.package with
  | none =>
      simp only [hpackage] at hq hp
      exact qualifiedOptional hq
  | some package =>
      simp only [hpackage] at hq hp
      exact ⟨optionalPackage_resolved hp, qualifiedOptional hq⟩

theorem ModelAllocation.reflectedResolutionFields (a : ModelAllocation model target) :
    (∀ c ∈ model.classes, ∀ super ∈ c.directSupers, resolvesClass model super) ∧
    (∀ p ∈ model.properties, match p.owner with
      | .class c => resolvesClass model c ∧ qualifiedBy c p.alias
      | .association association => resolvesAssociation model association ∧
          qualifiedBy association p.alias) ∧
    (∀ p ∈ model.properties, match p.type with
      | .reference c => resolvesClass model c
      | .enumeration e => resolvesEnumeration model e
      | _ => True) ∧
    (∀ l ∈ model.literals, resolvesEnumeration model l.enumeration ∧
      qualifiedBy l.enumeration l.alias) := by
  constructor
  · intro c hc super hs
    rcases source_zip_mem hc with ⟨index, hz⟩
    rcases mapM_ok_source a.classes hz with ⟨d, _, hb⟩
    have hf := classBinding_components hb
    rcases mapM_ok_source hf.2.2.1 hs with ⟨id, _, hid⟩
    exact classResolved_of_id hid
  · constructor
    · intro p hp
      rcases source_zip_mem hp with ⟨index, hz⟩
      rcases mapM_ok_source a.properties hz with ⟨d, _, hb⟩
      have hf := propertyBinding_components hb
      have hqual : qualifiedBy (ownerName p.owner) p.alias := by
        simpa [qualifiedBy] using qualifiedOptional hf.1
      cases ho : p.owner with
      | «class» name =>
          cases hr : classId model name <;>
            simp [ho, bindOwner, hr, Functor.map, Except.map] at hf
          exact ⟨classResolved_of_id hr, by simpa [ho, ownerName] using hqual⟩
      | association name =>
          cases hr : associationId model name <;>
            simp [ho, bindOwner, hr, Functor.map, Except.map] at hf
          have hresolved : resolvesAssociation model name := by
            unfold associationId at hr
            cases hi : resolveIndex "association" (model.associations.map Association.alias) name <;>
              simp [hi, Except.map] at hr
            exact resolves_of_resolveIndex hi
          exact ⟨hresolved, by simpa [ho, ownerName] using hqual⟩
    · constructor
      · intro p hp
        rcases source_zip_mem hp with ⟨index, hz⟩
        rcases mapM_ok_source a.properties hz with ⟨d, _, hb⟩
        have hf := propertyBinding_components hb
        cases ht : p.type with
        | boolean => trivial
        | integer => trivial
        | string => trivial
        | reference name =>
            cases hr : classId model name <;>
              simp [ht, bindType, hr, Functor.map, Except.map] at hf
            exact classResolved_of_id hr
        | enumeration name =>
            cases hr : enumerationId model name <;>
              simp [ht, bindType, hr, Functor.map, Except.map] at hf
            exact enumerationResolved_of_id hr
      · intro l hl
        rcases source_zip_mem hl with ⟨index, hz⟩
        rcases mapM_ok_source a.literals hz with ⟨d, _, hb⟩
        have hf := literalBinding_components hb
        exact ⟨enumerationResolved_of_id hf.2.1,
          by simpa [qualifiedBy] using qualifiedOptional hf.1⟩

theorem ModelAllocation.reflectedDisplayNames (a : ModelAllocation model target)
    (wf : SchemaWellFormed target) :
    (∀ x ∈ model.packages, validDisplayName x.name) ∧
    (∀ x ∈ model.classes, validDisplayName x.name) ∧
    (∀ x ∈ model.properties, validDisplayName x.name) ∧
    (∀ x ∈ model.associations, validDisplayName x.name) ∧
    (∀ x ∈ model.enumerations, validDisplayName x.name) ∧
    (∀ x ∈ model.literals, validDisplayName x.name) := by
  constructor
  · intro x hx
    rcases source_zip_mem hx with ⟨index, hz⟩
    rcases mapM_ok_source a.packages hz with ⟨d, hd, hb⟩
    have hn := wf.names.1 d hd
    rw [packageBinding_components hb |>.2.2] at hn
    simpa [validName, validDisplayName] using hn
  · constructor
    · intro x hx
      rcases source_zip_mem hx with ⟨index, hz⟩
      rcases mapM_ok_source a.classes hz with ⟨d, hd, hb⟩
      have hn := wf.names.2.1 d hd
      rw [classBinding_components hb |>.2.2.2] at hn
      simpa [validName, validDisplayName] using hn
    · constructor
      · intro x hx
        rcases source_zip_mem hx with ⟨index, hz⟩
        rcases mapM_ok_source a.properties hz with ⟨d, hd, hb⟩
        have hn := wf.names.2.2.1 d hd
        rw [propertyBinding_components hb |>.2.2.2] at hn
        simpa [validName, validDisplayName] using hn
      · constructor
        · intro x hx
          rcases source_zip_mem hx with ⟨index, hz⟩
          rcases mapM_ok_source a.associations hz with ⟨d, hd, hb⟩
          have hn := wf.names.2.2.2.1 d hd
          rw [associationBinding_name hb] at hn
          simpa [validName, validDisplayName] using hn
        · constructor
          · intro x hx
            rcases source_zip_mem hx with ⟨index, hz⟩
            rcases mapM_ok_source a.enumerations hz with ⟨d, hd, hb⟩
            have hn := wf.names.2.2.2.2.1 d hd
            rw [enumerationBinding_components hb |>.2.2] at hn
            simpa [validName, validDisplayName] using hn
          · intro x hx
            rcases source_zip_mem hx with ⟨index, hz⟩
            rcases mapM_ok_source a.literals hz with ⟨d, hd, hb⟩
            have hn := wf.names.2.2.2.2.2 d hd
            rw [literalBinding_components hb |>.2.2] at hn
            simpa [validName, validDisplayName] using hn

theorem ModelAllocation.reflectedPropertyFacts (a : ModelAllocation model target)
    (wf : SchemaWellFormed target) :
    (∀ p ∈ model.properties, multiplicityValid p.multiplicity) ∧
    (∀ p ∈ model.properties, p.aggregation = .composite →
      ∃ c, p.type = .reference c) := by
  constructor
  · intro p hp
    rcases source_zip_mem hp with ⟨index, hz⟩
    rcases mapM_ok_source a.properties hz with ⟨d, hd, hb⟩
    rw [← (propertyBinding_data hb).1]
    exact wf.multiplicities d hd
  · intro p hp hcomposite
    rcases source_zip_mem hp with ⟨index, hz⟩
    rcases mapM_ok_source a.properties hz with ⟨d, hd, hb⟩
    have hdcomposite : d.aggregation = .composite := by
      rw [(propertyBinding_data hb).2.1]
      exact hcomposite
    rcases wf.compositeReferences d hd hdcomposite with ⟨id, htype⟩
    have hbind := propertyBinding_components hb |>.2.2.1
    cases ht : p.type with
    | boolean => simp [ht, bindType, pure, Except.pure] at hbind; cases hbind.trans htype
    | integer => simp [ht, bindType, pure, Except.pure] at hbind; cases hbind.trans htype
    | string => simp [ht, bindType, pure, Except.pure] at hbind; cases hbind.trans htype
    | reference name => exact ⟨name, rfl⟩
    | enumeration name =>
        cases he : enumerationId model name <;>
          simp [ht, bindType, he, Functor.map, Except.map] at hbind
        cases hbind.trans htype

private theorem classBinding_id {x : Class × Nat} {d : ClassDecl}
    (hb : bindClassEntry model x = .ok d) : d.id = ⟨x.2⟩ := by
  unfold bindClassEntry at hb
  cases hq : checkQualification x.1.alias x.1.package <;>
    cases hp : optionalPackage model x.1.package <;>
    cases hs : x.1.directSupers.mapM (classId model) <;>
    simp [hq, hp, hs, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  rfl

private theorem packageBinding_id {x : Package × Nat} {d : PackageDecl}
    (hb : bindPackageEntry model x = .ok d) : d.id = ⟨x.2⟩ := by
  unfold bindPackageEntry at hb
  cases hq : checkQualification x.1.alias x.1.parent <;>
    cases hp : optionalPackage model x.1.parent <;>
    simp [hq, hp, Bind.bind, Except.bind, pure, Except.pure] at hb
  subst d
  rfl

private theorem classId_of_allocated (hn : uniqueAliases model)
    {c : Class} {index : Nat} {d : ClassDecl}
    (hz : (c, index) ∈ model.classes.zipIdx)
    (hb : bindClassEntry model (c, index) = .ok d) : classId model c.alias = .ok d.id := by
  have hall := hn
  simp only [uniqueAliases, aliases, List.nodup_append] at hall
  have hclasses : (model.classes.map Class.alias).Nodup := hall.1.1.1.1.2.1
  have hg := List.mk_mem_zipIdx_iff_getElem?.mp hz
  have hi : (model.classes.map Class.alias)[index]? = some c.alias := by
    simp [List.getElem?_map, hg]
  have hr : resolveIndex "class" (model.classes.map Class.alias) c.alias = .ok index := by
    rw [resolveIndex_iff_uniqueAliasAt]
    exact uniqueAliasAt_of_nodup hclasses hi
  unfold classId
  rw [hr, classBinding_id hb]
  rfl

private theorem packageId_of_allocated (hn : uniqueAliases model)
    {p : Package} {index : Nat} {d : PackageDecl}
    (hz : (p, index) ∈ model.packages.zipIdx)
    (hb : bindPackageEntry model (p, index) = .ok d) : packageId model p.alias = .ok d.id := by
  have hall := hn
  simp only [uniqueAliases, aliases, List.nodup_append] at hall
  have hpackages : (model.packages.map Package.alias).Nodup := hall.1.1.1.1.1
  have hg := List.mk_mem_zipIdx_iff_getElem?.mp hz
  have hi : (model.packages.map Package.alias)[index]? = some p.alias := by
    simp [List.getElem?_map, hg]
  have hr : resolveIndex "package" (model.packages.map Package.alias) p.alias = .ok index := by
    rw [resolveIndex_iff_uniqueAliasAt]
    exact uniqueAliasAt_of_nodup hpackages hi
  unfold packageId
  rw [hr, packageBinding_id hb]
  rfl

private theorem associationId_of_allocated (hn : uniqueAliases model)
    {source : Association} {index : Nat} {d : AssociationDecl}
    (hz : (source, index) ∈ model.associations.zipIdx)
    (hb : bindAssociationEntry model (source, index) = .ok d) :
    associationId model source.alias = .ok d.id := by
  have hall := hn
  simp only [uniqueAliases, aliases, List.nodup_append] at hall
  have hnames : (model.associations.map Association.alias).Nodup := hall.1.1.2.1
  have hg := List.mk_mem_zipIdx_iff_getElem?.mp hz
  have hi : (model.associations.map Association.alias)[index]? = some source.alias := by
    simp [List.getElem?_map, hg]
  have hr : resolveIndex "association" (model.associations.map Association.alias)
      source.alias = .ok index := by
    rw [resolveIndex_iff_uniqueAliasAt]
    exact uniqueAliasAt_of_nodup hnames hi
  unfold associationId
  rcases associationBinding_data hb with ⟨_, _, _, _, _, _, _, _, hid⟩
  rw [hr, hid]
  rfl

private theorem propertyId_of_allocated (hn : uniqueAliases model)
    {source : Property} {index : Nat} {d : PropertyDecl}
    (hz : (source, index) ∈ model.properties.zipIdx)
    (hb : bindPropertyEntry model (source, index) = .ok d) :
    propertyId model source.alias = .ok d.id := by
  have hall := hn
  simp only [uniqueAliases, aliases, List.nodup_append] at hall
  have hnames : (model.properties.map Property.alias).Nodup := hall.1.1.1.2.1
  have hg := List.mk_mem_zipIdx_iff_getElem?.mp hz
  have hi : (model.properties.map Property.alias)[index]? = some source.alias := by
    simp [List.getElem?_map, hg]
  have hr : resolveIndex "property" (model.properties.map Property.alias)
      source.alias = .ok index := by
    rw [resolveIndex_iff_uniqueAliasAt]
    exact uniqueAliasAt_of_nodup hnames hi
  unfold propertyId
  rw [hr]
  have hid : d.id = ⟨index⟩ := by
    unfold bindPropertyEntry at hb
    cases hq : checkQualification source.alias (some (ownerName source.owner)) <;>
      cases ho : bindOwner model source.owner <;> cases ht : bindType model source.type <;>
      simp [hq, ho, ht, Bind.bind, Except.bind, pure, Except.pure] at hb
    subst d
    rfl
  rw [hid]
  rfl

private theorem sourceReference_of_target {p : Property} {d : PropertyDecl} {index : Nat}
    (hb : bindPropertyEntry model (p, index) = .ok d)
    (ht : ∃ id, d.type = .reference id) : ∃ name, p.type = .reference name := by
  rcases ht with ⟨id, ht⟩
  have hbind := propertyBinding_components hb |>.2.2.1
  cases hp : p.type with
  | boolean => simp [hp, bindType, pure, Except.pure] at hbind; cases hbind.trans ht
  | integer => simp [hp, bindType, pure, Except.pure] at hbind; cases hbind.trans ht
  | string => simp [hp, bindType, pure, Except.pure] at hbind; cases hbind.trans ht
  | reference name => exact ⟨name, rfl⟩
  | enumeration name =>
      cases he : enumerationId model name <;>
        simp [hp, bindType, he, Functor.map, Except.map] at hbind
      cases hbind.trans ht

private theorem ownerMatches_reflect {source : Association} {a : AssociationDecl}
    {p : Property} {d : PropertyDecl} {index : Nat}
    (ha : associationId model source.alias = .ok a.id)
    (hb : bindPropertyEntry model (p, index) = .ok d)
    (hm : ownerMatchesEnd a d) : ownerMatches source p := by
  have ho := propertyBinding_components hb |>.2.1
  cases hp : p.owner with
  | «class» name => simp [ownerMatches, hp]
  | association name =>
      cases hr : associationId model name with
      | error error => simp [hp, bindOwner, hr, Functor.map, Except.map] at ho
      | ok id =>
          have hd : d.owner = .association id := by
            simpa [hp, bindOwner, hr, Functor.map, Except.map] using ho.symm
          have hid : id = a.id := by simpa [ownerMatchesEnd, hd] using hm
          have : name = source.alias := by
            unfold associationId at hr ha
            cases hri : resolveIndex "association" (model.associations.map Association.alias) name with
            | error e => simp [hri, Except.map] at hr
            | ok ni =>
              cases hai : resolveIndex "association" (model.associations.map Association.alias)
                  source.alias with
              | error e => simp [hai, Except.map] at ha
              | ok ai =>
                simp [hri, Except.map] at hr
                simp [hai, Except.map] at ha
                have hieq : ni = ai := AssociationId.mk.inj (hr.trans (hid ▸ ha).symm)
                subst ai
                exact resolveIndex_injective hri hai
          simpa [ownerMatches, hp] using this

private theorem classId_injective_ok {first second : Name} {id : ClassId}
    (hf : classId model first = .ok id) (hs : classId model second = .ok id) :
    first = second := by
  unfold classId at hf hs
  cases hfr : resolveIndex "class" (model.classes.map Class.alias) first with
  | error e => simp [hfr, Except.map] at hf
  | ok fi =>
      cases hsr : resolveIndex "class" (model.classes.map Class.alias) second with
      | error e => simp [hsr, Except.map] at hs
      | ok si =>
          simp [hfr, Except.map] at hf
          simp [hsr, Except.map] at hs
          have hi : fi = si := ClassId.mk.inj (hf.trans hs.symm)
          subst si
          exact resolveIndex_injective hfr hsr

private theorem classOwnerSource_reflect {p q : Property} {dp dq : PropertyDecl}
    {pi qi : Nat}
    (hp : bindPropertyEntry model (p, pi) = .ok dp)
    (hq : bindPropertyEntry model (q, qi) = .ok dq)
    (hm : classOwnerIsSource dp dq) : classOwnerMatchesSource p q := by
  have hop := propertyBinding_components hp |>.2.1
  have htq := propertyBinding_components hq |>.2.2.1
  cases hpo : p.owner with
  | association name =>
      have href : ∃ id, dq.type = .reference id := by
        cases hr : associationId model name <;>
          simp [hpo, bindOwner, hr, Functor.map, Except.map] at hop
        unfold classOwnerIsSource at hm
        rw [← hop] at hm
        cases hdq : dq.type <;> simp [hdq] at hm
        case reference id => exact ⟨id, rfl⟩
      rcases sourceReference_of_target hq href with ⟨source, hs⟩
      simp [classOwnerMatchesSource, hpo, hs]
  | «class» owner =>
      cases hr : classId model owner <;>
        simp [hpo, bindOwner, hr, Functor.map, Except.map] at hop
      cases hqt : q.type with
      | boolean =>
          simp [hqt, bindType, pure, Except.pure] at htq
          unfold classOwnerIsSource at hm
          rw [← hop, ← htq] at hm
          simp [classOwnerIsSource] at hm
      | integer =>
          simp [hqt, bindType, pure, Except.pure] at htq
          unfold classOwnerIsSource at hm
          rw [← hop, ← htq] at hm
          simp [classOwnerIsSource] at hm
      | string =>
          simp [hqt, bindType, pure, Except.pure] at htq
          unfold classOwnerIsSource at hm
          rw [← hop, ← htq] at hm
          simp [classOwnerIsSource] at hm
      | enumeration name =>
          cases he : enumerationId model name <;>
            simp [hqt, bindType, he, Functor.map, Except.map] at htq
          unfold classOwnerIsSource at hm
          rw [← hop, ← htq] at hm
          simp [classOwnerIsSource] at hm
      | reference source =>
          cases hs : classId model source <;>
            simp [hqt, bindType, hs, Functor.map, Except.map] at htq
          unfold classOwnerIsSource at hm
          rw [← hop, ← htq] at hm
          simp [classOwnerIsSource] at hm
          simpa [classOwnerMatchesSource, hpo, hqt] using
            classId_injective_ok hr (hm ▸ hs)

private theorem atMostOneOwner_reflect {p q : Property} {dp dq : PropertyDecl}
    {pi qi : Nat}
    (hp : bindPropertyEntry model (p, pi) = .ok dp)
    (hq : bindPropertyEntry model (q, qi) = .ok dq)
    (hm : atMostOneAssociationOwned dp dq) : atMostOneAssociationOwner p q := by
  cases hpo : p.owner with
  | «class» pn => simp [atMostOneAssociationOwner, hpo]
  | association pn =>
      cases hqo : q.owner with
      | «class» qn => simp [atMostOneAssociationOwner, hpo, hqo]
      | association qn =>
        have hpbind := propertyBinding_components hp |>.2.1
        have hqbind := propertyBinding_components hq |>.2.1
        cases hpr : associationId model pn <;>
          simp [hpo, bindOwner, hpr, Functor.map, Except.map] at hpbind
        cases hqr : associationId model qn <;>
          simp [hqo, bindOwner, hqr, Functor.map, Except.map] at hqbind
        unfold atMostOneAssociationOwned at hm
        rw [← hpbind, ← hqbind] at hm
        simp at hm

private theorem classPath_target (a : ModelAllocation model target)
    (hn : uniqueAliases model) {start finish : Name}
    (path : ClassAncestor model start finish) {sid fid : ClassId}
    (hs : classId model start = .ok sid) (hf : classId model finish = .ok fid) :
    ∃ n, SuperPath target sid fid n := by
  induction path generalizing sid fid with
  | refl =>
      have : sid = fid := by simpa [hs] using hf
      subst fid
      exact ⟨0, .refl sid⟩
  | step path edge ih =>
      rcases edge with ⟨c, hc, halias, hsuper⟩
      rcases source_zip_mem hc with ⟨index, hz⟩
      rcases mapM_ok_source a.classes hz with ⟨d, hd, hb⟩
      have hmid0 := classId_of_allocated hn hz hb
      rw [halias] at hmid0
      have hcomponents := classBinding_components hb
      rcases mapM_ok_source hcomponents.2.2.1 hsuper with ⟨next, hnext, hsuperId⟩
      have hnextEq : next = fid := by
        have := hsuperId.symm.trans hf
        exact Except.ok.inj this
      subst next
      rcases ih hs hmid0 with ⟨n, hp⟩
      exact ⟨n + 1, .step hp ⟨d, hd, rfl, hnext⟩⟩

theorem ModelAllocation.reflectedInheritanceAcyclic (a : ModelAllocation model target)
    (hn : uniqueAliases model) (wf : SchemaWellFormed target) :
    ∀ c ∈ model.classes, ∀ super ∈ c.directSupers,
      ¬ ClassAncestor model super c.alias := by
  intro c hc super hsuper hcycle
  rcases source_zip_mem hc with ⟨index, hz⟩
  rcases mapM_ok_source a.classes hz with ⟨d, hd, hb⟩
  have hcid := classId_of_allocated hn hz hb
  have hcomponents := classBinding_components hb
  rcases mapM_ok_source hcomponents.2.2.1 hsuper with ⟨sid, hsid, hsuperId⟩
  rcases classPath_target a hn hcycle hsuperId hcid with ⟨n, path⟩
  have huniverse : sid ∈ classUniverse target :=
    mem_classUniverse_of_classDecls_ne_nil (wf.supersResolved d hd sid hsid)
  apply wf.inheritanceAcyclic d hd sid hsid
  exact List.mem_eraseDups.mpr (path.mem_saturated wf huniverse)

private theorem packagePath_target (a : ModelAllocation model target)
    (hn : uniqueAliases model) {start finish : Name}
    (path : PackageAncestor model start finish) {sid fid : PackageId}
    (hs : packageId model start = .ok sid) (hf : packageId model finish = .ok fid) :
    StoredPath (PackageParentEdge target) sid fid := by
  induction path generalizing sid fid with
  | refl =>
      have : sid = fid := by simpa [hs] using hf
      subst fid
      exact .refl sid
  | step path edge ih =>
      rcases edge with ⟨p, hp, halias, hparent⟩
      rcases source_zip_mem hp with ⟨index, hz⟩
      rcases mapM_ok_source a.packages hz with ⟨d, hd, hb⟩
      have hmid0 := packageId_of_allocated hn hz hb
      rw [halias] at hmid0
      have hoptional := packageBinding_components hb |>.2.1
      rw [hparent] at hoptional
      unfold optionalPackage at hoptional
      simp [Functor.map, Except.map] at hoptional
      rw [hf] at hoptional
      simp [Functor.map, Except.map] at hoptional
      have hparentTarget : d.parent = some fid := hoptional.symm
      exact .step (ih hs hmid0) ⟨d, hd, rfl, hparentTarget⟩

theorem ModelAllocation.reflectedPackageAcyclic (a : ModelAllocation model target)
    (hn : uniqueAliases model) (wf : SchemaWellFormed target) :
    ∀ p ∈ model.packages, ∀ parent, p.parent = some parent →
      ¬ PackageAncestor model parent p.alias := by
  intro p hp parent hparent hcycle
  rcases source_zip_mem hp with ⟨index, hz⟩
  rcases mapM_ok_source a.packages hz with ⟨d, hd, hb⟩
  have hpid := packageId_of_allocated hn hz hb
  have hoptional := packageBinding_components hb |>.2.1
  rw [hparent] at hoptional
  unfold optionalPackage at hoptional
  cases hr : packageId model parent with
  | error error => simp [hr, Functor.map, Except.map] at hoptional
  | ok parentId =>
      simp [hr, Functor.map, Except.map] at hoptional
      have hdparent : d.parent = some parentId := hoptional.symm
      have path := packagePath_target a hn hcycle hr hpid
      have hstart : parentId ∈ packageUniverse target := by
        apply List.mem_map.mpr
        rcases a.packageForId hr with ⟨_, translated, _, _, ht, hid, _⟩
        exact ⟨translated, ht, hid⟩
      apply wf.packageAcyclic d hd parentId hdparent
      apply List.mem_eraseDups.mpr
      exact (packageClosure_iff target wf hstart).mpr path

theorem ModelAllocation.reflectedAssociationEnds (a : ModelAllocation model target)
    (hn : uniqueAliases model) (wf : SchemaWellFormed target) :
    ∀ source ∈ model.associations, ∃ p q,
      source.ends = [p.alias, q.alias] ∧ p ∈ model.properties ∧ q ∈ model.properties ∧
      p.alias ≠ q.alias ∧ (∃ c, p.type = .reference c) ∧
      (∃ c, q.type = .reference c) ∧ ownerMatches source p ∧ ownerMatches source q ∧
      classOwnerMatchesSource p q ∧ classOwnerMatchesSource q p ∧
      atMostOneAssociationOwner p q ∧
      ¬ (p.aggregation = .composite ∧ q.aggregation = .composite) := by
  intro source hs
  rcases source_zip_mem hs with ⟨index, hz⟩
  rcases mapM_ok_source a.associations hz with ⟨da, hda, hba⟩
  have haid := associationId_of_allocated hn hz hba
  rcases associationBinding_data hba with
    ⟨first, second, firstId, secondId, hends, hfirst, hsecond, hdaEnds, _⟩
  rcases a.propertyForId hfirst with ⟨p, dp, hp, hpAlias, hdp, hdpId, hbp⟩
  rcases a.propertyForId hsecond with ⟨q, dq, hq, hqAlias, hdq, hdqId, hbq⟩
  rcases wf.associationEnds da hda with
    ⟨tp, tq, htEnds, htp, htq, htne, htpRef, htqRef, hownerp, hownerq,
      hsourcep, hsourceq, hatMost, hnotBoth⟩
  have hpair : (tp.id, tq.id) = (dp.id, dq.id) := by
    rw [← htEnds, hdaEnds, hdpId, hdqId]
  have hpEq : tp = dp := uniqueBy_eq_local PropertyDecl.id wf.uniquePropertyIds htp hdp
    (congrArg Prod.fst hpair)
  have hqEq : tq = dq := uniqueBy_eq_local PropertyDecl.id wf.uniquePropertyIds htq hdq
    (congrArg Prod.snd hpair)
  subst tp
  subst tq
  refine ⟨p, q, ?_, hp, hq, ?_, sourceReference_of_target hbp htpRef,
    sourceReference_of_target hbq htqRef, ownerMatches_reflect haid hbp hownerp,
    ownerMatches_reflect haid hbq hownerq, classOwnerSource_reflect hbp hbq hsourcep,
    classOwnerSource_reflect hbq hbp hsourceq, atMostOneOwner_reflect hbp hbq hatMost, ?_⟩
  · simpa [hpAlias, hqAlias] using hends
  · intro heq
    have hnames : first = second := hpAlias.symm.trans (heq.trans hqAlias)
    have hid : firstId = secondId := by
      have := hfirst.symm.trans (hnames ▸ hsecond)
      exact Except.ok.inj this
    exact htne (by simpa [hdpId, hdqId] using hid)
  · intro both
    apply hnotBoth
    constructor
    · rw [(propertyBinding_data hbp).2.1]
      exact both.1
    · rw [(propertyBinding_data hbq).2.1]
      exact both.2

theorem ModelAllocation.reflectedContainerUpperOne (a : ModelAllocation model target)
    (hn : uniqueAliases model) (wf : SchemaWellFormed target) :
    ∀ source ∈ model.associations, ∀ p q,
    source.ends = [p.alias, q.alias] → p ∈ model.properties → q ∈ model.properties →
      (p.aggregation = .composite → q.multiplicity.upper = .finite 1) ∧
      (q.aggregation = .composite → p.multiplicity.upper = .finite 1) := by
  intro source hs p q hends hp hq
  rcases source_zip_mem hs with ⟨ai, haz⟩
  rcases mapM_ok_source a.associations haz with ⟨da, hda, hba⟩
  rcases associationBinding_data hba with
    ⟨first, second, firstId, secondId, hbends, hfirst, hsecond, hdaEnds, _⟩
  have hnames : first = p.alias ∧ second = q.alias := by
    have := hbends.symm.trans hends
    simpa using this
  rcases hnames with ⟨rfl, rfl⟩
  rcases source_zip_mem hp with ⟨pi, hpz⟩
  rcases mapM_ok_source a.properties hpz with ⟨dp, hdp, hbp⟩
  rcases source_zip_mem hq with ⟨qi, hqz⟩
  rcases mapM_ok_source a.properties hqz with ⟨dq, hdq, hbq⟩
  have hpId := propertyId_of_allocated hn hpz hbp
  have hqId := propertyId_of_allocated hn hqz hbq
  have hidp : firstId = dp.id := Except.ok.inj (hfirst.symm.trans hpId)
  have hidq : secondId = dq.id := Except.ok.inj (hsecond.symm.trans hqId)
  have htarget := wf.containerUpperOne da hda dp dq (by simpa [hidp, hidq] using hdaEnds) hdp hdq
  constructor
  · intro hc
    have hdc : dp.aggregation = .composite := by
      rw [(propertyBinding_data hbp).2.1]
      exact hc
    have := htarget.1 hdc
    rw [(propertyBinding_data hbq).1] at this
    exact this
  · intro hc
    have hdc : dq.aggregation = .composite := by
      rw [(propertyBinding_data hbq).2.1]
      exact hc
    have := htarget.2 hdc
    rw [(propertyBinding_data hbp).1] at this
    exact this

private def reflectedTargetEndHit (id : PropertyId) (association : AssociationDecl) : Nat :=
  if association.ends.1 = id then 1 else if association.ends.2 = id then 1 else 0

private def reflectedSourceEndHit (alias : Name) (association : Association) : Nat :=
  if alias ∈ association.ends then 1 else 0

private theorem propertyId_names_eq {first second : Name} {firstId secondId : PropertyId}
    (hf : propertyId model first = .ok firstId)
    (hs : propertyId model second = .ok secondId) (hid : firstId = secondId) :
    first = second := by
  unfold propertyId at hf hs
  cases hfr : resolveIndex "property" (model.properties.map Property.alias) first with
  | error e => simp [hfr, Except.map] at hf
  | ok fi =>
      cases hsr : resolveIndex "property" (model.properties.map Property.alias) second with
      | error e => simp [hsr, Except.map] at hs
      | ok si =>
          simp [hfr, Except.map] at hf
          simp [hsr, Except.map] at hs
          have hi : fi = si := PropertyId.mk.inj (hf.trans (hid ▸ hs).symm)
          subst si
          exact resolveIndex_injective hfr hsr

private theorem reflectedEndHit_binding
    {source : Association} {translated : AssociationDecl} {property : Property}
    {propertyTarget : PropertyDecl} {index : Nat}
    (hb : bindAssociationEntry model (source, index) = .ok translated)
    (hp : propertyId model property.alias = .ok propertyTarget.id) :
    reflectedTargetEndHit propertyTarget.id translated =
      reflectedSourceEndHit property.alias source := by
  rcases associationBinding_data hb with
    ⟨first, second, firstId, secondId, hends, hfirst, hsecond, htends, _⟩
  have hf : (firstId = propertyTarget.id) ↔ (first = property.alias) := by
    constructor
    · exact propertyId_names_eq hfirst hp
    · intro hn; subst first; exact Except.ok.inj (hfirst.symm.trans hp)
  have hs : (secondId = propertyTarget.id) ↔ (second = property.alias) := by
    constructor
    · exact propertyId_names_eq hsecond hp
    · intro hn; subst second; exact Except.ok.inj (hsecond.symm.trans hp)
  unfold reflectedTargetEndHit reflectedSourceEndHit
  rw [htends, hends]
  simp only [Prod.fst, Prod.snd, List.mem_cons, List.mem_singleton]
  by_cases hfe : first = property.alias
  · simp [hfe, hf]
  · by_cases hse : second = property.alias
    · simp [hfe, hse, hf, hs]
    · simp [hfe, hse, hf, hs, Ne.symm hfe, Ne.symm hse]

theorem ModelAllocation.reflectedEndMembershipUnique (a : ModelAllocation model target)
    (hn : uniqueAliases model) (wf : SchemaWellFormed target) :
    ∀ p ∈ model.properties,
      (model.associations.flatMap fun association =>
        if p.alias ∈ association.ends then [association.alias] else []).length ≤ 1 := by
  intro p hp
  rcases source_zip_mem hp with ⟨index, hz⟩
  rcases mapM_ok_source a.properties hz with ⟨d, hd, hb⟩
  have hpid := propertyId_of_allocated hn hz hb
  have hmap : target.associations.map (reflectedTargetEndHit d.id) =
      model.associations.zipIdx.map (fun z => reflectedSourceEndHit p.alias z.1) :=
    mapM_ok_map_eq a.associations (fun _ _ hbind => reflectedEndHit_binding hbind hpid)
  have hmap' : target.associations.map (reflectedTargetEndHit d.id) =
      model.associations.map (reflectedSourceEndHit p.alias) := by
    rw [hmap]
    have aux : ∀ (xs : List Association) (i : Nat),
        (xs.zipIdx i).map (fun z => reflectedSourceEndHit p.alias z.1) =
          xs.map (reflectedSourceEndHit p.alias) := by
      intro xs i
      induction xs generalizing i with
      | nil => simp
      | cons first rest ih => simp [List.zipIdx, ih]
    exact aux model.associations 0
  have ht : (target.oppositeCandidates d.id).length =
      (target.associations.map (reflectedTargetEndHit d.id)).sum := by
    unfold Schema.oppositeCandidates
    induction target.associations with
    | nil => simp
    | cons association rest ih =>
        by_cases hf : association.ends.1 = d.id <;>
          by_cases hs : association.ends.2 = d.id <;>
          simp [reflectedTargetEndHit, hf, hs, ih] <;> omega
  have hs : (model.associations.flatMap fun association =>
      if p.alias ∈ association.ends then [association.alias] else []).length =
      (model.associations.map (reflectedSourceEndHit p.alias)).sum := by
    induction model.associations with
    | nil => simp
    | cons association rest ih =>
        by_cases hm : p.alias ∈ association.ends <;>
          simp [reflectedSourceEndHit, hm, ih] <;> omega
  rw [hs, ← hmap', ← ht]
  exact wf.endMembershipUnique d hd

theorem ModelAllocation.reflectedAssociationOwnedEnds (a : ModelAllocation model target)
    (hn : uniqueAliases model) (wf : SchemaWellFormed target) :
    ∀ p ∈ model.properties, match p.owner with
    | .class _ => True
    | .association name => ∃ d ∈ model.associations, d.alias = name ∧ p.alias ∈ d.ends := by
  intro p hp
  cases howner : p.owner with
  | «class» name => trivial
  | association name =>
      rcases source_zip_mem hp with ⟨index, hz⟩
      rcases mapM_ok_source a.properties hz with ⟨dp, hdp, hbp⟩
      have hob := propertyBinding_components hbp |>.2.1
      cases hr : associationId model name with
      | error error => simp [howner, bindOwner, hr, Functor.map, Except.map] at hob
      | ok aid =>
          have hdpOwner : dp.owner = .association aid := by
            simpa [howner, bindOwner, hr, Functor.map, Except.map] using hob.symm
          have hw := wf.propertyOwnersResolved dp hdp
          rw [hdpOwner] at hw
          rcases hw with ⟨ta, hta, htaId, hend⟩
          rcases a.associationForId hr with ⟨source, da, hs, halias, hda, hdaId, hba⟩
          have hdaEq : da = ta := uniqueBy_eq_local AssociationDecl.id
            wf.uniqueAssociationIds hda hta (hdaId.trans htaId.symm)
          subst ta
          rcases associationBinding_data hba with
            ⟨first, second, firstId, secondId, hends, hfirst, hsecond, hdaEnds, _⟩
          have hpId := propertyId_of_allocated hn hz hbp
          rw [hdaEnds] at hend
          have hmem : p.alias = first ∨ p.alias = second := by
            rcases hend with hend | hend
            · left; exact (propertyId_names_eq hpId hfirst hend.symm)
            · right; exact (propertyId_names_eq hpId hsecond hend.symm)
          exact ⟨source, hs, halias, by rw [hends]; simpa [hmem]⟩

private theorem eq_of_mem_length_le_one {α : Type} {xs : List α} {x y : α}
    (hx : x ∈ xs) (hy : y ∈ xs) (hlen : xs.length ≤ 1) : x = y := by
  cases xs with
  | nil => simp at hx
  | cons z rest =>
      cases rest with
      | nil => simp_all
      | cons w tail => simp at hlen

theorem ModelAllocation.reflectedInheritedIdCount (a : ModelAllocation model target)
    (hn : uniqueAliases model) (wf : SchemaWellFormed target) :
    ∀ c ∈ model.classes, ∀ p ∈ model.properties, ∀ q ∈ model.properties,
      p.isId = true → q.isId = true →
      (∃ owner, p.owner = .class owner ∧ ClassAncestor model c.alias owner) →
      (∃ owner, q.owner = .class owner ∧ ClassAncestor model c.alias owner) →
      p.alias = q.alias := by
  intro c hc p hp q hq hpid hqid hpOwner hqOwner
  rcases source_zip_mem hc with ⟨ci, hcz⟩
  rcases mapM_ok_source a.classes hcz with ⟨dc, hdc, hbc⟩
  have hcid := classId_of_allocated hn hcz hbc
  rcases source_zip_mem hp with ⟨pi, hpz⟩
  rcases mapM_ok_source a.properties hpz with ⟨dp, hdp, hbp⟩
  rcases source_zip_mem hq with ⟨qi, hqz⟩
  rcases mapM_ok_source a.properties hqz with ⟨dq, hdq, hbq⟩
  have makeSelected : ∀ {r : Property} {dr : PropertyDecl} {ri : Nat},
      bindPropertyEntry model (r, ri) = .ok dr → r.isId = true →
      (∃ owner, r.owner = .class owner ∧ ClassAncestor model c.alias owner) →
      dr.isId && match dr.owner with
        | .class owner => (target.ancestors dc.id).contains owner
        | .association _ => false := by
    intro r dr ri hbr hrid howner
    rcases howner with ⟨owner, hro, hpath⟩
    have hob := propertyBinding_components hbr |>.2.1
    cases ho : classId model owner with
    | error e => simp [hro, bindOwner, ho, Functor.map, Except.map] at hob
    | ok oid =>
        have hdOwner : dr.owner = .class oid := by
          simpa [hro, bindOwner, ho, Functor.map, Except.map] using hob.symm
        rcases classPath_target a hn hpath hcid ho with ⟨n, path⟩
        have huniverse : dc.id ∈ classUniverse target := by
          exact List.mem_map.mpr ⟨dc, hdc, rfl⟩
        have hmem : oid ∈ target.ancestors dc.id :=
          List.mem_eraseDups.mpr (path.mem_saturated wf huniverse)
        rw [(propertyBinding_data hbr).2.2, hrid, hdOwner]
        exact Bool.and_eq_true_iff.mpr ⟨rfl, List.contains_iff_mem.mpr hmem⟩
  have hsp := makeSelected hbp hpid hpOwner
  have hsq := makeSelected hbq hqid hqOwner
  let selected := target.properties.filter (fun r => r.isId && match r.owner with
    | .class owner => (target.ancestors dc.id).contains owner
    | .association _ => false)
  have hmp : dp ∈ selected := List.mem_filter.mpr ⟨hdp, hsp⟩
  have hmq : dq ∈ selected := List.mem_filter.mpr ⟨hdq, hsq⟩
  have hlen : selected.length ≤ 1 := wf.inheritedIdCount dc hdc
  have heq := eq_of_mem_length_le_one hmp hmq hlen
  exact propertyId_names_eq (propertyId_of_allocated hn hpz hbp)
    (propertyId_of_allocated hn hqz hbq) (congrArg PropertyDecl.id heq)

/-- Schema well-formedness reflects through the actual successful binder. Raw AST
aliases need the explicit XML lexical premise because the executable alias check is
intentionally weaker. -/
theorem modelWellFormed_of_bindModel
    (aliasesValid : ∀ n ∈ aliases model, NameValid n)
    (hb : bindModel model = .ok target) (wf : SchemaWellFormed target) :
    ModelWellFormed model := by
  let a := modelAllocation_of_bindModel hb
  have hn : uniqueAliases model := aliasNodup_of_bindModel hb
  have hpkg := a.reflectedPackageFields
  have hresolve := a.reflectedResolutionFields
  have hproperty := a.reflectedPropertyFacts wf
  exact {
    uniqueQualifiedAliases := hn
    aliasesValid := aliasesValid
    displayNames := a.reflectedDisplayNames wf
    packageParents := hpkg.1
    packageAcyclic := a.reflectedPackageAcyclic hn wf
    classPackages := hpkg.2.1
    enumPackages := hpkg.2.2
    associationPackages := a.reflectedAssociationPackages
    supersResolved := hresolve.1
    inheritanceAcyclic := a.reflectedInheritanceAcyclic hn wf
    multiplicities := hproperty.1
    propertyOwners := hresolve.2.1
    propertyTypes := hresolve.2.2.1
    compositesAreReferences := hproperty.2
    literalsResolved := hresolve.2.2.2
    associationEnds := a.reflectedAssociationEnds hn wf
    associationOwnedEnds := a.reflectedAssociationOwnedEnds hn wf
    endMembershipUnique := a.reflectedEndMembershipUnique hn wf
    containerUpperOne := a.reflectedContainerUpperOne hn wf
    inheritedIdCount := a.reflectedInheritedIdCount hn wf
  }

end VLMOF.Source
