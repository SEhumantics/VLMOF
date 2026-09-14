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

end VLMOF.Source
