import VLMOF.Source.Binding.Values
import VLMOF.Source.Semantics

/-!
# Completeness of source binding

Every model satisfying the declarative source contract passes the executable
alias binder.  A satisfying document additionally supplies every classifier,
observation key, object reference, and enumeration literal needed by instance
binding, so elaboration cannot report a binding error.
-/
namespace VLMOF.Source

variable {α β ε : Type} {model : Model} {snapshot : Instance} {name : Name}

theorem validAlias_of_nameValid {name : Name} (h : NameValid name) :
    validAlias name = true := by
  rcases h with ⟨hne, hcomponents⟩
  cases name with
  | nil => exact False.elim (hne rfl)
  | cons first rest =>
      simp only [validAlias, List.isEmpty_cons, Bool.not_false, Bool.true_and]
      rw [List.all_eq_true]
      intro component hm
      simpa using (hcomponents component hm).1

theorem exists_resolveIndex_of_mem_of_nodup {kind : String} {names : List Name}
    (hn : names.Nodup) {name : Name} (hm : name ∈ names) :
    ∃ index, resolveIndex kind names name = .ok index := by
  obtain ⟨index, hi⟩ := List.mem_iff_getElem?.mp hm
  exact ⟨index, (resolveIndex_iff_uniqueAliasAt kind names name index).mpr
    (uniqueAliasAt_of_nodup hn hi)⟩

theorem mem_of_lookupAll_ne_nil {key : α → Name} {entries : List α} {name : Name}
    (h : lookupAll key entries name ≠ []) : name ∈ entries.map key := by
  obtain ⟨entry, he⟩ := List.exists_mem_of_ne_nil _ h
  have he' := (mem_lookupAll key entries name entry).mp he
  exact List.mem_map.mpr ⟨entry, he'.1, he'.2⟩

theorem mapM_exists_ok {f : α → Except ε β} {xs : List α}
    (h : ∀ x ∈ xs, ∃ y, f x = .ok y) : ∃ ys, xs.mapM f = .ok ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
      obtain ⟨y, hy⟩ := h x (by simp)
      obtain ⟨ys, hys⟩ := ih (fun z hz => h z (by simp [hz]))
      exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys, Bind.bind, Except.bind,
        pure, Except.pure]⟩

private theorem kind_nodup (h : ModelWellFormed model) :
    (model.packages.map Package.alias).Nodup ∧
    (model.classes.map Class.alias).Nodup ∧
    (model.properties.map Property.alias).Nodup ∧
    (model.associations.map Association.alias).Nodup ∧
    (model.enumerations.map Enumeration.alias).Nodup ∧
    (model.literals.map Literal.alias).Nodup := by
  have hn : (aliases model).Nodup := h.uniqueQualifiedAliases
  simp only [aliases, List.nodup_append] at hn
  exact ⟨hn.1.1.1.1.1, hn.1.1.1.1.2.1, hn.1.1.1.2.1,
    hn.1.1.2.1, hn.1.2.1, hn.2.1⟩

private theorem packageId_exists (h : ModelWellFormed model) (hr : resolvesPackage model name) :
    ∃ id, packageId model name = .ok id := by
  obtain ⟨index, hi⟩ := exists_resolveIndex_of_mem_of_nodup (kind := "package") (kind_nodup h).1
    (mem_of_lookupAll_ne_nil hr)
  exact ⟨⟨index⟩, by simp [packageId, hi, Except.map]⟩

private theorem classId_exists (h : ModelWellFormed model) (hr : resolvesClass model name) :
    ∃ id, classId model name = .ok id := by
  obtain ⟨index, hi⟩ := exists_resolveIndex_of_mem_of_nodup (kind := "class") (kind_nodup h).2.1
    (mem_of_lookupAll_ne_nil hr)
  exact ⟨⟨index⟩, by simp [classId, hi, Except.map]⟩

private theorem propertyId_exists (h : ModelWellFormed model)
    (hm : ∃ p ∈ model.properties, p.alias = name) :
    ∃ id, propertyId model name = .ok id := by
  rcases hm with ⟨p, hp, rfl⟩
  obtain ⟨index, hi⟩ := exists_resolveIndex_of_mem_of_nodup (kind := "property") (kind_nodup h).2.2.1
    (List.mem_map.mpr ⟨p, hp, rfl⟩)
  exact ⟨⟨index⟩, by simp [propertyId, hi, Except.map]⟩

private theorem associationId_exists (h : ModelWellFormed model)
    (hr : resolvesAssociation model name) :
    ∃ id, associationId model name = .ok id := by
  obtain ⟨index, hi⟩ := exists_resolveIndex_of_mem_of_nodup (kind := "association") (kind_nodup h).2.2.2.1
    (mem_of_lookupAll_ne_nil hr)
  exact ⟨⟨index⟩, by simp [associationId, hi, Except.map]⟩

private theorem enumerationId_exists (h : ModelWellFormed model)
    (hr : resolvesEnumeration model name) :
    ∃ id, enumerationId model name = .ok id := by
  obtain ⟨index, hi⟩ := exists_resolveIndex_of_mem_of_nodup (kind := "enumeration") (kind_nodup h).2.2.2.2.1
    (mem_of_lookupAll_ne_nil hr)
  exact ⟨⟨index⟩, by simp [enumerationId, hi, Except.map]⟩

private theorem literalId_exists (h : ModelWellFormed model)
    (hm : ∃ l ∈ model.literals, l.alias = name) :
    ∃ id, literalId model name = .ok id := by
  rcases hm with ⟨l, hl, rfl⟩
  obtain ⟨index, hi⟩ := exists_resolveIndex_of_mem_of_nodup (kind := "literal") (kind_nodup h).2.2.2.2.2
    (List.mem_map.mpr ⟨l, hl, rfl⟩)
  exact ⟨⟨index⟩, by simp [literalId, hi, Except.map]⟩

private theorem optionalPackage_exists (h : ModelWellFormed model) {package : Option Name}
    (hr : match package with | none => True | some name => resolvesPackage model name) :
    ∃ target, optionalPackage model package = .ok target := by
  cases package with
  | none => exact ⟨none, rfl⟩
  | some name =>
      obtain ⟨id, hi⟩ := packageId_exists h hr
      exact ⟨some id, by simp [optionalPackage, hi, Functor.map, Except.map]⟩

private theorem bindOwner_exists (h : ModelWellFormed model) (p : Property)
    (hp : p ∈ model.properties) : ∃ owner, bindOwner model p.owner = .ok owner := by
  cases ho : p.owner with
  | «class» name =>
      have hw := h.propertyOwners p hp
      simp [ho] at hw
      have hr : resolvesClass model name := hw.1
      obtain ⟨id, hi⟩ := classId_exists h hr
      exact ⟨.class id, by simp [bindOwner, hi, Functor.map, Except.map]⟩
  | association name =>
      have hw := h.propertyOwners p hp
      simp [ho] at hw
      have hr : resolvesAssociation model name := hw.1
      obtain ⟨id, hi⟩ := associationId_exists h hr
      exact ⟨.association id, by simp [bindOwner, hi, Functor.map, Except.map]⟩

private theorem bindType_exists (h : ModelWellFormed model) (p : Property)
    (hp : p ∈ model.properties) : ∃ type, bindType model p.type = .ok type := by
  cases ht : p.type with
  | boolean => exact ⟨.boolean, rfl⟩
  | integer => exact ⟨.integer, rfl⟩
  | string => exact ⟨.string, rfl⟩
  | reference name =>
      have hr : resolvesClass model name := by simpa [ht] using h.propertyTypes p hp
      obtain ⟨id, hi⟩ := classId_exists h hr
      exact ⟨.reference id, by simp [bindType, hi, Functor.map, Except.map]⟩
  | enumeration name =>
      have hr : resolvesEnumeration model name := by simpa [ht] using h.propertyTypes p hp
      obtain ⟨id, hi⟩ := enumerationId_exists h hr
      exact ⟨.enumeration id, by simp [bindType, hi, Functor.map, Except.map]⟩

/-- Declarative model well-formedness rules out every diagnostic produced by
`bindModel`: aliases are valid and unique, owners are qualified, and all names
consumed by the binder resolve in their kind-specific environments. -/
theorem bindModel_complete {model : Model} (h : ModelWellFormed model) :
    ∃ schema, bindModel model = .ok schema := by
  have hcheck : checkAliases "declaration" (aliases model) = .ok () := by
    rw [checkAliases_iff, aliasEnvironment_iff]
    exact ⟨h.uniqueQualifiedAliases, fun name hm => validAlias_of_nameValid (h.aliasesValid name hm)⟩
  have hpkg : ∀ x : Package × Nat, x ∈ model.packages.zipIdx → ∃ y : PackageDecl,
      (fun x => do
        checkQualification x.1.alias x.1.parent
        let parent ← optionalPackage model x.1.parent
        pure ({ id := ⟨x.2⟩, name := some x.1.name, parent } : PackageDecl)) x = .ok y := by
    rintro ⟨p, index⟩ hx
    have hp := List.fst_mem_of_mem_zipIdx hx
    have hw := h.packageParents p hp
    have hq : checkQualification p.alias p.parent = .ok () := by
      rw [checkQualification_iff]
      cases he : p.parent with
      | none => simpa [he, rootQualified] using hw
      | some name =>
          have hw' := hw
          simp [he] at hw'
          exact hw'.2
    have hr : match p.parent with | none => True | some name => resolvesPackage model name := by
      cases he : p.parent with
      | none => simp
      | some name =>
          have hw' := hw
          simp [he] at hw'
          exact hw'.1
    obtain ⟨parent, hparent⟩ := optionalPackage_exists h hr
    exact ⟨{ id := ⟨index⟩, name := some p.name, parent }, by
      simp [hq, hparent, Bind.bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨packages, hpackages⟩ := mapM_exists_ok hpkg
  have hcls : ∀ x : Class × Nat, x ∈ model.classes.zipIdx → ∃ y : ClassDecl,
      (fun x => do
        checkQualification x.1.alias x.1.package
        let boundPackage ← optionalPackage model x.1.package
        let directSupers ← x.1.directSupers.mapM (classId model)
        pure (ClassDecl.mk ⟨x.2⟩ (some x.1.name) boundPackage
          x.1.isAbstract directSupers)) x = .ok y := by
    rintro ⟨c, index⟩ hx
    have hc := List.fst_mem_of_mem_zipIdx hx
    have hw := h.classPackages c hc
    have hq : checkQualification c.alias c.package = .ok () := by
      rw [checkQualification_iff]
      cases he : c.package with
      | none => simpa [he, rootQualified] using hw
      | some name =>
          have hw' := hw
          simp [he] at hw'
          exact hw'.2
    have hr : match c.package with | none => True | some name => resolvesPackage model name := by
      cases he : c.package with
      | none => simp
      | some name =>
          have hw' := hw
          simp [he] at hw'
          exact hw'.1
    obtain ⟨boundPackage, hpackage⟩ := optionalPackage_exists h hr
    obtain ⟨supers, hsupers⟩ := mapM_exists_ok (fun super hs =>
      classId_exists h (h.supersResolved c hc super hs))
    exact ⟨ClassDecl.mk ⟨index⟩ (some c.name) boundPackage c.isAbstract supers, by
      simp [hq, hpackage, hsupers, Bind.bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨classes, hclasses⟩ := mapM_exists_ok hcls
  have hprop : ∀ x : Property × Nat, x ∈ model.properties.zipIdx → ∃ y : PropertyDecl,
      (fun x => do
        checkQualification x.1.alias (some (ownerName x.1.owner))
        let owner ← bindOwner model x.1.owner
        let type ← bindType model x.1.type
        pure (PropertyDecl.mk ⟨x.2⟩ (some x.1.name) owner type
          x.1.multiplicity x.1.aggregation x.1.isId)) x = .ok y := by
    rintro ⟨p, index⟩ hx
    have hp := List.fst_mem_of_mem_zipIdx hx
    have hq : checkQualification p.alias (some (ownerName p.owner)) = .ok () := by
      rw [checkQualification_iff]
      have hw := h.propertyOwners p hp
      cases ho : p.owner <;> simp [ho] at hw
      all_goals simpa [ownerName, qualifiedBy] using hw.2
    obtain ⟨owner, howner⟩ := bindOwner_exists h p hp
    obtain ⟨type, htype⟩ := bindType_exists h p hp
    exact ⟨PropertyDecl.mk ⟨index⟩ (some p.name) owner type
      p.multiplicity p.aggregation p.isId, by
      simp [hq, howner, htype, Bind.bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨properties, hproperties⟩ := mapM_exists_ok hprop
  have hassoc : ∀ x : Association × Nat, x ∈ model.associations.zipIdx → ∃ y : AssociationDecl,
      (fun x => do
        checkQualification x.1.alias x.1.package
        let boundPackage ← optionalPackage model x.1.package
        let ends ← match x.1.ends with
          | [first, second] => do pure (← propertyId model first, ← propertyId model second)
          | _ => throw ("association requires exactly two ends: " ++ showName x.1.alias)
        pure (AssociationDecl.mk ⟨x.2⟩ (some x.1.name) boundPackage ends)) x = .ok y := by
    rintro ⟨a, index⟩ hx
    have ha := List.fst_mem_of_mem_zipIdx hx
    have hw := h.associationPackages a ha
    have hq : checkQualification a.alias a.package = .ok () := by
      rw [checkQualification_iff]
      cases he : a.package with
      | none => simpa [he, rootQualified] using hw
      | some name =>
          have hw' := hw
          simp [he] at hw'
          exact hw'.2
    have hr : match a.package with | none => True | some name => resolvesPackage model name := by
      cases he : a.package with
      | none => simp
      | some name =>
          have hw' := hw
          simp [he] at hw'
          exact hw'.1
    obtain ⟨boundPackage, hpackage⟩ := optionalPackage_exists h hr
    obtain ⟨p, q, hends, hp, hqmem, _⟩ := h.associationEnds a ha
    obtain ⟨pid, hpid⟩ := propertyId_exists h ⟨p, hp, rfl⟩
    obtain ⟨qid, hqid⟩ := propertyId_exists h ⟨q, hqmem, rfl⟩
    exact ⟨AssociationDecl.mk ⟨index⟩ (some a.name) boundPackage (pid, qid), by
      simp [hq, hpackage, hends, hpid, hqid, Bind.bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨associations, hassociations⟩ := mapM_exists_ok hassoc
  have henum : ∀ x : Enumeration × Nat, x ∈ model.enumerations.zipIdx → ∃ y : EnumerationDecl,
      (fun x => do
        checkQualification x.1.alias x.1.package
        let boundPackage ← optionalPackage model x.1.package
        pure (EnumerationDecl.mk ⟨x.2⟩ (some x.1.name) boundPackage)) x = .ok y := by
    rintro ⟨e, index⟩ hx
    have he := List.fst_mem_of_mem_zipIdx hx
    have hw := h.enumPackages e he
    have hq : checkQualification e.alias e.package = .ok () := by
      rw [checkQualification_iff]
      cases he : e.package with
      | none => simpa [he, rootQualified] using hw
      | some name =>
          have hw' := hw
          simp [he] at hw'
          exact hw'.2
    have hr : match e.package with | none => True | some name => resolvesPackage model name := by
      cases he : e.package with
      | none => simp
      | some name =>
          have hw' := hw
          simp [he] at hw'
          exact hw'.1
    obtain ⟨boundPackage, hpackage⟩ := optionalPackage_exists h hr
    exact ⟨EnumerationDecl.mk ⟨index⟩ (some e.name) boundPackage, by
      simp [hq, hpackage, Bind.bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨enumerations, henumerations⟩ := mapM_exists_ok henum
  have hlit : ∀ x : Literal × Nat, x ∈ model.literals.zipIdx → ∃ y : LiteralDecl,
      (fun x => do
        checkQualification x.1.alias (some x.1.enumeration)
        let enumeration ← enumerationId model x.1.enumeration
        pure (LiteralDecl.mk ⟨x.2⟩ (some x.1.name) enumeration)) x = .ok y := by
    rintro ⟨l, index⟩ hx
    have hl := List.fst_mem_of_mem_zipIdx hx
    have hw := h.literalsResolved l hl
    have hq : checkQualification l.alias (some l.enumeration) = .ok () := by
      rw [checkQualification_iff]
      simpa [qualifiedBy] using hw.2
    obtain ⟨enumeration, henumeration⟩ := enumerationId_exists h hw.1
    exact ⟨{ id := ⟨index⟩, name := some l.name, enumeration }, by
      simp [hq, henumeration, Bind.bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨literals, hliterals⟩ := mapM_exists_ok hlit
  simp only [Bind.bind, Except.bind, pure, Except.pure] at hpackages hclasses hproperties hassociations henumerations hliterals
  exact ⟨{ packages, classes, properties, associations, enumerations, literals }, by
    unfold bindModel
    rw [show model.packages.map Package.alias ++ model.classes.map Class.alias ++
      model.properties.map Property.alias ++ model.associations.map Association.alias ++
      model.enumerations.map Enumeration.alias ++ model.literals.map Literal.alias = aliases model by rfl]
    simp only [hcheck, hpackages, hclasses, hproperties, henumerations,
      hliterals, Bind.bind, Except.bind, pure, Except.pure]
    exact congrArg (fun result : BindingResult (List AssociationDecl) =>
      result.bind fun boundAssociations => Except.ok
        (Schema.mk packages classes properties boundAssociations enumerations literals)) hassociations⟩

private theorem objectId_exists (hn : (snapshot.objects.map Object.alias).Nodup)
    (hm : ∃ o ∈ snapshot.objects, o.alias = name) :
    ∃ id, objectId snapshot name = .ok id := by
  rcases hm with ⟨o, ho, rfl⟩
  obtain ⟨index, hi⟩ := exists_resolveIndex_of_mem_of_nodup (kind := "object") hn
    (List.mem_map.mpr ⟨o, ho, rfl⟩)
  exact ⟨⟨index⟩, by simp [objectId, hi, Except.map]⟩

private theorem bindValue_matches_complete (hm : ModelWellFormed model)
    (ho : (snapshot.objects.map Object.alias).Nodup) {type : Source.ValueType}
    {value : Source.Value} (hmatch : sourceValueMatches model snapshot type value) :
    ∃ target, bindValue model snapshot value = .ok target := by
  cases type <;> cases value <;> simp [sourceValueMatches] at hmatch
  · exact ⟨.boolean _, rfl⟩
  · exact ⟨.integer _, rfl⟩
  · exact ⟨.string _, rfl⟩
  · rename_i expected actual literal
    rcases hmatch with ⟨rfl, declaration, hd, halias, henum⟩
    subst expected
    obtain ⟨eid, heid⟩ := enumerationId_exists hm (hm.literalsResolved declaration hd).1
    obtain ⟨lid, hlid⟩ := literalId_exists hm ⟨declaration, hd, halias⟩
    exact ⟨.enumeration eid lid, by
      simp [bindValue, heid, hlid, Bind.bind, Except.bind, pure, Except.pure]⟩
  · rename_i expected object
    rcases hmatch with ⟨declaration, hd, halias, _⟩
    obtain ⟨oid, hoid⟩ := objectId_exists ho ⟨declaration, hd, halias⟩
    exact ⟨.reference oid, by rw [bindValue, hoid]; rfl⟩

private theorem bindInstance_complete {model : Model} {snapshot : Instance}
    (h : SourceSatisfies { model, snapshot }) :
    ∃ target, bindInstance model snapshot = .ok target := by
  have hcheck : checkAliases "object" (snapshot.objects.map Object.alias) = .ok () := by
    rw [checkAliases_iff, aliasEnvironment_iff]
    refine ⟨h.uniqueObjectAliases, ?_⟩
    rintro name (hm : name ∈ snapshot.objects.map Object.alias)
    rcases List.mem_map.mp hm with ⟨o, ho, rfl⟩
    exact validAlias_of_nameValid (h.objectAliasesValid o ho)
  have hobjects : ∀ x : Object × Nat, x ∈ snapshot.objects.zipIdx →
      ∃ y : ObjectDecl, (fun x => do
        let classifier ← classId model x.1.classifier
        pure (ObjectDecl.mk ⟨x.2⟩ classifier)) x = .ok y := by
    rintro ⟨o, index⟩ hx
    have ho := List.fst_mem_of_mem_zipIdx hx
    obtain ⟨classifier, hc⟩ := classId_exists h.model (h.classifiersResolved o ho)
    exact ⟨ObjectDecl.mk ⟨index⟩ classifier, by simp [hc, Bind.bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨objects, hobjs⟩ := mapM_exists_ok hobjects
  have hobservations : ∀ a ∈ snapshot.observations, ∃ y : VLMOF.Observation,
      (fun entry => do
        let object ← objectId snapshot entry.object
        let property ← propertyId model entry.property
        let occurrences ← entry.occurrences.mapM (bindValue model snapshot)
        pure (VLMOF.Observation.mk object property occurrences)) a = .ok y := by
    intro a ha
    rcases h.observationKeysResolved a ha with ⟨ho, hp⟩
    obtain ⟨object, hobject⟩ := objectId_exists h.uniqueObjectAliases ho
    obtain ⟨property, hproperty⟩ := propertyId_exists h.model hp
    rcases hp with ⟨p, hp, halias⟩
    obtain ⟨occurrences, hoccurrences⟩ := mapM_exists_ok (xs := a.occurrences) (fun value hv =>
      bindValue_matches_complete h.model h.uniqueObjectAliases
        (h.valuesTyped a ha p hp halias value hv))
    exact ⟨VLMOF.Observation.mk object property occurrences, by
      simp [hobject, hproperty, hoccurrences, Bind.bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨observations, hobs⟩ := mapM_exists_ok hobservations
  simp only [Bind.bind, Except.bind, pure, Except.pure] at hobjs hobs
  refine ⟨Snapshot.mk objects observations, ?_⟩
  unfold bindInstance
  simp only [hcheck, hobjs, hobs, Bind.bind, Except.bind, pure, Except.pure]

/-- A satisfying source document has a successful numeric elaboration.  This is
binding completeness only; it does not assume or conclude target conformance. -/
theorem elaborate_complete {document : Document} (h : SourceSatisfies document) :
    ∃ schema snapshot, elaborate document = .ok (schema, snapshot) := by
  cases document with
  | mk model snapshot =>
  obtain ⟨schema, hs⟩ := bindModel_complete h.model
  obtain ⟨target, hi⟩ := bindInstance_complete h
  exact ⟨schema, target, by
    simp [elaborate, hs, hi, Bind.bind, Except.bind, pure, Except.pure]⟩

end VLMOF.Source
