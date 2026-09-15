import VLMOF.Checker.Correctness.Local

/-!
# Schema-checker reflection

The small list and option reflection lemmas support the main theorem, which maps each
named Boolean schema check to the corresponding `SchemaWellFormed` field.
-/

namespace VLMOF

/-- A list of decided propositions passes `List.all` exactly when every member
satisfies the proposition. -/
theorem all_decide_eq_true {α : Type} (xs : List α) (p : α → Prop)
    [∀ x, Decidable (p x)] :
    xs.all (fun x => decide (p x)) = true ↔ ∀ x ∈ xs, p x := by
  simp

/-- An optional-value check is vacuous for `none` and requires `p` for the stored
value of `some`; cases on the option prove the reflection. -/
theorem optionalCheck_eq_true {α : Type} (x : Option α) (p : α → Prop)
    [∀ a, Decidable (p a)] :
    (match x with | none => true | some a => decide (p a)) = true ↔
      ∀ a, x = some a → p a := by
  cases x <;> simp

/-- `refType` recognizes exactly the `ValueType.reference` constructor. -/
theorem refType_eq_true (t : ValueType) :
    refType t = true ↔ ∃ c, t = .reference c := by
  cases t <;> simp [refType]

/-- Reflection of every conjunct checked for one candidate association-end pair.
The only structural case split is reference-type recognition for both ends. -/
theorem associationPairOK_eq_true (a : AssociationDecl) (p q : PropertyDecl) :
    associationPairOK a p q = true ↔
      a.ends = (p.id, q.id) ∧ p.id ≠ q.id ∧
      (∃ pc, p.type = .reference pc) ∧ (∃ qc, q.type = .reference qc) ∧
      ownerMatchesEnd a p ∧ ownerMatchesEnd a q ∧ classOwnerIsSource p q ∧
      classOwnerIsSource q p ∧ atMostOneAssociationOwned p q ∧
      ¬(p.aggregation = .composite ∧ q.aggregation = .composite) := by
  simp only [associationPairOK, Bool.and_eq_true, decide_eq_true_eq]
  rw [refType_eq_true, refType_eq_true]
  simp only [and_assoc]

/-- The nested executable searches accept exactly when every stored association has
two property witnesses satisfying the declarative end constraints. -/
theorem associationEndsCheck_eq_true (s : Schema) :
    (s.associations.all fun a =>
      s.properties.any fun p => s.properties.any fun q => associationPairOK a p q) = true ↔
    ∀ a ∈ s.associations, ∃ p q,
      a.ends = (p.id, q.id) ∧ p ∈ s.properties ∧ q ∈ s.properties ∧ p.id ≠ q.id ∧
      (∃ pc, p.type = .reference pc) ∧ (∃ qc, q.type = .reference qc) ∧
      ownerMatchesEnd a p ∧ ownerMatchesEnd a q ∧ classOwnerIsSource p q ∧
      classOwnerIsSource q p ∧ atMostOneAssociationOwned p q ∧
      ¬(p.aggregation = .composite ∧ q.aggregation = .composite) := by
  simp only [List.all_eq_true, List.any_eq_true, associationPairOK_eq_true]
  constructor
  · intro h a ha
    rcases h a ha with ⟨p,hp,q,hq,hr⟩
    exact ⟨p,q,hr.1,hp,hq,hr.2⟩
  · intro h a ha
    rcases h a ha with ⟨p,q,he,hp,hq,hr⟩
    exact ⟨p,hp,q,hq,he,hr⟩

/-- The executable declaration checks accept exactly the source-level schema
contract.  Each Boolean guard below is reflected into its corresponding logical
field; no well-formedness premise is assumed. -/
theorem checkSchema_iff (s : Schema) : checkSchema s = true ↔ SchemaWellFormed s := by
  simp only [checkSchema, schemaFieldChecks, List.all_cons, List.all_nil,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, associationPairOK_eq_true,
    refType_eq_true, and_true]
  constructor
  · rintro ⟨uP, uC, uPr, uA, uE, uL, names, parents, pac, cpk, epk, apk, supers,
      iac, mult, owners, types, composites, lits, ends, memberships, containers, ids⟩
    refine ⟨uP, uC, uPr, uA, uE, uL, (by simpa [and_assoc] using names), ?_, ?_, ?_, ?_, ?_, supers, iac, mult,
      ?_, ?_, ?_, lits, ?_, memberships, ?_, ids⟩
    · intro d hd p hp
      cases hdparent : d.parent with
      | none => simp [hdparent] at hp
      | some q =>
        have hpq : p = q := Option.some.inj (hp.symm.trans hdparent)
        subst p; simpa [hdparent] using parents d hd
    · intro d hd p hp
      cases hdparent : d.parent with
      | none => simp [hdparent] at hp
      | some q =>
        have hpq : p = q := Option.some.inj (hp.symm.trans hdparent)
        subst p; simpa [hdparent] using pac d hd
    · intro d hd p hp
      cases hdpackage : d.package with
      | none => simp [hdpackage] at hp
      | some q =>
        have hpq : p = q := Option.some.inj (hp.symm.trans hdpackage)
        subst p; simpa [hdpackage] using cpk d hd
    · intro d hd p hp
      cases hdpackage : d.package with
      | none => simp [hdpackage] at hp
      | some q =>
        have hpq : p = q := Option.some.inj (hp.symm.trans hdpackage)
        subst p; simpa [hdpackage] using epk d hd
    · intro d hd p hp
      cases hdpackage : d.package with
      | none => simp [hdpackage] at hp
      | some q =>
        have hpq : p = q := Option.some.inj (hp.symm.trans hdpackage)
        subst p; simpa [hdpackage] using apk d hd
    · intro p hp
      cases howner : p.owner with
      | «class» c => simpa only [howner, decide_eq_true_eq] using owners p hp
      | association a =>
        simpa only [howner, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true,
          decide_eq_true_eq] using owners p hp
    · intro p hp
      cases htype : p.type with
      | boolean => trivial
      | integer => trivial
      | string => trivial
      | enumeration e => simpa only [htype, decide_eq_true_eq] using types p hp
      | reference c => simpa only [htype, decide_eq_true_eq] using types p hp
    · intro p hp hcomposite
      rcases composites p hp with hnone | ⟨c, hc⟩
      · exact False.elim (hnone hcomposite)
      · exact ⟨c, hc⟩
    · intro a ha
      rcases ends a ha with ⟨p, hp, q, hq, he, hrest⟩
      exact ⟨p, q, he, hp, hq, hrest⟩
    · intro a ha p q he hp hq
      rcases containers a ha p hp q hq with hne | ⟨left, right⟩
      · exact False.elim (hne he)
      constructor
      · intro hcomposite
        rcases left with hnone | hupper
        · exact False.elim (hnone hcomposite)
        · exact hupper
      · intro hcomposite
        rcases right with hnone | hupper
        · exact False.elim (hnone hcomposite)
        · exact hupper
  · intro h
    refine ⟨h.uniquePackageIds, h.uniqueClassIds, h.uniquePropertyIds,
      h.uniqueAssociationIds, h.uniqueEnumerationIds, h.uniqueLiteralIds, (by simpa [and_assoc] using h.names),
      ?_, ?_, ?_, ?_, ?_, h.supersResolved, h.inheritanceAcyclic, h.multiplicities,
      ?_, ?_, ?_, h.literalsResolved, ?_, h.endMembershipUnique, ?_, h.inheritedIdCount⟩
    · intro d hd
      cases hdparent : d.parent with
      | none => rfl
      | some p => exact decide_eq_true_eq.mpr (h.packageParentsResolved d hd p hdparent)
    · intro d hd
      cases hdparent : d.parent with
      | none => rfl
      | some p => exact decide_eq_true_eq.mpr (h.packageAcyclic d hd p hdparent)
    · intro d hd
      cases hdpackage : d.package with
      | none => rfl
      | some p => exact decide_eq_true_eq.mpr (h.classPackagesResolved d hd p hdpackage)
    · intro d hd
      cases hdpackage : d.package with
      | none => rfl
      | some p => exact decide_eq_true_eq.mpr (h.enumPackagesResolved d hd p hdpackage)
    · intro d hd
      cases hdpackage : d.package with
      | none => rfl
      | some p => exact decide_eq_true_eq.mpr (h.associationPackagesResolved d hd p hdpackage)
    · intro p hp
      cases howner : p.owner with
      | «class» c => exact decide_eq_true_eq.mpr (by simpa only [howner] using h.propertyOwnersResolved p hp)
      | association aid =>
        rcases (by simpa only [howner] using h.propertyOwnersResolved p hp) with ⟨a, ha, hid, hend⟩
        apply List.any_eq_true.mpr
        refine ⟨a, ha, ?_⟩
        simp [hid, hend]
    · intro p hp
      cases htype : p.type with
      | boolean => rfl
      | integer => rfl
      | string => rfl
      | enumeration e => exact decide_eq_true_eq.mpr (by simpa only [htype] using h.propertyTypesResolved p hp)
      | reference c => exact decide_eq_true_eq.mpr (by simpa only [htype] using h.propertyTypesResolved p hp)
    · intro p hp
      by_cases hc : p.aggregation = .composite
      · right
        rcases h.compositeReferences p hp hc with ⟨c, htype⟩
        exact ⟨c, htype⟩
      · exact Or.inl hc
    · intro a ha
      rcases h.associationEnds a ha with ⟨p, q, he, hp, hq, hrest⟩
      exact ⟨p, hp, q, hq, he, hrest⟩
    · intro a ha p hp q hq
      by_cases he : a.ends = (p.id, q.id)
      · right
        constructor
        · by_cases hc : p.aggregation = .composite
          · right; exact h.containerUpperOne a ha p q he hp hq |>.1 hc
          · exact Or.inl hc
        · by_cases hc : q.aggregation = .composite
          · right; exact h.containerUpperOne a ha p q he hp hq |>.2 hc
          · exact Or.inl hc
      · exact Or.inl he

end VLMOF
