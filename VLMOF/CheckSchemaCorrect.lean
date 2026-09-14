import VLMOF.CheckCorrect

namespace VLMOF

theorem all_decide_eq_true {α : Type} (xs : List α) (p : α → Prop)
    [∀ x, Decidable (p x)] :
    xs.all (fun x => decide (p x)) = true ↔ ∀ x ∈ xs, p x := by
  simp

theorem optionalCheck_eq_true {α β : Type} (x : Option α) (p : α → Prop)
    [∀ a, Decidable (p a)] :
    (match x with | none => true | some a => decide (p a)) = true ↔
      ∀ a, x = some a → p a := by
  cases x <;> simp

theorem refType_eq_true (t : ValueType) :
    refType t = true ↔ ∃ c, t = .reference c := by
  cases t <;> simp [refType]

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

end VLMOF
