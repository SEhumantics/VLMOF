import VLMOF.SourceSemantics

/-! Concrete witnesses for the symbolic source semantics. -/

namespace VLMOF.Source.SemanticExamples

def accepted : Document :=
  { model :=
      { packages := [{ alias := ["p"], name := "P", parent := none }]
        classes := [{ alias := ["p", "C"], name := "C", package := some ["p"],
                      isAbstract := false, directSupers := [] }]
        properties := [], associations := [], enumerations := [], literals := [] }
    snapshot := { objects := [{ alias := ["o"], classifier := ["p", "C"] }], observations := [] } }

theorem accepted_model : ModelWellFormed accepted.model := by
  constructor <;>
    simp [accepted, aliases, uniqueAliases, NameValid, VLMOF.validString, VLMOF.xmlChar,
      resolvesPackage, resolvesClass, resolvesAssociation, resolvesEnumeration,
      packageEntries, classEntries, associationEntries, enumerationEntries, qualifiedBy,
      rootQualified, validDisplayName]
  all_goals native_decide

theorem accepted_satisfies : SourceSatisfies accepted := by
  constructor
  · exact accepted_model
  all_goals
    simp [accepted, NameValid, VLMOF.validString, VLMOF.xmlChar,
      resolvesClass, classEntries, propertyApplies, sourceOccurrences,
      sourceCompositeEdge, incomingCompositeCount]
  all_goals native_decide

/-- Duplicate identities are raw source syntax but cannot satisfy `ModelWellFormed`. -/
def duplicateClassAlias : Model :=
  { accepted.model with classes := accepted.model.classes ++ accepted.model.classes }

example : ¬ ModelWellFormed duplicateClassAlias := by
  intro h
  have hd := h.uniqueQualifiedAliases
  simp [duplicateClassAlias, accepted, uniqueAliases, aliases] at hd

/-- Target metadata names are optional only before source validation; an empty
source spelling is rejected because elaboration produces `some ""`. -/
def emptyDisplayName : Model :=
  { accepted.model with classes :=
      [{ alias := ["p", "C"], name := "", package := some ["p"],
         isAbstract := false, directSupers := [] }] }

example : ¬ ModelWellFormed emptyDisplayName := by
  intro h
  have hn := h.displayNames.2.1
  let c : Class := { alias := ["p", "C"], name := "", package := some ["p"],
                      isAbstract := false, directSupers := [] }
  have hc := hn c (by simp [c, emptyDisplayName, accepted])
  simp [c, validDisplayName] at hc

/-- A descendant that skips a lexical owner level is raw syntax but fails the same
`dropLast` qualification rule used by binding. -/
def skippedQualification : Model :=
  { accepted.model with classes :=
      [{ alias := ["p", "nested", "C"], name := "C", package := some ["p"],
         isAbstract := false, directSupers := [] }] }

example : ¬ ModelWellFormed skippedQualification := by
  intro h
  let c : Class := { alias := ["p", "nested", "C"], name := "C", package := some ["p"],
                      isAbstract := false, directSupers := [] }
  have hq := h.classPackages c (by simp [c, skippedQualification, accepted])
  simp [c, skippedQualification, qualifiedBy] at hq

/-- A nonbinary association is representable but rejected by the raw-binary end rule. -/
def nonbinaryAssociation : Model :=
  { packages := []
    classes :=
      [{ alias := ["A"], name := "A", package := none, isAbstract := false, directSupers := [] },
       { alias := ["B"], name := "B", package := none, isAbstract := false, directSupers := [] },
       { alias := ["C"], name := "C", package := none, isAbstract := false, directSupers := [] }]
    properties :=
      [{ alias := ["A", "ab"], name := "ab", owner := .class ["A"], type := .reference ["B"],
         multiplicity := { lower := 0, upper := .unlimited, isOrdered := false, isUnique := false },
         aggregation := .none, isId := false }]
    associations := [{ alias := ["R"], name := "R", package := none,
                       ends := [["A", "ab"], ["x"], ["y"]] }]
    enumerations := [], literals := [] }

example : ¬ ModelWellFormed nonbinaryAssociation := by
  intro h
  let a : Association :=
    { alias := ["R"], name := "R", package := none, ends := [["A", "ab"], ["x"], ["y"]] }
  have ha : a ∈ nonbinaryAssociation.associations := by simp [a, nonbinaryAssociation]
  have he := h.associationEnds a ha
  simp [a, nonbinaryAssociation] at he

end VLMOF.Source.SemanticExamples
