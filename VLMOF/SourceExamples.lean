import VLMOF.Elaboration

namespace VLMOF.Source.BindingExamples

/-- Same-named class declarations remain distinct, and the subclass observation
uses the original inherited property's alias. No semantic acceptance is claimed here. -/
def sample : Document :=
  { model :=
      { packages := [{ alias := ["p"], name := "p", parent := none }]
        classes :=
          [{ alias := ["p", "A"], name := "Node", package := some ["p"],
             isAbstract := true, directSupers := [] },
           { alias := ["p", "B"], name := "Node", package := some ["p"],
             isAbstract := false, directSupers := [["p", "A"]] }]
        properties :=
          [{ alias := ["p", "A", "code"], name := "code", owner := .class ["p", "A"],
             type := .integer,
             multiplicity := { lower := 0, upper := .finite 2, isOrdered := true,
                               isUnique := false },
             aggregation := .none, isId := false }]
        associations := [], enumerations := [], literals := [] }
    snapshot :=
      { objects := [{ alias := ["b"], classifier := ["p", "B"] }]
        observations :=
          [{ object := ["b"], property := ["p", "A", "code"],
             occurrences := [.integer 0, .integer 0] }] } }

example : (elaborate sample).map (fun result => result.1.classes.map ClassDecl.id) =
    .ok [⟨0⟩, ⟨1⟩] := rfl
example : (elaborate sample).map (fun result => result.2.objects.map ObjectDecl.classifier) =
    .ok [⟨1⟩] := rfl
example : (elaborate sample).map (fun result => result.2.observations.map VLMOF.Observation.occurrences) =
    .ok [[.integer 0, .integer 0]] := rfl

/-- Resolving all observations forbids dangling references even in an otherwise
well-bound document; an absent declaration is never replaced by numeric ID zero. -/
def unknownProperty : Document :=
  { sample with snapshot :=
      { sample.snapshot with observations :=
          [{ object := ["b"], property := ["p", "B", "missing"], occurrences := [] }] } }
example : elaborate unknownProperty = .error "unknown property alias: p::B::missing" := rfl

/-- An alias in the wrong ownership scope fails before the core is produced. -/
def wrongScope : Document :=
  { sample with model :=
      { sample.model with classes :=
          [{ alias := ["different", "A"], name := "Node", package := some ["p"],
             isAbstract := false, directSupers := [] }] } }
example : elaborate wrongScope =
    .error "alias qualification disagrees with owner: different::A" := rfl

end VLMOF.Source.BindingExamples
