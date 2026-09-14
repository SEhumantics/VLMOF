import VLMOF.DSL
import VLMOF.Elaboration

namespace VLMOF.Source
namespace DSLExamples

/-- Binding-only regression: deliberately retains schema and snapshot violations
for the later conformance layer (including orphan end and duplicate observation). -/
def source : String :=
  "package p { enum Color { red; } class A { first : Integer [0..2] ordered nonunique; second : String [0..1] unordered unique; link : p::B [0..*] unordered nonunique; } class B { back : p::A [0..1] unordered unique; } class Diamond extends p::A, p::B { } association R { end owned : p::B [0..*] ordered nonunique; end host : p::A [1..1] unordered unique composite; ends p::A::link, p::R::owned; } } object obj : p::Diamond { observe p::A::first = [1, -2, 1]; observe p::A::link = [@obj, @obj]; observe p::A::second = []; observe p::R::owned = [@obj]; observe p::A::second = [p::Color::red]; }"

def bound : Except String (Schema × Snapshot) := do
  let document ← parse source
  elaborate document

example : bound.isOk := by native_decide

def boundIds : Bool := match bound with
  | .ok (schema, snapshot) =>
      decide (schema.classes.map ClassDecl.id = [⟨0⟩, ⟨1⟩, ⟨2⟩] ∧
        schema.properties.map PropertyDecl.id = [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩] ∧
        schema.associations.map AssociationDecl.ends = [(⟨2⟩, ⟨4⟩)] ∧
        snapshot.objects.map ObjectDecl.id = [⟨0⟩])
  | .error _ => false

def boundOccurrences : Bool := match bound with
  | .ok (_, snapshot) => decide (snapshot.observations.map VLMOF.Observation.occurrences =
      [[VLMOF.Value.integer 1, VLMOF.Value.integer (-2), VLMOF.Value.integer 1],
       [VLMOF.Value.reference (VLMOF.ObjectId.mk 0), VLMOF.Value.reference (VLMOF.ObjectId.mk 0)],
       [],
       [VLMOF.Value.reference (VLMOF.ObjectId.mk 0)],
       [VLMOF.Value.enumeration (VLMOF.EnumerationId.mk 0) (VLMOF.LiteralId.mk 0)]])
  | .error _ => false

example : boundIds := by native_decide
example : boundOccurrences := by native_decide
example : (parse "class X { p : Integer [0..1] unordered unique; } object x : X { observe p = [1,]; }").isOk = false := by native_decide
example : (parse "class X { p : Integer [0..1] unordered unique; }").isOk := by native_decide

end DSLExamples
end VLMOF.Source

