import VLMOF.Source.Parser
import VLMOF.Source.Elaboration

namespace VLMOF.Source

namespace Examples

/-! Executable parser examples cover nested qualification and lossless retention
of duplicate and negative occurrences.  The boolean projections below are kept
small so `native_decide` or an evaluator can inspect individual parser promises. -/

/-- A compact nested-package example used to exercise contextual qualification. -/
def nested : Except String Document := parse "package pets { package domestic { class Animal { name : String [0..1] unordered unique (id); } enum Mood { happy; } } class Person { pets : Pet [0..*] ordered nonunique; } association Ownership { end pet : Pet [0..1] unordered unique; end owner : Person [1..1] unordered unique composite; ends pets::pet, Ownership::owner; } }"

/-- A broader parser fixture containing classes, associations, an enumeration,
objects, duplicates, references, and negative integers. -/
def decoded : Except String Document := parse
  "package p { enum Color { red; blue; } class A { first : Integer [0..2] ordered nonunique; second : String [0..1] unordered unique; link : B [0..*] unordered nonunique; } class B { back : A [0..1] unordered unique; } association R { end owned : B [0..*] ordered nonunique; end host : A [1..1] unordered unique composite; ends p::A::link, p::R::owned; } } object obj : p::A { observe p::A::first = [1, -2, 1]; observe p::A::link = [@obj, @obj]; observe p::A::second = [p::Color::red]; }"

example : nested.isOk := by native_decide
example : decoded.isOk := by native_decide
/-- Checks that package context qualifies class aliases while retaining source order. -/
def decodedClasses : Bool := match decoded with | .ok d => decide (d.model.classes.map Class.alias = [["p", "A"], ["p", "B"]]) | .error _ => false
/-- Checks qualification of both class-owned and association-owned properties. -/
def decodedProperties : Bool := match decoded with | .ok d => decide (d.model.properties.map Property.alias = [["p", "A", "first"], ["p", "A", "second"], ["p", "A", "link"], ["p", "B", "back"], ["p", "R", "owned"], ["p", "R", "host"]]) | .error _ => false
/-- Checks that explicit association-end aliases are retained in their given order. -/
def decodedEnds : Bool := match decoded with | .ok d => decide (d.model.associations.map Association.ends = [[ ["p", "A", "link"], ["p", "R", "owned"] ]]) | .error _ => false
/-- Checks lossless value decoding, including duplicates, a negative integer,
object references, and a qualified enumeration literal. -/
def decodedValues : Bool := match decoded with | .ok d => decide (d.snapshot.observations.map Observation.occurrences = [[.integer 1, .integer (-2), .integer 1], [.reference ["obj"], .reference ["obj"]], [.enumeration ["p", "Color"] ["p", "Color", "red"]]]) | .error _ => false
example : decodedClasses := by native_decide
example : decodedProperties := by native_decide
example : decodedEnds := by native_decide
example : decodedValues := by native_decide
example : (parse "class Broken { x : Integer [0..] unordered unique; }").isOk = false := by native_decide
example : (parse "class Broken { x : Integer [0..1] unordered unique; }").isOk := by native_decide
example : (parse "class Broken { x : Integer [0..1] unordered unique; } object o : Broken { observe x = [1 2]; }").isOk = false := by native_decide
example : (parse "abstract enum Bad { x; }").isOk = false := by native_decide

end Examples

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

