import VLMOF.Model.Basic

/-!
# Symbolic source declarations

The source language names declarations with qualified aliases. These aliases are
binding keys, not EMOF names and not core numeric identities (MOF 12.5.1/12.5.4).
For example, `leftCode` and `rightCode` can both display the name `code` while
remaining separately addressable. Runtime object aliases have a separate domain.

A Model has an implicit outer package scope. Top-level declarations are owned by
that scope; `package := none` is its compact encoding, not absent ownership.
The scope has no source binding alias (see docs/model.md).

This AST is before binding and therefore retains unknown references and ambiguous
aliases for diagnostics. Multiplicity and aggregation reuse value constructors,
not target conformance. No definition below calls core conformance or elaborates
an input as a way of defining its source meaning.
-/
namespace VLMOF.Source

/-- Qualified binding components; component boundaries remain significant. -/
abbrev Name := List String

structure Package where
  alias : Name
  name : String
  parent : Option Name
  deriving DecidableEq, Repr

structure Class where
  alias : Name
  name : String
  package : Option Name
  isAbstract : Bool
  directSupers : List Name
  deriving DecidableEq, Repr

inductive ValueType where
  | boolean
  | integer
  | string
  | enumeration (alias : Name)
  | reference (alias : Name)
  deriving DecidableEq, Repr

inductive Owner where
  | class (alias : Name)
  | association (alias : Name)
  deriving DecidableEq, Repr

structure Property where
  alias : Name
  name : String
  owner : Owner
  type : ValueType
  multiplicity : Multiplicity
  aggregation : Aggregation
  isId : Bool
  deriving DecidableEq, Repr

structure Association where
  alias : Name
  name : String
  package : Option Name
  /-- Keep raw arity so the binding boundary can diagnose a non-binary form. -/
  ends : List Name
  deriving DecidableEq, Repr

structure Enumeration where
  alias : Name
  name : String
  package : Option Name
  deriving DecidableEq, Repr

structure Literal where
  alias : Name
  name : String
  enumeration : Name
  deriving DecidableEq, Repr

structure Model where
  packages : List Package
  classes : List Class
  properties : List Property
  associations : List Association
  enumerations : List Enumeration
  literals : List Literal
  deriving DecidableEq, Repr

inductive Value where
  | boolean (value : Bool)
  | integer (value : Int)
  | string (value : String)
  | enumeration (enumeration literal : Name)
  | reference (object : Name)
  deriving DecidableEq, Repr

structure Object where
  alias : Name
  classifier : Name
  deriving DecidableEq, Repr

/-- All-end observations permit independent orderings at opposite ends.
An association-owned observation describes incidence, not runtime navigation. -/
structure Observation where
  object : Name
  property : Name
  occurrences : List Value
  deriving DecidableEq, Repr

structure Instance where
  objects : List Object
  observations : List Observation
  deriving DecidableEq, Repr

structure Document where
  model : Model
  snapshot : Instance
  deriving DecidableEq, Repr

/-- Return all matches rather than silently choosing one ambiguous binding. -/
def lookupAll {α : Type} (key : α → Name) (entries : List α) (alias : Name) : List α :=
  entries.filter fun entry => decide (key entry = alias)

/-- The resolver's candidate list has exactly the symbolic binding meaning:
membership in the source environment and equality of the qualified alias. -/
theorem mem_lookupAll {α : Type} (key : α → Name) (entries : List α)
    (alias : Name) (entry : α) :
    entry ∈ lookupAll key entries alias ↔ entry ∈ entries ∧ key entry = alias := by
  simp [lookupAll]

inductive Resolution (α : Type) where
  | missing
  | unique (value : α)
  | ambiguous (values : List α)
  deriving Repr

/-- Kind-specific environments distinguish an unknown class from a same-spelled
property. Ambiguity survives until an elaborator issues a diagnostic. -/
def resolve {α : Type} (key : α → Name) (entries : List α) (alias : Name) : Resolution α :=
  match lookupAll key entries alias with
  | [] => .missing
  | [entry] => .unique entry
  | entries => .ambiguous entries

/-- Symbolic occurrence observation, independently of target numeric IDs. -/
def Equivalent (ordered : Bool) (left right : List Value) : Prop :=
  if ordered then left = right else left.Perm right

namespace Examples

def first : Class :=
  { alias := ["p", "First"], name := "Node", package := some ["p"],
    isAbstract := false, directSupers := [] }

def second : Class :=
  { alias := ["p", "Second"], name := "Node", package := some ["p"],
    isAbstract := false, directSupers := [] }

-- Display spelling never determines binding identity.
example : first.name = second.name := rfl
example : lookupAll Class.alias [first, second] ["p", "First"] = [first] := rfl
-- Reusing an alias remains ambiguous even if the records themselves are equal.
example : lookupAll Class.alias [first, first] ["p", "First"] = [first, first] := rfl
-- A missing observation is not false or zero; duplicates are not collapsed.
example : ([] : List Value) ≠ [.boolean false] := by simp
example : ¬ Equivalent false [.integer 7, .integer 7] [.integer 7] := by
  simp [Equivalent]

end Examples
end VLMOF.Source

