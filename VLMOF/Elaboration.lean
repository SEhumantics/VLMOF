import VLMOF.Source

/-!
# Resolving symbolic aliases into finite core identities

IDs are positions in kind-specific declaration lists. Resolution requires exactly
one candidate: neither duplicate aliases nor unknown references are projected away.
Display names are copied as metadata and have no effect on binding. This module
implements binding only; successful binding is not a conformance decision.
-/
namespace VLMOF.Source

abbrev BindingResult := Except String

def showName (name : Name) : String := String.intercalate "::" name

def matchingIndices (names : List Name) (name : Name) : List Nat :=
  (names.zipIdx.filter fun pair => decide (pair.1 = name)).map Prod.snd

def resolveIndex (kind : String) (names : List Name) (name : Name) : BindingResult Nat :=
  match matchingIndices names name with
  | [] => .error ("unknown " ++ kind ++ " alias: " ++ showName name)
  | [i] => .ok i
  | _ => .error ("ambiguous " ++ kind ++ " alias: " ++ showName name)

def validAlias (name : Name) : Bool :=
  !name.isEmpty && name.all (fun component => !component.isEmpty)

/-- Check entries in order against the complete environment, preserving the first
binding diagnostic. The explicit recursion also exposes the completeness boundary. -/
def checkAliasEntries (kind : String) (environment : List Name) : List Name → BindingResult Unit
  | [] => pure ()
  | name :: rest => do
      if !validAlias name then throw ("empty component in " ++ kind ++ " alias")
      let _ ← resolveIndex kind environment name
      checkAliasEntries kind environment rest

def checkAliases (kind : String) (names : List Name) : BindingResult Unit :=
  checkAliasEntries kind names names
private def packageId (model : Model) (name : Name) : BindingResult PackageId :=
  (resolveIndex "package" (model.packages.map Package.alias) name).map PackageId.mk
private def classId (model : Model) (name : Name) : BindingResult ClassId :=
  (resolveIndex "class" (model.classes.map Class.alias) name).map ClassId.mk
private def propertyId (model : Model) (name : Name) : BindingResult PropertyId :=
  (resolveIndex "property" (model.properties.map Property.alias) name).map PropertyId.mk
private def associationId (model : Model) (name : Name) : BindingResult AssociationId :=
  (resolveIndex "association" (model.associations.map Association.alias) name).map AssociationId.mk
def enumerationId (model : Model) (name : Name) : BindingResult EnumerationId :=
  (resolveIndex "enumeration" (model.enumerations.map Enumeration.alias) name).map EnumerationId.mk
def literalId (model : Model) (name : Name) : BindingResult LiteralId :=
  (resolveIndex "literal" (model.literals.map Literal.alias) name).map LiteralId.mk
def objectId (snapshot : Instance) (name : Name) : BindingResult ObjectId :=
  (resolveIndex "object" (snapshot.objects.map Object.alias) name).map ObjectId.mk

private def optionalPackage (model : Model) : Option Name → BindingResult (Option PackageId)
  | none => pure none
  | some name => some <$> packageId model name

/-- Alias qualification reflects lexical ownership; semantic display spelling is
intentionally absent from this check. Detached/root declarations have one component. -/
def checkQualification (name : Name) (owner : Option Name) : BindingResult Unit :=
  if name.dropLast = owner.getD [] then pure ()
  else throw ("alias qualification disagrees with owner: " ++ showName name)

private def bindType (model : Model) : Source.ValueType → BindingResult VLMOF.ValueType
  | .boolean => pure .boolean
  | .integer => pure .integer
  | .string => pure .string
  | .enumeration name => .enumeration <$> enumerationId model name
  | .reference name => .reference <$> classId model name

private def bindOwner (model : Model) : Owner → BindingResult PropertyOwner
  | .class name => .class <$> classId model name
  | .association name => .association <$> associationId model name

private def ownerName : Owner → Name
  | .class name | .association name => name

/-- Bind each represented declaration exactly once and preserve input list order.
Non-binding constraints (cycles, multiplicity, type compatibility, names) belong to
source satisfaction and the conformance layer, not this resolution procedure. -/
def bindModel (model : Model) : BindingResult Schema := do
  let names := model.packages.map Package.alias ++ model.classes.map Class.alias ++
    model.properties.map Property.alias ++ model.associations.map Association.alias ++
    model.enumerations.map Enumeration.alias ++ model.literals.map Literal.alias
  checkAliases "declaration" names
  let packages ← model.packages.zipIdx.mapM fun (entry, index) => do
    checkQualification entry.alias entry.parent
    let parent ← optionalPackage model entry.parent
    pure ({ id := ⟨index⟩, name := some entry.name, parent } : PackageDecl)
  let classes ← model.classes.zipIdx.mapM fun (entry, index) => do
    checkQualification entry.alias entry.package
    let package ← optionalPackage model entry.package
    let directSupers ← entry.directSupers.mapM (classId model)
    pure ({ id := ⟨index⟩, name := some entry.name, package,
            isAbstract := entry.isAbstract, directSupers } : ClassDecl)
  let properties ← model.properties.zipIdx.mapM fun (entry, index) => do
    checkQualification entry.alias (some (ownerName entry.owner))
    let owner ← bindOwner model entry.owner
    let type ← bindType model entry.type
    pure ({ id := ⟨index⟩, name := some entry.name, owner, type,
            multiplicity := entry.multiplicity, aggregation := entry.aggregation,
            isId := entry.isId } : PropertyDecl)
  let associations ← model.associations.zipIdx.mapM fun (entry, index) => do
    checkQualification entry.alias entry.package
    let package ← optionalPackage model entry.package
    let ends ← match entry.ends with
      | [first, second] => do pure (← propertyId model first, ← propertyId model second)
      | _ => throw ("association requires exactly two ends: " ++ showName entry.alias)
    pure ({ id := ⟨index⟩, name := some entry.name, package, ends } : AssociationDecl)
  let enumerations ← model.enumerations.zipIdx.mapM fun (entry, index) => do
    checkQualification entry.alias entry.package
    let package ← optionalPackage model entry.package
    pure ({ id := ⟨index⟩, name := some entry.name, package } : EnumerationDecl)
  let literals ← model.literals.zipIdx.mapM fun (entry, index) => do
    checkQualification entry.alias (some entry.enumeration)
    let enumeration ← enumerationId model entry.enumeration
    pure ({ id := ⟨index⟩, name := some entry.name, enumeration } : LiteralDecl)
  pure { packages, classes, properties, associations, enumerations, literals }

def bindValue (model : Model) (snapshot : Instance) : Source.Value → BindingResult VLMOF.Value
  | .boolean value => pure (.boolean value)
  | .integer value => pure (.integer value)
  | .string value => pure (.string value)
  | .enumeration enum lit => do pure (.enumeration (← enumerationId model enum) (← literalId model lit))
  | .reference object => .reference <$> objectId snapshot object

/-- Observations are mapped occurrence by occurrence, including both ends of an
association. Duplicate observation keys survive for semantic diagnostics. -/
def bindInstance (model : Model) (snapshot : Instance) : BindingResult Snapshot := do
  checkAliases "object" (snapshot.objects.map Object.alias)
  let objects ← snapshot.objects.zipIdx.mapM fun (entry, index) => do
    let classifier ← classId model entry.classifier
    pure ({ id := ⟨index⟩, classifier } : ObjectDecl)
  let observations ← snapshot.observations.mapM fun entry => do
    let object ← objectId snapshot entry.object
    let property ← propertyId model entry.property
    let occurrences ← entry.occurrences.mapM (bindValue model snapshot)
    pure ({ object, property, occurrences } : VLMOF.Observation)
  pure { objects, observations }

/-- The parser feeds this boundary; its result still requires conformance checking. -/
def elaborate (document : Document) : BindingResult (Schema × Snapshot) := do
  let model ← bindModel document.model
  let snapshot ← bindInstance document.model document.snapshot
  pure (model, snapshot)

namespace BindingExamples

example : resolveIndex "class" [["p", "A"], ["p", "B"]] ["p", "B"] = .ok 1 := rfl
example : resolveIndex "class" [["p", "A"], ["p", "A"]] ["p", "A"] =
    .error "ambiguous class alias: p::A" := rfl
example : resolveIndex "class" [["p", "A"]] ["p", "Missing"] =
    .error "unknown class alias: p::Missing" := rfl
example : checkQualification ["p", "A", "x"] (some ["p", "B"]) =
    .error "alias qualification disagrees with owner: p::A::x" := rfl

end BindingExamples
end VLMOF.Source



