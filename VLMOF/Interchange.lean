import Lean.Data.Json
import VLMOF.Core

/-!
The E1 wire format is intentionally a lossless envelope around `Core.Schema` and
`Core.Snapshot`.  It is a boundary adapter, not a second model representation:
declaration and object ids, and each occurrence (including empty observations),
are carried explicitly.  Producers must reject unsupported EMF input before
emitting this format; `provenance` records how an accepted source was obtained.
-/
namespace VLMOF.Interchange

open Lean

def version : String := "vlmof-e1-1"

structure Document where
  schema : Schema
  snapshot : Snapshot
  provenance : Json

private def field (j : Json) (n : String) : Except String Json :=
  j.getObjVal? n |>.mapError fun e => s!"E1 {e} (while reading `{n}`)"
private def nat (j : Json) : Except String Nat := j.getNat?.mapError fun e => s!"E1: {e}"
private def str (j : Json) : Except String String := j.getStr?.mapError fun e => s!"E1: {e}"
private def bool (j : Json) : Except String Bool := j.getBool?.mapError fun e => s!"E1: {e}"
private def arr (j : Json) : Except String (Array Json) := j.getArr?.mapError fun e => s!"E1: {e}"
private def tagged (j : Json) (expected : String) : Except String Unit := do
  if (← str (← field j "tag")) = expected then pure ()
  else throw s!"E1: expected tag `{expected}`"
private def optStr (j : Json) : Except String (Option String) :=
  match j with | .null => pure none | .str s => pure (some s) | _ => throw "E1: string or null expected"

private def upperToJson : Upper → Json
  | .finite n => Json.mkObj [("tag", "finite"), ("value", n)]
  | .unlimited => Json.mkObj [("tag", "unlimited")]
private def upperOfJson (j : Json) : Except String Upper := do
  match ← str (← field j "tag") with
  | "finite" => return .finite (← nat (← field j "value"))
  | "unlimited" => return .unlimited
  | tag => throw s!"E1: unsupported upper tag `{tag}`"

private def typeToJson : ValueType → Json
  | .boolean => Json.mkObj [("tag", "boolean")]
  | .integer => Json.mkObj [("tag", "integer")]
  | .string => Json.mkObj [("tag", "string")]
  | .enumeration i => Json.mkObj [("tag", "enumeration"), ("id", i.val)]
  | .reference i => Json.mkObj [("tag", "reference"), ("id", i.val)]
private def typeOfJson (j : Json) : Except String ValueType := do
  match ← str (← field j "tag") with
  | "boolean" => pure .boolean | "integer" => pure .integer | "string" => pure .string
  | "enumeration" => pure (.enumeration ⟨← nat (← field j "id")⟩)
  | "reference" => pure (.reference ⟨← nat (← field j "id")⟩)
  | tag => throw s!"E1: unsupported value-type `{tag}`"

private def valueToJson : Value → Json
  | .boolean b => Json.mkObj [("tag", "boolean"), ("value", b)]
  | .integer i => Json.mkObj [("tag", "integer"), ("value", i)]
  | .string s => Json.mkObj [("tag", "string"), ("value", s)]
  | .enumeration e l => Json.mkObj [("tag", "enumeration"), ("enumeration", e.val), ("literal", l.val)]
  | .reference o => Json.mkObj [("tag", "reference"), ("object", o.val)]
private def valueOfJson (j : Json) : Except String Value := do
  match ← str (← field j "tag") with
  | "boolean" => pure (.boolean (← bool (← field j "value")))
  | "integer" => pure (.integer (← (← field j "value").getInt?))
  | "string" => pure (.string (← str (← field j "value")))
  | "enumeration" => pure (.enumeration ⟨← nat (← field j "enumeration")⟩ ⟨← nat (← field j "literal")⟩)
  | "reference" => pure (.reference ⟨← nat (← field j "object")⟩)
  | tag => throw s!"E1: unsupported value tag `{tag}`"

private def multiplicityToJson (m : Multiplicity) : Json :=
  Json.mkObj [("lower", m.lower), ("upper", upperToJson m.upper), ("ordered", m.isOrdered), ("unique", m.isUnique)]
private def multiplicityOfJson (j : Json) : Except String Multiplicity :=
  return { lower := ← nat (← field j "lower"), upper := ← upperOfJson (← field j "upper"),
           isOrdered := ← bool (← field j "ordered"), isUnique := ← bool (← field j "unique") }

private def packageToJson (x : PackageDecl) := Json.mkObj [("id", x.id.val), ("name", x.name.map Json.str |>.getD .null), ("parent", x.parent.map (fun p => Json.num p.val) |>.getD .null)]
private def packageOfJson (j : Json) : Except String PackageDecl := do
  let p := ← field j "parent"
  let parent : Option PackageId ← if p.isNull then pure none else pure (some ⟨← nat p⟩)
  return { id := ⟨← nat (← field j "id")⟩, name := ← optStr (← field j "name"), parent }
private def classToJson (x : ClassDecl) := Json.mkObj [("id", x.id.val), ("name", x.name.map Json.str |>.getD .null), ("package", x.package.map (fun p => Json.num p.val) |>.getD .null), ("abstract", x.isAbstract), ("supers", .arr (x.directSupers.toArray.map fun i => i.val))]
private def classOfJson (j : Json) : Except String ClassDecl := do
  let p := ← field j "package"; let a ← arr (← field j "supers")
  let package : Option PackageId ← if p.isNull then pure none else pure (some ⟨← nat p⟩)
  return { id := ⟨← nat (← field j "id")⟩, name := ← optStr (← field j "name"), package, isAbstract := ← bool (← field j "abstract"), directSupers := (← a.toList.mapM fun q => return ⟨← nat q⟩) }
private def propertyToJson (x : PropertyDecl) := Json.mkObj [("id", x.id.val), ("name", x.name.map Json.str |>.getD .null), ("owner", match x.owner with | .class c => Json.mkObj [("tag", "class"), ("id", c.val)] | .association a => Json.mkObj [("tag", "association"), ("id", a.val)]), ("type", typeToJson x.type), ("multiplicity", multiplicityToJson x.multiplicity), ("aggregation", match x.aggregation with | .none => "none" | .composite => "composite"), ("idProperty", x.isId)]
private def propertyOfJson (j : Json) : Except String PropertyDecl := do
  let o := ← field j "owner"; let owner ← match ← str (← field o "tag") with | "class" => pure (.class ⟨← nat (← field o "id")⟩) | "association" => pure (.association ⟨← nat (← field o "id")⟩) | t => throw s!"E1: unsupported owner `{t}`"
  let aggregation ← match ← str (← field j "aggregation") with | "none" => pure .none | "composite" => pure .composite | t => throw s!"E1: unsupported aggregation `{t}`"
  return { id := ⟨← nat (← field j "id")⟩, name := ← optStr (← field j "name"), owner, type := ← typeOfJson (← field j "type"), multiplicity := ← multiplicityOfJson (← field j "multiplicity"), aggregation, isId := ← bool (← field j "idProperty") }
private def associationToJson (x : AssociationDecl) := Json.mkObj [("id", x.id.val), ("name", x.name.map Json.str |>.getD .null), ("package", x.package.map (fun p => Json.num p.val) |>.getD .null), ("ends", .arr #[x.ends.1.val, x.ends.2.val])]
private def associationOfJson (j : Json) : Except String AssociationDecl := do
  let p := ← field j "package"; let e ← arr (← field j "ends")
  if e.size != 2 then throw "E1: association ends must have length 2"
  let package : Option PackageId ← if p.isNull then pure none else pure (some ⟨← nat p⟩)
  return { id := ⟨← nat (← field j "id")⟩, name := ← optStr (← field j "name"), package, ends := (⟨← nat e[0]!⟩, ⟨← nat e[1]!⟩) }
private def enumToJson (x : EnumerationDecl) := Json.mkObj [("id", x.id.val), ("name", x.name.map Json.str |>.getD .null), ("package", x.package.map (fun p => Json.num p.val) |>.getD .null)]
private def enumOfJson (j : Json) : Except String EnumerationDecl := do
  let p := ← field j "package"
  let package : Option PackageId ← if p.isNull then pure none else pure (some ⟨← nat p⟩)
  return { id := ⟨← nat (← field j "id")⟩, name := ← optStr (← field j "name"), package }
private def literalToJson (x : LiteralDecl) := Json.mkObj [("id", x.id.val), ("name", x.name.map Json.str |>.getD .null), ("enumeration", x.enumeration.val)]
private def literalOfJson (j : Json) : Except String LiteralDecl := return { id := ⟨← nat (← field j "id")⟩, name := ← optStr (← field j "name"), enumeration := ⟨← nat (← field j "enumeration")⟩ }

private def listToJson {α : Type} (f : α → Json) (xs : List α) := Json.arr (xs.toArray.map f)
private def listOfJson {α : Type} (f : Json → Except String α) (j : Json) : Except String (List α) := do
  (← arr j).toList.mapM f

def encode (d : Document) : Json := Json.mkObj [("version", version), ("schema", Json.mkObj [("packages", listToJson packageToJson d.schema.packages), ("classes", listToJson classToJson d.schema.classes), ("properties", listToJson propertyToJson d.schema.properties), ("associations", listToJson associationToJson d.schema.associations), ("enumerations", listToJson enumToJson d.schema.enumerations), ("literals", listToJson literalToJson d.schema.literals)]), ("snapshot", Json.mkObj [("objects", listToJson (fun o => Json.mkObj [("id", o.id.val), ("classifier", o.classifier.val)]) d.snapshot.objects), ("observations", listToJson (fun o => Json.mkObj [("object", o.object.val), ("property", o.property.val), ("occurrences", listToJson valueToJson o.occurrences)]) d.snapshot.observations)]), ("provenance", d.provenance)]

def decode (j : Json) : Except String (Schema × Snapshot) := do
  if (← str (← field j "version")) != version then throw s!"E1: unsupported interchange version `{← str (← field j "version")}`"
  let s ← field j "schema"; let i ← field j "snapshot"
  let schema : Schema := { packages := ← listOfJson packageOfJson (← field s "packages"), classes := ← listOfJson classOfJson (← field s "classes"), properties := ← listOfJson propertyOfJson (← field s "properties"), associations := ← listOfJson associationOfJson (← field s "associations"), enumerations := ← listOfJson enumOfJson (← field s "enumerations"), literals := ← listOfJson literalOfJson (← field s "literals") }
  let snapshot : Snapshot := { objects := ← listOfJson (fun o => return { id := ⟨← nat (← field o "id")⟩, classifier := ⟨← nat (← field o "classifier")⟩ }) (← field i "objects"), observations := ← listOfJson (fun o => return { object := ⟨← nat (← field o "object")⟩, property := ⟨← nat (← field o "property")⟩, occurrences := ← listOfJson valueOfJson (← field o "occurrences") }) (← field i "observations") }
  pure (schema, snapshot)

def decodeDocument (j : Json) : Except String Document := do
  let (schema, snapshot) ← decode j
  return { schema, snapshot, provenance := ← field j "provenance" }

end VLMOF.Interchange
