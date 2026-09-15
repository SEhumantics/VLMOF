# Representation boundary

`VLMOF.Model.Basic` is a finite raw-state representation for the structural profile in
`sources/PROFILE.md`. It is deliberately broader than the valid fragment: lists retain
duplicate identifiers and records may contain dangling references, cycles, invalid
bounds, or inconsistent ownership. Later schema and snapshot predicates must diagnose
those states. Constructing a value here proves neither conformance nor full EMOF support.

Every declaration kind and runtime object has a distinct identifier type. A declaration's
optional `name` is metadata, not its identity. Source-language binding is a separate
elaboration concern. Thus one root property reached along both sides of a diamond keeps
one `PropertyId`, while independently declared same-named properties keep two identities.

Property ownership, property type, and association end membership occupy separate fields.
An association structurally has two end identifiers, and its opposite candidates are
derived from that membership rather than stored as arbitrary pointers. A nonnavigable,
association-owned end is represented. Its applicable source class can be derived from
the other end's reference type; its occurrences are mathematical incidence observations,
not an advertised reflective slot.

Snapshots use one observation store keyed by `(ObjectId, PropertyId)` for ordinary
features and all association ends. This prevents class-owned end observations from
disagreeing with a separate link store. Each value list retains occurrences, including
repeated primitive values and repeated object links. Ordered features compare lists;
unordered features compare them by permutation, preserving multiplicity. `isUnique`
is a later validity condition and never normalizes raw input. Empty occurrence lists
express absence independently of Boolean false, integer zero, and the empty string;
there is no null `Value`.

Host `Int` supplies mathematical integers. Host strings are raw input and can contain
characters outside the selected XML Schema string value space; later validity/import
checks must diagnose them. Enumeration values retain both enumeration and literal
identity, and references retain object identity.

The examples in [Examples.Model](../VLMOF/Examples/Model.lean) cover multiple inheritance, a shared diamond feature,
two same-named feature declarations, an association-owned end, repeated links, optional
absence, permutation-sensitive observations, and representable malformed input. A small
metadata schema and snapshot additionally represent the `Person` class as an ordinary
object with an ordinary String-valued `name` observation. They use no special metadata
constructors or access path; these raw examples alone establish no conformance.
The separate [metadata pilot](metadata.md) proves its bounded common-checker results.

Primary interpretation locators are MOF 2.5.1 9.3.3, 9.4.1, 10.5-10.6, 12.4, and
12.5 (printed pages 13-21 and 29-32), plus UML 2.5 9.9.4 (printed pages 130-134) and
the pinned `UML.xmi` definitions of Package, Class, Property, Association, Enumeration,
EnumerationLiteral, and MultiplicityElement. The occurrence-sensitive raw-state choice
is the accepted profile interpretation recorded in `sources/PROFILE.md`; it does not
claim that every raw state is reachable through reflective mutation operations.

## Implicit outer package scope

A `Schema` (and a source `Model`) denotes one implicit outer package scope.
`ClassDecl.package = none`, the corresponding enumeration/association fields,
and a root explicit package's `parent = none` mean ownership by that outer scope.
They do not denote ownerless Classes, Enumerations or Associations. This convention
reconciles root-level authoring with the adopted UML `Element::has_owner` rule and
EMOF's prohibition on nested classifiers: a top-level Class is package-owned,
never class-owned. For example, `class C {}` has the outer scope as its owner.

The outer scope is interpreted as a Package with a fresh identity distinct from
all explicit `PackageId`s and fixed nonempty display name `Model`. It has no source
binding alias and no stored `PackageDecl`. Display-name collisions are harmless
because names are not identities. A missing explicit package reference is the
compact encoding of that one scope. Package reachability theorems concern the
stored explicit package IDs; the implicit scope cannot be used as a query endpoint.
No reflective owner/package API or theorem about materializing this scope into a
complete EMOF object graph is claimed.

This is a representation convention, not an exemption from ownership in the
standard. The native Ecore exporter currently requires explicit package records;
it does not synthesize this outer scope. That narrower native domain is documented
separately. A future bridge that materializes the scope must give its own fresh
identity/name mapping and preservation argument.

## Container objects and container properties

MOF 2.5.1 12.5.5 imposes both one-container-object and one-non-null-container-property
rules. `SingleContainer` therefore compares the parent identities in incoming
composite observations. `SingleContainerProperty` separately compares nonempty
opposite container-end identities. Same parent values cannot merge distinct roles.
The existing opposite upper-one and acyclicity constraints remain in force.

The conformance examples provide four separating models:

- One unpaired nonunique slot containing the child twice conforms; its multiplicity
  is two but it has one parent.
- Two distinct parents fail ownership, even with no opposite properties.
- Two unpaired forward slots from the same parent conform; no reverse role is
  silently invented for either. This is broader than EMF's containment-feature policy.
- Two paired composite slots from the same parent fail because their two reverse
  container properties are both active, although the container object is unique.

`incomingCompositeCount` retains the old occurrence arithmetic for comparison, but
`SnapshotConforms.oneIncomingComposite` now contains the conjunction of the two
identity-based obligations. Clients must use its two components; the old field name
is retained for migration, not as a claim that ownership counts occurrences.
