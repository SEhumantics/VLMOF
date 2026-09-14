# Structural profile and source decisions

The target is a static structural fragment of EMOF 2.5.1. The source manifest
pins the normative MOF PDF, adopted UML 2.5 prose, and dated machine-readable
inputs. The Lean predicates implement the selected contract below; source fidelity
is supported by the clause audit, separately from the proofs about those predicates.

## Representation contract

Keep package, class, property, association, enumeration/literal, and runtime
object identities distinct. Spelling is metadata: the source language binds
names to identities, while semantic access uses identities. Multiple inheritance
exposes the union of property declaration identities, so a diamond does not
copy one inherited property. Same-named declarations remain distinct.

Represent finite nested packages, abstract/concrete classes and generalization,
properties, binary associations including a possible nonnavigable association-
owned end, Boolean/Integer/String/enumeration values, finite occurrence lists,
normalized multiplicities, ordering, uniqueness, opposites and containment.
A missing optional value is an empty observation, independently of false, zero
or an empty string. Null is not a value inside a multivalued reference.

Store enough information for every association end's observations, even where
an end is not navigable. Opposite is the other member of a binary association;
end membership, ownership and cross-typing must agree. A nonnavigable end's
observation is mathematical incidence data, not an advertised reflective slot.

Ordered observations compare as sequences. Unordered observations compare up
to permutation; occurrence count remains observable. Schema validity and
snapshot validity are separate predicates. Malformed records may be represented
for diagnostic testing; their representability must not imply acceptance.

## Selected static interpretation

- Use nonnegative lower bounds and positive finite upper bounds or unlimited,
  with lower <= upper, for a normalized creation-valid schema profile.
- `isUnique` controls equal-value duplication for both references and data.
  Multiplicity counts occurrences. Reference equality is object identity;
  primitive equality is value equality; literals retain their enumeration.
- Paired association ends have matching opposite occurrence counts. This
  prevents membership-only checking from losing a repeated relationship.
- Each child has at most one incoming composite occurrence, globally, and
  containment is acyclic. This also rules out two different composite features
  from the same parent. Opposite container ends have upper bound one.
- Count `isID` attributes over inherited declaration identities. Do not infer
  globally unique ID values or an identifier/URI service from that count.

These are explicit static interpretation choices. MOF 10.6's indexed sequence
insertion prose forbids duplicate Class references even though other collection
text makes uniqueness conditional on isUnique. It directly describes an ordered
reflective operation and does not settle raw snapshot validity or unordered
reference behavior. This profile admits raw non-unique occurrences and makes
no claim that every admitted snapshot is reachable through that API.

Occurrence-sensitive opposite matching and containment are coherent together:
repeated links consume multiplicity at both ends, including an upper-one
container end. They are stronger than a relationship-only abstraction. CMOF
13.2's repeatable Link rationale and optional Clause 15 corroborate this reading;
neither is silently imposed as a mandatory EMOF capability. This interpretation
must be named in any theorem's claimed standards correspondence.

## Boundary

Deferred legal EMOF features include operations/parameters, general structured
datatypes, Real and remaining value domains, defaults/unset histories,
derived/read-only behavior, comments/tags, and generic reflection. Fixed derived
facts used above (opposite, isComposite) still require consistent definitions.
The bounded metadata pilot will not establish full EMOF self-description.
General UML, CMOF and OCL-language formalization are outside the target.

Reject or diagnose unsupported imported constructs before decoding; do not erase
them and claim the original input was supported. An expressly named adaptation
may produce a separate supported input with provenance and every change recorded.
Original specification bytes remain unchanged. Published package merges describe
source assembly, not a requested user-language feature.

## Primary source map

Printed pages, not PDF page indices:

| Area | Source |
|---|---|
| EMOF scope, assembly, adopted UML | MOF 12.1-12.3, pp.25-28, Figures 12.1-12.5 |
| All fixed EMOF restrictions | MOF 12.4[1]-[32], pp.29-31 |
| Names, absence, static opposite/containment consequences | MOF 12.5, pp.31-32 |
| Names, type/bounds, composite/opposite creation premises | MOF 9.3.3, pp.13-14 |
| Identity/value equality and property access | MOF 9.4.1, pp.15-16 |
| Extent identity and URI capabilities | MOF 10.1-10.3, pp.17-19 |
| Collection and sequence behavior | MOF 10.5-10.6, pp.20-21 |
| Generalization/inherited properties | UML 2.5 9.9.4, pp.130-134, especially allParents/allAttributes and no_cycles |
| Binary member ends and ownership | MOF 12.4[9,12,30]; UML.xmi Property-type_of_opposite_end and Property-opposite |
| At most one inherited ID attribute | MOF 12.4[7,15]; EMOFConstraints.ocl inherited closure/asSet |

The auxiliary OCL has historical/editorial discrepancies (including the
PrimitiveType default rule testing Enumeration, and mislabeled constraint
numbers). Compare it with the printed rule before translating it. Fixed
mathematical predicates require total resolved navigation premises rather than
silently changing OCL null/invalid behavior. The dated UML.xmi contains 40
repeated xmi:id occurrences across seven package-import identifiers; preserve
nodes/provenance and diagnose collisions instead of overwriting an ID map.

## Primitive value boundary

MOF 12.4[5] adopts [XSD 1.0 Datatypes, second edition](https://www.w3.org/TR/2004/REC-xmlschema-2-20041028/),
sections 3.2.1, 3.2.2 and 3.3.13. Bool and arbitrary Int represent the selected
Boolean and Integer values. String values must contain only characters allowed
by [XML 1.0 second edition, production Char](https://www.w3.org/TR/2000/REC-xml-20001006#charsets):
tab, LF, CR, U+0020-D7FF, E000-FFFD, or 10000-10FFFF. An unconstrained host
String is useful for representing malformed inputs, but is not automatically
a valid XSD string. Empty string is valid; no case folding or Unicode
normalization is implicit. Source-language lexical choices are separate from
these value-space restrictions.

## Boundaries confirmed during semantic review

The positive-upper restriction above follows MOF 9.3.3[4]-[5], printed page 13:
the prerequisites for instantiating a Class include lower <= upper and upper >= 1
for all its Properties, including inherited Properties. General UML abstract syntax
can represent 0..0; this profile selects creation-valid declarations and does not
claim every structurally valid UML multiplicity.

Occurrence-sensitive lists preserve repeated endpoint values, and reference equality
uses ObjectId. They provide no first-class Link IDs or cross-end identity for two
equal repeated occurrences. Ordering is an observation of the retained list; unordered
observation equivalence is permutation. Optional MOF clause 15.3.3 opposite-end
isUnique compatibility is not selected, so opposite ends may have different uniqueness
flags; reciprocity and each end's own bounds and uniqueness still constrain snapshots.

## Root ownership convention

A whole Schema/Model supplies an implicit outer Package scope. An omitted explicit
package on a Class, Enumeration or Association denotes ownership by that scope,
not an ownerless declaration. Root explicit packages are also inside that scope.
The scope has a fresh identity, fixed nonempty display name `Model`, and no source
alias or stored package ID. This reconciles top-level DSL declarations with adopted
UML `Element::has_owner`; it does not permit nested classifiers. The exact encoding
and the excluded reflective/root-materialization claims are in
[REPRESENTATION.md](../VLMOF/REPRESENTATION.md).

The occurrence-based incoming-composite bound is also deliberately stronger than
counting distinct `(parent, property)` containers. For an unpaired nonunique
composite feature, one parent and one slot containing the same child twice is
rejected by this profile even though a distinct-container reading admits it.
We do not claim that the standard requires this stronger restriction; it selects
the occurrence-sensitive snapshot domain formalized here. If an opposite upper-one
container end exists, pair-count reciprocity already rules out that repetition.
