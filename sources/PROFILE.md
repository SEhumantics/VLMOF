# Structural profile and source decisions

The target is a static structural fragment of EMOF 2.5.1. The source manifest
pins the normative MOF PDF, adopted UML 2.5 prose, and dated machine-readable
inputs. This profile describes the contract to implement; the current Lean
entry point does not yet implement it.

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
| Names, type/bounds, composite/opposite creation premises | MOF 9.3.3, p.14 |
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
