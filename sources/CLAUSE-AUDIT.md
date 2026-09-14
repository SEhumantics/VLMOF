# Clause 12.4 disposition for the structural profile

This ledger records the selected interpretation of all 32 EMOF restrictions in
MOF 2.5.1, printed pp. 29–31. The normative PDF and adopted UML dependency are
pinned in [manifest.json](manifest.json). It is a source-audit argument, not a
machine-checked theorem about the prose. [PROFILE.md](PROFILE.md) explains the
cross-clause choices and their limits. `SchemaWellFormed` and `SnapshotConforms`
are defined in [Semantics.lean](../VLMOF/Semantics.lean).

“Fixed” means the selected constructors exclude the alternative; it is not a
claim to recognize arbitrary UML/XMI files. “Deferred” means legal EMOF behavior
or syntax outside this fragment. Native Ecore import has a separately documented,
narrower domain and rejects unsupported constructs rather than erasing them.

| Item | Source obligation | Current disposition / evidence |
|---|---|---|
| 1 | Raised exceptions are Classes. | Deferred: operations and exceptions absent. |
| 2 | Notation distinguishes bidirectional/non-navigable associations. | Explicit binary ends and ownership in AST/Core; no implicit opposite inferred from spelling. Surface DSL is documented separately. |
| 3 | Represented NamedElements require names. | `SchemaWellFormed.names`: `some` nonempty XML-valid names for all six declaration kinds. Raw `none` is representable but rejected. |
| 4 | Public visibility; no ElementImport aliases. | Fixed public form; visibility/import constructs absent. Source binding aliases are authoring keys, not UML ElementImport aliases. |
| 5 | Selected primitives follow XML Schema values. | Bool, arbitrary Int, XML-valid String; `xmlChar`/`validString`. Other primitive domains deferred. |
| 6 | Clause 15 is optional for EMOF. | Not adopted as a mandatory capability; optional rationale is distinguished from normative premises. |
| 7 | At most one `isID` Property of a Class. | `inheritedIdCount`, read with item 15 and inherited declaration identity. No global uniqueness of runtime ID values inferred. |
| 8 | Only listed concrete Kernel metaclasses. | Closed constructors select packages/classes/properties/associations/enums/literals and value forms; remaining listed metaclasses deferred. |
| 9 | Listed properties empty, including nested classifiers, datatype inheritance, redefinition/subsetting and navigableOwnedEnd. | Fixed by constructors. Nested packages are distinct from nested classifiers. Operations/parameters deferred. |
| 10 | Selected derived/final/static/union/leaf flags false. | Fixed static declaration form; richer behavior absent. Auxiliary OCL's extra query flag is not added as normative item 10. |
| 11 | Generalization substitutable. | Subtype/applicability relation follows every stored super edge; resolution and acyclicity checked. UML allParents/no_cycles supplies the latter obligations. |
| 12 | Two member ends, no navigableOwnedEnd, at most one ownedEnd. | `associationEnds`: distinct reference ends, ownership and cross-typing, at most one association-owned end. Such an end denotes nonnavigable incidence. |
| 13 | At most one return parameter; no ParameterSet. | Deferred: parameters absent. |
| 14 | Comments annotate NamedElements only. | Deferred: comments absent. |
| 15 | At most one member `isID` attribute. | `inheritedIdCount` counts distinct applicable property declarations, including inheritance; diamonds do not copy declarations. |
| 16 | Aggregation none or composite. | Two-constructor `Aggregation`; no contradictory independent composite flag. |
| 17 | Enumerations have no attributes/operations. | Fixed enumeration/literal records; property owners cannot be enumerations. |
| 18 | Behavioral concurrency sequential. | Deferred: behavioral features absent. |
| 19 | Classes not active. | Fixed structural class form; no active-class behavior. |
| 20 | EnumerationLiteral has no ValueSpecification. | Fixed identified literal declaration without attached value specification. |
| 21 | Parameters lack effect/exception/stream traits. | Deferred: parameters absent. |
| 22 | TypedElement cannot have Association type. | `ValueType` permits primitive, enum or class reference, never association. |
| 23 | Represented TypedElements require a type. | Mandatory property type and `propertyTypesResolved`. Missing/unresolved aliases fail binding. |
| 24 | Class-typed properties/parameters have no default. | Defaults excluded; native declared defaults rejected. |
| 25 | Enum default, if any, is InstanceValue. | Default behavior deferred; no default silently erased by native import. |
| 26 | Primitive default, if any, is LiteralSpecification. | Default behavior deferred. Auxiliary OCL incorrectly selects Enumeration; prose controls this disposition. |
| 27 | Restriction on mandatory composite subsetting. | Vacuous in selected EMOF domain: item 9 excludes subsetting. |
| 28 | DataType-valued properties have aggregation none. | `compositeReferences` excludes primitive/enum composites. |
| 29 | DataType-owned properties have DataType values. | General structured datatypes deferred; enum properties already excluded. |
| 30 | Association member ends Class-typed. | `associationEnds` requires reference types at both ends. |
| 31 | Multivalued properties/parameters lack defaults. | Defaults excluded and rejected at native boundary. |
| 32 | Bound literal kinds Integer / UnlimitedNatural. | Core uses normalized natural lower and finite-natural/unlimited upper constructors. Creation-valid bounds additionally follow MOF 9.3.3[4–5], p. 13. Native raw literal-kind fidelity is an adapter obligation. |

The static semantics additionally uses MOF 12.5 identity/absence/opposite/container
consequences, MOF 9.4 and 10.5–10.6 equality/collection discussion, and adopted
UML classifier inheritance. It does not implement update atomicity or prove
reachability through reflective APIs. Repeated nonunique raw occurrences count
at both opposite ends and in incoming composition; optional clause 15 uniqueness
compatibility is not imposed. The whole-EMOF self-description claim is deferred.

The machine-readable auxiliaries retain historical discrepancies and repeated
XML identifiers. They do not override the prose and are never rewritten by
source acquisition. Mathematical predicates use resolved finite navigation;
this development does not translate general OCL null/invalid semantics.
