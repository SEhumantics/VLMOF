# Representation boundary

`VLMOF.Core` is a finite raw-state representation for the structural profile in
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

The examples in `Core.lean` cover multiple inheritance, a shared diamond feature,
two same-named feature declarations, an association-owned end, repeated links, optional
absence, permutation-sensitive observations, and representable malformed input. A small
metadata schema and snapshot additionally represent the `Person` class as an ordinary
object with an ordinary String-valued `name` observation. They use no special metadata
constructors or access path and establish no M1 conformance or self-description theorem.

Primary interpretation locators are MOF 2.5.1 9.3.3, 9.4.1, 10.5-10.6, 12.4, and
12.5 (printed pages 14-21 and 29-32), plus UML 2.5 9.9.4 (printed pages 130-134) and
the pinned `UML.xmi` definitions of Package, Class, Property, Association, Enumeration,
EnumerationLiteral, and MultiplicityElement. The occurrence-sensitive raw-state choice
is the accepted profile interpretation recorded in `sources/PROFILE.md`; it does not
claim that every raw state is reachable through reflective mutation operations.
