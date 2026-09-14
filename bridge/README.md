# E1 runtime probe

This is a deliberately small Java/EMF setup for E1 mapping work. It pins Maven
dependencies `org.eclipse.emf.ecore` and `org.eclipse.emf.ecore.xmi` at 2.39.0,
and the transitively required `org.eclipse.emf.common` at 2.42.0.
It is **not** an importer, decoder, Core conformance check, exporter, round trip,
or claim of XML/Java verification.

Run the authored-resource loading probe from this directory:

```sh
mvn -q test-compile exec:java
```

It loads `samples/tiny.ecore`, registers that dynamically loaded package, then
loads `samples/tiny.xmi`. The sample asserts all of these observations: ordinary
inheritance exposes `baseCode` on `Child`; ordered non-unique `marks` retains
`[7, 7, 9]`; and the containment/opposite pair is reciprocal. It still does
not decode to Lean.

## Durable v0 adapter boundary

The future adapter maps nested packages, non-interface classes and direct
multiple inheritance, direct Boolean/Integer/String/enum attributes, and
references with bounds/order/uniqueness, containment, and reciprocal opposites.
It allocates Core declaration IDs by manifest-ordered Ecore containment traversal
and `ObjectId`s by manifest-ordered XMI containment preorder. Names, Ecore/XMI
locators, `xmi:id` status, and the explicit EObject-to-object-ID map are
provenance, never substitute identities. Inherited properties retain their one
declaration ID; both opposite ends produce occurrence observations, including
empty and reverse-only incidences.

Reject operations, annotations, generic types, derived/transient/volatile/
read-only/unsettable features, default values, unsupported/custom datatypes,
proxies, and unresolved classifiers before a future decoder runs. Schema
metadata implicit defaults (`lowerBound`, `upperBound`, `ordered`, `unique`)
may only be used through a named normalization record that retains lexical versus
implicit source status. Instance-default materialization is a separate adapted
input with original digest and an insertion manifest; it is not direct import.
The future versioned interchange therefore needs input digests, allocation
algorithm, source bindings, feature/default provenance, object/containment
bindings, occurrence origin, adaptations, and phase-tagged diagnostics.

The inventory command is a rejection preflight, not a complete EMOF validator.
After using the retained S3 fetch command, run:

```sh
mvn -q test-compile exec:java \
  -Dexec.mainClass=org.vlmof.bridge.EcoreProfileInventory \
  -Dexec.args=/absolute/public-cases/emf-compare/plugins/org.eclipse.emf.compare/model/compare.ecore
```

It reports operations, derived/transient/volatile/read-only features, generic
constructs, custom data types, and external reference classifiers. The latter
is an `OBSERVE`, rather than a rejection: an adapter decides support only after
checking the complete explicit package manifest. This avoids calling a type in
another explicitly loaded/nested package unsupported merely because it differs
from the package currently inspected. A future adapter must report every
unsupported construct before decode; this utility is evidence that the pinned
EMF Compare model has rejection-triggering features, not the whole diagnostic
contract.

The positive inheritance fixture is `samples/tiny.ecore`. Run the genuine
generic negative fixture with the same inventory command and
`samples/generic-negative.ecore`; it reports its type parameter and applied
type argument. Ordinary `eSuperTypes` are represented internally by EMF as
generic-type records with no type arguments, and are accepted by this preflight.
