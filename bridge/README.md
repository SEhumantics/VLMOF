# E1 EMF bridge

This is a Java/EMF setup for the bounded E1 mapping. It pins Maven
dependencies `org.eclipse.emf.ecore` and `org.eclipse.emf.ecore.xmi` at 2.39.0,
and the transitively required `org.eclipse.emf.common` at 2.42.0.
It uses EMF `ResourceSet` loading for supplied Ecore and XMI manifests, not an XML
replacement parser. The Java adapter is outside Lean's proof boundary. Lean decodes
the emitted `vlmof-e1-1` JSON into the common raw Core, then the separately proved
checker decides schema and snapshot conformance.

## Import and round trip

The command syntax makes package and instance closure explicit:

```sh
mvn -q test-compile exec:java \
  -Dexec.mainClass=org.vlmof.bridge.EmfInterchange \
  -Dexec.args='import /absolute/tiny.ecore [other.ecore ...] -- /absolute/tiny.xmi [other.xmi ...]'
```

It emits a `vlmof-e1-1` document with `schema`, `snapshot`, and `provenance`.
IDs are allocated by the supplied Ecore manifest's containment traversal and the
supplied XMI manifest's containment preorder. Names, locators and `xmi:id` remain
source provenance; they never become Core identities. Every object's applicable
feature has an observation, including an empty occurrence list. Lists are emitted
without deduplication.

`roundtrip` saves each accepted EMF XMI resource and reloads it through a fresh EMF
resource set, then compares the emitted schema and snapshot. Its deterministic IDs
are one permitted identity renaming; the comparison is otherwise occurrence exact.

```sh
mvn -q test-compile exec:java \
  -Dexec.mainClass=org.vlmof.bridge.EmfInterchange \
  -Dexec.args='roundtrip src/main/resources/samples/tiny.ecore -- src/main/resources/samples/tiny.xmi'
```

Only direct Boolean, Integer and String Ecore datatypes and enumerations are mapped.
The importer rejects operations, type parameters or applied generic feature types,
derived/transient/volatile/read-only/unsettable features, default literals and custom
datatypes. An instance default is never silently materialized: any such change must
be a separately named adapted input with an insertion manifest. Schema metadata
defaults are read from EMF's normalized values; this adapter presently records the
normalization policy in `provenance`, rather than claiming XML lexical-presence
evidence. That lexical distinction needs a retained XML-source binding before it can
support a source-fidelity claim.

All packages used by a classifier must appear in the supplied Ecore manifest (nested
packages count through their explicit parent). A proxy or a reference to an object
outside the supplied XMI manifest is rejected. Ecore represents both ends of a
bidirectional association as class-owned references, so this bridge exports paired
references as associations with class-owned ends. Association-owned/non-navigable
ends are outside this Ecore mapping domain and receive a diagnostic rather than an
unsupported claim of representation.

The Lean JSON decoder checks the version and required field shapes. It intentionally
ignores unknown object members for forward-compatible provenance additions. Lean's
JSON parser normalizes duplicate object keys before this decoder runs, so duplicate-key
rejection is an input-parser trust-boundary, not an established E1 guarantee.

Negative fixtures exercise the rejection branch:

```sh
mvn -q test-compile exec:java -Dexec.mainClass=org.vlmof.bridge.EmfInterchange \
  -Dexec.args='import src/main/resources/samples/default-negative.ecore -- src/main/resources/samples/tiny.xmi'
mvn -q test-compile exec:java -Dexec.mainClass=org.vlmof.bridge.EmfInterchange \
  -Dexec.args='import src/main/resources/samples/derived-custom-negative.ecore -- src/main/resources/samples/tiny.xmi'
mvn -q test-compile exec:java -Dexec.mainClass=org.vlmof.bridge.EmfInterchange \
  -Dexec.args='import src/main/resources/samples/broken-reference.ecore -- src/main/resources/samples/broken-reference.xmi'
```

Run the authored-resource loading probe from this directory:

```sh
mvn -q test-compile exec:java
```

It loads `samples/tiny.ecore`, registers that dynamically loaded package, then
loads `samples/tiny.xmi`. The sample asserts all of these observations: ordinary
inheritance exposes `baseCode` on `Child`; ordered non-unique `marks` retains
`[7, 7, 9]`; and the containment/opposite pair is reciprocal. It still does
not decode to Lean.

## Mapping limits

The implemented mapping admits nested packages, non-interface classes and direct
multiple inheritance, direct Boolean/Integer/String/enum attributes, and references
with bounds, order, uniqueness, containment and reciprocal opposites. Inherited
properties retain their one declaration identity; both opposite ends retain their
own observations, including empty and reverse-only incidence. It rejects annotations
as well as operations, generic constructs, derived/transient/volatile/read-only/
unsettable features, defaults, unsupported datatypes, proxies and classifiers outside
the declared package closure before an E1 document is emitted.

The JSON provenance currently records manifest locations and allocation policy. It
does not yet retain input byte digests, Ecore/XMI locators, `xmi:id` lexical status,
feature lexical-default status, occurrence origin, or an adaptation manifest. Those
are required before making a source-fidelity or adaptation claim beyond this bounded
runtime mapping.

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
