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

`export` takes an E1 JSON document and creates a **new** dynamic Ecore package and
new XMI objects; it does not retain or re-save the input resource. Object IDs choose
the temporary construction objects, and Ecore assigns its own XMI identities.

```sh
mvn -q exec:java -Dexec.mainClass=org.vlmof.bridge.EmfInterchange \
  -Dexec.args='export /tmp/e1-input.json /tmp/e1-export.ecore /tmp/e1-export.xmi'
mvn -q exec:java -Dexec.mainClass=org.vlmof.bridge.EmfInterchange \
  -Dexec.args='import /tmp/e1-export.ecore -- /tmp/e1-export.xmi' > /tmp/e1-reloaded.json
mvn -q exec:java -Dexec.mainClass=org.vlmof.bridge.EmfInterchange \
  -Dexec.args='compare /tmp/e1-input.json /tmp/e1-reloaded.json /tmp/e1-export.xmi.ids.json'
```

It reconstructs packages, enums/literals, classes/supertypes, attributes and
class-owned references, then allocates all objects before assigning every occurrence.
Association membership is restored by pairing two class-owned reference ends. An
association-owned end, non-reference association endpoint, dangling identifier,
multiple root package, or a value incompatible with the constructed Ecore feature is
rejected with an `E1 export` or `REJECT` diagnostic.

`compare` checks packages/classes/properties/associations/enums/literals, object
classifiers, observation domains and occurrence values. It uses sequence equality
for ordered features and sorted occurrence multisets for unordered ones. JSON member
order is ignored, and duplicate object or observation identities are rejected.
The exporter accepts distinct nonnegative IDs within Java's integer range. It writes
an `out.xmi.ids.json` sidecar recording each source ID and generated native URI.
The importer records reloaded IDs and native URIs in provenance. Supplying that
sidecar to `compare` constructs a bijection, rejects missing/duplicate/extra identities,
and remaps all foreign IDs before comparison. Names are not used to guess matches.
Without the optional sidecar, comparison requires identical numeric IDs. Native URI
identities are location dependent; relocating exported resources requires a separately
justified correspondence. These producer records are not cryptographic attestations.

Run the boundary regression from `bridge/`:

```sh
python3 scripts/e1_export_regression.py
```

It creates a Core JSON document with explicit `false`, `0`, empty String and first
enum values beside a second object whose corresponding features are empty. It also
uses repeated scalar occurrences and repeated paired references. The test exports
fresh resources, reimports them, compares observations, and asserts the separating
values directly. Other cases exercise independent ordering at an inverse end,
arbitrary IDs with changed object traversal order, and duplicate-map rejection.
Inconsistent inverse counts are rejected before either output is written, and
duplicate observation keys are rejected by comparison.

Repeated paired reference occurrences survive export and reimport. Both Ecore
opposite pointers are set explicitly; setting only one pointer produces asymmetric
metadata and can duplicate occurrences during reload. The regression checks the
complete reciprocal case, alongside independent ordering at the inverse end.

The exporter constructs opposite membership once, checks every supplied occurrence
list, and reorders each ordered end independently. It does not repair inconsistent
inverse observations into an accepted snapshot. It buffers both resources before
writing so representation errors do not leave a partially generated Ecore file.

Only direct Boolean, Integer and String Ecore datatypes and enumerations are mapped.
The importer rejects operations, type parameters or applied generic feature types,
derived/transient/volatile/read-only/unsettable features, default literals and custom
datatypes. An instance default is never silently materialized: any such change must
be a separately named adapted input with an insertion manifest. Schema metadata
defaults are read from EMF's normalized values; this adapter presently records the
normalization policy in `provenance`, rather than claiming XML lexical-presence
evidence. That lexical distinction needs a retained XML-source binding before it can
support a source-fidelity claim.

EMF's ordinary `eIsSet` cannot distinguish an omitted optional scalar from an XMI
scalar explicitly written with its default (`false`, `0`, empty string, or the first
enum literal). For file-backed XMI, the importer pairs original XML elements with
the EMF containment preorder and retains lexical attribute presence, so an explicit
default is emitted while an omission stays empty. A wrapper/XML shape that cannot be
paired is rejected as `lexical-presence-unmappable`; non-file resources are rejected
as lexical-presence unavailable. Unsettable features remain outside this profile.

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

## Public Train reproduction and adaptation

The public sources are pinned to Train Benchmark
`6490047d7449f9a4b66cec032b9377bfc06a54d2` (EPL-1.0) and EMF Compare
`9f25a964c1be423373587d8063a5b132714ebeae` (EPL-1.0). Obtain separate checkouts:

```sh
git clone https://github.com/FTSRG/trainbenchmark.git /absolute/trainbenchmark
git -C /absolute/trainbenchmark checkout --detach 6490047d7449f9a4b66cec032b9377bfc06a54d2
git clone https://github.com/eclipse-emf-compare/emf-compare.git /absolute/emf-compare
git -C /absolute/emf-compare checkout --detach 9f25a964c1be423373587d8063a5b132714ebeae
```

From the repository root after building the Lean executable, run:

```sh
bash bridge/scripts/run_train_e1.sh /absolute/trainbenchmark /absolute/new-train-results
bash bridge/scripts/run_train_roundtrip_review.sh /absolute/new-train-results
```

The output directory must be new. The first script checks the Train revision,
compiles the pinned Xcore with the configured Maven Xcore dependency, performs
explicit metamodel and instance adaptations, imports all six snapshots and runs
`check-json`. The second constructs fresh Ecore/XMI resources, reloads them,
compares through each generated native identity sidecar, and rechecks the Core.
`CHECKER` can select an explicit executable; `BRIDGE` can select another built
bridge directory. The integrated run accepted all six adapted snapshots and all
six reloaded snapshots, with all six comparisons passing. These are compatibility
observations, not a proved serializer or a whole-Ecore conformance claim.

The generated Ecore contains a generator annotation and maps three source
primitives to EJavaObject. `StripEcoreAnnotations` creates a separate profile Ecore,
requires exactly one annotation removal, and maps `RailwayElement.id` and
`Segment.length` to EInt and `Route.active` to EBoolean. Its JSON manifest records
the qualified changes, original annotation details, Xcore source basis and
input/output/Xcore hashes. The unadapted generated Ecore is rejected for annotation.

`adapt_train_defaults.py` records every inserted `FAILURE` enum occurrence in a
separate XMI and SHA-256 manifest. The six insertion counts are 12, 58, 21, 76, 31
and 58 for batch-1, batch-2, inject-1, inject-2, repair-1 and repair-2. The batch-1
control with raw XMI and the profile Ecore is also Core accepted: the six absent
`position` and six absent `currentPosition` observations have lower bound zero.
Materialization makes the intended runtime default values explicit; it is a
meaning adaptation, not a necessary repair for structural acceptance. Originals
are not changed. Neither acceptance result proves fidelity to reflective default
semantics of the raw source.

Run the behavioral negative suite from `bridge/`:

```sh
mvn -q test-compile
python3 scripts/e1_import_negative_regression.py --emf-compare /absolute/emf-compare/plugins/org.eclipse.emf.compare/model/compare.ecore
```

It includes standalone datatype, default, derived, generic and broken-reference
rejections. An EMF-generated cross-resource fixture rejects an omitted external
Ecore and succeeds when both Ecore files are explicitly listed. EMF Compare is
rejected for operations; omission of `--emf-compare` reports that case as not run.

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

The JSON provenance records manifest locations, allocation policy and native URI
identities. It does not yet retain input byte digests, `xmi:id` lexical status,
feature lexical-default status, occurrence origin, or an adaptation manifest. Those
are required before making a source-fidelity or adaptation claim beyond this bounded
runtime mapping.

The inventory command is a rejection preflight, not a complete EMOF validator.
Using the pinned checkout above, run:

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
from the package currently inspected. The importer rejects unsupported constructs before emitting Core JSON; this
inventory utility is evidence that the pinned
EMF Compare model has rejection-triggering features, not the whole diagnostic
contract.

The positive inheritance fixture is `samples/tiny.ecore`. Run the genuine
generic negative fixture with the same inventory command and
`samples/generic-negative.ecore`; it reports its type parameter and applied
type argument. Ordinary `eSuperTypes` are represented internally by EMF as
generic-type records with no type arguments, and are accepted by this preflight.
