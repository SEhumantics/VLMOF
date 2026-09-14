# E1 runtime probe

This is a deliberately small Java/EMF setup for E1 mapping work.  It pins Maven
dependencies `org.eclipse.emf.ecore` and `org.eclipse.emf.ecore.xmi` at 2.39.0.
It is **not** an importer, decoder, Core conformance check, exporter, round trip,
or claim of XML/Java verification.

Run the authored-resource loading probe from this directory:

```sh
mvn -q test-compile exec:java
```

It loads `samples/tiny.ecore`, registers that dynamically loaded package, then
loads `samples/tiny.xmi`.  The sample has a containment/opposite pair and an
ordered, non-unique integer feature (`marks="7 7 9"`) so EMF resource loading
does not erase the intended feature shapes before a future adapter sees them.

The inventory command is a rejection preflight, not a complete EMOF validator.
After using the retained S3 fetch command, run:

```sh
mvn -q test-compile exec:java \
  -Dexec.mainClass=org.vlmof.bridge.EcoreProfileInventory \
  -Dexec.args=/absolute/public-cases/emf-compare/plugins/org.eclipse.emf.compare/model/compare.ecore
```

It reports operations, derived/transient/volatile/read-only features, generic
constructs, custom data types, and external reference classifiers.  A future
adapter must report every unsupported construct before decode; this utility is
evidence that the pinned EMF Compare model has rejection-triggering features,
not the whole diagnostic contract.
