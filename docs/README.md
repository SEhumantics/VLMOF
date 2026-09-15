# Reading and using the Lean library

The library separates the meaning of a model from algorithms that check or
translate it. Start with one small mathematical component, then follow the
conformance and translation results. You need not read the parser or Java bridge
to understand the semantic definitions.

## Suggested reading order

1. **Multiplicity:** [Model.Multiplicity](../VLMOF/Model/Multiplicity.lean) explains upper bounds and
   admitted cardinalities. Structural interval consistency and reflective creation's
   positive-upper prerequisite are distinct questions. The [worked explanation](multiplicity.md)
   distinguishes interval feasibility from existence of a conforming model.
2. **Models:** [Model.Basic](../VLMOF/Model/Basic.lean) defines declaration and
   object identities, values and raw records.
   [Model.Semantics](../VLMOF/Model/Semantics.lean) defines schema validity and
   snapshot conformance. Read the fields of `SchemaWellFormed` and
   `SnapshotConforms` before their supporting lookup functions.
3. **Consequences:** [Model.Properties](../VLMOF/Model/Properties.lean) gives
   observation-key injectivity and the interaction between opposite counts and
   an upper-one bound. The example modules supply satisfying and separating cases.
4. **Executable checking:** [Checker.Basic](../VLMOF/Checker/Basic.lean) implements
   those predicates. [Acceptance](../VLMOF/Checker/Correctness/Acceptance.lean)
   states the final equivalences. Its supporting proofs are separated into local
   checks, schema checks, snapshot checks and diagnostics.
5. **Symbolic meaning:** [Source.Syntax](../VLMOF/Source/Syntax.lean) and
   [Source.Semantics](../VLMOF/Source/Semantics.lean) describe qualified names and
   source satisfaction. [Elaboration](../VLMOF/Source/Elaboration.lean) resolves
   names into typed numeric identities. Source meaning is not defined by running
   that elaborator or the checker.
6. **Translation result:** [Source.Adequacy](../VLMOF/Source/Adequacy.lean) is the
   entry point for the source/Core equivalence. Its imports provide binding
   completeness, preservation and reflection. The proof modules explain which
   fields or relations each step transports. Read [representability](representability.md)
   separately: adequacy does not imply that every raw Core record is literally
   produced by the source language.

## Directory responsibilities

| Directory | Contents |
|---|---|
| `VLMOF/Model/` | Raw declarations, multiplicity and conformance predicates; mathematical consequences |
| `VLMOF/Model/Reachability/` | Inheritance, package and containment path arguments |
| `VLMOF/Finite/` | Generic finite-carrier closure and an equivalent early-stopping implementation |
| `VLMOF/Checker/` | Boolean checks and correctness proofs against the declarative predicates |
| `VLMOF/Source/Binding/` | Alias resolution and transport of values, occurrences and applicability |
| `VLMOF/Source/Correctness/` | Allocation, field preservation and reflection of schemas/snapshots |
| `VLMOF/Interchange/` | Tested JSON codec boundary |
| `VLMOF/Metadata/` | Ordinary metadata vocabulary and checked interpretation |
| `VLMOF/Examples/` | Concrete witnesses and separating examples; not foundational definitions |

The directories organize imports; public declaration namespaces remain `VLMOF`
and `VLMOF.Source`. For example, moving a file into `Checker/Correctness/` does
not rename `VLMOF.checkSnapshot_iff`. Import paths have changed, so downstream
clients should import the new modules or the aggregate `VLMOF` entry point.

The default build includes the examples so their claims are checked along with
the library. For a focused proof client, import only the module containing the
result you need. [ProofClient.lean](../experiments/ProofClient.lean) demonstrates
using a conformance consequence without reimplementing the checker. Its
repeated-link edit result quantifies over arbitrary candidate snapshots of the
example metamodel: reciprocity and a reverse upper-one bound exclude a repeated
forward target even though that forward property is nonunique.

## What the proofs establish

Checker correctness is about the represented predicates for all raw inputs.
Source adequacy additionally needs the stated lexical condition because the
Core stores identities rather than source aliases. Standards interpretation is
supported by the [clause audit](../sources/CLAUSE-AUDIT.md); it is not a consequence
of Lean accepting our definitions. Parsing, JSON and the native EMF bridge are
tested code outside that correspondence theorem.

For details, see the [model representation](model.md), [source language](source-language.md),
[metadata pilot](metadata.md), [native bridge](../bridge/README.md) and
[explicit structural profile](../sources/PROFILE.md).

## Actual EMF validation comparison

`EmfInterchange` is a profile-limited interchange adapter; its successful load,
save, or round trip is not EMF validation. The separate
`org.vlmof.bridge.EmfValidationHarness` creates a fresh manifest-closed resource
set and isolated `EValidator` registry, registers `EcoreValidator` for Ecore,
then validates every Ecore and XMI root through `Diagnostician`. Dynamic Ecore
instance packages use the documented `EObjectValidator` fallback. It records the
effective registry and flattened EMF diagnostics as machine-readable JSON.

The full local protocol, state-alignment contract, and reproduction commands are
in [validation.md](validation.md). Run correctness cases into a **new** directory with:

```sh
python3 experiments/run_emf_validation.py --output /absolute/new-results
```

The optional `--measure` mode is only for a quiescent, pinned build. It runs 10
warmups and 30 repetitions by default of the preloaded combined schema plus
instance validation boundary; its retained values are observations, not speed
claims. The runner separately retains bridge normalization and Lean checking,
and refuses to overwrite a previous result directory.
