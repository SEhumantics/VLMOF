# Reading and using the Lean library

The library separates the meaning of a model from algorithms that check or
translate it. Start with one small mathematical component, then follow the
conformance and translation results. You need not read the parser or Java bridge
to understand the semantic definitions.

## Suggested reading order

1. **Multiplicity:** `VLMOF/Model/Multiplicity.lean` explains upper bounds and
   admitted cardinalities. Interval consistency and the selected profile's
   positive-upper rule are distinct questions.
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
using a conformance consequence without reimplementing the checker.

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
