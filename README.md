# VL-MOF

VL-MOF is a Lean library for a structural fragment of EMOF. It defines when a
schema is well formed and when a finite object snapshot conforms to it, proves
consequences of those definitions, and provides an executable conformance checker.
A symbolic model language and a limited EMF bridge make those definitions usable
with authored models and native resources.

Start with the [library reading guide](docs/README.md). It explains the module
structure and the route from multiplicity and model definitions to checker
correctness and source-language adequacy. The [source audit](sources/CLAUSE-AUDIT.md)
and [profile](sources/PROFILE.md) state the standards interpretation and omissions.

## Build and try a model

Use Linux or WSL with Python 3.10+, GNU Make and Lean installed through elan.
The toolchain file pins Lean 4.33.1. The Lean library has no external dependencies;
the acquisition and authored-case scripts use Python's standard library.

```sh
make sources
make check
lake exe vlmof check-dsl examples/simple.dsl
lake exe vlmof check-json examples/simple.json
```

`make sources` fetches six pinned OMG inputs and checks their hashes. `make check`
verifies those files offline, runs the acquisition tests, builds the library and
examples, and runs CLI tests. Downloaded sources are ignored by Git; the originals
are never rewritten. `make text` creates searchable PDF text when Poppler is installed.

The CLI emits a JSON report. Accepted inputs exit with 0; invalid represented
models with 1; malformed input or usage with 2; unsupported wire versions with 3;
and file errors with 4. DSL parsing and binding failures are reported separately
from conformance failures. See the [source-language guide](docs/source-language.md)
for syntax and examples.

## What to read next

- [Model representation](docs/model.md): identities, values, observations and
  malformed raw states.
- [Library guide](docs/README.md): semantic definitions, proof responsibilities,
  suggested reading order and focused imports.
- [Representability](docs/representability.md): what the source language can
  denote, and the premises of the proved reification results.
- [Metadata pilot](docs/metadata.md): descriptions treated as ordinary objects,
  with a separate check of the interpreted schema.
- [EMF bridge](bridge/README.md): Java requirements, supported native features,
  identity correspondence and import/export regression commands.
- [Authored experiments](experiments/README.md) and
  [public experiments](experiments/README-public.md): repeatable runs with input
  provenance, named adaptations and distinct outcome classifications.

Checker acceptance is proved equivalent to the declarative predicate on raw
represented inputs. Source adequacy connects independent symbolic satisfaction
to actual elaboration and acceptance under its explicit lexical premise. The
parser, JSON codec and Java/XML bridge are tested interfaces outside that theorem.
The source audit supports the selected EMOF interpretation; the theorem does not
establish standards fidelity merely by checking our definitions.

## Manuscript and development

Run `make -C paper` to build `paper/build/main.pdf`.
[Paper build instructions](paper/README.md) describe dependencies and formatting.
The manuscript and code are being revised following Review 3. No fourth review
or submission-readiness claim is implied by a successful build.

Keep mathematical definitions, their explanations and useful consequences together.
Use the existing semantic layers for new modules, put fixtures under `Examples/`,
and document the material assumptions and proof ideas. See [AGENTS.md](AGENTS.md)
for the repository's working conventions.
