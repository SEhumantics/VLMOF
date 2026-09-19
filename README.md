# VL-MOF

VL-MOF is a Lean library for a structural fragment of EMOF. It defines when a
schema is well formed and when a finite object snapshot conforms to it, proves
consequences of those definitions, and provides an executable conformance checker.
A symbolic model language and a limited EMF bridge make those definitions usable
with authored models and native resources.

## Start here

The paper, *Formalizing Structural EMOF in Lean for Metamodeling*, is built from
[`paper/`](paper/) into `paper/build/main.pdf` by `make -C paper`. The build
directory is not tracked.
Section 3 holds its definitions (Defs. 1–8) and Theorems 1–2, and Section 5
holds the evaluation (Tables 1–2).

| To find… | Go to |
|---|---|
| which file, theorem, fixture or log supports each claim, RQ1–RQ3 and every table row | [Paper map](docs/paper-map.md), checked by `lake env lean experiments/PaperMap.lean` |
| the Lean definitions and proofs | [Library guide](docs/README.md). Entry points: `SchemaWellFormed`, `SnapshotConforms` in [`Model/Semantics.lean`](VLMOF/Model/Semantics.lean); `checkSnapshot_iff` in [`Checker/Correctness/Acceptance.lean`](VLMOF/Checker/Correctness/Acceptance.lean); `sourceSatisfies_iff_conforms` in [`Source/Adequacy.lean`](VLMOF/Source/Adequacy.lean) |
| the textual language | [Source-language guide](docs/source-language.md); running example in [`examples/running-example/`](examples/running-example/) |
| the EMF bridge | [Bridge guide](bridge/README.md) |
| correctness fixtures, public inputs, timing workloads and the measurement protocol | [Evaluation guide](experiments/README.md) |
| how to rebuild and rerun everything | [Reproduction guide](REPRODUCING.md) and the wrapper [`experiments/reproduce.py`](experiments/reproduce.py) |
| the retained evidence behind the printed numbers | [`experiments/companion-evidence.json`](experiments/companion-evidence.json), not in this checkout |

The [source audit](sources/CLAUSE-AUDIT.md) and [profile](sources/PROFILE.md)
state the standards interpretation and omissions.

This checkout contains the sources, proofs, authored fixtures and runners. It
does not contain the pinned public inputs or the OMG specification files; both
are fetched and verified by hash. It also does not contain the evidence from
which the paper's tables were computed. A fresh run reproduces the decisions and
counts, while its times are new observations.

## Build and try a model

Use Linux or WSL with Python 3.10+, GNU Make and Lean installed through elan.
The toolchain file pins Lean 4.33.1. The Lean library has no external dependencies;
the acquisition and authored-case scripts use Python's standard library. The EMF
experiments also need Java 21 and Maven 3.9; see the [reproduction guide](REPRODUCING.md).

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
- [Representability](docs/representability.md): what the source language can
  denote, and the premises of the proved reification results.
- [Metadata pilot](docs/metadata.md): descriptions treated as ordinary objects,
  with a separate check of the interpreted schema.
- [Public runner](experiments/README-public.md): the import, round-trip and
  rejection controls on pinned public inputs.

Checker acceptance is proved equivalent to the declarative predicate on raw
represented inputs. Source adequacy connects independent symbolic satisfaction
to actual elaboration and acceptance under its explicit lexical premise. The
parser, JSON codec and Java/XML bridge are tested interfaces outside that theorem.
The source audit supports the selected EMOF interpretation; the theorem does not
establish standards fidelity merely by checking our definitions.

## Manuscript and development

Run `make -C paper` to build `paper/build/main.pdf`.
[Paper build instructions](paper/README.md) describe dependencies and formatting.
The manuscript presents the structural definitions, their source justification,
proved correspondence results and bounded native evaluation. Successful builds
establish the recorded checks, not submission readiness or author acceptance.

Keep mathematical definitions, their explanations and useful consequences together.
Use the existing semantic layers for new modules, put fixtures under `Examples/`,
and document the material assumptions and proof ideas. See [AGENTS.md](AGENTS.md)
for the repository's working conventions.

## Licence

The code, proofs, scripts, tests and documentation are MIT-licensed
([LICENSE](LICENSE)). Some files are not; [NOTICE](NOTICE) explains each
exception and [REUSE.toml](REUSE.toml) lists them by path:

- files derived from the Train Benchmark are EPL-1.0;
- the manuscript sources in `paper/` are the submitted version (a preprint), all rights reserved;
- Springer's template in `paper/template/` keeps its CC BY 4.0 and LPPL licences.

The OMG specification files are not in the repository. `make sources` downloads
and verifies them, because OMG's terms do not allow redistributing them.
