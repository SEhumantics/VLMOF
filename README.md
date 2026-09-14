# VL-MOF

An EMOF formalization project in Lean 4. The current baseline provides a Lean
build, reproducible specification downloads, and a finite raw representation of
the structural profile, separate schema and snapshot conformance predicates, and
proved consequences of opposite multiplicity. Executable schema and snapshot checkers are proved equivalent to those predicates.
The symbolic source language has independent satisfaction predicates and proved
binding completeness. The full source-to-core conformance correspondence remains
under development.

## Getting started

Use Linux or WSL with Python 3.10+, GNU Make and Lean installed through elan.
`lean-toolchain` pins Lean 4.33.1. Python uses only its standard library; there
are no external Lean libraries yet.

```sh
make sources
make check
```

The first command downloads six OMG files into `sources/raw/` and checks their
SHA-256 hashes. The second verifies those files offline, tests the download tool
and builds the Lean library. The library entry point compiles the core, semantics, interaction proofs, closure proofs, checker correctness and semantic examples.
See [VLMOF/REPRESENTATION.md](VLMOF/REPRESENTATION.md) for the data model;
constructing these records does not establish conformance.

The main interaction theorem shows that reciprocal occurrence counts and an upper-one
opposite force each forward reference count to be at most one, even without a forward
uniqueness declaration. Examples include a conforming witness and cases separating
the two premises. Inheritance uses a finite identity-deduplicated closure; persistence
and direct-superclass inclusion are proved. For well-formed schemas and resolved
starting classes, saturation proves that the class-count bound computes full
reflexive-transitive superclass reachability.

The Java/EMF resource-loading probe is documented in [bridge/README.md](bridge/README.md).
It checks inherited features, repeated values and reciprocal containment; it does not
yet import into or export from the Lean core.

The checker API is `checkSchema` / `checkSnapshot` in `VLMOF/Check.lean`.
`CheckAcceptance.lean` proves acceptance iff the corresponding predicate, with no
prevalidated-input assumption. Diagnostic lists report exactly the failed named
field checks. The command-line interface reads the versioned JSON interchange:

```sh
lake exe vlmof check-json examples/simple.json
lake exe vlmof check-dsl examples/simple.dsl
```

The command emits one JSON report. `check-dsl` first uses the tested, trusted DSL
parser and alias binder, reporting `parse-malformed` and `binding-failure` separately.
Its `accepted` result means the elaborated Core schema and snapshot pass the same
checker as JSON; a full source-to-core correspondence theorem remains pending. Exit codes are 0 accepted, 1 invalid represented
model, 2 malformed input or usage, 3 unsupported wire version, and 4 file error.
The decoder is a tested boundary, not a proved XML/JSON parser. It ignores unknown
object fields; the Lean JSON parser normalizes duplicate keys. Provenance is carried
as producer-supplied metadata, not independently verified. The Java EMF import/export
workflow remains under development.

The [symbolic DSL](VLMOF/DSL.md) supports qualified aliases, inheritance,
associations and occurrence lists. Its parser and binding examples are compiled
by the default build. Binding preserves identity distinctions, occurrence counts,
uniqueness, ordered equality and unordered permutation. `SourceSemantics.lean`
defines satisfaction directly over symbolic declarations; `ElaborationComplete.lean`
proves that every satisfying source document binds successfully. This result does
not yet establish conformance of the resulting core schema and snapshot.

The [metadata pilot](VLMOF/METADATA.md) treats class/attribute descriptions as
ordinary checked objects, interprets them into a schema, and validates an instance.
It documents which semantic constraints remain outside the metadata vocabulary.

## Reading the specification

Start with clause 12 of `sources/raw/MOF-2.5.1.pdf`. For searchable text, install
Poppler's `pdftotext` and run:

```sh
make text
```

This writes `sources/text/MOF-2.5.1.txt`. Use the PDF when checking figures and
page references.

MOF.xmi refers to a dated UML metamodel. We download that exact dependency and
its primitive declarations so those references can be inspected. The supplied
EMOF OCL file is also preserved for comparison with the prose. These files are
inputs to the source audit; downloading them does not determine their semantics.
Their URLs, purposes and hashes are recorded in `sources/manifest.json`.

Downloads and extracted text are ignored by Git. `make sources` reuses verified
files. To download again, run `python3 scripts/sources.py fetch --refresh`.
A failed download or hash mismatch leaves an existing file untouched. Hashes
are changed only through an explicit manifest edit after inspecting the source.

The reviewed static interpretation is documented in [sources/PROFILE.md](sources/PROFILE.md).
It identifies supported forms, explicit interpretation choices and deferred behavior.

## Manuscript

The [evaluation runner](experiments/README.md) records authored JSON/DSL cases and
a proof-library client with input hashes, commands and observed outcomes. Public-case
bridge evaluation remains pending.

Run `make -C paper` to build the working manuscript at `paper/build/main.pdf`.
See [paper/README.md](paper/README.md) for TeX dependencies and venue rules.
The manuscript skeleton has no completed semantic or evaluation claims.

## Development

Run `make test` for the Python tests and `lake build` for Lean. Run `make check`
before handing off an increment. Add dependencies and documentation when a
working feature needs them. Explain important modeling choices beside the
definitions or in a worked example.







