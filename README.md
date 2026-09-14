# VL-MOF

An EMOF formalization project in Lean 4. The current baseline provides a Lean
build and reproducible specification downloads. Semantic definitions come next.

## Getting started

Use Linux or WSL with Python 3.10+, GNU Make and Lean installed through elan.
`lean-toolchain` pins Lean 4.33.1. Python uses only its standard library; there
are no external Lean libraries yet.

```sh
make sources
make check
```

The first command downloads five OMG files into `sources/raw/` and checks their
SHA-256 hashes. The second verifies those files offline, tests the download tool
and builds the Lean library. The library entry point is currently empty.

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

## Manuscript

Run `make -C paper` to build the working manuscript at `paper/build/main.pdf`.
See [paper/README.md](paper/README.md) for TeX dependencies and venue rules.
The manuscript skeleton has no completed semantic or evaluation claims.

## Development

Run `make test` for the Python tests and `lake build` for Lean. Run `make check`
before handing off an increment. Add dependencies and documentation when a
working feature needs them. Explain important modeling choices beside the
definitions or in a worked example.

