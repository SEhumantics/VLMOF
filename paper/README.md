# Building the manuscript

From the repository root, run `make -C paper`. Requires GNU Make, latexmk,
pdfLaTeX and the standard TeX Live packages used by main.tex. The PDF is
`paper/build/main.pdf`. Generated files are ignored. `make -C paper clean`
cleans the build through latexmk.

The checked-in `template/` contains the unmodified complete official archive
linked by SOICT, including Springer class 2.24 (29 January 2024), bibliography
style, sample, documentation and attribution. TEXINPUTS/BSTINPUTS select this
local copy. The downloaded archive has SHA-256
`7cc8efaa4f6e7ea8d17069c37a192c6023170f1e60f59509f3bb00591dcaf5de`.

Template origin (accessed 14 September 2026):
https://soict.org/wp-content/uploads/2025/09/Latex-Template-for-Springer.zip

The SOICT 2026 submission instructions require CCIS format, at most 12 pages
excluding references, a PDF without page numbers, and author names and
affiliations for single-blind review:
https://soict.org/submission/paper-submission/

Springer identifies these instructions/templates as applicable to CCIS:
https://link.springer.com/series/558/information-for-authors-and-editors

The camera-ready page separately specifies 12-15 pages including references
for full papers. This manuscript follows the submission page policy; the later
production policy applies to camera-ready work. Recheck the venue rules before submission.

The manuscript describes the delivered structural semantics, source adequacy,
executable checker and bounded EMF route. Its proof and compatibility claims
have different trust boundaries, stated in the text.

The companion archive is named `VL-MOF-artifact.zip`. Artifact manifests, rather
than the scientific narrative, record exact source revisions, dependency and
input hashes, bridge versions, and command logs. Its reproduction guide should
map the paper's mathematical concepts to the public layout. The principal map is:

- Core records: `VLMOF/Model/Basic.lean`;
- $W(S)$ and $C(S,M)$: `VLMOF/Model/Semantics.lean`, declarations
  `SchemaWellFormed` and `SnapshotConforms`;
- reachability and derived properties: `VLMOF/Model/Reachability/` and
  `VLMOF/Model/Properties.lean`;
- Equation (2): `VLMOF/Checker/Correctness/Acceptance.lean`, declaration
  `checkSnapshot_iff`;
- symbolic syntax and independent meaning: `VLMOF/Source/Syntax.lean` and
  `VLMOF/Source/Semantics.lean`, declaration `SourceSatisfies`;
- actual translation: `VLMOF/Source/Elaboration.lean`;
- Equation (3): `VLMOF/Source/Adequacy.lean`, declaration
  `sourceSatisfies_iff_exists_accepted`;
- the metadata reuse case: `VLMOF/Metadata/Pilot.lean`.

The reproduction guide also identifies the command-line front ends, restricted
EMF bridge, public evaluation manifests, and all trusted runtime boundaries.

The full running example is `paper/catalog-example.dsl`. From the repository
root, check it with:

```
lake exe vlmof check-dsl paper/catalog-example.dsl
```

Author fields remain empty because no author information was supplied. They and
the venue rules must be checked before submission.
