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

The paper-to-artifact map is [`docs/paper-map.md`](../docs/paper-map.md). It
names the Lean declaration behind each definition and theorem, the evidence behind
RQ1–RQ3, and the fixture and evidence file behind each row of Tables 1 and 2.
[`experiments/PaperMap.lean`](../experiments/PaperMap.lean) checks those Lean
names. The principal entries:

- Core records: `VLMOF/Model/Basic.lean`;
- $W(S)$ and $C(S,M)$: `VLMOF/Model/Semantics.lean`, declarations
  `SchemaWellFormed` and `SnapshotConforms`;
- Theorem 1, Equation (1): `VLMOF/Checker/Correctness/Acceptance.lean`,
  declaration `checkSnapshot_iff`;
- Theorem 2: `VLMOF/Source/Completeness.lean` (`elaborate_complete`, part (i))
  and `VLMOF/Source/Adequacy.lean` (`sourceSatisfies_iff_conforms`, part (ii));
- Equation (2): `VLMOF/Source/Adequacy.lean`, declarations
  `sourceSatisfies_iff_accepted` and `sourceSatisfies_iff_exists_accepted`;
- the running example and the Section 3 counterexamples: `examples/running-example/`.

[`REPRODUCING.md`](../REPRODUCING.md) is the reproduction guide. The retained
evidence behind the printed tables (exact source revisions, input hashes, bridge
versions and command logs) is described in
[`experiments/companion-evidence.json`](../experiments/companion-evidence.json);
it is not part of this repository.

`make -C paper` rewrites `build/main.pdf`. To check that the sources build without
replacing the submitted PDF, build a copy of `paper/` elsewhere.

The published Train structural projection is `examples/train/route-switch.dsl`. From the repository
root, check it with:

```
lake exe vlmof check-dsl examples/train/route-switch.dsl
```

## Status and licence

`main.tex`, `sections/`, `figures/` and `references.bib` are the source of the
version submitted for review, which is a preprint. They are not covered by the
repository's MIT licence: all rights are reserved by the authors (see
[`NOTICE`](../NOTICE)). Springer's policy for proceedings papers allows a preprint
to be shared at any time, provided it is not under an open licence. The revision
made after peer review is the accepted manuscript. Springer's licence to publish
governs where that version may appear, so it is not published in this repository.
The template in `template/` keeps Springer's licence: CC BY 4.0, with LPPL for
`splncs04.bst`.

Author fields are populated in `main.tex`. Any further author identifiers or
publication declarations must come from the authors; verify the applicable venue
rules for the actual submission stage.
