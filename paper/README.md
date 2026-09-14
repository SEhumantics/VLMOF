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

Author fields are empty because author information has not been supplied;
they must be completed before submission. The manuscript describes the delivered
structural semantics, source adequacy, executable checker and bounded EMF route.
Its proof and compatibility claims have different trust boundaries, stated in the
text. Evaluation identifies the recorded artifact commit and named adaptations.
The companion `VL-MOF-review4-supplement.zip` packages source history, recorded
evaluation and independent Review 4 reports. Its `INDEX.json` identifies the shipped
source revision and hashes; `README.md` explains evidence locations and reproduction.
Technical review support and a successful PDF build are not submission-readiness
verdicts: author details and final venue requirements still need the author's check.
