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
for full papers. This skeleton follows the submission policy, not that later
production policy. Recheck the venue rules before submission.

Author fields are empty because author information has not been supplied;
they must be completed before submission. Bibliography commands are supplied
as comments and can be enabled when reviewed references are actually cited.
There are no dummy references. Scientific results are explicitly pending.
The present two-page PDF verifies the build/layout only, not paper readiness.
