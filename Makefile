PYTHON ?= python3
.DEFAULT_GOAL := check
.PHONY: sources verify test check text

sources:
	$(PYTHON) scripts/sources.py fetch

verify:
	$(PYTHON) scripts/sources.py verify

test:
	$(PYTHON) -m unittest discover -s tests -v

check: verify test
	lake build

text: verify
	mkdir -p sources/text
	pdftotext -layout sources/raw/MOF-2.5.1.pdf sources/text/MOF-2.5.1.txt
