.DEFAULT_GOAL := pdf
.PHONY: pdf clean
export TEXINPUTS := ./template/:
export BSTINPUTS := ./template/:
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
clean:
	latexmk -C -outdir=build main.tex
