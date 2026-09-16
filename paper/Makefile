.DEFAULT_GOAL := pdf
.PHONY: pdf clean
export TEXINPUTS := ./template/:
export BSTINPUTS := ./template/:
pdf: build/train-diagram.pdf
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
clean:
	latexmk -C -outdir=build main.tex

build/train-diagram.pdf: figures/train-diagram.tex
	mkdir -p build
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build figures/train-diagram.tex
