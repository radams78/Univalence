agdatex := $(subst src/,latex/,$(subst .lagda,.tex,$(shell find src -name *.lagda)))

all: latex/TYPES2016/main.pdf

latex/%.tex: src/%.lagda
	@cd src; agda -i . -i ${AGDALIBDIR} --latex --latex-dir=../latex $*.lagda

latex/TYPES2016/main.pdf: latex/TYPES2016/main.tex
	@cd latex/TYPES2016; latexmk -pdf -g main
