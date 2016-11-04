agdatex := $(subst src/,latex/,$(subst .lagda,.tex,$(shell find src -name *.lagda)))

all: latex/jar.pdf
latex/%.tex: src/%.lagda
	@cd src; agda -i . -i ${AGDALIBDIR} --latex --latex-dir=../latex $*.lagda

latex/jar.pdf: $(agdatex) latex/jar.tex
	@cd latex;latexmk -g -pdf jar
